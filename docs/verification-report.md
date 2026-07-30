# Formal Verification of SP1's Core RISC-V AIR in Lean — Technical Report

*sp1-clean-native — a Clean-native, semantically-specified verification of SP1's RISC-V chips.*
*Snapshot: 2026-07 (branch `dtumad/final-remediation`; SP1 semantic pin `v6.3.1-8-ga630089d9`).*

> **Line-number caveat.** Declarations are cited by name and file; line numbers appear only where
> stable. All quoted signatures are mechanically checked against the tree at the snapshot commit
> (see §13). If a quote and the tree ever disagree, the tree is authoritative.

## 1. Executive summary

This repository contains a machine-checked verification, in the Lean 4 proof assistant, that
**SP1's Core RISC-V AIR constraint system soundly implements the official RISC-V instruction-set
semantics**, for the 25 instruction chips of SP1 v6.3.1's supported Core profile, against the
Sail-generated RV64 model. The verification is built on the public
[Clean](https://github.com/Verified-zkEVM/clean) zkVM DSL and is structured so that every claim is
either a kernel-checked theorem, a mechanically enforced pin, or an explicitly named open
obligation.

The deliverables:

- **D1 — Native chip formalization.** All 25 supported instruction chips (the RV64IM ALU,
  control-flow, and memory core) are implemented as Clean `GeneralFormalCircuit`s with semantic
  specifications, plus 11 provider/boundary tables, forming the 36-table `sp1Ensemble`
  (`SP1Clean/Soundness/SP1Ensemble.lean`).
- **D2 — Per-chip soundness, completeness, and ISA refinement.** Every chip carries closed
  soundness *and* completeness proofs against a semantic `Spec`, and a Sail bridge (`advance`)
  showing its rows realize genuine steps of the official RV64 interpreter.
- **D3 — Whole-chip Rust faithfulness.** For each chip, a `ChipFaithful` theorem proves the
  hand-built native circuit's complete constraint system is *bidirectionally equivalent* to the
  complete `assertZero` list and interaction multiset extracted from SP1's Rust `Air::eval` by a
  pin-checked exporter (§4).
- **D4 — Machine-checked bus grounding.** The meaning of the inter-chip buses (state, program,
  memory, byte) is *derived* inside Lean from Clean's proved balance theorem plus per-chip
  lemmas — there are no paper-justified bus axioms (§6).
- **D5 — The headline theorem.** `supported_core_native_sound`
  (`SP1Clean/Soundness/AIR.lean`): every constraint-satisfying, channel-balanced witness of the
  36-table ensemble, with explicit boundary and timestamp premises, yields a genuine finite run
  of the official Sail RV64 interpreter between the public program-counter/clock endpoints (§8).
- **D6 — Conformance testing against the real prover.** A quarantined `native_decide` test
  library checks native witness generation and whole-chip trace generation cell-for-cell against
  batteries dumped from SP1's actual Rust prover at SP1's field (§9).
- **D7 — A reproducible audit harness.** One script (`scripts/run_audit.sh`) re-derives the
  dependency pins, gates zero proof deferrals with an empty allowlist, and regenerates a
  per-theorem `#print axioms` census (§13).

**The honest claim boundary, up front.** The proved statement is *existential and shard-local*:
it produces a Sail execution segment for one shard, whose initial state is characterized by the
provider-table binding rather than tied to an ELF-loaded boot state, and it consumes two
explicitly disclosed semantic premises (the provider/program binding and a physical
memory-timestamp range bound) that are not yet derived from the exact upstream system tables. The
repository deliberately *reserves* — declares nothing under — the names `sp1_air_sound`,
`sp1_execution_sound`, and `sp1_verifier_sound`: the exact-upstream refinement exists only as an
honestly conditional combinator (`sp1_air_sound_of_obligations`) over a named, currently
uninstantiated proof bundle (§8.3), the cross-shard execution relation is specified but has no
soundness theorem, and no cryptographic/probabilistic verifier claim of any kind is made (that is
the planned ArkLib layer, §12). No theorem in the main library depends on `sorry`, on any project
axiom, or on `native_decide`.

## 2. System overview

### 2.1 What is being verified

SP1 proves RISC-V guest executions with a STARK whose Core stage commits, per shard, a
multi-table AIR: one table per instruction class (Add, Mul, LoadByte, …), system tables
(syscalls, memory bumps, global accumulation), and preprocessed tables (program ROM, byte table,
range table). Tables communicate over LogUp-style buses: a chip row *pulls* its operands (a
register read is a receive on the memory bus) and *pushes* its effects (the register write-back,
the next CPU state). The verifier checks each table's polynomial constraints plus the global
bus balance.

The verification target is SP1 at semantic revision
`a630089d9ff484ec6f2feade8d0afbb1447eed11` (`v6.3.1-8-ga630089d9`), pinned in
`SP1Clean/FormalModel/CoreProfile.lean` (`sp1SemanticRevision`) and enforced end-to-end by the
extraction pipeline (§4). The supported profile is the exact 25-instruction-table slice of
upstream `RiscvAir::machine()`:

| Class | Chips |
|---|---|
| ALU / R-type | Add, Addi, Addw, Sub, Subw, Bitwise (XOR/OR/AND), Lt (SLT/SLTU), ShiftLeft (SLL/SLLW), ShiftRight (SRL/SRA/SRLW/SRAW), Mul (MUL/MULH/MULHU/MULHSU/MULW), DivRem (8 ops), UType (LUI/AUIPC) |
| Control flow | Jal, Jalr, Branch (BEQ/BNE/BLT/BGE/BLTU/BGEU) |
| Memory | LoadByte/Half/Word/Double, StoreByte/Half/Word/Double |
| x0 fast paths | AluX0 (any covered ALU op with `rd = x0`), LoadX0 (any load into `x0`) |

The only opcodes of SP1's 53-value opcode alphabet outside this profile are ECALL, EBREAK, and
UNIMP; they route to no chip on both sides (SP1's syscalls are ECALL-dispatched and handled by
the system tables and an explicit `SyscallHandler` boundary, §7.3). The routing table — including
the `rd = x0` dispatch split — is proved to partition the alphabet and has been independently
diffed against SP1's `tracing.rs` event emission, arm by arm.

### 2.2 Architecture: five pillars around a whole-chip boundary

The stable verification boundary is the **whole chip**, not individual gadgets:

```
Math/, Model/        general math + the SP1 substrate (Sail wrapping, buses, machine model)
Extracted/           auto-generated: complete Rust rows, assertZero lists, interaction lists
FormalModel/         the audit surface: Inputs + semantic Specs + relations (what is claimed)
Native/              hand-built Clean circuits (chips, operations, readers)
Proofs/, Faithful/,  soundness/completeness/Sail bridges; native↔Rust faithfulness;
Soundness/           the whole-machine grounding engine and the capstone theorems
```

Two design decisions distinguish this from transcription-style verifications:

1. **The Lean circuits are independent implementations, not transcriptions.** A native chip and
   SP1's Rust chip may decompose arithmetic differently; nothing requires per-gadget
   correspondence. The two are reconciled only at the whole-chip boundary by the `ChipFaithful`
   theorem (§4.3), which compares *complete* assertion systems and interaction multisets. This
   keeps proof-oriented circuit engineering (subcircuit reuse, witness design) free, while making
   the Rust-equivalence claim total rather than per-recognized-fragment.
2. **Specs are semantic, not structural.** A chip's `Spec` states what a row *means* — e.g. for
   Add, `is_real = 1 → toBitVec64 value = RV64.add (toBitVec64 op_c) (toBitVec64 op_b)` — never a
   restatement of its constraint list. The field is generic over primes `p > 2^17`
   (`p > 2^24` where Mul's column-sum bounds require it); SP1's KoalaBear
   (`p = 2^31 − 2^24 + 1`) satisfies both, and the conformance layer runs at exactly that field.

## 3. The Sail foundation

### 3.1 The model and the step relation

The ISA authority is the **official RISC-V Sail specification**, mechanically translated to Lean
(the `LeanRV64D` model, generated by the opencompl `sail-riscv-lean` pipeline). The repository
does not hand-write an ISA model; it wraps the generated interpreter:

```lean
-- SP1Clean/Model/Semantics/GuestProgram.lean
def SailStep (s s' : SailState) : Prop :=
  ∃ b : Bool, (try_step 0 false).run s = .ok b s'
```

`try_step` is the model's topmost entry point — interrupt dispatch, instruction fetch, decode,
execute, and PC commit — so no part of the interpreter is bypassed. Chains of steps
(`SailChain`), initial-state loading (`IsInitialState`), and the halt convention (`SP1Halted`:
PC at the halting ECALL with `x5 = HALT = 0` and the exit code in `x10`, matching SP1's Rust
syscall convention) are all defined over that single step relation. The two fixed `try_step`
arguments are audited benign: `step_no` feeds only trace strings, and `exit_wait` affects only a
hart-waiting arm that is dead under the configured active-hart state.

Instruction decoding is likewise delegated: the typed program-ROM decoder used by the grounding
engine is anchored to the generated `ext_decode` (a `decodedInROM` fact yields
`(ext_decode w).run s = .ok i s`), with per-class round-trip lemmas — so opcode/funct field
extraction is the Sail model's, not a re-implementation.

### 3.2 The fork delta: three configuration lines

SP1's runtime differs from a stock RV64 platform (no CLINT timer, no PMP, no test-signature
region). Rather than assuming these away per-proof, the repository builds on a minimal fork of
`sail-riscv-lean` whose **semantic delta is exactly three platform-configuration constants**
(documented with the retirement path in `docs/agents/sail-fork-delta.md`, and *proved* as `rfl`
lemmas in `SP1Clean/Model/SailMemory.lean`):

```
plat_have_clint = false     -- no core-local interruptor
plat_have_sig   = false     -- no test-signature region
sys_pmp_count   = 0         -- no PMP entries (unprotected M-mode)
```

The remaining platform configuration (machine privilege, disabled interrupts, HTIF off, the
single SP1 PMA region, …) is packaged as the `SailConfigured` invariant carried through every
execution statement, and `SailCodeMemoryCompatible` is the explicitly disclosed contract that
SP1's immutable program table and Sail's unified instruction/data memory agree on the code
region. (Compare Nethermind's A1–A4 assumptions for OpenVM, §11 — the same platform-shaping
concerns, handled there as per-proof hypotheses, here as a pinned three-line fork plus named
invariants.)

### 3.3 What the Sail layer contributes to the trust base

The generated model's *platform hooks* remain external axioms of the Lean environment, disclosed
per-theorem by the axiom census. Seven of them concern the supported slice's own effects:
`plat_term_write`, the four LR/SC reservation operations (`load_reservation`, `match_reservation`,
`valid_reservation`, `cancel_reservation`), `get_16_random_bits`, and
`sys_enable_experimental_extensions`. (The Sail runtime's `print` is a total definition, not an
axiom.) None is given a nontrivial axiomatized *property*; they are opaque effects the supported
instruction slice does not semantically depend on.

A theorem whose target is the *complete* generated interpreter inherits the whole hook surface of
that target, including hooks the supported RV64IM path never executes, and the census discloses
this rather than pruning it. Measured at this snapshot,
`SP1Clean.Soundness.supported_core_native_sound` depends on 100 axioms: the three logical baseline
constants (`propext`, `Classical.choice`, `Quot.sound`), the seven platform hooks above, 67
`riscv_f*`/`riscv_i*`/`riscv_ui*` floating-point and integer-conversion hooks reached through
`try_step`'s full instruction dispatch, and 23 generated `bv_decide` proof constants inherited from
the shift/multiply/store bridge lemmas. See `docs/snapshots/axiom-ledger.md` for the per-class
reading and `docs/snapshots/axiom-census.txt` for the raw entry.

## 4. Extraction and Rust faithfulness

### 4.1 The pin-checked exporter

The "what does SP1 actually constrain" side enters Lean through `update_extracted.py`, which
drives SP1's own constraint compiler as a **trusted but heavily fenced oracle**:

- `SP1_DIR` must be the audited *extraction overlay*: a checkout whose merge base with the
  semantic pin is exactly `a630089d9…`, whose committed delta over the **semantic AIR sources**
  (the 25 chip files plus the shared memory-access columns carrier — the 26-entry
  `EXTRACTOR_METADATA_FILES` set) is verified line-by-line to be reflection metadata only (`use sp1_derive` /
  `#[derive(...)`) — changes outside that surface are confined by an explicit allowlist to the
  exporter's own directories — and whose working tree carries exactly the two checked-in exporter
  patches (`scripts/extractor-patches/*.patch`), byte-hash-verified against the live diff. Every
  gate is fail-closed (`SystemExit` before any file is written).
- The exporter emits, per table, the complete column structure, the ordered `assertZero` list,
  and the ordered interaction list — **never a Clean circuit**, so extraction cannot manufacture
  the proof's other side. The patches were audited hunk-by-hunk: they operate strictly on the
  symbolic IR *after* `air.eval` and only render what the unmodified evaluator recorded.
- A machine-shape manifest is extracted unconditionally and compared against the audited profile
  (34-table execution cluster, 6-table memory-boundary cluster, every main/preprocessed width,
  the 160-cell public-values block) before anything regenerates; `Extracted/Provenance.lean` pins
  the semantic revision, overlay revision, and patch digest (the semantic revision additionally
  tied to `CoreProfile` by an `rfl` theorem; the other two enforced by the regeneration gates).
- Regeneration is byte-idempotent: a full `EXTRACT_AIR_ONLY` run at the pinned overlay reproduces
  all 59 generated AIR modules identically (every `.lean` file under `SP1Clean/Extracted/` except
  the hand-written `ExtractionDSL.lean`; re-verified at this snapshot; the separate trace-battery
  pass is the disclosed §4.3 provenance gap).

The readable table profile is additionally hand-transcribed in
`FormalModel/CoreProfile.lean` and proved to match the generated manifest by `decide`
(permutation on names with equal widths) — and that transcription was independently re-checked
against upstream `riscv/mod.rs` name-by-name for this report.

### 4.2 What "faithful" means here

For each chip, `Faithful/ChipOracle.lean` defines a `ChipOracle`: a bijective reconfiguration
between the native row and the extracted Rust row (`reconfigure`/`deconfigure` with proved
round-trips — field-copy maps, closed by `cases; rfl`), plus the extracted `assertZeros` and
`interactions`. The anchor theorem, quoted for Add:

```lean
-- SP1Clean/Faithful/AddChip.lean
theorem addChip_faithful :
    ChipFaithful (p := p) AddChip.Inputs AddChip.Columns Extracted.AddOracle.AddCols
      AddChip.circuit addChipRowCodec addChipOracle
```

where `ChipFaithful` demands, for **every** Rust row:

1. *constraints*: SP1's complete `assertZero` list vanishes **iff** the native circuit's complete
   constraint system holds on the reconfigured row (bidirectional — the native circuit neither
   weakens nor strengthens the Rust AIR); and
2. *interactions*: on every locally-accepted row, the native circuit's active interaction multiset
   is a **permutation** of the Rust row's active interaction multiset (all four buses, projected
   with multiplicities).

`Faithful/SupportedMachine.lean` then ties the 25 anchors to the upstream profile: a list of
`ChipFaithfulnessAnchor`s carrying the actual theorems, with `rfl`/`decide` certificates that its
length, chip names (SP1's `MachineAir::name` strings), and table tags match the pinned
instruction-table profile. Adding, removing, or reordering a supported table breaks these
certificates in the same change.

### 4.3 The residual extraction trust and its mitigations

`ChipFaithful` compares native circuits against *extracted* lists; the step from Rust source to
extracted list is the trusted oracle. Three mitigations bound it: the fail-closed pin/patch/shape
fencing above; a manual spot re-derivation (for this report, the Add oracle was re-derived
symbol-by-symbol from `operations/add.rs` + `add.rs` — the 4-limb carry chain in its
`2^16`-inverse form, both `is_real` booleanity asserts, and the `(Range, value[i], 16, 0)` byte
sends match exactly); and the independent trace-conformance layer (§9), which exercises the same
rows against the real prover's output rather than the exporter's.

One provenance gap is disclosed rather than closed: the whole-trace dumper that produced the
trace-conformance vector batteries is not part of the pinned overlay (audit finding F-R-01;
details in `docs/agents/extraction.md` and the archived findings log, git history at
`14c926bd`); the batteries' content is still independently
validated cell-for-cell by `native_decide` against the native circuits' own trace generation, and
reconstruction of the dumper as a third checked-in patch is filed follow-up work.

## 5. Chip contracts: one worked example

### 5.1 Add, end to end

The Add chip illustrates the whole per-chip chain. Its **native circuit**
(`Native/Chips/AddChip/Defs.lean`) composes three true Clean subcircuits — the CPU-state block,
the R-type register reader, and the native add gadget (`Native/Operations/AddOperation/`, which
re-derives the u16-limb carry chain in-project) — and assembles the chip's own row type. Its
**Spec** (`FormalModel/Contracts/Chips.lean`, `AddChip` namespace) is a semantic statement over
that row:

```lean
def Spec (input : Inputs (ZMod p)) (cols : Columns (ZMod p)) ... : Prop :=
  ... Readers.RTypeReader.Spec { ... } ∧          -- the register-file discipline of the row
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (input.is_real = 1 →
    Word.toBitVec64 cols.add_operation.value
      = RV64.add (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val))
```

with `op_b ↦ rs1`, `op_c ↦ rs2` projected from the reader's memory slots, and `RV64.add` the
riscv-lean reference function proved equal to the Sail `execute_RTYPE` ADD clause. Around this
Spec:

- **Soundness and completeness** (`Proofs/Chips/AddChip/Formal.lean`): the constraint system
  implies the Spec (assumptions: `True` — operand ranges are *derived* from the reader's bus
  pulls), and honest witness generation satisfies it.
- **The Sail bridge** (`Proofs/Chips/AddChip/Bridge.lean` + the chip's `advance` contract): a
  Spec-satisfying real row, wired to decoded program-ROM operands, realizes one step of the
  official interpreter. (Add is a `rd ≠ x0` chip — SP1 routes the `rd = x0` variant of every ALU
  opcode to the separate AluX0 table, whose own bridge proves the discarded write; chips that
  genuinely admit `rd = x0` rows, like Jal/Jalr, carry two proven bridge arms.)
- **Faithfulness** (`Faithful/AddChip.lean`, §4.2) and **conformance** (§9) close the loop to
  SP1's Rust implementation.

Every conjunct of every chip Spec was adversarially re-reviewed for this report against the Sail
clauses and SP1's Rust executor (the 2026-07 release-readiness audit, batches A1–A7; findings
log archived in git history at `14c926bd`):
operand order for the non-commutative ops, sign-extension and mask widths for all six shifts,
byte-lane selection and extension widths for all loads, and the store merge math (proven to
preserve untouched bytes) — with zero soundness findings.

### 5.2 The hard case: DivRem's evidence contract

Division is where zkVM constraint bugs classically live (underconstrained `q·b + r = a`
identities). The DivRem chip uses a dedicated contract design
(`FormalModel/Contracts/DivRem.lean`): the eight opcodes partition into **four semantic
families** (signed/unsigned × 64/32-bit), each defined by an evidence record whose Euclidean
identity is stated over **full-precision ℕ/ℤ** (not modulo 2^64) together with the exact
remainder-bound, sign, divide-by-zero, and INT_MIN/−1 overflow conditions. The audit confirmed
the families are *total* (one-hot selection is forced on real rows) and *uniquely determining*
(the conditions pin quotient and remainder — precisely the property whose absence is the classic
bug). Circuit-independent lemmas (`Proofs/Chips/DivRemChip/Cases.lean`) take evidence to the ISA
result; the one heavy arithmetic seam is the whole-chip `evidenceSoundness` theorem deriving the
evidence from circuit facts plus two disclosed operand-range assumptions.

## 6. Buses and machine-checked grounding

### 6.1 Channels carry what SP1 constrains — nothing more

Each of the four buses is a plain Clean `Channel` whose row-local guarantee is exactly what SP1's
receiving table enforces (`Model/Channels.lean`):

| Channel | Row guarantee | SP1 counterpart |
|---|---|---|
| State | `True` | the state bus has no row-local receiver checks |
| Program | `RowSpec` (register indices < 32, pc limb bound, boolean `op_a_0`) | the preprocessed program table |
| Memory | `isU64 ∧ ClkBound` (value limbs are u16s; access timestamp < 2^24) | the memory-access columns' range checks |
| Byte | `ByteRowSpec` (the AND/OR/XOR/U8Range/LTU/MSB table clauses + width-8/13/16 range rows) | the preprocessed byte table and range table |

Crucially, channels do **not** assert reachability or execution semantics. A guarantee like
`ClkBound` is backed row-by-row by an actual receiver circuit in the ensemble (the byte/range
provider tables — mirroring SP1's own preprocessed `Byte` and `Range` chips, the latter being the
genuine receiver of SP1's `(Range, a, bits, 0)` lookups).

### 6.2 Execution truth is a conclusion, not an assumption

The global facts one actually wants — "the state messages describe a chained execution," "every
memory read sees the last write," "program rows come from the committed ROM" — are **theorems**
(`StateTruth`/`MemTruth`/`ProgTruth` in `Model/Semantics/Truth.lean`), derived by a timed
grounding engine (`Soundness/TimedGrounding.lean`, `RankedGrounding.lean`,
`GroundingAdapter.lean`, `ChipContracts.lean`) from:

- Clean's proved **channel-balance theorem** (the multiset of pushes equals the multiset of
  pulls);
- the provider/boundary tables' facts and the program commitment;
- the strict rank induced by the 24-bit access timestamps (`ClkBound` is what makes "earlier"
  well-founded — the `pull_lt_push` lemma); and
- one `advance` lemma per chip (its rows pull operands at the scheduled ticks and push the
  correctly-advanced state 8 ticks later; syscall events take 264 ticks, with the SP1 host
  behavior confined behind an explicit `SyscallHandler` boundary).

The payoff theorem of this layer:

```lean
-- SP1Clean/Soundness/AIR.lean
theorem supported_core_witness_grounding ... :
    ∃ orderedRows, SupportedCoreGrounding statement witness initial orderedRows
```

where `SupportedCoreGrounding` packages: *exhaustive* (the ordered rows are a permutation of
exactly the witness's real decoded rows), *walk* (they chain program counters from the public
initial to the public final PC), *grounded* (each row's operands are the evolving machine state's
values at its ticks), and *clockCount* (`init_clk + 8·length = final_clk`).

This is the central methodological contrast with bus treatments that assume well-formedness
properties on read and verify them on write, justifying the global argument on paper (§11): here
the entire read-side meaning is downstream of the balance theorem and the timestamp discipline,
inside the kernel.

The comparison to StarkWare's S-two AIR verification (§11) is instructive precisely because their
memory model differs. Cairo memory is *read-only*, so S-two needs only functional
well-definedness of its memory maps, and it **assumes** this (`IsMemAssign`, enforced upstream by
preprocessed distinct-value columns — "we do not verify… add it as a hypothesis"). SP1's
read-write memory requires the strictly harder "every read sees the last write," which this
section derives in-kernel from channel balance plus the 24-bit timestamp rank rather than
assuming it. Conversely, S-two proves in Lean the LogUp lookup argument that underwrites its bus
(including a quantitative soundness-error bound), whereas we take multiset balance as an
interface and defer that layer (C2).

## 7. From grounded rows to Sail execution

### 7.1 Decode, walk, and the local chain

`Soundness/WitnessDecode.lean` deterministically decodes typed rows from the raw table witness;
the grounding walk orders them; and `Soundness/LocalExecution.lean` turns the ordered, grounded
rows into a genuine interpreter run: each row's `advance` lemma discharges one `SailStep`, and
the chain composes into a `trajectory`-style finite run of `try_step`. The conclusion object
(`Machine.ClosedLocalExecutionSegmentWitness`) carries the real run — this was verified for the
report by tracing the definition chain down to `(try_step 0 false).run`; the conclusion is not
bookkeeping around an abstract relation.

### 7.2 The machine model parameter

The capstone quantifies over a `Machine.SP1MachineModel` (scheduling + boot packaging) restricted
by `UsesOrdinarySchedule` (ordinary instructions take the 8-tick schedule). Only the schedule
field is consumed by the shard-local theorem; boot reachability is deliberately deferred to a
later anchor. Two honest notes: (i) no `SP1MachineModel` instance is currently constructed
in-repo, so the theorem is a parametric conditional not yet exercised end-to-end — the
configured-state core is already witnessed (`isInitialState_nonvacuous`,
`FormalModel/Trace/Witness.lean`), but the model's total boot-loader field (ROM+image loading for
arbitrary well-formed programs) is filed follow-up work, and an empty-shard witness of the full
native relation was assessed feasible but is not yet constructed (audit findings
F-A8-04/F-A9-02); (ii) the shard-local initial state comes from the boundary binding, not from
`model.boot`.

### 7.3 What is *not* claimed at this layer

No cross-shard stitching (the relation exists — `SP1ExecutionRelation`, with full-state
continuity between consecutive execution shards, last-shard canonical-halt, and ledger
authentication fields — but its soundness theorem is intentionally not declared). No syscall
host-behavior semantics beyond the `SyscallHandler` interface. No boot/ELF-loading claim. No
completeness claim at the capstone (per-chip completeness is proved; the ensemble-level
completeness statement is deliberately left undeclared rather than stated in a false-if-broader
form — the boundary comment in `Soundness/AIR.lean` documents the intended shape).

## 8. The headline theorem and the conditional exact-AIR layer

### 8.1 The native relation

```lean
-- SP1Clean/Soundness/AIR.lean
def SupportedCoreNativeRelation :
    WitnessRelation.Relation (SupportedCoreStatement p) (SupportedCoreNativeWitness p) :=
  fun statement witness =>
    SupportedCoreEnsembleRelation statement witness ∧
      SP1SemanticBoundaryRelation statement witness ∧
        SupportedCoreMemoryTimestampRangeRelation statement witness
```

- `SupportedCoreEnsembleRelation`: the public input matches, **all** row constraints hold over
  **all** 36 tables (+ the state-boundary verifier), and **all** channels balance — verified for
  this report quantifier-by-quantifier down into Clean's `FlatEnsemble` (∀-tables, ∀-rows;
  no existential slips).
- `SP1SemanticBoundaryRelation`: there is an initial Sail state bound to the committed program
  and the provider tables' boundary facts (`RomLoaded`, `SailConfigured`, initial PC/clock,
  provider bounds). This is an explicit companion *premise* — provider tables mean what they say —
  not something derivable from balance alone.
- `SupportedCoreMemoryTimestampRangeRelation`: the pulled memory timestamps respect the physical
  `< 2^24` bound — the premise that prevents timestamp wraparound at the field characteristic.

### 8.2 The theorem

```lean
theorem supported_core_native_sound (model : Machine.SP1MachineModel)
    (ordinary : model.UsesOrdinarySchedule) :
    WitnessRelation.Sound (SupportedCoreNativeRelation (p := p))
      (SupportedCoreLocalExecutionRelation model)
```

Read precisely: for every statement and every witness in the native relation, **there exists** a
shard-local execution witness — a genuine finite `try_step` run of the official Sail RV64
interpreter, on the committed program, whose PC and clock endpoints are the statement's public
values. Axiom census: `propext`, `Classical.choice`, `Quot.sound`, plus the disclosed Sail
platform hooks and `bv_decide` constants inherited from the bridges (§3.3). No `sorryAx`
anywhere in the released set (empty allowlist, gated in CI).

This existential, public-endpoint-anchored shape matches the independently developed S-two
AIR-soundness theorem (§11; arXiv 2606.04311, App. A: `∃ mem, ∃ exec, exec 0 = initialState ∧
exec (Fin.last n) = finalState ∧ ∀ i, NextState mem …`), which likewise concludes the
*existence* of a semantic execution segment between agreed endpoints rather than a functional or
verifier-level statement — corroborating that this is the natural target for an AIR-soundness
result, with the shard-local restriction being ours alone.

### 8.3 The exact-upstream layer is honestly conditional

The relation over SP1's *exact* extracted tables (the 34-table execution cluster, with
`GlobalValid` demanding well-formed public values and an exact natural-number send/receive
balance) is defined in `Faithful/CoreAIR.lean` + `FormalModel/CoreAIRRelation.lean`. Its
refinement into the eventful SP1/Sail shard relation exists only as:

```lean
-- SP1Clean/Soundness/CoreAIR.lean
theorem sp1_air_sound_of_obligations ...
    (proofs : CoreAIRRefinementObligations binds handler programBinding) :
    WitnessRelation.Sound (CoreAIR.Current.Relation binds .execution)
      (SP1CoreShardExecutionRelation .base handler programBinding)
```

conditional on `CoreAIRRefinementObligations` — a named structure whose fields are the open
proofs (decode totality, public-value/program well-formedness, first-shard discipline, syscall
transcript and commit-operand equalities, the boundary-shard case, and the substantive
`executionCase`: exact system-table rows ground an eventful Sail segment). The bundle was audited
for coherence (fields well-typed, mutually consistent, none dead — every field is consumed by the
combinator). Until a closed construction exists, the unqualified names stay reserved. This is the
repository's core honesty discipline: conditional results are *named* as conditional, and
headline names are not spent early.

## 9. Conformance testing against the real prover

Kernel-checked theorems establish soundness; they cannot establish that the formalized constraint
system is the one the *shipping prover* satisfies, nor that witness generation is live. A separate
test library (`SP1CleanTest/`, never imported by the main library) closes that gap empirically at
SP1's own field (KoalaBear, `p = 2130706433`):

- **Witness conformance** (11 operation anchors): the native Lean witness functions reproduce,
  on every vector dumped from SP1's real `populate`, the exact column values Rust wrote.
- **Whole-chip trace conformance** (10 chips today; extending it to all 25 is documented
  follow-up work in `docs/agents/extraction.md`): the chip's
  *own* `main` acts as a trace generator — witness columns from its witness closures, layout from
  its output struct — and the resulting full padded matrix is checked **cell-for-cell** by
  `native_decide` against a matrix dumped from SP1's real `MachineAir::generate_trace`. For
  migrated chips the check runs through the faithfulness `reconfigure` map, so it also audits the
  native→Rust row correspondence on real data. Selector-driven chips (Mul, DivRem, Bitwise, Lt,
  the shifts) take a per-event hint that was verified to be the dumped executor opcode — an input
  to the run, structurally incapable of laundering expected outputs into agreement.

These anchors are the project's only `native_decide` uses (they trust the Lean compiler, adding
`Lean.ofReduceBool`/`trustCompiler`), quarantined by a CI guard that forbids `native_decide` in
the main library, and disclosed per-anchor in the axiom census. What conformance establishes:
populate fidelity and non-vacuity evidence on real prover data. What it does not: proof. The two
layers are complementary by construction. (Provenance caveat for the trace batteries: §4.3.)

Additionally, `SP1CleanTest/NonVacuity.lean` witnesses the satisfiability of every non-trivial
chip `Assumptions` (all 20 chips whose assumptions are not literally `True`, instantiated at
SP1's field with the gated store conjuncts exercised on real rows) — closing the "could a chip's
assumptions be unsatisfiable?" vacuity question at the chip level.

## 10. Trust base

Everything the results depend on beyond the Lean kernel, numbered for reference. **T** = tooling,
**M** = model premises (semantic hypotheses of the proved theorems), **C** = cryptographic layers
(future work, no claim made here). The per-theorem axiom census (`docs/snapshots/axiom-ledger.md`)
discloses which of these each headline declaration actually touches.

- **T1 — The constraint exporter.** SP1's constraint compiler, run at the pin-checked overlay, is
  trusted to print the constraint/interaction lists its `air.eval` recorded. Mitigations: §4.1's
  fail-closed fencing, §4.3's manual re-derivation, and the independent conformance layer.
  (Note: the exporter tooling lives on sp1's `dtumad/clean-native` branch, not upstream `main`;
  upstreaming/committing the remaining tooling is follow-up work bundled with the pin
  restoration.)
- **T2 — The Sail platform hooks.** The generated model's external operations (§3.3) — opaque,
  property-free axioms.
- **T3 — `native_decide` in the test library only.** The conformance anchors trust the Lean
  compiler; the main library is `native_decide`-free (CI-gated).
- **T4 — Toolchain state (temporary).** At this snapshot the Clean/Sail dependencies are local
  4.31-migration path checkouts; restoring reproducible git pins is a named release blocker
  tracked outside this report. The `lake-manifest` pins recorded by the audit script are the
  intended targets.
- **M1 — The semantic boundary binding.** Provider/boundary tables mean the selected program and
  initial state (`SP1SemanticBoundaryRelation`, §8.1). To be derived from the exact upstream
  system tables (the `executionCase` obligation).
- **M2 — The memory-timestamp range bound.** Pulled high timestamps < 2^24
  (`SupportedCoreMemoryTimestampRangeRelation`) — prevents wrap at the characteristic; to be
  derived from the upstream range constraints in the same obligation closure.
- **M3 — The syscall handler.** SP1 host-syscall behavior is confined behind the
  `SyscallHandler` interface; its faithfulness to SP1's host is out of scope.
- **M4 — The machine model.** The capstone is parametric over `SP1MachineModel` +
  `UsesOrdinarySchedule`; no instance is constructed in-repo yet (§7.2).
- **C1 — Preprocessed commitment binding** (`PreprocessedBinding`) — to be discharged at the
  PCS/ArkLib layer.
- **C2 — Exact natural balance.** The exact-AIR relation's `Balance.Valid` is a natural-number
  multiset equality; connecting it to the field-level LogUp/GKR argument (with its soundness
  error) is the cryptographic layer's job.
- **C3 — Shard-ledger cryptography.** Cross-shard cumulative sums and deferred-proof digests —
  the recursion/verifier layer.

Baseline logical axioms: `propext`, `Classical.choice`, `Quot.sound`; plus `bv_decide`'s checker
constants on named shift, multiply, store, jump, and byte-gadget lemmas (23 of them reach the
headline theorem, §3.3). Zero `sorryAx`; zero project `axiom` declarations; both gated by CI with
empty allowlists.

## 11. Scope comparison: the Nethermind OpenVM verification

The closest related effort is Nethermind's formal verification of the OpenVM RV32IM zkVM
(technical report, Feb 2026; Lean 4.26). It is substantial work — 45 RV32IM opcodes verified
against the Lean RISC-V specification, with an execution/memory-consistency development — and the
comparison below is about *methodological shape*, not quality. Where their scope is broader
(e.g. full RV32IM including AUIPC-class and all immediate-variant opcodes verified individually,
against a spec instantiated for RV32), we say so. **Dating note:** this comparison is against
their v1.5.0 report (OpenVM engagement commit `645460f`); the live `openvm-fv` repository has
since re-targeted OpenVM v2.0.0 with the same 45-opcode Lean surface, and additionally carries
per-chip soundness proofs for the Keccak-f[1600], Keccak sponge, and SHA-256/512 precompile chips
(against FIPS reference models) plus a three-gate axiom-footprint CI whose independent
`lean4export` re-export is a genuinely strong axiom-discipline mechanism — both real strengths
beyond the report compared here.

| Dimension | Nethermind / OpenVM | This work / SP1 |
|---|---|---|
| Target | OpenVM, RV32IM, 45 opcodes | SP1 v6.3.1 Core, RV64IM slice, 25 chips (~50 opcodes incl. W-variants and x0 paths) |
| ISA reference | Lean RISC-V spec (RV32 instantiation), per-opcode `execute_*` clauses | Same Sail lineage, RV64 generated model, full-interpreter `try_step` step relation |
| Circuit side | Transpiled/extracted constraints are the proof object; AIR columns hand-transcribed with "eyeball correspondence" macros | Independent hand-built Clean circuits; extracted lists are a *comparison target*; whole-chip bidirectional `ChipFaithful` + interaction-multiset permutation |
| Bus semantics | `BusEntry` classes: well-formedness assumed on read / asserted on write; bus *axioms* (pc bounds, timestamp bounds) justified **on paper** (their §E1–E12, §M1–M6) | Channel guarantees are row-local facts backed by receiver circuits; all read-side meaning derived in-kernel from Clean's balance theorem + timestamp rank (§6); zero paper bus axioms |
| Consistency | Rising-bus theorem: execution/memory bus entries can be reordered chronologically, conditional on balance hypotheses; per-opcode row-local equivalence theorems | One glued theorem: balanced constrained witness → existence of a Sail interpreter run with matching public endpoints (§8.2); per-chip statements are internal lemmas of it |
| Prover conformance | none against the real prover/witness generator (their CI gates — an axiom-hygiene scan, an in-build `collectAxioms` audit, and an independent re-export comparator — police the *axiom footprint*, not prover-trace conformance) | `native_decide` witness + whole-trace batteries vs the real prover at SP1's field (§9) |
| Crypto trust | Lookup argument + proof system assumed (their I1 = lookup/bus argument, I2 = proof system; their I3/I4 cover spec faithfulness and Lean's kernel) | Same boundary, expressed as named relations/obligations (C1–C3) with an ArkLib-shaped target signature |
| Claim discipline | Per-opcode theorems + consistency lemmas | Reserved-name policy: headline names undeclared until unconditional (§8.3) |
| Their broader coverage | Immediate-variant opcodes verified as first-class; RV32 spec assumptions (S1–S4, A1–A4) documented per-proof | Immediate variants fold into base chips (as SP1 itself does); completeness witnesses currently cover register-register forms only for Bitwise/Lt (disclosed) |

**A third reference point: StarkWare's S-two AIR verification.** The other closely comparable
effort is StarkWare/CMU's Lean 4 verification of the S-two Cairo-AIR (Avigad, Ganor, Goldberg,
Levit, Nir, Seginer, Titelman, arXiv 2606.04311, June 2026). Its top theorem `trace_sound` has
the *same existential, endpoint-anchored shape* as ours — AIR satisfiability yields
`∃ mem, ∃ exec : Fin (n+1) → RegisterState Felt252` chaining the public initial state to the
public final state under the Cairo `NextState` relation — a useful independent confirmation that
"AIR witness ⇒ existence of a semantic execution segment between public endpoints" is the right
claim shape for a zkVM AIR-soundness result. Three axes distinguish the projects:

| Axis | StarkWare / S-two | This work / SP1 |
|---|---|---|
| AIR into Lean | Hand-re-modeled constraint-*generating* code; a fixed, collapsed component set (an idealization); trust that "the S-two code has been modeled in Lean correctly" | Pin-checked extraction of the exact shipping constraint/interaction lists, reconciled by bidirectional `ChipFaithful` |
| Semantics authority | Self-defined Cairo `NextState`, formalizing the informal Cairo whitepaper | Official RISC-V Sail interpreter (`try_step`), mechanically translated |
| Lookup argument | The LogUp lookup argument is **proved in Lean**, with a quantitative bad-set soundness-error bound | Field-level LogUp/GKR soundness **deferred** (C2); we prove only *from* multiset balance |

On the first two axes our exact-extraction and official-Sail choices are more faithful to the
shipping system; on the third, S-two reaches one layer deeper into the proof system than we
currently do, and their AIR-soundness reduction is a completed whole-program proof (theirs found
and fixed real production bugs — a missing range check and insufficient LogUp security bits)
where ours is shard-local with the `executionCase` obligation still open.

The essential difference is where the bus argument lives. Both projects face the same global
question — *why do reads see the right values?* Nethermind answers it with a well-structured
paper argument justifying bus axioms their per-opcode proofs consume. This project's answer is a
Lean derivation: the only bus facts any proof consumes are row-local guarantees enforced by an
in-ensemble receiver, and everything global is a theorem downstream of channel balance. The cost
of that choice is the large grounding layer of §6–7; the benefit is that the paper step — the
usual home of subtle gaps — is inside the kernel.

## 12. Limitations, open obligations, and the path forward

Stated plainly:

1. **Shard-local, existential conclusion.** One shard segment; boot reachability and cross-shard
   stitching are specified but unproven (§7.3). No machine-model instance is constructed yet.
2. **Two semantic premises** (M1, M2) await derivation from the exact upstream system tables —
   the `CoreAIRRefinementObligations.executionCase` closure, the single genuinely open
   mathematical obligation of the AIR layer.
3. **No cryptographic claim.** Nothing here says anything about STARK soundness, FRI, LogUp/GKR,
   or Fiat–Shamir. The planned final form is probabilistic and lives in the ArkLib/VCVio
   integration: an executable `verifyCore` agreeing with the pinned Rust verifier, ArkLib
   knowledge soundness extracting a full AIR witness with an explicit error bound, and
   `sp1_air_sound` turning that witness into the Sail execution relation. The
   `FormalModel/Verifier.lean` boundary (a deterministic `PerfectExtraction` analogue with
   composition lemmas) is shaped for that seam. StarkWare's S-two verification (§11) is a
   concrete precedent for the layer immediately below `sp1_air_sound`: they formalize the LogUp
   lookup argument itself in Lean — the logarithmic-derivative counting lemma and explicit
   bad-set cardinality bounds quantifying the soundness error — while still treating the
   underlying circle STARK and the Fiat–Shamir randomness as assumed. That is exactly the
   intermediate abstraction our C2 obligation names (multiset balance ⇒ field-level LogUp
   soundness with an error bound), and their lemmas are a candidate model for how the ArkLib
   layer can discharge C2 rather than assume it.
4. **Completeness at the ensemble level is undeclared** (per-chip completeness is proved;
   Bitwise/Lt completeness witnesses currently cover register-register forms only).
5. **Trusted surfaces T1–T4** (§10), including the temporary local dependency pins and the
   trace-battery provenance caveat (§4.3).
6. The AIR models the *supervisor-mode* Core profile; user-mode/mprotect table variants,
   precompiles, and the memory-protection chips are out of scope.

This report describes the state of an ongoing verification, not an audit certificate. Findings
of the 2026-07 release-readiness audit — including everything disclosed above — were logged with
file-level citations in a findings log kept out of the release tree by design; retrieve
docs/audits/2026-07-release-readiness.md (no longer in the tree) from git history at commit
`14c926bd`.

## 13. Reproduction

```sh
lake build SP1Clean        # the main library: 0 errors, 0 warnings, 0 info notes
lake test                  # the conformance anchors (the only native_decide)
lake lint                  # curated environment linters
scripts/run_audit.sh       # pins + zero-deferral gates + per-theorem axiom census
```

Toolchain: Lean `v4.31.0` / mathlib `v4.31.0` (dependency-pin caveat: T4). Extraction
regeneration requires the pinned sp1 extraction overlay (sp1's `dtumad/clean-native` branch tip
plus the two checked-in patches) and a Rust toolchain — see `docs/agents/extraction.md`. The
axiom census snapshot lives at `docs/snapshots/axiom-ledger.md`; regenerate before citing.
Report quotes are checked by `scripts/check_report_citations.sh` (added with this report).
