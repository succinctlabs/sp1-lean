# SP1 verified: what is proven, and how to check it — TARGET STATE

**STATUS: ASPIRATIONAL GOAL DOCUMENT (drafted 2026-07-09; goal restated 2026-07-17).**
This is a completed-voice sketch of the target: **full Core AIR soundness, stated and proven as a
layered refinement stack whose top composes with an actual verifier** — an executable Lean
`verifyCore` agreeing with the pinned Rust verifier, made sound by ArkLib/VCVio knowledge soundness
post-composed through the AIR refinement. It is not a checklist. Use `release-audit.md`,
`overview.md`, and `proposals/consolidation-progress.md` for current claims. Do not cite this
document as current status.

---

## 0. The claim, and how to read this document

SP1 is a RISC-V zkVM: a prover claims "this program, run on these inputs, exited with this code,"
and a succinct proof convinces a verifier. This repository proves, in Lean 4 with the kernel
checking every step, that SP1's constraint system actually enforces that claim: **if the verifier
accepts, then the official RISC-V specification — the Sail model, the same one hardware vendors
test against — executing the committed program, really reaches that exit.**

For the SP1/Rust reader: every Lean object names its Rust counterpart — chip names are
`MachineAir::name()`, the routing table mirrors `tracing.rs`, the column structs are extracted from
your constraint compiler, and the trace conformance suite runs against your real `generate_trace`.
For the Lean/Clean reader: chips are Clean circuits, buses are Clean channels, and the top theorem
is an `Ensemble.Statement → Spec` implication whose `Spec` is external (Sail) semantics.

**Altitude convention.** This document describes what SP1-clean-native builds *on top of* its
dependencies — Clean (the circuit/channel calculus) and LeanRV64D (the RISC-V Sail model) — at the
level of the configuration we impose and the notions we define; it does not re-explain the
dependencies themselves. §2.1 states the global Lean configuration verbatim; every dependency notion
(a Sail step, a Clean channel, a decoded instruction) is named where a reader who already knows that
dependency can audit the seam. Read from whichever end you know: the config block + §2 suffice to
audit the RISC-V connection, the chip/ensemble sections + `Faithful/` the SP1 connection.

Vocabulary, used consistently: a **chip** is one of the 26 semantic tables (SP1's `RiscvAir`
variants, including HALT); a **table** is any ensemble member (chips + providers); **pull/push**
are Clean's bus operations — SP1's Rust `send`s where we `pull` on the Program and Memory buses,
and the interaction lists match SP1's up to that per-channel sign flip (a LogUp symmetry,
machine-checked per chip); an **SP1 opcode** is the 53-value field-encoded discriminant, distinct
from a RISC-V **instruction** (the Sail `ast`); an **adapter** (SP1's term) is what the Lean code
calls a reader; "**trace witness**" = the prover's matrix, "**witnessed columns**" =
circuit-generated values, "**witness generator**" = the populate function.

## 1. The theorem stack

Every layer is a witness-producing refinement (`WitnessRelation.Sound`, `FormalModel/Relations.lean`),
so the layers compose by `Sound.trans` and the verifier consumes them through `Sound.extract` without
touching the knowledge error:

```lean
-- Layer 1 (native): a satisfied, balanced native Clean ensemble witness yields a
-- shard-local official-Sail execution segment between the public endpoints.
theorem supported_core_native_sound :
    WitnessRelation.Sound SupportedCoreNativeRelation
      (SupportedCoreLocalExecutionRelation model)

-- Layer 2 (faithfulness): the extracted Rust AIR is the native ensemble — per-chip
-- whole-row ChipFaithful anchors (assert-list iff + interaction-multiset Perm)
-- transport Layer 1 to the AIR SP1 actually proves.
theorem supported_core_air_sound :
    WitnessRelation.Sound SupportedCoreAIRRelation
      (SupportedCoreLocalExecutionRelation model)

-- Layer 3 (full upstream): the complete Core shard AIR with the real SP1PublicValues
-- record, then boot-to-halt shard composition over an authenticated ledger.
def sp1_air_refinement :
    WitnessRelation.FunctionalRefinement
      (CoreAIR.Current.Relation preprocessedBinding .execution)
      (Execution.SP1CoreShardExecutionRelation .base handler programBinding)

theorem sp1_execution_sound :
    WitnessRelation.Sound SP1RecursiveAIRRelation
      (Execution.SP1ExecutionRelation layout model handler programBinding
        globalBalance deferredAuthenticated)

-- Layer 4 (the verifier): ArkLib/VCVio knowledge soundness for the executable
-- verifier, its straight-line extractor post-composed through sp1_air_sound
-- (FormalModel/Verifier.lean's PerfectExtraction.refine is the deterministic seam).
theorem sp1_verifier_sound :
    verifier.knowledgeSoundness ...
```

Read: Layer 1 is proven natively over the timed-grounding engine — balance and per-row constraints
force a genuine Sail chain, row by row at its clock position. Layer 2 is where "the circuit is SP1's
circuit" enters: 25 whole-chip faithfulness anchors, internals-flexible by design. Layer 3 widens the
statement to everything the upstream verifier checks (all tables, public-value integrity, digests,
shard continuity, the halting ECALL). Layer 4 is the actual verifier: an executable Lean `verifyCore`
that agrees with the pinned Rust verifier on structured real proofs, whose ArkLib knowledge-soundness
theorem — Fiat–Shamir, commitments, LogUp GKR, PCS — extracts a full AIR witness with an explicit
error bound; post-composing the extractor through the deterministic stack yields the headline claim.
The final statement is probabilistic/knowledge-soundness-shaped; nothing here claims the unconditional
implication `verifyCore = true → valid execution`. The native ensemble and its faithfulness proofs
implement the AIR relations; they are never silently substituted for the verifier.

The trust base — six rows, and the audit harness asserts the theorem's axiom set is **exactly**
this (`scripts/run_audit.sh` reproduces the census):

| # | Trusted | Form |
|---|---|---|
| 1 | Lean kernel + `propext` / `Classical.choice` / `Quot.sound` | axioms |
| 2 | `Lean.ofReduceBool` / `trustCompiler` (bv_decide on byte-extraction lemmas; the conformance battery) | axioms |
| 3 | ArkLib knowledge soundness for LogUp GKR, zero-check, PCS, commitments, and Fiat–Shamir; in particular extraction of exact non-wrapping natural interaction multiplicities | dependency theorem + explicit error bound |
| 4 | `sailPlatformSurface` — the LeanRV64D platform bundle (~76 axioms: softfloat hooks, reservation set, terminal writes; the RV64IM integer paths touch 4) | named `List Name`, gate-enforced |
| 5 | the Rust→Lean constraint extractor | outside Lean; byte-identical regeneration gate at the pinned SP1 commit |
| 6 | `populate` conformance | tested (native_decide @ KoalaBear), quarantined test library, never imported by proofs |

**The gap ledger is empty.** The audit allowlist contains no `sorry`; every obligation of
the three capstone theorems are theorems of the six-row base above.

## 2. What sits under us: the configuration, and the Sail seam

This section is written **up to what a reader who knows the dependencies knows**: it states the
config we impose and the local notions we define on top, and defers to the dependency for its own
semantics. A Sail-familiar reviewer should be able to audit the RISC-V connection from the constants
listed here alone; a Lean reviewer should be able to audit the config block and the guarantees the
proofs run under. Nothing below re-derives the RISC-V ISA or the Clean channel calculus.

### 2.1 The global Lean configuration (the audit surface)

Every theorem is generic over a prime field, under one standing variable block; the machine layer
adds one larger bound (needed to decode field-encoded clocks/addresses into ℕ without wraparound):

```lean
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]   -- the standing block
-- the ensemble/engine additionally assumes a `Fact (2 ^ 25 < p)`-class bound
```

It is instantiated only at SP1's production prime (BabyBear / KoalaBear), which satisfies both with
margin. Pins and gates, all machine-checked by `scripts/run_audit.sh`:

- **Toolchain**: `leanprover/lean4:v4.31.0`, mathlib `v4.31.0`, Clean pinned to a released 4.31-compatible
  revision, and the two
  `succinctlabs` Sail forks (`sail-riscv-lean` carrying the platform delta below + `riscv-lean`),
  which pull `LeanRV64D` and `lean-sail`.
- **Trust gates**: the main `SP1Clean` library is `native_decide`-free and `skipKernelTC`-free (both
  CI-scripted); `Extracted/` regenerates byte-identically at the pinned SP1 commit.

### 2.2 The reference semantics and the platform configuration

The reference semantics is **LeanRV64D** — the Lean translation of the official RISC-V Sail model,
consumed as an external dependency and **never modified** beyond a disclosed platform configuration.
That configuration *is* the RISC-V seam a Sail reviewer audits; it is exactly SP1's execution
environment, in two pieces:

- **Compile-time (fork constants, in `sail-riscv-lean`):** `plat_have_clint = false` (no CLINT
  timer/software-interrupt device), `plat_have_sig = false` (no HTIF signature output),
  `sys_pmp_count = 0` (no PMP entries).
- **Per-state (`SailState.isValidMemConfig`, the initial platform mode — a clause of the `SP1Boot`
  precondition, exhibited by the canonical loader in §2.3):** M-mode (`cur_privilege = Machine`),
  MPRV off (`mstatus[17] = 0`),
  Zicfilp landing-pads off (`mseccfg[10] = 0`), **pointer-masking off (`mseccfg[33:32] = 0`)** — the
  one constant added during the 4.30/Sail-generation update, faithful (SP1 has no PMM) — HTIF tohost
  unset, and a single uniform main-memory PMA region `[2^16, 2^48)` with no atomics/reservations.

Beyond these constants, the model runs unaltered. The platform bundle (trust row 4) is the ~76
platform hooks the Sail model declares as axioms; the theorem statement ranges over the full
interpreter so it imports the bundle, and the RV64IM integer paths this project executes touch
exactly 4. The full list is the named constant `sailPlatformSurface` (`docs/snapshots/axiom-census.txt`),
gate-enforced.

### 2.3 What "really executes" means — local notions over Sail's own driver

`SailStep`/`SailChain` are **this project's** thin wrappers; we add no semantics, only iteration.
`try_step` is LeanRV64D's own top-level driver — interrupt dispatch, fetch, decode, execute, PC
commit — and we defer to it entirely for what a step *computes*:

```lean
def SailStep (s s' : SailState) : Prop := ∃ b, (try_step 0 false).run s = .ok b s'  -- one real step
inductive SailChain : ℕ → SailState → SailState → Prop | refl … | step …             -- n steps
```

Nothing is bypassed or re-implemented — the theorem's execution chain is the interpreter anyone else
can run. `SP1Boot prog s0` says `s0` has the program image loaded at its link addresses, PC at the
entry point, registers zeroed, and the platform configured as in 2.2; it is satisfiable by
construction (`SP1Boot.canonical prog` exhibits the loader state), so the ∀-form is demonstrably
non-vacuous. `SP1Halted prog exit s_f` says `s_f` is about to execute the halting `ECALL` (PC at an
`ECALL` word in ROM, syscall id HALT in `t0`/x5, exit code in `a0`/x10) — the chain stops one step
before the ECALL, because SP1's `ECALL` is an execution-environment halt, not RISC-V's privileged
trap, so it is *observed* against the unmodified model rather than simulated.

**The decode boundary is a per-program theorem, not an assumption.** A `GuestProgram` carries its
ROM together with a **decode certificate**: for each ROM word, the real generated decoder
(`ext_decode`), in every configured state, returns one fixed instruction whose column-projection is
the committed program row. For any concrete program the certificate is *proven by kernel reduction*,
word by word (the branch-skip reduction of the real decoder; the generator is mechanical), so no
decode fact enters the trust base. Two structural theorems back it: the row projection is injective
on the decoder's image (only canonical multiply-operand records and widths in {1, 2, 4, 8}; no LDU),
and decode determinism follows from that injectivity — both machine-checked, neither trusted.

## 3. The four buses

Chips communicate over four plain Clean channels; global soundness reduces to per-key balance
(LogUp). One rule governs all four: **the channel guarantee is the posted message's *hygiene* —
what the poster's byte checks establish, provable row-locally by both sides — and each bus's global
meaning is a theorem of the engine (§5) about every balanced trace.**

| Bus | Message (arity; SP1 kind) | Channel guarantee (row-local hygiene) | The semantic theorem (engine-proved, per balanced trace) |
|---|---|---|---|
| State | `(clk, pc)` (5; State) | clk decodability bound + pc-limb bounds | `StateTruth` at every key: the committed program's execution is at this (clk, pc) |
| Program | instruction row (16; Program) | `RowSpec` (structural decode bounds) | every fetched row is the decode of ROM[pc] |
| Memory | `(addr, time, value)` (9; Memory) | `isU64` value + timestamp bound + address shape | value currency: a read returns the most recent write at the read's timestamp |
| Byte | `(op, a, b, c)` (4; Byte) | `ByteRowSpec` (table membership) | — (already row-local: the guarantee *is* the meaning) |

**State** is SP1's execution-threading token: each row pulls "(clk, pc)" and pushes
"(clk + Δ, next_pc)" — Δ = 8, or `8 + 256 = 264` for syscall rows — and balance forces every sent state to be
consumed exactly once. That balance structure is how one sequential execution decomposes across
independent tables, and the engine's time-ordered induction turns it back into one real execution;
the per-chip obligation (§4) is exactly "my row advances it one step". **Program** rows are pushed
only by the preprocessed ROM provider, whose rows are the decode of the committed program by
construction (§2). **Memory** carries only hygiene on the channel; its currency theorem never
appears in the final statement. **Byte** is the root of well-formedness: every range fact bottoms
out in a preprocessed-table membership.

Sign convention, stated once: SP1's Rust *sends* with positive multiplicity where Clean consumers
*pull* (multiplicity −1) on Program and Memory; the emitted interaction lists equal SP1's extracted
oracle up to that negation — checked per chip, not assumed (§6).

## 4. One chip, end to end: Add

Every chip passes the same five gates. For `AddChip` (SP1's `add_sub` AIR):

| Gate | Artifact | What it pins |
|---|---|---|
| extract | `Extracted/ChipOracle/Add.lean` (auto-generated) | chip-namespaced Rust row + complete assert/interaction lists, rendered from SP1's constraint compiler |
| faithful | `Faithful/AddChip.lean` | circuit constraints ⟺ the extracted asserts (logical equivalence); emitted interactions ≐ SP1's oracle, all four buses (list permutation) |
| sound | `Proofs/Chips/AddChip/Formal.lean` | constraints ⟹ the chip contract `Spec` |
| decode | the Program pull + the row inversion | the row's operands are the fixed decoded instruction's operands |
| advance | `Proofs/Chips/AddChip/Bridge.lean` | one real `try_step` from any state matching the row produces the row's committed effect |

The chip's `main` composes the shared readers (CPUState, RTypeReader, RegisterWrite) and the add
gadget as true Clean subcircuits, returning its independent native row. One explicit
native-to-Rust `reconfigure` map is the only column-layout bridge; extraction never generates the
native circuit. The two per-chip statements, verbatim:

```lean
-- the contract (soundness conclusion), stated against the RV64 ISA function:
Spec : … ∧ (input.is_real = 1 →
  Word.toBitVec64 cols.add_operation.value
    = RV64.add (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val))

-- the uniform Sail-step obligation every chip registers (the same shape for all 26):
advance : is_real = 1 → chipSpec inp cols data → Ready r prog s → OperandCurrency r s →
    ∃ s', SailStep s s' ∧ RowEffect prog r s s'
```

`RowEffect` is the faithful per-row effect model: the PC transition, at most one register write, at
most one contiguous memory write, everything else framed — the three orthogonal axes of the Sail
machine state. `Ready` is one fixed structure (adapter passthrough, routing, pc-limb bounds),
discharged once at trace level, identically for every chip; no chip carries bespoke side
conditions. Adding a chip means: extract its columns, compose its `main`, prove its `Spec`, give
its `advance` over the per-format core — and never touch the capstone.

## 5. The ensemble, and how the proof feeds out to chips

`sp1Ensemble prog` bundles the tables — the 26 instruction chips plus the providers (byte/range,
the program ROM for `prog`, memory init/finalize) — over the four channels, with one boundary
verifier that pulls the final state and pushes the initial state committed in the public values.

The soundness engine (`Soundness/TimedGrounding.lean`) grounds every bus's semantic theorem by one
well-founded induction over the balanced channels, in time order:

> Pop the row whose state-pull carries the minimal timestamp. Balance forces that pull to equal the
> running head of the execution — no other row can match it, and around any would-be cycle the
> timestamps strictly increase, so no cycle closes. Per-address balance forces its memory pulls to
> equal the live frontier: the most recent write to each address. Its `advance` fact then fires —
> one real `try_step` extends the execution — the frontier updates, and the row's pushes become
> true facts for whoever consumes them next. Repeat until no rows remain; the final boundary pull
> now carries `StateTruth` of the committed final (clk, pc), which is the theorem's conclusion.

The per-chip interface to that induction is exactly the `advance` obligation of §4: one generic
adapter (`stepFact_of_advance`) converts every chip's `advance` into the engine's per-row step
record, so the capstone is chip-count-agnostic. Between the Clean `Statement` and the engine's
inputs sit two proven translations: deterministic typed witness decoding plus its grounding theorem
(`supported_core_witness_grounding` now proves exact ordering, PC/clock projection, and static
grounding; its one dependency `supportedCore_orderedRows_dynamic` supplies the remaining timed row
facts) and the typed-multiset balance bridge (Clean's
`BalancedInteractions` lifted to per-key message-multiset equalities). The whole path from
"verifier accepts" to "Sail halts with the committed exit code" is theorems of the six-row base.

## 6. Faithfulness: the circuit is SP1's circuit

Two independent anchors tie the Lean circuits to SP1's Rust, per chip:

- **Constraints.** `update_extracted.py` renders SP1's constraint-compiler output into
  `Extracted/` (auto-generated, hand-editing forbidden, byte-identical regeneration checked at the
  pinned SP1 commit). `Faithful/<Chip>.lean` proves the extracted assert list holds **iff** the
  native circuit's composed contract does — logical equivalence, not resemblance.
- **Interactions.** The circuit's *emitted* channel interactions and SP1's extracted interaction
  list project to the same `(kind, table, values, signed multiplicity)` tuples — a list permutation
  per chip, **all four buses, all 26 chips, full equivalence**, with no semantic interpretation in
  the statement. The anchors are macro-derived from two bundled hypotheses per chip; the syntactic
  form replaced an earlier semantic interpreter and, in doing so, caught a real slot-ordering bug
  the semantic form had masked.

## 7. Witness tests: the prover side, checked against the real prover

Soundness lives entirely in §4–§6. Independently, the honest-prover path is conformance-tested:
the circuits' own witness closures, run on event batteries dumped from SP1's real Rust prover,
reproduce SP1's `generate_trace` matrices cell for cell — column order, padding, and the
hint-driven variant flags included — **for all 26 chips**. These checks use `native_decide`
(compiler-trusted evaluation) at SP1's production prime and are therefore quarantined in a separate
test library (`SP1CleanTest`, built by `lake test`) that the proof library never imports;
`lake build SP1Clean` is `native_decide`-free by CI gate.

## 8. Boundary of the claim, and how to audit it

Modeled: the Supervisor-mode RV64IM instruction chips including ECALL/HALT (53 of 53 SP1 opcodes
routed), single shard, the four buses, the committed program/exit boundary. **Not modeled**:
multi-shard composition, precompiles, page protection, traps beyond the halting ECALL, the
User-mode duplicate AIRs, and the cryptographic lookup argument itself (trust row 3).

To audit: `scripts/run_audit.sh` — re-checks the toolchain pins, the empty `sorry` allowlist, the
`native_decide`/`skipKernelTC` gates, and regenerates the axiom census that backs §1's trust table,
including exact-set gates on `sp1_air_sound`, `sp1_execution_sound`, and `sp1_verifier_sound`.
The extraction currency check re-renders
`Extracted/` at the pinned SP1 commit and diffs byte-for-byte. Every claim in this document is a
named theorem you can `#print axioms`.

---

## Appendix: the instruction formats

One row per RISC-V format; each cell is a checkable artifact (the ast column is a decode-projection
equation; the advance column is one generic core lemma).

| Format | Chips | Adapter (reader) | Program-bus pin | Sail ast | Advance effect | Quirks |
|---|---|---|---|---|---|---|
| R | Add, Sub, Bitwise, Lt, ShiftL/R, Mul, DivRem | `RTypeReader` (rs1/rs2 reads + rd write) | opcode, `imm_c = 0` | `RTYPE (rs2, rs1, rd, op)` | pc+4; rd ← op(rs1, rs2) | W variants via `RTYPEW`; Mul's canonical-operand image guard |
| I | Addi + immediate arms of Bitwise/Lt/Shift | `ITypeReader` / `ALUTypeReader` | opcode, `imm_c = 1` | `ITYPE (imm, rs1, rd, op)` | pc+4; rd ← op(rs1, imm) | ADDIW shares ADDW's opcode, split by `imm_c` |
| Load | LB/LH/LW/LD (+ LoadX0) | I-shape + `MemoryAccess` | opcode | `LOAD (imm, rs1, rd, u, w)` | pc+4; rd ← ext(mem[rs1+imm]) | width ∈ {1,2,4,8}, no LDU (decoder image); x0 routes to LoadX0 |
| S | SB/SH/SW/SD | I-immutable shape + `MemoryAccess` | opcode | `STORE (imm, rs2, rs1, w)` | pc+4; mem[rs1+imm] ← rs2 bytes | alignment for wide stores; ROM/data disjointness |
| B | Branch | I-immutable (`op_a` is a *source*) | opcode | `BTYPE (imm, rs2, rs1, op)` | pc ← taken ? pc+imm : pc+4; no write | the no-write control axis |
| U | UType (LUI/AUIPC) | `JTypeReader` shape | own opcodes | `UTYPE (imm, rd, op)` | pc+4; rd ← imm-form | 20-bit immediate reconstruction |
| J | Jal, Jalr | `JTypeReader` / `ITypeReader` | opcode | `JAL` / `JALR` | pc ← target; rd ← pc+4 | JALR clears the target LSB |
| Sys | Halt (ECALL) | state-only | opcode | `ECALL` | terminal; clk + 256 | the boundary chip; exit code in `a0` |

Each format's generic advance core (`advance_of_<format>`) is proved once over the `try_step`
ladder; a chip's `advance` is a thin instantiation. The reader set mirrors SP1's Rust adapters
one-to-one; the format distinction enters through the decode projection, not through new columns.
