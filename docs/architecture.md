# Architecture

## The thesis

`sp1-clean-native` verifies SP1's RISC-V chips by writing **semantic** Clean circuits whose arithmetic is
**re-derived natively**, then anchoring each complete chip to both the RISC-V Sail spec and SP1's complete
chip AIR.
This is the opposite of the `sp1-lean`/`SP1Clean` approach, which writes *structural* specs (restatements of the
constraint list) and *borrows* the arithmetic and Sail semantics from `SP1Operations`/`SP1Chips`.

The Add worked example (recorded in `SP1Clean/Comparison.lean`) closes all of this end-to-end,
axiom-clean, and comes out **comparable or smaller** than the borrowing structural version while being
self-contained. The Bitwise chip reproduces the pattern at full parity. The pattern is the product; new chips
are scale-out.

## Whole-machine theorem stack

The circuit and proof-system boundaries are intentionally separate:

1. Plain Clean channels enforce structural interaction equality. State records `(clock, pc)` edges;
   Program records decoded fetch rows; Memory records timestamped locations and values; Byte records
   finite lookup facts. State does not locally assume reachability and Program does not locally assume
   ROM commitment.
2. `Soundness/TimedGrounding.lean` interprets balanced records in time order. Its current proved scope is
   the ordinary, register-only slice; RAM, repeated touches, state bumps, and syscalls are explicit open
   generalizations.
3. `Model/Machine/{Boot,Schedule,Execution}.lean` defines the native semantic machine. A fixed
   `SP1MachineModel` chooses the loader and opcode-dependent timing policy, so neither can be selected by
   the proof witness. PolyFun's `DynSystem.Machine` packages the official Sail `try_step` trajectory; it
   is not used in circuit construction.
4. `FormalModel/Relations.lean` states AIR soundness as witness-producing refinement. The currently
   honest native target is `supported_core_native_sound`; the former headline is now
   `balanced_state_trail_soundness`, accurately naming its Eulerian interaction conclusion. The name
   `supported_core_air_sound` is reserved for native/extracted faithfulness, and `sp1_air_sound` for a
   faithful relation over the complete upstream shard AIR and `SP1PublicValues`. Native shard soundness
   first ends in a local Sail segment; `supportedCoreLocalExecution_anchors` places it in the canonical
   boot trajectory once shard composition proves the initial state was reached. `SP1ExecutionRelation`
   composes consecutive anchored shards into boot-to-halt execution.
5. ArkLib owns probabilistic verifier knowledge soundness. `FormalModel/Verifier.lean` provides the
   dependency-free extractor/refinement seam; a future ArkLib adapter will state `sp1_verifier_sound` by
   post-processing an extracted AIR witness through `sp1_air_sound`.

This factorization prevents an algebraic trail, a Sail execution, and verifier acceptance from being
presented as the same claim.

The supported machine census is `Soundness/SupportedMachine.lean`: each entry owns its Clean table,
semantic `ChipKind`, opcodes, and `rd` guard. `allChipKinds`, `sp1Tables`, `coverage`, and routing are
projections of that descriptor rather than independently maintained lists. `RankedGrounding.lean` proves
the generic structural upgrade from a balanced subtrail to an exhaustive trail when every edge strictly
increases its clock rank, ruling out disconnected balanced cycles.

`WitnessDecode.lean` deterministically decodes each typed circuit table; no capstone theorem may
existentially choose unrelated rows or casts between flat components. `LocalExecution.lean` proves that
an ordered list of retained physical rows whose semantic projections are grounded in their evolving
states constructs a genuine Sail chain by dispatching through each registered chip's `advance`. Ranked
State balance now constructs an exhaustive order of exactly `realDecodedInstructionRows`; its PC walk,
clock count, activity, registry membership, and committed Program decode are proved. The one remaining
semantic bridge is `supportedCore_orderedRows_dynamic`: it must derive each row's timed Memory
guarantees, circuit assumptions, operand currency, and readiness in the corresponding Sail state.

The dynamic bridge reads the circuits' interactions through a typed adapter, not through the older
hand-written `memoryLookups` projection. `TypedInteractions.lean` retains each exact evaluated Clean
interaction and recovers its channel message; `TypedMemory.lean` turns the active Memory pulls into
timed row facts and live-register bindings. A chip supplies only an exact operand-pull shape over its
own `exposedChannels` list. Add is the first complete descriptor instance in
`TypedMemoryContracts.lean`; extending the registry is structural scale-out, while RAM and repeated
same-location scheduling remain grounding-engine work.

Whole-machine completeness is the converse `WitnessRelation.Complete`, not Clean circuit soundness and
not opcode coverage. It may remain a disclosed top-level `sorry` while the verified trace generator is
built. Upstream Clean remains unchanged; this project continues to use its existing
`GeneralFormalCircuit`/`Ensemble` packaging.

## The chip-centered verification chain

The stable Rust/Lean boundary is a **whole chip**, not a Rust operation. Rust operations and Lean gadgets
serve complementary purposes and may use different structs, intermediate values, carry decompositions, or
subcircuits. A local gadget remains a useful proof abstraction, but refactoring it must not require changing
the extraction contract.

For a chip `<Chip>`:

1. **Native semantic implementation.** `Native/Operations/` contains proof-oriented Lean gadgets and
   witness functions. `Native/Chips/<Chip>/Defs.lean` composes those gadgets and readers into one native
   row type and one `main`. `Proofs/Operations/` may prove local semantic lemmas; these are implementation
   details, not faithfulness anchors. The chip's `GeneralFormalCircuit` soundness/completeness theorem is
   stated against the semantic contract in `FormalModel/Contracts/Chips.lean`.
2. **ISA bridge.** `Proofs/Chips/<Chip>/Bridge.lean` derives the relevant Sail step from the chip's semantic
   `Spec`. This proves what the native row means independently of the current Rust helper decomposition.
3. **Whole-chip Rust AIR anchor.** Extraction produces the complete Rust chip row plus its `asserts` and
   `interactions` lists. `Faithful/ChipOracle.lean` supplies the common boundary:
   `ChipOracle.reconfigure` is the one explicit map from the native row to the Rust row, and
   `ChipFaithful` proves (a) extensional equivalence of the two complete assertion systems and (b) equality
   up to permutation of the complete four-bus interaction multisets. Helper operations emitted inside the
   Rust expression may be unfolded locally by this proof, but no helper-level theorem is exported.
4. **Populate/trace conformance.** `SP1CleanTest/TraceGenTests/` derives complete rows from the native chip's
   own witness closures and output struct and compares them with traces dumped from Rust
   `generate_trace`. These executable anchors catch layout, population, padding, and hint-routing drift;
   they complement rather than replace the kernel-checked `ChipFaithful` theorem.

`AddChip` and `SubChip` are the pilots for this boundary. Their native `Columns` no longer alias Rust
rows, their self-contained Rust oracles live under `Extracted/ChipOracle/`, their gadgets no longer
import generated direct-to-circuit artifacts, and `addChip_faithful` / `subChip_faithful` package the
complete assertion and interaction comparisons. Performing the Add whole-chip comparison exposed a
real gap: Rust asserts `op_a_0 = 0` for routing, while the native chip previously carried it only as a
prover assumption. It is now a verifier-enforced chip constraint.

### DivRem as the heavy-duty contract test ground

`DivRemChip` deliberately uses a two-stage semantic boundary rather than eight giant circuit proofs:

1. `FormalModel/Contracts/DivRem.lean` defines the stable public vocabulary: four arithmetic families,
   quotient/remainder output routing, the eight committed opcode selectors, unique real-row selection,
   `PairSpec`, `CaseSpec`, and `RowSpec`. The RV64 definitions themselves cover divide-by-zero and signed
   overflow, so neither behavior is hidden in an assumption.
2. `Proofs/Chips/DivRemChip/Cases.lean` is independent of the chip circuit and Clean elaboration. It gives
   explicit Euclidean evidence for unsigned families and explicit `normal`/`divisorZero`/`overflow`
   constructors for signed families, proves each family determines both quotient and remainder, and then
   proves a small routing lemma for each selected opcode.
3. `DivRemChip.evidenceSoundness` is the sole heavy whole-chip arithmetic seam: generated constraints must
   yield reader behavior, unique selection, one of those family evidence values, and the final routing
   equality. `contractSoundness` and public `soundness` are proved from it. The former nine per-op circuit
   proofs and their shared tail were retired (about 5,600 lines) rather than retained as dead, misleading
   proof debt.

This split is the intended pattern for future complex chips: isolate pure semantic evidence, keep row-offset
and subcircuit extraction in one chip-level conformance theorem, and never make the machine layer depend on
the proof decomposition.

The remaining generated operation modules, direct circuit forms, operation witness vectors, and
`Faithful/<Operation>.lean` files are **migration debt**. They may remain temporarily where an unmigrated
chip proof imports them, but new work must not add operation-level faithfulness APIs. Delete each artifact
once every consuming chip has a native row reconfiguration and a whole-chip `ChipFaithful` anchor.

Each new module's import goes into the root `SP1Clean.lean`.

## Trace Generation (`SP1CleanTest/TraceGenTests/`)

Partially deriving SP1's `generate_trace` from the circuit definition.
`SP1CleanTest/TraceGenTests/TraceGenerator.lean` (axiom-clean,
generic): `circuitTraceRow` seeds Clean's `FlatOperation.dynamicWitnesses` env-threading fold with
one row's input column values, runs `main`'s own witness closures in emission order, then evaluates
`main`'s **output struct** under the final environment — the output layout *is* the row layout, so
nothing about column order, witness formulas, or wiring is restated; `generateTrace` adds SP1's
zero padding. The only hand-written remainder is the event → input-column extraction
(`EventPopulate.lean`, a direct ℕ transcription of SP1's `CPUState::populate` /
`RTypeReader::populate` / `ALUTypeReader::populate` / `RegisterAccessTimestamp::
populate_timestamp`). The `<Chip>TraceWitness.lean` anchors `native_decide` that the derived
matrix equals, cell-for-cell, whole traces dumped from SP1's **real** `MachineAir::generate_trace`
(`<Chip>TraceVectors.lean`, regenerated by `update_extracted.py` pass 2d / the
`witness_vectors --chip` mode) — covering witness formulas, env wiring, emission order, full
column layout, and padding at once; the per-`populate` vector anchors check only the witness
formulas pointwise.

This trace-gen layer and the transitional per-operation `populate`-conformance layer (`WitnessTests/`)
both live in the **top-level `SP1CleanTest` test library** (the `lake test` target), *not* the main
`SP1Clean/` tree. New coverage belongs in the whole-chip trace layer; remove an operation battery once
no unmigrated chip relies on it. The reason for test-library isolation is `native_decide`: the
`<Chip>TraceWitness.lean` / legacy `<Op>Witness.lean`
anchors are the project's only uses of it (it trusts the whole compiler, adding
`Lean.ofReduceBool`/`Lean.trustCompiler`), so the entire layer — anchors, the `Conformance.lean` /
`EventPopulate.lean` concrete-prime scaffold, and the auto-gen `<Chip>ChipTraceVectors.lean` /
`WitnessTests/Vectors/<Op>.lean` batteries — is quarantined in a library that imports `SP1Clean` but
is never imported by it. `scripts/check_no_native_decide.sh` keeps the main build clean. (Because the
vectors travel with the anchors, the old "can't split the vectors into `Extracted/` without inverting
the pillar layering" tension is moot — the whole test layer is one self-contained library.)

Status (10 chips, 44 events + 20 padding rows each, **all unmasked** — every column of every
covered chip is compared cell-for-cell):

- Fixed-witness chips: `AddChip` (33 cols), `SubChip` (33), `SubwChip` (32 — the W-result
  value/msb witness pair), `AddwChip` (36 — the first `ALUTypeReader` adapter trace,
  register-`c` events).
- **Hint-driven-flag chips** (the variant selector flags are witnessed from a per-chip
  `ProverHint` key — `"mul_flags"`/`"div_rem_flags"`/`"bitwise_flags"`/`"lt_flags"`/
  `"shift_left_flags"`/`"shift_right_flags"` — and the anchor builds the per-event hint from the
  dumped executor opcode, the `*Op` event kinds): `MulChip` (82; all five variants),
  `DivRemChip` (246; DIV/DIVU/REM/REMU + the W variants), `BitwiseChip` (51;
  XOR/OR/AND), `LtChip` (44; SLT/SLTU, **immediate-`c`** events — `LtChip`'s compare operand is
  `adapter.op_c`, which on register rows is the register-index word, a scoped adapter-projection
  gap independent of the flags), `ShiftLeftChip` (65; SLL/SLLW × register/immediate, the shift
  amount swept over every byte/bit shift), `ShiftRightChip` (69; SRL/SRA/SRLW/SRAW ×
  register/immediate). The shift chips pad with SP1's non-zero `padded_row_template`
  (`v_* = 1/1/1` resp. `16/256/65536`), reproduced by the circuits' own zero-input/empty-hint
  derived row (`generateTrace`'s `padRow` parameter).

The former masked-flags scope gap is closed: the five flag chips' completeness proofs are stated
against the same hint-driven closures the anchors test. Reasoning hook for later: under
`Circuit.ComputableWitnesses`, the derived environment agrees with `Operations.localWitnesses` at
the fixpoint env (`Circuit.proverEnvironment_usesLocalWitnesses`), the bridge from this sampled
conformance to the chips' completeness theorems.

## The spec layer (`FormalModel/Contracts/`)

The `Inputs` structs and semantic `Spec`s for **every** circuit are consolidated into the
`FormalModel/Contracts/` audit surface (the base `Reader → Operation → Chip` sequence plus focused
contract modules for unusually rich chips), so the whole spec surface
is auditable in one place and depends only on `Math/`/`Model/` + `Extracted/` (never on the proof files):

- **`FormalModel/Contracts/Readers.lean`** — the reader `Inputs`/`Spec`s (`CPUState`, `RTypeReader`, `RegisterAccessCols`,
  `RegisterAccessTimestamp`).
- **`FormalModel/Contracts/Operations.lean`** — the operation gadgets' `Inputs`/`Spec`s, plus the pure result helpers a
  `Spec` directly needs (`resultWord`, and Mul's `productVal`).
- **`FormalModel/Contracts/Chips.lean`** — the chip `Inputs`/`Spec`s. Each chip states its headline identity against the
  **RV64 ISA function** from `RISCV/Instructions.lean` (`RV64.add`/`sub`/`addw`/`subw`/`and`/`or`/`xor`).
  ADD/SUB and the bitwise ops are *definitional* (`RV64.add rs2 rs1 := rs1 + rs2`); ADDW/SUBW go through
  the `rv64_addw_eq`/`rv64_subw_eq` truncation lemmas (also here), used by the chip soundness proofs and
  the W-bridges.
- **`FormalModel/Contracts/DivRem.lean`** — the focused DivRem family/selection/case vocabulary consumed
  by `DivRemChip.Spec`; separated so arithmetic cases can be audited without importing the circuit proof.

Each declaration keeps its **original namespace**, so the proof machinery (`main`, `elaborated`, the
structural `RawSpec`, soundness/completeness, `circuit`) stays in the per-circuit file and resolves the
moved `Inputs`/`Spec` by name after `import SP1Clean.FormalModel.Contracts.<Readers|Operations|Chips>`. The `RawSpec`s
stay with the proofs that consume them, not in `FormalModel/Contracts/`.

## Chip conventions (non-negotiable; standardization pass 2026-06-07)

These keep every chip uniform and each `Spec` auditable on its own. Violations are bugs.

1. **Operands are adapter projections, never committed `Inputs` columns.** An `Inputs` struct carries
   only `{is_real (or selectors), state, adapter}` plus genuinely-extra witnesses (e.g. Store's
   `store_value`, Load's `offset_bit`/`selected_*`/`msb`). The operand words are `@[reducible]`
   projections off the adapter — `Inputs.op_b_val := i.adapter.op_b_memory.prev_value`,
   `Inputs.op_c_imm := i.adapter.op_c_imm`, `op_c_val := i.adapter.op_c_memory.prev_value` (or
   `i.adapter.op_c` for the ALU adapter). This makes the chip's operand *definitionally* the value the
   Memory bus pins — no free column, no extra equality constraint. (Soundness/completeness unfold the
   projection with `simp only [Inputs.op_b_val, …]` right after `circuit_proof_start`.)
2. **Each `Spec` is self-contained on the `FormalModel/Contracts/` audit surface.** No shared chip-spec *builder* (the old
   `RTypeChipSpec` was inlined per chip and deleted) — a reader audits one `Spec` without chasing a
   shared abstraction. The `Spec`, its `Inputs`, and the helper defs the `Spec` *directly* references
   live together there; a focused contract module such as `DivRem.lean` is appropriate when it exposes a
   named semantic algebra rather than hiding constraint structure. Helpers used only by `main`/`Defs` live
   in `Native/Chips/<Op>Chip/Defs.lean`.
3. **Variant flags live in the `cols` column struct, read from `cols` in the `Spec`** — never duplicated
   as `Inputs` fields. (`main` witnesses them; the flag-sum gate binds `is_real = Σ flags`.)
4. **Range checks go through the byte bus, not `Gadgets.ToBits.rangeCheck`.** A width-`n` range check is a
   `byteChannel.pullIf <gate> (⟨6, value, n, 0⟩ : ByteRow …)` (`ByteOpcode 6 = Range`), matching
   SP1's extracted `Range(n)` send. Soundness consumes the `byteChannel.Guarantees`/`ByteRowSpec`
   guarantee (via `byteRowSpec_range`); completeness proves it the same way. (AddressOperation's offset
   check uses this; `Gadgets.ToBits.rangeCheck` bit-decomposition is *not* faithful to SP1.)
5. **Extra files in a chip directory only for `Core.lean` (inlined arithmetic kernel reused by
   soundness+completeness), `Math.lean` (pure `BitVec`/`RV64` lemmas), or a `Soundness/` subdir (proof
   decomposition)** — justified only when a chip's inlined arithmetic would blow the heartbeat/LSP budget
   in `Defs`/`Formal`. Fold one-off names into these unless genuinely reused; fold conservatively
   (the splits exist to avoid timeouts).

## Layout (mirror-rust)

```
SP1Clean/
├── Math/           Word, Bitwise, Misc, MulCarryChain, HWord,   (general math, no SP1/Sail deps —
│                   GetElemFastPath                                the upstreaming candidate)
├── Model/          Register, SailWrap, SailMemory, Channels,     (SP1 substrate: Sail wrappers +
│                   InteractionBus/Projection/Recovery, ChipAir,   structural buses + byte table;
│                   SP1Constraint, ByteTable, Machine/{Boot,        native boot/schedule/execution)
│                   Schedule,Execution}
├── Extracted/      ChipOracle/<Chip>.lean (chip-namespaced Rust  (PILLAR 1 "extracted from Rust" —
│                   row + complete asserts/interactions); legacy   auto-generated, do NOT hand-edit;
│                   <Chip>Chip/<Op>/Circuit helper artifacts       regen via update_extracted.py)
├── FormalModel/    Contracts/{Readers,Operations,Chips,           (THE central audit surface — the
│                   PublicValues} (Inputs + semantic Specs),        "middle ground" between Extracted
│                   Relations, Execution, Verifier, Trace/          and the proofs)
├── Native/         Chips/<Op>Chip/Defs (main+elaborated),        (PILLAR 2 "implemented native" —
│                   Operations/<Op>/{Populate,RawSpec} + flat ops, circuit construction)
│                   Readers/ (reader sub-circuits)
├── Faithful/       ChipOracle + whole-chip anchors               (PILLAR 3 "proven faithful")
├── Proofs/         Chips/<Op>Chip/{Formal,Bridge,…},             (PILLAR 4 "proven sound/complete" +
│                   Operations/<Op>/Formal, Sail bridges; complex-chip proof decomposition such as
│                   DivRem/{Math,Cases,Assembly} and Shift soundness families)
├── Soundness/      {State,Byte,Program,Memory}Consistency,       (PILLAR 5 "whole-machine reasoning":
│                   ChipRow (`ChipKind`+`name`), ChipRegistry,      SP1Ensemble = balanced-trail
│                   GatedVm/, SP1Ensemble, TimedGrounding, AIR,     intermediate; TimedGrounding + AIR
│                   TargetVm,                                      own the semantic capstone;
│                   Opcode, Coverage, AIR, RowView                 Coverage = Opcode→chip→Sail table;
│                                                               AIR = relation-level capstone boundary)
├── Comparison.lean the worked-example findings doc — full rationale, no new proofs
└── Step0Smoke.lean
SP1Clean.lean  root index — import every module here

Lake libraries (lakefile.toml): umbrella `SP1Clean` (default target) + per-pillar build-targets
`SP1Math` / `SP1Model` / `SP1Extracted` / `SP1FormalModel` / `SP1Native` / `SP1Proofs` (submodule globs).
Namespaces are decoupled from paths (`SP1Clean.AddChip`, `SP1Clean.Word`), so moves don't change FQNs.
```

All circuits are field-generic: `variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]`.

## Design verdict

- **Semantic + native wins.** A witnessed `FormalCircuit` with a genuinely semantic spec, natively-proven
  arithmetic, composed into a `GeneralFormalCircuit`, reaches the RISC-V spec with **zero** coupling to
  `update_constraints.py` output, `SailBridge`, or borrowed `correct_*`. Add: ~394 op-specific lines (incl. the
  native arithmetic) + reusable `Math`/`Model`, vs sp1-lean's ~971 that still borrow arithmetic + Sail.
- **Completeness is provable here** because the gadget is *witnessed* with a *semantic* spec. (Pure-semantic
  specs over *free* combinatorial witnesses make completeness false — the witness is the thing being
  constrained. The witnessed gadget closes that gap.)
- **Reuse Clean's primitives.** Range via `Gadgets.ToBits.rangeCheck`; byte ops via Clean's proven
  `ByteXorTable` + opcode-selected Lagrange lookups — no custom SP1 byte-bus.

## Assertion vs `FormalCircuit` — the demotion decision

The Add worked example ("the chip witnesses the result via `populate`, the op is an assert-only `FormalAssertion`"
— `Native/Operations/AddOperation/`) generalizes to **some** ops but not all. The deciding test is whether **every
witnessed column is pinned by the *semantic* `Spec`**:

- **Spec-determined witnesses → clean semantic `FormalAssertion`.** `value = a+b` (Add/Sub), `msb = high
  bit` (U16MSB), `bit = (a<b)` (U16Compare), `value = sext32(a±b)` (Addw/Subw), `low_bytes = decomp`
  (U16toU8Safe) each *uniquely* fix the witnessed column, so completeness (∀ inputs satisfying `Spec`,
  constraints hold) goes through via the `<sem>_of_<raw>` / `<raw>_of_<sem>` core. **Demoted axiom-clean:**
  U16MSB, Sub, Addw, Subw, U16Compare; the Sub/Addw/Subw chips witness via `populate`
  and compose with `assertion …circuit`. (Addw/Subw additionally need a *converse* core
  `carries_of_{addw,subw}Semantics` — completeness of a FormalAssertion must reconstruct the sub-`assertion`'s
  Spec from the semantic Spec. See `agents/proof-patterns.md`.)
- **Auxiliary witnesses → keep it a `FormalCircuit`.** Ops with witness columns the semantic `Spec` does
  *not* determine — Lt's `u16_flags`/`not_eq_inv`, Mul's `carry`/`b_lower`/`c_lower`, Bitwise's
  `b_low`/`c_low` — make a *semantic* FormalAssertion's completeness **provably false** (an input with the
  right output but garbage aux cols satisfies the `Spec` yet breaks the constraints). They **stay
  `FormalCircuit`s**. When such an op composes a *demoted* sub-op it only switches that composition to the
  assertion interface (witness the bit/msb locally via `populate_*`, then
  `assertion <Sub>.circuit ⟨a, w, 1⟩`) while staying a circuit itself — done for `LtOperationSigned`,
  `LtOperationUnsigned`, `MulOperation` (which compose the demoted U16MSB/U16Compare).

The **"full send"** (make the aux-column ops assertions too) is *possible* but is an end-state architectural
choice, not a fix: it needs a **structural** op `Spec` (the `RawSpec`, pinning every column) with the
semantic theorem exposed at the chip — the more faithful mirror of SP1's `populate`/`eval` split — yet it
(a) downgrades the op `Spec` from semantic to structural (against the spec-layer principle), (b) does **not**
reduce the proof burden (a `FormalCircuit`'s completeness *is* "the populate witness satisfies the
constraints"; the full send just relocates it to `spec_populate`), and (c) needs a chip to own the
witnessing. Defer it until an op's completeness is actually proven (Mul's now is — axiom-clean).

## Interaction buses (the CPU-operation / table-interaction representation)

> See `bus-model.md` §0 for the authoritative
> status. **All four buses emit in-circuit** as Clean `Channel`s (`Model/Channels.lean`:
> `stateChannel`/`byteChannel`/`memoryChannel`/`programChannel`), composed axiom-clean through
> `Proofs/Chips/AddChip.lean`. **Receiver chips + cross-chip closure:** `Proofs/Chips/ByteChip.lean` +
> `Proofs/Chips/ProgramChip.lean` are native predicate-model providers (`ByteProvider`/`ProgramProvider`); the
> `*_of_balance` discharges in `Soundness/{Byte,Program}Consistency.lean` turn `Trace{Byte,Program}Link`
> into *(provider + `isConsistentBalanced`)*. **`Soundness/ProgramProviderSpike.lean` then *constructs* the
> Program provider** (`programProvider_of_validRom`) instead of assuming it, so
> `traceProgramLink_of_validRom_and_balance` discharges the fetch-membership link from just *(the committed
> ROM rows being validly decoded — `ProgramRowSpec` — plus `isConsistentBalanced`)*, isolating the residual
> to exactly the preprocessing/commitment trust of the ROM content (or a real decode Air whose range checks
> would bottom out one level down at the Byte bus; the Byte bus is the exact analog). (The bespoke `Soundness/MachineConsistency.lean`
> machine-closure `traceLinks_of_machineBalance` was retired with the bespoke `TraceValid` capstone; the
> gated capstone `Soundness/GatedVm/` derives the execution trail from the State-bus balance alone.) The Byte bus is
> received by two preprocessed chips (`ByteChip` ⊕
> `RangeChip`, no separate `Range` kind). **`emitted = projection`:** the hand-written
> `*Lookups` are *theorems* equal to the actual emissions for State, Program, and Memory
> (`{program,memory}Lookups_eq_emitted`, recovered through the composed `RTypeReader` by
> `Model/InteractionRecovery.lean`); only Byte's `eq_emitted` remains. **Byte faithfulness:**
> reader byte checks SP1 has no analog of (CPUState's 4 `pc`, `RegisterAccessCols`'s 4
> `prev_value`) are removed, so `StateMsg.Spec`/`RegisterAccessCols.Spec → True` and the readers emit exactly SP1's 8
> byte checks per Add row. **`TraceStateLink` (PC chain) is balance-derived** —
> `pcChain_of_balance_and_clkInj` discharges it from the State-bus balance + the trace-shape side conditions
> `clkInjective` + `TraceClkAdvance`; the gated capstone `gatedExecution_of_specs_and_balance` drops the PC
chain side conditions entirely, forcing the trail from the State-bus balance alone (Eulerian). Still threaded
> (the genuinely-hard math, exactly as `../sp1-lean` defers): `TraceMemoryLink` (offline-memory — the
> faithful encoding + `MemoryProvider` + balance-core `mem_opA_read_send_matched` are in place, but the full
> `isConsistentOnline_of_memBalance` derivation remains), and `isConsistentBalanced` (LogUp/GKR).

SP1's cross-chip interactions are a **multiplicity-weighted multiset bus**: each chip row contributes signed
`(kind, table_id, entry, multiplicity)` tuples to a typed bus (`State`, `Byte`, `Program`, `Memory`), and global
soundness reduces to "for every key the signed multiplicity sum is zero" (sends `+`, receives `−`). The
faithful representation has **three layers**, demonstrated end-to-end on the
**State bus / `AddChip`**:

1. **Row emission** — a `Native/Readers/<Reader>.lean` sub-circuit (`Native/Readers/{CPUState,RTypeReader}.lean`)
   **witnesses and returns its `Extracted` column block** while imposing exactly SP1's
   per-row checks, and the chip's `main` *composes it as a real sub-circuit*.
   `Native/Readers/CPUState.lean` is a **`FormalAssertion`** taking its `cols` block plus
   `next_pc`/`clk_inc` as **inputs**: the chip owns and witnesses the `state` block and forms
   `next_pc = [pc[0]+4, …]` from its own `cols.pc`, faithful to SP1's
   `CPUState::eval(cols, next_pc, clk_increment, is_real)`; its byte-bound `Spec` is *derived from the
   byte-bus pull* in soundness and *consumed* in completeness. `RTypeReader` and the immediate-capable
   `ALUTypeReader` are likewise **`FormalAssertion`s** taking their `cols` as inputs; the bus layer reads
   them through the reader-agnostic `Trace.AdapterView` projection. The
   checks are `is_real`-gated (range-check `is_real * value`, vacuous on padding) so real zero-padding rows pass,
   matching SP1's `is_real`-multiplicity byte sends; the chip `Spec` gains the reader's per-row facts as a direct
   sub-spec call. A reader whose column block is itself *deeply nested* is, in turn, **factored into composed
   sub-circuits** mirroring the struct nesting — `RTypeReader` composes three `RegisterAccessCols` (one per
   operand), each composing a `RegisterAccessTimestamp` carrying the two timestamp byte checks as inline
   `ByteTable` lookups. This keeps every proof at the default heartbeat floor (each block is a `circuit_norm`
   black box, no single circuit witnessing the 22-column tower); see `agents/proof-patterns.md` "Reader
   composition" for the recipe (omit `output`, inline the struct-projected lookups, the soundness/completeness
   shapes).
2. **Bus data** — `Model/InteractionBus.lean` is the reusable, axiom-clean multiset core
   (`multiplicitySum`, `isConsistentBalanced/Online`); a per-row projection (`Soundness/StateConsistency.lean`'s
   `stateLookups`) turns each row into its signed bus contributions.
3. **Trace consistency** — the bus's *meaning* across rows (e.g. the State bus's PC chain `next_pc[i] = pc[i+1]`,
   `pcChainProp`) plus boundary conditions. `Faithful/<Reader>.lean` anchors the row emission to SP1's generated
   `<Reader>.constraints`.

The deep soundness link *bus-balance ⟹ per-row property* (e.g. ⟹ `pcChainProp`) needs whole-trace
clock-injectivity reasoning. For the **State** bus this is **proven**: `pcChain_of_balance_and_clkInj`
derives `pcChainProp` from the State-bus balance plus two honest trace-shape side conditions (`clkInjective`,
`TraceClkAdvance`), so `TraceStateLink` is no longer threaded. For the **Memory** bus the analogous
`isConsistentOnline_of_memBalance` is still open (the balance-core `mem_opA_read_send_matched` is proven; the
full offline derivation + ordering side-condition remain), so `TraceMemoryLink` stays **threaded as a
hypothesis** — exactly as `../sp1-lean` ships it, an honest assumption, not a `sorry`/axiom.

## Design status & limitations

- **Native readers.** `Native/Readers/CPUState.lean` (State bus), `Native/Readers/RTypeReader.lean`
  (register reads + timestamp byte checks, scalar `op_c`), and `Native/Readers/ALUTypeReader.lean` (the
  immediate-capable adapter — `op_c : Word` + `imm_c`, op_c access gated `is_real - imm_c`) are **all
  `FormalAssertion`s** taking their committed `cols` block as an *input*. Add/Sub/Subw compose `RTypeReader`;
  the SLTU exemplar (`Proofs/Chips/Ltu{Chip,Bridge}.lean`) composes `ALUTypeReader`. The trace-level bus layer reads
  a **reader-agnostic `Trace.AdapterView`** that every reader projects into via `<Reader>.toAdapterView`
  (R-type ⇒ `op_c := #v[op_c, 0, 0, 0]`, `imm_c := 0`, so the op_c gating + Program/Memory tuples degenerate
  to the scalar shape), so the homogeneous `List RowView` and the `ChipKind` capstone carry both adapter
  kinds with no central edit (`Soundness.traceValid_addLtu_mixed` is the Add+SLTU acceptance test). Porting
  the remaining ALU chips (bitwise immediate variants, shifts, Mul) is the scale-out step;
  `agents/porting-recipe.md` is the recipe.
- **Control-flow chips (JAL + JALR).** The chips whose committed `next_pc` is *computed
  data* rather than the straight-line `pc + 4`. **`Proofs/Chips/Jal{Chip,Bridge}.lean`** (opcode 46, `JTypeReader`,
  two immediates): `next_pc = add_operation.value = pc + op_b_imm`, the jump target, plus a `pc + 4` link
  `AddOperation` gated additively by `is_real - op_a_0`. **`Proofs/Chips/Jalr{Chip,Bridge}.lean`** (opcode 47,
  `ITypeReader`, rs1 register + immediate): `next_pc = (rs1 + op_c_imm) & ~1` — the jump base is the
  **source register** value `adapter.op_b_memory.prev_value`, and a committed `lsb` witness (binary-gated)
  clears the target's low bit, the cleared limb `add_operation.value[0] - lsb` feeding `CPUState` and the
  `Range((add_operation.value[0] - lsb)/4, 14)` alignment send. Both register through the generalized
  `Soundness.ChipKind` (`view` threads the data-dependent `next_pc`, the reader projects through
  `<Reader>.toAdapterView`), whose `sailEquiv` quantifies the row's PC read, the register/immediate decode,
  `op_a_0`, alignment (and, for JALR, the rs1 read and the LSB-clearing relation `next_pc_word =
  BitVec.update (rs1 + sign_extend imm) 0 0#1`) internally — so the capstone consumes them generically with
  no central edit. The chip soundness/completeness + the `Faithful/Jal{,r}Chip.lean` assertion anchors are
  axiom-clean; each `correct_<op>_native` carries **one isolated, documented `sorry`** on the deep
  `execute_{JAL,JALR}` monad equivalence (the `jump_to` retire-under-alignment + `get_next_pc`/`set_next_pc`/
  `wX_bits` reduction), the only deferred step in the chain. The interactions-half faithfulness anchors are
  likewise deferred.
- **`x0`-destination chips (LoadX0 + AluX0 — fully axiom-clean).** SP1 routes any instruction writing `x0`
  (the hardwired-zero register) to a dedicated result-discarding chip — loads to `Proofs/Chips/LoadX0Chip/`, ALU ops
  to **`Proofs/Chips/AluX0Chip/`** — and `Soundness/Coverage.lean`'s `routeOf` keys on `(opcode, rd == x0)` exactly as
  `tracing.rs`. `AluX0` is the ALU analog of LoadX0, *structurally simpler*: no arithmetic gadget and no
  memory access (the result is thrown away), just `CPUState` + the new **`Native/Readers/ALUTypeReaderImmutable.lean`**
  (op_a a source *read*, not a write — the immutable sibling of `ALUTypeReader`) + an LTU `opcode < 29` range
  send + the `op_a_0` forcing gates. Its Sail bridge is the cleanest in the project: since the only state
  effect of `execute_<family> rs2 rs1 0#5 op` is `wX_bits 0#5 result`, and `run_wX_bits` makes a write to
  `x0` a **no-op regardless of the result**, *five generic family-core lemmas* (RTYPE/RTYPEW/ITYPE/MUL/MULW)
  prove `spec_aluX0_<op> ≡ sp1_aluX0` for all 21 covered ALU opcodes with **no `execute_*_pure = RV64.*`
  result-correctness lemma and no Sail-platform axiom** — the `ChipKind.sailEquiv` is the ungated 21-way
  conjunction. The Faithful anchor (`Faithful/AluX0.lean`) discharges the *inlined* reader constraints
  directly (SP1's `eval_op_a_immutable` is a plain method, not an `SP1Operation`, so unlike LoadX0 there is no
  `ALUTypeReaderImmutable.asserts` sub-call). Soundness, completeness, bridge, and anchor are all axiom-clean.
- **Shift-left chip (SLL + SLLW — soundness proven, axiom-clean).** `Proofs/Chips/ShiftLeftChip.lean` is the first
  chip whose shift logic is **inlined** (no operation gadget): the six shift-amount bits, the `v_01/v_012/
  v_0123` power encodings, the `shift_u16` one-hot byte selector, the `lower/higher_limb` bit-split, the
  `limb_result` reassembly, and the SLLW MSB sign-extension are ~53 inline `assertZero`s + 9 byte-range
  pulls in `main`. **Both soundness branches are proven and axiom-clean**: SLL via `ShiftLeftCore.sll_assembly`
  (4-way byte-shift dispatch), SLLW via `sllw_assembly` (2-way, since `is_sll = 0` ⇒ byteShift = `cb4`) over
  a new **2-limb 32-bit `Math/HWord.lean`** — the 32→64 sign fill *reuses* `Word.toBitVec64_signExtend_word`
  rather than re-deriving an `HWord` sign-extend. **Completeness**: `main` witnesses via the honest
  `ShiftLeftCore.pop*` generators (SP1's `event_to_row`; `popA` is built as the *placement of the recomputed
  `limb_result`* so placements hold by construction), and soundness verifies under that witnessing — but the
  completeness **proof** (~62 inline-constraint discharges + the three reader sub-assertion obligations) is one
  of the five deferred completeness proofs. Tooling note: the LSP times out on the 680-line chip; a scratch `import` + `example :
  Completeness … := by circuit_proof_start; sorry` elaborates fast and exposes the full goal for iteration.
- **Real-data threading (the reader column blocks are chip `Inputs`).** All readers are
  `FormalAssertion`s taking their `cols` as inputs, so the chip `Inputs` carry the committed `state`/`adapter`
  blocks (real clocks/timestamps/registers, not self-witnessed padding) and the clock/timestamp
  well-formedness lives in the chip's `ProverAssumptions` (the honest "the verifier commits a well-formed row"
  direction); soundness still derives the byte bounds from the bus. The remaining step is threading those
  inputs from the actual trace/Sail layer (so a real row's `state`/`adapter` come from the run) and unifying
  the operands with the register reads (`op_b_val`/`op_c_val` = the `rs1`/`rs2` `prev_value`s).
- **Memory bus (register *and* real 48-bit addresses).** The Byte/Program/Memory buses
  reuse the same three-layer pattern. The register memory bus (`addr1 = addr2 = 0`) emits from the readers'
  `send`/`receive` pairs into `InteractionBus` and is projected per-row by `Soundness/MemoryConsistency.lean`
  (`memoryLookups`/`rowMemEvents`, the `memoryLookups_padding`/`memoryLookups_eq_emitted` recovery). The
  **memory chips** (see below) then exercise the bus at **real 48-bit addresses** via the `Native/Readers/MemoryAccess`
  block, projected by the same file's `memAccessLookups`/`memAccessEvent` (+ their `_padding`/`_eq_emitted`),
  feeding the *same* `multiplicitySum` bus and the *same* `MemEvent`/`memoryConsistent` offline-memory model
  with no data-model change. `MemEvent` carries a faithful read-old/write-new pair. Still threaded
  (the genuinely-hard orthogonal piece, exactly as `../sp1-lean` defers its `OfflineMemory` closure):
  `TraceMemoryLink` — the read/write multiset-permutation ("last-write-wins") argument over the whole trace.
  The scaffolding is in place (`Proofs/Chips/MemoryProvider.lean` init/finalize receiver, the three-provider balance
  extraction, and the balance-core `mem_opA_read_send_matched`); the remaining `isConsistentOnline_of_memBalance`
  needs a bus↔access-list correspondence + an honest ordering side-condition. The `InteractionBus` core carries
  the `Memory` `InteractionKind`, so all of this plugs into the existing bus.
- **Native `balance ⟹ chain`** — **proven for State** (`pcChain_of_balance_and_clkInj`); the Memory analogue
  (`isConsistentOnline_of_memBalance`) and the lookup-soundness reduction remain.
- **Full trace consistency** — `Soundness/RowView.lean` is the reader-agnostic `RowView`/`AdapterView` row-view infra; the State-bus PC chain is modeled
  (`Soundness/StateConsistency.lean`), but cross-shard memory consistency is future work (see Memory bus above).
- **Matching the literal generated artifact** — the operation-level structs + constraints are generated into
  `SP1Clean/Extracted/<Op>.lean` by `update_extracted.py` (see `agents/extraction.md`); `Faithful/` anchors pin
  those to the native gadgets (now including `Faithful/CPUState.lean` for the CPUState fragment). Matching the exact
  *chip-level* output (`AddCols.constraints`, composing all reader/CPU fragments) awaits the remaining readers.
- **Per-operation proof status.** `Operations/` mixes fully-proven gadgets — the demoted
  `FormalAssertion`s (Add, Sub, Addw, Subw, U16MSB, U16Compare) + the surviving `FormalCircuit`s (Bitwise,
  the U16toU8 byte splits, IsZero / IsZeroWord / IsEqualWord, **LtOperationUnsigned**) — soundness +
  completeness axiom-clean — with spec-surface skeletons (proofs `sorry`) ported ahead of their chips; see
  each file's header note. **`MulOperation`**: soundness is fully proven (axiom-clean, via
  `mulSemantics_of_raw`); only its **completeness** is `sorry` — see `agents/mul-operation-learnings.md`.
  `LtOperationSigned`, `BitwiseOperation` are ordinary skeletons. **`AddrAddOperation` /
  `AddressOperation` are fully proven** (soundness + completeness, axiom-clean): `AddrAddOperation` adds the
  48-bit no-overflow `Assumptions` (`(toNat a + toNat b) % 2^64 < 2^48`) the previously-documented
  completeness gap required (the top carry `c3 = (a[3]+b[3]+c2)*65536⁻¹` is input-determined over all of
  `isU64`); `AddressOperation` carries the address-validity assumptions (offset bits boolean, `addr ≥ 2^16`,
  8-alignment) its inverse gate + offset range-check need.

## Memory chips (`LoadDouble` read + `StoreDouble` write)

The first two memory chips complete the semantic native/Sail path at **real 48-bit addresses**, both
directions, all axiom-clean. Their legacy fragment anchors remain to be consolidated into the
whole-chip `ChipFaithful` boundary:

- **Address gadgets** — `Native/Operations/AddrAddOperation.lean` (3-limb `rs1 + signExtend(imm)` with the top
  carry against `0`) and `Native/Operations/AddressOperation.lean` (composes `AddrAdd` + the offset-bit decode +
  the `top_two_limb_inv` inverse gate), proven soundness + completeness.
- **Readers** — `Native/Readers/ITypeReader.lean` (op_a = rd **write**, op_b = rs1 read, op_c immediate; for loads)
  and `Native/Readers/ITypeReaderImmutable.lean` (op_a = rs2 **read**; for stores), plus `Native/Readers/MemoryAccess.lean`
  — the core memory-interaction primitive: the timestamp-monotonicity machinery (`compare_low` select, the
  `clk − prev − 1 = diff_low + diff_high·2^16` decomposition, byte ranges) + the two `memoryChannel` emits
  (send prior value `+is_real`, receive `new_value` `−is_real`) at the **real 3-limb address**
  (`new = prev` for a read, `= store_value` for a write).
- **Chips** — `Proofs/Chips/LoadDoubleChip.lean` (`rd ← mem[rs1+imm]`) and `Proofs/Chips/StoreDoubleChip.lean`
  (`mem[rs1+imm] ← rs2`), each a `GeneralFormalCircuit` composing CPUState + `AddressOperation` (subcircuit) +
  `MemoryAccess` + the I-type adapter, soundness + completeness axiom-clean.
- **Sail bridges** — `Model/SailMemory.lean` ports the Sail width-8 memory **read *and* write** model
  (`run_vmem_read_of_width_8'` / `run_vmem_write_of_width_8`, with the SP1 PMA / `isValidMemConfig` /
  alignment infra) natively against the shared `LeanRV64D` model; `Proofs/Chips/{LoadDouble,StoreDouble}Chip/Bridge.lean`
  prove `correct_{load,store}_double_native` (`spec ≡ sp1`) and `{ld,sd}_chip_reaches_sail`. Axiom profile:
  the base trio + the `LeanRV64D` platform constants + bv_decide's pair (no `sorryAx`).
- **Faithfulness** — `Faithful/{ITypeReader,ITypeReaderImmutable,LoadDouble,StoreDouble}.lean` anchor the
  generated constraint lists to the composed sub-anchors + the inlined `MemoryAccess` timestamp gates.
- **Trace** — `Soundness/MemoryConsistency.lean` gains the real-address `memAccessLookups`/`memAccessEvent`
  projections + recovery lemmas (above), so a load/store row's memory access joins the existing offline-memory
  model with no data-model change. `TraceMemoryLink` stays threaded.

The reusable spine (address gadget + `MemoryAccess` + I-type readers + the Sail read/write model) drops
straight onto `StoreByte` / the sub-word load/store ops — only per-op byte gadgetry remains.
