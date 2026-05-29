# CLEAN_NATIVE_DIRECTION.md — is the structural-`FormalAssertion` shape the right long-term model?

**Status:** architecture findings + prototype brief (2026-05-29). Written to seed a
fresh prototyping session. Question that prompted it: *are we modeling chips
"correctly" for the long term, or are the closed chips (Lt/Bitwise/ShiftLeft/
ShiftRight…) in a sub-optimal shape forced by compatibility with the legacy
`SP1Chips/*` + `update_constraints.py` machinery we intend to retire?*

**Short answer:** the current structural-`FormalAssertion` + `SailBridge` shape is a
**well-engineered stepping-stone, not the Clean-native end-state.** Two parts of it
are compatibility artifacts that should not be scaled further as the *target* shape:
(1) the ~75-conjunct **structural `FormalSpec`** (a restatement of the constraints,
not a semantic statement), and (2) the fact that **all RISC-V semantics is borrowed**
from `_root_.<Chip>.Poly.correct_*` via the `SailBridge`. The expensive, genuinely
Clean-native assets (the inline `main` gates, the gated reader/lookup subcircuits, the
multiplicity bus, the trace aggregation) are reusable and survive a cutover. The fix
direction the user intuited is correct, but the lever is **`FormalAssertion` →
`FormalCircuit`/`GeneralFormalCircuit` with witness generators**, *not* `localLength`
on its own.

---

## 1. The decisive fact: in a STARK, every column is committed

There is no "local witness that isn't a committed column." Confirmed on both sides:

- **Clean:** `witness`/`localLength` cells are compiled into committed advice columns.
  `FlatOperation.witnessGenerators` (`.lake/packages/Clean/Clean/Circuit/Basic.lean:562`)
  emits one generator closure per column; the prover fills them. `localLength` is just
  the *count* of those cells (offset bookkeeping for subcircuit composition).
- **SP1:** the trace row `Main : Vector F N` contains *every* column the AIR references —
  primary results **and** all auxiliary columns (bit decompositions, limb splits, carry
  chains, memory `prev_value`/timestamps). There is no second-class non-committed column
  type. The `SP1Constraint` datatype (`SP1Foundations/Constraint.lean`) only has
  `assertZero | send | receive` over committed `F` values.

**Consequence:** moving aux columns to `localLength` witnesses does **not** change what
gets committed or reduce trace width. What it changes is *who owns the witness generator*
and *where the proof obligation lives*:

| | aux columns are… | completeness obligation | spec can be… |
|---|---|---|---|
| **`FormalAssertion`** (today) | fields of `Input` (no generator) | `Assumptions ∧ Spec → constraints` | **structural only** (must restate the constraints) |
| **`FormalCircuit` / `GeneralFormalCircuit`** | `witness` cells with generator closures | `Assumptions ∧ Spec ∧ UsesLocalWitnessesCompleteness → constraints` | **semantic** (`aw = RV64.srl cw bw`), strictly weaker than constraints |

The Clean `FormalAssertion` docstring is explicit
(`.lake/packages/Clean/Clean/Circuit/Basic.lean:328`):

> `FormalAssertion` … by design, does not have `FormalCircuit`'s completeness. …
> the *completeness* statement is weaker: assumptions ∧ spec → constraints. Given
> assumptions, the constraints might not be satisfiable and **the spec must be an
> equivalent reformulation of the constraints**. (In the case of `FormalCircuit`,
> given assumptions, the constraints are always satisfiable and **the spec can be
> strictly weaker than the constraints**.)

So the 75-conjunct structural spec is a *direct consequence of the `FormalAssertion`
choice*, and it is avoidable by switching to witnessed `FormalCircuit`/`GeneralFormalCircuit`.

---

## 2. What is actually coupled to the legacy layer today

Verified across all 24 closed/partial chips:

- **Constraint definitions** come from `update_constraints.py` output
  (`SP1Chips/<Chip>/Constraints.lean`, the `_root_.<Chip>.constraints Main` function).
- **The Clean `main`** is a *faithful re-statement* of those same constraint equations
  in the Clean DSL (the inline gates). It is independent **in content** but is tied to
  the legacy layout through `fromMain`/`toMain` + `allHold_iff_structural`, which bridge
  to `_root_.<Chip>.constraints Main`.
- **All RISC-V/Sail semantics is borrowed.** Every chip's `SailBridge.lean` calls
  `_root_.<Chip>.Poly.correct_*` directly. There are currently **0/24 Clean-native
  Sail-equivalence proofs**. Delete `SP1Chips/*` today → every `SailBridge` breaks.
- **The top-level Clean theorem** (`SP1Clean/Soundness/TraceSoundness.lean`,
  `trace_soundness_aggregateMemory`) proves bus/memory/PC consistency over per-row
  `Spec`s but **does not link to Sail** — that link is per-chip via the borrowed
  `correct_*`. `ExecuteTrace.lean` wires only Add/Addi/Sub.

**Reusable (Clean-native already; survives `SP1Chips` retirement):**
the inline `main` gate logic, the gated readers (`CPUState.Gated`, `ALUTypeReader.Gated`,
`OperandAccess`), the multiplicity bus (`SP1Clean/SP1Lookup.lean`,
`SP1Clean/Multiplicity.lean`), and the trace aggregation (`SP1Clean/Soundness/*`:
memory consistency, state/PC chain, offline-memory permutation).

**Replaced at cutover (cheap, mechanical):** `fromMain`/`toMain`,
`allHold_iff_structural`, the structural `FormalSpec`, and the `SailBridge` wrappers.
Low sunk cost — these are the compatibility glue.

---

## 3. The Clean-native idiom (Clean already supports it)

Clean's own VM example and table layer show the intended shape — it is **not** a flat
structural `FormalAssertion` over a projected row:

- **`.lake/packages/Clean/Clean/Examples/FemtoCairo/FemtoCairo.lean`** models instruction
  steps as **`GeneralFormalCircuit`** — semantic specs (`output = decode(input)` /
  `= memory[addr]`), assertion-like range constraints, **lookups** into program/memory
  tables, and **separate prover vs verifier assumptions** (`ProverAssumptions`/
  `ProverSpec` with a `ProverHint`). This is the right fit for a chip row, whose
  "output" is not a returned value but committed columns + bus sends.
- **`.lake/packages/Clean/Clean/Table/*`** provides `Trace`, `TraceOfLength`,
  `TableConstraint` (window size 1 or 2 → `SingleRowConstraint`/`TwoRowsConstraint`),
  `TableOperation` (`boundary | everyRow | everyRowExceptLast` ⇒ boundary + transition
  constraints), `FormalTable`, and `InductiveTable` (`State × Input → State` with a
  per-step `Spec`). This is the AIR/trace layer — the natural home for the global
  multiset/bus argument across rows.
- The **witnessed-gadget pattern** already exists in-repo as a pilot:
  `SP1Clean/Operations/BitwiseU16OperationWitnessed.lean` (a `FormalCircuit` that
  internalizes its aux cells as `witness` and carries a semantic spec). The docs call
  this frontier **"Boundary A"** (modeling witness generation) — see
  `CLEAN_VERIFICATION_STATUS.md`.

**Target design for a chip, Clean-native:**

1. **Arithmetic sub-operations** (Add, U16MSB, the shift-power chain, byte
   decomposition, carry chains) as `FormalCircuit`/`GeneralFormalCircuit` **witnessed
   gadgets** with **semantic specs** (`out = f(in)`) and **witness generators** that
   construct the aux cells. Completeness becomes constructive and real.
2. **The chip row** as a `GeneralFormalCircuit` whose `Spec` is the **semantic
   next-state + bus-effect relation** (e.g. `aw = RV64.srl cw bw`, register/memory bus
   effects), composing the sub-gadgets. The aux columns are generated by the gadgets, so
   the row's completeness no longer needs a structural restatement — the 75-conjunct
   spec disappears.
3. **The trace** as a `FormalTable`/`InductiveTable` carrying the multiplicity/permutation
   bus argument across rows (reuse the existing `SP1Clean/Soundness/*` aggregators).

---

## 4. The real cost (why this is the *same project* as retiring `SP1Chips`)

A semantic spec is not a free refactor — it forces two pieces of genuinely new work
that the current approach *borrows* from `SP1Chips`:

- **(a) Native `correct_*`.** A semantic spec means you can no longer route through
  `_root_.<Chip>.Poly.correct_srl`; you must **prove the shift/mul/div correctness in
  Clean** (re-derive what the legacy `_poly` lemmas establish, or bridge to Sail
  directly). This is the bulk of the work and the actual point of retiring `SP1Chips`.
- **(b) Witness generators ("Boundary A").** You must write the closures that compute
  each aux column from the instruction event (model SP1's Rust `event_to_row` in Lean:
  bit-decompose the shift amount, split limbs, compute `v_0123 = 2^shift`, sign MSBs,
  carries, …). Completeness then *constructs* them rather than asserting their relations.

So "use witnesses to slim the spec" and "retire `SP1Chips`/`update_constraints.py`"
are the same effort. The structural+`SailBridge` route was a sensible stepping-stone
precisely because it closed chips fast by reusing proven assets; it does **not block**
the ideal, it just hasn't built it.

---

## 5. Recommendation

- **Do not scale the structural-`FormalAssertion` + `SailBridge` pattern as the
  *target* shape.** It is fine as a stepping-stone; its expensive parts are reusable.
- **Prototype the Clean-native witnessed design on one chip end-to-end** before
  committing the fleet to a direction. The prototype proves out the end-state and
  measures the true per-chip cost of a `SP1Chips`-free chip.
- **Bias new column structs/readers toward "aux cells are circuit-owned witnesses"**
  (allocated by gadgets) rather than "fields projected from `Main` via `fromMain`," so
  the eventual cutover doesn't require re-modeling layouts.

### Prototype brief (fresh session)

Pick a **small chip** to minimize arithmetic — `Add` (clean carry chain, already has a
`correct_add` to diff against) or extend the existing **Bitwise witnessed pilot**.
Build it with **no dependency on `_root_.<Chip>.*`**:

1. **Witnessed sub-op gadget(s).** Take the relevant `SP1Clean/Operations/<Op>.lean`
   (e.g. `AddOp`) and produce a `FormalCircuit` variant whose aux cells (carries/limbs)
   are `witness` with generator closures, and whose `Spec` is semantic
   (`value = (a + b) mod 2^64` form). Model on `BitwiseU16OperationWitnessed.lean`.
   Prove its `soundness`/`completeness` (completeness now *constructs* the carries).
2. **Chip row as `GeneralFormalCircuit`.** One `main` composing the witnessed sub-op +
   the gated readers (memory/program via Clean lookups) + selector gates. `Spec` =
   semantic next-state + bus effects (`aw = RV64.add …`, register write, PC+4). Use
   FemtoCairo's `ProverAssumptions`/`ProverSpec`/`ProverHint` split for the
   memory/program lookups.
3. **Native Sail equivalence.** Prove `chip.Spec → (spec_add …).run s = (sp1_add …).run s`
   directly from the semantic `Spec` (the `RV64.add` content), **without** calling
   `_root_.Add.correct_add`. This is the hard, decisive step — it shows a chip can reach
   Sail without `SP1Chips`.
4. **Slot it into the trace layer.** Confirm the row's bus sends feed the existing
   `SP1Clean/Soundness/*` aggregation (multiplicity bus, memory/state consistency)
   unchanged — these are already Clean-native.
5. **Compare head-to-head** against the current structural version: spec readability,
   proof size, what (if anything) still references `update_constraints.py` output, and
   the witness-generator burden. Use that to decide the fleet-wide direction.

**Acceptance for the prototype:** the chip elaborates and is axiom-clean with **zero**
references to `_root_.<Chip>.constraints`, `_root_.<Chip>.allHold_constraints_iff`, or
`_root_.<X>.Poly.correct_*` — and its `FormalSpec` is the semantic statement, not a
constraint restatement.

---

## 6. Key pointers

**Clean framework:**
- `.lake/packages/Clean/Clean/Circuit/Basic.lean` — `FormalCircuit` (285), `FormalAssertion`
  (342, with the decisive docstring at 328), `GeneralFormalCircuit` (355+),
  `Soundness`/`Completeness` defs, `witnessGenerators` (562), `localLength` (78, 222).
- `.lake/packages/Clean/Clean/Table/*` — `Trace`, `TraceOfLength`, `TableConstraint`,
  `TableOperation`, `FormalTable`, `InductiveTable`.
- `.lake/packages/Clean/Clean/Circuit/Lookup.lean` — `Table`/`lookup` (membership-style;
  global cross-table multiset arg is the bus layer we build on top).
- `.lake/packages/Clean/Clean/Examples/FemtoCairo/FemtoCairo.lean` — the canonical
  `GeneralFormalCircuit` + lookups VM example to imitate.

**Repo (this project):**
- `SP1Clean/Operations/BitwiseU16OperationWitnessed.lean` — existing witnessed-`FormalCircuit` pilot.
- `SP1Clean/SP1Lookup.lean`, `SP1Clean/Multiplicity.lean` — multiplicity bus (reusable).
- `SP1Clean/Soundness/{TraceSoundness,ExecuteTrace,MemoryConsistency,StateConsistency}.lean`
  — trace aggregation (reusable; `ExecuteTrace` currently wires Add/Addi/Sub).
- `SP1Clean/Chips/Spec.lean` — where the structural `FormalSpec`s live today (what a
  semantic rewrite would replace).
- Any `SP1Clean/Chips/*/SailBridge.lean` — shows the `_root_.<X>.Poly.correct_*` borrow
  to be eliminated.
- `docs/CLEAN_VERIFICATION_STATUS.md` (Boundary A/B framing),
  `docs/CLEAN_FUTURE.md` (retirement roadmap / Phase D),
  `docs/MULTIPLICITY_BUS.md` (bus model).

**SP1 model (for faithfulness checks):** SP1 Rust is **not** checked out locally
(`SP1_DIR` unset); reason from the Lean side. All columns committed; `event_to_row`
(Rust) fills the row; the AIR `eval` asserts polynomial + interaction constraints;
`AirInteraction`/`InteractionKind` is the multiset bus (`SP1Foundations/Constraint.lean`).
