import SP1Clean.Chips.AddChip.Formal
import SP1Clean.Trace

/-! # Native-semantic vs structural verification — the Add operation, head to head

Documentation (no proofs). It contrasts the Clean-native, semantically-specified Add built here
(`SP1Clean.AddOperation` + `AddChip`) with the structural-`FormalAssertion` + `SailBridge`
style (as in `SP1Clean/Operations/AddOperation.lean` + `SP1Clean/Chips/ALU/AddChip/*`), to show
why a semantic spec yields a smaller, self-contained, axiom-clean proof.

## 1. Spec shape (the headline difference)

* **Native** — the operation `Spec` is a 2-conjunct *semantic* statement:
  `Word.isU64 value ∧ Word.toBitVec64 value = Word.toBitVec64 a + Word.toBitVec64 b`,
  and the chip `Spec` is the `is_real`-gated `toBitVec64 a_val = toBitVec64 op_b +
  toBitVec64 op_c`. No constraint restatement appears anywhere.
* **sp1-lean** — the chip `FormalSpec` is a conjunction of *structural* sub-Specs
  (`CPUState.Gated.Spec ∧ RTypeReader.Gated.Spec ∧ op_a_0 = 0 ∧ …`) plus the
  semantic clause; the operation completeness routes through
  `AddOperation.iff_sp1_full`. The structural reader Specs are bus-send restatements.

## 2. Self-containment (the decisive difference)

* **Native** — soundness AND completeness are proved by re-deriving the carry chain
  in-project (`RawSpec`, `addSemantics_of_carries`, `carries_of_addSemantics` =
  native ports of `AddOperation.spec`/`spec_inv`, on a local `limb_lift`). Range via
  Clean's native `Gadgets.ToBits.rangeCheck`. **Zero** references to
  `_root_.Add.constraints`, `AddOperation.{spec,iff_sp1_full,allHold_constraints_iff}`,
  `Poly.correct_*`, `update_constraints.py` output, or `SP1Chips` (verified by grep;
  only doc-comments name them). No `.Gated`.
* **sp1-lean** — borrows ALL arithmetic from `_root_.AddOperation.*` and ALL RISC-V
  semantics from `_root_.Add.correct_add` via the `SailBridge`; the chip is welded to
  the `update_constraints.py`-generated `_root_.Add.constraints` through
  `fromMain`/`toMain` + `allHold_iff_structural`.

## 3. Size

* **Native, Add-specific:** `Operations/AddOperation.lean` (306) + `Chips/AddChip.lean` (88) = ~394
  lines — *including* the natively re-derived add correctness — plus a reusable
  `Foundations.lean` (110, shared by every future chip).
* **sp1-lean:** `Operations/AddOperation.lean` (385) + `Chips/ALU/AddChip/*` (586) =
  ~971 lines that **still borrow** the arithmetic (from SP1Operations' AddOperation,
  ~256 lines more) and Sail (from SP1Chips' `correct_add`).
* The native figures count the operation and chip proper; the parts they omit (the borrowed
  arithmetic and the borrowed Sail correctness) are exactly the ones the structural version
  cannot avoid, so the semantic+native side is comparable or smaller while remaining
  self-contained.

## 4. Axiom cleanliness

`#print axioms` on `SP1Clean.AddOperation.circuit` and `SP1Clean.AddChip.circuit`
both yield only `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no
`AddOperation`/`Add` axioms. `lake build SP1Clean` is 0 errors / 0 warnings.

## 5. Toolchain

The full Clean feature set (`GeneralFormalCircuit` + `ProverData`/`ProverHint`,
`FormalCircuit` witness generation, `subcircuit` composition, `FormalTable`/
`InductiveTable`, `Gadgets.ToBits.rangeCheck`, the `FemtoCairo` example) compiles on
**public Clean `main` + Lean 4.28 + mathlib v4.28**. The same modules are *broken* on
the succinctlabs Clean `v6.2.2` / 4.29 fork that sp1-lean pins (`Table.Inductive`,
`Types.U32`, `Addition8FullCarry` — the last with a `sorry`).

## 6. Native Sail bridge

The Sail RISC-V model (`LeanRV64D`) and runtime (`lean-sail`) are mathlib-free and build on
Lean 4.28; `RISCV` (riscv-lean) is not needed for Add. `Chips/AddChip/Bridge.lean` re-creates a
minimal subset of the foundations (`Misc`, `Register`, a trimmed `SailWrap` = RTYPE/register
wrappers) and proves `correct_add_native : spec_add ≡ sp1_add` — the RISC-V Sail `ADD` execution
equals the chip's emulation — sourcing the add identity from the **chip's semantic Spec** (`h_add`),
with no `_root_.Add.*` / `AddOperation.*` / `SP1Chips` borrow. `add_chip_reaches_sail` then derives
the Sail equivalence directly from the verified `AddChip.Spec`. Both are axiom-clean.

## 7. Faithfulness anchor

`Faithful/AddOperation.lean` carries a trimmed `SP1Constraints` datatype, `ByteOpcode`, and a
verbatim copy of SP1's `AddOperation.constraints` (the operation fragment the Rust extraction
composes into the chip-level `Add.constraints`). `add_constraints_faithful` proves
`(AddOperation.constraints a b ⟨value⟩ 1).allHold ↔ AddOperation.RawSpec a b value` — SP1's
constraint list is *exactly* the native gadget's `RawSpec`, which the gadget's soundness and
completeness run through, so the native proof is faithful to SP1's operation constraints. This is
operation-level; the chip-level anchor to the full generated `Add.constraints` (which also composes
reader/CPU constraints) builds on the native readers.

## Summary

For Add, the four-artifact chain holds end-to-end on a public toolchain: a witnessed `FormalCircuit`
with a genuinely semantic spec, natively-proven arithmetic, composed into a `GeneralFormalCircuit`
chip, a native Sail bridge (`correct_add_native` / `add_chip_reaches_sail`) reaching the RISC-V spec,
and a faithfulness anchor (`add_constraints_faithful`) to SP1's operation constraints — all
axiom-clean in one unified `lake build SP1Clean`, smaller than the borrowing structural
version and free of any `SailBridge`/extracted-constraint coupling. -/

namespace SP1Clean.Comparison

end SP1Clean.Comparison
