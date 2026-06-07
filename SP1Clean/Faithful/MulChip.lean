import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Chips.MulChip.Formal
import SP1Clean.Foundations.SP1Constraint
import SP1Clean.Extracted.MulChip

/-! # Faithfulness anchor to the SP1 (Rust-extraction) constraints (Mul) — skeleton

Anchors the native `MulChip`'s two structural specs (`AssertSpec` / `InteractSpec`) to **SP1's `Mul`
chip constraint definition** (`Extracted/MulChip.lean`: a composed `MulOperation ++ CPUState ++
RTypeReader` prefix plus the inline variant-flag booleans `E5,E7,E9,E11,E13,E15` and the `op_a_0`
zeroing flag; the chip's *own* interactions tail is empty).

Following the two-list split (per `Faithful/AddOperation.lean`'s `add_asserts_faithful` /
`add_interactions_faithful`), there are two anchor theorems — one per extracted list. The assertion half
is stated as the **forward** (soundness) direction (the extracted constraints entail the structural
spec), left as a skeleton `sorry`; the full `↔` form — peeling the composed `MulOperation`/`CPUState`/
`RTypeReader` sub-lists via `forall_append`/their own anchors — is the deferred fill-in. The interaction
half is trivial (SP1's `MulCols.interactions` own tail is empty, `InteractSpec := True`), so it needs no
`sorry`; the operation-level byte ranges are anchored in `MulOperation`'s own faithfulness work. -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- **Faithfulness anchor — assertion half.** SP1's `Mul` chip `asserts` list entails the
native chip's `AssertSpec` (the five variant-flag booleans + their sum-bound + the `op_a_0` flag,
after peeling the composed `MulOperation`/`CPUState`/`RTypeReader` prefix). -/
theorem mul_asserts_faithful (cols : Extracted.MulCols (ZMod p)) :
    List.Forall (· = 0) (Extracted.MulCols.asserts cols) →
      SP1Clean.MulChip.AssertSpec cols := by
  intro h
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  simp only [Extracted.MulCols.asserts, Extracted.forall_append_single, List.Forall] at h
  dsimp only [SP1Clean.MulChip.AssertSpec]
  exact h.2

omit [Fact (2 ^ 24 < p)] in
/-- **Faithfulness anchor — interaction half.** SP1's `Mul` chip `interactions` own tail is empty, so it
trivially entails the native chip's `InteractSpec` (`True`); the multiply's byte-range pulls live inside
the composed `MulOperation` sub-list and are anchored there. -/
theorem mul_interactions_faithful (cols : Extracted.MulCols (ZMod p)) :
    List.Forall Interaction.toProp (Extracted.MulCols.interactions cols) →
      SP1Clean.MulChip.InteractSpec cols := by
  intro _; trivial

end SP1Clean.Faithful
