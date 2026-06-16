import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Chips.ShiftRightChip.Formal
import SP1Clean.Model.SP1Constraint
import SP1Clean.Extracted.ShiftRightChip

/-! # Faithfulness anchor to the SP1 (Rust-extraction) constraints (ShiftRight)

Anchors the native `ShiftRightChip`'s two structural specs (`AssertSpec` / `InteractSpec`) to **SP1's
`ShiftRightChip` constraint definition** (`Extracted/ShiftRightChip.lean`: a composed
`U16MSBOperation×3 ++ CPUState ++ ALUTypeReader` prefix plus the inline shift assertZeros and the nine
byte-range sends).

The two anchor theorems (one per extracted list) are **proven** in the forward (soundness) direction:
peel the composed prefix sub-lists via `forall_append_single`/`forall_append_interactions`, then the
inline tail matches `AssertSpec`/`InteractSpec` definitionally (the byte sends reduce through
`toProp_send_byte` + `Range.constrain`). A `Nat.cast_one` (asserts) / `zero_add` (interactions)
normalizes the extractor's literal coercions to the hand-written spec form. Both are axiom-clean. -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **Faithfulness anchor — assertion half.** SP1's `ShiftRightChip` `asserts` list entails the
native chip's `AssertSpec` (the 58 inline shift assertZeros, after peeling the composed prefix). -/
theorem shiftRight_asserts_faithful (cols : Extracted.ShiftRightCols (ZMod p)) :
    List.Forall (· = 0) (Extracted.ShiftRightCols.asserts cols) →
      SP1Clean.ShiftRightChip.AssertSpec cols := by
  intro h
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [Extracted.ShiftRightCols.asserts, Extracted.forall_append_single, List.Forall,
    Nat.cast_one] at h
  dsimp only [SP1Clean.ShiftRightChip.AssertSpec]
  exact h.2

omit [Fact (2 ^ 17 < p)] in
/-- **Faithfulness anchor — interaction half.** SP1's `ShiftRightChip` `interactions` byte-range sends
entail the native chip's `InteractSpec` (each `Range` send's `mult ≠ 0 → a.val < 2^b.val`). -/
theorem shiftRight_interactions_faithful (cols : Extracted.ShiftRightCols (ZMod p)) :
    List.Forall Interaction.toProp (Extracted.ShiftRightCols.interactions cols) →
      SP1Clean.ShiftRightChip.InteractSpec cols := by
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  intro h
  simp only [Extracted.ShiftRightCols.interactions, Extracted.forall_append_interactions,
    List.Forall, Interaction.toProp_send_byte,
    show (ByteOpcode.ofNat 6 : ByteOpcode) = ByteOpcode.Range from rfl, ByteOpcode.constrain,
    zero_add] at h
  dsimp only [SP1Clean.ShiftRightChip.InteractSpec]
  exact h.2

end SP1Clean.Faithful
