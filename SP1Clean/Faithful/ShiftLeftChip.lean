import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Chips.ShiftLeftChip.Formal
import SP1Clean.Model.SP1Constraint
import SP1Clean.Extracted.ShiftLeftChip

/-! # Faithfulness anchor — `ShiftLeftChip` constraints → native `AssertSpec`/`InteractSpec`

Anchors the native `ShiftLeftChip`'s two structural specs (`AssertSpec` / `InteractSpec`) to SP1's
`ShiftLeftChip` constraint definition (`Extracted/ShiftLeftChip.lean`: a composed
`U16MSBOperation ++ CPUState ++ ALUTypeReader` prefix plus the inline shift assertZeros and the nine
byte-range sends). Two anchor theorems, one per extracted list, both proved in the forward (`→`)
direction; the full `↔` form is future work. -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **Faithfulness anchor — assertion half.** SP1's `ShiftLeftChip` `asserts` list entails the
native chip's `AssertSpec` (the inline shift assertZeros, after peeling the composed prefix). -/
theorem shiftLeft_asserts_faithful (cols : Extracted.ShiftLeftCols (ZMod p)) :
    List.Forall (· = 0) (Extracted.ShiftLeftCols.asserts cols) →
      SP1Clean.ShiftLeftChip.AssertSpec cols := by
  intro h
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [Extracted.ShiftLeftCols.asserts, Extracted.forall_append_single, List.Forall] at h
  dsimp only [SP1Clean.ShiftLeftChip.AssertSpec]
  exact h.2

omit [Fact (2 ^ 17 < p)] in
/-- **Faithfulness anchor — interaction half.** SP1's `ShiftLeftChip` `interactions` byte-range sends
entail the native chip's `InteractSpec` (the nine byte-range sends, each `mult ≠ 0 → a.val < 2^b.val`). -/
theorem shiftLeft_interactions_faithful (cols : Extracted.ShiftLeftCols (ZMod p)) :
    List.Forall Interaction.toProp (Extracted.ShiftLeftCols.interactions cols) →
      SP1Clean.ShiftLeftChip.InteractSpec cols := by
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  intro h
  simp only [Extracted.ShiftLeftCols.interactions, Extracted.forall_append_interactions,
    List.Forall, Interaction.toProp_send_byte,
    show (ByteOpcode.ofNat 6 : ByteOpcode) = ByteOpcode.Range from rfl, ByteOpcode.constrain,
    zero_add] at h
  dsimp only [SP1Clean.ShiftLeftChip.InteractSpec]
  exact h.2

end SP1Clean.Faithful
