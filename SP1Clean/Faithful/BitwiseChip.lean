import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Chips.BitwiseChip.Formal
import SP1Clean.Foundations.SP1Constraint
import SP1Clean.Extracted.BitwiseChip

/-! # Faithfulness anchor — `BitwiseChip` constraints → native `AssertSpec`/`InteractSpec`

Anchors the native `BitwiseChip`'s structural specs to SP1's `Bitwise` chip constraint definition
(`Extracted/BitwiseChip.lean`: `BitwiseU16Operation ++ CPUState ++ ALUTypeReader` prefix plus the
four inline opcode-flag booleans and the `op_a_0` flag). Two anchor theorems — one per extracted
list. The assertion half anchors the forward (`→`) direction only; the full `↔` is future work.
The interaction half is trivial: `BitwiseCols.interactions` own tail is empty (`InteractSpec := True`);
the operation-level byte ranges are anchored in `BitwiseU16Operation`'s own faithfulness work. -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **Faithfulness anchor — assertion half (`→`).** SP1's `Bitwise` chip `asserts` list entails
the native chip's `AssertSpec` (the four opcode-flag booleans, their sum-bound, and `op_a_0`). -/
theorem bitwiseChip_asserts_faithful (cols : Extracted.BitwiseCols (ZMod p)) :
    List.Forall (· = 0) (Extracted.BitwiseCols.asserts cols) →
      SP1Clean.BitwiseChip.AssertSpec cols := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  intro h
  -- Unfold SP1's composed `asserts` list and peel its three `++`s, discarding the
  -- `BitwiseU16Operation`/`CPUState`/`ALUTypeReader` sub-list facts and keeping only the chip's own
  -- inline tail `[E3, E5, E7, E9, op_a_0]`, which is exactly `AssertSpec`.
  simp only [Extracted.BitwiseCols.asserts] at h
  rw [SP1Clean.Extracted.forall_append_single,
      SP1Clean.Extracted.forall_append_single,
      SP1Clean.Extracted.forall_append_single] at h
  obtain ⟨_, _, _, h_tail⟩ := h
  simp only [List.Forall, SP1Clean.BitwiseChip.AssertSpec] at h_tail ⊢
  tauto

omit [Fact (2 ^ 17 < p)] in
/-- **Faithfulness anchor — interaction half.** SP1's `Bitwise` chip `interactions` own tail is empty,
so it trivially entails the native chip's `InteractSpec` (`True`); the bitwise op's byte-range pulls
live inside the composed `BitwiseU16Operation` sub-list and are anchored there. -/
theorem bitwiseChip_interactions_faithful (cols : Extracted.BitwiseCols (ZMod p)) :
    List.Forall Interaction.toProp (Extracted.BitwiseCols.interactions cols) →
      SP1Clean.BitwiseChip.InteractSpec cols := by
  intro _; trivial

end SP1Clean.Faithful
