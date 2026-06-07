import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Operations.IsZeroWordOperation.RawSpec
import SP1Clean.Foundations.SP1Constraint
import SP1Clean.Extracted.IsZeroWordOperation
import SP1Clean.Faithful.IsZeroOperation

/-! # Faithfulness anchor to the SP1 (Rust-extraction) constraints (IsZeroWord)

Anchors the native `IsZeroWordOperation` gadget's `RawSpec` to **SP1's `IsZeroWordOperation`
constraint definition** (`Extracted/IsZeroWordOperation.lean`: four `IsZeroOperation` sub-lists plus
the `is_real` gate, `result` boolean, and the two half-product + final gluing equalities). This is
the first **compositional** anchor: the `++` of the four sub-lists splits under `List.Forall`, and
each sub-list folds into `IsZeroOperation.RawSpec` (the `IsZero` anchor's RHS), which `RawSpec`
references directly. -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
/-- Carry-bool bridge: `x*(x-1)=0 ↔ x∈{0,1}` (field; `→` via `bool_of_mul_pred`). -/
private lemma bool_iff {x : ZMod p} : x * (x - 1) = 0 ↔ (x = 0 ∨ x = 1) := by
  rw [sub_eq_add_neg]
  exact ⟨SP1Clean.bool_of_mul_pred,
    fun h => by rcases h with h | h <;> rw [h] <;> ring⟩

omit [Fact (2 ^ 17 < p)] in
/-- **Faithfulness anchor.** SP1's `IsZeroWordOperation` constraint list holds iff the native
gadget's `RawSpec` holds. (No range bounds, so `NeZero p` follows from primality.) -/
theorem isZeroWord_constraints_faithful (a : Word (ZMod p))
    (cols : Extracted.IsZeroWordOperation (ZMod p)) :
    (List.Forall (· = 0) (Extracted.IsZeroWordOperation.asserts a cols 1) ∧
      List.Forall Interaction.toProp (Extracted.IsZeroWordOperation.interactions a cols 1)) ↔
      SP1Clean.IsZeroWordOperation.RawSpec a cols := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  -- Split the four `IsZeroOperation` sub-lists at each `++` and collapse each to its `RawSpec` via
  -- the `IsZero` anchor (the design `RawSpec` references `IsZeroOperation.RawSpec` directly), leaving
  -- only the small own-tail. This keeps the `result * a` products opaque (no `mul_eq_zero` blowup).
  simp only [Extracted.IsZeroWordOperation.asserts, Extracted.IsZeroWordOperation.interactions]
  rw [forall_append_pair, forall_append_pair, forall_append_pair,
    forall_append_pair, isZero_constraints_faithful, isZero_constraints_faithful,
    isZero_constraints_faithful, isZero_constraints_faithful]
  simp only [List.Forall, IsZeroWordOperation.RawSpec, one_mul,
    bool_iff, sub_self, true_and, and_true, and_assoc]

end SP1Clean.Faithful
