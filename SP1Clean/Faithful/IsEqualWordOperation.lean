import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Operations.IsEqualWordOperation.RawSpec
import SP1Clean.Foundations.SP1Constraint
import SP1Clean.Extracted.IsEqualWordOperation

/-! # Faithfulness anchor to the SP1 (Rust-extraction) constraints (IsEqualWord)

Anchors the native `IsEqualWordOperation` gadget's `RawSpec` to **SP1's `IsEqualWordOperation`
constraint definition** — a single `IsZeroWordOperation` sub-list on the difference plus the
`is_real` gate. Verified and wired into the root index (the extracted `IsZeroWordOperation` column
struct uses flattened `is_zero_limb_0..3` fields, so its `deriving ProvableStruct` succeeds). -/

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
/-- **Faithfulness anchor.** SP1's `IsEqualWordOperation` constraint list holds iff the native
gadget's `RawSpec` holds. (Unverified pending the upstream `IsZeroWordOperation` deriving fix.) -/
theorem isEqualWord_constraints_faithful (a b : Word (ZMod p))
    (cols : Extracted.IsEqualWordOperation (ZMod p)) :
    (List.Forall (· = 0) (Extracted.IsEqualWordOperation.asserts a b cols 1) ∧
      List.Forall Interaction.toProp (Extracted.IsEqualWordOperation.interactions a b cols 1)) ↔
      SP1Clean.IsEqualWordOperation.RawSpec a b cols := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  simp only [Extracted.IsEqualWordOperation.asserts, Extracted.IsEqualWordOperation.interactions,
    Extracted.IsZeroWordOperation.asserts, Extracted.IsZeroWordOperation.interactions,
    Extracted.IsZeroOperation.asserts, Extracted.IsZeroOperation.interactions, one_mul,
    List.cons_append, List.nil_append, List.Forall, bool_iff,
    IsEqualWordOperation.RawSpec, IsZeroWordOperation.RawSpec, IsZeroOperation.RawSpec, and_assoc]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, mul_eq_zero,
    List.getElem_cons_succ, sub_self, and_true, true_and]

end SP1Clean.Faithful
