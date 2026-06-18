import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Native.Operations.IsZeroOperation.RawSpec
import SP1Clean.Extracted.Circuit.IsZeroOperation
import SP1Clean.Model.SP1Constraint
import SP1Clean.Model.InteractionProjection
import SP1Clean.Model.InteractionRecovery
import SP1Clean.Faithful.ExtractedInteractionModel
import SP1Clean.Extracted.IsZeroOperation

/-! # Faithfulness anchor to the SP1 (Rust-extraction) constraints (IsZero)

Anchors the native `IsZeroOperation` gadget's `RawSpec` to **SP1's `IsZeroOperation` constraint
definition** (the generated operation fragment in `Extracted/IsZeroOperation.lean`: three
`assertZero`s — `result = 1 - inverse*a`, `result` boolean, `result*a = 0`). The anchor
`isZero_constraints_faithful` proves the SP1 constraint list's `allHold` is **exactly** the native
gadget's `RawSpec`. No byte sends, so this is the purest `assertZero`-only anchor. -/

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
/-- **Faithfulness anchor — assertion half.** SP1's `IsZeroOperation` `asserts` list holds iff the
native gadget's `AssertSpec` holds. (No range bounds here, so `NeZero p` follows from primality
alone.) -/
theorem isZero_asserts_faithful (a : ZMod p) (cols : Extracted.IsZeroOperation (ZMod p)) :
    List.Forall (· = 0) (Extracted.IsZeroOperation.asserts a cols 1) ↔
      SP1Clean.IsZeroOperation.AssertSpec a cols := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  simp only [Extracted.IsZeroOperation.asserts, List.Forall,
    SP1Clean.IsZeroOperation.AssertSpec, one_mul, bool_iff]

omit [Fact (2 ^ 17 < p)] in
/-- **Faithfulness anchor — interaction half.** `IsZeroOperation` emits no bus interactions, so its
(empty) `interactions` list trivially holds, matching the trivial `InteractSpec`. -/
theorem isZero_interactions_faithful (a : ZMod p) (cols : Extracted.IsZeroOperation (ZMod p)) :
    List.Forall Interaction.toProp (Extracted.IsZeroOperation.interactions a cols 1) ↔
      SP1Clean.IsZeroOperation.InteractSpec a cols := by
  simp only [Extracted.IsZeroOperation.interactions, List.Forall,
    SP1Clean.IsZeroOperation.InteractSpec]

omit [Fact (2 ^ 17 < p)] in
/-- Combined anchor (`asserts ∧ interactions ↔ RawSpec = AssertSpec`). Composed by
`IsZeroWord`/`IsEqualWord`. -/
theorem isZero_constraints_faithful (a : ZMod p) (cols : Extracted.IsZeroOperation (ZMod p)) :
    (List.Forall (· = 0) (Extracted.IsZeroOperation.asserts a cols 1) ∧
      List.Forall Interaction.toProp (Extracted.IsZeroOperation.interactions a cols 1)) ↔
      SP1Clean.IsZeroOperation.RawSpec a cols := by
  rw [isZero_asserts_faithful, isZero_interactions_faithful]
  simp only [SP1Clean.IsZeroOperation.InteractSpec, SP1Clean.IsZeroOperation.AssertSpec,
    SP1Clean.IsZeroOperation.RawSpec, and_true]

open SP1Clean.Channels (byteChannel)
open SP1Clean.InteractionRecovery

omit [Fact (2 ^ 17 < p)] in
/-- **Faithfulness anchor — interaction half, SYNTACTIC.** `IsZeroOperation` is a pure `assertZero` gadget:
its `main` emits no byte interactions, matching SP1's empty extracted `interactions` list — both `toAccess`
images are `[]`. -/
theorem isZero_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var SP1Clean.IsZeroOperation.Inputs (ZMod p)) (offset : ℕ)
    (a is_real : ZMod p) (cols : Extracted.IsZeroOperation (ZMod p)) :
    (Extracted.IsZeroOperation.interactions a cols is_real).map Extracted.Interaction.toAccess
      = (((SP1Clean.IsZeroOperation.main input).operations offset).interactionsWith
          byteChannel.toRaw).map (AbstractInteraction.toAccess env) := by
  have heq := fun (n : ℕ) (inp : Var (ProvablePair id id) (ZMod p)) =>
    filter_interactions_formalAssertion_eq_nil (Gadgets.Equality.circuit id) byteChannel.toRaw
      (n := n) inp List.not_mem_nil List.not_mem_nil
  simp only [SP1Clean.IsZeroOperation.main, circuit_norm, heq, Extracted.IsZeroOperation.interactions,
    List.map_nil, List.append_nil]

end SP1Clean.Faithful
