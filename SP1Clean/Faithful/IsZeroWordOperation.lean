import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Native.Operations.IsZeroWordOperation.RawSpec
import SP1Clean.Extracted.Circuit.IsZeroWordOperation
import SP1Clean.Model.SP1Constraint
import SP1Clean.Model.InteractionProjection
import SP1Clean.Model.InteractionRecovery
import SP1Clean.Faithful.ExtractedInteractionModel
import SP1Clean.Extracted.IsZeroWordOperation
import SP1Clean.Faithful.IsZeroOperation
import SP1Clean.Faithful.ChipTactics

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

open SP1Clean.Channels (byteChannel)
open SP1Clean.InteractionRecovery

omit [Fact (2 ^ 17 < p)] in
/-- **Faithfulness anchor — interaction half, SYNTACTIC.** `IsZeroWordOperation` composes four
`IsZeroOperation` subcircuits (each emits nothing) plus `assertZero` gates; its `main` emits no byte
interactions, matching SP1's empty extracted `interactions` (the four composed `IsZero` lists are each `[]`). -/
theorem isZeroWord_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var SP1Clean.IsZeroWordOperation.Inputs (ZMod p)) (offset : ℕ)
    (a : Word (ZMod p)) (is_real : ZMod p) (cols : Extracted.IsZeroWordOperation (ZMod p)) :
    (Extracted.IsZeroWordOperation.interactions a cols is_real).map Extracted.Interaction.toAccess
      = (((SP1Clean.IsZeroWordOperation.main input).operations offset).interactionsWith
          byteChannel.toRaw).map (AbstractInteraction.toAccess env) := by
  have heqZ := fun (n : ℕ) (inp : Var SP1Clean.IsZeroOperation.Inputs (ZMod p)) =>
    filter_interactions_formalAssertion_eq_nil SP1Clean.IsZeroOperation.circuit byteChannel.toRaw
      (n := n) inp List.not_mem_nil List.not_mem_nil
  have heqEq := fun (n : ℕ) (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil (ZMod p) _ (ProvablePair field field)
      ProvablePair.instance (Gadgets.Equality.circuit field) byteChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  simp only [SP1Clean.IsZeroWordOperation.main, circuit_norm, heqZ, heqEq,
    Extracted.IsZeroWordOperation.interactions, Extracted.IsZeroOperation.interactions,
    List.map_nil, List.append_nil]

end SP1Clean.Faithful
