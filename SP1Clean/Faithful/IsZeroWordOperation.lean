import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Native.Operations.IsZeroWordOperation.RawSpec
import SP1Clean.Native.Operations.IsZeroWordOperation.Defs
import SP1Clean.Model.SP1Constraint
import SP1Clean.Model.InteractionProjection
import ToClean.Circuit.InteractionRecovery
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
  -- Split the four `IsZeroOperation` sub-lists at each `++` and collapse each to its `RawSpec` via
  -- the `IsZero` anchor (the design `RawSpec` references `IsZeroOperation.RawSpec` directly), leaving
  -- only the small own-tail. This keeps the `result * a` products opaque (no `mul_eq_zero` blowup).
  simp only [Extracted.IsZeroWordOperation.asserts, Extracted.IsZeroWordOperation.interactions]
  rw [forall_append_pair, forall_append_pair, forall_append_pair,
    forall_append_pair, isZero_constraints_faithful, isZero_constraints_faithful,
    isZero_constraints_faithful, isZero_constraints_faithful]
  simp only [List.Forall, IsZeroWordOperation.RawSpec, one_mul,
    bool_iff, sub_self, true_and, and_true, and_assoc]

omit [Fact (2 ^ 17 < p)] in
@[circuit_norm] theorem eval_isZeroWordColumns
    (env : Environment (ZMod p))
    (cols : Extracted.IsZeroWordOperation (Expression (ZMod p))) :
    Eval.eval env cols =
      ({ is_zero_limb_0 := Eval.eval env cols.is_zero_limb_0
         is_zero_limb_1 := Eval.eval env cols.is_zero_limb_1
         is_zero_limb_2 := Eval.eval env cols.is_zero_limb_2
         is_zero_limb_3 := Eval.eval env cols.is_zero_limb_3
         is_zero_first_half :=
           Expression.eval env cols.is_zero_first_half
         is_zero_second_half :=
           Expression.eval env cols.is_zero_second_half
         result := Expression.eval env cols.result } :
        Extracted.IsZeroWordOperation (ZMod p)) := by
  provable_struct_simp

private def isZeroWordChild
    (input : Var SP1Clean.IsZeroWordOperation.Inputs (ZMod p))
    (i : ℕ) (hi : i < 4) :
    Var SP1Clean.IsZeroOperation.Inputs (ZMod p) :=
  let cols :=
    match i with
    | 0 => input.cols.is_zero_limb_0
    | 1 => input.cols.is_zero_limb_1
    | 2 => input.cols.is_zero_limb_2
    | _ => input.cols.is_zero_limb_3
  ⟨input.a[i], cols, input.is_real⟩

private def isZeroWordOwnExpressions
    (input : Var SP1Clean.IsZeroWordOperation.Inputs (ZMod p)) :
    List (Expression (ZMod p)) :=
  let cols := input.cols
  [input.is_real * (input.is_real - 1),
    cols.result * (cols.result - 1),
    cols.is_zero_first_half -
      cols.is_zero_limb_0.result * cols.is_zero_limb_1.result,
    cols.is_zero_second_half -
      cols.is_zero_limb_2.result * cols.is_zero_limb_3.result,
    input.is_real *
      (cols.result -
        cols.is_zero_first_half * cols.is_zero_second_half)]

set_option linter.unusedSectionVars false in
-- Measured (W3/r3c/b2): clears 40000 heartbeats; the former 1M ceiling was >=25x over, removed.
private theorem isZeroWord_nativeAssertions
    (env : Environment (ZMod p))
    (input : Var SP1Clean.IsZeroWordOperation.Inputs (ZMod p))
    (offset : ℕ) :
    nativeAssertZeros env
        ((SP1Clean.IsZeroWordOperation.main input).operations offset) =
      nativeAssertZeros env
          ((SP1Clean.IsZeroOperation.main
            (isZeroWordChild input 0 (by decide))).operations offset) ++
        nativeAssertZeros env
          ((SP1Clean.IsZeroOperation.main
            (isZeroWordChild input 1 (by decide))).operations offset) ++
        nativeAssertZeros env
          ((SP1Clean.IsZeroOperation.main
            (isZeroWordChild input 2 (by decide))).operations offset) ++
        nativeAssertZeros env
          ((SP1Clean.IsZeroOperation.main
            (isZeroWordChild input 3 (by decide))).operations offset) ++
        (isZeroWordOwnExpressions input).map
          (Expression.eval env) := by
  simp only [nativeAssertZeros, SP1Clean.IsZeroWordOperation.main,
    Circuit.operations, Circuit.bind_def, assertion,
    HasAssertEq.assert_eq, Expression.assertEquals,
    Operations.localLength, Operations.constraints_append,
    Operations.constraints_subcircuit,
    constraints_toSubcircuit_formalAssertion,
    FormalAssertion.toSubcircuit_localLength,
    Operations.constraints_nil, List.map_append, List.map_nil]
  simp only [SP1Clean.IsZeroOperation.circuit_localLength,
    Gadgets.Equality.localLength_eq, Nat.add_zero]
  simp only [SP1Clean.IsZeroOperation.circuit,
    Gadgets.Equality.circuit, isZeroWordChild]
  repeat' rw [CanonicalReader.equalityAssertionList]
  simp [isZeroWordOwnExpressions, Expression.eval]

-- Measured (W3/r3c/b2): clears 40000 heartbeats; the former 1M ceiling was >=25x over, removed.
/-- Folded normalization of the native word-zero fragment to the exact generated Rust list. -/
theorem isZeroWord_assertions_exact
    (env : Environment (ZMod p))
    (input : Var SP1Clean.IsZeroWordOperation.Inputs (ZMod p))
    (offset : ℕ) :
    nativeAssertZeros env
        ((SP1Clean.IsZeroWordOperation.main input).operations offset) =
      Extracted.IsZeroWordOperation.asserts
        (Eval.eval env input.a)
        (Eval.eval env input.cols)
        (Expression.eval env input.is_real) := by
  rw [eval_isZeroWordColumns,
    isZeroWord_nativeAssertions,
    Extracted.IsZeroWordOperation.asserts]
  rw [isZero_assertions_exact env
      (isZeroWordChild input 0 (by decide)) offset,
    isZero_assertions_exact env
      (isZeroWordChild input 1 (by decide)) offset,
    isZero_assertions_exact env
      (isZeroWordChild input 2 (by decide)) offset,
    isZero_assertions_exact env
      (isZeroWordChild input 3 (by decide)) offset]
  simp only [isZeroWordChild, isZeroWordOwnExpressions,
    List.map_cons, List.map_nil]
  rw [← ProvableType.getElem_eval_fields env input.a 0 (by decide),
    ← ProvableType.getElem_eval_fields env input.a 1 (by decide),
    ← ProvableType.getElem_eval_fields env input.a 2 (by decide),
    ← ProvableType.getElem_eval_fields env input.a 3 (by decide)]
  rw [eval_isZeroColumns env input.cols.is_zero_limb_0,
    eval_isZeroColumns env input.cols.is_zero_limb_1,
    eval_isZeroColumns env input.cols.is_zero_limb_2,
    eval_isZeroColumns env input.cols.is_zero_limb_3]
  repeat' first | rw [eval_sub] | rw [eval_mul]
  simp only [eval_sub, Expression.eval]

open SP1Clean.Channels (byteChannel)
open InteractionRecovery

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
