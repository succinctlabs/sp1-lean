import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Native.Operations.IsZeroOperation.RawSpec
import SP1Clean.Native.Operations.IsZeroOperation.Defs
import SP1Clean.Model.SP1Constraint
import SP1Clean.Model.InteractionProjection
import SP1Clean.Model.InteractionRecovery
import SP1Clean.Faithful.ExtractedInteractionModel
import SP1Clean.Extracted.IsZeroOperation
import SP1Clean.Faithful.ChipTactics
import SP1Clean.Faithful.ChipOracle

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

variable {p : ℕ} [Fact p.Prime]

/-- **Faithfulness anchor — assertion half.** SP1's `IsZeroOperation` `asserts` list holds iff the
native gadget's `AssertSpec` holds. (No range bounds here, so `NeZero p` follows from primality
alone.) -/
theorem isZero_asserts_faithful (a : ZMod p) (cols : Extracted.IsZeroOperation (ZMod p)) :
    List.Forall (· = 0) (Extracted.IsZeroOperation.asserts a cols 1) ↔
      SP1Clean.IsZeroOperation.AssertSpec a cols := by
  simp only [Extracted.IsZeroOperation.asserts, List.Forall,
    SP1Clean.IsZeroOperation.AssertSpec, one_mul, bool_iff]

/-- **Faithfulness anchor — interaction half.** `IsZeroOperation` emits no bus interactions, so its
(empty) `interactions` list trivially holds, matching the trivial `InteractSpec`. -/
theorem isZero_interactions_faithful (a : ZMod p) (cols : Extracted.IsZeroOperation (ZMod p)) :
    List.Forall Interaction.toProp (Extracted.IsZeroOperation.interactions a cols 1) ↔
      SP1Clean.IsZeroOperation.InteractSpec a cols := by
  simp only [Extracted.IsZeroOperation.interactions, List.Forall,
    SP1Clean.IsZeroOperation.InteractSpec]

/-- Combined anchor (`asserts ∧ interactions ↔ RawSpec = AssertSpec`). Composed by
`IsZeroWord`/`IsEqualWord`. -/
theorem isZero_constraints_faithful (a : ZMod p) (cols : Extracted.IsZeroOperation (ZMod p)) :
    (List.Forall (· = 0) (Extracted.IsZeroOperation.asserts a cols 1) ∧
      List.Forall Interaction.toProp (Extracted.IsZeroOperation.interactions a cols 1)) ↔
      SP1Clean.IsZeroOperation.RawSpec a cols := by
  rw [isZero_asserts_faithful, isZero_interactions_faithful]
  simp only [SP1Clean.IsZeroOperation.InteractSpec, SP1Clean.IsZeroOperation.AssertSpec,
    SP1Clean.IsZeroOperation.RawSpec, and_true]

@[circuit_norm] theorem eval_isZeroColumns
    (env : Environment (ZMod p))
    (cols : Extracted.IsZeroOperation (Expression (ZMod p))) :
    Eval.eval env cols =
      ({ inverse := Expression.eval env cols.inverse
         result := Expression.eval env cols.result } :
        Extracted.IsZeroOperation (ZMod p)) := by
  provable_struct_simp

private def isZeroAssertionExpressions
    (input : Var SP1Clean.IsZeroOperation.Inputs (ZMod p)) :
    List (Expression (ZMod p)) :=
  let e0 := input.cols.inverse * input.a
  let e1 := 1 - e0
  let e2 := e1 - input.cols.result
  let e3 := input.is_real * e2
  let e4 := input.cols.result - 1
  let e5 := input.cols.result * e4
  let e6 := input.is_real * e5
  let e7 := input.cols.result * input.a
  let e8 := input.is_real * e7
  [e3, e6, e8]

private theorem isZero_nativeAssertions
    (env : Environment (ZMod p))
    (input : Var SP1Clean.IsZeroOperation.Inputs (ZMod p))
    (offset : ℕ) :
    nativeAssertZeros env
        ((SP1Clean.IsZeroOperation.main input).operations offset) =
      (isZeroAssertionExpressions input).map
        (Expression.eval env) := by
  unfold nativeAssertZeros
  simp only [SP1Clean.IsZeroOperation.main, circuit_norm,
    List.map_append]
  repeat' rw [CanonicalReader.equalityAssertionList]
  simp [isZeroAssertionExpressions, Expression.eval]

/-- Folded normalization of the native assertion fragment to the exact generated Rust list.
This is an implementation lemma for whole-chip `ChipFaithful` proofs, not an additional
operation-level verification boundary. -/
theorem isZero_assertions_exact
    (env : Environment (ZMod p))
    (input : Var SP1Clean.IsZeroOperation.Inputs (ZMod p))
    (offset : ℕ) :
    nativeAssertZeros env
        ((SP1Clean.IsZeroOperation.main input).operations offset) =
      Extracted.IsZeroOperation.asserts
        (Expression.eval env input.a)
        (Eval.eval env input.cols)
        (Expression.eval env input.is_real) := by
  rw [eval_isZeroColumns, isZero_nativeAssertions,
    Extracted.IsZeroOperation.asserts]
  simp only [isZeroAssertionExpressions, List.map_cons,
    List.map_nil, Expression.eval]
  repeat' first | rw [eval_sub] | rw [eval_mul]
  simp only [Expression.eval]

open SP1Clean.Channels (byteChannel)
open SP1Clean.InteractionRecovery

/-- **Faithfulness anchor — interaction half, SYNTACTIC.** `IsZeroOperation` is a pure `assertZero` gadget:
its `main` emits no byte interactions, matching SP1's empty extracted `interactions` list — both `toAccess`
images are `[]`. -/
theorem isZero_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var SP1Clean.IsZeroOperation.Inputs (ZMod p)) (offset : ℕ)
    (a is_real : ZMod p) (cols : Extracted.IsZeroOperation (ZMod p)) :
    (Extracted.IsZeroOperation.interactions a cols is_real).map Extracted.Interaction.toAccess
      = (((SP1Clean.IsZeroOperation.main input).operations offset).interactionsWith
          byteChannel.toRaw).map (AbstractInteraction.toAccess env) := by
  have heq := fun (n : ℕ) inp =>
    @filter_interactions_formalAssertion_eq_nil (ZMod p) _ (ProvablePair field field)
      ProvablePair.instance (Gadgets.Equality.circuit field) byteChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  simp only [SP1Clean.IsZeroOperation.main, circuit_norm, heq, Extracted.IsZeroOperation.interactions,
    List.map_nil, List.append_nil]

end SP1Clean.Faithful
