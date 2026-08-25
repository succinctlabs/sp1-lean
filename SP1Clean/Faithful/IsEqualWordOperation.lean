import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Native.Operations.IsEqualWordOperation.RawSpec
import SP1Clean.Native.Operations.IsEqualWordOperation.Defs
import SP1Clean.Model.SP1Constraint
import SP1Clean.Model.InteractionProjection
import ToClean.Circuit.InteractionRecovery
import SP1Clean.Extracted.InteractionModel
import SP1Clean.Extracted.IsEqualWordOperation
import SP1Clean.Faithful.IsZeroWordOperation
import SP1Clean.Faithful.ChipTactics

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
/-- **Faithfulness anchor.** SP1's `IsEqualWordOperation` constraint list holds iff the native
gadget's `RawSpec` holds. -/
theorem isEqualWord_constraints_faithful (a b : Word (ZMod p))
    (cols : Extracted.IsEqualWordOperation (ZMod p)) :
    (List.Forall (· = 0) (Extracted.IsEqualWordOperation.asserts a b cols 1) ∧
      List.Forall Interaction.toProp (Extracted.IsEqualWordOperation.interactions a b cols 1)) ↔
      SP1Clean.IsEqualWordOperation.RawSpec a b cols := by
  simp only [Extracted.IsEqualWordOperation.asserts, Extracted.IsEqualWordOperation.interactions,
    Extracted.IsZeroWordOperation.asserts, Extracted.IsZeroWordOperation.interactions,
    Extracted.IsZeroOperation.asserts, Extracted.IsZeroOperation.interactions, one_mul,
    List.cons_append, List.nil_append, List.Forall, bool_iff,
    IsEqualWordOperation.RawSpec, IsZeroWordOperation.RawSpec, IsZeroOperation.RawSpec, and_assoc]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, mul_eq_zero,
    List.getElem_cons_succ, sub_self, and_true, true_and]

omit [Fact (2 ^ 17 < p)] in
@[circuit_norm] theorem eval_isEqualWordColumns
    (env : Environment (ZMod p))
    (cols : Extracted.IsEqualWordOperation (Expression (ZMod p))) :
    Eval.eval env cols =
      ({ is_diff_zero := Eval.eval env cols.is_diff_zero } :
        Extracted.IsEqualWordOperation (ZMod p)) := by
  provable_struct_simp

private def isEqualWordChild
    (input : Var SP1Clean.IsEqualWordOperation.Inputs (ZMod p)) :
    Var SP1Clean.IsZeroWordOperation.Inputs (ZMod p) :=
  ⟨#v[input.a[0] - input.b[0], input.a[1] - input.b[1],
      input.a[2] - input.b[2], input.a[3] - input.b[3]],
    input.cols.is_diff_zero, input.is_real⟩

-- Perf (measured 2026-07-28, control at 1 heartbeat gave a real timeout): elaborates inside 40000
-- heartbeats, so the plain default carries >=5x headroom — the former 1000000-heartbeat ceiling
-- was >=25x over and has been removed.
set_option linter.unusedSectionVars false in
private theorem isEqualWord_nativeAssertions
    (env : Environment (ZMod p))
    (input : Var SP1Clean.IsEqualWordOperation.Inputs (ZMod p))
    (offset : ℕ) :
    nativeAssertZeros env
        ((SP1Clean.IsEqualWordOperation.main input).operations offset) =
      nativeAssertZeros env
          ((SP1Clean.IsZeroWordOperation.main
            (isEqualWordChild input)).operations offset) ++
        [Expression.eval env
          (input.is_real * (input.is_real - 1))] := by
  simp only [nativeAssertZeros, SP1Clean.IsEqualWordOperation.main,
    Circuit.operations, Circuit.bind_def, assertion,
    HasAssertEq.assert_eq, Expression.assertEquals,
    Operations.localLength, Operations.constraints_append,
    Operations.constraints_subcircuit,
    constraints_toSubcircuit_formalAssertion,
    FormalAssertion.toSubcircuit_localLength,
    Operations.constraints_nil, List.map_append, List.map_nil]
  simp only [SP1Clean.IsZeroWordOperation.circuit_localLength,
    Nat.add_zero]
  simp only [SP1Clean.IsZeroWordOperation.circuit,
    Gadgets.Equality.circuit]
  rw [CanonicalReader.equalityAssertionList]
  simp [isEqualWordChild, Expression.eval]

/-- Folded normalization of the native word-equality fragment to the exact generated Rust list.

Perf (measured 2026-07-28, control at 2 heartbeats gave a real timeout): elaborates inside 40000
heartbeats, so the plain default carries >=5x headroom — the former 1000000-heartbeat ceiling was
>=25x over and has been removed. -/
theorem isEqualWord_assertions_exact
    (env : Environment (ZMod p))
    (input : Var SP1Clean.IsEqualWordOperation.Inputs (ZMod p))
    (offset : ℕ) :
    nativeAssertZeros env
        ((SP1Clean.IsEqualWordOperation.main input).operations offset) =
      Extracted.IsEqualWordOperation.asserts
        (Eval.eval env input.a) (Eval.eval env input.b)
        (Eval.eval env input.cols)
        (Expression.eval env input.is_real) := by
  rw [eval_isEqualWordColumns,
    isEqualWord_nativeAssertions,
    Extracted.IsEqualWordOperation.asserts,
    isZeroWord_assertions_exact env (isEqualWordChild input) offset]
  simp only [isEqualWordChild]
  have hdiff :
      Eval.eval env
          #v[input.a[0] - input.b[0], input.a[1] - input.b[1],
            input.a[2] - input.b[2], input.a[3] - input.b[3]] =
        #v[(Eval.eval env input.a)[0] - (Eval.eval env input.b)[0],
          (Eval.eval env input.a)[1] - (Eval.eval env input.b)[1],
          (Eval.eval env input.a)[2] - (Eval.eval env input.b)[2],
          (Eval.eval env input.a)[3] - (Eval.eval env input.b)[3]] := by
    rw [ProvableType.eval_fields]
    ext k hk
    interval_cases k <;>
      simp [eval_sub, ProvableType.getElem_eval_fields]
  rw [hdiff]
  simp only [eval_sub, Expression.eval]

open SP1Clean.Channels (byteChannel)
open InteractionRecovery

omit [Fact (2 ^ 17 < p)] in
/-- **Faithfulness anchor — interaction half, SYNTACTIC.** `IsEqualWordOperation` composes one
`IsZeroWordOperation` subcircuit (which itself emits nothing) plus `assertZero` gates; its `main` emits no
byte interactions, matching SP1's empty extracted `interactions`. -/
theorem isEqualWord_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var SP1Clean.IsEqualWordOperation.Inputs (ZMod p)) (offset : ℕ)
    (a b : Word (ZMod p)) (is_real : ZMod p) (cols : Extracted.IsEqualWordOperation (ZMod p)) :
    (Extracted.IsEqualWordOperation.interactions a b cols is_real).map Extracted.Interaction.toAccess
      = (((SP1Clean.IsEqualWordOperation.main input).operations offset).interactionsWith
          byteChannel.toRaw).map (AbstractInteraction.toAccess env) := by
  have heqZW := fun (n : ℕ) (inp : Var SP1Clean.IsZeroWordOperation.Inputs (ZMod p)) =>
    filter_interactions_formalAssertion_eq_nil SP1Clean.IsZeroWordOperation.circuit byteChannel.toRaw
      (n := n) inp List.not_mem_nil List.not_mem_nil
  have heqEq := fun (n : ℕ) (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil (ZMod p) _ (ProvablePair field field)
      ProvablePair.instance (Gadgets.Equality.circuit field) byteChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  simp only [SP1Clean.IsEqualWordOperation.main, circuit_norm, heqZW, heqEq,
    Extracted.IsEqualWordOperation.interactions, Extracted.IsZeroWordOperation.interactions,
    Extracted.IsZeroOperation.interactions, List.map_nil, List.append_nil]

end SP1Clean.Faithful
