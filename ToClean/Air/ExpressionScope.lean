module

public import Clean.Air.Extraction.Lower
import all Clean.Air.Extraction.Lower
public import ToClean.Air.TableBuild

/-! # Physical prefix evaluation from Clean's extraction scope check

Clean rejects AIR expressions whose variable indices exceed the component width. These lemmas
give its existing `expressionBadVariable` check a semantic consequence: evaluation is unchanged
when environments agree below that width. In particular, truncating a wider physical row to the
checked prefix preserves constraints without lookups and the literal interaction ledger.

This is a proof extension to the upstream lowering check, not another expression representation
or evaluator. Lookup predicates and channel guarantees can depend on prover data and still need
their own transport proofs. The implementation import exposes the existing scope checker to
these proofs; remove it when upstream exports the corresponding evaluation lemmas.
-/

@[expose] public section

namespace Air.Flat.Extraction

variable {F : Type} [FiniteField F]

/-- A successful upstream scope check restricts evaluation to cells below the checked width. -/
theorem eval_eq_of_expressionBadVariable_eq_none {width : ℕ} {env env' : Environment F}
    (agree : ∀ index < width, env.get index = env'.get index)
    (expression : Expression F) (scope : expressionBadVariable width expression = none) :
    expression.eval env = expression.eval env' := by
  induction expression with
  | var cell =>
    simp only [expressionBadVariable] at scope
    split at scope
    next bound => exact agree cell.index bound
    next => contradiction
  | const => rfl
  | add left right ihLeft ihRight | mul left right ihLeft ihRight =>
    simp only [expressionBadVariable] at scope
    have leftScope : expressionBadVariable width left = none := by
      cases h : expressionBadVariable width left <;> simp_all
    have rightScope : expressionBadVariable width right = none := by
      simpa only [leftScope, Option.orElse_none] using scope
    simp only [Expression.eval, ihLeft leftScope, ihRight rightScope]

/-- Prefix extraction preserves every cell the upstream scope check permits. -/
theorem eval_extract {width : ℕ} (row : Array F) (data data' : ProverData F)
    (expression : Expression F) (scope : expressionBadVariable width expression = none) :
    expression.eval (Environment.fromArray (row.extract 0 width) data') =
      expression.eval (Environment.fromArray row data) := by
  apply eval_eq_of_expressionBadVariable_eq_none (width := width) ?_ expression scope
  intro index bound
  by_cases inside : index < row.size
  · simp [bound, inside]
  · simp [bound, inside]

/-- A lookup-free component's checked assertions are preserved by physical prefix projection. -/
theorem constraints_extract {width : ℕ} {ops : Operations F} (row : Array F)
    (data data' : ProverData F) (lookups : ops.lookups = [])
    (scope : expressionsBadVariable width ops.constraints = none)
    (checked : ops.ConstraintsHold (Environment.fromArray row data)) :
    ops.ConstraintsHold (Environment.fromArray (row.extract 0 width) data') := by
  refine ⟨?_, by simp [lookups]⟩
  intro expression member
  exact (eval_extract row data data' expression
    ((List.findSome?_eq_none_iff.mp scope) expression member)).trans (checked.1 expression member)

/-- A checked interaction keeps its multiplicity and message, including disabled occurrences. -/
theorem interaction_eval_extract {width : ℕ} (row : Array F) (data data' : ProverData F)
    (interaction : AbstractInteraction F)
    (scope : expressionsBadVariable width
      (interaction.mult :: interaction.msg.toList) = none) :
    interaction.eval (Environment.fromArray (row.extract 0 width) data') =
      interaction.eval (Environment.fromArray row data) := by
  have scope := List.findSome?_eq_none_iff.mp scope
  have message : interaction.msg.map (Expression.eval (Environment.fromArray (row.extract 0 width) data')) =
      interaction.msg.map (Expression.eval (Environment.fromArray row data)) := by
    apply Vector.ext
    intro index bound
    simp only [Vector.getElem_map]
    exact eval_extract row data data' _ (scope _ (List.mem_cons_of_mem _ (by
      simpa only [Vector.mem_toList_iff] using Vector.getElem_mem (xs := interaction.msg) bound)))
  simp only [AbstractInteraction.eval, message,
    eval_extract row data data' interaction.mult (scope _ (List.mem_cons_self ..))]

end Air.Flat.Extraction
