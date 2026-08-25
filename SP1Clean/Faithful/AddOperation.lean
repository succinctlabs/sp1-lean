import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Native.Operations.AddOperation.RawSpec
import SP1Clean.Native.Operations.AddOperation.Defs
import SP1Clean.Model.SP1Constraint
import SP1Clean.Model.InteractionProjection
import ToClean.Circuit.InteractionRecovery
import SP1Clean.Faithful.ChipTactics
import SP1Clean.Extracted.InteractionModel
import SP1Clean.Extracted.AddOperation
import SP1Clean.Faithful.ChipOracle

/-! # Faithfulness anchor — `AddOperation` constraints ↔ native `AssertSpec`/`InteractSpec`

Anchors the native `AddOp` gadget's hand-written constraints to SP1's generated
`AddOperation` constraint definition (`Extracted/AddOperation.lean`). The two anchor theorems
`add_asserts_faithful` / `add_interactions_faithful` prove those two constraint lists hold
**exactly** iff the native gadget's `AssertSpec` / `InteractSpec` respectively.

The generated `constraints` is field-generic with a `[CoeHead F ℕ]` hypothesis; applying it at
`ZMod p` uses the scoped `CoeHead (ZMod p) ℕ` instance (`open scoped …ConstraintCoe`). -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
/-- **Faithfulness anchor — assertion half.** SP1's `AddOperation` `asserts` list (the five gated
carry-bool field constraints) holds iff the native gadget's `AssertSpec` (the four carry-bool
predicates) holds. -/
theorem add_asserts_faithful (a b value : Word (ZMod p)) :
    List.Forall (· = 0) (Extracted.AddOperation.asserts a b ⟨value⟩ 1) ↔
      SP1Clean.AddOperation.AssertSpec a b value := by
  simp only [Extracted.AddOperation.asserts, List.Forall,
    SP1Clean.AddOperation.AssertSpec, one_mul, add_zero, sub_self, mul_zero, true_and,
    bool_iff]

/-- **Faithfulness anchor — interaction half.** SP1's `AddOperation` `interactions` list (the four
`Range` byte sends) holds iff the native gadget's `InteractSpec` (the four limb-range predicates)
holds. Together with `add_asserts_faithful`, native-gadget proofs (which route through `AssertSpec`
and `InteractSpec`) are faithful to SP1's operation constraints. -/
theorem add_interactions_faithful (a b value : Word (ZMod p)) :
    List.Forall Interaction.toProp (Extracted.AddOperation.interactions a b ⟨value⟩ 1) ↔
      SP1Clean.AddOperation.InteractSpec value := by
  simp only [Extracted.AddOperation.interactions, List.Forall,
    Interaction.toProp_send_byte, ByteOpcode.constrainField_six,
    ByteOpcode.constrain_Range, val_16, one_ne_zero, ne_eq, not_false_eq_true, true_implies,
    SP1Clean.AddOperation.InteractSpec, show (2 : ℕ) ^ 16 = 65536 by norm_num]

@[circuit_norm] theorem eval_addColumns
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : SP1Clean.AddOperation.Columns (Expression F)) :
    Eval.eval env cols =
      ({ value := Eval.eval env cols.value } :
        SP1Clean.AddOperation.Columns F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] theorem eval_extractedAddColumns
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.AddOperation (Expression F)) :
    Eval.eval env cols =
      ({ value := Eval.eval env cols.value } :
        Extracted.AddOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

private def addAssertionExpressions
    (input : Var SP1Clean.AddOperation.Inputs (ZMod p)) :
    List (Expression (ZMod p)) :=
  let c0 :=
    (input.a[0] + input.b[0] - input.cols.value[0]) *
      (65536 : ZMod p)⁻¹
  let c1 :=
    (input.a[1] + input.b[1] - input.cols.value[1] + c0) *
      (65536 : ZMod p)⁻¹
  let c2 :=
    (input.a[2] + input.b[2] - input.cols.value[2] + c1) *
      (65536 : ZMod p)⁻¹
  let c3 :=
    (input.a[3] + input.b[3] - input.cols.value[3] + c2) *
      (65536 : ZMod p)⁻¹
  [input.is_real * (input.is_real - 1),
    input.is_real * (c0 * (c0 - 1)),
    input.is_real * (c1 * (c1 - 1)),
    input.is_real * (c2 * (c2 - 1)),
    input.is_real * (c3 * (c3 - 1))]

omit [Fact (2 ^ 17 < p)] in
private theorem add_nativeAssertions
    (env : Environment (ZMod p))
    (input : Var SP1Clean.AddOperation.Inputs (ZMod p))
    (offset : ℕ) :
    nativeAssertZeros env
        ((SP1Clean.AddOperation.main input).operations offset) =
      (addAssertionExpressions input).map
        (Expression.eval env) := by
  unfold nativeAssertZeros
  simp [SP1Clean.AddOperation.main, addAssertionExpressions,
    circuit_norm, Expression.eval]

omit [Fact (2 ^ 17 < p)] in
/-- Folded normalization of the native add fragment to the exact generated Rust assertion list. -/
theorem add_assertions_exact
    (env : Environment (ZMod p))
    (input : Var SP1Clean.AddOperation.Inputs (ZMod p))
    (offset : ℕ) :
    nativeAssertZeros env
        ((SP1Clean.AddOperation.main input).operations offset) =
      Extracted.AddOperation.asserts
        (Eval.eval env input.a) (Eval.eval env input.b)
        ⟨Eval.eval env input.cols.value⟩
        (Expression.eval env input.is_real) := by
  rw [add_nativeAssertions, Extracted.AddOperation.asserts]
  simp only [addAssertionExpressions, List.map_cons, List.map_nil,
    eval_sub, Expression.eval, ProvableType.getElem_eval_fields,
    add_zero]

open SP1Clean.Channels (byteChannel)
open InteractionRecovery

/-- **Faithfulness anchor — interaction half, SYNTACTIC** (the canonical replacement for the `toProp`
`add_interactions_faithful`). Instead of an *interpreter* mapping a byte send to `mult ≠ 0 →
op.constrain …` (and every non-byte interaction to `True`), this compares the **emitted interaction
list itself**: SP1's extracted `AddOperation.interactions` and the Clean circuit's emitted byte
interactions project — through `Extracted.Interaction.toAccess` / `AbstractInteraction.toAccess` — to
the **same** `LookupAccess` list `(kind, table, argvals, signedmult)`. No semantics (`op.constrain`,
`< 65536`), just interaction modeling: channel, message arg values, and the signed multiplicity (the
byte *pull* sink sign `-is_real`). Under an `env` realising the result-limb columns (`h_v*`) and
`is_real` (`h_ir`). The byte tuple `[6, value[i].val, 16, 0]` matches field-for-field; the sole modeling
fact is the byte send/receive (sink) sign, recorded in `Extracted.Interaction.toAccess`'s `.byte` arm.
The `a b` operands are ignored by `interactions` (`_a`/`_b`), so they are passed as `value` here. -/
theorem add_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var SP1Clean.AddOperation.Inputs (ZMod p)) (offset : ℕ)
    (value : Word (ZMod p)) (is_real : ZMod p)
    (h_ir : Expression.eval env input.is_real = is_real)
    (h_v0 : Expression.eval env input.cols.value[0] = value[0])
    (h_v1 : Expression.eval env input.cols.value[1] = value[1])
    (h_v2 : Expression.eval env input.cols.value[2] = value[2])
    (h_v3 : Expression.eval env input.cols.value[3] = value[3]) :
    (Extracted.AddOperation.interactions value value ⟨value⟩ is_real).map
        Extracted.Interaction.toAccess
      = (((SP1Clean.AddOperation.main input).operations offset).interactionsWith
          byteChannel.toRaw).map (AbstractInteraction.toAccess env) := by
  have h6 : (6 : ZMod p).val = 6 := val_6_zmod_p
  have hk := toAccess_pullIf_byte_forall env
  -- RHS: recover the 4 byte pulls from `main`; LHS: expand the extracted list + projection.
  simp only [SP1Clean.AddOperation.main, circuit_norm, hk,
    Extracted.AddOperation.interactions, List.map_cons, List.map_nil,
    Extracted.Interaction.toAccess_byte, h_ir, h_v0, h_v1, h_v2, h_v3, h6]

/-- **Faithfulness anchor — combined.** The two-list pair form of `add_asserts_faithful` /
`add_interactions_faithful`. Legacy `toProp` form — this module's only live external consumer is
`Faithful/DivRemChip/Exact.lean`; the canonical interaction anchor is
`add_interactions_faithful_syntactic`. -/
theorem add_constraints_faithful (a b value : Word (ZMod p)) :
    (List.Forall (· = 0) (Extracted.AddOperation.asserts a b ⟨value⟩ 1) ∧
        List.Forall Interaction.toProp (Extracted.AddOperation.interactions a b ⟨value⟩ 1)) ↔
      (SP1Clean.AddOperation.AssertSpec a b value ∧
        SP1Clean.AddOperation.InteractSpec value) := by
  rw [add_asserts_faithful, add_interactions_faithful]

end SP1Clean.Faithful
