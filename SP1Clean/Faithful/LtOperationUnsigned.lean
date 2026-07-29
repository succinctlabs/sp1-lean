import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Native.Operations.LtOperationUnsigned.RawSpec
import SP1Clean.Native.Operations.LtOperationUnsigned.Defs
import SP1Clean.Model.SP1Constraint
import SP1Clean.Model.InteractionProjection
import SP1Clean.Model.InteractionRecovery
import SP1Clean.Faithful.ExtractedInteractionModel
import SP1Clean.Faithful.U16CompareOperation
import SP1Clean.Extracted.LtOperationUnsigned
import SP1Clean.Faithful.ChipTactics

/-! # Faithfulness anchor to the SP1 (Rust-extraction) constraints (LtUnsigned)

Anchors the native `LtOperationUnsigned` gadget's `RawSpec` to **SP1's `LtOperationUnsigned`
constraint definition** (`Extracted/LtOperationUnsigned.lean`: a `U16CompareOperation` sub-list plus
thirteen `assertZero`s — flag booleans, the sum-bound, the limb-selection products, the two
limb-extraction equalities, and the non-equality witness). Same recipe as the simpler anchors, with
`zero_add` to absorb the `0 +` accumulator seeds. -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

-- The former 2M ceiling was ~33x over; measured floor in (50000, 60000], kept at 6.7x headroom.
set_option maxHeartbeats 400000 in
/-- **Faithfulness anchor.** SP1's `LtOperationUnsigned` constraint list holds iff the native
gadget's `RawSpec` holds. -/
theorem ltUnsigned_constraints_faithful (b cc : Word (ZMod p))
    (cols : Extracted.LtOperationUnsigned (ZMod p)) :
    (List.Forall (· = 0) (Extracted.LtOperationUnsigned.asserts b cc cols 1) ∧
      List.Forall Interaction.toProp (Extracted.LtOperationUnsigned.interactions b cc cols 1)) ↔
      SP1Clean.LtOperationUnsigned.RawSpec b cc cols := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [Extracted.LtOperationUnsigned.asserts, Extracted.LtOperationUnsigned.interactions,
    Extracted.U16CompareOperation.asserts, Extracted.U16CompareOperation.interactions,
    List.Forall, List.cons_append, List.nil_append,
    Interaction.toProp_send_byte, ByteOpcode.constrainField_six,
    ByteOpcode.constrain_Range, val_16, one_ne_zero, ne_eq, not_false_eq_true, true_implies,
    SP1Clean.LtOperationUnsigned.RawSpec, SP1Clean.U16CompareOperation.RawSpec,
    Nat.cast_zero, Nat.cast_one,
    zero_add, sub_self, mul_zero, true_and, and_assoc, bool_iff,
    show (2 : ℕ) ^ 16 = 65536 by norm_num]
  itauto

@[circuit_norm] theorem eval_ltUnsignedColumns
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.LtOperationUnsigned (Expression F)) :
    Eval.eval env cols =
      ({ u16_compare_operation :=
           Eval.eval env cols.u16_compare_operation
         u16_flags := Eval.eval env cols.u16_flags
         not_eq_inv := Eval.eval env cols.not_eq_inv
         comparison_limbs := Eval.eval env cols.comparison_limbs } :
        Extracted.LtOperationUnsigned F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

omit [Fact (2 ^ 17 < p)] in
private theorem ltUnsigned_equalityConstraintsExact
    (value : Expression (ZMod p)) (offset : ℕ) :
    ((Gadgets.Equality.main (M := field)
      (value, 0)).operations offset).constraints = [value - 0] := by
  simp [Gadgets.Equality.main, circuit_norm,
    explicit_provable_type]

private def ltUnsignedAssertionTail
    (b cc : Word (ZMod p))
    (cols : Extracted.LtOperationUnsigned (ZMod p))
    (isReal : ZMod p) : List (ZMod p) :=
  let sum3 := (0 : ZMod p) + cols.u16_flags[3]
  let sum2 := sum3 + cols.u16_flags[2]
  let sum1 := sum2 + cols.u16_flags[1]
  let selectedAll := sum1 + cols.u16_flags[0]
  let flagTotal :=
    cols.u16_flags[0] + cols.u16_flags[1] +
      cols.u16_flags[2] + cols.u16_flags[3]
  let comparison0 :=
    (0 : ZMod p) + b[3] * cols.u16_flags[3] +
      b[2] * cols.u16_flags[2] +
      b[1] * cols.u16_flags[1] + b[0] * cols.u16_flags[0]
  let comparison1 :=
    (0 : ZMod p) + cc[3] * cols.u16_flags[3] +
      cc[2] * cols.u16_flags[2] +
      cc[1] * cols.u16_flags[1] + cc[0] * cols.u16_flags[0]
  [isReal * (isReal - 1),
    cols.u16_flags[0] * (cols.u16_flags[0] - 1),
    cols.u16_flags[1] * (cols.u16_flags[1] - 1),
    cols.u16_flags[2] * (cols.u16_flags[2] - 1),
    cols.u16_flags[3] * (cols.u16_flags[3] - 1),
    flagTotal * (flagTotal - 1),
    (isReal - sum3) * (b[3] - cc[3]),
    (isReal - sum2) * (b[2] - cc[2]),
    (isReal - sum1) * (b[1] - cc[1]),
    (isReal - selectedAll) * (b[0] - cc[0]),
    comparison0 - cols.comparison_limbs[0],
    comparison1 - cols.comparison_limbs[1],
    ((1 : ZMod p) - flagTotal - (1 : ZMod p)) *
      (cols.not_eq_inv *
        (cols.comparison_limbs[0] - cols.comparison_limbs[1]) -
          isReal)]

omit [Fact (2 ^ 17 < p)] in
private theorem extracted_ltUnsignedAssertions_decompose
    (b cc : Word (ZMod p))
    (cols : Extracted.LtOperationUnsigned (ZMod p))
    (isReal : ZMod p) :
    Extracted.LtOperationUnsigned.asserts b cc cols isReal =
      Extracted.U16CompareOperation.asserts
          cols.comparison_limbs[0] cols.comparison_limbs[1]
          cols.u16_compare_operation isReal ++
        ltUnsignedAssertionTail b cc cols isReal := by
  rw [Extracted.LtOperationUnsigned.asserts]
  simp [ltUnsignedAssertionTail]

private def ltUnsignedConstraintTail
    (input : Var SP1Clean.LtOperationUnsigned.Inputs (ZMod p)) :
    List (Expression (ZMod p)) :=
  let b := input.b
  let cc := input.cc
  let cols := input.cols
  let isReal := input.is_real
  let sum3 := (0 : Expression (ZMod p)) + cols.u16_flags[3]
  let sum2 := sum3 + cols.u16_flags[2]
  let sum1 := sum2 + cols.u16_flags[1]
  let selectedAll := sum1 + cols.u16_flags[0]
  let flagTotal :=
    cols.u16_flags[0] + cols.u16_flags[1] +
      cols.u16_flags[2] + cols.u16_flags[3]
  let comparison0 :=
    (0 : Expression (ZMod p)) +
      b[3] * cols.u16_flags[3] + b[2] * cols.u16_flags[2] +
      b[1] * cols.u16_flags[1] + b[0] * cols.u16_flags[0]
  let comparison1 :=
    (0 : Expression (ZMod p)) +
      cc[3] * cols.u16_flags[3] + cc[2] * cols.u16_flags[2] +
      cc[1] * cols.u16_flags[1] + cc[0] * cols.u16_flags[0]
  [isReal * (isReal - 1) - 0,
    cols.u16_flags[0] * (cols.u16_flags[0] - 1) - 0,
    cols.u16_flags[1] * (cols.u16_flags[1] - 1) - 0,
    cols.u16_flags[2] * (cols.u16_flags[2] - 1) - 0,
    cols.u16_flags[3] * (cols.u16_flags[3] - 1) - 0,
    flagTotal * (flagTotal - 1) - 0,
    (isReal - sum3) * (b[3] - cc[3]) - 0,
    (isReal - sum2) * (b[2] - cc[2]) - 0,
    (isReal - sum1) * (b[1] - cc[1]) - 0,
    (isReal - selectedAll) * (b[0] - cc[0]) - 0,
    (comparison0 - cols.comparison_limbs[0]) - 0,
    (comparison1 - cols.comparison_limbs[1]) - 0,
    (((1 : Expression (ZMod p)) - flagTotal -
      (1 : Expression (ZMod p))) *
      (cols.not_eq_inv *
        (cols.comparison_limbs[0] - cols.comparison_limbs[1]) -
          isReal)) - 0]

private theorem ltUnsigned_constraints_decompose
    (input : Var SP1Clean.LtOperationUnsigned.Inputs (ZMod p))
    (offset : ℕ) :
    ((SP1Clean.LtOperationUnsigned.main input).operations
        offset).constraints =
      ((SP1Clean.U16CompareOperation.main
        ⟨input.cols.comparison_limbs[0],
          input.cols.comparison_limbs[1],
          { bit := input.cols.u16_compare_operation.bit },
          input.is_real⟩).operations offset).constraints ++
        ltUnsignedConstraintTail input := by
  simp only [SP1Clean.LtOperationUnsigned.main,
    SP1Clean.U16CompareOperation.circuit, circuit_norm]
  repeat rw [ltUnsigned_equalityConstraintsExact]
  unfold ltUnsignedConstraintTail
  rfl

omit [Fact (2 ^ 17 < p)] in
private theorem ltUnsignedConstraintTail_eval
    (env : Environment (ZMod p))
    (input : Var SP1Clean.LtOperationUnsigned.Inputs (ZMod p)) :
    (ltUnsignedConstraintTail input).map (Expression.eval env) =
      ltUnsignedAssertionTail
        (Eval.eval env input.b) (Eval.eval env input.cc)
        (Eval.eval env input.cols)
        (Expression.eval env input.is_real) := by
  have hb0 :=
    (ProvableType.getElem_eval_fields env input.b 0 (by decide)).symm
  have hb1 :=
    (ProvableType.getElem_eval_fields env input.b 1 (by decide)).symm
  have hb2 :=
    (ProvableType.getElem_eval_fields env input.b 2 (by decide)).symm
  have hb3 :=
    (ProvableType.getElem_eval_fields env input.b 3 (by decide)).symm
  have hc0 :=
    (ProvableType.getElem_eval_fields env input.cc 0 (by decide)).symm
  have hc1 :=
    (ProvableType.getElem_eval_fields env input.cc 1 (by decide)).symm
  have hc2 :=
    (ProvableType.getElem_eval_fields env input.cc 2 (by decide)).symm
  have hc3 :=
    (ProvableType.getElem_eval_fields env input.cc 3 (by decide)).symm
  have hf0 :=
    (ProvableType.getElem_eval_fields env
      input.cols.u16_flags 0 (by decide)).symm
  have hf1 :=
    (ProvableType.getElem_eval_fields env
      input.cols.u16_flags 1 (by decide)).symm
  have hf2 :=
    (ProvableType.getElem_eval_fields env
      input.cols.u16_flags 2 (by decide)).symm
  have hf3 :=
    (ProvableType.getElem_eval_fields env
      input.cols.u16_flags 3 (by decide)).symm
  have hcl0 :=
    (ProvableType.getElem_eval_fields env
      input.cols.comparison_limbs 0 (by decide)).symm
  have hcl1 :=
    (ProvableType.getElem_eval_fields env
      input.cols.comparison_limbs 1 (by decide)).symm
  unfold ltUnsignedConstraintTail ltUnsignedAssertionTail
  simp only [List.map_cons, List.map_nil, List.cons.injEq]
  rw [eval_ltUnsignedColumns]
  rw [hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3,
    hf0, hf1, hf2, hf3, hcl0, hcl1]
  simp only [CircuitType.eval_expr, eval_sub,
    Expression.eval, sub_zero]
  simp

private theorem native_ltUnsignedAssertions_decompose
    (env : Environment (ZMod p))
    (input : Var SP1Clean.LtOperationUnsigned.Inputs (ZMod p))
    (offset : ℕ) :
    nativeAssertZeros env
        ((SP1Clean.LtOperationUnsigned.main input).operations offset) =
      nativeAssertZeros env
          ((SP1Clean.U16CompareOperation.main
            ⟨input.cols.comparison_limbs[0],
              input.cols.comparison_limbs[1],
              { bit := input.cols.u16_compare_operation.bit },
              input.is_real⟩).operations offset) ++
        ltUnsignedAssertionTail
          (Eval.eval env input.b) (Eval.eval env input.cc)
          (Eval.eval env input.cols)
          (Expression.eval env input.is_real) := by
  rw [nativeAssertZeros, ltUnsigned_constraints_decompose,
    List.map_append, ← nativeAssertZeros,
    ltUnsignedConstraintTail_eval]

/-- Folded normalization of the native unsigned-comparison fragment to the exact generated list. -/
theorem ltUnsigned_assertions_exact
    (env : Environment (ZMod p))
    (input : Var SP1Clean.LtOperationUnsigned.Inputs (ZMod p))
    (offset : ℕ) :
    nativeAssertZeros env
        ((SP1Clean.LtOperationUnsigned.main input).operations offset) =
      Extracted.LtOperationUnsigned.asserts
        (Eval.eval env input.b) (Eval.eval env input.cc)
        (Eval.eval env input.cols)
        (Expression.eval env input.is_real) := by
  let cmpInput : Var SP1Clean.U16CompareOperation.Inputs (ZMod p) :=
    ⟨input.cols.comparison_limbs[0],
      input.cols.comparison_limbs[1],
      { bit := input.cols.u16_compare_operation.bit },
      input.is_real⟩
  have ha : Expression.eval env cmpInput.a =
      (Eval.eval env input.cols).comparison_limbs[0] := by
    simp only [cmpInput]
    rw [eval_ltUnsignedColumns]
    exact ProvableType.getElem_eval_fields env
      input.cols.comparison_limbs 0 (by decide)
  have hb : Expression.eval env cmpInput.b =
      (Eval.eval env input.cols).comparison_limbs[1] := by
    simp only [cmpInput]
    rw [eval_ltUnsignedColumns]
    exact ProvableType.getElem_eval_fields env
      input.cols.comparison_limbs 1 (by decide)
  have hcols : Eval.eval env cmpInput.cols =
      (Eval.eval env input.cols).u16_compare_operation := by
    simp only [cmpInput, eval_u16CompareColumns]
    rw [eval_ltUnsignedColumns, eval_u16CompareColumns]
  have hreal : Expression.eval env cmpInput.is_real =
      Expression.eval env input.is_real := rfl
  rw [native_ltUnsignedAssertions_decompose,
    extracted_ltUnsignedAssertions_decompose,
    u16compare_assertions_exact]
  rw [ha, hb, hcols, hreal]

open SP1Clean.Channels (byteChannel)
open SP1Clean.InteractionRecovery

/-- **Faithfulness anchor — interaction half, SYNTACTIC (op-level COMPOSITION).** `LtOperationUnsigned`
emits its single byte interaction only through the composed `U16CompareOperation` subcircuit (its own
thirteen `=== 0` gates emit nothing). So its byte-bus image is *exactly* `U16Compare`'s, and this anchor
**composes** `u16compare_interactions_faithful_syntactic` at the threaded sub-input
`⟨comparison_limbs[0], comparison_limbs[1], ⟨u16_compare_operation.bit⟩, is_real⟩` rather than re-descending
the byte pull. The first op-level composition anchor — the template for `Addw`/`Subw`/`LtSigned` and the
chip-level composed channels. -/
theorem ltUnsigned_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var SP1Clean.LtOperationUnsigned.Inputs (ZMod p)) (offset : ℕ)
    (b cc : Word (ZMod p)) (cols : Extracted.LtOperationUnsigned (ZMod p)) (is_real : ZMod p)
    (h_ir : Expression.eval env input.is_real = is_real)
    (h_cl0 : Expression.eval env input.cols.comparison_limbs[0] = cols.comparison_limbs[0])
    (h_cl1 : Expression.eval env input.cols.comparison_limbs[1] = cols.comparison_limbs[1])
    (h_bit : Expression.eval env input.cols.u16_compare_operation.bit = cols.u16_compare_operation.bit) :
    (Extracted.LtOperationUnsigned.interactions b cc cols is_real).map
        Extracted.Interaction.toAccess
      = (((SP1Clean.LtOperationUnsigned.main input).operations offset).interactionsWith
          byteChannel.toRaw).map (AbstractInteraction.toAccess env) := by
  -- LHS: the oracle is `U16Compare.interactions cl0 cl1 ⟨bit⟩ is_real ++ []`.
  simp only [Extracted.LtOperationUnsigned.interactions, List.append_nil]
  -- RHS: descend the chip into the single `U16Compare` subcircuit; the thirteen `=== 0` gates are
  -- `Gadgets.Equality` assertions that emit no interaction (`Equality.main` → just an `assert`), so their
  -- `byteChannel` filters are `[]` and the `++` chain collapses to the `U16Compare` byte pull.
  simp only [SP1Clean.LtOperationUnsigned.main, circuit_norm,
    FormalAssertion.toSubcircuit_interactions, SP1Clean.U16CompareOperation.circuit,
    Gadgets.Equality.main, List.filter_nil, List.append_nil]
  -- both sides are the two sides of the U16Compare syntactic anchor at the threaded sub-input.
  exact u16compare_interactions_faithful_syntactic env
    ⟨input.cols.comparison_limbs[0], input.cols.comparison_limbs[1],
      input.cols.u16_compare_operation, input.is_real⟩ _
    cols.comparison_limbs[0] cols.comparison_limbs[1] is_real
    cols.u16_compare_operation h_ir h_cl0 h_cl1 h_bit

end SP1Clean.Faithful
