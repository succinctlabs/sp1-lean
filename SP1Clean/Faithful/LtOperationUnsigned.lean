import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Operations.LtOperationUnsigned.RawSpec
import SP1Clean.Operations.LtOperationUnsigned.Extracted
import SP1Clean.Foundations.SP1Constraint
import SP1Clean.Foundations.InteractionProjection
import SP1Clean.Foundations.InteractionRecovery
import SP1Clean.Faithful.ExtractedInteractionModel
import SP1Clean.Faithful.U16CompareOperation
import SP1Clean.Extracted.LtOperationUnsigned

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

/-- `(16 : ZMod p).val = 16` under `Fact (2^17 < p)`. -/
private lemma val_16 [NeZero p] : (16 : ZMod p).val = 16 := by
  have : (131072 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  exact ZMod.val_natCast_of_lt (show (16 : ℕ) < p by omega)

omit [Fact (2 ^ 17 < p)] in
/-- Carry-bool bridge: `x*(x-1)=0 ↔ x∈{0,1}` (field; `→` via `bool_of_mul_pred`). -/
private lemma bool_iff {x : ZMod p} : x * (x - 1) = 0 ↔ (x = 0 ∨ x = 1) := by
  rw [sub_eq_add_neg]
  exact ⟨SP1Clean.bool_of_mul_pred,
    fun h => by rcases h with h | h <;> rw [h] <;> ring⟩

set_option maxHeartbeats 4000000 in
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
    Interaction.toProp_send_byte, ByteOpcode.ofNat_six,
    ByteOpcode.constrain_Range, val_16, one_ne_zero, ne_eq, not_false_eq_true, true_implies,
    SP1Clean.LtOperationUnsigned.RawSpec, SP1Clean.U16CompareOperation.RawSpec,
    Nat.cast_zero, Nat.cast_one,
    zero_add, sub_self, mul_zero, true_and, and_assoc, bool_iff,
    show (2 : ℕ) ^ 16 = 65536 from by norm_num]
  itauto

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
