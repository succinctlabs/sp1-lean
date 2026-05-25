import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations.Constraint
import SP1Foundations.ByteOpcode
import SP1Foundations.Field
import SP1Operations.Compare.LtOperationUnsigned.LtOperationUnsigned
import SP1Clean.Operations.U16CompareOperation

/-! # `LtOperationUnsigned` Clean mirror (scaffold)

SP1's `LtOperationUnsigned` performs a 4-limb unsigned `<` comparison
on two `Word F` values by:
- Witnessing 4 one-hot `u16_flags : Word F` — the first non-equal limb's
  index from MSB→LSB (or all-zero if equal).
- Witnessing two `comparison_limbs : Vector F 2` — the selected (b, c)
  byte pair to feed into `U16CompareOperation`.
- Witnessing `not_eq_inv : F` — the multiplicative inverse of
  `(comparison_limbs[0] - comparison_limbs[1])` (gates the all-equal
  case).
- Composing one `U16CompareOperation.constraints` call on the selected
  byte pair, plus 13 `assertZero` gates wiring the flags + comparison
  limb selection + `not_eq_inv` discipline.

Rust nesting: `LtOperationUnsigned::eval` calls `U16CompareOperation::eval`
on `comparison_limbs[0..1]` and emits the surrounding flag arithmetic.
The Clean mirror does the same — `Assertion.main` composes
`U16CompareOp.assertion` and emits the 13 surrounding gates. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.LtUnsignedOp

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Bundled FormalAssertion input: the two compared words, the cols-struct
fields (compare-op witness, 4 u16-flags, not-eq-inverse, selected 2-limb
comparison pair). Mirrors Rust `LtOperationUnsigned<T>` cols. -/
structure Inputs (F : Type) where
  b : fields 4 F
  c : fields 4 F
  compare_bit : F
  u16_flags : fields 4 F
  not_eq_inv : F
  comparison_limbs : fields 2 F
deriving ProvableStruct

/-- Clean-side circuit. Composes `U16CompareOp.assertion` on the selected
2-limb pair and emits the 13 surrounding `assertZero` gates that wire the
flag one-hot, the cross-limb selection arithmetic, and the not-eq-inv
discipline. Mirrors `LtOperationUnsigned.constraints` from SP1 verbatim
under `is_real = 1`. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  -- Sub-circuit: byte-comparison of the selected limb pair.
  SP1Clean.U16CompareOp.assertion
    (⟨input.comparison_limbs[0], input.comparison_limbs[1], input.compare_bit⟩ :
      Var SP1Clean.U16CompareOp.Inputs (ZMod p))
  -- 4 one-hot flag booleans.
  input.u16_flags[0] * (input.u16_flags[0] - 1) === 0
  input.u16_flags[1] * (input.u16_flags[1] - 1) === 0
  input.u16_flags[2] * (input.u16_flags[2] - 1) === 0
  input.u16_flags[3] * (input.u16_flags[3] - 1) === 0
  -- Sum-of-flags is boolean (0 or 1 — at most one limb differs).
  let sum_flags := input.u16_flags[0] + input.u16_flags[1] +
    input.u16_flags[2] + input.u16_flags[3]
  sum_flags * (sum_flags - 1) === 0
  -- Cross-limb selection: for each limb index i (MSB→LSB), if no higher
  -- flag fired yet AND this flag didn't fire, then b[i] = c[i]. This is
  -- encoded as `(is_real - cumulative_flags) * (b[i] - c[i]) === 0`.
  let one_expr : Expression (ZMod p) := 1
  let cum3 := input.u16_flags[3]
  let cum2 := cum3 + input.u16_flags[2]
  let cum1 := cum2 + input.u16_flags[1]
  (one_expr - cum3) * (input.b[3] - input.c[3]) === 0
  (one_expr - cum2) * (input.b[2] - input.c[2]) === 0
  (one_expr - cum1) * (input.b[1] - input.c[1]) === 0
  (one_expr - (cum1 + input.u16_flags[0])) * (input.b[0] - input.c[0]) === 0
  -- comparison_limbs[0,1] = Σ flag[i] * b[i], Σ flag[i] * c[i].
  let cl0_expected := input.b[3] * input.u16_flags[3] +
    input.b[2] * input.u16_flags[2] +
    input.b[1] * input.u16_flags[1] +
    input.b[0] * input.u16_flags[0]
  let cl1_expected := input.c[3] * input.u16_flags[3] +
    input.c[2] * input.u16_flags[2] +
    input.c[1] * input.u16_flags[1] +
    input.c[0] * input.u16_flags[0]
  cl0_expected - input.comparison_limbs[0] === 0
  cl1_expected - input.comparison_limbs[1] === 0
  -- not_eq_inv discipline: if all-equal then `not_eq_inv = 0`, else
  -- `not_eq_inv * (cl0 - cl1) = is_real`. Equivalently:
  -- `(1 - sum_flags - 1) * (not_eq_inv * (cl0 - cl1) - 1) === 0`.
  let one_expr : Expression (ZMod p) := 1
  (-sum_flags) * (input.not_eq_inv *
    (input.comparison_limbs[0] - input.comparison_limbs[1]) - one_expr) === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.LtUnsignedOp"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- Spec: structural mirror of `LtOperationUnsigned.constraints.allHold`
under `is_real = 1`, in the `_ = 0` form that matches `main`'s emitted
gates. Carries `U16CompareOp.Spec` (the inner byte-comparison) + 4 flag
booleans + sum-of-flags binary + 4 cross-limb selection gates + 2
`comparison_limbs` derivation identities + the `not_eq_inv` discipline. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  let one : ZMod p := 1
  SP1Clean.U16CompareOp.Assertion.Spec
    ⟨input.comparison_limbs[0], input.comparison_limbs[1], input.compare_bit⟩ ∧
  input.u16_flags[0] * (input.u16_flags[0] - one) = 0 ∧
  input.u16_flags[1] * (input.u16_flags[1] - one) = 0 ∧
  input.u16_flags[2] * (input.u16_flags[2] - one) = 0 ∧
  input.u16_flags[3] * (input.u16_flags[3] - one) = 0 ∧
  (let sum_flags := input.u16_flags[0] + input.u16_flags[1] +
     input.u16_flags[2] + input.u16_flags[3]
   sum_flags * (sum_flags - one) = 0) ∧
  -- 4 cross-limb selection gates (MSB→LSB cumulative). `one : ZMod p` is
  -- bound above to fix the leading-`1` elaboration ambiguity that would
  -- otherwise let Lean infer `(1 : ℕ) - <coerced field value>`.
  (one - input.u16_flags[3]) * (input.b[3] - input.c[3]) = 0 ∧
  (one - (input.u16_flags[3] + input.u16_flags[2])) *
    (input.b[2] - input.c[2]) = 0 ∧
  (one - (input.u16_flags[3] + input.u16_flags[2] + input.u16_flags[1])) *
    (input.b[1] - input.c[1]) = 0 ∧
  (one - (input.u16_flags[3] + input.u16_flags[2] +
        input.u16_flags[1] + input.u16_flags[0])) *
    (input.b[0] - input.c[0]) = 0 ∧
  -- 2 `comparison_limbs` derivation identities.
  (input.b[3] * input.u16_flags[3] + input.b[2] * input.u16_flags[2] +
    input.b[1] * input.u16_flags[1] + input.b[0] * input.u16_flags[0]) -
      input.comparison_limbs[0] = 0 ∧
  (input.c[3] * input.u16_flags[3] + input.c[2] * input.u16_flags[2] +
    input.c[1] * input.u16_flags[1] + input.c[0] * input.u16_flags[0]) -
      input.comparison_limbs[1] = 0 ∧
  -- `not_eq_inv` discipline.
  (let sum_flags := input.u16_flags[0] + input.u16_flags[1] +
     input.u16_flags[2] + input.u16_flags[3]
   (-sum_flags) * (input.not_eq_inv *
     (input.comparison_limbs[0] - input.comparison_limbs[1]) - one) = 0)

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_b_eq, h_c_eq, h_bit_eq, h_f_eq, h_nei_eq, h_cl_eq⟩ := h_input
  subst h_b_eq
  subst h_c_eq
  subst h_bit_eq
  subst h_f_eq
  subst h_nei_eq
  subst h_cl_eq
  obtain ⟨h_u16_sub, h_f0, h_f1, h_f2, h_f3, h_s, h_x3, h_x2, h_x1, h_x0,
          h_cl0, h_cl1, h_nei⟩ := h_holds
  -- U16CompareOp subcircuit hands back its Spec under trivial assumption.
  have h_u16 := h_u16_sub trivial
  unfold id at *
  simp only [Spec, Vector.getElem_map]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- U16CompareOp.Spec form bridge.
    exact h_u16
  · linear_combination h_f0
  · linear_combination h_f1
  · linear_combination h_f2
  · linear_combination h_f3
  · linear_combination h_s
  · linear_combination h_x3
  · linear_combination h_x2
  · linear_combination h_x1
  · linear_combination h_x0
  · linear_combination h_cl0
  · linear_combination h_cl1
  · linear_combination h_nei

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_b_eq, h_c_eq, h_bit_eq, h_f_eq, h_nei_eq, h_cl_eq⟩ := h_input
  subst h_b_eq
  subst h_c_eq
  subst h_bit_eq
  subst h_f_eq
  subst h_nei_eq
  subst h_cl_eq
  simp only [Spec, Vector.getElem_map] at h_spec
  obtain ⟨h_u16, h_f0, h_f1, h_f2, h_f3, h_s, h_x3, h_x2, h_x1, h_x0,
          h_cl0, h_cl1, h_nei⟩ := h_spec
  unfold id at *
  refine ⟨⟨trivial, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_u16
  · linear_combination h_f0
  · linear_combination h_f1
  · linear_combination h_f2
  · linear_combination h_f3
  · linear_combination h_s
  · linear_combination h_x3
  · linear_combination h_x2
  · linear_combination h_x1
  · linear_combination h_x0
  · linear_combination h_cl0
  · linear_combination h_cl1
  · linear_combination h_nei

/-- The full Clean `FormalAssertion` for `LtOperationUnsigned`. -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { elaborated with
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

/-- Bridge to SP1: `Spec input` is equivalent to SP1's
`LtOperationUnsigned.constraints` `allHold` form under `is_real = 1`.
Unfolds both `LtOperationUnsigned.constraints` and the embedded
`U16CompareOperation.constraints` simultaneously, flattens via
`List.forall_append` + `List.Forall`, then bridges the byte-send
conjunct via `U16CompareOp.iff_sp1`'s recipe. -/
theorem iff_sp1 (input : Inputs (ZMod p)) :
    Spec input ↔
      (LtOperationUnsigned.constraints input.b input.c
        { u16_compare_operation := { bit := input.compare_bit },
          u16_flags := input.u16_flags,
          not_eq_inv := input.not_eq_inv,
          comparison_limbs := input.comparison_limbs } 1).allHold := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  have h16_val : (16 : ZMod p).val = 16 := by
    rw [show (16 : ZMod p) = ((16 : ℕ) : ZMod p) from by push_cast; rfl,
        ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  simp only [LtOperationUnsigned.constraints, U16CompareOperation.constraints,
             SP1ConstraintList.allHold, List.forall_append, List.Forall,
             SP1Constraint.toProp, SP1Constraint.toProp_send_byte, Spec,
             SP1Clean.U16CompareOp.Assertion.Spec,
             one_ne_zero, not_false_eq_true, true_imp_iff,
             ByteOpcode.ofNat_seven, ByteOpcode.constrain_Range, h16_val,
             show (2 ^ 16 : ℕ) = 65536 from rfl, and_assoc]
  -- After simp:
  -- LHS (Spec):    bit_bin ∧ range ∧ 4 flag_bin ∧ sum_bin ∧ 4 cross ∧ 2 cl ∧ nei
  -- RHS (SP1):     E1 (= 1*0 ; trivial) ∧ bit_bin ∧ range ∧ E1' (trivial)
  --                ∧ 4 flag_bin ∧ sum_bin ∧ 4 cross ∧ 2 cl ∧ nei
  -- The 2 trivial `1 * (1 - 1) = 0` E1 conjuncts drop; the rest match.
  constructor
  · rintro ⟨h_bit_bin, h_range, h_f0, h_f1, h_f2, h_f3, h_s, h_x3, h_x2, h_x1,
            h_x0, h_cl0, h_cl1, h_nei⟩
    refine ⟨by ring, h_bit_bin, fun _ => h_range, by ring, h_f0, h_f1, h_f2, h_f3,
            h_s, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    -- Cross-limb / cl-derivation / nei conjuncts: SP1 form has `0 +` prefix
    -- from accumulator-style intermediate `let E16 := 0 + ...` etc.
    · linear_combination h_x3
    · linear_combination h_x2
    · linear_combination h_x1
    · linear_combination h_x0
    · linear_combination h_cl0
    · linear_combination h_cl1
    · linear_combination h_nei
  · rintro ⟨_h_E1, h_bit_bin, h_range, _h_E1', h_f0, h_f1, h_f2, h_f3, h_s,
            h_x3, h_x2, h_x1, h_x0, h_cl0, h_cl1, h_nei⟩
    refine ⟨h_bit_bin, h_range one_ne_zero, h_f0, h_f1, h_f2, h_f3, h_s,
            ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · linear_combination h_x3
    · linear_combination h_x2
    · linear_combination h_x1
    · linear_combination h_x0
    · linear_combination h_cl0
    · linear_combination h_cl1
    · linear_combination h_nei

end SP1Clean.LtUnsignedOp
