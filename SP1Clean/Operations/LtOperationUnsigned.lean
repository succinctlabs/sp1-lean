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

/-! ## Multiplicity-gated `AssertionGated` form

Parallel to the unconditional `Assertion` namespace above. The
`AssertionGated` form threads a multiplicity expression `is_real` and
gates every emitted constraint by it (strict gating, matching the
convention used by `U16CompareOp.AssertionGated` / `AddwOp.AssertionGated`
in earlier phases). The inner `U16CompareOp` sub-call is the gated form.

The contract is literal-conjunction under `is_real = 1 →` (the gated
analogue of the unconditional `Spec` above), not a BV-collapsed semantic
form — `LtOperationUnsigned` has no `iff_sp1_full` / `spec_inv` to bridge
through. The chip composes this `Spec` directly. -/

/-- Multiplicity-aware input: same fields as `Inputs` plus the gating
multiplicity `is_real`. -/
structure InputsGated (F : Type) where
  b : fields 4 F
  c : fields 4 F
  compare_bit : F
  u16_flags : fields 4 F
  not_eq_inv : F
  comparison_limbs : fields 2 F
  is_real : F
deriving ProvableStruct

namespace AssertionGated

open Circuit

/-- Multiplicity-gated `main`: gates every emission by `is_real`. Inner
`U16CompareOp` sub-call uses `assertionGated` with `is_real` wired
through. -/
@[reducible]
def main (input : Var InputsGated (ZMod p)) : Circuit (ZMod p) Unit := do
  input.is_real * (input.is_real - 1) === 0
  -- Inner gated byte-comparison (gates its own bit-bool + lookup).
  SP1Clean.U16CompareOp.assertionGated
    (⟨input.comparison_limbs[0], input.comparison_limbs[1],
       input.compare_bit, input.is_real⟩ :
      Var SP1Clean.U16CompareOp.InputsGated (ZMod p))
  -- 4 one-hot flag booleans (gated).
  input.is_real * (input.u16_flags[0] * (input.u16_flags[0] - 1)) === 0
  input.is_real * (input.u16_flags[1] * (input.u16_flags[1] - 1)) === 0
  input.is_real * (input.u16_flags[2] * (input.u16_flags[2] - 1)) === 0
  input.is_real * (input.u16_flags[3] * (input.u16_flags[3] - 1)) === 0
  -- Sum-of-flags binary (gated).
  let sum_flags := input.u16_flags[0] + input.u16_flags[1] +
    input.u16_flags[2] + input.u16_flags[3]
  input.is_real * (sum_flags * (sum_flags - 1)) === 0
  -- Cross-limb selection ×4 (MSB→LSB cumulative), gated.
  let one_expr : Expression (ZMod p) := 1
  let cum3 := input.u16_flags[3]
  let cum2 := cum3 + input.u16_flags[2]
  let cum1 := cum2 + input.u16_flags[1]
  input.is_real * ((one_expr - cum3) * (input.b[3] - input.c[3])) === 0
  input.is_real * ((one_expr - cum2) * (input.b[2] - input.c[2])) === 0
  input.is_real * ((one_expr - cum1) * (input.b[1] - input.c[1])) === 0
  input.is_real *
    ((one_expr - (cum1 + input.u16_flags[0])) * (input.b[0] - input.c[0])) === 0
  -- comparison_limbs derivation ×2 (gated).
  let cl0_expected := input.b[3] * input.u16_flags[3] +
    input.b[2] * input.u16_flags[2] +
    input.b[1] * input.u16_flags[1] +
    input.b[0] * input.u16_flags[0]
  let cl1_expected := input.c[3] * input.u16_flags[3] +
    input.c[2] * input.u16_flags[2] +
    input.c[1] * input.u16_flags[1] +
    input.c[0] * input.u16_flags[0]
  input.is_real * (cl0_expected - input.comparison_limbs[0]) === 0
  input.is_real * (cl1_expected - input.comparison_limbs[1]) === 0
  -- not_eq_inv discipline (gated).
  input.is_real *
    ((-sum_flags) * (input.not_eq_inv *
      (input.comparison_limbs[0] - input.comparison_limbs[1]) - one_expr)) === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) InputsGated unit where
  name := "SP1Clean.LtUnsignedOpGated"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]
  subcircuitsConsistent input offset := by
    simp +arith only [main, circuit_norm]

/-- Binarity of `is_real`. The chip-side `is_real * (is_real - 1) = 0`
gate establishes this externally. -/
def Assumptions (input : InputsGated (ZMod p)) : Prop :=
  input.is_real = 0 ∨ input.is_real = 1

/-- Semantic contract: vacuous on padding rows, asserts the full
literal-conjunction form of the non-gated `Spec` on real rows. -/
def Spec (input : InputsGated (ZMod p)) : Prop :=
  input.is_real = 1 →
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
    (one - input.u16_flags[3]) * (input.b[3] - input.c[3]) = 0 ∧
    (one - (input.u16_flags[3] + input.u16_flags[2])) *
      (input.b[2] - input.c[2]) = 0 ∧
    (one - (input.u16_flags[3] + input.u16_flags[2] + input.u16_flags[1])) *
      (input.b[1] - input.c[1]) = 0 ∧
    (one - (input.u16_flags[3] + input.u16_flags[2] +
          input.u16_flags[1] + input.u16_flags[0])) *
      (input.b[0] - input.c[0]) = 0 ∧
    (input.b[3] * input.u16_flags[3] + input.b[2] * input.u16_flags[2] +
      input.b[1] * input.u16_flags[1] + input.b[0] * input.u16_flags[0]) -
        input.comparison_limbs[0] = 0 ∧
    (input.c[3] * input.u16_flags[3] + input.c[2] * input.u16_flags[2] +
      input.c[1] * input.u16_flags[1] + input.c[0] * input.u16_flags[0]) -
        input.comparison_limbs[1] = 0 ∧
    (let sum_flags := input.u16_flags[0] + input.u16_flags[1] +
       input.u16_flags[2] + input.u16_flags[3]
     (-sum_flags) * (input.not_eq_inv *
       (input.comparison_limbs[0] - input.comparison_limbs[1]) - one) = 0)

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start [AssertionGated.main]
  obtain ⟨h_b_eq, h_c_eq, h_bit_eq, h_f_eq, h_nei_eq, h_cl_eq, h_ir_eq⟩ := h_input
  subst h_b_eq; subst h_c_eq; subst h_bit_eq; subst h_f_eq; subst h_nei_eq
  subst h_cl_eq; subst h_ir_eq
  obtain ⟨h_ir_bin, h_u16_sub, h_f0, h_f1, h_f2, h_f3, h_s, h_x3, h_x2, h_x1,
          h_x0, h_cl0, h_cl1, h_nei⟩ := h_holds
  intro h_is_real
  unfold id at *
  have h_ir_ne_zero : Expression.eval env input_var_is_real ≠ 0 := by
    rw [h_is_real]; exact one_ne_zero
  -- Inner U16CompareOp.assertionGated under is_real = 1 yields its Spec.
  have h_u16_assumps :
      Expression.eval env input_var_is_real = 0 ∨
      Expression.eval env input_var_is_real = 1 := Or.inr h_is_real
  have ⟨h_bit_bool, h_range_val⟩ := (h_u16_sub h_u16_assumps) h_is_real
  simp only [Spec, Vector.getElem_map]
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- U16CompareOp.Assertion.Spec field 1 — bit boolean.
    exact h_bit_bool
  · -- U16CompareOp.Assertion.Spec field 2 — range.
    exact h_range_val
  · -- 4 flag-bool gates: extract via mul_eq_zero.mp + resolve_left.
    linear_combination (mul_eq_zero.mp h_f0).resolve_left h_ir_ne_zero
  · linear_combination (mul_eq_zero.mp h_f1).resolve_left h_ir_ne_zero
  · linear_combination (mul_eq_zero.mp h_f2).resolve_left h_ir_ne_zero
  · linear_combination (mul_eq_zero.mp h_f3).resolve_left h_ir_ne_zero
  · -- sum-of-flags binary.
    linear_combination (mul_eq_zero.mp h_s).resolve_left h_ir_ne_zero
  · -- 4 cross-limb gates.
    linear_combination (mul_eq_zero.mp h_x3).resolve_left h_ir_ne_zero
  · linear_combination (mul_eq_zero.mp h_x2).resolve_left h_ir_ne_zero
  · linear_combination (mul_eq_zero.mp h_x1).resolve_left h_ir_ne_zero
  · linear_combination (mul_eq_zero.mp h_x0).resolve_left h_ir_ne_zero
  · -- 2 cl-derivation gates.
    linear_combination (mul_eq_zero.mp h_cl0).resolve_left h_ir_ne_zero
  · linear_combination (mul_eq_zero.mp h_cl1).resolve_left h_ir_ne_zero
  · -- not_eq_inv discipline.
    linear_combination (mul_eq_zero.mp h_nei).resolve_left h_ir_ne_zero

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start [AssertionGated.main]
  obtain ⟨h_b_eq, h_c_eq, h_bit_eq, h_f_eq, h_nei_eq, h_cl_eq, h_ir_eq⟩ := h_input
  subst h_b_eq; subst h_c_eq; subst h_bit_eq; subst h_f_eq; subst h_nei_eq
  subst h_cl_eq; subst h_ir_eq
  unfold id at *
  rcases h_assumptions with h_ir0 | h_ir1
  · -- Padding row: is_real = 0; all gated emissions trivialize.
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h_ir0]; ring
    · -- Inner U16CompareOp.assertionGated: ⟨SubAssumptions, SubSpec⟩.
      refine ⟨Or.inl h_ir0, fun h_contra => ?_⟩
      exact absurd (h_ir0.symm.trans h_contra) zero_ne_one
    all_goals rw [h_ir0]; ring
  · -- Real row: recover all 13 facts from Spec.
    simp only [Spec, Vector.getElem_map] at h_spec
    obtain ⟨⟨h_bit_bool, h_range_val⟩, h_f0, h_f1, h_f2, h_f3, h_s, h_x3, h_x2,
            h_x1, h_x0, h_cl0, h_cl1, h_nei⟩ := h_spec h_ir1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h_ir1]; ring
    · -- Inner U16CompareOp.assertionGated: ⟨SubAssumptions, SubSpec⟩.
      refine ⟨Or.inr h_ir1, fun _ => ⟨?_, ?_⟩⟩
      · exact h_bit_bool
      · exact h_range_val
    · rw [h_ir1]; linear_combination h_f0
    · rw [h_ir1]; linear_combination h_f1
    · rw [h_ir1]; linear_combination h_f2
    · rw [h_ir1]; linear_combination h_f3
    · rw [h_ir1]; linear_combination h_s
    · rw [h_ir1]; linear_combination h_x3
    · rw [h_ir1]; linear_combination h_x2
    · rw [h_ir1]; linear_combination h_x1
    · rw [h_ir1]; linear_combination h_x0
    · rw [h_ir1]; linear_combination h_cl0
    · rw [h_ir1]; linear_combination h_cl1
    · rw [h_ir1]; linear_combination h_nei

end AssertionGated

/-- Multiplicity-gated FormalAssertion for `LtOperationUnsigned`. Compose
via `LtUnsignedOp.assertionGated input` in `Chips/.../Multiplicity/`
mirrors. -/
def assertionGated : FormalAssertion (ZMod p) InputsGated :=
  { AssertionGated.elaborated with
    Assumptions := AssertionGated.Assumptions,
    Spec := AssertionGated.Spec,
    soundness := AssertionGated.soundness,
    completeness := AssertionGated.completeness }

end SP1Clean.LtUnsignedOp
