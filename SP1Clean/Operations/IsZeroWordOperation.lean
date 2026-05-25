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
import SP1Operations.Compare.IsZeroWordOperation.IsZeroWordOperation

/-! # `IsZeroWordOperation` Clean mirror (scaffold)

SP1's `IsZeroWordOperation` checks whether a 4-limb `Word F` is zero.
Rust source: `SP1Operations/Compare/IsZeroWordOperation/Constraints.lean`.
Composes 4 `IsZeroOperation.constraints` calls (one per limb) + 5
trailing `assertZero` gates that aggregate the per-limb zero witnesses
into `is_zero_first_half`, `is_zero_second_half`, and the final
`result`.

For each limb the IsZero check inlines as 3 gates (under is_real = 1):
```
is_real * (1 - inverse*a - result) = 0   -- result = 1 - inverse*a
is_real * (result * (result - 1)) = 0    -- result is boolean
is_real * (result * a) = 0               -- result = 1 → a = 0
```

This wrapper composes the per-limb sub-gates inline (the 3-gate IsZero
pattern doesn't have its own `FormalAssertion` wrapper yet — its Clean
analog `SP1Clean.IsZeroOp.circuit` is a witness-form `FormalCircuit`).
Proof bodies `sorry`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.IsZeroWordOp

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Bundled FormalAssertion input. Mirrors Rust `IsZeroWordOperation<T>`:
the input word, the 4 per-limb (inverse, result) IsZero-witness pairs,
the two half-fold witnesses, and the final aggregate result. -/
structure Inputs (F : Type) where
  a : fields 4 F
  is_zero_limb_inverse : fields 4 F
  is_zero_limb_result : fields 4 F
  is_zero_first_half : F
  is_zero_second_half : F
  result : F
deriving ProvableStruct

/-- Clean-side circuit. Inlines the 4-per-limb `IsZeroOperation` gate
pattern (3 gates × 4 limbs = 12 gates) plus the 5 aggregation gates
under `is_real = 1`. Matches `IsZeroWordOperation.constraints` from SP1
exactly. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  -- 4 per-limb IsZero sub-gates (3 each):
  -- limb 0
  let one_expr : Expression (ZMod p) := 1
  (one_expr - input.is_zero_limb_inverse[0] * input.a[0]
    - input.is_zero_limb_result[0]) === 0
  input.is_zero_limb_result[0] * (input.is_zero_limb_result[0] - 1) === 0
  input.is_zero_limb_result[0] * input.a[0] === 0
  -- limb 1
  (one_expr - input.is_zero_limb_inverse[1] * input.a[1]
    - input.is_zero_limb_result[1]) === 0
  input.is_zero_limb_result[1] * (input.is_zero_limb_result[1] - 1) === 0
  input.is_zero_limb_result[1] * input.a[1] === 0
  -- limb 2
  (one_expr - input.is_zero_limb_inverse[2] * input.a[2]
    - input.is_zero_limb_result[2]) === 0
  input.is_zero_limb_result[2] * (input.is_zero_limb_result[2] - 1) === 0
  input.is_zero_limb_result[2] * input.a[2] === 0
  -- limb 3
  (one_expr - input.is_zero_limb_inverse[3] * input.a[3]
    - input.is_zero_limb_result[3]) === 0
  input.is_zero_limb_result[3] * (input.is_zero_limb_result[3] - 1) === 0
  input.is_zero_limb_result[3] * input.a[3] === 0
  -- Aggregate: result is boolean.
  input.result * (input.result - 1) === 0
  -- first_half = limb_result[0] * limb_result[1].
  (input.is_zero_first_half -
    input.is_zero_limb_result[0] * input.is_zero_limb_result[1]) === 0
  -- second_half = limb_result[2] * limb_result[3].
  (input.is_zero_second_half -
    input.is_zero_limb_result[2] * input.is_zero_limb_result[3]) === 0
  -- result = first_half * second_half.
  (input.result -
    input.is_zero_first_half * input.is_zero_second_half) === 0

set_option maxHeartbeats 800000 in
-- 18 inline gates; default `localLength_eq` tactic exceeds budget.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.IsZeroWordOp"
  main := main
  localLength _ := 0

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- Spec: the **joint witness contract** — captures all SP1 IsZeroWord
constraint facts under `is_real = 1` in one structured tuple. The
top-level `result` indicator (`= 1 iff a is zero` componentwise) is
implied by this contract but isn't explicit — derived via
`IsZeroWordOperation.spec` when consumers need it. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  -- Per-limb IsZero contract (3 facts × 4 limbs = 12), normalized to
  -- `+ -` form (matching `sub_eq_add_neg` normalization in circuit_norm).
  ((1 : ZMod p) - input.is_zero_limb_inverse[0] * input.a[0]
    - input.is_zero_limb_result[0] = 0) ∧
  (input.is_zero_limb_result[0] *
    (input.is_zero_limb_result[0] - 1) = (0 : ZMod p)) ∧
  (input.is_zero_limb_result[0] * input.a[0] = (0 : ZMod p)) ∧
  ((1 : ZMod p) - input.is_zero_limb_inverse[1] * input.a[1]
    - input.is_zero_limb_result[1] = 0) ∧
  (input.is_zero_limb_result[1] *
    (input.is_zero_limb_result[1] - 1) = (0 : ZMod p)) ∧
  (input.is_zero_limb_result[1] * input.a[1] = (0 : ZMod p)) ∧
  ((1 : ZMod p) - input.is_zero_limb_inverse[2] * input.a[2]
    - input.is_zero_limb_result[2] = 0) ∧
  (input.is_zero_limb_result[2] *
    (input.is_zero_limb_result[2] - 1) = (0 : ZMod p)) ∧
  (input.is_zero_limb_result[2] * input.a[2] = (0 : ZMod p)) ∧
  ((1 : ZMod p) - input.is_zero_limb_inverse[3] * input.a[3]
    - input.is_zero_limb_result[3] = 0) ∧
  (input.is_zero_limb_result[3] *
    (input.is_zero_limb_result[3] - 1) = (0 : ZMod p)) ∧
  (input.is_zero_limb_result[3] * input.a[3] = (0 : ZMod p)) ∧
  -- Aggregate facts (4).
  (input.result * (input.result - 1) = (0 : ZMod p)) ∧
  (input.is_zero_first_half - input.is_zero_limb_result[0] *
    input.is_zero_limb_result[1] = (0 : ZMod p)) ∧
  (input.is_zero_second_half - input.is_zero_limb_result[2] *
    input.is_zero_limb_result[3] = (0 : ZMod p)) ∧
  (input.result - input.is_zero_first_half * input.is_zero_second_half
    = (0 : ZMod p))

omit [Fact (2 ^ 17 < p)] in
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_a, h_inv, h_res, h_fh, h_sh, h_r⟩ := h_input
  subst_eqs
  simp only [Spec, Vector.getElem_map, sub_eq_add_neg]
  exact h_holds

omit [Fact (2 ^ 17 < p)] in
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_a, h_inv, h_res, h_fh, h_sh, h_r⟩ := h_input
  subst_eqs
  simp only [Spec, Vector.getElem_map, sub_eq_add_neg] at h_spec
  exact h_spec

/-- The full Clean `FormalAssertion` for `IsZeroWordOperation`. -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { elaborated with
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

omit [Fact (2 ^ 17 < p)] in
/-- Bridge to SP1: under `is_real = 1`, `Spec input` is equivalent to
SP1's `IsZeroWordOperation.constraints` `allHold`. Each of the 12 per-limb
IsZeroOp gates and 4 aggregate gates corresponds 1:1 to a Spec conjunct;
the chip-level `is_real * (is_real - 1) = 0` gate is trivially `1 * 0 = 0`
and dropped via `one_mul` simplification. -/
lemma iff_sp1 (input : Inputs (ZMod p)) :
    Spec input ↔
      (IsZeroWordOperation.constraints input.a
        { is_zero_limb := #v[
            ⟨input.is_zero_limb_inverse[0], input.is_zero_limb_result[0]⟩,
            ⟨input.is_zero_limb_inverse[1], input.is_zero_limb_result[1]⟩,
            ⟨input.is_zero_limb_inverse[2], input.is_zero_limb_result[2]⟩,
            ⟨input.is_zero_limb_inverse[3], input.is_zero_limb_result[3]⟩],
          is_zero_first_half := input.is_zero_first_half,
          is_zero_second_half := input.is_zero_second_half,
          result := input.result } 1).allHold := by
  simp only [IsZeroWordOperation.constraints, IsZeroOperation.constraints,
             SP1ConstraintList.allHold, List.Forall, SP1Constraint.toProp,
             SP1Constraint.toProp_assertZero,
             Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
             List.getElem_cons_succ, Spec, List.append_assoc, List.append_nil,
             one_mul]
  -- LHS form: 16-tuple. RHS form: 17-tuple (extra `1 * (1 - 1) = 0` chip-binary).
  constructor
  · rintro ⟨c0_a, c0_b, c0_c, c1_a, c1_b, c1_c, c2_a, c2_b, c2_c,
            c3_a, c3_b, c3_c, c4, c5, c6, c7⟩
    exact ⟨c0_a, c0_b, c0_c, c1_a, c1_b, c1_c, c2_a, c2_b, c2_c, c3_a, c3_b,
           c3_c, by rw [SP1Constraint.toProp_assertZero]; ring, c4, c5, c6, c7⟩
  · rintro ⟨c0_a, c0_b, c0_c, c1_a, c1_b, c1_c, c2_a, c2_b, c2_c,
            c3_a, c3_b, c3_c, _h_ir, c4, c5, c6, c7⟩
    exact ⟨c0_a, c0_b, c0_c, c1_a, c1_b, c1_c, c2_a, c2_b, c2_c, c3_a, c3_b,
           c3_c, c4, c5, c6, c7⟩

end SP1Clean.IsZeroWordOp
