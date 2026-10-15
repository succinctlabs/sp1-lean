import SP1Clean.FormalModel.Contracts.AddressOrder
import Clean.Gadgets.IsZeroField
import Clean.Gadgets.Bits

/-! # An inclusive address comparison without lookup-channel traffic

Select the highest unequal limb, or the low limb if the upper two agree, and range-check its
nonnegative difference. Input bounds rule out field wrap. All twenty auxiliary cells are produced
by Clean's standard zero-test and bit-decomposition witness programs. Fixed-table providers can
therefore compare endpoints without adding demands to the instruction ensemble's Byte ledger.
-/

namespace SP1Clean.AddressOrder

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

private theorem difference_le (lower upper : ZMod p)
    (bounded : lower.val < 2 ^ 16) (gapBound : (upper - lower).val < 2 ^ 16) :
    lower.val ≤ upper.val := by
  have hp := Fact.out (p := 2 ^ 17 < p)
  have reconstruct : upper = lower + (upper - lower) := by ring
  have values : upper.val = lower.val + (upper - lower).val := by
    conv_lhs => rw [reconstruct]
    rw [ZMod.val_add_of_lt (by omega)]
  omega

omit [Fact (2 ^ 17 < p)] in
private theorem difference_bound (lower upper : ZMod p)
    (bounded : upper.val < 2 ^ 16) (order : lower.val ≤ upper.val) :
    (upper - lower).val < 2 ^ 16 := by
  rw [ZMod.val_sub order]
  omega

def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let sameHigh ← Gadgets.IsZeroField.circuit (input.lower[2] - input.upper[2])
  let sameMiddle ← Gadgets.IsZeroField.circuit (input.lower[1] - input.upper[1])
  let gap := ((1 : Expression (ZMod p)) - sameHigh) * (input.upper[2] - input.lower[2]) +
    sameHigh * (((1 : Expression (ZMod p)) - sameMiddle) * (input.upper[1] - input.lower[1]) +
      sameMiddle * (input.upper[0] - input.lower[0]))
  assertion (Gadgets.ToBits.rangeCheck 16 (by have := Fact.out (p := 2 ^ 17 < p); omega)) gap

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main := by elaborate_circuit

theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start [Assumptions, Spec, Gadgets.IsZeroField.circuit, Gadgets.ToBits.rangeCheck]
  obtain ⟨lower, upper⟩ := h_assumptions
  obtain ⟨sameHigh, sameMiddle, gap⟩ := h_holds
  simp only [sub_eq_zero] at sameHigh sameMiddle
  rw [sameHigh, sameMiddle] at gap
  have lowerEval (index : ℕ) (bound : index < 3) :
      Expression.eval env input_var_lower[index] = input_lower[index] := by
    simpa only [Vector.getElem_map] using congrArg (fun v : fields 3 (ZMod p) => v[index]) h_input.1
  have upperEval (index : ℕ) (bound : index < 3) :
      Expression.eval env input_var_upper[index] = input_upper[index] := by
    simpa only [Vector.getElem_map] using congrArg (fun v : fields 3 (ZMod p) => v[index]) h_input.2
  simp only [lowerEval, upperEval] at gap
  have l0 : input_lower[0].val < 2 ^ 16 := lower 0
  have l1 : input_lower[1].val < 2 ^ 16 := lower 1
  have l2 : input_lower[2].val < 2 ^ 16 := lower 2
  have u0 : input_upper[0].val < 2 ^ 16 := upper 0
  have u1 : input_upper[1].val < 2 ^ 16 := upper 1
  have u2 : input_upper[2].val < 2 ^ 16 := upper 2
  dsimp only [value, Address.toNat]
  by_cases high : input_lower[2] = input_upper[2]
  · simp only [if_pos high, sub_self, zero_mul, one_mul, zero_add] at gap
    by_cases middle : input_lower[1] = input_upper[1]
    · simp only [if_pos middle, sub_self, zero_mul, one_mul, zero_add] at gap
      have order := difference_le _ _ l0 gap
      rw [high, middle]
      omega
    · simp only [if_neg middle, sub_zero, one_mul, zero_mul, add_zero] at gap
      have order := difference_le _ _ l1 gap
      have different : input_lower[1].val ≠ input_upper[1].val := fun same => middle (ZMod.val_injective p same)
      rw [high]
      omega
  · simp only [if_neg high, sub_zero, one_mul, zero_mul, add_zero] at gap
    have order := difference_le _ _ l2 gap
    have different : input_lower[2].val ≠ input_upper[2].val := fun same => high (ZMod.val_injective p same)
    omega

theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start [Assumptions, Spec, Gadgets.IsZeroField.circuit, Gadgets.ToBits.rangeCheck]
  obtain ⟨lower, upper⟩ := h_assumptions
  obtain ⟨sameHigh, sameMiddle⟩ := h_env
  simp only [sub_eq_zero] at sameHigh sameMiddle
  rw [sameHigh, sameMiddle]
  have lowerEval (index : ℕ) (bound : index < 3) :
      Expression.eval env input_var_lower[index] = input_lower[index] := by
    simpa only [Vector.getElem_map] using congrArg (fun v : fields 3 (ZMod p) => v[index]) h_input.1
  have upperEval (index : ℕ) (bound : index < 3) :
      Expression.eval env input_var_upper[index] = input_upper[index] := by
    simpa only [Vector.getElem_map] using congrArg (fun v : fields 3 (ZMod p) => v[index]) h_input.2
  simp only [lowerEval, upperEval]
  have l0 : input_lower[0].val < 2 ^ 16 := lower 0
  have l1 : input_lower[1].val < 2 ^ 16 := lower 1
  have l2 : input_lower[2].val < 2 ^ 16 := lower 2
  have u0 : input_upper[0].val < 2 ^ 16 := upper 0
  have u1 : input_upper[1].val < 2 ^ 16 := upper 1
  have u2 : input_upper[2].val < 2 ^ 16 := upper 2
  dsimp only [value, Address.toNat] at h_spec
  by_cases high : input_lower[2] = input_upper[2]
  · simp only [if_pos high, sub_self, zero_mul, one_mul, zero_add]
    by_cases middle : input_lower[1] = input_upper[1]
    · simp only [if_pos middle, sub_self, zero_mul, one_mul, zero_add]
      apply difference_bound _ _ u0
      rw [high, middle] at h_spec
      omega
    · simp only [if_neg middle, sub_zero, one_mul, zero_mul, add_zero]
      apply difference_bound _ _ u1
      rw [high] at h_spec
      omega
  · simp only [if_neg high, sub_zero, one_mul, zero_mul, add_zero]
    apply difference_bound _ _ u2
    omega

def circuit : FormalAssertion (ZMod p) Inputs where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

end SP1Clean.AddressOrder
