import SP1Clean.FormalModel.Contracts.ClockOrder
import Clean.Gadgets.IsZeroField
import Clean.Gadgets.Bits

/-! # A bounded native clock comparison

The circuit checks both clock limbs and compares the low limbs exactly when the high limbs
agree. Otherwise it compares the high limbs. The bounded subtraction cannot wrap in the field.
All selectors and bit witnesses are computed by the composed Clean gadgets.
-/

namespace SP1Clean.ClockOrder

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

private theorem subtraction_lt (current previous : ZMod p)
    (previousBound : previous.val < 2 ^ 24)
    (gapBound : (current - previous - 1).val < 2 ^ 24) : previous.val < current.val := by
  have hp := Fact.out (p := 2 ^ 25 < p)
  have reconstruct : current = previous + (1 + (current - previous - 1)) := by ring
  have gapVal : (1 + (current - previous - 1)).val = 1 + (current - previous - 1).val := by
    rw [ZMod.val_add_of_lt (by rw [ZMod.val_one]; omega), ZMod.val_one]
  have currentVal : current.val = previous.val + (1 + (current - previous - 1).val) := by
    conv_lhs => rw [reconstruct]
    rw [ZMod.val_add_of_lt (by rw [gapVal]; omega), gapVal]
  omega

private theorem subtraction_bound (current previous : ZMod p)
    (bound : current.val < 2 ^ 24) (increases : previous.val < current.val) :
    (current - previous - 1).val < 2 ^ 24 := by
  have hp := Fact.out (p := 2 ^ 25 < p)
  have gapBound : current.val - previous.val - 1 < 2 ^ 24 := by omega
  have reconstruct : previous.val + 1 + (current.val - previous.val - 1) = current.val := by omega
  have cast := congrArg (fun n : ℕ => (n : ZMod p)) reconstruct
  push_cast at cast
  simp only [ZMod.natCast_zmod_val] at cast
  have gap : current - previous - 1 = ((current.val - previous.val - 1 : ℕ) : ZMod p) := by
    linear_combination -cast
  rw [gap, ZMod.val_natCast_of_lt (by omega)]
  exact gapBound

def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertion (Gadgets.ToBits.rangeCheck 24 (by have := Fact.out (p := 2 ^ 25 < p); omega)) input.previousHigh
  assertion (Gadgets.ToBits.rangeCheck 24 (by have := Fact.out (p := 2 ^ 25 < p); omega)) input.previousLow
  assertion (Gadgets.ToBits.rangeCheck 24 (by have := Fact.out (p := 2 ^ 25 < p); omega)) input.currentHigh
  assertion (Gadgets.ToBits.rangeCheck 24 (by have := Fact.out (p := 2 ^ 25 < p); omega)) input.currentLow
  let same ← Gadgets.IsZeroField.circuit (input.previousHigh - input.currentHigh)
  let gap := same * (input.currentLow - input.previousLow) +
    (1 - same) * (input.currentHigh - input.previousHigh) - 1
  assertion (Gadgets.ToBits.rangeCheck 24 (by have := Fact.out (p := 2 ^ 25 < p); omega)) gap

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main := by elaborate_circuit

theorem soundness : GeneralFormalCircuit.Soundness (Output := unit) (ZMod p) main
    (fun _ _ => True) (fun input _ _ => Spec input) := by
  circuit_proof_start [Gadgets.ToBits.rangeCheck, Gadgets.IsZeroField.circuit]
  obtain ⟨previousHigh, previousLow, currentHigh, currentLow, same, gap⟩ := h_holds
  refine ⟨previousHigh, previousLow, currentHigh, currentLow, ?_⟩
  simp only [sub_eq_zero] at same
  rw [same] at gap
  by_cases equal : input_previousHigh = input_currentHigh
  · simp only [equal, if_true, one_mul, sub_self, zero_mul, add_zero] at gap
    have order := subtraction_lt _ _ previousLow gap
    simp only [Semantics.clkNat, equal]
    omega
  · simp only [if_neg equal, zero_mul, sub_zero, one_mul, zero_add] at gap
    have order := subtraction_lt _ _ previousHigh gap
    simp only [Semantics.clkNat]
    omega

theorem completeness : GeneralFormalCircuit.Completeness (Output := unit) (ZMod p) main
    (fun input _ _ => Spec input) (fun _ _ _ => True) := by
  circuit_proof_start [Gadgets.ToBits.rangeCheck, Gadgets.IsZeroField.circuit, Spec]
  obtain ⟨previousHigh, previousLow, currentHigh, currentLow, order⟩ := h_assumptions
  have same := h_env
  simp only [sub_eq_zero] at same
  refine ⟨previousHigh, previousLow, currentHigh, currentLow, ?_⟩
  rw [same]
  simp only [Semantics.clkNat] at order
  by_cases equal : input_previousHigh = input_currentHigh
  · simp only [equal, if_true, one_mul, sub_self, zero_mul, add_zero]
    apply subtraction_bound _ _ currentLow
    rw [equal] at order
    omega
  · simp only [if_neg equal, zero_mul, sub_zero, one_mul, zero_add]
    have different : input_previousHigh.val ≠ input_currentHigh.val := fun h => equal (ZMod.val_injective p h)
    apply subtraction_bound _ _ currentHigh
    omega

def circuit : GeneralFormalCircuit (ZMod p) Inputs unit where
  main
  elaborated
  Spec input _ _ := Spec input
  ProverAssumptions input _ _ := Spec input
  soundness
  completeness

end SP1Clean.ClockOrder
