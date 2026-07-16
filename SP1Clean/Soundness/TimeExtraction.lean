import SP1Clean.FormalModel.Contracts.Readers
import SP1Clean.Model.Semantics.MicroTime

/-! # Extracting natural-number time from CPUState clocks

SP1 emits State-channel clocks as field elements.  The CPUState byte checks are precisely what rules
out wraparound and lets the whole-machine layer interpret its `clk + 8` edge as a strict step in `ℕ`.
This module proves that arithmetic fact once, independently of any particular instruction chip.
-/

namespace SP1Clean.Soundness.TimeExtraction

open SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- The two CPUState range checks make the field-valued low-clock increment an exact natural-number
increment.  The stronger machine-level field bound leaves enough room for the final `+ 8` after the
24-bit clock limbs have been reconstructed. -/
theorem clkNat_add_eight_of_cpuState_bounds (clkHigh clk0 clk1 : ZMod p)
    (clk0Bound : ((clk0 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13)
    (clk1Bound : clk1.val < 2 ^ 8) :
    clkNat clkHigh (clk0 + clk1 * 65536 + 8) =
      clkNat clkHigh (clk0 + clk1 * 65536) + 8 := by
  let scaled := (clk0 - 1) * (8 : ZMod p)⁻¹
  have eightNe : (8 : ZMod p) ≠ 0 := val_8_ne_zero
  have scaledBound : scaled.val < 2 ^ 13 := clk0Bound
  have reconstruct : scaled * 8 + 1 = clk0 := by
    dsimp only [scaled]
    rw [mul_assoc, inv_mul_cancel₀ eightNe, mul_one]
    ring_nf
  have scaledMulLt : scaled.val * (8 : ZMod p).val < p := by
    rw [val_8_zmod_p]
    have := Fact.out (p := 2 ^ 25 < p)
    omega
  have scaledMulVal : (scaled * 8).val = scaled.val * 8 := by
    rw [ZMod.val_mul_of_lt scaledMulLt, val_8_zmod_p]
  have clk0AddLt : (scaled * 8).val + (1 : ZMod p).val < p := by
    rw [scaledMulVal, ZMod.val_one]
    have := Fact.out (p := 2 ^ 25 < p)
    omega
  have clk0Val : clk0.val = scaled.val * 8 + 1 := by
    calc
      clk0.val = (scaled * 8 + 1).val := congrArg ZMod.val reconstruct.symm
      _ = (scaled * 8).val + (1 : ZMod p).val := ZMod.val_add_of_lt clk0AddLt
      _ = scaled.val * 8 + 1 := by rw [scaledMulVal, ZMod.val_one]
  have highLimbMulLt : clk1.val * (65536 : ZMod p).val < p := by
    rw [val_65536_zmod_p]
    have := Fact.out (p := 2 ^ 25 < p)
    omega
  have highLimbVal : (clk1 * 65536).val = clk1.val * 65536 := by
    rw [ZMod.val_mul_of_lt highLimbMulLt, val_65536_zmod_p]
  have lowAddLt : clk0.val + (clk1 * 65536).val < p := by
    rw [clk0Val, highLimbVal]
    have := Fact.out (p := 2 ^ 25 < p)
    omega
  have lowVal : (clk0 + clk1 * 65536).val = clk0.val + clk1.val * 65536 := by
    rw [ZMod.val_add_of_lt lowAddLt, highLimbVal]
  have incrementAddLt : (clk0 + clk1 * 65536).val + (8 : ZMod p).val < p := by
    rw [lowVal, clk0Val, val_8_zmod_p]
    have := Fact.out (p := 2 ^ 25 < p)
    omega
  have incrementedVal : (clk0 + clk1 * 65536 + 8).val =
      (clk0 + clk1 * 65536).val + 8 := by
    rw [ZMod.val_add_of_lt incrementAddLt, val_8_zmod_p]
  simp only [clkNat, incrementedVal]
  omega

/-- Contract-level form used by instruction-row proofs. -/
theorem clkNat_add_eight_of_cpuState_spec (input : Readers.CPUState.Inputs (ZMod p))
    (real : input.is_real = 1) (spec : Readers.CPUState.Spec input)
    (clkInc : input.clk_inc = 8) :
    clkNat input.cols.clk_high
        (input.cols.clk_0_16 + input.cols.clk_16_24 * 65536 + input.clk_inc) =
      clkNat input.cols.clk_high
        (input.cols.clk_0_16 + input.cols.clk_16_24 * 65536) + 8 := by
  rw [clkInc]
  exact clkNat_add_eight_of_cpuState_bounds _ _ _ (spec real).1 (spec real).2

end SP1Clean.Soundness.TimeExtraction
