import SP1Clean.Math.Word

/-! # Natural order from a bounded SP1 register timestamp gap

The previous low clock and the two gap limbs are bounded. Their sum fits below the field
characteristic, so the field subtraction represents a strict natural-number increase. This
arithmetic boundary is shared by register readers and whole-machine time extraction.
-/

namespace SP1Clean.MemoryClock

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

theorem lt_of_register_gap (clk_target prev_low diff_low_limb : ZMod p)
    (prevBound : prev_low.val < 2 ^ 24)
    (diffLow : diff_low_limb.val < 2 ^ 16)
    (diffHigh : ((clk_target - prev_low - 1 - diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8) :
    prev_low.val < clk_target.val := by
  have hp := Fact.out (p := 2 ^ 25 < p)
  set high := (clk_target - prev_low - 1 - diff_low_limb) * (65536 : ZMod p)⁻¹ with highDef
  have reconstruct : clk_target = prev_low + (1 + (diff_low_limb + high * 65536)) := by
    rw [highDef, mul_assoc, inv_mul_cancel₀ val_65536_ne_zero, mul_one]
    ring
  have highMulVal : (high * 65536).val = high.val * 65536 := by
    rw [ZMod.val_mul_of_lt (by rw [val_65536_zmod_p]; omega), val_65536_zmod_p]
  have diffVal : (diff_low_limb + high * 65536).val = diff_low_limb.val + high.val * 65536 := by
    rw [ZMod.val_add_of_lt (by rw [highMulVal]; omega), highMulVal]
  have succVal : (1 + (diff_low_limb + high * 65536)).val
      = 1 + (diff_low_limb.val + high.val * 65536) := by
    rw [ZMod.val_add_of_lt (by rw [diffVal, ZMod.val_one]; omega), diffVal, ZMod.val_one]
  have targetVal : clk_target.val = prev_low.val + (1 + (diff_low_limb.val + high.val * 65536)) := by
    rw [reconstruct, ZMod.val_add_of_lt (by rw [succVal]; omega), succVal]
  omega

theorem gap_encoding (current previous : ZMod p)
    (increases : previous.val < current.val) (bound : current.val < 2 ^ 24) :
    let gap := current.val - previous.val - 1
    current - previous - 1 = ((gap % 65536 : ℕ) : ZMod p) + ((gap / 65536 : ℕ) : ZMod p) * 65536 ∧
      ((gap % 65536 : ℕ) : ZMod p).val < 2 ^ 16 ∧ ((gap / 65536 : ℕ) : ZMod p).val < 2 ^ 8 := by
  dsimp only
  let gap := current.val - previous.val - 1
  have gapBound : gap < 2 ^ 24 := by dsimp only [gap]; omega
  have low : gap % 65536 < 2 ^ 16 := Nat.mod_lt _ (by norm_num)
  have high : gap / 65536 < 2 ^ 8 := by omega
  have hp := Fact.out (p := 2 ^ 25 < p)
  refine ⟨?_, ?_, ?_⟩
  · have reconstruct : previous.val + 1 + (gap % 65536 + gap / 65536 * 65536) = current.val := by
      have := Nat.mod_add_div gap 65536
      dsimp only [gap] at *
      omega
    have cast := congrArg (fun n : ℕ => (n : ZMod p)) reconstruct
    push_cast at cast
    simp only [ZMod.natCast_zmod_val] at cast
    linear_combination -cast
  · rw [ZMod.val_natCast_of_lt (by omega : gap % 65536 < p)]
    exact low
  · rw [ZMod.val_natCast_of_lt (by omega : gap / 65536 < p)]
    exact high

end SP1Clean.MemoryClock
