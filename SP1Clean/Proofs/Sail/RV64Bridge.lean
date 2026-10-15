import SP1Clean.Model.SailPure
import SP1Clean.Semantics.ISA.RV64
import ToMathlib.BitVec
/-!
# Sail "M"-extension write values are the RV64 reference functions

For each `execute_MUL`/`MULW`/`DIV`/`DIVW`/`REM`/`REMW` clause, the monad-free write value of
`Model/SailPure.lean` (stated over `Int` with the model's truncations) equals the bit-vector
reference function of `Semantics/ISA/RV64.lean` (stated with `BitVec.sdiv`/`srem`/`udiv`/`umod`
and wide multiplications). Together with `SailRV64.execute_*_eq` these are the whole ISA-equivalence
chain a chip's Sail bridge needs: `execute_X = skeleton_binary … (SailRV64.x)` by `rfl`, then
`SailRV64.x = RV64.x` here.

The signed division/remainder cases are the ones with content: the model computes `Int.tdiv`/
`Int.tmod` on `toInt` and re-truncates, with the ISA's `-1` zero-divisor result and the
`MIN / -1` overflow clamp; `BitVec.sdiv`/`srem` already carry both conventions, and core's
`toInt_sdiv_of_ne_or_ne`/`toInt_srem` connect them away from the overflow corner.

This module replaces the former `riscv-lean` dependency's `SailPureToInstructions` role.
-/

open LeanRV64D.Defs

namespace SP1Clean.RV64

open Sail LeanRV64D LeanRV64D.Functions

/-! ## Division -/

theorem div_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.div rs1_val rs2_val false = div rs1_val rs2_val := by
  simp only [SailRV64.div, LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int, Nat.reduceAdd,
    LeanRV64D.Functions.not, Bool.false_eq_true, ↓reduceIte, beq_iff_eq, Int.reduceNeg,
    LeanRV64D.Functions.xlen, Int.cast_ofNat_Int, Int.reduceSub, ge_iff_le, Bool.not_false,
    Bool.true_and, decide_eq_true_eq, div]
  rw [BitVec.extractLsb'_ofInt_eq_ofInt (by omega)]
  by_cases h1 : rs1_val = 0#64
  · simp [h1, show ¬ (2 ^ (63 : Int) : Int) ≤ -1 by omega]
  · have h1' : ¬ rs1_val.toInt = 0 := BitVec.toInt_ne.mpr h1
    simp only [h1', ↓reduceIte, h1]
    apply BitVec.eq_of_toInt_eq
    by_cases hcond : rs2_val ≠ BitVec.intMin 64 ∨ rs1_val ≠ -1#64
    · rw [← BitVec.toInt_sdiv_of_ne_or_ne rs2_val rs1_val hcond]
      split
      · have := BitVec.toInt_le (x := rs2_val.sdiv rs1_val)
        omega
      · simp
    · simp only [ne_eq, not_or, Decidable.not_not] at hcond
      obtain ⟨hcond, hcond'⟩ := hcond
      simp only [hcond, BitVec.toInt_intMin, Nat.add_one_sub_one, Nat.reducePow, Nat.reduceMod,
        Int.cast_ofNat_Int, Int.reduceNeg, hcond', BitVec.reduceNeg, BitVec.reduceToInt,
        Int.tdiv_neg, Int.tdiv_one, Int.neg_neg, BitVec.toInt_ofInt]
      rw [Int.bmod_eq_of_le (by omega) (by omega)]
      rfl

theorem divu_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.div rs1_val rs2_val true = divu rs1_val rs2_val := by
  simp only [SailRV64.div, LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int, Nat.reduceAdd,
    LeanRV64D.Functions.not, Bool.not_true, ↓reduceIte, beq_iff_eq, Sail.BitVec.toNatInt, Int.ofNat_eq_natCast,
    Int.natCast_eq_zero, LeanRV64D.Functions.xlen, ge_iff_le, Bool.false_and, Bool.false_eq_true,
    divu, BitVec.ofNat_eq_ofNat, BitVec.udiv_eq]
  rw [BitVec.extractLsb'_ofInt_eq_ofInt (by omega)]
  split
  · rename_i heq
    rw [show 0 = (0#64).toNat by rfl, ← BitVec.toNat_eq] at heq
    simp [heq]
  · rename_i hne
    rw [show 0 = (0#64).toNat by rfl, ← BitVec.toNat_eq] at hne
    simp only [hne, ↓reduceIte, ← Int.ofNat_tdiv, BitVec.ofInt_natCast]
    apply BitVec.eq_of_toNat_eq
    have := Nat.div_lt_of_lt (a := rs2_val.toNat) (b := rs1_val.toNat) (c := 2 ^ 64) (by omega)
    simp [BitVec.toNat_ofNat]
    omega

theorem divw_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.divw rs1_val rs2_val false = divw rs1_val rs2_val := by
  simp only [SailRV64.divw, LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int, Nat.reduceAdd,
    LeanRV64D.Functions.not, Bool.false_eq_true, ↓reduceIte, beq_iff_eq, Int.reduceNeg, ge_iff_le,
    Bool.not_false, Bool.true_and, decide_eq_true_eq, divw, LeanRV64D.Functions.sign_extend,
    Sail.BitVec.extractLsb, Sail.BitVec.signExtend]
  rw [BitVec.extractLsb'_ofInt_eq_ofInt (by omega)]
  by_cases h1 : BitVec.extractLsb 31 0 rs1_val = 0#32
  · simp [h1, show ¬ (2 ^ (31 : Int) : Int) ≤ -1 by omega]
  · generalize hrs1 : (BitVec.extractLsb 31 0 rs1_val) = rs1 at *
    generalize hrs2 : (BitVec.extractLsb 31 0 rs2_val) = rs2 at *
    have h1' : ¬ rs1.toInt = 0 := BitVec.toInt_ne.mpr h1
    simp only [h1', ↓reduceIte, h1]
    apply BitVec.eq_of_toInt_eq
    by_cases hcond : rs2 ≠ BitVec.intMin 32 ∨ rs1 ≠ -1#32
    · rw [← BitVec.toInt_sdiv_of_ne_or_ne rs2 rs1 hcond]
      split
      · have := BitVec.toInt_le (x := rs2.sdiv rs1)
        omega
      · simp
    · simp only [ne_eq, not_or, Decidable.not_not] at hcond
      obtain ⟨hcond, hcond'⟩ := hcond
      congr
      simp only [Nat.sub_zero, Nat.reduceAdd, hcond, BitVec.toInt_intMin, Nat.add_one_sub_one,
        hcond', BitVec.reduceNeg, BitVec.reduceToInt, Int.tdiv_neg, Int.tdiv_one, Int.neg_neg,
        Nat.mod_eq_of_lt (a := 2 ^ 31) (b := 2 ^ 32) (by omega),
        show (2 ^ (31 : Int) : Int) ≤ (2 ^ (31 : Nat) : Nat) by omega]
      rfl

theorem divuw_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.divw rs1_val rs2_val true = divuw rs1_val rs2_val := by
  simp only [SailRV64.divw, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int, Nat.reduceAdd,
    LeanRV64D.Functions.not, Bool.not_true, ↓reduceIte, Sail.BitVec.extractLsb, Sail.BitVec.toNatInt, Int.ofNat_eq_natCast,
    beq_iff_eq, Int.natCast_eq_zero, ge_iff_le, Bool.false_and, Bool.false_eq_true, divuw,
    BitVec.udiv_eq]
  rw [BitVec.extractLsb'_ofInt_eq_ofInt (by omega)]
  split
  · rename_i heq
    rw [show ((BitVec.extractLsb 31 0 rs1_val).toNat = 0) =
        ((BitVec.extractLsb 31 0 rs1_val).toNat = (0#(31 - 0 + 1)).toNat) by rfl,
      ← BitVec.toNat_eq] at heq
    simp [heq]
  · rename_i hne
    rw [show ((BitVec.extractLsb 31 0 rs1_val).toNat = 0) =
        ((BitVec.extractLsb 31 0 rs1_val).toNat = (0#(31 - 0 + 1)).toNat) by rfl,
      ← BitVec.toNat_eq] at hne
    generalize hrs1 : (BitVec.extractLsb 31 0 rs1_val) = rs1 at *
    generalize hrs2 : (BitVec.extractLsb 31 0 rs2_val) = rs2 at *
    congr
    simp only [hne, ↓reduceIte, ← Int.ofNat_tdiv, BitVec.ofInt_natCast]
    apply BitVec.eq_of_toNat_eq
    have := Nat.div_lt_of_lt (a := rs2.toNat) (b := rs1.toNat) (c := 2 ^ 32) (by omega)
    simp [BitVec.toNat_ofNat]
    omega

/-! ## Remainder -/

theorem rem_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.rem false rs1_val rs2_val = rem rs1_val rs2_val := by
  simp only [SailRV64.rem, rem, LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int,
    Nat.reduceAdd, Bool.false_eq_true, ↓reduceIte, beq_iff_eq]
  rw [BitVec.extractLsb'_ofInt_eq_ofInt (by omega)]
  by_cases h : rs1_val = 0#64
  · simp [h]
  · simp only [← BitVec.toInt_inj, BitVec.toInt_zero] at h
    simp only [h, ↓reduceIte, BitVec.ofInt_toInt_tmod_toInt]

theorem remu_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.rem true rs1_val rs2_val = remu rs1_val rs2_val := by
  simp only [SailRV64.rem, LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int, remu,
    Sail.BitVec.toNatInt, Int.ofNat_eq_natCast]
  by_cases h1 : rs1_val = 0#64
  · simp [h1, BitVec.extractLsb'_setWidth_of_le]
  · simp only [Nat.reduceAdd, ↓reduceIte, beq_iff_eq]
    have h1' : ¬ rs1_val.toNat = 0 := by
      simp only [BitVec.toNat_eq, BitVec.toNat_ofNat, Nat.zero_mod] at h1
      exact h1
    simp only [Int.natCast_eq_zero, BitVec.umod_eq]
    rw [BitVec.extractLsb'_ofInt_eq_ofInt (by omega)]
    apply BitVec.eq_of_toInt_eq
    simp only [BitVec.toInt_ofInt, Nat.reducePow, BitVec.toInt_umod, h1', ↓reduceIte]
    congr

theorem remw_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.remw false rs1_val rs2_val = remw rs1_val rs2_val := by
  simp only [SailRV64.remw, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int, Nat.reduceAdd,
    Bool.false_eq_true, ↓reduceIte, Nat.reduceSub, Sail.BitVec.extractLsb, beq_iff_eq, remw]
  rw [BitVec.extractLsb'_ofInt_eq_ofInt (by omega)]
  split
  · rename_i htrue
    have heq := BitVec.eq_of_toInt_eq (x := BitVec.extractLsb 31 0 rs1_val) (y := 0#64) htrue
    simp only [Nat.sub_zero, Nat.reduceAdd, Nat.reduceLeDiff, BitVec.setWidth_ofNat_of_le] at heq
    congr
    simp only [heq, BitVec.ofInt_toInt, BitVec.srem_zero]
  · rw [← BitVec.toInt_srem, BitVec.ofInt_toInt]

theorem remuw_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.remw true rs1_val rs2_val = remuw rs1_val rs2_val := by
  simp only [SailRV64.remw, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int, Nat.reduceAdd, Nat.reduceSub,
    Sail.BitVec.extractLsb, Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, beq_iff_eq, remuw, ↓reduceIte, BitVec.umod_eq]
  rw [BitVec.extractLsb'_ofInt_eq_ofInt (by omega)]
  split
  · rename_i htrue
    congr
    norm_cast at htrue
    have heq := BitVec.eq_of_toNat_eq (x := BitVec.extractLsb 31 0 rs1_val) (y := 0#32) htrue
    simp only [BitVec.ofInt_natCast, heq, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.umod_zero]
  · congr
    apply BitVec.eq_of_toInt_eq
    simp only [BitVec.extractLsb_toNat, Nat.shiftRight_zero, Nat.sub_zero, Nat.reduceAdd,
      Nat.reducePow, Int.natCast_emod, Int.cast_ofNat_Int, BitVec.toInt_ofInt, BitVec.toInt_umod]
    rfl

/-! ## Multiplication -/

theorem mul_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.mul rs1_val rs2_val
        {result_part := VectorHalf.Low, signed_rs1 := Signedness.Signed,
          signed_rs2 := Signedness.Signed}
      = mul rs1_val rs2_val := by
  have h1 : rs1_val.toInt = (rs1_val.signExtend 129).toInt := by
    simp only [Nat.reduceLeDiff, BitVec.toInt_signExtend_of_le]
  have h2 : rs2_val.toInt = (rs2_val.signExtend 129).toInt := by
    simp only [Nat.reduceLeDiff, BitVec.toInt_signExtend_of_le]
  simp [SailRV64.mul, LeanRV64D.Functions.mult_to_bits_half, Sail.BitVec.extractLsb,
    LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int, mul, BitVec.extractLsb,
    h2, h1, BitVec.ofInt_mul, ← BitVec.setWidth_eq_extractLsb', BitVec.setWidth_mul,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_signExtend_eq_self, BitVec.mul_comm]

theorem mulh_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.mul rs1_val rs2_val
        {result_part := VectorHalf.High, signed_rs1 := Signedness.Signed,
          signed_rs2 := Signedness.Signed}
      = mulh rs1_val rs2_val := by
  have h1 : rs1_val.toInt = (rs1_val.signExtend 129).toInt := by
    simp only [Nat.reduceLeDiff, BitVec.toInt_signExtend_of_le]
  have h2 : rs2_val.toInt = (rs2_val.signExtend 129).toInt := by
    simp only [Nat.reduceLeDiff, BitVec.toInt_signExtend_of_le]
  simp only [SailRV64.mul, LeanRV64D.Functions.mult_to_bits_half, Int.cast_ofNat_Int,
    Int.reduceMul, Int.reduceSub, Int.reduceToNat, Nat.reduceSub, Nat.reduceAdd,
    Sail.BitVec.extractLsb, BitVec.extractLsb, LeanRV64D.Functions.to_bits_truncate,
    Sail.get_slice_int, h2, h1, BitVec.ofInt_mul, BitVec.ofInt_toInt, mulh]
  rw [BitVec.extractLsb'_extractLsb'_of_le (by omega), BitVec.setWidth_eq_extractLsb' (by omega)]
  simp

theorem mulhu_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.mul rs1_val rs2_val
        {result_part := VectorHalf.High, signed_rs1 := Signedness.Unsigned,
          signed_rs2 := Signedness.Unsigned}
      = mulhu rs1_val rs2_val := by
  simp only [SailRV64.mul, Sail.BitVec.extractLsb, BitVec.extractLsb, Int.cast_ofNat_Int,
    Int.reduceMul, Int.reduceToNat, Int.reduceSub, Nat.reduceSub, Nat.reduceAdd,
    LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int, mulhu, BitVec.truncate_eq_setWidth,
    BitVec.extractLsb'_eq_self, LeanRV64D.Functions.mult_to_bits_half, Sail.BitVec.toNatInt, Int.ofNat_eq_natCast]
  rw [BitVec.extractLsb'_ofInt_eq_ofInt (by omega)]
  congr

theorem mulhsu_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.mul rs1_val rs2_val
        {result_part := VectorHalf.High, signed_rs1 := Signedness.Signed,
          signed_rs2 := Signedness.Unsigned}
      = mulhsu rs1_val rs2_val := by
  have h1 : rs2_val.toInt = (rs2_val.signExtend 129).toInt := by
    simp only [Nat.reduceLeDiff, BitVec.toInt_signExtend_of_le]
  simp only [SailRV64.mul, LeanRV64D.Functions.mult_to_bits_half, Sail.BitVec.extractLsb,
    LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int, Sail.BitVec.toNatInt,
    Int.ofNat_eq_natCast, Nat.cast_ofNat, Int.reduceMul, Int.reduceSub, Int.reduceToNat,
    Nat.reduceSub, Nat.reduceAdd, mulhsu, BitVec.truncate_eq_setWidth]
  rw [h1, BitVec.ofInt_mul, BitVec.ofInt_toInt, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  simp only [BitVec.extractLsb, Nat.reduceSub, Nat.reduceAdd]
  rw [BitVec.extractLsb'_extractLsb'_of_le (by omega)]
  simp

theorem mulw_eq (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    SailRV64.mulw rs1_val rs2_val = mulw rs1_val rs2_val := by
  simp only [SailRV64.mulw, LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend,
    LeanRV64D.Functions.to_bits_truncate, Sail.get_slice_int, Sail.BitVec.extractLsb, mulw]
  rw [BitVec.extractLsb'_ofInt_eq_ofInt (by omega), BitVec.extractLsb]
  congr
  apply BitVec.eq_of_toInt_eq
  simp

end SP1Clean.RV64
