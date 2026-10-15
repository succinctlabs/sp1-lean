module

public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Data.BitVec

/-!
# `BitVec` lemmas to be ported upstream

Width-changing `BitVec` facts the RV64 semantic bridge needs: truncating an `ofInt` to a narrower
width, sign-extending and truncating back, the two-`Int` description of `srem`, and the arithmetic
right shift expressed through a sign extension followed by an `extractLsb`. Nothing here mentions
Clean or SP1.

The gap against upstream (Lean core `Init/Data/BitVec/`, v4.32.2): core has `toInt_srem`,
`toInt_sdiv_of_ne_or_ne`, `getElem_sshiftRight`, `getLsbD_signExtend`, `getLsbD_extractLsb`, and
`ofInt_toInt`, but not these four composites; each is a short consequence of those and belongs
beside them. The former `riscv-lean` dependency carried private copies of the same facts.
-/

public section

set_option linter.unusedSimpArgs false

namespace BitVec

/-- Truncating `ofInt w' x` to a narrower width `w ≤ w'` is `ofInt w x`. -/
theorem extractLsb'_ofInt_eq_ofInt {x : Int} {w w' : Nat} (h : w ≤ w') :
    (BitVec.ofInt w' x).extractLsb' 0 w = BitVec.ofInt w x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofInt, Nat.shiftRight_zero]
  push_cast
  have hd : ((2 : Int) ^ w) ∣ ((2 : Int) ^ w') := pow_dvd_pow 2 h
  have hy : 0 ≤ x % (2 : Int) ^ w' := Int.emod_nonneg _ (by positivity)
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hy
  rw [← Int.emod_emod_of_dvd x hd, hn, Int.toNat_natCast,
    show ((n : Int) % (2 : Int) ^ w) = ((n % 2 ^ w : Nat) : Int) by push_cast; rfl,
    Int.toNat_natCast]

/-- Sign-extending to `w' ≥ w` and truncating back to `w` is the identity. -/
theorem setWidth_signExtend_eq_self {w w' : Nat} {x : BitVec w} (h : w ≤ w') :
    (x.signExtend w').setWidth w = x := by
  ext i hi
  rw [BitVec.getElem_setWidth, BitVec.getLsbD_signExtend]
  simp [hi, show i < w' by omega, BitVec.getLsbD_eq_getElem]

/-- `srem` through the two-`Int` truncating remainder. -/
theorem ofInt_toInt_tmod_toInt {w : Nat} {x y : BitVec w} :
    BitVec.ofInt w (x.toInt.tmod y.toInt) = x.srem y := by
  rw [← BitVec.toInt_srem, BitVec.ofInt_toInt]

/-- The arithmetic right shift by `n` is the sign extension by `n` bits, read from bit `n` up. -/
theorem sshiftRight_eq_setWidth_extractLsb_signExtend {w : Nat} (n : Nat) (x : BitVec w) :
    x.sshiftRight n = ((x.signExtend (w + n)).extractLsb (w - 1 + n) n).setWidth w := by
  ext i hi
  simp only [BitVec.getElem_sshiftRight, BitVec.getElem_setWidth, BitVec.getLsbD_extractLsb,
    BitVec.getLsbD_signExtend, Nat.add_sub_cancel, show i ≤ w - 1 by omega, decide_true,
    Bool.true_and, show n + i < w + n by omega]
  split <;> simp_all <;> omega

end BitVec
