import Clean.Circuit.Basic
import Clean.Utils.Field
import Mathlib.Tactic.LinearCombination
import SP1Clean.Math.GetElemFastPath

/-! # Minimal numeric foundations

A `Word` is four little-endian 16-bit limbs of a field element; `toBitVec64`
reassembles the 64-bit value. Everything is field-generic over `ZMod p` with
`Fact (2 ^ 17 < p)` (so each limb and small constant stays `< p`). -/

namespace SP1Clean

variable {p : ℕ}

-- Project-wide `circuit_norm` augmentation. These four pure, terminating projections recur inline in
-- `simp only [..., circuit_norm]` lists across chip soundness proofs (the `fromElements`/ProvableStruct
-- field-projection tower in particular), yet Clean's `circuit_norm` only carries the `getElem`/`add_zero`
-- siblings (`Clean/Circuit/Basic.lean`). Globalizing them here (Word.lean is transitively imported by
-- nearly every op/reader/chip) lets those lists drop to a bare `simp only [circuit_norm]`.
-- `Word.toNat_def` is deliberately NOT globalized — it unfolds every `Word.toNat` to a 4-limb sum and
-- must stay an explicit `rw`.
attribute [circuit_norm] Vector.getElem_take Vector.getElem_drop List.sum_cons List.sum_nil

/-- A 64-bit value as four little-endian 16-bit limbs. Identical in shape to
Clean's `fields 4`. -/
abbrev Word (F : Type) := Vector F 4

namespace Word

/-- Each limb is a genuine 16-bit value. -/
def isU64 [NeZero p] (w : Word (ZMod p)) : Prop :=
  ∀ i : Fin 4, w[i].val < 2 ^ 16

lemma isU64_of_cases [NeZero p] {w : Word (ZMod p)}
    (h0 : w[0].val < 2 ^ 16) (h1 : w[1].val < 2 ^ 16)
    (h2 : w[2].val < 2 ^ 16) (h3 : w[3].val < 2 ^ 16) : w.isU64 := by
  intro i; fin_cases i <;> simpa [isU64]

lemma lt_cases_of_isU64 [NeZero p] {w : Word (ZMod p)} (hw : w.isU64) :
    w[0].val < 2 ^ 16 ∧ w[1].val < 2 ^ 16 ∧ w[2].val < 2 ^ 16 ∧ w[3].val < 2 ^ 16 :=
  ⟨hw 0, hw 1, hw 2, hw 3⟩

/-- Little-endian reassembly to `ℕ`. -/
def toNat [NeZero p] (w : Word (ZMod p)) : ℕ :=
  w[0].val + w[1].val * 2 ^ 16 + w[2].val * 2 ^ 32 + w[3].val * 2 ^ 48

lemma toNat_def [NeZero p] (w : Word (ZMod p)) :
    w.toNat = w[0].val + w[1].val * 2 ^ 16 + w[2].val * 2 ^ 32 + w[3].val * 2 ^ 48 := rfl

/-- The 64-bit value of the word. -/
def toBitVec64 [NeZero p] (w : Word (ZMod p)) : BitVec 64 :=
  BitVec.ofNat 64 (toNat w)

lemma toBitVec64_toNat [NeZero p] {w : Word (ZMod p)} (hw : w.isU64) :
    w.toBitVec64.toNat = w.toNat := by
  simp only [toBitVec64, BitVec.toNat_ofNat, toNat]
  have := lt_cases_of_isU64 hw
  omega

/-- The 64-bit value's residue mod 4 is the low limb's residue mod 4 (the higher limbs all carry a
factor `2^16`, hence `4 ∣`). No `isU64` hypothesis needed: `2^64` is itself a multiple of 4, so the
`BitVec.ofNat` wrap-around drops out. Used by the JALR/Jal/Branch alignment bridges to lift the
in-circuit low-limb divisibility to the committed `next_pc` word. -/
lemma toBitVec64_toNat_mod_four [NeZero p] (w : Word (ZMod p)) :
    w.toBitVec64.toNat % 4 = w[0].val % 4 := by
  simp only [toBitVec64, BitVec.toNat_ofNat, toNat,
    show (2 : ℕ) ^ 16 = 65536 from by norm_num,
    show (2 : ℕ) ^ 32 = 4294967296 from by norm_num,
    show (2 : ℕ) ^ 48 = 281474976710656 from by norm_num]
  rw [Nat.mod_mod_of_dvd _ (show (4 : ℕ) ∣ 2 ^ 64 from by norm_num)]
  omega

/-- The 128-bit zero-extension of a (64-bit) word's value. Used for the `MULH*`
high-half product specs, where the schoolbook 16-byte product is the full 128-bit
product of the (sign/zero-extended) operands. -/
def toBitVec128 [NeZero p] (w : Word (ZMod p)) : BitVec 128 :=
  BitVec.ofNat 128 (toNat w)

lemma toBitVec128_toNat [NeZero p] {w : Word (ZMod p)} (hw : w.isU64) :
    w.toBitVec128.toNat = w.toNat := by
  simp only [toBitVec128, BitVec.toNat_ofNat, toNat]
  have := lt_cases_of_isU64 hw
  rw [Nat.mod_eq_of_lt (by omega)]

end Word

/-- Clearing bit 0 (the Sail `BitVec.update _ 0 0#1`, which unfolds to `~~~(1#64) &&& ·`) of
`BitVec.ofNat 64 (M + b)` — with `b ≤ 1` and `M` even — yields `BitVec.ofNat 64 M`. Stated in the
Sail-free `~~~(1#64) &&&` form so `Math/` stays Sail-independent; the JALR bridge bridges this to
`BitVec.update` (a one-line `simp [Sail.BitVec.update, Sail.BitVec.updateSubrange']`). Used by the JALR
LSB-clearing `Spec` conjunct (`toNat add_value = toNat next_pc_word + lsb`, `lsb ∈ {0,1}`). -/
lemma ofNat64_clear_lsb_and {M b : ℕ} (hb : b ≤ 1) (hM : M % 2 = 0) :
    BitVec.ofNat 64 M = ~~~(1#64) &&& BitVec.ofNat 64 (M + b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_ofNat, hi, decide_true,
    Bool.true_and]
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0; simp [Nat.testBit_zero, hM]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    have hdiv : (M + b) / 2 = M / 2 := by omega
    simp [Nat.testBit_succ, hdiv]

/-! ## Field constants (`ZMod p`, `Fact (2 ^ 17 < p)`) -/

@[simp] lemma val_65536_zmod_p [NeZero p] [Fact (2 ^ 17 < p)] :
    (65536 : ZMod p).val = 65536 := by
  have : (131072 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  exact ZMod.val_natCast_of_lt (show (65536 : ℕ) < p by omega)

lemma val_65536_ne_zero [NeZero p] [Fact (2 ^ 17 < p)] : (65536 : ZMod p) ≠ 0 := by
  have h : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
  intro hz; rw [hz] at h; simp at h

@[simp] lemma val_2_zmod_p [NeZero p] [Fact (2 ^ 17 < p)] :
    (2 : ZMod p).val = 2 := by
  have : (131072 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  exact ZMod.val_natCast_of_lt (show (2 : ℕ) < p by omega)

@[simp] lemma val_4_zmod_p [NeZero p] [Fact (2 ^ 17 < p)] :
    (4 : ZMod p).val = 4 := by
  have : (131072 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  exact ZMod.val_natCast_of_lt (show (4 : ℕ) < p by omega)

lemma val_4_ne_zero [NeZero p] [Fact (2 ^ 17 < p)] : (4 : ZMod p) ≠ 0 := by
  have h : (4 : ZMod p).val = 4 := val_4_zmod_p
  intro hz; rw [hz] at h; simp at h

/-- The `÷4` alignment check `(x · 4⁻¹).val < 2^14` pins `x = (x · 4⁻¹) · 4` exactly in `ℕ`: since
`(x · 4⁻¹).val · 4 < 2^16 < p` there is no wrap, so `x.val = (x · 4⁻¹).val · 4`. The shared core of the
two corollaries below (divisibility + the `< 2^16` bound). -/
lemma val_eq_mul_inv_four_mul_four [Fact p.Prime] [Fact (2 ^ 17 < p)] {x : ZMod p}
    (h : (x * (4 : ZMod p)⁻¹).val < 2 ^ 14) : x.val = (x * (4 : ZMod p)⁻¹).val * 4 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : (131072 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  rw [show (2 : ℕ) ^ 14 = 16384 from by norm_num] at h
  have h41 : (4 : ZMod p)⁻¹ * 4 = 1 := inv_mul_cancel₀ val_4_ne_zero
  conv_lhs => rw [show x = (x * (4 : ZMod p)⁻¹) * 4 by rw [mul_assoc, h41, mul_one]]
  rw [ZMod.val_mul, val_4_zmod_p, Nat.mod_eq_of_lt (by omega)]

/-- The reverse of `U16toU8OperationSafe.high_byte_lt` for the `÷4` alignment check: if `x · 4⁻¹` is a
14-bit value (the in-circuit `Range` byte-lookup), then `x` is divisible by 4. -/
lemma val_mod_four_of_mul_inv_four_lt [Fact p.Prime] [Fact (2 ^ 17 < p)] {x : ZMod p}
    (h : (x * (4 : ZMod p)⁻¹).val < 2 ^ 14) : x.val % 4 = 0 := by
  rw [val_eq_mul_inv_four_mul_four h]; omega

/-- Companion bound to `val_mod_four_of_mul_inv_four_lt`: the same `÷4` range check also gives
`x.val < 2^16` (`x.val = (x · 4⁻¹).val · 4 < 2^14 · 4`). Used by the JALR LSB-clearing soundness to lift
the field subtraction `value[0] - lsb` to `ℕ`. -/
lemma val_lt_65536_of_mul_inv_four_lt [Fact p.Prime] [Fact (2 ^ 17 < p)] {x : ZMod p}
    (h : (x * (4 : ZMod p)⁻¹).val < 2 ^ 14) : x.val < 2 ^ 16 := by
  have he := val_eq_mul_inv_four_mul_four h
  rw [show (2 : ℕ) ^ 14 = 16384 from by norm_num] at h
  rw [he, show (2 : ℕ) ^ 16 = 65536 from by norm_num]; omega

@[simp] lemma val_65535_zmod_p [NeZero p] [Fact (2 ^ 17 < p)] :
    (65535 : ZMod p).val = 65535 := by
  have : (131072 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  exact ZMod.val_natCast_of_lt (show (65535 : ℕ) < p by omega)

/-- The 16-bit complement `65535 - x` has a clean `.val` (= `65535 - x.val` in `ℕ`).
Used by the Sub borrow-chain limb lift: feeding `bbar := 65535 - b[i]` (a genuine
16-bit value) into the unchanged `limb_lift` keeps every additive sum `< p`, exactly
as in the Add carry chain. -/
lemma val_compl_65535 [NeZero p] [Fact (2 ^ 17 < p)] {x : ZMod p} (hx : x.val < 2 ^ 16) :
    (((65535 : ℕ) : ZMod p) - x).val = 65535 - x.val := by
  have hp : (131072 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have hxle : x.val ≤ 65535 := by omega
  have hcast : ((65535 - x.val : ℕ) : ZMod p) = ((65535 : ℕ) : ZMod p) - x := by
    rw [Nat.cast_sub hxle, ZMod.natCast_zmod_val]
  rw [← hcast]
  exact ZMod.val_natCast_of_lt (by omega)

/-- Per-limb Nat lift: the `ZMod`-level limb equation `bb + vv + prev = aa + cc *
65536` (with `prev, cc ∈ {0,1}` and `bb, vv, aa` 16-bit-bounded) lifts to the `ℕ`
equation `bb.val + vv.val + prev.val = aa.val + cc.val * 65536`. Ported verbatim
from `AddOperation.limb_lift`. -/
lemma limb_lift [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (bb vv aa prev cc : ZMod p)
    (hbb : bb.val < 2 ^ 16) (hvv : vv.val < 2 ^ 16) (haa : aa.val < 2 ^ 16)
    (hprev : prev = 0 ∨ prev = 1) (hcc : cc = 0 ∨ cc = 1)
    (h : bb + vv + prev = aa + cc * 65536) :
    bb.val + vv.val + prev.val = aa.val + cc.val * 65536 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  apply_fun ZMod.val at h
  have hprev_lt : prev.val ≤ 1 := by
    rcases hprev with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hcc_lt : cc.val ≤ 1 := by
    rcases hcc with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hbv : (bb + vv).val = bb.val + vv.val :=
    ZMod.val_add_of_lt (by omega)
  have h1 : (bb + vv + prev).val = bb.val + vv.val + prev.val := by
    rw [ZMod.val_add_of_lt (by rw [hbv]; omega), hbv]
  have h2 : (cc * 65536 : ZMod p).val = cc.val * 65536 := by
    rcases hcc with h | h <;> simp [h, ZMod.val_zero, val_65536_zmod_p, ZMod.val_one]
  have h3 : (aa + cc * 65536 : ZMod p).val = aa.val + cc.val * 65536 := by
    rw [ZMod.val_add_of_lt
      (by rw [h2]; rcases hcc with h | h <;>
            simp [h, ZMod.val_zero, ZMod.val_one] <;> omega), h2]
  rw [h1, h3] at h
  exact h

/-- `x * (x + -1) = 0 → x ∈ {0,1}` in a field, via `inv_mul_cancel₀` (avoids
`mul_eq_zero`, which hits a `ZMod p` `Mul`-instance unification quirk). -/
lemma bool_of_mul_pred [Fact (Nat.Prime p)] {x : ZMod p}
    (h : x * (x + -1) = 0) : x = 0 ∨ x = 1 := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · right
    have hx1 : x⁻¹ * (x * (x + -1)) = x⁻¹ * 0 := by rw [h]
    rw [mul_zero, ← mul_assoc, inv_mul_cancel₀ hx, one_mul] at hx1
    linear_combination hx1

set_option maxHeartbeats 2000000 in
/-- **Sign-extension reassembly** (the ADDW/SUBW keystone). The four-limb word
`#v[v0, v1, m*65535, m*65535]` — where `v0, v1` are the low two 16-bit limbs of a 32-bit
result and `m ∈ {0,1}` is the high bit of `v1` — is the 64-bit sign extension of the 32-bit
value `X` whose `toNat` is `v0 + v1*2^16`. The two high limbs realise the sign fill because
`65535*(2^32 + 2^48) = 2^64 - 2^32`, which is exactly `toNat_signExtend`'s correction term. -/
lemma toBitVec64_signExtend_word [NeZero p] [Fact (2 ^ 17 < p)]
    (R : Word (ZMod p)) (X : BitVec 32) (m : ZMod p)
    (hr0 : R[0].val < 2 ^ 16) (hr1 : R[1].val < 2 ^ 16)
    (hm : m = if R[1].val ≥ 32768 then 1 else 0)
    (hr2 : R[2] = m * 65535) (hr3 : R[3] = m * 65535)
    (hX : X.toNat = R[0].val + R[1].val * 2 ^ 16) :
    Word.toBitVec64 R = X.signExtend 64 := by
  have hp : 2 ^ 17 < p := Fact.out
  have hm_lt : (m * 65535 : ZMod p).val < 2 ^ 16 := by
    rw [hm]; split_ifs with h
    · rw [one_mul, val_65535_zmod_p]; omega
    · rw [zero_mul, ZMod.val_zero]; omega
  have hRU : Word.isU64 R :=
    Word.isU64_of_cases hr0 hr1 (by rw [hr2]; exact hm_lt) (by rw [hr3]; exact hm_lt)
  have hXlt : X.toNat < 2 ^ 32 := X.isLt
  rw [← BitVec.toNat_inj, Word.toBitVec64_toNat hRU, Word.toNat_def,
      BitVec.toNat_signExtend, BitVec.toNat_setWidth, hX,
      Nat.mod_eq_of_lt (by omega : R[0].val + R[1].val * 2 ^ 16 < 2 ^ 64)]
  have hmsb_iff : (X.msb = true) ↔ R[1].val ≥ 32768 := by
    rw [BitVec.msb_eq_decide, decide_eq_true_eq, hX]; omega
  split_ifs with hmsb
  · have hge : R[1].val ≥ 32768 := hmsb_iff.mp hmsb
    have hmv : (m * 65535 : ZMod p).val = 65535 := by
      rw [hm, if_pos hge, one_mul, val_65535_zmod_p]
    rw [hr2, hr3, hmv]; omega
  · have hlt : ¬ R[1].val ≥ 32768 := fun hc => hmsb (hmsb_iff.mpr hc)
    have hmv : (m * 65535 : ZMod p).val = 0 := by
      rw [hm, if_neg hlt, zero_mul, ZMod.val_zero]
    rw [hr2, hr3, hmv]; omega

end SP1Clean
