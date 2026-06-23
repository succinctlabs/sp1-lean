import SP1Clean.Proofs.Chips.ShiftRightChip.Core
import RISCV.Instructions

/-! # `SP1Clean.ShiftRightChip` — bitvec/word goal-shape converters (native arithmetic)

The mathematical bridge from the chip's committed result columns (in `Word`/`HWord.toBitVec*` /
Nat-division form, as the `ShiftRightMath.*_close_su16_*` dispatch lemmas produce them) to the RV64 ISA
functions (`RV64.srl`/`sra`/`srlw`/`sraw` from `RISCV/Instructions.lean`). Split out of `Formal.lean`
(the chip-folder convention, mirroring `DivRemChip/Math.lean`): these are pure `Word`/`BitVec`/`ZMod p`
lemmas with no circuit context.

The `RV64.srl`/`sra` `.toNat` reductions plant a `2^64` that the kernel deep-recurses on when reduced
over a concrete `Word`-derived `BitVec 64` (`BitVec.toNat_ushiftRight`/`sshiftRight` via the
`@[expose]` shift bodies; see `docs/agents/proof-patterns.md`). Rather than suppress the kernel,
we isolate that unfold into abstract-`BitVec` bridges
(`srl_toNat`/`sra_toNat_{false,true}`, kernel-checked once over variables) and mask every `2^N` power
to a concrete literal — the `ShiftLeftChip` discipline. All lemmas are kernel-clean and axiom-clean
(`#print axioms` = `[propext, Classical.choice, Quot.sound]`). -/

namespace SP1Clean.ShiftRightChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-! ### Abstract-`BitVec` RV64 shift bridges (kernel-clean isolation of the `2^64` landmine)

`RV64.srl`/`RV64.sra` unfold (via `BitVec.ushiftRight`/`sshiftRight`'s `@[expose]` bodies) plants a
`2^64` the kernel deep-recurses on **when reduced over a concrete `Word`-derived `BitVec 64`**. We
isolate that unfold into these three lemmas over **abstract** `BitVec 64` arguments, where the `2^64`
body is kernel-checked once over variables (the discipline `ShiftLeftChip`'s `sll_rv64_eq` uses). The
`_div_to_bitvec` wrappers then only apply `BitVec.eq_of_toNat_eq` plus the clean `Word`-level
shift-count bridge — they never re-unfold a shift over a `Word` value, so they stay kernel-clean. -/

/-- `(RV64.srl c b).toNat` as a Nat division, over abstract `BitVec 64` (isolates the `2^64` unfold). -/
lemma srl_toNat (c b : BitVec 64) : (RV64.srl c b).toNat = b.toNat / 2 ^ (c.toNat % 64) := by
  have hsh : (BitVec.extractLsb 5 0 c).toNat = c.toNat % 64 := by
    simp only [BitVec.extractLsb, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  simp only [RV64.srl]
  rw [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hsh]

/-- `(RV64.sra c b).toNat` on a non-negative `b` (msb = 0): arithmetic = logical shift. -/
lemma sra_toNat_false (c b : BitVec 64) (h_msb : b.msb = false) :
    (RV64.sra c b).toNat = b.toNat / 2 ^ (c.toNat % 64) := by
  have hsh : (BitVec.extractLsb 5 0 c).toNat = c.toNat % 64 := by
    simp only [BitVec.extractLsb, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  simp only [RV64.sra]
  rw [BitVec.sshiftRight_eq', BitVec.toNat_sshiftRight_of_msb_false h_msb,
      Nat.shiftRight_eq_div_pow, hsh]

/-- `(RV64.sra c b).toNat` on a negative `b` (msb = 1): the sign-filled complement form. -/
lemma sra_toNat_true (c b : BitVec 64) (h_msb : b.msb = true) :
    (RV64.sra c b).toNat = 2 ^ 64 - 1 - (2 ^ 64 - 1 - b.toNat) / 2 ^ (c.toNat % 64) := by
  have hsh : (BitVec.extractLsb 5 0 c).toNat = c.toNat % 64 := by
    simp only [BitVec.extractLsb, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  simp only [RV64.sra]
  rw [BitVec.sshiftRight_eq', BitVec.toNat_sshiftRight_of_msb_true h_msb,
      Nat.shiftRight_eq_div_pow, hsh]

omit [Fact (Nat.Prime p)] in
/-- **Goal-shape conversion for SRL.** Reduces the `RV64.srl` Spec equality to the Nat division form the
`srl_close_su16_*` lemmas produce, with the shift count normalised to `rs2[0].val % 64`. The `2^64`
kernel landmine is isolated in `srl_toNat`; here only `BitVec.eq_of_toNat_eq` and the clean shift-count
bridge are used. -/
lemma srl_div_to_bitvec (W rs1 rs2 : Word (ZMod p)) (h_rs2U : Word.isU64 rs2)
    (hdiv : (Word.toBitVec64 W).toNat
        = (Word.toBitVec64 rs1).toNat / 2 ^ (rs2[0].val % 64)) :
    Word.toBitVec64 W = RV64.srl (Word.toBitVec64 rs2) (Word.toBitVec64 rs1) := by
  have hsh : (Word.toBitVec64 rs2).toNat % 64 = rs2[0].val % 64 := by
    rw [Word.toBitVec64_toNat h_rs2U, Word.toNat_def,
        show (2:ℕ)^16 = 65536 from by norm_num, show (2:ℕ)^32 = 4294967296 from by norm_num,
        show (2:ℕ)^48 = 281474976710656 from by norm_num]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [srl_toNat, hsh]
  exact hdiv

omit [Fact (Nat.Prime p)] in
/-- **SRA goal-shape conversion, MSB = 0 arm.** On a non-negative `rs1` (`toBitVec64 rs1`.msb = false),
arithmetic shift = logical shift, so `RV64.sra` reduces to the same Nat division form as `RV64.srl`. -/
lemma sra_div_to_bitvec_false (W rs1 rs2 : Word (ZMod p)) (h_rs2U : Word.isU64 rs2)
    (h_msb : (Word.toBitVec64 rs1).msb = false)
    (hdiv : (Word.toBitVec64 W).toNat = (Word.toBitVec64 rs1).toNat / 2 ^ (rs2[0].val % 64)) :
    Word.toBitVec64 W = RV64.sra (Word.toBitVec64 rs2) (Word.toBitVec64 rs1) := by
  have hsh : (Word.toBitVec64 rs2).toNat % 64 = rs2[0].val % 64 := by
    rw [Word.toBitVec64_toNat h_rs2U, Word.toNat_def,
        show (2:ℕ)^16 = 65536 from by norm_num, show (2:ℕ)^32 = 4294967296 from by norm_num,
        show (2:ℕ)^48 = 281474976710656 from by norm_num]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [sra_toNat_false _ _ h_msb, hsh]
  exact hdiv

omit [Fact (Nat.Prime p)] in
/-- **SRA goal-shape conversion, MSB = 1 arm.** On a negative `rs1`, arithmetic shift fills the high bits
with the sign, giving the `2^64 - 1 - (2^64 - 1 - rs1) / 2^shamt` form (`toNat_sshiftRight_of_msb_true`). -/
lemma sra_div_to_bitvec_true (W rs1 rs2 : Word (ZMod p)) (h_rs2U : Word.isU64 rs2)
    (h_msb : (Word.toBitVec64 rs1).msb = true)
    (hsra : (Word.toBitVec64 W).toNat
      = 2 ^ 64 - 1 - (2 ^ 64 - 1 - (Word.toBitVec64 rs1).toNat) / 2 ^ (rs2[0].val % 64)) :
    Word.toBitVec64 W = RV64.sra (Word.toBitVec64 rs2) (Word.toBitVec64 rs1) := by
  have hsh : (Word.toBitVec64 rs2).toNat % 64 = rs2[0].val % 64 := by
    rw [Word.toBitVec64_toNat h_rs2U, Word.toNat_def,
        show (2:ℕ)^16 = 65536 from by norm_num, show (2:ℕ)^32 = 4294967296 from by norm_num,
        show (2:ℕ)^48 = 281474976710656 from by norm_num]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [sra_toNat_true _ _ h_msb, hsh]
  exact hsra

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
/-- The MSB of `rs1`'s low 32 bits is the high bit of limb 1 (`rs1[1] ≥ 2^15`). The SRAW sign bit.
Mirrors the kernel-clean `ShiftRightMath.toBitVec64_msb_eq_b3_ge` template: a `rw` chain (not
`simp only`) plus full concrete-literal masking of every `2^N` power (incl. `2^48`), so the kernel
never deep-recurses on a symbolic power. -/
lemma low32_msb_eq_b1 [NeZero p] {b : Word (ZMod p)} (h_isU64 : Word.isU64 b) :
    (BitVec.extractLsb' 0 32 (Word.toBitVec64 b)).msb = decide (b[1].val ≥ 32768) := by
  obtain ⟨b0_16, b1_16, _, _⟩ := Word.lt_cases_of_isU64 h_isU64
  rw [BitVec.msb_eq_decide, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
      Word.toBitVec64_toNat h_isU64, Word.toNat_def]
  have e16 : (2 : ℕ) ^ 16 = 65536 := by decide
  have e31 : (2 : ℕ) ^ (32 - 1) = 2147483648 := by decide
  have e32 : (2 : ℕ) ^ 32 = 4294967296 := by decide
  have e48 : (2 : ℕ) ^ 48 = 281474976710656 := by decide
  rw [e16, e31, e32, e48] at *
  congr 1
  apply propext
  constructor
  · intro h; omega
  · intro h; omega

omit [Fact (Nat.Prime p)] in
/-- `HWord.toBitVec32 #v[a,b]`'s `toNat` is the little-endian sum when both limbs are `< 2^16`. -/
lemma hword_toNat {a b : ZMod p} (ha : a.val < 2 ^ 16) (hb : b.val < 2 ^ 16) :
    (ShiftRightMath.HWord.toBitVec32 #v[a, b]).toNat = a.val + b.val * 2 ^ 16 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  unfold ShiftRightMath.HWord.toBitVec32
  simp only [BitVec.toNat_ofNat, ShiftRightMath.HWord.toNat, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  omega

/-- **SRLW goal-shape conversion.** The committed result word `Wd` is the 64-bit sign-extension of the
low-32 logical shift. Uses `toBitVec64_signExtend_word` (the W-variant keystone): `Wd[2] = Wd[3] = m*65535`
sign-fill with `m` the output high bit (`srw_msb` on `a[1]`), and the low two limbs carry the 32-bit logical
shift `(rs1.low32) / 2^(rs2[0] % 32)`. `RV64.srlw` unfolds to exactly `signExtend 64` of that shift. -/
lemma srlw_div_to_bitvec (Wd rs1 rs2 : Word (ZMod p))
    (h_rs1U : Word.isU64 rs1) (h_rs2U : Word.isU64 rs2) (m : ZMod p)
    (hr0 : Wd[0].val < 2 ^ 16) (hr1 : Wd[1].val < 2 ^ 16)
    (hm : m = if Wd[1].val ≥ 32768 then 1 else 0)
    (hr2 : Wd[2] = m * 65535) (hr3 : Wd[3] = m * 65535)
    (hdiv : (ShiftRightMath.HWord.toBitVec32 #v[Wd[0], Wd[1]]).toNat
        = (ShiftRightMath.HWord.toBitVec32 #v[rs1[0], rs1[1]]).toNat / 2 ^ (rs2[0].val % 32)) :
    Word.toBitVec64 Wd = RV64.srlw (Word.toBitVec64 rs2) (Word.toBitVec64 rs1) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨hr1_0, hr1_1, _, _⟩ := Word.lt_cases_of_isU64 h_rs1U
  rw [hword_toNat hr0 hr1, hword_toNat hr1_0 hr1_1] at hdiv
  have hlow : (BitVec.extractLsb' 0 32 (Word.toBitVec64 rs1)).toNat
      = rs1[0].val + rs1[1].val * 2 ^ 16 := by
    rw [BitVec.extractLsb'_toNat, Word.toBitVec64_toNat h_rs1U, Word.toNat_def,
        Nat.shiftRight_zero]; omega
  have hshamt : (BitVec.extractLsb' 0 5 (BitVec.extractLsb' 0 32 (Word.toBitVec64 rs2))).toNat
      = rs2[0].val % 32 := by
    rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, Word.toBitVec64_toNat h_rs2U,
        Word.toNat_def, Nat.shiftRight_zero, Nat.shiftRight_zero]; omega
  have hX : (BitVec.extractLsb' 0 32 (Word.toBitVec64 rs1) >>>
        BitVec.extractLsb' 0 5 (BitVec.extractLsb' 0 32 (Word.toBitVec64 rs2))).toNat
      = Wd[0].val + Wd[1].val * 2 ^ 16 := by
    rw [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
        hlow, hshamt]; exact hdiv.symm
  rw [toBitVec64_signExtend_word Wd _ m hr0 hr1 hm hr2 hr3 hX]; rfl

/-- **SRAW goal-shape conversion, MSB = 0 arm.** On a non-negative low-32 input, the arithmetic word-shift
equals the logical one, so the result is `signExtend 64` of the same division form as SRLW. -/
lemma sraw_div_to_bitvec_false (Wd rs1 rs2 : Word (ZMod p))
    (h_rs1U : Word.isU64 rs1) (h_rs2U : Word.isU64 rs2) (m : ZMod p)
    (hr0 : Wd[0].val < 2 ^ 16) (hr1 : Wd[1].val < 2 ^ 16)
    (hm : m = if Wd[1].val ≥ 32768 then 1 else 0)
    (hr2 : Wd[2] = m * 65535) (hr3 : Wd[3] = m * 65535)
    (h_msb : (BitVec.extractLsb' 0 32 (Word.toBitVec64 rs1)).msb = false)
    (hdiv : (ShiftRightMath.HWord.toBitVec32 #v[Wd[0], Wd[1]]).toNat
        = (ShiftRightMath.HWord.toBitVec32 #v[rs1[0], rs1[1]]).toNat / 2 ^ (rs2[0].val % 32)) :
    Word.toBitVec64 Wd = RV64.sraw (Word.toBitVec64 rs2) (Word.toBitVec64 rs1) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨hr1_0, hr1_1, _, _⟩ := Word.lt_cases_of_isU64 h_rs1U
  rw [hword_toNat hr0 hr1, hword_toNat hr1_0 hr1_1] at hdiv
  have hlow : (BitVec.extractLsb' 0 32 (Word.toBitVec64 rs1)).toNat
      = rs1[0].val + rs1[1].val * 2 ^ 16 := by
    rw [BitVec.extractLsb'_toNat, Word.toBitVec64_toNat h_rs1U, Word.toNat_def,
        Nat.shiftRight_zero]; omega
  have hshamt : (BitVec.extractLsb' 0 5 (Word.toBitVec64 rs2)).toNat = rs2[0].val % 32 := by
    rw [BitVec.extractLsb'_toNat, Word.toBitVec64_toNat h_rs2U, Word.toNat_def,
        Nat.shiftRight_zero]; omega
  have hX : (BitVec.sshiftRight' (BitVec.extractLsb' 0 32 (Word.toBitVec64 rs1))
        (BitVec.extractLsb' 0 5 (Word.toBitVec64 rs2))).toNat = Wd[0].val + Wd[1].val * 2 ^ 16 := by
    rw [BitVec.sshiftRight_eq', BitVec.toNat_sshiftRight_of_msb_false h_msb,
        Nat.shiftRight_eq_div_pow, hlow, hshamt]; exact hdiv.symm
  rw [toBitVec64_signExtend_word Wd _ m hr0 hr1 hm hr2 hr3 hX]
  simp only [RV64.sraw, BitVec.extractLsb]

/-- **SRAW goal-shape conversion, MSB = 1 arm.** On a negative low-32 input, the arithmetic word-shift
fills with the sign, giving the `2^32 - 1 - (2^32 - 1 - rs1.low32) / 2^shamt` complement form
(`toNat_sshiftRight_of_msb_true` at width 32), then `signExtend 64`. -/
lemma sraw_div_to_bitvec_true (Wd rs1 rs2 : Word (ZMod p))
    (h_rs1U : Word.isU64 rs1) (h_rs2U : Word.isU64 rs2) (m : ZMod p)
    (hr0 : Wd[0].val < 2 ^ 16) (hr1 : Wd[1].val < 2 ^ 16)
    (hm : m = if Wd[1].val ≥ 32768 then 1 else 0)
    (hr2 : Wd[2] = m * 65535) (hr3 : Wd[3] = m * 65535)
    (h_msb : (BitVec.extractLsb' 0 32 (Word.toBitVec64 rs1)).msb = true)
    (hdiv : (ShiftRightMath.HWord.toBitVec32 #v[Wd[0], Wd[1]]).toNat
        = 2 ^ 32 - 1 - (2 ^ 32 - 1 - (ShiftRightMath.HWord.toBitVec32 #v[rs1[0], rs1[1]]).toNat)
            / 2 ^ (rs2[0].val % 32)) :
    Word.toBitVec64 Wd = RV64.sraw (Word.toBitVec64 rs2) (Word.toBitVec64 rs1) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨hr1_0, hr1_1, _, _⟩ := Word.lt_cases_of_isU64 h_rs1U
  rw [hword_toNat hr0 hr1, hword_toNat hr1_0 hr1_1] at hdiv
  have hlow : (BitVec.extractLsb' 0 32 (Word.toBitVec64 rs1)).toNat
      = rs1[0].val + rs1[1].val * 2 ^ 16 := by
    rw [BitVec.extractLsb'_toNat, Word.toBitVec64_toNat h_rs1U, Word.toNat_def,
        Nat.shiftRight_zero]; omega
  have hshamt : (BitVec.extractLsb' 0 5 (Word.toBitVec64 rs2)).toNat = rs2[0].val % 32 := by
    rw [BitVec.extractLsb'_toNat, Word.toBitVec64_toNat h_rs2U, Word.toNat_def,
        Nat.shiftRight_zero]; omega
  have hX : (BitVec.sshiftRight' (BitVec.extractLsb' 0 32 (Word.toBitVec64 rs1))
        (BitVec.extractLsb' 0 5 (Word.toBitVec64 rs2))).toNat = Wd[0].val + Wd[1].val * 2 ^ 16 := by
    rw [BitVec.sshiftRight_eq', BitVec.toNat_sshiftRight_of_msb_true h_msb,
        Nat.shiftRight_eq_div_pow, hlow, hshamt]; exact hdiv.symm
  rw [toBitVec64_signExtend_word Wd _ m hr0 hr1 hm hr2 hr3 hX]
  simp only [RV64.sraw, BitVec.extractLsb]

/-! ### Shift-count field-arithmetic bridges

Pure `ZMod p` identities/bounds on the `c_bits` shift-count columns, lifted out of the soundness
proof's per-variant preambles (they recur verbatim across SRL/SRA/SRLW/SRAW). No circuit context. -/

/-- The six-bit shift count `Σ cbᵢ·2^i` (each `cbᵢ` binary) has `val < 64` — the `is_mod_64`/`is_mod_32`
shift-count normalisation precondition. -/
lemma cbsum_val_lt_64 {cb0 cb1 cb2 cb3 cb4 cb5 : ZMod p}
    (b_cb0 : cb0 = 0 ∨ cb0 = 1) (b_cb1 : cb1 = 0 ∨ cb1 = 1)
    (b_cb2 : cb2 = 0 ∨ cb2 = 1) (b_cb3 : cb3 = 0 ∨ cb3 = 1)
    (b_cb4 : cb4 = 0 ∨ cb4 = 1) (b_cb5 : cb5 = 0 ∨ cb5 = 1) :
    (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32 : ZMod p).val < 64 := by
  have hcv := ShiftRightMath.cb_sum_val_eq b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
  have e0 : cb0.val ≤ 1 := by rcases b_cb0 with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have e1 : cb1.val ≤ 1 := by rcases b_cb1 with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have e2 : cb2.val ≤ 1 := by rcases b_cb2 with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have e3 : cb3.val ≤ 1 := by rcases b_cb3 with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have e4 : cb4.val ≤ 1 := by rcases b_cb4 with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have e5 : cb5.val ≤ 1 := by rcases b_cb5 with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  omega

set_option linter.unusedSectionVars false in
/-- Recast the four-bit byte-shift count `Σ cbᵢ·2^i` to the `((·:ℕ):ZMod p)`-cast form the
`srl_close_su16_*` exponents expect. -/
lemma cb4sum_natCast {cb0 cb1 cb2 cb3 : ZMod p} :
    (cb0 * 1 + cb1 * 2 + cb2 * 4 + cb3 * 8 : ZMod p)
      = cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8 := by push_cast; ring

set_option linter.unusedSectionVars false in
/-- The complement form of `cb4sum_natCast` (`16 - …`), for the higher-limb range bridges. -/
lemma cb4sum_sub_natCast {cb0 cb1 cb2 cb3 : ZMod p} :
    (16 + -(cb0 * 1 + cb1 * 2 + cb2 * 4 + cb3 * 8) : ZMod p)
      = 16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8) := by push_cast; ring

set_option linter.unusedSectionVars false in
/-- The `c_bits` shift-count bridge: rewrite the `is_mod_64` quotient `(c0 - Σ cbᵢ·2^i)·64⁻¹` into the
assert's `+ -(Σ cbᵢ·1·2^i)` form. -/
lemma c0mod_inv_bridge {c0 cb0 cb1 cb2 cb3 cb4 cb5 : ZMod p} :
    (c0 - (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32) : ZMod p) * (64 : ZMod p)⁻¹
      = (c0 + -(cb0 * 1 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32)) * (64 : ZMod p)⁻¹ := by
  ring

end SP1Clean.ShiftRightChip
