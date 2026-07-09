import SP1Clean.Proofs.Chips.DivRemChip.Extract

/-! # `DivRemChip` — per-family soundness assembly

One "core" lemma per RV64 division family: consumes the carry-chain limb equations, the two
`MulOperation` product words, the `isU64`s, the remainder range, and the divide-by-zero /
overflow branches, and concludes the family's quotient + remainder RV64 identity pair. Stated
over loose Words; `Formal.lean` does the offset bookkeeping and routes `.1`/`.2` to `cols.a`. -/

namespace SP1Clean.DivRemChip

open SP1Clean

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- **Unsigned family core (`DIVU`/`REMU`).** From the eight unsigned carry-chain limb equations (on
the `mul_lower`/`mul_upper` result words `rwlo`/`rwhi`, non-overflow branch with sign fills `0`), the
two Mul product forms, the remainder range, and the divide-by-zero branch, the quotient column is
`RV64.divu` and the remainder column is `RV64.remu`. Wraps `hid_of_carry_chain` (the ℕ Euclidean
identity) into `Math.divu_remu_of_identity`. -/
lemma assemble_unsigned {b c quotient remainder rwlo rwhi : Word (ZMod p)} {carry : Vector (ZMod p) 8}
    (hcU : c.isU64) (hbU : b.isU64) (hqU : quotient.isU64) (hrU : remainder.isU64)
    (hloU : rwlo.isU64) (hhiU : rwhi.isU64)
    (hc0 : carry[0] = 0 ∨ carry[0] = 1) (hc1 : carry[1] = 0 ∨ carry[1] = 1)
    (hc2 : carry[2] = 0 ∨ carry[2] = 1) (hc3 : carry[3] = 0 ∨ carry[3] = 1)
    (hc4 : carry[4] = 0 ∨ carry[4] = 1) (hc5 : carry[5] = 0 ∨ carry[5] = 1)
    (hc6 : carry[6] = 0 ∨ carry[6] = 1) (hc7 : carry[7] = 0 ∨ carry[7] = 1)
    (hl0 : rwlo[0] + remainder[0] = b[0] + carry[0] * 65536)
    (hl1 : rwlo[1] + remainder[1] + carry[0] = b[1] + carry[1] * 65536)
    (hl2 : rwlo[2] + remainder[2] + carry[1] = b[2] + carry[2] * 65536)
    (hl3 : rwlo[3] + remainder[3] + carry[2] = b[3] + carry[3] * 65536)
    (hh4 : rwhi[0] + carry[3] = carry[4] * 65536)
    (hh5 : rwhi[1] + carry[4] = carry[5] * 65536)
    (hh6 : rwhi[2] + carry[5] = carry[6] * 65536)
    (hh7 : rwhi[3] + carry[6] = carry[7] * 65536)
    (hlo : rwlo.toBitVec64 = quotient.toBitVec64 * c.toBitVec64)
    (hhi : rwhi.toBitVec64
        = (((quotient.toBitVec64).setWidth 128 * (c.toBitVec64).setWidth 128) >>> 64).setWidth 64)
    (hlt : c.toNat ≠ 0 → remainder.toNat < c.toNat)
    (hzero : c.toNat = 0 → quotient.toNat = 2 ^ 64 - 1 ∧ remainder.toNat = b.toNat) :
    quotient.toBitVec64 = RV64.divu c.toBitVec64 b.toBitVec64 ∧
    remainder.toBitVec64 = RV64.remu c.toBitVec64 b.toBitVec64 := by
  have hid := hid_of_carry_chain hcU hbU hqU hrU hloU hhiU hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
    hl0 hl1 hl2 hl3 hh4 hh5 hh6 hh7 hlo hhi
  exact divu_remu_of_identity hbU hcU hqU hrU hid hlt hzero

omit [Fact p.Prime] in
/-- **Signed family core, normal (non-overflow, nonzero-divisor) case (`DIV`/`REM`).** The signed
Euclidean identity (from `euclid_identity_signed`), the abs-column remainder range (`hlt_signed_of_abs`),
and the sign conditions (`sign_conditions`) feed `Math.div_rem_of_identity`: the quotient column is
`RV64.div` and the remainder column is `RV64.rem`. The `hid` is stated in the `quotient · c` order the
signed bridge produces; `div_rem_of_identity` wants `c · quotient`, bridged by `ring`. -/
lemma assemble_signed_normal {b c quotient remc : Word (ZMod p)}
    (hc0 : c.toBitVec64 ≠ 0#64)
    (hid : b.toBitVec64.toInt
        = quotient.toBitVec64.toInt * c.toBitVec64.toInt + remc.toBitVec64.toInt)
    (hlt : remc.toBitVec64.toInt.natAbs < c.toBitVec64.toInt.natAbs)
    (hsgn_pos : 0 ≤ b.toBitVec64.toInt → 0 ≤ remc.toBitVec64.toInt)
    (hsgn_neg : b.toBitVec64.toInt ≤ 0 → remc.toBitVec64.toInt ≤ 0) :
    quotient.toBitVec64 = RV64.div c.toBitVec64 b.toBitVec64 ∧
    remc.toBitVec64 = RV64.rem c.toBitVec64 b.toBitVec64 :=
  div_rem_of_identity hc0 (by rw [hid]; ring) hlt hsgn_pos hsgn_neg

omit [Fact p.Prime] in
/-- **Unsigned word family core (`DIVUW`/`REMUW`).** The 64-bit Euclidean identity over the (zero-high)
operand/comp columns is exactly the 32-bit identity (`extractLsb_toNat_of_hi_zero` on all four words),
so it feeds `Math.divuw_remuw_of_identity`. The conclusion is on the sign-extension of the comp columns'
low 32 — `Formal` bridges those to the output column via `word_eq_signExtend_lo` + `extractLsb_lo_congr`.
`hzero`'s quotient value is `2^32 − 1` (the *low-32* all-ones; the comp column zero-extends it). -/
lemma assemble_unsigned_word {b c qc rc : Word (ZMod p)}
    (hbU : b.isU64) (hcU : c.isU64) (hqU : qc.isU64) (hrU : rc.isU64)
    (hb2 : b[2] = 0) (hb3 : b[3] = 0) (hc2 : c[2] = 0) (hc3 : c[3] = 0)
    (hq2 : qc[2] = 0) (hq3 : qc[3] = 0) (hr2 : rc[2] = 0) (hr3 : rc[3] = 0)
    (hid : b.toNat = c.toNat * qc.toNat + rc.toNat)
    (hlt : c.toNat ≠ 0 → rc.toNat < c.toNat)
    (hzero : c.toNat = 0 → qc.toNat = 2 ^ 32 - 1 ∧ rc.toNat = b.toNat) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 qc.toBitVec64) = RV64.divuw c.toBitVec64 b.toBitVec64 ∧
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 rc.toBitVec64) = RV64.remuw c.toBitVec64 b.toBitVec64 := by
  refine divuw_remuw_of_identity (q32 := BitVec.extractLsb 31 0 qc.toBitVec64)
    (r32 := BitVec.extractLsb 31 0 rc.toBitVec64) ?_ ?_ ?_
  · rw [extractLsb_toNat_of_hi_zero hbU hb2 hb3, extractLsb_toNat_of_hi_zero hcU hc2 hc3,
        extractLsb_toNat_of_hi_zero hqU hq2 hq3, extractLsb_toNat_of_hi_zero hrU hr2 hr3]
    exact hid
  · rw [extractLsb_toNat_of_hi_zero hcU hc2 hc3, extractLsb_toNat_of_hi_zero hrU hr2 hr3]
    exact hlt
  · rw [extractLsb_toNat_of_hi_zero hcU hc2 hc3, extractLsb_toNat_of_hi_zero hqU hq2 hq3,
        extractLsb_toNat_of_hi_zero hbU hb2 hb3, extractLsb_toNat_of_hi_zero hrU hr2 hr3]
    exact hzero

omit [Fact p.Prime] in
/-- **Signed word family core, normal case (`DIVW`/`REMW`).** The 64-bit signed Euclidean identity over
the (sign-filled) operand/comp columns is exactly the 32-bit `toInt` identity (`toInt_eq_extractLsb_of_signfill`
on all four), so it feeds `Math.divw_remw_of_identity`. The divide-by-zero / overflow branches use the
`Math.divw_remw_divzero`/`_overflow` consumers directly in `Formal`. -/
lemma assemble_signed_word_normal {b c qc rc : Word (ZMod p)}
    (hbU : b.isU64) (hcU : c.isU64) (hqU : qc.isU64) (hrU : rc.isU64)
    (hbf2 : b[2].val = (if 32768 ≤ b[1].val then 65535 else 0))
    (hbf3 : b[3].val = (if 32768 ≤ b[1].val then 65535 else 0))
    (hcf2 : c[2].val = (if 32768 ≤ c[1].val then 65535 else 0))
    (hcf3 : c[3].val = (if 32768 ≤ c[1].val then 65535 else 0))
    (hqf2 : qc[2].val = (if 32768 ≤ qc[1].val then 65535 else 0))
    (hqf3 : qc[3].val = (if 32768 ≤ qc[1].val then 65535 else 0))
    (hrf2 : rc[2].val = (if 32768 ≤ rc[1].val then 65535 else 0))
    (hrf3 : rc[3].val = (if 32768 ≤ rc[1].val then 65535 else 0))
    (hc0 : BitVec.extractLsb 31 0 c.toBitVec64 ≠ 0#32)
    (hid : b.toBitVec64.toInt
        = qc.toBitVec64.toInt * c.toBitVec64.toInt + rc.toBitVec64.toInt)
    (hlt : rc.toBitVec64.toInt.natAbs < c.toBitVec64.toInt.natAbs)
    (hsgn_pos : 0 ≤ b.toBitVec64.toInt → 0 ≤ rc.toBitVec64.toInt)
    (hsgn_neg : b.toBitVec64.toInt ≤ 0 → rc.toBitVec64.toInt ≤ 0) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 qc.toBitVec64) = RV64.divw c.toBitVec64 b.toBitVec64 ∧
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 rc.toBitVec64) = RV64.remw c.toBitVec64 b.toBitVec64 := by
  have hbp := toInt_eq_extractLsb_of_signfill hbU hbf2 hbf3
  have hcp := toInt_eq_extractLsb_of_signfill hcU hcf2 hcf3
  have hqp := toInt_eq_extractLsb_of_signfill hqU hqf2 hqf3
  have hrp := toInt_eq_extractLsb_of_signfill hrU hrf2 hrf3
  refine divw_remw_of_identity (q32 := BitVec.extractLsb 31 0 qc.toBitVec64)
    (r32 := BitVec.extractLsb 31 0 rc.toBitVec64) hc0 ?_ ?_ ?_ ?_
  · rw [← hbp, ← hcp, ← hqp, ← hrp, hid]; ring
  · rw [← hcp, ← hrp]; exact hlt
  · rw [← hbp, ← hrp]; exact hsgn_pos
  · rw [← hbp, ← hrp]; exact hsgn_neg

end SP1Clean.DivRemChip
