import SP1Clean.Math.Word
import RISCV.Instructions
import Mathlib.Tactic.Linarith

/-! # `DivRemChip` — native divide/remainder arithmetic

The mathematical core of the `DivRem` chip soundness (chip-specific math in `Chips/<Op>Chip/`,
reusable gadgets in `Operations/`). Re-derives from first principles in `Word`/`toBitVec64` forms
the bridge from SP1's constraint bundle to the RV64 divide/remainder ISA functions
(`RISCV/Instructions.lean`).

**Unsigned variants (`DIVU`/`REMU`):** `divu_remu_of_identity` takes the three hypotheses supplied
by the chip soundness — the Euclidean identity `b = c·quotient + remainder` (from the two
`MulOperation`s + `carry`/`c_times_quotient` columns), the remainder range (`remainder < c` when
`c ≠ 0`, from `remainder_lt_operation`), and the divide-by-zero branch (`c = 0 → quotient`
all-ones `∧ remainder = b`, from `is_c_0`). The signed and word variants follow in §§2–3. -/

namespace SP1Clean.DivRemChip

variable {p : ℕ} [NeZero p]

/-- A 64-bit word's little-endian value is `< 2^64`. -/
lemma toNat_lt_2_64 {w : Word (ZMod p)} (hw : w.isU64) : w.toNat < 2 ^ 64 := by
  obtain ⟨h0, h1, h2, h3⟩ := Word.lt_cases_of_isU64 hw
  rw [Word.toNat_def]; omega

/-- Euclidean-division uniqueness over `ℕ`: `b = c·q + r` with `r < c` pins `q`/`r` to `b / c` and
`b % c`. Shared by `divu_remu_spec` (on the `ℕ` operands) and `udiv_umod_bitvec` (on their
`toNat`). -/
private lemma div_mod_of_euclid {b c q r : ℕ} (hcpos : 0 < c) (hid : b = c * q + r) (hlt : r < c) :
    q = b / c ∧ r = b % c :=
  ⟨by rw [hid, Nat.mul_add_div hcpos, Nat.div_eq_of_lt hlt]; omega,
   by rw [hid, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]⟩

/-- **Unsigned divide/remainder core (over `ℕ`).** Given the Euclidean identity `b = c·q + r`, the
remainder range `r < c` (when `c ≠ 0`), and SP1's divide-by-zero convention (`c = 0` forces the
quotient to all-ones `2^64 - 1` and the remainder to `b`), the 64-bit quotient is `RV64.divu` and the
remainder is `RV64.remu` of the operands. Operand order matches the RV64 signature `f rs2 rs1` with
`rs2 = c` (divisor), `rs1 = b` (dividend): `divu` is `if c = 0 then -1 else b.udiv c`, `remu` is
`b.umod c` (and `umod` by `0` is the dividend, matching the `c = 0 → r = b` convention). -/
theorem divu_remu_spec {b c q r : ℕ}
    (hb : b < 2 ^ 64) (hc : c < 2 ^ 64) (hq : q < 2 ^ 64) (hr : r < 2 ^ 64)
    (hid : b = c * q + r)
    (hlt : c ≠ 0 → r < c)
    (hzero : c = 0 → q = 2 ^ 64 - 1 ∧ r = b) :
    BitVec.ofNat 64 q = RV64.divu (BitVec.ofNat 64 c) (BitVec.ofNat 64 b) ∧
    BitVec.ofNat 64 r = RV64.remu (BitVec.ofNat 64 c) (BitVec.ofNat 64 b) := by
  have hbt : (BitVec.ofNat 64 b).toNat = b := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hb
  have hct : (BitVec.ofNat 64 c).toNat = c := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hc
  unfold RV64.divu RV64.remu
  by_cases hc0 : c = 0
  · subst hc0
    obtain ⟨hqv, hrv⟩ := hzero rfl
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, if_pos rfl]
    subst hrv
    exact ⟨by subst hqv; rfl, BitVec.eq_of_toNat_eq (by simp [BitVec.umod, hbt, hct])⟩
  · have hcne : BitVec.ofNat 64 c ≠ 0#64 := fun h => hc0 (by rw [← hct, h]; simp)
    rw [if_neg hcne]
    obtain ⟨hqdiv, hrmod⟩ := div_mod_of_euclid (Nat.pos_of_ne_zero hc0) hid (hlt hc0)
    refine ⟨BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_⟩
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq, hqdiv]; simp [BitVec.udiv, hbt, hct]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr, hrmod]; simp [BitVec.umod, hbt, hct]

/-- **Unsigned divide/remainder core (over `Word`).** The `divu_remu_spec` bridge phrased on the chip's
`Word` columns: the quotient column's `toBitVec64` is `RV64.divu` and the remainder column's is
`RV64.remu` of the operand words. This is the exact shape the chip soundness feeds into the `is_divu`/
`is_remu` conjuncts of the `Spec` (with `b = op_b_val`, `c = op_c_val`). -/
theorem divu_remu_of_identity {b c quotient remainder : Word (ZMod p)}
    (hb : b.isU64) (hc : c.isU64) (hq : quotient.isU64) (hr : remainder.isU64)
    (hid : b.toNat = c.toNat * quotient.toNat + remainder.toNat)
    (hlt : c.toNat ≠ 0 → remainder.toNat < c.toNat)
    (hzero : c.toNat = 0 → quotient.toNat = 2 ^ 64 - 1 ∧ remainder.toNat = b.toNat) :
    quotient.toBitVec64 = RV64.divu c.toBitVec64 b.toBitVec64 ∧
    remainder.toBitVec64 = RV64.remu c.toBitVec64 b.toBitVec64 :=
  divu_remu_spec (toNat_lt_2_64 hb) (toNat_lt_2_64 hc) (toNat_lt_2_64 hq) (toNat_lt_2_64 hr)
    hid hlt hzero

/-! ## Signed variants `DIV`/`REM`

`RV64.div`/`RV64.rem` are **truncated** (round-toward-zero) signed division on the operands'
`toInt`: `BitVec.toInt_sdiv`/`toInt_srem` characterize them as `Int.tdiv`/`Int.tmod` (the `sdiv`
case carries a `.bmod 2^64` that absorbs the lone `i64::MIN / -1` overflow). SP1 computes the same
result through absolute values with sign corrections; the bridge below is stated at the `BitVec`
level (the soundness applies it to `Word.toBitVec64` of the columns) and splits into the three cases
SP1's flags gate: the normal Euclidean case, divide-by-zero (`is_c_0`), and signed overflow
(`is_overflow`). The normal case is plain truncated-division uniqueness (`Int.tdiv_tmod_unique`);
the two special cases are direct `BitVec` identities. Operand order is `f rs2 rs1` with `rs2 = c`,
`rs1 = b`. -/

/-- **Signed divide/remainder core (normal case, width-generic `sdiv`/`srem` form).** When the divisor
is nonzero and the signed Euclidean identity `b = c·q + r` holds with `|r| < |c|` and the remainder
carrying the dividend's sign, the quotient is `b.sdiv c` and the remainder is `b.srem c`. Stated for
any width `w` (used at `w = 64` for `DIV`/`REM` and at `w = 32` for `DIVW`/`REMW`). Truncated-division
uniqueness (`Int.tdiv_tmod_unique`); the quotient's `toInt` is already in range so the `sdiv` `bmod`
cancels (`BitVec.toInt_bmod_cancel`) — overflow cannot satisfy these hypotheses. -/
theorem sdiv_srem_bitvec {w : ℕ} {b c q r : BitVec w}
    (hc0 : c ≠ 0#w)
    (hid : b.toInt = c.toInt * q.toInt + r.toInt)
    (hlt : r.toInt.natAbs < c.toInt.natAbs)
    (hsgn_pos : 0 ≤ b.toInt → 0 ≤ r.toInt)
    (hsgn_neg : b.toInt ≤ 0 → r.toInt ≤ 0) :
    q = b.sdiv c ∧ r = b.srem c := by
  have hcz : c.toInt ≠ 0 := fun h => hc0 (BitVec.eq_of_toInt_eq (by rw [h]; simp))
  have key : b.toInt.tdiv c.toInt = q.toInt ∧ b.toInt.tmod c.toInt = r.toInt := by
    rcases le_total 0 b.toInt with hb | hb
    · rw [Int.tdiv_tmod_unique hb hcz]; exact ⟨by linarith, hsgn_pos hb, by omega⟩
    · rw [Int.tdiv_tmod_unique' hb hcz]; exact ⟨by linarith, by omega, hsgn_neg hb⟩
  obtain ⟨hq, hr⟩ := key
  exact ⟨BitVec.eq_of_toInt_eq (by rw [BitVec.toInt_sdiv, hq, BitVec.toInt_bmod_cancel]),
         BitVec.eq_of_toInt_eq (by rw [BitVec.toInt_srem, hr])⟩

/-- **Signed divide/remainder (normal case, RV64 form).** As `sdiv_srem_bitvec` at width 64, but
concluding the `RV64.div`/`RV64.rem` ISA functions directly (`RV64.div` is `b.sdiv c` for a nonzero
divisor; `RV64.rem` is `b.srem c` definitionally). This is the consumer the chip soundness feeds for
the `is_div`/`is_rem` conjuncts on non-overflow real rows. -/
theorem div_rem_of_identity {b c quotient remainder : BitVec 64}
    (hc0 : c ≠ 0#64)
    (hid : b.toInt = c.toInt * quotient.toInt + remainder.toInt)
    (hlt : remainder.toInt.natAbs < c.toInt.natAbs)
    (hsgn_pos : 0 ≤ b.toInt → 0 ≤ remainder.toInt)
    (hsgn_neg : b.toInt ≤ 0 → remainder.toInt ≤ 0) :
    quotient = RV64.div c b ∧ remainder = RV64.rem c b := by
  obtain ⟨hq, hr⟩ := sdiv_srem_bitvec hc0 hid hlt hsgn_pos hsgn_neg
  exact ⟨by rw [hq]; unfold RV64.div; rw [if_neg hc0], hr⟩

/-- **Signed divide-by-zero.** SP1's `is_c_0` branch forces the quotient to all-ones (`-1`) and the
remainder to the dividend; that matches `RV64.div` (the `c = 0` case returns `-1`) and `RV64.rem`
(`srem` by `0` is the dividend). -/
theorem div_rem_divzero {b c quotient remainder : BitVec 64}
    (hc : c = 0#64) (hq : quotient = -1#64) (hr : remainder = b) :
    quotient = RV64.div c b ∧ remainder = RV64.rem c b := by
  subst hc hq hr
  exact ⟨by unfold RV64.div; rw [if_pos rfl], by unfold RV64.rem; rw [BitVec.srem_zero]⟩

/-- `-1` divides everything, so a signed remainder by `-1` is `0`. The width hypothesis
`(-1#w).toInt = -1` is `by decide` at each concrete width. Shared by the 64-bit and 32-bit
signed-overflow arms. -/
private lemma srem_neg_one_eq_zero {w : ℕ} (h : (-1#w : BitVec w).toInt = -1) (x : BitVec w) :
    x.srem (-1#w) = 0#w :=
  BitVec.srem_zero_of_dvd (by rw [h]; exact neg_dvd.mpr (one_dvd _))

/-- **Signed overflow** (`b = i64::MIN`, `c = -1`). SP1's `is_overflow` branch forces the quotient to
the dividend and the remainder to `0`; that matches `RV64.div` (`i64::MIN.sdiv (-1) = i64::MIN`) and
`RV64.rem` (`-1` divides everything, so the remainder is `0`). -/
theorem div_rem_overflow {b c quotient remainder : BitVec 64}
    (hb : b = BitVec.intMin 64) (hc : c = -1#64) (hq : quotient = b) (hr : remainder = 0#64) :
    quotient = RV64.div c b ∧ remainder = RV64.rem c b := by
  subst hc hq hr hb
  refine ⟨by unfold RV64.div; rw [if_neg (by decide), BitVec.intMin_sdiv_neg_one], ?_⟩
  unfold RV64.rem
  exact (srem_neg_one_eq_zero (by decide) _).symm

/-! ## Word variants `DIVW`/`REMW`/`DIVUW`/`REMUW`

The `*w` instructions operate on the **low 32 bits** of the operands (`BitVec.extractLsb 31 0`) and
`signExtend` the 32-bit result back to 64. So the arithmetic is the *same core* at width 32, wrapped
in a sign extension. The unsigned word core `udiv_umod_bitvec` is width-generic (the `DIVUW`'s
`if c = 0 then -1` divide-by-zero is folded into its conclusion, so `DIVUW`/`REMUW` need a single
lemma); the signed word variants reuse `sdiv_srem_bitvec` at width 32 and split into the same three
flag-gated cases as `DIV`/`REM`. -/

/-- **Unsigned divide/remainder core (width-generic, `BitVec` form).** The Euclidean identity over
`toNat` with the remainder range and SP1's all-ones divide-by-zero convention pins the quotient to the
`if c = 0 then -1 else b.udiv c` form and the remainder to `b.umod c`, at any width `w` (used at
`w = 32` for `DIVUW`/`REMUW`). Parallel to `divu_remu_spec` but stated on `BitVec` operands directly. -/
theorem udiv_umod_bitvec {w : ℕ} {b c q r : BitVec w}
    (hid : b.toNat = c.toNat * q.toNat + r.toNat)
    (hlt : c.toNat ≠ 0 → r.toNat < c.toNat)
    (hzero : c.toNat = 0 → q.toNat = 2 ^ w - 1 ∧ r.toNat = b.toNat) :
    q = (if c = 0#w then -1#w else b.udiv c) ∧ r = b.umod c := by
  by_cases hc0 : c = 0#w
  · have hcz : c.toNat = 0 := by rw [hc0]; simp
    obtain ⟨hqv, hrv⟩ := hzero hcz
    rw [if_pos hc0]
    refine ⟨BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_⟩
    · rw [hqv, BitVec.neg_one_eq_allOnes]; exact BitVec.toNat_allOnes.symm
    · rw [hrv, hc0]; simp [BitVec.umod]
  · have hcz : c.toNat ≠ 0 := fun h => hc0 (BitVec.eq_of_toNat_eq (by rw [h]; simp))
    rw [if_neg hc0]
    obtain ⟨hqdiv, hrmod⟩ := div_mod_of_euclid (Nat.pos_of_ne_zero hcz) hid (hlt hcz)
    exact ⟨BitVec.eq_of_toNat_eq (by rw [hqdiv]; simp [BitVec.udiv]),
           BitVec.eq_of_toNat_eq (by rw [hrmod]; simp [BitVec.umod])⟩

/-- **Unsigned word `DIVUW`/`REMUW`.** The 32-bit unsigned core on the low halves of the operands,
sign-extended to 64 — exactly `RV64.divuw`/`RV64.remuw`. A single lemma (no separate overflow case;
unsigned division cannot overflow). The hypotheses are on the low-32-bit values
`BitVec.extractLsb 31 0 b/c` of the operands, which is what `RV64.*uw` extract. -/
theorem divuw_remuw_of_identity {b c : BitVec 64} {q32 r32 : BitVec 32}
    (hid : (BitVec.extractLsb 31 0 b).toNat
        = (BitVec.extractLsb 31 0 c).toNat * q32.toNat + r32.toNat)
    (hlt : (BitVec.extractLsb 31 0 c).toNat ≠ 0 →
        r32.toNat < (BitVec.extractLsb 31 0 c).toNat)
    (hzero : (BitVec.extractLsb 31 0 c).toNat = 0 →
        q32.toNat = 2 ^ 32 - 1 ∧ r32.toNat = (BitVec.extractLsb 31 0 b).toNat) :
    BitVec.signExtend 64 q32 = RV64.divuw c b ∧ BitVec.signExtend 64 r32 = RV64.remuw c b := by
  obtain ⟨hq, hr⟩ := udiv_umod_bitvec hid hlt hzero
  exact ⟨by unfold RV64.divuw; rw [hq], by unfold RV64.remuw; rw [hr]⟩

/-- **Signed word `DIVW`/`REMW`, normal case.** The 32-bit signed core (`sdiv_srem_bitvec` at width
32) on the low halves, sign-extended — `RV64.divw`/`RV64.remw` on a nonzero (low-32) divisor. -/
theorem divw_remw_of_identity {b c : BitVec 64} {q32 r32 : BitVec 32}
    (hc0 : BitVec.extractLsb 31 0 c ≠ 0#32)
    (hid : (BitVec.extractLsb 31 0 b).toInt
        = (BitVec.extractLsb 31 0 c).toInt * q32.toInt + r32.toInt)
    (hlt : r32.toInt.natAbs < (BitVec.extractLsb 31 0 c).toInt.natAbs)
    (hsgn_pos : 0 ≤ (BitVec.extractLsb 31 0 b).toInt → 0 ≤ r32.toInt)
    (hsgn_neg : (BitVec.extractLsb 31 0 b).toInt ≤ 0 → r32.toInt ≤ 0) :
    BitVec.signExtend 64 q32 = RV64.divw c b ∧ BitVec.signExtend 64 r32 = RV64.remw c b := by
  obtain ⟨hq, hr⟩ := sdiv_srem_bitvec hc0 hid hlt hsgn_pos hsgn_neg
  exact ⟨by simp only [RV64.divw]; rw [if_neg hc0, hq], by simp only [RV64.remw]; rw [hr]⟩

/-- **Signed word `DIVW`/`REMW`, divide-by-zero.** Low-32 divisor zero ⇒ quotient all-ones, remainder
the (low-32) dividend, sign-extended. -/
theorem divw_remw_divzero {b c : BitVec 64} {q32 r32 : BitVec 32}
    (hc : BitVec.extractLsb 31 0 c = 0#32) (hq : q32 = -1#32)
    (hr : r32 = BitVec.extractLsb 31 0 b) :
    BitVec.signExtend 64 q32 = RV64.divw c b ∧ BitVec.signExtend 64 r32 = RV64.remw c b := by
  subst hq hr
  exact ⟨by simp only [RV64.divw]; rw [if_pos hc], by simp only [RV64.remw]; rw [hc, BitVec.srem_zero]⟩

/-- **Signed word `DIVW`/`REMW`, overflow** (`i32::MIN / -1` on the low halves). -/
theorem divw_remw_overflow {b c : BitVec 64} {q32 r32 : BitVec 32}
    (hb : BitVec.extractLsb 31 0 b = BitVec.intMin 32) (hc : BitVec.extractLsb 31 0 c = -1#32)
    (hq : q32 = BitVec.extractLsb 31 0 b) (hr : r32 = 0#32) :
    BitVec.signExtend 64 q32 = RV64.divw c b ∧ BitVec.signExtend 64 r32 = RV64.remw c b := by
  subst hq hr
  exact ⟨by simp only [RV64.divw]; rw [hb, hc, if_neg (by decide), BitVec.intMin_sdiv_neg_one],
         by simp only [RV64.remw]; rw [hc, srem_neg_one_eq_zero (by decide)]⟩

end SP1Clean.DivRemChip
