import SP1Clean.Proofs.Chips.DivRemChip.Math
import SP1Clean.Math.Word

/-! # `DivRemChip` — soundness bridge lemmas

Carry-chain → ℕ/Int reassembly lemmas bridging the chip's composed sub-circuit `Spec`s + `ownAsserts`
to the pure-arithmetic consumers in `Math.lean`. Kept separate so each bridge lemma is independently
checkable and `Formal.lean` reads as a thin assembly. -/

namespace SP1Clean.DivRemChip

open SP1Clean

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance neZeroP_soundness : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

set_option maxHeartbeats 4000000 in
/-- **Unsigned carry-chain reassembly.** The chip pins `c·quotient + remainder = b` through an
eight-limb base-`2^16` carry chain. On the unsigned, non-overflow branch the high four limbs carry no
sign fill (`b_neg = rem_neg = 0`), so the eight limb equations are:

* low (i=0..3): `ctq[i] + rem[i] + carry[i-1] = b[i] + carry[i]·2^16` (with `carry[-1] := 0`);
* high (i=4..7): `ctq[i] + carry[i-1] = carry[i]·2^16`.

Given the limbs are 16-bit, the carries are boolean, and the eight `ctq` limbs reassemble (base `2^16`)
to the 128-bit product `c·quotient` (with `c, quotient < 2^64`), the low 64 bits telescope to the
Euclidean identity `b.toNat = c·quotient + remainder.toNat`. The top carry is forced to `0` because the
product `c·quotient ≤ (2^64-1)^2 < 2^128 - 2^64`, so its high half can never reach the `2^64 - 1` that a
nonzero top carry would require. -/
lemma euclid_identity_unsigned
    {ctq carry : Vector (ZMod p) 8} {rem b : Word (ZMod p)} {qn cn : ℕ}
    (hv0 : (ctq[0]).val < 2 ^ 16) (hv1 : (ctq[1]).val < 2 ^ 16) (hv2 : (ctq[2]).val < 2 ^ 16)
    (hv3 : (ctq[3]).val < 2 ^ 16) (hv4 : (ctq[4]).val < 2 ^ 16) (hv5 : (ctq[5]).val < 2 ^ 16)
    (hv6 : (ctq[6]).val < 2 ^ 16) (hv7 : (ctq[7]).val < 2 ^ 16)
    (hrem : rem.isU64) (hb : b.isU64)
    (hc0 : carry[0] = 0 ∨ carry[0] = 1) (hc1 : carry[1] = 0 ∨ carry[1] = 1)
    (hc2 : carry[2] = 0 ∨ carry[2] = 1) (hc3 : carry[3] = 0 ∨ carry[3] = 1)
    (hc4 : carry[4] = 0 ∨ carry[4] = 1) (hc5 : carry[5] = 0 ∨ carry[5] = 1)
    (hc6 : carry[6] = 0 ∨ carry[6] = 1) (hc7 : carry[7] = 0 ∨ carry[7] = 1)
    (hl0 : ctq[0] + rem[0] = b[0] + carry[0] * 65536)
    (hl1 : ctq[1] + rem[1] + carry[0] = b[1] + carry[1] * 65536)
    (hl2 : ctq[2] + rem[2] + carry[1] = b[2] + carry[2] * 65536)
    (hl3 : ctq[3] + rem[3] + carry[2] = b[3] + carry[3] * 65536)
    (hh4 : ctq[4] + carry[3] = carry[4] * 65536)
    (hh5 : ctq[5] + carry[4] = carry[5] * 65536)
    (hh6 : ctq[6] + carry[5] = carry[6] * 65536)
    (hh7 : ctq[7] + carry[6] = carry[7] * 65536)
    (hprod : (ctq[0]).val + (ctq[1]).val * 65536 + (ctq[2]).val * 65536 ^ 2
        + (ctq[3]).val * 65536 ^ 3 + (ctq[4]).val * 65536 ^ 4 + (ctq[5]).val * 65536 ^ 5
        + (ctq[6]).val * 65536 ^ 6 + (ctq[7]).val * 65536 ^ 7 = cn * qn)
    (hqn : qn < 2 ^ 64) (hcn : cn < 2 ^ 64) :
    b.toNat = cn * qn + rem.toNat := by
  haveI : Fact (Nat.Prime p) := ‹Fact p.Prime›
  haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨r0, r1, r2, r3⟩ := Word.lt_cases_of_isU64 hrem
  obtain ⟨b0, b1, b2, b3⟩ := Word.lt_cases_of_isU64 hb
  -- lift each ZMod limb equation to ℕ via `Word.limb_lift` (the high limbs have `vv = aa = 0`).
  have L0 := limb_lift ctq[0] rem[0] b[0] 0 carry[0] hv0 r0 b0 (Or.inl rfl) hc0
    (by rw [add_zero]; exact hl0)
  have L1 := limb_lift ctq[1] rem[1] b[1] carry[0] carry[1] hv1 r1 b1 hc0 hc1 hl1
  have L2 := limb_lift ctq[2] rem[2] b[2] carry[1] carry[2] hv2 r2 b2 hc1 hc2 hl2
  have L3 := limb_lift ctq[3] rem[3] b[3] carry[2] carry[3] hv3 r3 b3 hc2 hc3 hl3
  have H4 := limb_lift ctq[4] 0 0 carry[3] carry[4] hv4 (by simp) (by simp) hc3 hc4
    (by rw [add_zero, zero_add]; exact hh4)
  have H5 := limb_lift ctq[5] 0 0 carry[4] carry[5] hv5 (by simp) (by simp) hc4 hc5
    (by rw [add_zero, zero_add]; exact hh5)
  have H6 := limb_lift ctq[6] 0 0 carry[5] carry[6] hv6 (by simp) (by simp) hc5 hc6
    (by rw [add_zero, zero_add]; exact hh6)
  have H7 := limb_lift ctq[7] 0 0 carry[6] carry[7] hv7 (by simp) (by simp) hc6 hc7
    (by rw [add_zero, zero_add]; exact hh7)
  simp only [ZMod.val_zero] at L0 H4 H5 H6 H7
  -- carry `.val ≤ 1`.
  have C0 : (carry[0]).val ≤ 1 := by rcases hc0 with h | h <;> rw [h] <;> simp [ZMod.val_one]
  have C1 : (carry[1]).val ≤ 1 := by rcases hc1 with h | h <;> rw [h] <;> simp [ZMod.val_one]
  have C2 : (carry[2]).val ≤ 1 := by rcases hc2 with h | h <;> rw [h] <;> simp [ZMod.val_one]
  have C3 : (carry[3]).val ≤ 1 := by rcases hc3 with h | h <;> rw [h] <;> simp [ZMod.val_one]
  have C4 : (carry[4]).val ≤ 1 := by rcases hc4 with h | h <;> rw [h] <;> simp [ZMod.val_one]
  have C5 : (carry[5]).val ≤ 1 := by rcases hc5 with h | h <;> rw [h] <;> simp [ZMod.val_one]
  have C6 : (carry[6]).val ≤ 1 := by rcases hc6 with h | h <;> rw [h] <;> simp [ZMod.val_one]
  have C7 : (carry[7]).val ≤ 1 := by rcases hc7 with h | h <;> rw [h] <;> simp [ZMod.val_one]
  -- the product is bounded by `(2^64-1)^2`, ruling out the top carry.
  have hpb : cn * qn ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  rw [Word.toNat_def, Word.toNat_def]
  -- linear in limb `.val`s; telescope + rule out the top carry.
  omega

omit [Fact p.Prime] in
/-- **Product low/high reassembly.** The two `MulOperation` sub-circuits expose the low 64 bits
(`is_mul`) and the high 64 bits (`is_mulhu`, unsigned) of the 128-bit product `quotient_comp · c` as
their result words `rwlo`/`rwhi`. Concatenating them recovers the full product over `ℕ`:
`rwlo.toNat + rwhi.toNat · 2^64 = qc.toNat · c.toNat`. This supplies the `hprod` hypothesis of
`euclid_identity_unsigned` (with `qc = quotient_comp`). -/
lemma prod_lo_hi_reassembly {qc c rwlo rwhi : Word (ZMod p)}
    (hqcU : qc.isU64) (hcU : c.isU64) (hloU : rwlo.isU64) (hhiU : rwhi.isU64)
    (hlo : rwlo.toBitVec64 = qc.toBitVec64 * c.toBitVec64)
    (hhi : rwhi.toBitVec64
        = (((qc.toBitVec64).setWidth 128 * (c.toBitVec64).setWidth 128) >>> 64).setWidth 64) :
    rwlo.toNat + rwhi.toNat * 2 ^ 64 = qc.toNat * c.toNat := by
  have hq64 : qc.toNat < 2 ^ 64 := toNat_lt_2_64 hqcU
  have hc64 : c.toNat < 2 ^ 64 := toNat_lt_2_64 hcU
  have hP : qc.toNat * c.toNat < 2 ^ 128 := by
    calc qc.toNat * c.toNat < 2 ^ 64 * 2 ^ 64 := by
            apply Nat.mul_lt_mul_of_lt_of_le hq64 (le_of_lt hc64); omega
      _ = 2 ^ 128 := by norm_num
  have e_lo : rwlo.toNat = qc.toNat * c.toNat % 2 ^ 64 := by
    rw [← Word.toBitVec64_toNat hloU, hlo, BitVec.toNat_mul,
        Word.toBitVec64_toNat hqcU, Word.toBitVec64_toNat hcU]
  have hdiv : qc.toNat * c.toNat / 2 ^ 64 < 2 ^ 64 := by
    apply Nat.div_lt_of_lt_mul; rw [← pow_add]; exact hP
  have e_hi : rwhi.toNat = qc.toNat * c.toNat / 2 ^ 64 := by
    rw [← Word.toBitVec64_toNat hhiU, hhi, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
        BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
        Word.toBitVec64_toNat hqcU, Word.toBitVec64_toNat hcU]
    rw [Nat.mod_eq_of_lt (a := qc.toNat) (by omega), Nat.mod_eq_of_lt (a := c.toNat) (by omega),
        Nat.mod_eq_of_lt hP, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hdiv]
  rw [e_lo, e_hi]
  omega

/-- **Unsigned Euclidean identity from the carry chain + the two Mul result words.** Consolidates
`prod_lo_hi_reassembly` (the 128-bit product) and `euclid_identity_unsigned` (the telescoping): given
the eight carry-chain limb equations stated directly on the low/high Mul result words `rwlo`/`rwhi`
(unsigned non-overflow branch — the M0 gluing has already substituted `c_times_quotient[i]` by the
Mul result limbs), the chip's result is the ℕ Euclidean identity `b.toNat = c·quotient + remainder`.
This is the single `hid` the `Formal` soundness feeds into `divu_remu_of_identity`; `Formal` only has to
de-gate the carry constraints and supply the two Mul `Spec`s. -/
lemma hid_of_carry_chain
    {b c quotient remainder rwlo rwhi : Word (ZMod p)} {carry : Vector (ZMod p) 8}
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
        = (((quotient.toBitVec64).setWidth 128 * (c.toBitVec64).setWidth 128) >>> 64).setWidth 64) :
    b.toNat = c.toNat * quotient.toNat + remainder.toNat := by
  have hprod0 : rwlo.toNat + rwhi.toNat * 2 ^ 64 = quotient.toNat * c.toNat :=
    prod_lo_hi_reassembly hqU hcU hloU hhiU hlo hhi
  obtain ⟨l0, l1, l2, l3⟩ := Word.lt_cases_of_isU64 hloU
  obtain ⟨g0, g1, g2, g3⟩ := Word.lt_cases_of_isU64 hhiU
  -- the eight product limbs as one vector; its base-2^16 sum is the 128-bit product.
  have hprod : (rwlo[0]).val + (rwlo[1]).val * 65536 + (rwlo[2]).val * 65536 ^ 2
      + (rwlo[3]).val * 65536 ^ 3 + (rwhi[0]).val * 65536 ^ 4 + (rwhi[1]).val * 65536 ^ 5
      + (rwhi[2]).val * 65536 ^ 6 + (rwhi[3]).val * 65536 ^ 7 = c.toNat * quotient.toNat := by
    rw [Word.toNat_def, Word.toNat_def, mul_comm quotient.toNat c.toNat] at hprod0; omega
  exact euclid_identity_unsigned (ctq := #v[rwlo[0], rwlo[1], rwlo[2], rwlo[3],
      rwhi[0], rwhi[1], rwhi[2], rwhi[3]]) (carry := carry)
    l0 l1 l2 l3 g0 g1 g2 g3 hrU hbU hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
    hl0 hl1 hl2 hl3 hh4 hh5 hh6 hh7 hprod (toNat_lt_2_64 hqU) (toNat_lt_2_64 hcU)

/-- **One-hot flag sum.** The eight boolean variant flags summing to `1` in `ZMod p` means their `.val`s
sum to `1` over `ℕ` (no wraparound, since `8 < p`). Combined with a known active flag (`.val = 1`) this
forces every other flag to `0` — the lever that collapses the cross-variant terms in soundness. -/
lemma flags_val_sum {f0 f1 f2 f3 f4 f5 f6 f7 : ZMod p}
    (b0 : f0 = 0 ∨ f0 = 1) (b1 : f1 = 0 ∨ f1 = 1) (b2 : f2 = 0 ∨ f2 = 1) (b3 : f3 = 0 ∨ f3 = 1)
    (b4 : f4 = 0 ∨ f4 = 1) (b5 : f5 = 0 ∨ f5 = 1) (b6 : f6 = 0 ∨ f6 = 1) (b7 : f7 = 0 ∨ f7 = 1)
    (hsum : f0 + f1 + f2 + f3 + f4 + f5 + f6 + f7 = 1) :
    f0.val + f1.val + f2.val + f3.val + f4.val + f5.val + f6.val + f7.val = 1 := by
  haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 8 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have e0 : f0.val ≤ 1 := by rcases b0 with h | h <;> rw [h] <;> simp [ZMod.val_one]
  have e1 : f1.val ≤ 1 := by rcases b1 with h | h <;> rw [h] <;> simp [ZMod.val_one]
  have e2 : f2.val ≤ 1 := by rcases b2 with h | h <;> rw [h] <;> simp [ZMod.val_one]
  have e3 : f3.val ≤ 1 := by rcases b3 with h | h <;> rw [h] <;> simp [ZMod.val_one]
  have e4 : f4.val ≤ 1 := by rcases b4 with h | h <;> rw [h] <;> simp [ZMod.val_one]
  have e5 : f5.val ≤ 1 := by rcases b5 with h | h <;> rw [h] <;> simp [ZMod.val_one]
  have e6 : f6.val ≤ 1 := by rcases b6 with h | h <;> rw [h] <;> simp [ZMod.val_one]
  have e7 : f7.val ≤ 1 := by rcases b7 with h | h <;> rw [h] <;> simp [ZMod.val_one]
  have hlt : f0.val + f1.val + f2.val + f3.val + f4.val + f5.val + f6.val + f7.val < p := by omega
  have key : ((f0.val + f1.val + f2.val + f3.val + f4.val + f5.val + f6.val + f7.val : ℕ) : ZMod p)
      = 1 := by push_cast [ZMod.natCast_zmod_val]; linear_combination hsum
  calc f0.val + f1.val + f2.val + f3.val + f4.val + f5.val + f6.val + f7.val
      = (((f0.val + f1.val + f2.val + f3.val + f4.val + f5.val + f6.val + f7.val : ℕ) : ZMod p)).val :=
        (ZMod.val_natCast_of_lt hlt).symm
    _ = (1 : ZMod p).val := by rw [key]
    _ = 1 := ZMod.val_one p

/-! ## Signed `DIV`/`REM` bridges

The signed variants need the operands' `toInt` (truncated division): abs columns give `|·|` (range),
sign bits give the dividend-sign conditions, and the carry chain with `b_neg`/`rem_neg` sign fills gives
the signed Euclidean identity fed to `Math.div_rem_of_identity`. -/

omit [Fact p.Prime] in
/-- **Absolute value, magnitude form.** The chip's `abs_c`/`abs_remainder` columns are the
two's-complement absolute value of `c`/`remainder` — `abs = c` when `c` is non-negative (`msb = false`),
`abs = -c` when negative. Either way the magnitude `abs.toNat` equals `c.toInt.natAbs` (no `i64::MIN`
exception, since `|intMin| = 2^63 = (-intMin).toNat`). This feeds the range hypothesis
`remainder.toInt.natAbs < c.toInt.natAbs` of `Math.div_rem_of_identity` (the chip proves
`abs_remainder.toNat < abs_c.toNat` via `LtOperationUnsigned`). -/
lemma abs_toNat_eq_natAbs {c abs : Word (ZMod p)} (habsU : abs.isU64)
    (hpos : c.toBitVec64.msb = false → abs.toBitVec64 = c.toBitVec64)
    (hneg : c.toBitVec64.msb = true → abs.toBitVec64 = -c.toBitVec64) :
    abs.toNat = c.toBitVec64.toInt.natAbs := by
  rw [← Word.toBitVec64_toNat habsU]
  by_cases h : c.toBitVec64.msb = true
  · rw [hneg h, BitVec.toInt_eq_neg_toNat_neg_of_msb_true h, Int.natAbs_neg, Int.natAbs_natCast]
  · rw [Bool.not_eq_true] at h
    rw [hpos h, BitVec.toInt_eq_toNat_of_msb h, Int.natAbs_natCast]

omit [Fact p.Prime] in
/-- **Signed 128-bit product, `toInt`.** The chip's `c_times_quotient` for signed ops is the 128-bit
signed product `quotient · c` (low 64 from `MUL`, high 64 from `MULH`). Its `toInt` is exactly the
integer product `quotient.toInt · c.toInt` — no `bmod` correction, since 64-bit operands give
`|product| ≤ 2^126 < 2^127`. This is the signed analogue of the unsigned half of `prod_lo_hi_reassembly`,
feeding the `hid` of `Math.div_rem_of_identity`. -/
lemma signed_prod_toInt (x y : BitVec 64) :
    (x.signExtend 128 * y.signExtend 128).toInt = x.toInt * y.toInt := by
  rw [BitVec.toInt_mul, BitVec.toInt_signExtend_of_le (by norm_num),
      BitVec.toInt_signExtend_of_le (by norm_num)]
  have hx1 : x.toInt < 2 ^ 63 := BitVec.toInt_lt
  have hx2 : -2 ^ 63 ≤ x.toInt := BitVec.le_toInt x
  have hy1 : y.toInt < 2 ^ 63 := BitVec.toInt_lt
  have hy2 : -2 ^ 63 ≤ y.toInt := BitVec.le_toInt y
  have hP : -2 ^ 126 ≤ x.toInt * y.toInt ∧ x.toInt * y.toInt ≤ 2 ^ 126 := by
    constructor <;> nlinarith [hx1, hx2, hy1, hy2]
  apply Int.bmod_eq_of_le_mul_two <;> push_cast <;> omega

omit [Fact p.Prime] in
private lemma setWidth_signExtend_self (x : BitVec 64) : (x.signExtend 128).setWidth 64 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_signExtend]
  have hx : x.toNat < 2 ^ 64 := x.isLt
  rcases Bool.eq_false_or_eq_true x.msb with h | h <;> rw [h] <;> simp <;> omega

omit [Fact p.Prime] in
/-- **Signed 128-bit product, low/high `toNat` split.** The chip's `MUL`/`MULH` result words `rwlo`/
`rwhi` are the low/high 64 bits of the signed product `P = quotient · c`; concatenating recovers
`P.toNat = rwlo.toNat + rwhi.toNat · 2^64`. With `signed_prod_toInt` this gives the `toInt` product the
signed Euclidean identity needs. -/
lemma prod128_toNat_split {q c rwlo rwhi : Word (ZMod p)}
    (hlo : rwlo.toBitVec64 = q.toBitVec64 * c.toBitVec64)
    (hhi : rwhi.toBitVec64
        = ((q.toBitVec64.signExtend 128 * c.toBitVec64.signExtend 128) >>> 64).setWidth 64) :
    (q.toBitVec64.signExtend 128 * c.toBitVec64.signExtend 128).toNat
      = rwlo.toBitVec64.toNat + rwhi.toBitVec64.toNat * 2 ^ 64 := by
  have hPlt : (q.toBitVec64.signExtend 128 * c.toBitVec64.signExtend 128).toNat < 2 ^ 128 :=
    BitVec.isLt _
  have hlon : rwlo.toBitVec64.toNat
      = (q.toBitVec64.signExtend 128 * c.toBitVec64.signExtend 128).toNat % 2 ^ 64 := by
    have heq : rwlo.toBitVec64
        = (q.toBitVec64.signExtend 128 * c.toBitVec64.signExtend 128).setWidth 64 := by
      rw [hlo]; simp [BitVec.setWidth_mul, setWidth_signExtend_self]
    rw [heq, BitVec.toNat_setWidth]
  have hhin : rwhi.toBitVec64.toNat
      = (q.toBitVec64.signExtend 128 * c.toBitVec64.signExtend 128).toNat / 2 ^ 64 := by
    rw [hhi, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
        Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact hPlt))]
  rw [hlon, hhin]; omega

omit [Fact p.Prime] in
private lemma toInt_eq_toNat_sub64 (x : BitVec 64) :
    x.toInt = (x.toNat : ℤ) - (if x.msb then 2 ^ 64 else 0) := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.msb_eq_decide]
  have hlt : x.toNat < 2 ^ 64 := x.isLt
  split <;> rename_i h <;> simp only [decide_eq_true_eq] at * <;> split <;> omega

omit [Fact p.Prime] in
private lemma toInt_eq_toNat_sub128 (x : BitVec 128) :
    x.toInt = (x.toNat : ℤ) - (if x.msb then 2 ^ 128 else 0) := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.msb_eq_decide]
  have hlt : x.toNat < 2 ^ 128 := x.isLt
  split <;> rename_i h <;> simp only [decide_eq_true_eq] at * <;> split <;> omega

omit [Fact p.Prime] in
private lemma toNat_eq_toInt_add128 (x : BitVec 128) :
    (x.toNat : ℤ) = x.toInt + (if x.toInt < 0 then 2 ^ 128 else 0) := by
  by_cases hm : x.msb = true
  · have h1 : x.toInt < 0 := by rw [BitVec.msb_eq_toInt] at hm; simpa using hm
    rw [if_pos h1, toInt_eq_toNat_sub128, if_pos hm]; ring
  · have h1 : ¬ x.toInt < 0 := by rw [BitVec.msb_eq_toInt] at hm; simpa using hm
    rw [if_neg h1, toInt_eq_toNat_sub128, if_neg hm]; ring

set_option maxHeartbeats 8000000 in
/-- **Signed Euclidean identity from the carry chain.** The signed analogue of
`euclid_identity_unsigned`: the eight carry-chain limb equations carry the `b_neg`/`rem_neg` sign fills
on the high limbs (`b_neg = b.msb`, `rem_neg = remainder_comp.msb`), and the `c_times_quotient` limbs are
the **signed** 128-bit product `quotient · c` (`MUL` low + `MULH` high). Telescoping over `ℤ` (with the
sign-extension realised by the `·65535` fills and the product's `toInt`/`toNat` via `signed_prod_toInt`
+ `prod128_toNat_split`) gives the signed Euclidean identity `b.toInt = quotient.toInt · c.toInt +
remainder.toInt` that `Math.div_rem_of_identity` consumes (the non-overflow normal case). -/
lemma euclid_identity_signed
    {b c quotient remc rwlo rwhi : Word (ZMod p)} {carry : Vector (ZMod p) 8}
    {b_neg rem_neg : ZMod p}
    (hbU : b.isU64) (hremcU : remc.isU64) (hloU : rwlo.isU64) (hhiU : rwhi.isU64)
    (hbneg : b_neg = if b.toBitVec64.msb then 1 else 0)
    (hrneg : rem_neg = if remc.toBitVec64.msb then 1 else 0)
    (hc0 : carry[0] = 0 ∨ carry[0] = 1) (hc1 : carry[1] = 0 ∨ carry[1] = 1)
    (hc2 : carry[2] = 0 ∨ carry[2] = 1) (hc3 : carry[3] = 0 ∨ carry[3] = 1)
    (hc4 : carry[4] = 0 ∨ carry[4] = 1) (hc5 : carry[5] = 0 ∨ carry[5] = 1)
    (hc6 : carry[6] = 0 ∨ carry[6] = 1) (hc7 : carry[7] = 0 ∨ carry[7] = 1)
    (hl0 : rwlo[0] + remc[0] = b[0] + carry[0] * 65536)
    (hl1 : rwlo[1] + remc[1] + carry[0] = b[1] + carry[1] * 65536)
    (hl2 : rwlo[2] + remc[2] + carry[1] = b[2] + carry[2] * 65536)
    (hl3 : rwlo[3] + remc[3] + carry[2] = b[3] + carry[3] * 65536)
    (hh4 : rwhi[0] + rem_neg * 65535 + carry[3] = b_neg * 65535 + carry[4] * 65536)
    (hh5 : rwhi[1] + rem_neg * 65535 + carry[4] = b_neg * 65535 + carry[5] * 65536)
    (hh6 : rwhi[2] + rem_neg * 65535 + carry[5] = b_neg * 65535 + carry[6] * 65536)
    (hh7 : rwhi[3] + rem_neg * 65535 + carry[6] = b_neg * 65535 + carry[7] * 65536)
    (hlo : rwlo.toBitVec64 = quotient.toBitVec64 * c.toBitVec64)
    (hhi : rwhi.toBitVec64
        = ((quotient.toBitVec64.signExtend 128 * c.toBitVec64.signExtend 128) >>> 64).setWidth 64) :
    b.toBitVec64.toInt
      = quotient.toBitVec64.toInt * c.toBitVec64.toInt + remc.toBitVec64.toInt := by
  haveI : Fact (Nat.Prime p) := ‹Fact p.Prime›
  haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hbn_bin : b_neg = 0 ∨ b_neg = 1 := by rw [hbneg]; split <;> simp
  have hrn_bin : rem_neg = 0 ∨ rem_neg = 1 := by rw [hrneg]; split <;> simp
  obtain ⟨lo0, lo1, lo2, lo3⟩ := Word.lt_cases_of_isU64 hloU
  obtain ⟨hi0, hi1, hi2, hi3⟩ := Word.lt_cases_of_isU64 hhiU
  obtain ⟨rc0, rc1, rc2, rc3⟩ := Word.lt_cases_of_isU64 hremcU
  obtain ⟨bb0, bb1, bb2, bb3⟩ := Word.lt_cases_of_isU64 hbU
  have hrnf : (rem_neg * 65535 : ZMod p).val < 2 ^ 16 := by
    rcases hrn_bin with h | h <;> rw [h] <;> simp [val_65535_zmod_p]
  have hbnf : (b_neg * 65535 : ZMod p).val < 2 ^ 16 := by
    rcases hbn_bin with h | h <;> rw [h] <;> simp [val_65535_zmod_p]
  have L0 := limb_lift rwlo[0] remc[0] b[0] 0 carry[0] lo0 rc0 bb0 (Or.inl rfl) hc0
    (by rw [add_zero]; exact hl0)
  have L1 := limb_lift rwlo[1] remc[1] b[1] carry[0] carry[1] lo1 rc1 bb1 hc0 hc1 hl1
  have L2 := limb_lift rwlo[2] remc[2] b[2] carry[1] carry[2] lo2 rc2 bb2 hc1 hc2 hl2
  have L3 := limb_lift rwlo[3] remc[3] b[3] carry[2] carry[3] lo3 rc3 bb3 hc2 hc3 hl3
  have H4 := limb_lift rwhi[0] (rem_neg*65535) (b_neg*65535) carry[3] carry[4] hi0 hrnf hbnf hc3 hc4 hh4
  have H5 := limb_lift rwhi[1] (rem_neg*65535) (b_neg*65535) carry[4] carry[5] hi1 hrnf hbnf hc4 hc5 hh5
  have H6 := limb_lift rwhi[2] (rem_neg*65535) (b_neg*65535) carry[5] carry[6] hi2 hrnf hbnf hc5 hc6 hh6
  have H7 := limb_lift rwhi[3] (rem_neg*65535) (b_neg*65535) carry[6] carry[7] hi3 hrnf hbnf hc6 hc7 hh7
  simp only [ZMod.val_zero] at L0
  have hrnv : (rem_neg*65535 : ZMod p).val = rem_neg.val * 65535 := by
    rcases hrn_bin with h | h <;> rw [h] <;> simp [val_65535_zmod_p, ZMod.val_one]
  have hbnv : (b_neg*65535 : ZMod p).val = b_neg.val * 65535 := by
    rcases hbn_bin with h | h <;> rw [h] <;> simp [val_65535_zmod_p, ZMod.val_one]
  rw [hrnv, hbnv] at H4 H5 H6 H7
  have C0 : carry[0].val ≤ 1 := by rcases hc0 with h|h <;> rw [h] <;> simp [ZMod.val_one]
  have C1 : carry[1].val ≤ 1 := by rcases hc1 with h|h <;> rw [h] <;> simp [ZMod.val_one]
  have C2 : carry[2].val ≤ 1 := by rcases hc2 with h|h <;> rw [h] <;> simp [ZMod.val_one]
  have C3 : carry[3].val ≤ 1 := by rcases hc3 with h|h <;> rw [h] <;> simp [ZMod.val_one]
  have C4 : carry[4].val ≤ 1 := by rcases hc4 with h|h <;> rw [h] <;> simp [ZMod.val_one]
  have C5 : carry[5].val ≤ 1 := by rcases hc5 with h|h <;> rw [h] <;> simp [ZMod.val_one]
  have C6 : carry[6].val ≤ 1 := by rcases hc6 with h|h <;> rw [h] <;> simp [ZMod.val_one]
  have C7 : carry[7].val ≤ 1 := by rcases hc7 with h|h <;> rw [h] <;> simp [ZMod.val_one]
  have BN : b_neg.val ≤ 1 := by rcases hbn_bin with h|h <;> rw [h] <;> simp [ZMod.val_one]
  have RN : rem_neg.val ≤ 1 := by rcases hrn_bin with h|h <;> rw [h] <;> simp [ZMod.val_one]
  have hsplit := prod128_toNat_split hlo hhi
  rw [Word.toBitVec64_toNat hloU, Word.toBitVec64_toNat hhiU] at hsplit
  -- **Heavy telescoping in pure ℕ** (the unsigned-style step that omega handles without the kernel
  -- deep-recursing on the mixed-ℤ certificate): collapse the eight limb equations + the product split
  -- into one ℕ identity, keeping `b.toNat`/`remc.toNat`/`prod128.toNat` as atoms.
  have hT : (quotient.toBitVec64.signExtend 128 * c.toBitVec64.signExtend 128).toNat
        + remc.toNat + rem_neg.val * (2 ^ 128 - 2 ^ 64)
      = b.toNat + b_neg.val * (2 ^ 128 - 2 ^ 64) + carry[7].val * 2 ^ 128 := by
    rw [hsplit]; simp only [Word.toNat_def]; omega
  -- the limb equations are subsumed by `hT`; clear them so the final integrality omega sees only
  -- the clean relation (otherwise the redundant limb system confuses it).
  clear hl0 hl1 hl2 hl3 hh4 hh5 hh6 hh7 L0 L1 L2 L3 H4 H5 H6 H7 hsplit hrnv hbnv hrnf hbnf
    lo0 lo1 lo2 lo3 hi0 hi1 hi2 hi3 rc0 rc1 rc2 rc3 bb0 bb1 bb2 bb3
    hc0 hc1 hc2 hc3 hc4 hc5 hc6 C0 C1 C2 C3 C4 C5 C6
  -- The `toInt`/`toNat` bridges (atoms, NOT expanded into limbs) and the product magnitude bound.
  have hpn := toNat_eq_toInt_add128 (quotient.toBitVec64.signExtend 128 * c.toBitVec64.signExtend 128)
  rw [signed_prod_toInt] at hpn
  have hbif := toInt_eq_toNat_sub64 b.toBitVec64
  have hrif := toInt_eq_toNat_sub64 remc.toBitVec64
  rw [Word.toBitVec64_toNat hbU] at hbif
  rw [Word.toBitVec64_toNat hremcU] at hrif
  have hbif2 : (if b.toBitVec64.msb then (2:ℤ)^64 else 0) = (b_neg.val:ℤ) * 2^64 := by
    rw [hbneg]; split <;> simp [ZMod.val_one, ZMod.val_zero]
  have hrif2 : (if remc.toBitVec64.msb then (2:ℤ)^64 else 0) = (rem_neg.val:ℤ) * 2^64 := by
    rw [hrneg]; split <;> simp [ZMod.val_one, ZMod.val_zero]
  rw [hbif2] at hbif; rw [hrif2] at hrif
  rw [hbif, hrif]
  -- the product magnitude bound rules out the spurious `2^128` multiple (signed top-carry argument).
  have hQbound : -2 ^ 126 ≤ quotient.toBitVec64.toInt * c.toBitVec64.toInt
      ∧ quotient.toBitVec64.toInt * c.toBitVec64.toInt ≤ 2 ^ 126 := by
    have q1 : quotient.toBitVec64.toInt < 2 ^ 63 := BitVec.toInt_lt
    have q2 : -2 ^ 63 ≤ quotient.toBitVec64.toInt := BitVec.le_toInt _
    have c1 : c.toBitVec64.toInt < 2 ^ 63 := BitVec.toInt_lt
    have c2 : -2 ^ 63 ≤ c.toBitVec64.toInt := BitVec.le_toInt _
    constructor <;> nlinarith
  have hbtn : b.toNat < 2 ^ 64 := toNat_lt_2_64 hbU
  have hrtn : remc.toNat < 2 ^ 64 := toNat_lt_2_64 hremcU
  have hbnv01 : b_neg.val = 0 ∨ b_neg.val = 1 := by
    rcases hbn_bin with h | h <;> rw [h] <;> simp [ZMod.val_one]
  have hrnv01 : rem_neg.val = 0 ∨ rem_neg.val = 1 := by
    rcases hrn_bin with h | h <;> rw [h] <;> simp [ZMod.val_one]
  have hc7v01 : carry[7].val = 0 ∨ carry[7].val = 1 := by
    rcases hc7 with h | h <;> rw [h] <;> simp [ZMod.val_one]
  zify at hT
  -- small ℤ step: substitute `prod128.toNat` (via `hpn`) into the telescoped `hT`, fix the three sign
  -- bits `b_neg`/`rem_neg`/`carry[7]` to concrete `0/1` (so the `·2^128` terms are constants, keeping
  -- omega linear), and reduce powers to numerals (so the kernel does not deep-recurse on the `2^128`
  -- pow). omega then rules out the spurious `2^128` multiple via the magnitude bounds (or closes the
  -- inconsistent sign combinations).
  have hbnd : (2 : ℤ) ^ 126 + 2 ^ 64 + 2 ^ 64 < 2 ^ 128 := by norm_num
  by_cases hsgn : quotient.toBitVec64.toInt * c.toBitVec64.toInt < 0
  · rw [if_pos hsgn] at hpn; rw [hpn] at hT
    rcases hbnv01 with h | h <;> rcases hrnv01 with h2 | h2 <;> rcases hc7v01 with h3 | h3 <;>
      simp only [h, h2, h3] at hT ⊢ <;> norm_num at hT hbnd hQbound hbtn hrtn ⊢ <;> omega
  · rw [if_neg hsgn] at hpn; rw [hpn] at hT
    rcases hbnv01 with h | h <;> rcases hrnv01 with h2 | h2 <;> rcases hc7v01 with h3 | h3 <;>
      simp only [h, h2, h3] at hT ⊢ <;> norm_num at hT hbnd hQbound hbtn hrtn ⊢ <;> omega

omit [Fact p.Prime] in
/-- **Sign bit ↔ high limb.** A `Word`'s 64-bit `msb` is set iff its high 16-bit limb is `≥ 2^15`.
The chip's `U16MSBOperation` on the high limb `w[3]` computes exactly this indicator, so this is the
bridge from the gadget's `msb` column to `toBitVec64.msb` (= the dividend/remainder sign). -/
lemma toBitVec64_msb_iff {w : Word (ZMod p)} (hw : w.isU64) :
    w.toBitVec64.msb = true ↔ 32768 ≤ w[3].val := by
  rw [BitVec.msb_eq_decide, decide_eq_true_eq, Word.toBitVec64_toNat hw, Word.toNat_def]
  obtain ⟨h0, h1, h2, h3⟩ := Word.lt_cases_of_isU64 hw
  omega

/-- **Sign conditions** (the remainder carries the dividend's sign). From the chip's `b_neg`/`rem_neg`
sign columns (`= if msb then 1 else 0`, via `U16MSBOperation` + `E15`/`E17`) and the two sign-product
constraints `E225` (`rem_neg = 0 ∨ b_neg = 1`) and `E228` (`remainder = 0 ∨ rem_neg = 1 ∨ b_neg = 0`),
the two sign hypotheses of `Math.div_rem_of_identity` follow. The `b.toInt = 0` edge of `hsgn_neg`
(where the sign columns alone only give `r ≥ 0`) is closed from the Euclidean identity + range:
`b = 0`, `|r| < |c|`, `c ≠ 0` force `r = 0`. -/
lemma sign_conditions {b remc c quotient : BitVec 64} {b_neg rem_neg : ZMod p}
    (hbneg : b_neg = if b.msb then 1 else 0)
    (hrneg : rem_neg = if remc.msb then 1 else 0)
    (hE225 : rem_neg = 0 ∨ b_neg = 1)
    (hE228 : remc = 0#64 ∨ rem_neg = 1 ∨ b_neg = 0)
    (hc0 : c ≠ 0#64)
    (hid : b.toInt = c.toInt * quotient.toInt + remc.toInt)
    (hlt : remc.toInt.natAbs < c.toInt.natAbs) :
    (0 ≤ b.toInt → 0 ≤ remc.toInt) ∧ (b.toInt ≤ 0 → remc.toInt ≤ 0) := by
  haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h01 : (0 : ZMod p) ≠ 1 := zero_ne_one
  have hbm : b.msb = decide (b.toInt < 0) := BitVec.msb_eq_toInt
  have hrm : remc.msb = decide (remc.toInt < 0) := BitVec.msb_eq_toInt
  -- `rem_neg = 0` forces `remc.msb = false` (≥ 0); `rem_neg = 1` forces `remc.msb = true` (< 0).
  have hrn0_msb : rem_neg = 0 → 0 ≤ remc.toInt := by
    intro h; rw [hrm] at hrneg
    rcases Int.lt_or_le remc.toInt 0 with hl | hl
    · rw [decide_eq_true (by exact hl)] at hrneg; rw [hrneg] at h; exact absurd h.symm h01
    · exact hl
  have hrn1_msb : rem_neg = 1 → remc.toInt ≤ 0 := by
    intro h; rw [hrm] at hrneg
    rcases Int.lt_or_le remc.toInt 0 with hl | hl
    · omega
    · rw [decide_eq_false (by omega)] at hrneg; rw [hrneg] at h; exact absurd h h01
  refine ⟨?_, ?_⟩
  · -- hsgn_pos: `0 ≤ b.toInt` ⇒ `b_neg = 0` ⇒ (E225) `rem_neg = 0` ⇒ `0 ≤ remc.toInt`.
    intro hbpos
    have hbf : b.msb = false := by rw [hbm]; exact decide_eq_false (by omega)
    have hbn0 : b_neg = 0 := by rw [hbneg, hbf]; simp
    rcases hE225 with h | h
    · exact hrn0_msb h
    · rw [hbn0] at h; exact absurd h h01
  · -- hsgn_neg.
    intro hbnp
    rcases lt_or_eq_of_le hbnp with hblt | hb0
    · -- `b.toInt < 0` ⇒ `b_neg = 1` ⇒ (E228) `remc = 0 ∨ rem_neg = 1` ⇒ `remc.toInt ≤ 0`.
      have hbt : b.msb = true := by rw [hbm]; exact decide_eq_true hblt
      have hbn1 : b_neg = 1 := by rw [hbneg, hbt]; simp
      rcases hE228 with h | h | h
      · rw [h, BitVec.toInt_zero]
      · exact hrn1_msb h
      · rw [hbn1] at h; exact absurd h.symm h01
    · -- `b.toInt = 0`: `b_neg = 0` ⇒ (E225) `rem_neg = 0` ⇒ `0 ≤ remc.toInt`; the identity forces `= 0`.
      have hbf : b.msb = false := by rw [hbm]; exact decide_eq_false (by omega)
      have hbn0 : b_neg = 0 := by rw [hbneg, hbf]; simp
      have hrnn : 0 ≤ remc.toInt := by
        rcases hE225 with h | h
        · exact hrn0_msb h
        · rw [hbn0] at h; exact absurd h h01
      have hcz : c.toInt ≠ 0 := fun hh => hc0 (BitVec.eq_of_toInt_eq (by rw [hh]; simp))
      have key : remc.toInt = -(c.toInt * quotient.toInt) := by rw [hb0] at hid; linarith
      have hna : remc.toInt.natAbs = c.toInt.natAbs * quotient.toInt.natAbs := by
        rw [key, Int.natAbs_neg, Int.natAbs_mul]
      rw [hna] at hlt
      have hq0 : quotient.toInt.natAbs = 0 := by
        by_contra hq
        have h1 : 1 ≤ quotient.toInt.natAbs := Nat.one_le_iff_ne_zero.mpr hq
        have h2 : c.toInt.natAbs ≤ c.toInt.natAbs * quotient.toInt.natAbs :=
          Nat.le_mul_of_pos_right _ (by omega)
        omega
      have : quotient.toInt = 0 := Int.natAbs_eq_zero.mp hq0
      rw [this, mul_zero, neg_zero] at key
      omega

omit [Fact p.Prime] in
/-- **Signed remainder range from the abs columns.** `abs_toNat_eq_natAbs` on both abs columns turns
the chip's unsigned comparison `abs_remainder.toNat < abs_c.toNat` (proved by `LtOperationUnsigned`)
into the `toInt.natAbs` form `Math.div_rem_of_identity` needs. -/
lemma hlt_signed_of_abs {remc c absr absc : Word (ZMod p)}
    (habsrU : absr.isU64) (habscU : absc.isU64)
    (hposr : remc.toBitVec64.msb = false → absr.toBitVec64 = remc.toBitVec64)
    (hnegr : remc.toBitVec64.msb = true → absr.toBitVec64 = -remc.toBitVec64)
    (hposc : c.toBitVec64.msb = false → absc.toBitVec64 = c.toBitVec64)
    (hnegc : c.toBitVec64.msb = true → absc.toBitVec64 = -c.toBitVec64)
    (hcmp : absr.toNat < absc.toNat) :
    remc.toBitVec64.toInt.natAbs < c.toBitVec64.toInt.natAbs := by
  rw [← abs_toNat_eq_natAbs habsrU hposr hnegr, ← abs_toNat_eq_natAbs habscU hposc hnegc]
  exact hcmp

/-! ### Signed-64 overflow endpoints (`b = i64::MIN`, `c = -1`) -/

omit [Fact p.Prime] in
/-- A `u64` word whose value is `2^63` is `i64::MIN` as a `BitVec`. In the signed overflow branch the
`is_overflow_b` `IsEqualWord` against `#v[0,0,0,32768]` pins the `b` column to this value. -/
lemma intMin_of_toNat {b : Word (ZMod p)} (hbU : b.isU64) (h : b.toNat = 2 ^ 63) :
    b.toBitVec64 = BitVec.intMin 64 := by
  rw [← BitVec.toNat_inj, Word.toBitVec64_toNat hbU, h, BitVec.toNat_intMin]; norm_num

omit [Fact p.Prime] in
/-- A `u64` word whose value is `2^64 - 1` is `-1` as a `BitVec`. In the signed overflow branch the
`is_overflow_c` `IsEqualWord` against `#v[65535,65535,65535,65535]` pins the `c` column to this value. -/
lemma neg_one_of_toNat {c : Word (ZMod p)} (hcU : c.isU64) (h : c.toNat = 2 ^ 64 - 1) :
    c.toBitVec64 = -1#64 := by
  rw [← BitVec.toNat_inj, Word.toBitVec64_toNat hcU, h, BitVec.neg_one_eq_allOnes,
    BitVec.toNat_allOnes]

/-! ## `*W` projection bridges

`DIVUW`/`REMUW` zero-extend (top two limbs `0`); `DIVW`/`REMW` sign-extend (top two limbs
`m·65535` of bit 31). The lemmas below project the 64-bit carry-chain identity to the
32-bit `extractLsb 31 0` form consumed by `Math.*w`, and the output column to `signExtend 64 (low-32)`. -/

omit [Fact p.Prime] in
/-- low-32 `toNat` of an `extractLsb` in terms of the bottom two limbs. -/
lemma extractLsb_lo_toNat {w : Word (ZMod p)} (hw : w.isU64) :
    (BitVec.extractLsb 31 0 w.toBitVec64).toNat = w[0].val + w[1].val * 2 ^ 16 := by
  obtain ⟨c0, c1, c2, c3⟩ := Word.lt_cases_of_isU64 hw
  rw [BitVec.extractLsb, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Word.toBitVec64_toNat hw,
      Word.toNat_def]
  omega

/-- **Zero-high projection.** A word whose top two limbs are `0` (zero-extended low-32, the shape of
`DIVUW`/`REMUW` operands & comp columns) has `(extractLsb 31 0 w).toNat = w.toNat`. -/
lemma extractLsb_toNat_of_hi_zero {w : Word (ZMod p)} (hw : w.isU64)
    (h2 : w[2] = 0) (h3 : w[3] = 0) :
    (BitVec.extractLsb 31 0 w.toBitVec64).toNat = w.toNat := by
  obtain ⟨c0, c1, c2, c3⟩ := Word.lt_cases_of_isU64 hw
  have hv2 : w[2].val = 0 := by rw [h2, ZMod.val_zero]
  have hv3 : w[3].val = 0 := by rw [h3, ZMod.val_zero]
  rw [extractLsb_lo_toNat hw, Word.toNat_def, hv2, hv3]; ring

omit [Fact p.Prime] in
/-- the `extractLsb 31 0` msb is the high bit of limb 1 (bit 31 of the word). -/
lemma extractLsb_msb {w : Word (ZMod p)} (hw : w.isU64) :
    (BitVec.extractLsb 31 0 w.toBitVec64).msb = decide (32768 ≤ w[1].val) := by
  obtain ⟨c0, c1, c2, c3⟩ := Word.lt_cases_of_isU64 hw
  rw [BitVec.msb_eq_decide, extractLsb_lo_toNat hw, decide_eq_decide]
  omega

omit [Fact p.Prime] in
/-- **Sign-fill ⟹ sign-extension of low-32.** A word whose top two limbs are the sign fill of bit 31
(`m·65535` with `m = msb of low-32`, the shape of `*W` output columns and signed-`*W` operands) equals
the 64-bit sign extension of its low 32 bits. -/
lemma word_eq_signExtend_lo {w : Word (ZMod p)} (hw : w.isU64)
    (h2 : w[2].val = (if 32768 ≤ w[1].val then 65535 else 0))
    (h3 : w[3].val = (if 32768 ≤ w[1].val then 65535 else 0)) :
    w.toBitVec64 = BitVec.signExtend 64 (BitVec.extractLsb 31 0 w.toBitVec64) := by
  obtain ⟨c0, c1, c2, c3⟩ := Word.lt_cases_of_isU64 hw
  apply BitVec.eq_of_toNat_eq
  rw [Word.toBitVec64_toNat hw, Word.toNat_def, BitVec.toNat_signExtend, BitVec.toNat_setWidth,
      extractLsb_lo_toNat hw, extractLsb_msb hw]
  by_cases hb : 32768 ≤ w[1].val <;> rw [h2, h3] <;>
    simp only [hb, decide_true, decide_false, reduceCtorEq, reduceIte] <;> omega

omit [Fact p.Prime] in
/-- **Sign-fill ⟹ `toInt` projection.** As `word_eq_signExtend_lo`, but the `toInt` form: a sign-filled
word has the same signed value as its low 32 bits (the `DIVW`/`REMW` signed-identity projection). -/
lemma toInt_eq_extractLsb_of_signfill {w : Word (ZMod p)} (hw : w.isU64)
    (h2 : w[2].val = (if 32768 ≤ w[1].val then 65535 else 0))
    (h3 : w[3].val = (if 32768 ≤ w[1].val then 65535 else 0)) :
    w.toBitVec64.toInt = (BitVec.extractLsb 31 0 w.toBitVec64).toInt := by
  conv_lhs => rw [word_eq_signExtend_lo hw h2 h3]
  exact BitVec.toInt_signExtend_of_le (by norm_num)

omit [Fact p.Prime] in
/-- two words sharing their bottom two limbs have equal low-32 extracts (the comp↔output bridge, since
`quotient_comp[0,1] = quotient[0,1]` via `E48`/`E49`). -/
lemma extractLsb_lo_congr {w1 w2 : Word (ZMod p)} (hw1 : w1.isU64) (hw2 : w2.isU64)
    (h0 : w1[0] = w2[0]) (h1 : w1[1] = w2[1]) :
    BitVec.extractLsb 31 0 w1.toBitVec64 = BitVec.extractLsb 31 0 w2.toBitVec64 := by
  apply BitVec.eq_of_toNat_eq
  rw [extractLsb_lo_toNat hw1, extractLsb_lo_toNat hw2, h0, h1]

set_option maxHeartbeats 4000000 in
/-- **Unsigned word Euclidean identity (low product only).** For `DIVUW`/`REMUW` the operand/quotient/
remainder columns are all zero-extended low-32 (`< 2^32`), so the *low* 64-bit product (`mul_lower`,
`ctqlo = qc·c`) already captures the whole product. The four low carry-chain limb equations then pin the
32-bit identity: the magnitude bound `(2^32-1)^2 < 2^64 - 2^32` forces the top carry to 0, so the high
product limbs (`ctq[4..7]`, which the *flagless* upper `MulOperation` does not pin in our port — SP1
constrains them to its selected output `= 0`, but our gluing ties them to the unexposed raw product
bytes) are never needed. -/
lemma euclid_identity_word_unsigned
    {ctqlo rem b qc c : Word (ZMod p)} {carry : Vector (ZMod p) 4}
    (hloU : ctqlo.isU64) (hrU : rem.isU64) (hbU : b.isU64) (hqU : qc.isU64) (hcU : c.isU64)
    (hq2 : qc[2] = 0) (hq3 : qc[3] = 0) (hc2 : c[2] = 0) (hc3 : c[3] = 0)
    (hb2 : b[2] = 0) (hb3 : b[3] = 0) (hr2 : rem[2] = 0) (hr3 : rem[3] = 0)
    (hcb0 : carry[0] = 0 ∨ carry[0] = 1) (hcb1 : carry[1] = 0 ∨ carry[1] = 1)
    (hcb2 : carry[2] = 0 ∨ carry[2] = 1) (hcb3 : carry[3] = 0 ∨ carry[3] = 1)
    (hl0 : ctqlo[0] + rem[0] = b[0] + carry[0] * 65536)
    (hl1 : ctqlo[1] + rem[1] + carry[0] = b[1] + carry[1] * 65536)
    (hl2 : ctqlo[2] + rem[2] + carry[1] = b[2] + carry[2] * 65536)
    (hl3 : ctqlo[3] + rem[3] + carry[2] = b[3] + carry[3] * 65536)
    (hlo : ctqlo.toBitVec64 = qc.toBitVec64 * c.toBitVec64) :
    b.toNat = c.toNat * qc.toNat + rem.toNat := by
  haveI : Fact (Nat.Prime p) := ‹Fact p.Prime›
  obtain ⟨l0, l1, l2, l3⟩ := Word.lt_cases_of_isU64 hloU
  obtain ⟨r0, r1, _, _⟩ := Word.lt_cases_of_isU64 hrU
  obtain ⟨bb0, bb1, _, _⟩ := Word.lt_cases_of_isU64 hbU
  have hqlt : qc.toNat < 2 ^ 32 := by
    obtain ⟨q0, q1, _, _⟩ := Word.lt_cases_of_isU64 hqU
    rw [Word.toNat_def, show qc[2].val = 0 from by rw [hq2, ZMod.val_zero],
        show qc[3].val = 0 from by rw [hq3, ZMod.val_zero]]; omega
  have hclt : c.toNat < 2 ^ 32 := by
    obtain ⟨cc0, cc1, _, _⟩ := Word.lt_cases_of_isU64 hcU
    rw [Word.toNat_def, show c[2].val = 0 from by rw [hc2, ZMod.val_zero],
        show c[3].val = 0 from by rw [hc3, ZMod.val_zero]]; omega
  -- low 64 product = qc·c (no wraparound: both < 2^32).
  have hprod : ctqlo.toNat = qc.toNat * c.toNat := by
    rw [← Word.toBitVec64_toNat hloU, hlo, BitVec.toNat_mul, Word.toBitVec64_toNat hqU,
        Word.toBitVec64_toNat hcU, Nat.mod_eq_of_lt (by nlinarith [hqlt, hclt])]
  -- lift the four low limb equations to ℕ.
  have L0 := limb_lift ctqlo[0] rem[0] b[0] 0 carry[0] l0 r0 bb0 (Or.inl rfl) hcb0
    (by rw [add_zero]; exact hl0)
  simp only [ZMod.val_zero] at L0
  have L1 := limb_lift ctqlo[1] rem[1] b[1] carry[0] carry[1] l1 r1 bb1 hcb0 hcb1 hl1
  have L2 := limb_lift ctqlo[2] rem[2] b[2] carry[1] carry[2] l2 (by rw [hr2]; simp [ZMod.val_zero])
    (by rw [hb2]; simp [ZMod.val_zero]) hcb1 hcb2 hl2
  have L3 := limb_lift ctqlo[3] rem[3] b[3] carry[2] carry[3] l3 (by rw [hr3]; simp [ZMod.val_zero])
    (by rw [hb3]; simp [ZMod.val_zero]) hcb2 hcb3 hl3
  have C3 : carry[3].val ≤ 1 := by rcases hcb3 with h | h <;> rw [h] <;> simp [ZMod.val_one]
  have hbv2 : b[2].val = 0 := by rw [hb2, ZMod.val_zero]
  have hbv3 : b[3].val = 0 := by rw [hb3, ZMod.val_zero]
  have hrv2 : rem[2].val = 0 := by rw [hr2, ZMod.val_zero]
  have hrv3 : rem[3].val = 0 := by rw [hr3, ZMod.val_zero]
  -- the product (= ctqlo sum) is ≤ (2^32-1)^2 < 2^64 - 2^32, ruling out the top carry.
  have hpb : ctqlo[0].val + ctqlo[1].val * 2 ^ 16 + ctqlo[2].val * 2 ^ 32 + ctqlo[3].val * 2 ^ 48
      ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := by
    rw [← Word.toNat_def, hprod]; exact Nat.mul_le_mul (by omega) (by omega)
  rw [mul_comm c.toNat qc.toNat, ← hprod, Word.toNat_def, Word.toNat_def, Word.toNat_def]
  omega

omit [Fact p.Prime] in
/-- `toNat ↔ toInt` for a 64-bit `BitVec`: the unsigned value is the signed value plus a `2^64`
correction when negative (the 64-bit analogue of `toNat_eq_toInt_add128`). -/
private lemma toNat_eq_toInt_add64 (x : BitVec 64) :
    (x.toNat : ℤ) = x.toInt + (if x.toInt < 0 then 2 ^ 64 else 0) := by
  by_cases hm : x.msb = true
  · have h1 : x.toInt < 0 := by rw [BitVec.msb_eq_toInt] at hm; simpa using hm
    rw [if_pos h1, toInt_eq_toNat_sub64, if_pos hm]; ring
  · have h1 : ¬ x.toInt < 0 := by rw [BitVec.msb_eq_toInt] at hm; simpa using hm
    rw [if_neg h1, toInt_eq_toNat_sub64, if_neg hm]; ring

omit [Fact p.Prime] in
/-- `toInt` of a 64-bit product whose integer value fits in `[-2^62, 2^62]` is bmod-free (the 64-bit,
clean-context analogue of `signed_prod_toInt`'s core). Kept standalone so the `bmod`/`omega` step runs
in a minimal hypothesis context — `omega` in the heavy carry-chain context produces a huge certificate
that the kernel deep-recurses on. -/
private lemma toInt_mul64_of_bound {x y : BitVec 64}
    (hlo : -2 ^ 62 ≤ x.toInt * y.toInt) (hhi : x.toInt * y.toInt ≤ 2 ^ 62) :
    (x * y).toInt = x.toInt * y.toInt := by
  rw [BitVec.toInt_mul]
  apply Int.bmod_eq_of_le_mul_two <;> push_cast <;> omega

set_option maxHeartbeats 8000000 in
/-- **Signed word Euclidean identity (low product only).** The signed analogue of
`euclid_identity_word_unsigned`: for `DIVW`/`REMW` the operand/quotient/remainder columns are all
*sign-extended* low-32 (top two limbs the sign fill of bit 31), so the *low* 64-bit product
(`mul_lower`, `ctqlo = quotient·c`) captures the whole signed 32-bit product (`|q32·c32| ≤ 2^62 < 2^63`,
no 64-bit wraparound — the flagless upper `MulOperation` is never needed). The four low carry-chain limb
equations telescope over ℕ to `ctqlo.toNat + remc.toNat = b.toNat + carry[3]·2^64`; converting to `toInt`
(the sign corrections are multiples of `2^64`) and using the magnitude bound
`|q·c| + |remc| + |b| < 2^64` forces the spurious `2^64` multiple to `0`, giving the 64-bit signed
identity `b.toInt = quotient.toInt·c.toInt + remc.toInt` that `assemble_signed_word_normal` projects to
32 bits. -/
lemma euclid_identity_word_signed
    {ctqlo b c quotient remc : Word (ZMod p)} {carry : Vector (ZMod p) 4}
    (hloU : ctqlo.isU64) (hbU : b.isU64) (hcU : c.isU64) (hqU : quotient.isU64) (hrU : remc.isU64)
    (hbf2 : b[2].val = (if 32768 ≤ b[1].val then 65535 else 0))
    (hbf3 : b[3].val = (if 32768 ≤ b[1].val then 65535 else 0))
    (hcf2 : c[2].val = (if 32768 ≤ c[1].val then 65535 else 0))
    (hcf3 : c[3].val = (if 32768 ≤ c[1].val then 65535 else 0))
    (hqf2 : quotient[2].val = (if 32768 ≤ quotient[1].val then 65535 else 0))
    (hqf3 : quotient[3].val = (if 32768 ≤ quotient[1].val then 65535 else 0))
    (hrf2 : remc[2].val = (if 32768 ≤ remc[1].val then 65535 else 0))
    (hrf3 : remc[3].val = (if 32768 ≤ remc[1].val then 65535 else 0))
    (hcb0 : carry[0] = 0 ∨ carry[0] = 1) (hcb1 : carry[1] = 0 ∨ carry[1] = 1)
    (hcb2 : carry[2] = 0 ∨ carry[2] = 1) (hcb3 : carry[3] = 0 ∨ carry[3] = 1)
    (hl0 : ctqlo[0] + remc[0] = b[0] + carry[0] * 65536)
    (hl1 : ctqlo[1] + remc[1] + carry[0] = b[1] + carry[1] * 65536)
    (hl2 : ctqlo[2] + remc[2] + carry[1] = b[2] + carry[2] * 65536)
    (hl3 : ctqlo[3] + remc[3] + carry[2] = b[3] + carry[3] * 65536)
    (hlo : ctqlo.toBitVec64 = quotient.toBitVec64 * c.toBitVec64) :
    b.toBitVec64.toInt
      = quotient.toBitVec64.toInt * c.toBitVec64.toInt + remc.toBitVec64.toInt := by
  haveI : Fact (Nat.Prime p) := ‹Fact p.Prime›
  -- 32-bit `toInt` projections (sign-extension) and the resulting `[-2^31, 2^31)` bounds.
  have hbp := toInt_eq_extractLsb_of_signfill hbU hbf2 hbf3
  have hcp := toInt_eq_extractLsb_of_signfill hcU hcf2 hcf3
  have hqp := toInt_eq_extractLsb_of_signfill hqU hqf2 hqf3
  have hrp := toInt_eq_extractLsb_of_signfill hrU hrf2 hrf3
  have hbB1 : b.toBitVec64.toInt < 2 ^ 31 := by rw [hbp]; exact BitVec.toInt_lt
  have hbB2 : -2 ^ 31 ≤ b.toBitVec64.toInt := by rw [hbp]; exact BitVec.le_toInt _
  have hrB1 : remc.toBitVec64.toInt < 2 ^ 31 := by rw [hrp]; exact BitVec.toInt_lt
  have hrB2 : -2 ^ 31 ≤ remc.toBitVec64.toInt := by rw [hrp]; exact BitVec.le_toInt _
  have hqB1 : quotient.toBitVec64.toInt < 2 ^ 31 := by rw [hqp]; exact BitVec.toInt_lt
  have hqB2 : -2 ^ 31 ≤ quotient.toBitVec64.toInt := by rw [hqp]; exact BitVec.le_toInt _
  have hcB1 : c.toBitVec64.toInt < 2 ^ 31 := by rw [hcp]; exact BitVec.toInt_lt
  have hcB2 : -2 ^ 31 ≤ c.toBitVec64.toInt := by rw [hcp]; exact BitVec.le_toInt _
  -- product magnitude bound `|q·c| ≤ 2^62 < 2^63` ⟹ no 64-bit wraparound (bmod is the identity).
  have hPhi : quotient.toBitVec64.toInt * c.toBitVec64.toInt ≤ 2 ^ 62 := by
    nlinarith [hqB1, hqB2, hcB1, hcB2]
  have hPlo : -2 ^ 62 ≤ quotient.toBitVec64.toInt * c.toBitVec64.toInt := by
    nlinarith [hqB1, hqB2, hcB1, hcB2]
  have hctqloInt : ctqlo.toBitVec64.toInt = quotient.toBitVec64.toInt * c.toBitVec64.toInt := by
    rw [hlo]; exact toInt_mul64_of_bound hPlo hPhi
  -- ℕ telescoping of the four low carry-chain limb equations.
  obtain ⟨lo0, lo1, lo2, lo3⟩ := Word.lt_cases_of_isU64 hloU
  obtain ⟨rc0, rc1, rc2, rc3⟩ := Word.lt_cases_of_isU64 hrU
  obtain ⟨bb0, bb1, bb2, bb3⟩ := Word.lt_cases_of_isU64 hbU
  have L0 := limb_lift ctqlo[0] remc[0] b[0] 0 carry[0] lo0 rc0 bb0 (Or.inl rfl) hcb0
    (by rw [add_zero]; exact hl0)
  have L1 := limb_lift ctqlo[1] remc[1] b[1] carry[0] carry[1] lo1 rc1 bb1 hcb0 hcb1 hl1
  have L2 := limb_lift ctqlo[2] remc[2] b[2] carry[1] carry[2] lo2 rc2 bb2 hcb1 hcb2 hl2
  have L3 := limb_lift ctqlo[3] remc[3] b[3] carry[2] carry[3] lo3 rc3 bb3 hcb2 hcb3 hl3
  simp only [ZMod.val_zero] at L0
  have hT : ctqlo.toNat + remc.toNat = b.toNat + carry[3].val * 2 ^ 64 := by
    rw [Word.toNat_def, Word.toNat_def, Word.toNat_def]; omega
  -- `toNat ↔ toInt` bridges (the sign corrections are multiples of `2^64`); the product `toInt` is
  -- bmod-free by `hctqloInt`.
  have eQ := toNat_eq_toInt_add64 ctqlo.toBitVec64
  rw [Word.toBitVec64_toNat hloU, hctqloInt] at eQ
  have eB := toNat_eq_toInt_add64 b.toBitVec64
  rw [Word.toBitVec64_toNat hbU] at eB
  have eR := toNat_eq_toInt_add64 remc.toBitVec64
  rw [Word.toBitVec64_toNat hrU] at eR
  have hc3v : (carry[3].val : ℤ) = 0 ∨ (carry[3].val : ℤ) = 1 := by
    rcases hcb3 with h | h <;> rw [h] <;> simp [ZMod.val_one, ZMod.val_zero]
  zify at hT
  rw [eQ, eB, eR] at hT
  -- clear the carry-chain / sign-fill clutter so the integrality `omega` runs in a minimal context
  -- (a large context makes its certificate kernel-deep-recurse on the `2^64` literals).
  clear hl0 hl1 hl2 hl3 L0 L1 L2 L3 lo0 lo1 lo2 lo3 rc0 rc1 rc2 rc3 bb0 bb1 bb2 bb3
    hbf2 hbf3 hcf2 hcf3 hqf2 hqf3 hrf2 hrf3 hbp hcp hqp hrp eQ eB eR hctqloInt hlo
    hcb0 hcb1 hcb2 hcb3 hqB1 hqB2 hcB1 hcB2
  have hbnd : (2 : ℤ) ^ 62 + 2 ^ 31 + 2 ^ 31 < 2 ^ 64 := by norm_num
  -- fix the three sign corrections + the top carry to concrete values, reduce the powers to numerals,
  -- then `omega` rules out the spurious `2^64` multiple via the magnitude bounds.
  split_ifs at hT with h1 h2 h3 <;> rcases hc3v with hc | hc <;> rw [hc] at hT <;>
    norm_num at hT hbB1 hbB2 hrB1 hrB2 hPlo hPhi hbnd ⊢ <;> omega
