import SP1Clean.Proofs.Chips.DivRemChip.Populate.Signs
import SP1Clean.Proofs.Chips.DivRemChip.Populate.Shapes
import SP1Clean.Proofs.Operations.LtOperationUnsigned.Formal

/-! # `DivRemChip` populate value bundles — divide-by-zero, absolute values, `max(|c|,1)`, range

Value-level facts about the populate functions feeding four own-assert groups:

* **E230–E244** (the `is_c_0`-gated quotient/remainder pins): `isC0Witness`'s `result` in if-form
  (`isC0_result_eq`/`isC0_result_bool`), the per-class bridge between "`cComp` is the zero word"
  and the division core's divisor-zero tests (`cComp_zero_iff_64`/`_signedW`/`_unsignedW`), and the
  divisor-zero values themselves: every `quotient` limb is `65535` (`isC0_one_quotient`) and
  `remainder_comp = bComp` (`isC0_one_remComp`).
* **E247–E268 + E270–E284** (the abs ties and the gated `AddOperation` zero-values):
  `populateAbsC`/`populateAbsRem` collapse to the computational operands when the matching sign
  cell is off (`absC_eq_of_not_neg`/`absRem_eq_of_not_neg`), and when a negation event fires the
  populated `AddOperation` value word is zero (`wCneg_value_zero`/`wRneg_value_zero`), via the
  base-2^16 characterization `addPopulate_eq_wordOfNat`
  (`AddOperation.populate x y = wordOfNat ((x + y) mod 2^64)`).
* **E299–E305** (the `max(1, |c|)` formula): the committed `max_abs_c_or_1` limbs in the
  constraint's `is_c_0`-selected form (`maxAbs_limb0`/`maxAbs_limbk`), keyed on the
  `|c| = 0 ↔ cComp = 0` bridge `absC_toNat_zero_iff`.
* **E307** (the remainder range bit): on a live remainder check the composed
  `U16CompareOperation` bit is `1` (`ltBit_one_of_gate`) — the per-class core
  `|remainder| < max(1, |c|)` runs through width-generic `BitVec` magnitude lemmas
  (`bvAbs_srem_lt`: `|x.srem y| < |y|` for `y ≠ 0`, proved from core's `BitVec.srem_eq`
  four-case `umod` characterization, no `toInt` divisibility theory needed); the off-gate
  `lt` blocks are zero (`ltCl_zero_of_gate_ne` and friends).

Statement deviations from the working notes: `isC0_one_quotient` and the divisor-zero core
`quotBits_allOnes_of_czero` need **no** one-hot flag facts (every `quotBits` branch maps its own
divisor-zero test through the matching `cComp_zero_iff_*` bridge); `maxAbs_limb0`/`maxAbs_limbk`
need only `hC` (no flag facts). The alu-event definitional forms (E286/E288) are already covered
by `Shapes.populateMisc_0/1` (`rfl`-lemmas), so no `alu_event_defs` is added here. -/

namespace SP1Clean.DivRemChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-! ## Width-generic `BitVec` magnitude helpers

`bvAbs` is the chip's two's-complement absolute value (`if msb then -x else x`). The block below
derives its `toNat` characterization, the `|x.srem y| < |y|` core (via core's `BitVec.srem_eq`),
and the 32→64 sign-extension transport (`|sext x| = |x|`, `msb (sext x) = msb x`,
`setWidth 32 ∘ signExtend 64 = id`). None of these mention the field. -/

/-- `BitVec.toNat_umod` restated on the `.umod` spelling the division core uses. -/
private lemma toNat_umod' {w : ℕ} (x y : BitVec w) : (x.umod y).toNat = x.toNat % y.toNat :=
  BitVec.toNat_umod

/-- `toNat`-injectivity packaged on the zero endpoint. -/
private lemma bv_toNat_eq_zero_iff {w : ℕ} (z : BitVec w) : z.toNat = 0 ↔ z = 0 := by
  constructor
  · intro h
    rw [← BitVec.toNat_inj, h]
    simp
  · intro h
    rw [h]
    simp

/-- The two's-complement magnitude in `toNat` form. -/
lemma bvAbs_toNat {w : ℕ} (x : BitVec w) :
    (bvAbs x).toNat = if x.msb = true then (2 ^ w - x.toNat) % 2 ^ w else x.toNat := by
  unfold bvAbs
  cases hmx : x.msb
  · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
  · rw [if_pos rfl, if_pos rfl, BitVec.toNat_neg]

/-- `bvAbs x = 0` exactly on `x = 0` (`-x = 0 → x = 0` at the `toNat` level). -/
private lemma bvAbs_eq_zero_iff {w : ℕ} (x : BitVec w) : bvAbs x = 0 ↔ x = 0 := by
  unfold bvAbs
  split
  · constructor
    · intro h
      have h2 : (-x).toNat = 0 := by rw [h]; simp
      rw [BitVec.toNat_neg] at h2
      have hx := x.isLt
      rw [← BitVec.toNat_inj]
      have h0 : (0 : BitVec w).toNat = 0 := by simp
      rw [h0]
      by_contra hxn
      rw [Nat.mod_eq_of_lt (by omega)] at h2
      omega
    · intro h
      rw [h, ← BitVec.toNat_inj, BitVec.toNat_neg]
      simp
  · exact Iff.rfl

/-- Negation preserves the magnitude of a small (`< 2^(w-1)`) value: `|-z| = z`. -/
private lemma bvAbs_neg_toNat {w : ℕ} (hw : 0 < w) {z : BitVec w}
    (hz : z.toNat < 2 ^ (w - 1)) : (bvAbs (-z)).toNat = z.toNat := by
  have hzlt := z.isLt
  have h2w : 2 ^ (w - 1) * 2 = 2 ^ w := by
    rw [← pow_succ]
    congr 1
    omega
  have hnt : (-z).toNat = (2 ^ w - z.toNat) % 2 ^ w := BitVec.toNat_neg z
  by_cases h0 : z.toNat = 0
  · have hnt0 : (-z).toNat = 0 := by rw [hnt, h0, Nat.sub_zero, Nat.mod_self]
    have hm : (-z).msb = false := by
      rw [BitVec.msb_eq_decide]
      apply decide_eq_false
      rw [hnt0]
      omega
    rw [bvAbs_toNat, hm, if_neg Bool.false_ne_true, hnt0, h0]
  · have hnt1 : (-z).toNat = 2 ^ w - z.toNat := by
      rw [hnt, Nat.mod_eq_of_lt (by omega)]
    have hm : (-z).msb = true := by
      rw [BitVec.msb_eq_decide]
      apply decide_eq_true
      rw [hnt1]
      omega
    rw [bvAbs_toNat, hm, if_pos rfl, hnt1, Nat.mod_eq_of_lt (by omega)]
    omega

/-- The magnitude of an `umod` by a nonzero divisor of magnitude `≤ 2^(w-1)` is below the
divisor (the result's `msb` is forced clear, so `bvAbs` is the identity on it). -/
private lemma bvAbs_umod_lt {w : ℕ} {a d : BitVec w} (hd : d.toNat ≠ 0)
    (hdle : d.toNat ≤ 2 ^ (w - 1)) :
    (bvAbs (a % d)).toNat < d.toNat := by
  have hum : (a % d).toNat = a.toNat % d.toNat := BitVec.toNat_umod
  have hlt : a.toNat % d.toNat < d.toNat := Nat.mod_lt _ (by omega)
  have hm : (a % d).msb = false := by
    rw [BitVec.msb_eq_decide]
    exact decide_eq_false (by omega)
  rw [bvAbs_toNat, hm, if_neg Bool.false_ne_true, hum]
  omega

/-- Core's four-case `srem`, repackaged on the magnitudes: the dividend's sign chooses the
result's sign, the inner division is always `|x| % |y|`. -/
private lemma srem_eq_bvAbs {w : ℕ} (x y : BitVec w) :
    x.srem y = if x.msb = true then -((bvAbs x) % (bvAbs y)) else (bvAbs x) % (bvAbs y) := by
  rw [BitVec.srem_eq]
  unfold bvAbs
  cases hmx : x.msb <;> cases hmy : y.msb <;> simp

/-- **The signed-remainder range core**: `|x.srem y| < |y|` for `y ≠ 0`, width-generic (used at
widths 64 and 32). Includes the wrap rows: `|intMin.srem (-1)| = 0 < 1`. -/
lemma bvAbs_srem_lt {w : ℕ} (hw : 0 < w) {x y : BitVec w} (hy : y ≠ 0) :
    (bvAbs (x.srem y)).toNat < (bvAbs y).toNat := by
  have hylt := y.isLt
  have h2w : 2 ^ (w - 1) * 2 = 2 ^ w := by
    rw [← pow_succ]
    congr 1
    omega
  have hyn : y.toNat ≠ 0 := by
    intro h
    apply hy
    rw [← BitVec.toNat_inj, h]
    simp
  have hd : (bvAbs y).toNat ≠ 0 ∧ (bvAbs y).toNat ≤ 2 ^ (w - 1) := by
    rw [bvAbs_toNat]
    cases hmy : y.msb
    · have hlt := BitVec.toNat_lt_of_msb_false hmy
      rw [if_neg Bool.false_ne_true]
      omega
    · have hge := BitVec.le_toNat_of_msb_true hmy
      rw [if_pos rfl, Nat.mod_eq_of_lt (by omega)]
      omega
  rw [srem_eq_bvAbs]
  cases hmx : x.msb
  · rw [if_neg Bool.false_ne_true]
    exact bvAbs_umod_lt hd.1 hd.2
  · rw [if_pos rfl]
    have hzlt : ((bvAbs x) % (bvAbs y)).toNat < 2 ^ (w - 1) := by
      have hum : ((bvAbs x) % (bvAbs y)).toNat = (bvAbs x).toNat % (bvAbs y).toNat :=
        BitVec.toNat_umod
      have hml : (bvAbs x).toNat % (bvAbs y).toNat < (bvAbs y).toNat :=
        Nat.mod_lt _ (by omega)
      omega
    rw [bvAbs_neg_toNat hw hzlt, BitVec.toNat_umod]
    exact Nat.mod_lt _ (by omega)

/-- `|x|` as the integer absolute value: `(bvAbs x).toNat = x.toInt.natAbs`. -/
lemma bvAbs_toNat_eq_natAbs {w : ℕ} (hw : 0 < w) (x : BitVec w) :
    (bvAbs x).toNat = x.toInt.natAbs := by
  have hx := x.isLt
  have h2w : 2 ^ (w - 1) * 2 = 2 ^ w := by
    rw [← pow_succ]
    congr 1
    omega
  have hti := BitVec.toInt_eq_toNat_cond x
  rw [bvAbs_toNat]
  cases hmx : x.msb
  · have hlt := BitVec.toNat_lt_of_msb_false hmx
    rw [if_neg Bool.false_ne_true]
    rw [if_pos (by omega : 2 * x.toNat < 2 ^ w)] at hti
    omega
  · have hge := BitVec.le_toNat_of_msb_true hmx
    rw [if_pos rfl]
    rw [if_neg (by omega : ¬2 * x.toNat < 2 ^ w)] at hti
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- `|sext₃₂→₆₄ x| = |x|` (sign extension preserves `toInt`, hence the magnitude). -/
lemma bvAbs_signExtend_toNat (x : BitVec 32) :
    (bvAbs (x.signExtend 64)).toNat = (bvAbs x).toNat := by
  rw [bvAbs_toNat_eq_natAbs (by norm_num : (0 : ℕ) < 64) (x.signExtend 64),
    bvAbs_toNat_eq_natAbs (by norm_num : (0 : ℕ) < 32) x,
    BitVec.toInt_signExtend_of_le (by norm_num : (32 : ℕ) ≤ 64)]

/-- The 64-bit sign of a sign-extended 32-bit value is its 32-bit sign. -/
lemma signExtend32_msb_eq (x : BitVec 32) : (x.signExtend 64).msb = x.msb := by
  have hx := x.isLt
  have hse : (x.signExtend 64).toNat = x.toNat + if x.msb then 2 ^ 64 - 2 ^ 32 else 0 := by
    rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth_of_le (by norm_num : (32 : ℕ) ≤ 64)]
  cases hmx : x.msb
  · rw [hmx, if_neg Bool.false_ne_true, Nat.add_zero] at hse
    have hlt := BitVec.toNat_lt_of_msb_false hmx
    rw [BitVec.msb_eq_decide, hse]
    exact decide_eq_false (by omega)
  · rw [hmx, if_pos rfl] at hse
    rw [BitVec.msb_eq_decide, hse]
    exact decide_eq_true (by omega)

/-- Truncating a sign extension back to 32 bits recovers the value. -/
lemma setWidth32_signExtend (x : BitVec 32) : (x.signExtend 64).setWidth 32 = x := by
  have hx := x.isLt
  have hse : (x.signExtend 64).toNat = x.toNat + if x.msb then 2 ^ 64 - 2 ^ 32 else 0 := by
    rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth_of_le (by norm_num : (32 : ℕ) ≤ 64)]
  rw [← BitVec.toNat_inj, BitVec.toNat_setWidth, hse]
  cases hmx : x.msb
  · rw [if_neg Bool.false_ne_true]
    omega
  · rw [if_pos rfl]
    omega

/-! ## Flag-sum arithmetic

The class-branch proofs below all open by turning a `FlagClasses` branch's zero/one flag cells into
the two- and four-term flag sums the `cComp`/`remBits`/`populateAbs*` `if`-conditions are stated on.
These lemmas are that step, over loose field elements; the `have` types at the call sites are
unchanged, so every downstream `rw`/`if_neg` still fires on the same syntactic condition. -/

omit [Fact (2 ^ 24 < p)] in
private lemma sum2_ne_one {a b : ZMod p} (ha : a = 0) (hb : b = 0) : ¬(a + b = 1) := by
  rw [ha, hb, add_zero]
  exact zero_ne_one

omit [Fact (2 ^ 24 < p)] in
private lemma sum4_ne_one {a b c d : ZMod p} (ha : a = 0) (hb : b = 0) (hc : c = 0) (hd : d = 0) :
    ¬(a + b + c + d = 1) := by
  rw [ha, hb, hc, hd, add_zero, add_zero, add_zero]
  exact zero_ne_one

omit [Fact (2 ^ 24 < p)] in
private lemma sum4_eq_one_of_head {a b c d : ZMod p} (hc : c = 0) (hd : d = 0) (h : a + b = 1) :
    a + b + c + d = 1 := by
  rw [hc, hd, add_zero, add_zero]
  exact h

omit [Fact (2 ^ 24 < p)] in
private lemma sum4_eq_one_of_tail {a b c d : ZMod p} (ha : a = 0) (hb : b = 0) (h : c + d = 1) :
    a + b + c + d = 1 := by
  rw [ha, hb, zero_add, zero_add]
  exact h

omit [Fact (2 ^ 24 < p)] in
private lemma cComp_eq_self {C : Word (ZMod p)} {f : Vector (ZMod p) 8}
    (h45 : ¬(f[4] + f[5] = 1)) (h67 : ¬(f[6] + f[7] = 1)) : cComp C f = C := by
  unfold cComp
  rw [if_neg h45, if_neg h67]

private lemma remCompBits_eq_remBits {B C : Word (ZMod p)} {f : Vector (ZMod p) 8}
    (h67 : ¬(f[6] + f[7] = 1)) : remCompBits B C f = remBits B C f := by
  simp only [remCompBits]
  rw [if_neg h67]

/-! ## Word-level glue -/

section
set_option linter.unusedSectionVars false

/-- A field element with zero `val` is zero. -/
private lemma eq_zero_of_val' {x : ZMod p} (h : x.val = 0) : x = 0 := by
  rw [← ZMod.natCast_zmod_val x, h, Nat.cast_zero]

/-- An `isU64` word's value is zero exactly when all four limbs are. -/
private lemma toNat_eq_zero_iff {w : Word (ZMod p)} (hw : w.isU64) :
    Word.toNat w = 0 ↔ (w[0] = 0 ∧ w[1] = 0 ∧ w[2] = 0 ∧ w[3] = 0) := by
  obtain ⟨h0, h1, h2, h3⟩ := Word.lt_cases_of_isU64 hw
  rw [Word.toNat_def]
  constructor
  · intro h
    exact ⟨eq_zero_of_val' (by omega), eq_zero_of_val' (by omega),
      eq_zero_of_val' (by omega), eq_zero_of_val' (by omega)⟩
  · rintro ⟨e0, e1, e2, e3⟩
    rw [e0, e1, e2, e3, ZMod.val_zero]
    norm_num

/-- `wordOfNat 0` is the zero word. -/
private lemma wordOfNat_zero : wordOfNat (p := p) 0 = #v[0, 0, 0, 0] := by
  simp [wordOfNat]

/-- `wordOfBits` round-trips through `Word.toNat`. -/
lemma wordOfBits_toNat (z : BitVec 64) : Word.toNat (wordOfBits (p := p) z) = z.toNat := by
  have h := Word.toBitVec64_toNat (wordOfBits_isU64 (p := p) z)
  rw [wordOfBits_toBitVec64] at h
  exact h.symm

/-- The low-32 truncation of an `isU64` word vanishes exactly when its low two limbs do. -/
private lemma toBitVec64_setWidth32_eq_zero_iff {C : Word (ZMod p)} (hC : C.isU64) :
    (Word.toBitVec64 C).setWidth 32 = 0 ↔ C[0] = 0 ∧ C[1] = 0 := by
  obtain ⟨h0, h1, h2, h3⟩ := Word.lt_cases_of_isU64 hC
  rw [← bv_toNat_eq_zero_iff, BitVec.toNat_setWidth, Word.toBitVec64_toNat hC, Word.toNat_def]
  constructor
  · intro h
    exact ⟨eq_zero_of_val' (by omega), eq_zero_of_val' (by omega)⟩
  · rintro ⟨e0, e1⟩
    rw [e0, e1, ZMod.val_zero]
    omega

/-- The sign-fill word `#v[w₀, w₁, m·65535, m·65535]` (with `m = populate_msb w₁`) is the 64-bit
sign extension of the low 32 bits — `Word.toBitVec64_signExtend_word` specialized to the
`U16MSBOperation.populate_msb` witness. -/
private lemma signFill_toBitVec64 {w : Word (ZMod p)} (hw : w.isU64) :
    Word.toBitVec64 (#v[w[0], w[1], U16MSBOperation.populate_msb w[1] * 65535,
        U16MSBOperation.populate_msb w[1] * 65535])
      = ((Word.toBitVec64 w).setWidth 32).signExtend 64 := by
  obtain ⟨h0, h1, h2, h3⟩ := Word.lt_cases_of_isU64 hw
  refine toBitVec64_signExtend_word _ ((Word.toBitVec64 w).setWidth 32)
    (U16MSBOperation.populate_msb w[1]) h0 h1 ?_ rfl rfl ?_
  · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
    unfold U16MSBOperation.populate_msb
    split_ifs with h
    · rw [show w[1].val / 32768 = 1 by omega]
      exact Nat.cast_one
    · rw [show w[1].val / 32768 = 0 by omega]
      exact Nat.cast_zero
  · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
    rw [BitVec.toNat_setWidth, Word.toBitVec64_toNat hw, Word.toNat_def]
    omega

/-- The zero-fill word `#v[w₀, w₁, 0, 0]` is the 64-bit zero extension of the low 32 bits. -/
private lemma zeroFill_toBitVec64 {w : Word (ZMod p)} (hw : w.isU64) :
    Word.toBitVec64 (#v[w[0], w[1], 0, 0])
      = ((Word.toBitVec64 w).setWidth 32).setWidth 64 := by
  obtain ⟨h0, h1, h2, h3⟩ := Word.lt_cases_of_isU64 hw
  have hU : Word.isU64 (#v[w[0], w[1], 0, 0] : Word (ZMod p)) := by
    apply Word.isU64_of_cases <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, ZMod.val_zero] <;>
      first
        | exact h0
        | exact h1
        | norm_num
  rw [← BitVec.toNat_inj, Word.toBitVec64_toNat hU, Word.toNat_def,
    BitVec.toNat_setWidth_of_le (by norm_num : (32 : ℕ) ≤ 64), BitVec.toNat_setWidth,
    Word.toBitVec64_toNat hw, Word.toNat_def]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, ZMod.val_zero]
  omega

/-- On the signed-word class the committed operand `b` is the sign extension of the raw read's
low 32 bits. -/
lemma bComp_toBitVec64_signedW {B : Word (ZMod p)} (hB : B.isU64) {f : Vector (ZMod p) 8}
    (hW : f[4] + f[5] = 1) :
    Word.toBitVec64 (bComp B f) = ((Word.toBitVec64 B).setWidth 32).signExtend 64 := by
  have hbc : bComp B f = #v[B[0], B[1], U16MSBOperation.populate_msb B[1] * 65535,
      U16MSBOperation.populate_msb B[1] * 65535] := by
    unfold bComp
    rw [if_pos hW]
  rw [hbc]
  exact signFill_toBitVec64 hB

/-- As `bComp_toBitVec64_signedW`, for the `c` operand. -/
lemma cComp_toBitVec64_signedW {C : Word (ZMod p)} (hC : C.isU64) {f : Vector (ZMod p) 8}
    (hW : f[4] + f[5] = 1) :
    Word.toBitVec64 (cComp C f) = ((Word.toBitVec64 C).setWidth 32).signExtend 64 := by
  have hcc : cComp C f = #v[C[0], C[1], U16MSBOperation.populate_msb C[1] * 65535,
      U16MSBOperation.populate_msb C[1] * 65535] := by
    unfold cComp
    rw [if_pos hW]
  rw [hcc]
  exact signFill_toBitVec64 hC

/-- On the unsigned-word class the committed operand `b` is the zero extension of the raw read's
low 32 bits. -/
lemma bComp_toBitVec64_unsignedW {B : Word (ZMod p)} (hB : B.isU64) {f : Vector (ZMod p) 8}
    (h45 : ¬(f[4] + f[5] = 1)) (h67 : f[6] + f[7] = 1) :
    Word.toBitVec64 (bComp B f) = ((Word.toBitVec64 B).setWidth 32).setWidth 64 := by
  have hbc : bComp B f = #v[B[0], B[1], 0, 0] := by
    unfold bComp
    rw [if_neg h45, if_pos h67]
  rw [hbc]
  exact zeroFill_toBitVec64 hB

/-- As `bComp_toBitVec64_unsignedW`, for the `c` operand. -/
lemma cComp_toBitVec64_unsignedW {C : Word (ZMod p)} (hC : C.isU64) {f : Vector (ZMod p) 8}
    (h45 : ¬(f[4] + f[5] = 1)) (h67 : f[6] + f[7] = 1) :
    Word.toBitVec64 (cComp C f) = ((Word.toBitVec64 C).setWidth 32).setWidth 64 := by
  have hcc : cComp C f = #v[C[0], C[1], 0, 0] := by
    unfold cComp
    rw [if_neg h45, if_pos h67]
  rw [hcc]
  exact zeroFill_toBitVec64 hC

/-- **The `AddOperation.populate` characterization**: the carry recursion is exactly the base-2^16
digit algorithm, so the populated word is `wordOfNat` of the wrapped `ℕ`-sum.  Carried no measured
cost: the former 1M ceiling here was ≥25× over; floor ≤ 40000. -/
lemma addPopulate_eq_wordOfNat {x y : Word (ZMod p)} (hx : x.isU64) (hy : y.isU64) :
    AddOperation.populate x y = wordOfNat ((Word.toNat x + Word.toNat y) % 2 ^ 64) := by
  obtain ⟨hx0, hx1, hx2, hx3⟩ := Word.lt_cases_of_isU64 hx
  obtain ⟨hy0, hy1, hy2, hy3⟩ := Word.lt_cases_of_isU64 hy
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    · simp only [AddOperation.populate, wordOfNat, Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ]
      congr 1
      rw [Word.toNat_def, Word.toNat_def]
      omega

/-- The populate-form of the gated `AddOperation` zero-value pins: a wrapped sum of `0` populates
the zero word. -/
private lemma addPopulate_eq_zero_of_sum {x y : Word (ZMod p)} (hx : x.isU64) (hy : y.isU64)
    (h : (Word.toNat x + Word.toNat y) % 2 ^ 64 = 0) :
    AddOperation.populate x y = #v[0, 0, 0, 0] := by
  rw [addPopulate_eq_wordOfNat hx hy, h, wordOfNat_zero]

/-! ## §1 The `is_c_0` characterization and the divide-by-zero block (E230–E244) -/

/-- The `is_c_0` result in if-form, on the computational operand's limbs. -/
lemma isC0_result_eq (C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    (isC0Witness C f).result
      = if (cComp C f)[0] = 0 ∧ (cComp C f)[1] = 0 ∧ (cComp C f)[2] = 0 ∧ (cComp C f)[3] = 0
        then 1 else 0 :=
  isZeroWord_populate_result (cComp C f)

/-- The `is_c_0` result is boolean. -/
lemma isC0_result_bool (C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    (isC0Witness C f).result = 0 ∨ (isC0Witness C f).result = 1 := by
  rw [isC0_result_eq]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The remainder-check multiplicity is boolean whenever the row gate is boolean. -/
lemma ltGate_bool (C : Word (ZMod p)) (f : Vector (ZMod p) 8) {ir : ZMod p}
    (hir : ir = 0 ∨ ir = 1) : ltGate ir C f = 0 ∨ ltGate ir C f = 1 := by
  unfold ltGate
  rcases hir with h0 | h1
  · left
    rw [h0, zero_mul]
  · rw [h1, one_mul]
    rcases isC0_result_bool C f with hz | ho
    · right
      rw [hz, sub_zero]
    · left
      rw [ho, sub_self]

/-- 64-bit classes: `cComp` is the zero word iff the raw `c` is zero as a 64-bit value. -/
lemma cComp_zero_iff_64 {C : Word (ZMod p)} (hC : C.isU64) {f : Vector (ZMod p) 8}
    (h45 : ¬(f[4] + f[5] = 1)) (h67 : ¬(f[6] + f[7] = 1)) :
    ((cComp C f)[0] = 0 ∧ (cComp C f)[1] = 0 ∧ (cComp C f)[2] = 0 ∧ (cComp C f)[3] = 0)
      ↔ Word.toBitVec64 C = 0 := by
  have hcc : cComp C f = C := cComp_eq_self h45 h67
  rw [hcc, ← bv_toNat_eq_zero_iff, Word.toBitVec64_toNat hC]
  exact (toNat_eq_zero_iff hC).symm

/-- Signed-word class: the sign-extension `cComp` is the zero word iff the low 32 bits of `c` are
zero (a zero low word forces a clear sign fill, and conversely). -/
lemma cComp_zero_iff_signedW {C : Word (ZMod p)} (hC : C.isU64) {f : Vector (ZMod p) 8}
    (hW : f[4] + f[5] = 1) :
    ((cComp C f)[0] = 0 ∧ (cComp C f)[1] = 0 ∧ (cComp C f)[2] = 0 ∧ (cComp C f)[3] = 0)
      ↔ (Word.toBitVec64 C).setWidth 32 = 0 := by
  have hcc : cComp C f = #v[C[0], C[1], U16MSBOperation.populate_msb C[1] * 65535,
      U16MSBOperation.populate_msb C[1] * 65535] := by
    unfold cComp
    rw [if_pos hW]
  rw [hcc, toBitVec64_setWidth32_eq_zero_iff hC]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  constructor
  · rintro ⟨e0, e1, _, _⟩
    exact ⟨e0, e1⟩
  · rintro ⟨e0, e1⟩
    have hm : U16MSBOperation.populate_msb C[1] = 0 := by
      rw [e1]
      unfold U16MSBOperation.populate_msb
      rw [ZMod.val_zero]
      norm_num
    exact ⟨e0, e1, by rw [hm, zero_mul], by rw [hm, zero_mul]⟩

/-- Unsigned-word class: the zero-extension `cComp` is the zero word iff the low 32 bits of `c`
are zero. -/
lemma cComp_zero_iff_unsignedW {C : Word (ZMod p)} (hC : C.isU64) {f : Vector (ZMod p) 8}
    (h45 : ¬(f[4] + f[5] = 1)) (h67 : f[6] + f[7] = 1) :
    ((cComp C f)[0] = 0 ∧ (cComp C f)[1] = 0 ∧ (cComp C f)[2] = 0 ∧ (cComp C f)[3] = 0)
      ↔ (Word.toBitVec64 C).setWidth 32 = 0 := by
  have hcc : cComp C f = #v[C[0], C[1], 0, 0] := by
    unfold cComp
    rw [if_neg h45, if_pos h67]
  rw [hcc, toBitVec64_setWidth32_eq_zero_iff hC]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  constructor
  · rintro ⟨e0, e1, _, _⟩
    exact ⟨e0, e1⟩
  · rintro ⟨e0, e1⟩
    exact ⟨e0, e1, trivial, trivial⟩

/-- A zero computational divisor lands every `quotBits` class in its divisor-zero branch, so the
quotient bit pattern is RISC-V's `allOnes`. Needs no flag facts: each branch tests its own class's
divisor-zero condition, which the matching `cComp_zero_iff_*` bridge supplies. -/
private lemma quotBits_allOnes_of_czero {B C : Word (ZMod p)} (hC : C.isU64)
    {f : Vector (ZMod p) 8}
    (hz : (cComp C f)[0] = 0 ∧ (cComp C f)[1] = 0 ∧ (cComp C f)[2] = 0 ∧ (cComp C f)[3] = 0) :
    quotBits B C f = BitVec.allOnes 64 := by
  by_cases h45 : f[4] + f[5] = 1
  · have hc32 : (Word.toBitVec64 C).setWidth 32 = 0 := (cComp_zero_iff_signedW hC h45).mp hz
    simp only [quotBits]
    rw [if_pos h45, if_pos hc32]
  · by_cases h67 : f[6] + f[7] = 1
    · have hc32 : (Word.toBitVec64 C).setWidth 32 = 0 :=
        (cComp_zero_iff_unsignedW hC h45 h67).mp hz
      simp only [quotBits]
      rw [if_neg h45, if_pos h67, if_pos hc32]
    · have hc : Word.toBitVec64 C = 0 := (cComp_zero_iff_64 hC h45 h67).mp hz
      by_cases h02 : f[0] + f[2] = 1
      · simp only [quotBits]
        rw [if_neg h45, if_neg h67, if_pos h02, if_pos hc]
      · simp only [quotBits]
        rw [if_neg h45, if_neg h67, if_neg h02, if_pos hc]

/-- On the 64-bit classes a zero divisor makes the remainder bit pattern the raw dividend
(both the signed and unsigned sub-branches). -/
private lemma remBits_eq_b_of_czero_64 {B C : Word (ZMod p)} {f : Vector (ZMod p) 8}
    (h45 : ¬(f[4] + f[5] = 1)) (h67 : ¬(f[6] + f[7] = 1)) (hc : Word.toBitVec64 C = 0) :
    remBits B C f = Word.toBitVec64 B := by
  by_cases h02 : f[0] + f[2] = 1
  · simp only [remBits]
    rw [if_neg h45, if_neg h67, if_pos h02, if_pos hc]
  · simp only [remBits]
    rw [if_neg h45, if_neg h67, if_neg h02, if_pos hc]

end

/-- **E230–E236 at the populate**: `is_c_0 = 1` pins every committed `quotient` limb to `65535`
(`q = allOnes 64` in every class). Needs no one-hot flag facts. -/
lemma isC0_one_quotient {B C : Word (ZMod p)} (hC : C.isU64) {f : Vector (ZMod p) 8}
    (h1 : (isC0Witness C f).result = 1) :
    ∀ k (hk : k < 4), (populateQuotient B C f)[k]'hk = 65535 := by
  have hz : (cComp C f)[0] = 0 ∧ (cComp C f)[1] = 0 ∧ (cComp C f)[2] = 0
      ∧ (cComp C f)[3] = 0 := by
    by_contra hN
    rw [isC0_result_eq, if_neg hN] at h1
    exact zero_ne_one h1
  have hquot := quotBits_allOnes_of_czero (B := B) hC hz
  intro k hk
  apply ZMod.val_injective
  rw [val_65535_zmod_p]
  unfold populateQuotient wordOfBits
  rw [hquot, wordOfNat_val _ k hk, BitVec.toNat_allOnes]
  interval_cases k <;> omega

set_option linter.unusedSimpArgs false in
/-- The one-hot flags split into the three operand-width shapes the comp links case on:
64-bit (no `W` flag), signed word (`divw`/`remw`), unsigned word (`divuw`/`remuw`). -/
private lemma width_cases {f : Vector (ZMod p) 8}
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1) (hf2 : f[2] = 0 ∨ f[2] = 1)
    (hf3 : f[3] = 0 ∨ f[3] = 1) (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1) :
    (¬(f[4] + f[5] = 1) ∧ ¬(f[6] + f[7] = 1))
      ∨ (f[4] + f[5] = 1 ∧ ¬(f[6] + f[7] = 1))
      ∨ (¬(f[4] + f[5] = 1) ∧ f[6] + f[7] = 1) := by
  rcases flags_cases hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ | ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ |
    ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ | ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ |
    ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ | ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ |
    ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ | ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ <;>
    rw [h4, h5, h6, h7] <;>
    norm_num

/-- **E238–E244 at the populate**: `is_c_0 = 1` pins the committed `remainder_comp` to the
committed operand `b` — divisor-zero remainders are the (class-appropriately extended)
dividend in every variant class. -/
lemma isC0_one_remComp {B C : Word (ZMod p)} (hB : B.isU64) (hC : C.isU64)
    {f : Vector (ZMod p) 8}
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1) (hf2 : f[2] = 0 ∨ f[2] = 1)
    (hf3 : f[3] = 0 ∨ f[3] = 1) (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1)
    (h1 : (isC0Witness C f).result = 1) :
    populateRemComp B C f = bComp B f := by
  have hz : (cComp C f)[0] = 0 ∧ (cComp C f)[1] = 0 ∧ (cComp C f)[2] = 0
      ∧ (cComp C f)[3] = 0 := by
    by_contra hN
    rw [isC0_result_eq, if_neg hN] at h1
    exact zero_ne_one h1
  rcases width_cases hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum with
    ⟨h45, h67⟩ | ⟨h45, h67⟩ | ⟨h45, h67⟩
  · -- 64-bit classes
    have hc : Word.toBitVec64 C = 0 := (cComp_zero_iff_64 hC h45 h67).mp hz
    have hrb : remBits B C f = Word.toBitVec64 B := remBits_eq_b_of_czero_64 h45 h67 hc
    have hrc : remCompBits B C f = remBits B C f := remCompBits_eq_remBits h67
    have hbc : bComp B f = B := by
      unfold bComp
      rw [if_neg h45, if_neg h67]
    unfold populateRemComp
    rw [hrc, hrb, hbc]
    exact word_eq_of_toBitVec64_eq (wordOfBits_isU64 _) hB (wordOfBits_toBitVec64 _)
  · -- signed word class
    have hc32 : (Word.toBitVec64 C).setWidth 32 = 0 := (cComp_zero_iff_signedW hC h45).mp hz
    have hrb : remBits B C f = ((Word.toBitVec64 B).setWidth 32).signExtend 64 := by
      simp only [remBits]
      rw [if_pos h45, if_pos hc32]
    have hrc : remCompBits B C f = remBits B C f := remCompBits_eq_remBits h67
    unfold populateRemComp
    rw [hrc, hrb]
    exact word_eq_of_toBitVec64_eq (wordOfBits_isU64 _) (bComp_isU64 hB f)
      (by rw [wordOfBits_toBitVec64, bComp_toBitVec64_signedW hB h45])
  · -- unsigned word class (the divisor-zero remainder is still the sign extension, but the
    -- computational form truncates it back to the zero extension = `bComp`)
    have hc32 : (Word.toBitVec64 C).setWidth 32 = 0 :=
      (cComp_zero_iff_unsignedW hC h45 h67).mp hz
    have hrb : remBits B C f = ((Word.toBitVec64 B).setWidth 32).signExtend 64 := by
      simp only [remBits]
      rw [if_neg h45, if_pos h67, if_pos hc32]
    have hrc : remCompBits B C f = ((Word.toBitVec64 B).setWidth 32).setWidth 64 := by
      simp only [remCompBits]
      rw [if_pos h67, hrb, setWidth32_signExtend]
    unfold populateRemComp
    rw [hrc]
    exact word_eq_of_toBitVec64_eq (wordOfBits_isU64 _) (bComp_isU64 hB f)
      (by rw [wordOfBits_toBitVec64, bComp_toBitVec64_unsignedW hB h45 h67])

/-! ## §2 Abs ties (E247–E268) and the gated `AddOperation` zero-values (E270–E284) -/

/-- **E247/E253/E259/E265 at the populate**: `c_neg = 0` collapses `abs_c` to the computational
operand (unsigned classes definitionally; signed classes because the clear sign cell forces a
clear 64-bit `msb`, making `bvAbs` the identity). -/
lemma absC_eq_of_not_neg {C : Word (ZMod p)} (hC : C.isU64) {f : Vector (ZMod p) 8}
    (hclass : FlagClasses f) (h : populateCNeg C f = 0) :
    populateAbsC C f = cComp C f := by
  obtain ⟨hC0, hC1, hC2, hC3⟩ := Word.lt_cases_of_isU64 hC
  rcases hclass with ⟨hcl, h4, h5, h6, h7⟩ | ⟨hcl, h0, h2, h6, h7⟩ | hcl
  · -- signed 64-bit class
    have hsig : f[0] + f[2] + f[4] + f[5] = 1 := sum4_eq_one_of_head h4 h5 hcl
    have hW : ¬(f[4] + f[5] + f[6] + f[7] = 1) := sum4_ne_one h4 h5 h6 h7
    have h45 : ¬(f[4] + f[5] = 1) := sum2_ne_one h4 h5
    have h67 : ¬(f[6] + f[7] = 1) := sum2_ne_one h6 h7
    have hcc : cComp C f = C := cComp_eq_self h45 h67
    have hm : U16MSBOperation.populate_msb C[3] = 0 := by
      unfold populateCNeg cMsbCell at h
      rw [hsig, one_mul, if_neg hW] at h
      exact h
    have hmsb : (Word.toBitVec64 C).msb = false := by
      rcases Bool.eq_false_or_eq_true (Word.toBitVec64 C).msb with hb | hb
      · exact absurd ((toBitVec64_msb_iff hC).mp hb)
          (Nat.not_le.mpr ((populate_msb_eq_zero_iff hC3).mp hm))
      · exact hb
    unfold populateAbsC
    rw [if_pos hsig, hcc]
    unfold bvAbs
    rw [if_neg (by rw [hmsb]; exact Bool.false_ne_true)]
    exact word_eq_of_toBitVec64_eq (wordOfBits_isU64 _) hC (wordOfBits_toBitVec64 _)
  · -- signed word class
    have hsig : f[0] + f[2] + f[4] + f[5] = 1 := sum4_eq_one_of_tail h0 h2 hcl
    have hW : f[4] + f[5] + f[6] + f[7] = 1 := sum4_eq_one_of_head h6 h7 hcl
    have hm : U16MSBOperation.populate_msb C[1] = 0 := by
      unfold populateCNeg cMsbCell at h
      rw [hsig, one_mul, if_pos hW] at h
      exact h
    have hcc : cComp C f = #v[C[0], C[1], U16MSBOperation.populate_msb C[1] * 65535,
        U16MSBOperation.populate_msb C[1] * 65535] := by
      unfold cComp
      rw [if_pos hcl]
    have hlimb3 : (cComp C f)[3] = 0 := by
      rw [hcc]
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
      rw [hm, zero_mul]
    have hmsb : (Word.toBitVec64 (cComp C f)).msb = false := by
      rcases Bool.eq_false_or_eq_true (Word.toBitVec64 (cComp C f)).msb with hb | hb
      · exfalso
        have hge := (toBitVec64_msb_iff (cComp_isU64 hC f)).mp hb
        rw [hlimb3, ZMod.val_zero] at hge
        omega
      · exact hb
    unfold populateAbsC
    rw [if_pos hsig]
    unfold bvAbs
    rw [if_neg (by rw [hmsb]; exact Bool.false_ne_true)]
    exact word_eq_of_toBitVec64_eq (wordOfBits_isU64 _) (cComp_isU64 hC f)
      (wordOfBits_toBitVec64 _)
  · -- unsigned classes: definitional
    have hsig : ¬(f[0] + f[2] + f[4] + f[5] = 1) := by rw [hcl]; exact zero_ne_one
    unfold populateAbsC
    rw [if_neg hsig]

/-- **E250/E256/E262/E268 at the populate**: `rem_neg = 0` collapses `abs_remainder` to the
computational remainder (same shape as `absC_eq_of_not_neg`; on the word classes the
sign-extension structure of `remBits` routes the clear limb-1 sign cell to a clear 64-bit
`msb`). -/
lemma absRem_eq_of_not_neg {B C : Word (ZMod p)} {f : Vector (ZMod p) 8}
    (hclass : FlagClasses f) (h : populateRemNeg B C f = 0) :
    populateAbsRem B C f = populateRemComp B C f := by
  obtain ⟨hR0, hR1, hR2, hR3⟩ := Word.lt_cases_of_isU64 (populateRemainder_isU64 B C f)
  rcases hclass with ⟨hcl, h4, h5, h6, h7⟩ | ⟨hcl, h0, h2, h6, h7⟩ | hcl
  · -- signed 64-bit class
    have hsig : f[0] + f[2] + f[4] + f[5] = 1 := sum4_eq_one_of_head h4 h5 hcl
    have hW : ¬(f[4] + f[5] + f[6] + f[7] = 1) := sum4_ne_one h4 h5 h6 h7
    have h67 : ¬(f[6] + f[7] = 1) := sum2_ne_one h6 h7
    have hm : U16MSBOperation.populate_msb (populateRemainder B C f)[3] = 0 := by
      unfold populateRemNeg remMsbCell at h
      rw [hsig, one_mul, if_neg hW] at h
      exact h
    have hmsb : (remBits B C f).msb = false := by
      rcases Bool.eq_false_or_eq_true (remBits B C f).msb with hb | hb
      · exfalso
        have hTB : Word.toBitVec64 (populateRemainder B C f) = remBits B C f :=
          wordOfBits_toBitVec64 _
        have hge := (toBitVec64_msb_iff (populateRemainder_isU64 B C f)).mp
          (by rw [hTB]; exact hb)
        have hlt := (populate_msb_eq_zero_iff hR3).mp hm
        omega
      · exact hb
    have hrc : remCompBits B C f = remBits B C f := remCompBits_eq_remBits h67
    unfold populateAbsRem
    rw [if_pos hsig]
    unfold populateRemComp
    rw [hrc]
    unfold bvAbs
    rw [if_neg (by rw [hmsb]; exact Bool.false_ne_true)]
  · -- signed word class
    have hsig : f[0] + f[2] + f[4] + f[5] = 1 := sum4_eq_one_of_tail h0 h2 hcl
    have hW : f[4] + f[5] + f[6] + f[7] = 1 := sum4_eq_one_of_head h6 h7 hcl
    have h67 : ¬(f[6] + f[7] = 1) := sum2_ne_one h6 h7
    have hm : U16MSBOperation.populate_msb (populateRemainder B C f)[1] = 0 := by
      unfold populateRemNeg remMsbCell at h
      rw [hsig, one_mul, if_pos hW] at h
      exact h
    have hr1lt : (remBits B C f).toNat / 2 ^ 16 % 2 ^ 16 < 32768 := by
      rw [← populateRemainder_limb1_val]
      exact (populate_msb_eq_zero_iff hR1).mp hm
    have hshape : ∃ x : BitVec 32, remBits B C f = x.signExtend 64 := by
      simp only [remBits]
      rw [if_pos hcl]
      split
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    obtain ⟨x, hx⟩ := hshape
    have hxm : x.msb = false := by
      rcases Bool.eq_false_or_eq_true x.msb with hb | hb
      · exfalso
        rw [hx] at hr1lt
        exact absurd hr1lt (Nat.not_lt.mpr (signExtend_toNat_limb1_ge hb))
      · exact hb
    have hmsb : (remBits B C f).msb = false := by
      rw [hx, signExtend32_msb_eq]
      exact hxm
    have hrc : remCompBits B C f = remBits B C f := remCompBits_eq_remBits h67
    unfold populateAbsRem
    rw [if_pos hsig]
    unfold populateRemComp
    rw [hrc]
    unfold bvAbs
    rw [if_neg (by rw [hmsb]; exact Bool.false_ne_true)]
  · -- unsigned classes: definitional
    have hsig : ¬(f[0] + f[2] + f[4] + f[5] = 1) := by rw [hcl]; exact zero_ne_one
    unfold populateAbsRem
    rw [if_neg hsig]

/-- **E270–E276 at the populate**: when the `abs_c_alu_event` fires (`c_neg · is_real = 1`) the
populated `AddOperation` value word `c + abs_c` is zero — the live `abs_c` is the two's-complement
negation, so the `ℕ`-sum is exactly `2^64` (or `0` for `c = 0`, which cannot occur live but is
covered by the wrap anyway). -/
lemma wCneg_value_zero {C : Word (ZMod p)} (hC : C.isU64) {ir : ZMod p}
    {f : Vector (ZMod p) 8} (hclass : FlagClasses f)
    (h : populateCNeg C f * ir = 1) :
    AddOperation.populate (cComp C f) (populateAbsC C f) = #v[0, 0, 0, 0] := by
  obtain ⟨hC0, hC1, hC2, hC3⟩ := Word.lt_cases_of_isU64 hC
  have hcn1 : populateCNeg C f = 1 := by
    rcases populateCNeg_bool hC (sig_bool_of_class hclass) with h0 | h1
    · exfalso
      rw [h0, zero_mul] at h
      exact zero_ne_one h
    · exact h1
  have hsig : f[0] + f[2] + f[4] + f[5] = 1 := by
    rcases sig_bool_of_class hclass with hs | hs
    · exfalso
      rw [populateCNeg_def, hs, zero_mul] at hcn1
      exact zero_ne_one hcn1
    · exact hs
  have hmsb : (Word.toBitVec64 (cComp C f)).msb = true := by
    rcases hclass with ⟨hcl, h4, h5, h6, h7⟩ | ⟨hcl, h0, h2, h6, h7⟩ | hcl
    · -- signed 64-bit class
      have hW : ¬(f[4] + f[5] + f[6] + f[7] = 1) := sum4_ne_one h4 h5 h6 h7
      have h45 : ¬(f[4] + f[5] = 1) := sum2_ne_one h4 h5
      have h67 : ¬(f[6] + f[7] = 1) := sum2_ne_one h6 h7
      have hm1 : U16MSBOperation.populate_msb C[3] = 1 := by
        unfold populateCNeg cMsbCell at hcn1
        rw [hsig, one_mul, if_neg hW] at hcn1
        exact hcn1
      have hcc : cComp C f = C := cComp_eq_self h45 h67
      rw [hcc]
      exact (toBitVec64_msb_iff hC).mpr ((populate_msb_eq_one_iff hC3).mp hm1)
    · -- signed word class
      have hW : f[4] + f[5] + f[6] + f[7] = 1 := sum4_eq_one_of_head h6 h7 hcl
      have hm1 : U16MSBOperation.populate_msb C[1] = 1 := by
        unfold populateCNeg cMsbCell at hcn1
        rw [hsig, one_mul, if_pos hW] at hcn1
        exact hcn1
      have hcc : cComp C f = #v[C[0], C[1], U16MSBOperation.populate_msb C[1] * 65535,
          U16MSBOperation.populate_msb C[1] * 65535] := by
        unfold cComp
        rw [if_pos hcl]
      have hlimb3 : (cComp C f)[3] = (65535 : ZMod p) := by
        rw [hcc]
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ]
        rw [hm1, one_mul]
      apply (toBitVec64_msb_iff (cComp_isU64 hC f)).mpr
      rw [hlimb3, val_65535_zmod_p]
      norm_num
    · -- unsigned classes: contradiction
      exfalso
      rw [populateCNeg_zero_of_unsigned C hcl] at hcn1
      exact zero_ne_one hcn1
  have habs : populateAbsC C f = wordOfBits (-(Word.toBitVec64 (cComp C f))) := by
    unfold populateAbsC
    rw [if_pos hsig]
    unfold bvAbs
    rw [if_pos hmsb]
  apply addPopulate_eq_zero_of_sum (cComp_isU64 hC f) (populateAbsC_isU64 hC f)
  rw [habs, wordOfBits_toNat, BitVec.toNat_neg,
    ← Word.toBitVec64_toNat (cComp_isU64 hC f)]
  have hlt := (Word.toBitVec64 (cComp C f)).isLt
  omega

/-- **E278–E284 at the populate**: when the `abs_rem_alu_event` fires (`rem_neg · is_real = 1`)
the populated `AddOperation` value word `remainder + abs_remainder` is zero. The witness adds the
**writeback** `remainder` (not `remainder_comp`); on the signed classes where the gate can fire
they share the bit pattern `remBits`, so the wrap argument is identical. -/
lemma wRneg_value_zero {B C : Word (ZMod p)} {ir : ZMod p} {f : Vector (ZMod p) 8}
    (hclass : FlagClasses f) (h : populateRemNeg B C f * ir = 1) :
    AddOperation.populate (populateRemainder B C f) (populateAbsRem B C f) = #v[0, 0, 0, 0] := by
  obtain ⟨hR0, hR1, hR2, hR3⟩ := Word.lt_cases_of_isU64 (populateRemainder_isU64 B C f)
  have hrn1 : populateRemNeg B C f = 1 := by
    rcases populateRemNeg_bool B C (sig_bool_of_class hclass) with h0 | h1
    · exfalso
      rw [h0, zero_mul] at h
      exact zero_ne_one h
    · exact h1
  have hsig : f[0] + f[2] + f[4] + f[5] = 1 := by
    rcases sig_bool_of_class hclass with hs | hs
    · exfalso
      rw [populateRemNeg_def, hs, zero_mul] at hrn1
      exact zero_ne_one hrn1
    · exact hs
  have hmsb : (remBits B C f).msb = true := by
    rcases hclass with ⟨hcl, h4, h5, h6, h7⟩ | ⟨hcl, h0, h2, h6, h7⟩ | hcl
    · -- signed 64-bit class
      have hW : ¬(f[4] + f[5] + f[6] + f[7] = 1) := sum4_ne_one h4 h5 h6 h7
      have hm1 : U16MSBOperation.populate_msb (populateRemainder B C f)[3] = 1 := by
        unfold populateRemNeg remMsbCell at hrn1
        rw [hsig, one_mul, if_neg hW] at hrn1
        exact hrn1
      have hTB : Word.toBitVec64 (populateRemainder B C f) = remBits B C f :=
        wordOfBits_toBitVec64 _
      rw [← hTB]
      exact (toBitVec64_msb_iff (populateRemainder_isU64 B C f)).mpr
        ((populate_msb_eq_one_iff hR3).mp hm1)
    · -- signed word class
      have hW : f[4] + f[5] + f[6] + f[7] = 1 := sum4_eq_one_of_head h6 h7 hcl
      have hm1 : U16MSBOperation.populate_msb (populateRemainder B C f)[1] = 1 := by
        unfold populateRemNeg remMsbCell at hrn1
        rw [hsig, one_mul, if_pos hW] at hrn1
        exact hrn1
      have hge : 32768 ≤ (remBits B C f).toNat / 2 ^ 16 % 2 ^ 16 := by
        rw [← populateRemainder_limb1_val]
        exact (populate_msb_eq_one_iff hR1).mp hm1
      have hshape : ∃ x : BitVec 32, remBits B C f = x.signExtend 64 := by
        simp only [remBits]
        rw [if_pos hcl]
        split
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
      obtain ⟨x, hx⟩ := hshape
      have hxm : x.msb = true := by
        rcases Bool.eq_false_or_eq_true x.msb with hb | hb
        · exact hb
        · exfalso
          rw [hx] at hge
          exact absurd hge (Nat.not_le.mpr (signExtend_toNat_limb1_lt hb))
      rw [hx, signExtend32_msb_eq]
      exact hxm
    · -- unsigned classes: contradiction with the signed-class sum
      exfalso
      rw [hcl] at hsig
      exact zero_ne_one hsig
  have habs : populateAbsRem B C f = wordOfBits (-(remBits B C f)) := by
    unfold populateAbsRem
    rw [if_pos hsig]
    unfold bvAbs
    rw [if_pos hmsb]
  apply addPopulate_eq_zero_of_sum (populateRemainder_isU64 B C f) (populateAbsRem_isU64 B C f)
  have hpr : Word.toNat (populateRemainder B C f) = (remBits B C f).toNat := wordOfBits_toNat _
  rw [habs, wordOfBits_toNat, BitVec.toNat_neg, hpr]
  have hlt := (remBits B C f).isLt
  omega

/-! ## §3 The `max(1, |c|)` formula (E299–E305) -/

set_option linter.unusedSectionVars false in
/-- The `|c| = 0 ↔ cComp = 0` bridge: `bvAbs` preserves zeroness, so the committed `abs_c`
vanishes exactly when the computational operand does. -/
private lemma absC_toNat_zero_iff {C : Word (ZMod p)} (hC : C.isU64) (f : Vector (ZMod p) 8) :
    Word.toNat (populateAbsC C f) = 0 ↔ Word.toNat (cComp C f) = 0 := by
  unfold populateAbsC
  split
  · rw [wordOfBits_toNat, bv_toNat_eq_zero_iff, bvAbs_eq_zero_iff, ← bv_toNat_eq_zero_iff,
      Word.toBitVec64_toNat (cComp_isU64 hC f)]
  · exact Iff.rfl

/-- **E299 at the populate**: limb 0 of `max_abs_c_or_1` in the constraint's selected form
`is_c_0 + (1 − is_c_0) · abs_c[0]`. -/
lemma maxAbs_limb0 {C : Word (ZMod p)} (hC : C.isU64) (f : Vector (ZMod p) 8) :
    (populateMaxAbsCOr1 C f)[0]
      = (isC0Witness C f).result
        + (1 - (isC0Witness C f).result) * (populateAbsC C f)[0] := by
  have hres := isC0_result_eq C f
  have heq : populateMaxAbsCOr1 C f
      = if Word.toNat (populateAbsC C f) = 0 then (#v[1, 0, 0, 0] : Word (ZMod p))
        else populateAbsC C f := rfl
  by_cases h : Word.toNat (populateAbsC C f) = 0
  · have hlimbs := (toNat_eq_zero_iff (cComp_isU64 hC f)).mp ((absC_toNat_zero_iff hC f).mp h)
    rw [heq, if_pos h, hres, if_pos hlimbs]
    simp
  · have hlimbs : ¬((cComp C f)[0] = 0 ∧ (cComp C f)[1] = 0 ∧ (cComp C f)[2] = 0
        ∧ (cComp C f)[3] = 0) :=
      fun hh => h ((absC_toNat_zero_iff hC f).mpr ((toNat_eq_zero_iff (cComp_isU64 hC f)).mpr hh))
    rw [heq, if_neg h, hres, if_neg hlimbs]
    simp

/-- **E300–E302 at the populate**: limbs 1–3 of `max_abs_c_or_1` in the constraint's selected
form `(1 − is_c_0) · abs_c[k]`. -/
lemma maxAbs_limbk {C : Word (ZMod p)} (hC : C.isU64) (f : Vector (ZMod p) 8)
    (k : ℕ) (hk1 : 1 ≤ k) (hk : k < 4) :
    (populateMaxAbsCOr1 C f)[k]'hk
      = (1 - (isC0Witness C f).result) * ((populateAbsC C f)[k]'hk) := by
  have hres := isC0_result_eq C f
  have heq : populateMaxAbsCOr1 C f
      = if Word.toNat (populateAbsC C f) = 0 then (#v[1, 0, 0, 0] : Word (ZMod p))
        else populateAbsC C f := rfl
  by_cases h : Word.toNat (populateAbsC C f) = 0
  · have hlimbs := (toNat_eq_zero_iff (cComp_isU64 hC f)).mp ((absC_toNat_zero_iff hC f).mp h)
    rw [heq, if_pos h, hres, if_pos hlimbs]
    interval_cases k <;> simp
  · have hlimbs : ¬((cComp C f)[0] = 0 ∧ (cComp C f)[1] = 0 ∧ (cComp C f)[2] = 0
        ∧ (cComp C f)[3] = 0) :=
      fun hh => h ((absC_toNat_zero_iff hC f).mpr ((toNat_eq_zero_iff (cComp_isU64 hC f)).mpr hh))
    rw [heq, if_neg h, hres, if_neg hlimbs]
    simp

/-! ## §4 The remainder range fact (E307) -/

section
set_option linter.unusedSectionVars false

/-- The populate-level limb scan: for `isU64` words in strict `toNat` order, the
`U16CompareOperation` bit on the most-significant differing limb pair is `1`. Routed through
`LtOperationUnsigned.result_semantic` at the fully-populated struct. -/
private lemma comparison_bit_one {a b : Word (ZMod p)} (ha : a.isU64) (hb : b.isU64)
    (h : Word.toNat a < Word.toNat b) :
    U16CompareOperation.populate_bit (LtOperationUnsigned.comparisonLimbsWitness a b)[0]
      (LtOperationUnsigned.comparisonLimbsWitness a b)[1] = 1 := by
  have hsem := (LtOperationUnsigned.result_semantic
      (input := ⟨a, b, LtOperationUnsigned.populate a b, 1⟩) ha hb rfl
      LtOperationUnsigned.spec_populate).1
  rw [if_pos h] at hsem
  exact hsem

/-- Unsigned 64-bit core: `b % c < c = |c|`. -/
private lemma absRem_lt_absC_u64 {B C : Word (ZMod p)} (hC : C.isU64) {f : Vector (ZMod p) 8}
    (h0 : f[0] = 0) (h2 : f[2] = 0) (h4 : f[4] = 0) (h5 : f[5] = 0) (h6 : f[6] = 0)
    (h7 : f[7] = 0) (hcz : Word.toBitVec64 C ≠ 0) :
    Word.toNat (populateAbsRem B C f) < Word.toNat (populateAbsC C f) := by
  have h45 : ¬(f[4] + f[5] = 1) := sum2_ne_one h4 h5
  have h67 : ¬(f[6] + f[7] = 1) := sum2_ne_one h6 h7
  have h02 : ¬(f[0] + f[2] = 1) := sum2_ne_one h0 h2
  have hsig : ¬(f[0] + f[2] + f[4] + f[5] = 1) := sum4_ne_one h0 h2 h4 h5
  have hcc : cComp C f = C := cComp_eq_self h45 h67
  have habsC : populateAbsC C f = C := by
    unfold populateAbsC
    rw [if_neg hsig, hcc]
  have hrb : remBits B C f = (Word.toBitVec64 B).umod (Word.toBitVec64 C) := by
    simp only [remBits]
    rw [if_neg h45, if_neg h67, if_neg h02, if_neg hcz]
  have hrc : remCompBits B C f = remBits B C f := remCompBits_eq_remBits h67
  have habsR : populateAbsRem B C f
      = wordOfBits ((Word.toBitVec64 B).umod (Word.toBitVec64 C)) := by
    unfold populateAbsRem
    rw [if_neg hsig]
    unfold populateRemComp
    rw [hrc, hrb]
  have hcn : (Word.toBitVec64 C).toNat ≠ 0 :=
    fun hh => hcz ((bv_toNat_eq_zero_iff _).mp hh)
  rw [habsR, habsC, wordOfBits_toNat, toNat_umod', ← Word.toBitVec64_toNat hC]
  exact Nat.mod_lt _ (by omega)

/-- Signed 64-bit core: `|b.srem c| < |c|` via `bvAbs_srem_lt`. -/
private lemma absRem_lt_absC_s64 {B C : Word (ZMod p)} {f : Vector (ZMod p) 8}
    (hcl : f[0] + f[2] = 1) (h4 : f[4] = 0) (h5 : f[5] = 0) (h6 : f[6] = 0) (h7 : f[7] = 0)
    (hcz : Word.toBitVec64 C ≠ 0) :
    Word.toNat (populateAbsRem B C f) < Word.toNat (populateAbsC C f) := by
  have h45 : ¬(f[4] + f[5] = 1) := sum2_ne_one h4 h5
  have h67 : ¬(f[6] + f[7] = 1) := sum2_ne_one h6 h7
  have hsig : f[0] + f[2] + f[4] + f[5] = 1 := sum4_eq_one_of_head h4 h5 hcl
  have hcc : cComp C f = C := cComp_eq_self h45 h67
  have habsC : populateAbsC C f = wordOfBits (bvAbs (Word.toBitVec64 C)) := by
    unfold populateAbsC
    rw [if_pos hsig, hcc]
  have hrb : remBits B C f = (Word.toBitVec64 B).srem (Word.toBitVec64 C) := by
    simp only [remBits]
    rw [if_neg h45, if_neg h67, if_pos hcl, if_neg hcz]
  have habsR : populateAbsRem B C f
      = wordOfBits (bvAbs ((Word.toBitVec64 B).srem (Word.toBitVec64 C))) := by
    unfold populateAbsRem
    rw [if_pos hsig, hrb]
  rw [habsR, habsC, wordOfBits_toNat, wordOfBits_toNat]
  exact bvAbs_srem_lt (by norm_num) hcz

/-- Signed-word core: both abs words are sign extensions of 32-bit magnitudes, so the comparison
drops to width 32 (`bvAbs_signExtend_toNat`) where `bvAbs_srem_lt` closes it. -/
private lemma absRem_lt_absC_sW {B C : Word (ZMod p)} (hC : C.isU64) {f : Vector (ZMod p) 8}
    (hcl : f[4] + f[5] = 1) (h0 : f[0] = 0) (h2 : f[2] = 0)
    (hcz : (Word.toBitVec64 C).setWidth 32 ≠ 0) :
    Word.toNat (populateAbsRem B C f) < Word.toNat (populateAbsC C f) := by
  have hsig : f[0] + f[2] + f[4] + f[5] = 1 := sum4_eq_one_of_tail h0 h2 hcl
  have habsC : populateAbsC C f
      = wordOfBits (bvAbs (((Word.toBitVec64 C).setWidth 32).signExtend 64)) := by
    unfold populateAbsC
    rw [if_pos hsig, cComp_toBitVec64_signedW hC hcl]
  have hrb : remBits B C f = (((Word.toBitVec64 B).setWidth 32).srem
      ((Word.toBitVec64 C).setWidth 32)).signExtend 64 := by
    simp only [remBits]
    rw [if_pos hcl, if_neg hcz]
  have habsR : populateAbsRem B C f
      = wordOfBits (bvAbs ((((Word.toBitVec64 B).setWidth 32).srem
          ((Word.toBitVec64 C).setWidth 32)).signExtend 64)) := by
    unfold populateAbsRem
    rw [if_pos hsig, hrb]
  rw [habsR, habsC, wordOfBits_toNat, wordOfBits_toNat, bvAbs_signExtend_toNat,
    bvAbs_signExtend_toNat]
  exact bvAbs_srem_lt (by norm_num) hcz

/-- Unsigned-word core: `b32 % c32 < c32`, with the computational remainder the zero extension
of the 32-bit `umod` (the sign extension truncated back). -/
private lemma absRem_lt_absC_uW {B C : Word (ZMod p)} (hC : C.isU64) {f : Vector (ZMod p) 8}
    (hcl : f[6] + f[7] = 1) (h0 : f[0] = 0) (h2 : f[2] = 0) (h4 : f[4] = 0) (h5 : f[5] = 0)
    (hcz : (Word.toBitVec64 C).setWidth 32 ≠ 0) :
    Word.toNat (populateAbsRem B C f) < Word.toNat (populateAbsC C f) := by
  have h45 : ¬(f[4] + f[5] = 1) := sum2_ne_one h4 h5
  have hsig : ¬(f[0] + f[2] + f[4] + f[5] = 1) := sum4_ne_one h0 h2 h4 h5
  have habsC : populateAbsC C f = cComp C f := by
    unfold populateAbsC
    rw [if_neg hsig]
  have hrb : remBits B C f = (((Word.toBitVec64 B).setWidth 32).umod
      ((Word.toBitVec64 C).setWidth 32)).signExtend 64 := by
    simp only [remBits]
    rw [if_neg h45, if_pos hcl, if_neg hcz]
  have hrc : remCompBits B C f = (((Word.toBitVec64 B).setWidth 32).umod
      ((Word.toBitVec64 C).setWidth 32)).setWidth 64 := by
    simp only [remCompBits]
    rw [if_pos hcl, hrb, setWidth32_signExtend]
  have habsR : populateAbsRem B C f = wordOfBits ((((Word.toBitVec64 B).setWidth 32).umod
      ((Word.toBitVec64 C).setWidth 32)).setWidth 64) := by
    unfold populateAbsRem
    rw [if_neg hsig]
    unfold populateRemComp
    rw [hrc]
  have htc : Word.toNat (cComp C f) = ((Word.toBitVec64 C).setWidth 32).toNat := by
    rw [← Word.toBitVec64_toNat (cComp_isU64 hC f), cComp_toBitVec64_unsignedW hC h45 hcl,
      BitVec.toNat_setWidth_of_le (by norm_num : (32 : ℕ) ≤ 64)]
  have hcn : ((Word.toBitVec64 C).setWidth 32).toNat ≠ 0 :=
    fun hh => hcz ((bv_toNat_eq_zero_iff _).mp hh)
  rw [habsR, habsC, wordOfBits_toNat,
    BitVec.toNat_setWidth_of_le (by norm_num : (32 : ℕ) ≤ 64), toNat_umod', htc]
  exact Nat.mod_lt _ (by omega)

end

/-- **E307 at the populate**: a live remainder-check gate (`is_real · (1 − is_c_0) = 1`) makes
the composed `U16CompareOperation` bit `1` — the populated `|remainder|` is strictly below
`max(1, |c|)` in every variant class (divisor nonzero in-class because `is_c_0 = 0`).
Statement deviation: no `hB : B.isU64` is needed — the populated `abs_remainder` is `isU64`
unconditionally (`populateAbsRem_isU64`). -/
lemma ltBit_one_of_gate {B C : Word (ZMod p)} (hC : C.isU64) {ir : ZMod p}
    {f : Vector (ZMod p) 8}
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1) (hf2 : f[2] = 0 ∨ f[2] = 1)
    (hf3 : f[3] = 0 ∨ f[3] = 1) (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1)
    (hgate : ltGate ir C f = 1) :
    (ltBitWitness ir B C f)[0] = 1 := by
  have hr0 : (isC0Witness C f).result = 0 := by
    rcases isC0_result_bool C f with h | h
    · exact h
    · exfalso
      unfold ltGate at hgate
      rw [h, sub_self, mul_zero] at hgate
      exact zero_ne_one hgate
  have hP : ¬((cComp C f)[0] = 0 ∧ (cComp C f)[1] = 0 ∧ (cComp C f)[2] = 0
      ∧ (cComp C f)[3] = 0) := by
    intro hcz
    rw [isC0_result_eq, if_pos hcz] at hr0
    exact one_ne_zero hr0
  have hmax : populateMaxAbsCOr1 C f = populateAbsC C f := by
    have heq : populateMaxAbsCOr1 C f
        = if Word.toNat (populateAbsC C f) = 0 then (#v[1, 0, 0, 0] : Word (ZMod p))
          else populateAbsC C f := rfl
    rw [heq, if_neg fun hzz =>
      hP ((toNat_eq_zero_iff (cComp_isU64 hC f)).mp ((absC_toNat_zero_iff hC f).mp hzz))]
  have hcore : Word.toNat (populateAbsRem B C f) < Word.toNat (populateAbsC C f) := by
    rcases flags_cases hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum with
      ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ | ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ |
      ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ | ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ |
      ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ | ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ |
      ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ | ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
    · -- div
      refine absRem_lt_absC_s64 (by rw [h0, h2, add_zero]) h4 h5 h6 h7 ?_
      exact fun hc => hP ((cComp_zero_iff_64 hC
        (by rw [h4, h5, add_zero]; exact zero_ne_one)
        (by rw [h6, h7, add_zero]; exact zero_ne_one)).mpr hc)
    · -- divu
      refine absRem_lt_absC_u64 hC h0 h2 h4 h5 h6 h7 ?_
      exact fun hc => hP ((cComp_zero_iff_64 hC
        (by rw [h4, h5, add_zero]; exact zero_ne_one)
        (by rw [h6, h7, add_zero]; exact zero_ne_one)).mpr hc)
    · -- rem
      refine absRem_lt_absC_s64 (by rw [h0, h2, zero_add]) h4 h5 h6 h7 ?_
      exact fun hc => hP ((cComp_zero_iff_64 hC
        (by rw [h4, h5, add_zero]; exact zero_ne_one)
        (by rw [h6, h7, add_zero]; exact zero_ne_one)).mpr hc)
    · -- remu
      refine absRem_lt_absC_u64 hC h0 h2 h4 h5 h6 h7 ?_
      exact fun hc => hP ((cComp_zero_iff_64 hC
        (by rw [h4, h5, add_zero]; exact zero_ne_one)
        (by rw [h6, h7, add_zero]; exact zero_ne_one)).mpr hc)
    · -- divw
      refine absRem_lt_absC_sW hC (by rw [h4, h5, add_zero]) h0 h2 ?_
      exact fun hc => hP ((cComp_zero_iff_signedW hC (by rw [h4, h5, add_zero])).mpr hc)
    · -- remw
      refine absRem_lt_absC_sW hC (by rw [h4, h5, zero_add]) h0 h2 ?_
      exact fun hc => hP ((cComp_zero_iff_signedW hC (by rw [h4, h5, zero_add])).mpr hc)
    · -- divuw
      refine absRem_lt_absC_uW hC (by rw [h6, h7, add_zero]) h0 h2 h4 h5 ?_
      exact fun hc => hP ((cComp_zero_iff_unsignedW hC
        (by rw [h4, h5, add_zero]; exact zero_ne_one)
        (by rw [h6, h7, add_zero])).mpr hc)
    · -- remuw
      refine absRem_lt_absC_uW hC (by rw [h6, h7, zero_add]) h0 h2 h4 h5 ?_
      exact fun hc => hP ((cComp_zero_iff_unsignedW hC
        (by rw [h4, h5, add_zero]; exact zero_ne_one)
        (by rw [h6, h7, zero_add])).mpr hc)
  have hclw : ltClWitness ir B C f = LtOperationUnsigned.comparisonLimbsWitness
      (populateAbsRem B C f) (populateMaxAbsCOr1 C f) := by
    unfold ltClWitness
    rw [if_pos hgate]
  unfold ltBitWitness
  rw [if_pos hgate]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero]
  rw [hclw, hmax]
  exact comparison_bit_one (populateAbsRem_isU64 B C f) (populateAbsC_isU64 hC f) hcore

/-! ### Off-gate corollaries -/

set_option linter.unusedSectionVars false

/-- Off the remainder-check gate the `comparison_limbs` block is zero. -/
lemma ltCl_zero_of_gate_ne {ir : ZMod p} (B C : Word (ZMod p)) {f : Vector (ZMod p) 8}
    (h : ltGate ir C f ≠ 1) : ltClWitness ir B C f = #v[0, 0] := by
  unfold ltClWitness
  rw [if_neg h]

/-- Off the remainder-check gate the `u16_flags` block is zero. -/
lemma ltFlags_zero_of_gate_ne {ir : ZMod p} (B C : Word (ZMod p)) {f : Vector (ZMod p) 8}
    (h : ltGate ir C f ≠ 1) : ltFlagsWitness ir B C f = #v[0, 0, 0, 0] := by
  unfold ltFlagsWitness
  rw [if_neg h]

/-- Off the remainder-check gate the `not_eq_inv` cell is zero. -/
lemma ltNotEqInv_zero_of_gate_ne {ir : ZMod p} (B C : Word (ZMod p)) {f : Vector (ZMod p) 8}
    (h : ltGate ir C f ≠ 1) : ltNotEqInvWitness ir B C f = #v[0] := by
  unfold ltNotEqInvWitness
  rw [if_neg h]

/-- Off the remainder-check gate the `U16CompareOperation` bit is zero. -/
lemma ltBit_zero_of_gate_ne {ir : ZMod p} (B C : Word (ZMod p)) {f : Vector (ZMod p) 8}
    (h : ltGate ir C f ≠ 1) : ltBitWitness ir B C f = #v[0] := by
  unfold ltBitWitness
  rw [if_neg h]

end SP1Clean.DivRemChip
