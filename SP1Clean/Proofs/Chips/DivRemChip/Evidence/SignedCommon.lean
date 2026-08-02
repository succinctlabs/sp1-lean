import SP1Clean.Proofs.Chips.DivRemChip.Assembly
import SP1Clean.Proofs.Chips.DivRemChip.Defs

/-! # `DivRemChip` — shared signed-family evidence lemmas

These small, circuit-independent lemmas isolate the two semantic facts shared by the signed 64-bit
and signed word cases: the conditional two's-complement absolute-value witness and the conversion of
the row's zero limb-sum constraint into a zero `BitVec`. -/

namespace SP1Clean.DivRemChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

omit [Fact (2 ^ 24 < p)] in
/-- Turn the signed-absolute-value row contract into its two semantic branches. The caller handles
the four raw limb equations once and supplies their compact positive/negative-gate consequences. -/
lemma signedAbsBehavior {x abs negValue : Word (ZMod p)} {neg event : ZMod p}
    (hneg : neg = if x.toBitVec64.msb then 1 else 0)
    (hpos : neg = 0 → abs = x) (hevent : event = neg)
    (hzero : event = 1 → negValue = #v[0, 0, 0, 0])
    (hadd : AddOperation.Spec ⟨x, abs, ⟨negValue⟩, event⟩) :
    (x.toBitVec64.msb = false → abs.toBitVec64 = x.toBitVec64) ∧
    (x.toBitVec64.msb = true → abs.toBitVec64 = -x.toBitVec64) := by
  constructor
  · intro hmsb
    rw [hpos (by rw [hneg, hmsb]; simp)]
  · intro hmsb
    have he : event = 1 := hevent.trans (by rw [hneg, hmsb]; simp)
    obtain ⟨_, hsum⟩ := hadd he
    have hz : Word.toBitVec64 (#v[0, 0, 0, 0] : Word (ZMod p)) = 0#64 := by
      norm_num [Word.toBitVec64, Word.toNat_def]
    rw [hzero he, hz] at hsum
    bv_omega

/-- Four genuine u16 limbs whose field sum is zero form the zero 64-bit word. This is the semantic
readout needed from DivRem's `E228` sign constraint. -/
lemma toBitVec64_eq_zero_of_limb_sum_eq_zero {w : Word (ZMod p)} (hw : w.isU64)
    (hsum : w[0] + w[1] + w[2] + w[3] = 0) : w.toBitVec64 = 0#64 := by
  obtain ⟨h0, h1, h2, h3⟩ := Word.lt_cases_of_isU64 hw
  have hp : 2 ^ 24 < p := Fact.out
  have h01 : (w[0] + w[1]).val = w[0].val + w[1].val :=
    ZMod.val_add_of_lt (by omega)
  have h012 : (w[0] + w[1] + w[2]).val = w[0].val + w[1].val + w[2].val := by
    rw [ZMod.val_add_of_lt (by rw [h01]; omega), h01]
  have h0123 : (w[0] + w[1] + w[2] + w[3]).val =
      w[0].val + w[1].val + w[2].val + w[3].val := by
    rw [ZMod.val_add_of_lt (by rw [h012]; omega), h012]
  have hv := congrArg ZMod.val hsum
  rw [h0123, ZMod.val_zero] at hv
  apply BitVec.eq_of_toNat_eq
  rw [Word.toBitVec64_toNat hw, BitVec.toNat_zero, Word.toNat_def]
  omega

omit [Fact (2 ^ 24 < p)] in
/-- A `gate * (x - y) = 0` row constraint on an *active* gate says exactly `x = y`. Both signed
evidence proofs hit this shape two dozen times (the `is_overflow` and `is_c_0` branches); applying
it as a **term** keeps the equivalent `rw`/`linear_combination` tactic pair — and that pair's
renormalisation of the surrounding ~115-hypothesis context — out of those branch bodies. -/
lemma eq_of_gate_eq_one {g x y : ZMod p} (hg : g = 1) (h : g * (x - y) = 0) : x = y := by
  rw [hg, one_mul, sub_eq_zero] at h
  exact h

omit [Fact (2 ^ 24 < p)] in
/-- `signedAbsBehavior` read straight off the raw `E247…E288` row equations. The signed 64-bit and
signed word evidence proofs each apply this twice — once for `|c|`, once for `|remainder|` — so the
componentwise `Vector.ext` sweeps run here, over four opaque `Word`s, instead of four times inside
those proofs' ~115-hypothesis `normal` branch. -/
lemma signedAbs_of_asserts {x abs value : Word (ZMod p)} {neg event is_real : ZMod p}
    (hmsb : neg = if x.toBitVec64.msb then 1 else 0) (hir : is_real = 1)
    (p0 : (neg - (1 : ZMod p)) * (x[0] - abs[0]) = 0)
    (p1 : (neg - (1 : ZMod p)) * (x[1] - abs[1]) = 0)
    (p2 : (neg - (1 : ZMod p)) * (x[2] - abs[2]) = 0)
    (p3 : (neg - (1 : ZMod p)) * (x[3] - abs[3]) = 0)
    (hev : event - neg * is_real = 0)
    (v0 : event * ((0 : ZMod p) - value[0]) = 0) (v1 : event * ((0 : ZMod p) - value[1]) = 0)
    (v2 : event * ((0 : ZMod p) - value[2]) = 0) (v3 : event * ((0 : ZMod p) - value[3]) = 0)
    (hadd : AddOperation.Spec ⟨x, abs, ⟨value⟩, event⟩) :
    (x.toBitVec64.msb = false → abs.toBitVec64 = x.toBitVec64) ∧
    (x.toBitVec64.msb = true → abs.toBitVec64 = -x.toBitVec64) := by
  refine signedAbsBehavior hmsb ?_ ?_ ?_ hadd
  · intro hn
    apply Vector.ext; intro i hi; interval_cases i
    · rw [hn] at p0
      linear_combination p0
    · rw [hn] at p1
      linear_combination p1
    · rw [hn] at p2
      linear_combination p2
    · rw [hn] at p3
      linear_combination p3
  · rw [hir] at hev; linear_combination hev
  · intro he
    apply Vector.ext; intro i hi; interval_cases i
    all_goals simp only [Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ]
    · rw [he] at v0
      linear_combination -v0
    · rw [he] at v1
      linear_combination -v1
    · rw [he] at v2
      linear_combination -v2
    · rw [he] at v3
      linear_combination -v3

/-- The Euclidean remainder-magnitude bound `|remainder| < |c|`, read off the raw `E299…E307` row
equations on a nonzero divisor. `max(|c|, 1)` collapses to `|c|`, the range-check multiplicity is
`1`, and the `LtOperationUnsigned` comparison bit is therefore forced. Shared verbatim by the
signed 64-bit and signed word proofs. -/
lemma absRemainder_lt_absC {cols : Columns (ZMod p)} (hir : cols.is_real = 1)
    (hcnz : ¬ (cols.c[0] = 0 ∧ cols.c[1] = 0 ∧ cols.c[2] = 0 ∧ cols.c[3] = 0))
    (habsRU : Word.isU64 cols.abs_remainder) (habsCU : Word.isU64 cols.abs_c)
    (hisZero : IsZeroWordOperation.Spec ⟨cols.c, cols.is_c_0, cols.is_real⟩)
    (hltSpec : LtOperationUnsigned.Spec ⟨cols.abs_remainder, cols.max_abs_c_or_1,
      cols.remainder_lt_operation, cols.remainder_check_multiplicity⟩)
    (e299 : cols.max_abs_c_or_1[0] -
      (cols.is_c_0.result * (1 : ZMod p) +
        ((1 : ZMod p) - cols.is_c_0.result) * cols.abs_c[0]) = 0)
    (e300 : cols.max_abs_c_or_1[1] - ((1 : ZMod p) - cols.is_c_0.result) * cols.abs_c[1] = 0)
    (e301 : cols.max_abs_c_or_1[2] - ((1 : ZMod p) - cols.is_c_0.result) * cols.abs_c[2] = 0)
    (e302 : cols.max_abs_c_or_1[3] - ((1 : ZMod p) - cols.is_c_0.result) * cols.abs_c[3] = 0)
    (e305 : ((1 : ZMod p) - cols.is_c_0.result) * cols.is_real -
      cols.remainder_check_multiplicity = 0)
    (e307 : cols.remainder_check_multiplicity *
      ((1 : ZMod p) - cols.remainder_lt_operation.u16_compare_operation.bit) = 0) :
    cols.abs_remainder.toNat < cols.abs_c.toNat := by
  have hzeroResult := IsZeroWordOperation.result_semantic hisZero hir
  rw [if_neg hcnz] at hzeroResult
  have hrcm : cols.remainder_check_multiplicity = 1 := by
    rw [hzeroResult, hir] at e305; linear_combination -e305
  have hmax0 : cols.max_abs_c_or_1[0] = cols.abs_c[0] := by
    rw [hzeroResult] at e299; linear_combination e299
  have hmax1 : cols.max_abs_c_or_1[1] = cols.abs_c[1] := by
    rw [hzeroResult] at e300; linear_combination e300
  have hmax2 : cols.max_abs_c_or_1[2] = cols.abs_c[2] := by
    rw [hzeroResult] at e301; linear_combination e301
  have hmax3 : cols.max_abs_c_or_1[3] = cols.abs_c[3] := by
    rw [hzeroResult] at e302; linear_combination e302
  have hmaxEq : cols.max_abs_c_or_1 = cols.abs_c := by
    apply Vector.ext; intro i hi; interval_cases i <;> assumption
  have hmaxU : Word.isU64 cols.max_abs_c_or_1 := hmaxEq ▸ habsCU
  have hbit := (LtOperationUnsigned.result_semantic habsRU hmaxU hrcm hltSpec).1
  have hbit1 : cols.remainder_lt_operation.u16_compare_operation.bit = 1 := by
    rw [hrcm] at e307; linear_combination -e307
  rw [hbit1] at hbit
  have hcmpMax : cols.abs_remainder.toNat < cols.max_abs_c_or_1.toNat := by
    by_contra hnot
    rw [if_neg hnot] at hbit
    exact one_ne_zero hbit
  simpa [hmaxEq] using hcmpMax

/-- The two remainder-sign gates `E225`/`E228` in the form `sign_conditions` consumes, read off the
raw row equations together with the `E345`/`E351` booleanness constraints. Shared verbatim by the
signed 64-bit and signed word proofs. -/
lemma signGates_of_asserts {cols : Columns (ZMod p)} (hremU : Word.isU64 cols.remainder)
    (hrcEq : cols.remainder_comp = cols.remainder)
    (e225 : cols.rem_neg * (cols.b_neg - 1) = 0)
    (e228 : ((0 : ZMod p) + cols.remainder[0] + cols.remainder[1] + cols.remainder[2] +
      cols.remainder[3]) * (((1 : ZMod p) - cols.rem_neg) * cols.b_neg) = 0)
    (e345 : cols.b_neg * (cols.b_neg - 1) = 0)
    (e351 : cols.rem_neg * (cols.rem_neg - 1) = 0) :
    (cols.rem_neg = 0 ∨ cols.b_neg = 1) ∧
    (Word.toBitVec64 cols.remainder_comp = 0#64 ∨ cols.rem_neg = 1 ∨ cols.b_neg = 0) := by
  have hbnegBin := bool_of_mul_pred e345
  have hrnegBin := bool_of_mul_pred e351
  constructor
  · rcases hrnegBin with hr0 | hr1
    · exact Or.inl hr0
    · rcases hbnegBin with hb0 | hb1
      · rw [hr1, hb0] at e225
        norm_num at e225
      · exact Or.inr hb1
  · have hE228 : Word.toBitVec64 cols.remainder = 0#64 ∨
        cols.rem_neg = 1 ∨ cols.b_neg = 0 := by
      rcases hrnegBin with hr0 | hr1
      · rcases hbnegBin with hb0 | hb1
        · exact Or.inr (Or.inr hb0)
        · apply Or.inl
          apply toBitVec64_eq_zero_of_limb_sum_eq_zero hremU
          rw [hr0, hb1] at e228; linear_combination e228
      · exact Or.inr (Or.inl hr1)
    simpa [hrcEq] using hE228

end SP1Clean.DivRemChip
