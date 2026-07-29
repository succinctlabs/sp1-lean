import SP1Clean.Proofs.Chips.DivRemChip.Assembly

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

end SP1Clean.DivRemChip
