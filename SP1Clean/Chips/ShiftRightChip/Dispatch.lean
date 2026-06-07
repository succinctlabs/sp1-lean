import SP1Clean.Chips.ShiftRightChip.Core

/-! # ShiftRight dispatch lemmas (16-way within-byte case split)

For each shift variant (`srl`/`sra`/`srlw`/`sraw`) and byte-shift offset, one lemma performs the
16-way case split on the within-byte shift bits `cb0..cb3` and dispatches to the matching
`*_close_su16_*_case` reconstruction lemma. Each lemma encapsulates a ~175-line
`rcases … <;> first | exact …` case split, so `ShiftRightChip.soundness` discharges every
byte-shift case with a single `exact ShiftRightMath.<var>_dispatch_<bs> …`.

`hcb4`/`hcb5` fix the byte-shift offset (which limb window the result occupies); `b_cb0..b_cb3`
are the within-byte shift bits that get case-split. The `_msb1` lemmas are the negative
(sign-extending) arm of the arithmetic shifts. All are field-generic and axiom-clean. -/

namespace SP1Clean.ShiftRightMath

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

set_option maxHeartbeats 1000000 in
/-- SRL (logical, 64-bit) byte-shift 0: the within-byte dispatch to `srl_close_su16_0_case`. -/
lemma srl_dispatch_0
    {cb0 cb1 cb2 cb3 cb4 cb5 v01 v012 v0123 b0 b1 b2 b3 ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 : ZMod p}
    (b_cb0 : cb0 = 0 ∨ cb0 = 1) (b_cb1 : cb1 = 0 ∨ cb1 = 1)
    (b_cb2 : cb2 = 0 ∨ cb2 = 1) (b_cb3 : cb3 = 0 ∨ cb3 = 1)
    (hcb4 : cb4 = 0) (hcb5 : cb5 = 0)
    (eq_v01 : v01 = (1 + -cb0 + 1) * 2 * ((1 + -cb1) * 3 + 1))
    (eq_v012 : v012 = v01 * ((1 + -cb2) * 15 + 1))
    (eq_v0123 : v0123 = v012 * ((1 + -cb3) * 255 + 1))
    (lt_ll0 : ll0.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh0 : hl0.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (lt_ll1 : ll1.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh1 : hl1.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (lt_ll2 : ll2.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh2 : hl2.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (lt_ll3 : ll3.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh3 : hl3.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (h_b0_dec : b0 * v0123 = hl0 * ((65536 : ℕ) : ZMod p) + ll0 * v0123)
    (h_b1_dec : b1 * v0123 = hl1 * ((65536 : ℕ) : ZMod p) + ll1 * v0123)
    (h_b2_dec : b2 * v0123 = hl2 * ((65536 : ℕ) : ZMod p) + ll2 * v0123)
    (h_b3_dec : b3 * v0123 = hl3 * ((65536 : ℕ) : ZMod p) + ll3 * v0123) :
    (Word.toBitVec64 #v[hl0 + ll1 * v0123, hl1 + ll2 * v0123, hl2 + ll3 * v0123, hl3]).toNat
    = (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat
        / 2 ^ (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val := by
  have hp17 : (2 : ℕ) ^ 17 < p := Fact.out
  rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
    rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3 <;>
    first
      | exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 0 (by omega) 65536 1 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 1 (by omega) 32768 2 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 2 (by omega) 16384 4 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 3 (by omega) 8192 8 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 4 (by omega) 4096 16 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 5 (by omega) 2048 32 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 6 (by omega) 1024 64 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 7 (by omega) 512 128 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 8 (by omega) 256 256 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 9 (by omega) 128 512 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 10 (by omega) 64 1024 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 11 (by omega) 32 2048 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 12 (by omega) 16 4096 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 13 (by omega) 8 8192 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 14 (by omega) 4 16384 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 15 (by omega) 2 32768 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec

set_option maxHeartbeats 1000000 in
/-- SRL (logical, 64-bit) byte-shift 1: the within-byte dispatch to `srl_close_su16_1_case`. -/
lemma srl_dispatch_1
    {cb0 cb1 cb2 cb3 cb4 cb5 v01 v012 v0123 b0 b1 b2 b3 ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 : ZMod p}
    (b_cb0 : cb0 = 0 ∨ cb0 = 1) (b_cb1 : cb1 = 0 ∨ cb1 = 1)
    (b_cb2 : cb2 = 0 ∨ cb2 = 1) (b_cb3 : cb3 = 0 ∨ cb3 = 1)
    (hcb4 : cb4 = 1) (hcb5 : cb5 = 0)
    (eq_v01 : v01 = (1 + -cb0 + 1) * 2 * ((1 + -cb1) * 3 + 1))
    (eq_v012 : v012 = v01 * ((1 + -cb2) * 15 + 1))
    (eq_v0123 : v0123 = v012 * ((1 + -cb3) * 255 + 1))
    (lt_ll0 : ll0.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh0 : hl0.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (lt_ll1 : ll1.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh1 : hl1.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (lt_ll2 : ll2.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh2 : hl2.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (lt_ll3 : ll3.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh3 : hl3.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (h_b0_dec : b0 * v0123 = hl0 * ((65536 : ℕ) : ZMod p) + ll0 * v0123)
    (h_b1_dec : b1 * v0123 = hl1 * ((65536 : ℕ) : ZMod p) + ll1 * v0123)
    (h_b2_dec : b2 * v0123 = hl2 * ((65536 : ℕ) : ZMod p) + ll2 * v0123)
    (h_b3_dec : b3 * v0123 = hl3 * ((65536 : ℕ) : ZMod p) + ll3 * v0123) :
    (Word.toBitVec64 #v[hl1 + ll2 * v0123, hl2 + ll3 * v0123, hl3, 0]).toNat
    = (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat
        / 2 ^ (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val := by
  have hp17 : (2 : ℕ) ^ 17 < p := Fact.out
  rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
    rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3 <;>
    first
      | exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 0 (by omega) 65536 1 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 1 (by omega) 32768 2 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 2 (by omega) 16384 4 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 3 (by omega) 8192 8 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 4 (by omega) 4096 16 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 5 (by omega) 2048 32 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 6 (by omega) 1024 64 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 7 (by omega) 512 128 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 8 (by omega) 256 256 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 9 (by omega) 128 512 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 10 (by omega) 64 1024 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 11 (by omega) 32 2048 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 12 (by omega) 16 4096 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 13 (by omega) 8 8192 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 14 (by omega) 4 16384 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 15 (by omega) 2 32768 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec

set_option maxHeartbeats 1000000 in
/-- SRL (logical, 64-bit) byte-shift 2: the within-byte dispatch to `srl_close_su16_2_case`. -/
lemma srl_dispatch_2
    {cb0 cb1 cb2 cb3 cb4 cb5 v01 v012 v0123 b0 b1 b2 b3 ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 : ZMod p}
    (b_cb0 : cb0 = 0 ∨ cb0 = 1) (b_cb1 : cb1 = 0 ∨ cb1 = 1)
    (b_cb2 : cb2 = 0 ∨ cb2 = 1) (b_cb3 : cb3 = 0 ∨ cb3 = 1)
    (hcb4 : cb4 = 0) (hcb5 : cb5 = 1)
    (eq_v01 : v01 = (1 + -cb0 + 1) * 2 * ((1 + -cb1) * 3 + 1))
    (eq_v012 : v012 = v01 * ((1 + -cb2) * 15 + 1))
    (eq_v0123 : v0123 = v012 * ((1 + -cb3) * 255 + 1))
    (lt_ll0 : ll0.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh0 : hl0.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (lt_ll1 : ll1.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh1 : hl1.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (lt_ll2 : ll2.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh2 : hl2.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (lt_ll3 : ll3.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh3 : hl3.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (h_b0_dec : b0 * v0123 = hl0 * ((65536 : ℕ) : ZMod p) + ll0 * v0123)
    (h_b1_dec : b1 * v0123 = hl1 * ((65536 : ℕ) : ZMod p) + ll1 * v0123)
    (h_b2_dec : b2 * v0123 = hl2 * ((65536 : ℕ) : ZMod p) + ll2 * v0123)
    (h_b3_dec : b3 * v0123 = hl3 * ((65536 : ℕ) : ZMod p) + ll3 * v0123) :
    (Word.toBitVec64 #v[hl2 + ll3 * v0123, hl3, 0, 0]).toNat
    = (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat
        / 2 ^ (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val := by
  have hp17 : (2 : ℕ) ^ 17 < p := Fact.out
  rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
    rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3 <;>
    first
      | exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 0 (by omega) 65536 1 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 1 (by omega) 32768 2 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 2 (by omega) 16384 4 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 3 (by omega) 8192 8 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 4 (by omega) 4096 16 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 5 (by omega) 2048 32 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 6 (by omega) 1024 64 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 7 (by omega) 512 128 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 8 (by omega) 256 256 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 9 (by omega) 128 512 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 10 (by omega) 64 1024 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 11 (by omega) 32 2048 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 12 (by omega) 16 4096 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 13 (by omega) 8 8192 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 14 (by omega) 4 16384 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 15 (by omega) 2 32768 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec

set_option maxHeartbeats 1000000 in
/-- SRL (logical, 64-bit) byte-shift 3: the within-byte dispatch to `srl_close_su16_3_case`. -/
lemma srl_dispatch_3
    {cb0 cb1 cb2 cb3 cb4 cb5 v01 v012 v0123 b0 b1 b2 b3 ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 : ZMod p}
    (b_cb0 : cb0 = 0 ∨ cb0 = 1) (b_cb1 : cb1 = 0 ∨ cb1 = 1)
    (b_cb2 : cb2 = 0 ∨ cb2 = 1) (b_cb3 : cb3 = 0 ∨ cb3 = 1)
    (hcb4 : cb4 = 1) (hcb5 : cb5 = 1)
    (eq_v01 : v01 = (1 + -cb0 + 1) * 2 * ((1 + -cb1) * 3 + 1))
    (eq_v012 : v012 = v01 * ((1 + -cb2) * 15 + 1))
    (eq_v0123 : v0123 = v012 * ((1 + -cb3) * 255 + 1))
    (lt_ll0 : ll0.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh0 : hl0.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (lt_ll1 : ll1.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh1 : hl1.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (lt_ll2 : ll2.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh2 : hl2.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (lt_ll3 : ll3.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh3 : hl3.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (h_b0_dec : b0 * v0123 = hl0 * ((65536 : ℕ) : ZMod p) + ll0 * v0123)
    (h_b1_dec : b1 * v0123 = hl1 * ((65536 : ℕ) : ZMod p) + ll1 * v0123)
    (h_b2_dec : b2 * v0123 = hl2 * ((65536 : ℕ) : ZMod p) + ll2 * v0123)
    (h_b3_dec : b3 * v0123 = hl3 * ((65536 : ℕ) : ZMod p) + ll3 * v0123) :
    (Word.toBitVec64 #v[hl3, 0, 0, 0]).toNat
    = (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat
        / 2 ^ (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val := by
  have hp17 : (2 : ℕ) ^ 17 < p := Fact.out
  rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
    rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3 <;>
    first
      | exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 0 (by omega) 65536 1 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 1 (by omega) 32768 2 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 2 (by omega) 16384 4 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 3 (by omega) 8192 8 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 4 (by omega) 4096 16 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 5 (by omega) 2048 32 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 6 (by omega) 1024 64 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 7 (by omega) 512 128 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 8 (by omega) 256 256 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 9 (by omega) 128 512 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 10 (by omega) 64 1024 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 11 (by omega) 32 2048 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 12 (by omega) 16 4096 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 13 (by omega) 8 8192 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 14 (by omega) 4 16384 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 15 (by omega) 2 32768 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec

set_option maxHeartbeats 1000000 in
/-- SRA (arithmetic, 64-bit) negative arm, byte-shift 0: dispatch to `sra_close_su16_0_case`. -/
lemma sra_dispatch_0_msb1
    {cb0 cb1 cb2 cb3 cb4 cb5 v01 v012 v0123 b0 b1 b2 b3 ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 : ZMod p}
    (b_cb0 : cb0 = 0 ∨ cb0 = 1) (b_cb1 : cb1 = 0 ∨ cb1 = 1)
    (b_cb2 : cb2 = 0 ∨ cb2 = 1) (b_cb3 : cb3 = 0 ∨ cb3 = 1)
    (hcb4 : cb4 = 0) (hcb5 : cb5 = 0)
    (eq_v01 : v01 = (1 + -cb0 + 1) * 2 * ((1 + -cb1) * 3 + 1))
    (eq_v012 : v012 = v01 * ((1 + -cb2) * 15 + 1))
    (eq_v0123 : v0123 = v012 * ((1 + -cb3) * 255 + 1))
    (lt_ll0 : ll0.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh0 : hl0.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (lt_ll1 : ll1.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh1 : hl1.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (lt_ll2 : ll2.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh2 : hl2.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (lt_ll3 : ll3.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh3 : hl3.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (h_b0_dec : b0 * v0123 = hl0 * ((65536 : ℕ) : ZMod p) + ll0 * v0123)
    (h_b1_dec : b1 * v0123 = hl1 * ((65536 : ℕ) : ZMod p) + ll1 * v0123)
    (h_b2_dec : b2 * v0123 = hl2 * ((65536 : ℕ) : ZMod p) + ll2 * v0123)
    (h_b3_dec : b3 * v0123 = hl3 * ((65536 : ℕ) : ZMod p) + ll3 * v0123) :
    (Word.toBitVec64 #v[hl0 + ll1 * v0123, hl1 + ll2 * v0123,
        hl2 + ll3 * v0123, hl3 + (((65536 : ℕ) : ZMod p) - v0123)]).toNat
    = 2 ^ 64 - 1 - (2 ^ 64 - 1 - (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat)
        / 2 ^ (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val := by
  have hp17 : (2 : ℕ) ^ 17 < p := Fact.out
  rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
    rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3 <;>
    first
      | exact sra_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 0 (by omega) 65536 1 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 1 (by omega) 32768 2 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 2 (by omega) 16384 4 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 3 (by omega) 8192 8 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 4 (by omega) 4096 16 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 5 (by omega) 2048 32 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 6 (by omega) 1024 64 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 7 (by omega) 512 128 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 8 (by omega) 256 256 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 9 (by omega) 128 512 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 10 (by omega) 64 1024 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 11 (by omega) 32 2048 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 12 (by omega) 16 4096 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 13 (by omega) 8 8192 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 14 (by omega) 4 16384 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 15 (by omega) 2 32768 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec

set_option maxHeartbeats 1000000 in
/-- SRA (arithmetic, 64-bit) negative arm, byte-shift 1: dispatch to `sra_close_su16_1_case`. -/
lemma sra_dispatch_1_msb1
    {cb0 cb1 cb2 cb3 cb4 cb5 v01 v012 v0123 b0 b1 b2 b3 ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 : ZMod p}
    (b_cb0 : cb0 = 0 ∨ cb0 = 1) (b_cb1 : cb1 = 0 ∨ cb1 = 1)
    (b_cb2 : cb2 = 0 ∨ cb2 = 1) (b_cb3 : cb3 = 0 ∨ cb3 = 1)
    (hcb4 : cb4 = 1) (hcb5 : cb5 = 0)
    (eq_v01 : v01 = (1 + -cb0 + 1) * 2 * ((1 + -cb1) * 3 + 1))
    (eq_v012 : v012 = v01 * ((1 + -cb2) * 15 + 1))
    (eq_v0123 : v0123 = v012 * ((1 + -cb3) * 255 + 1))
    (lt_ll0 : ll0.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh0 : hl0.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (lt_ll1 : ll1.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh1 : hl1.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (lt_ll2 : ll2.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh2 : hl2.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (lt_ll3 : ll3.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh3 : hl3.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (h_b0_dec : b0 * v0123 = hl0 * ((65536 : ℕ) : ZMod p) + ll0 * v0123)
    (h_b1_dec : b1 * v0123 = hl1 * ((65536 : ℕ) : ZMod p) + ll1 * v0123)
    (h_b2_dec : b2 * v0123 = hl2 * ((65536 : ℕ) : ZMod p) + ll2 * v0123)
    (h_b3_dec : b3 * v0123 = hl3 * ((65536 : ℕ) : ZMod p) + ll3 * v0123) :
    (Word.toBitVec64 #v[hl1 + ll2 * v0123, hl2 + ll3 * v0123,
        hl3 + (((65536 : ℕ) : ZMod p) - v0123), ((65535 : ℕ) : ZMod p)]).toNat
    = 2 ^ 64 - 1 - (2 ^ 64 - 1 - (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat)
        / 2 ^ (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val := by
  have hp17 : (2 : ℕ) ^ 17 < p := Fact.out
  rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
    rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3 <;>
    first
      | exact sra_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 0 (by omega) 65536 1 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 1 (by omega) 32768 2 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 2 (by omega) 16384 4 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 3 (by omega) 8192 8 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 4 (by omega) 4096 16 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 5 (by omega) 2048 32 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 6 (by omega) 1024 64 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 7 (by omega) 512 128 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 8 (by omega) 256 256 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 9 (by omega) 128 512 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 10 (by omega) 64 1024 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 11 (by omega) 32 2048 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 12 (by omega) 16 4096 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 13 (by omega) 8 8192 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 14 (by omega) 4 16384 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 15 (by omega) 2 32768 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec

set_option maxHeartbeats 1000000 in
/-- SRA (arithmetic, 64-bit) negative arm, byte-shift 2: dispatch to `sra_close_su16_2_case`. -/
lemma sra_dispatch_2_msb1
    {cb0 cb1 cb2 cb3 cb4 cb5 v01 v012 v0123 b0 b1 b2 b3 ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 : ZMod p}
    (b_cb0 : cb0 = 0 ∨ cb0 = 1) (b_cb1 : cb1 = 0 ∨ cb1 = 1)
    (b_cb2 : cb2 = 0 ∨ cb2 = 1) (b_cb3 : cb3 = 0 ∨ cb3 = 1)
    (hcb4 : cb4 = 0) (hcb5 : cb5 = 1)
    (eq_v01 : v01 = (1 + -cb0 + 1) * 2 * ((1 + -cb1) * 3 + 1))
    (eq_v012 : v012 = v01 * ((1 + -cb2) * 15 + 1))
    (eq_v0123 : v0123 = v012 * ((1 + -cb3) * 255 + 1))
    (lt_ll0 : ll0.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh0 : hl0.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (lt_ll1 : ll1.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh1 : hl1.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (lt_ll2 : ll2.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh2 : hl2.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (lt_ll3 : ll3.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh3 : hl3.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (h_b0_dec : b0 * v0123 = hl0 * ((65536 : ℕ) : ZMod p) + ll0 * v0123)
    (h_b1_dec : b1 * v0123 = hl1 * ((65536 : ℕ) : ZMod p) + ll1 * v0123)
    (h_b2_dec : b2 * v0123 = hl2 * ((65536 : ℕ) : ZMod p) + ll2 * v0123)
    (h_b3_dec : b3 * v0123 = hl3 * ((65536 : ℕ) : ZMod p) + ll3 * v0123) :
    (Word.toBitVec64 #v[hl2 + ll3 * v0123, hl3 + (((65536 : ℕ) : ZMod p) - v0123),
        ((65535 : ℕ) : ZMod p), ((65535 : ℕ) : ZMod p)]).toNat
    = 2 ^ 64 - 1 - (2 ^ 64 - 1 - (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat)
        / 2 ^ (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val := by
  have hp17 : (2 : ℕ) ^ 17 < p := Fact.out
  rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
    rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3 <;>
    first
      | exact sra_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 0 (by omega) 65536 1 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 1 (by omega) 32768 2 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 2 (by omega) 16384 4 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 3 (by omega) 8192 8 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 4 (by omega) 4096 16 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 5 (by omega) 2048 32 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 6 (by omega) 1024 64 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 7 (by omega) 512 128 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 8 (by omega) 256 256 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 9 (by omega) 128 512 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 10 (by omega) 64 1024 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 11 (by omega) 32 2048 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 12 (by omega) 16 4096 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 13 (by omega) 8 8192 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 14 (by omega) 4 16384 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 15 (by omega) 2 32768 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec

set_option maxHeartbeats 1000000 in
/-- SRA (arithmetic, 64-bit) negative arm, byte-shift 3: dispatch to `sra_close_su16_3_case`. -/
lemma sra_dispatch_3_msb1
    {cb0 cb1 cb2 cb3 cb4 cb5 v01 v012 v0123 b0 b1 b2 b3 ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 : ZMod p}
    (b_cb0 : cb0 = 0 ∨ cb0 = 1) (b_cb1 : cb1 = 0 ∨ cb1 = 1)
    (b_cb2 : cb2 = 0 ∨ cb2 = 1) (b_cb3 : cb3 = 0 ∨ cb3 = 1)
    (hcb4 : cb4 = 1) (hcb5 : cb5 = 1)
    (eq_v01 : v01 = (1 + -cb0 + 1) * 2 * ((1 + -cb1) * 3 + 1))
    (eq_v012 : v012 = v01 * ((1 + -cb2) * 15 + 1))
    (eq_v0123 : v0123 = v012 * ((1 + -cb3) * 255 + 1))
    (lt_ll0 : ll0.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh0 : hl0.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (lt_ll1 : ll1.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh1 : hl1.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (lt_ll2 : ll2.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh2 : hl2.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (lt_ll3 : ll3.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh3 : hl3.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (h_b0_dec : b0 * v0123 = hl0 * ((65536 : ℕ) : ZMod p) + ll0 * v0123)
    (h_b1_dec : b1 * v0123 = hl1 * ((65536 : ℕ) : ZMod p) + ll1 * v0123)
    (h_b2_dec : b2 * v0123 = hl2 * ((65536 : ℕ) : ZMod p) + ll2 * v0123)
    (h_b3_dec : b3 * v0123 = hl3 * ((65536 : ℕ) : ZMod p) + ll3 * v0123) :
    (Word.toBitVec64 #v[hl3 + (((65536 : ℕ) : ZMod p) - v0123),
        ((65535 : ℕ) : ZMod p), ((65535 : ℕ) : ZMod p), ((65535 : ℕ) : ZMod p)]).toNat
    = 2 ^ 64 - 1 - (2 ^ 64 - 1 - (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat)
        / 2 ^ (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val := by
  have hp17 : (2 : ℕ) ^ 17 < p := Fact.out
  rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
    rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3 <;>
    first
      | exact sra_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 0 (by omega) 65536 1 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 1 (by omega) 32768 2 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 2 (by omega) 16384 4 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 3 (by omega) 8192 8 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 4 (by omega) 4096 16 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 5 (by omega) 2048 32 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 6 (by omega) 1024 64 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 7 (by omega) 512 128 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 8 (by omega) 256 256 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 9 (by omega) 128 512 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 10 (by omega) 64 1024 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 11 (by omega) 32 2048 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 12 (by omega) 16 4096 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 13 (by omega) 8 8192 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 14 (by omega) 4 16384 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      | exact sra_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 15 (by omega) 2 32768 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec

set_option maxHeartbeats 1000000 in
/-- SRLW (logical word, 32-bit) byte-shift 0: dispatch to `srlw_close_su16_0_case`. -/
lemma srlw_dispatch_0
    {cb0 cb1 cb2 cb3 cb4 v01 v012 v0123 b0 b1 ll0 ll1 hl0 hl1 : ZMod p}
    (b_cb0 : cb0 = 0 ∨ cb0 = 1) (b_cb1 : cb1 = 0 ∨ cb1 = 1)
    (b_cb2 : cb2 = 0 ∨ cb2 = 1) (b_cb3 : cb3 = 0 ∨ cb3 = 1)
    (hcb4 : cb4 = 0)
    (eq_v01 : v01 = (1 + -cb0 + 1) * 2 * ((1 + -cb1) * 3 + 1))
    (eq_v012 : v012 = v01 * ((1 + -cb2) * 15 + 1))
    (eq_v0123 : v0123 = v012 * ((1 + -cb3) * 255 + 1))
    (lt_ll0 : ll0.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh0 : hl0.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (lt_ll1 : ll1.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh1 : hl1.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (h_b0_dec : b0 * v0123 = hl0 * ((65536 : ℕ) : ZMod p) + ll0 * v0123)
    (h_b1_dec : b1 * v0123 = hl1 * ((65536 : ℕ) : ZMod p) + ll1 * v0123) :
    (HWord.toBitVec32 #v[hl0 + ll1 * v0123, hl1]).toNat
    = (HWord.toBitVec32 #v[b0, b1]).toNat
        / 2 ^ (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16).val := by
  have hp17 : (2 : ℕ) ^ 17 < p := Fact.out
  rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
    rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3 <;>
    first
      | exact srlw_close_su16_0_case 0 (by omega) 65536 1 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact srlw_close_su16_0_case 1 (by omega) 32768 2 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact srlw_close_su16_0_case 2 (by omega) 16384 4 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact srlw_close_su16_0_case 3 (by omega) 8192 8 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact srlw_close_su16_0_case 4 (by omega) 4096 16 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact srlw_close_su16_0_case 5 (by omega) 2048 32 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact srlw_close_su16_0_case 6 (by omega) 1024 64 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact srlw_close_su16_0_case 7 (by omega) 512 128 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact srlw_close_su16_0_case 8 (by omega) 256 256 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact srlw_close_su16_0_case 9 (by omega) 128 512 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact srlw_close_su16_0_case 10 (by omega) 64 1024 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact srlw_close_su16_0_case 11 (by omega) 32 2048 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact srlw_close_su16_0_case 12 (by omega) 16 4096 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact srlw_close_su16_0_case 13 (by omega) 8 8192 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact srlw_close_su16_0_case 14 (by omega) 4 16384 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact srlw_close_su16_0_case 15 (by omega) 2 32768 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec

set_option maxHeartbeats 1000000 in
/-- SRLW (logical word, 32-bit) byte-shift 1: dispatch to `srlw_close_su16_1_case`. -/
lemma srlw_dispatch_1
    {cb0 cb1 cb2 cb3 cb4 v01 v012 v0123 b0 b1 ll0 ll1 hl0 hl1 : ZMod p}
    (b_cb0 : cb0 = 0 ∨ cb0 = 1) (b_cb1 : cb1 = 0 ∨ cb1 = 1)
    (b_cb2 : cb2 = 0 ∨ cb2 = 1) (b_cb3 : cb3 = 0 ∨ cb3 = 1)
    (hcb4 : cb4 = 1)
    (eq_v01 : v01 = (1 + -cb0 + 1) * 2 * ((1 + -cb1) * 3 + 1))
    (eq_v012 : v012 = v01 * ((1 + -cb2) * 15 + 1))
    (eq_v0123 : v0123 = v012 * ((1 + -cb3) * 255 + 1))
    (lt_ll0 : ll0.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh0 : hl0.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (lt_ll1 : ll1.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh1 : hl1.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (h_b0_dec : b0 * v0123 = hl0 * ((65536 : ℕ) : ZMod p) + ll0 * v0123)
    (h_b1_dec : b1 * v0123 = hl1 * ((65536 : ℕ) : ZMod p) + ll1 * v0123) :
    (HWord.toBitVec32 #v[hl1, 0]).toNat
    = (HWord.toBitVec32 #v[b0, b1]).toNat
        / 2 ^ (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16).val := by
  have hp17 : (2 : ℕ) ^ 17 < p := Fact.out
  rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
    rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3 <;>
    first
      | exact srlw_close_su16_1_case 0 (by omega) 65536 1 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact srlw_close_su16_1_case 1 (by omega) 32768 2 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact srlw_close_su16_1_case 2 (by omega) 16384 4 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact srlw_close_su16_1_case 3 (by omega) 8192 8 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact srlw_close_su16_1_case 4 (by omega) 4096 16 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact srlw_close_su16_1_case 5 (by omega) 2048 32 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact srlw_close_su16_1_case 6 (by omega) 1024 64 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact srlw_close_su16_1_case 7 (by omega) 512 128 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact srlw_close_su16_1_case 8 (by omega) 256 256 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact srlw_close_su16_1_case 9 (by omega) 128 512 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact srlw_close_su16_1_case 10 (by omega) 64 1024 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact srlw_close_su16_1_case 11 (by omega) 32 2048 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact srlw_close_su16_1_case 12 (by omega) 16 4096 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact srlw_close_su16_1_case 13 (by omega) 8 8192 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact srlw_close_su16_1_case 14 (by omega) 4 16384 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact srlw_close_su16_1_case 15 (by omega) 2 32768 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec

set_option maxHeartbeats 1000000 in
/-- SRAW (arithmetic word, 32-bit) negative arm, byte-shift 0: dispatch to `sraw_close_su16_0_case_msb1`. -/
lemma sraw_dispatch_0_msb1
    {cb0 cb1 cb2 cb3 cb4 v01 v012 v0123 b0 b1 ll0 ll1 hl0 hl1 : ZMod p}
    (b_cb0 : cb0 = 0 ∨ cb0 = 1) (b_cb1 : cb1 = 0 ∨ cb1 = 1)
    (b_cb2 : cb2 = 0 ∨ cb2 = 1) (b_cb3 : cb3 = 0 ∨ cb3 = 1)
    (hcb4 : cb4 = 0)
    (eq_v01 : v01 = (1 + -cb0 + 1) * 2 * ((1 + -cb1) * 3 + 1))
    (eq_v012 : v012 = v01 * ((1 + -cb2) * 15 + 1))
    (eq_v0123 : v0123 = v012 * ((1 + -cb3) * 255 + 1))
    (lt_ll0 : ll0.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh0 : hl0.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (lt_ll1 : ll1.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh1 : hl1.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (h_b0_dec : b0 * v0123 = hl0 * ((65536 : ℕ) : ZMod p) + ll0 * v0123)
    (h_b1_dec : b1 * v0123 = hl1 * ((65536 : ℕ) : ZMod p) + ll1 * v0123) :
    (HWord.toBitVec32 #v[hl0 + ll1 * v0123, hl1 + (((65536 : ℕ) : ZMod p) - v0123)]).toNat
    = 2 ^ 32 - 1 - (2 ^ 32 - 1 - (HWord.toBitVec32 #v[b0, b1]).toNat)
        / 2 ^ (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16).val := by
  have hp17 : (2 : ℕ) ^ 17 < p := Fact.out
  rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
    rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3 <;>
    first
      | exact sraw_close_su16_0_case_msb1 0 (by omega) 65536 1 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact sraw_close_su16_0_case_msb1 1 (by omega) 32768 2 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact sraw_close_su16_0_case_msb1 2 (by omega) 16384 4 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact sraw_close_su16_0_case_msb1 3 (by omega) 8192 8 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact sraw_close_su16_0_case_msb1 4 (by omega) 4096 16 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact sraw_close_su16_0_case_msb1 5 (by omega) 2048 32 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact sraw_close_su16_0_case_msb1 6 (by omega) 1024 64 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact sraw_close_su16_0_case_msb1 7 (by omega) 512 128 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact sraw_close_su16_0_case_msb1 8 (by omega) 256 256 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact sraw_close_su16_0_case_msb1 9 (by omega) 128 512 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact sraw_close_su16_0_case_msb1 10 (by omega) 64 1024 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact sraw_close_su16_0_case_msb1 11 (by omega) 32 2048 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact sraw_close_su16_0_case_msb1 12 (by omega) 16 4096 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact sraw_close_su16_0_case_msb1 13 (by omega) 8 8192 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact sraw_close_su16_0_case_msb1 14 (by omega) 4 16384 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact sraw_close_su16_0_case_msb1 15 (by omega) 2 32768 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec

set_option maxHeartbeats 1000000 in
/-- SRAW (arithmetic word, 32-bit) negative arm, byte-shift 1: dispatch to `sraw_close_su16_1_case_msb1`. -/
lemma sraw_dispatch_1_msb1
    {cb0 cb1 cb2 cb3 cb4 v01 v012 v0123 b0 b1 ll0 ll1 hl0 hl1 : ZMod p}
    (b_cb0 : cb0 = 0 ∨ cb0 = 1) (b_cb1 : cb1 = 0 ∨ cb1 = 1)
    (b_cb2 : cb2 = 0 ∨ cb2 = 1) (b_cb3 : cb3 = 0 ∨ cb3 = 1)
    (hcb4 : cb4 = 1)
    (eq_v01 : v01 = (1 + -cb0 + 1) * 2 * ((1 + -cb1) * 3 + 1))
    (eq_v012 : v012 = v01 * ((1 + -cb2) * 15 + 1))
    (eq_v0123 : v0123 = v012 * ((1 + -cb3) * 255 + 1))
    (lt_ll0 : ll0.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh0 : hl0.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (lt_ll1 : ll1.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8 : ZMod p).val)
    (lt_lh1 : hl1.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
      + cb3 * 8) : ZMod p).val)
    (h_b0_dec : b0 * v0123 = hl0 * ((65536 : ℕ) : ZMod p) + ll0 * v0123)
    (h_b1_dec : b1 * v0123 = hl1 * ((65536 : ℕ) : ZMod p) + ll1 * v0123) :
    (HWord.toBitVec32 #v[hl1 + (((65536 : ℕ) : ZMod p) - v0123), ((65535 : ℕ) : ZMod p)]).toNat
    = 2 ^ 32 - 1 - (2 ^ 32 - 1 - (HWord.toBitVec32 #v[b0, b1]).toNat)
        / 2 ^ (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16).val := by
  have hp17 : (2 : ℕ) ^ 17 < p := Fact.out
  rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
    rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3 <;>
    first
      | exact sraw_close_su16_1_case_msb1 0 (by omega) 65536 1 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact sraw_close_su16_1_case_msb1 1 (by omega) 32768 2 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact sraw_close_su16_1_case_msb1 2 (by omega) 16384 4 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact sraw_close_su16_1_case_msb1 3 (by omega) 8192 8 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact sraw_close_su16_1_case_msb1 4 (by omega) 4096 16 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact sraw_close_su16_1_case_msb1 5 (by omega) 2048 32 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact sraw_close_su16_1_case_msb1 6 (by omega) 1024 64 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact sraw_close_su16_1_case_msb1 7 (by omega) 512 128 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact sraw_close_su16_1_case_msb1 8 (by omega) 256 256 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact sraw_close_su16_1_case_msb1 9 (by omega) 128 512 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact sraw_close_su16_1_case_msb1 10 (by omega) 64 1024 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact sraw_close_su16_1_case_msb1 11 (by omega) 32 2048 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact sraw_close_su16_1_case_msb1 12 (by omega) 16 4096 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact sraw_close_su16_1_case_msb1 13 (by omega) 8 8192 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact sraw_close_su16_1_case_msb1 14 (by omega) 4 16384 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec
      | exact sraw_close_su16_1_case_msb1 15 (by omega) 2 32768 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring1)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1
          h_b0_dec h_b1_dec

end SP1Clean.ShiftRightMath
