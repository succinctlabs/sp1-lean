import SP1Clean.Proofs.Chips.ShiftRightChip.Core

/-! # ShiftRight dispatch lemmas (16-way within-byte case split)

For each shift variant (`srl`/`sra`/`srlw`/`sraw`) and byte-shift offset, one lemma performs the
16-way case split on the within-byte shift bits `cb0..cb3` and dispatches to the matching
`*_close_su16_*_case` reconstruction lemma, so `ShiftRightChip.soundness` discharges every
byte-shift case with a single `exact ShiftRightMath.<var>_dispatch_<bs> …`.

`hcb4`/`hcb5` fix the byte-shift offset (which limb window the result occupies); `b_cb0..b_cb3`
are the within-byte shift bits that get case-split. The `_msb1` lemmas are the negative
(sign-extending) arm of the arithmetic shifts. All are field-generic and axiom-clean.

Proof shape (load-bearing, do not revert): each lemma `rcases`es the four bit hypotheses with
`rfl`, so the `cb_i` become literals and the three side-condition tactic blocks are then uniform
across all sixteen cases; a local `key` fixes the twelve limb/decomposition arguments once; and the
cases are discharged by **ordered bullets**, one per `rcases` goal. `cb0` splits outermost, so the
shift amounts run `0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15`.

This replaced a 16-alternative `first | exact …` ladder that re-elaborated ~8 failing alternatives
per goal (each one a full `rw`/`push_cast`/`ring1`) and carried a 1000000-heartbeat ceiling on all
twelve lemmas. Laddered after the rewrite (LSP, with the mandatory 1-heartbeat control confirming
real re-elaboration): 200000 ok, 50000 ok, 35000 ok, 25000 FAILS (`whnf` /
`«synthesize pending MVars»`), 20000 FAILS. True floor (25k, 35k] — ≥5x headroom at the 200000
default, so all twelve ceilings were removed. -/

namespace SP1Clean.ShiftRightMath

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

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
  have key := fun (S M N : ℕ) (hS : S ≤ 15) (hMN : M * N = 65536) (hMpos : 0 < M)
      (hMeq : M = 2 ^ (16 - S)) (hNeq : N = 2 ^ S) (hMlt : M < p) hin htot hv =>
    srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) S hS M N hMN hMpos hMeq hNeq hMlt hv hin htot
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3 h_b0_dec h_b1_dec h_b2_dec h_b3_dec
  rcases b_cb0 with rfl | rfl <;> rcases b_cb1 with rfl | rfl <;>
    rcases b_cb2 with rfl | rfl <;> rcases b_cb3 with rfl | rfl
  · exact key 0 65536 1 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 8 256 256 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 4 4096 16 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 12 16 4096 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 2 16384 4 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 10 64 1024 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 6 1024 64 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 14 4 16384 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 1 32768 2 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 9 128 512 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 5 2048 32 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 13 8 8192 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 3 8192 8 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 11 32 2048 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 7 512 128 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 15 2 32768 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)

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
  have key := fun (S M N : ℕ) (hS : S ≤ 15) (hMN : M * N = 65536) (hMpos : 0 < M)
      (hMeq : M = 2 ^ (16 - S)) (hNeq : N = 2 ^ S) (hMlt : M < p) hin htot hv =>
    srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) S hS M N hMN hMpos hMeq hNeq hMlt hv hin htot
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3 h_b0_dec h_b1_dec h_b2_dec h_b3_dec
  rcases b_cb0 with rfl | rfl <;> rcases b_cb1 with rfl | rfl <;>
    rcases b_cb2 with rfl | rfl <;> rcases b_cb3 with rfl | rfl
  · exact key 0 65536 1 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 8 256 256 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 4 4096 16 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 12 16 4096 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 2 16384 4 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 10 64 1024 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 6 1024 64 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 14 4 16384 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 1 32768 2 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 9 128 512 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 5 2048 32 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 13 8 8192 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 3 8192 8 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 11 32 2048 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 7 512 128 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 15 2 32768 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)

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
  have key := fun (S M N : ℕ) (hS : S ≤ 15) (hMN : M * N = 65536) (hMpos : 0 < M)
      (hMeq : M = 2 ^ (16 - S)) (hNeq : N = 2 ^ S) (hMlt : M < p) hin htot hv =>
    srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) S hS M N hMN hMpos hMeq hNeq hMlt hv hin htot
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3 h_b0_dec h_b1_dec h_b2_dec h_b3_dec
  rcases b_cb0 with rfl | rfl <;> rcases b_cb1 with rfl | rfl <;>
    rcases b_cb2 with rfl | rfl <;> rcases b_cb3 with rfl | rfl
  · exact key 0 65536 1 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 8 256 256 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 4 4096 16 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 12 16 4096 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 2 16384 4 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 10 64 1024 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 6 1024 64 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 14 4 16384 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 1 32768 2 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 9 128 512 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 5 2048 32 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 13 8 8192 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 3 8192 8 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 11 32 2048 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 7 512 128 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 15 2 32768 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)

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
  have key := fun (S M N : ℕ) (hS : S ≤ 15) (hMN : M * N = 65536) (hMpos : 0 < M)
      (hMeq : M = 2 ^ (16 - S)) (hNeq : N = 2 ^ S) (hMlt : M < p) hin htot hv =>
    srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) S hS M N hMN hMpos hMeq hNeq hMlt hv hin htot
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3 h_b0_dec h_b1_dec h_b2_dec h_b3_dec
  rcases b_cb0 with rfl | rfl <;> rcases b_cb1 with rfl | rfl <;>
    rcases b_cb2 with rfl | rfl <;> rcases b_cb3 with rfl | rfl
  · exact key 0 65536 1 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 8 256 256 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 4 4096 16 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 12 16 4096 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 2 16384 4 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 10 64 1024 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 6 1024 64 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 14 4 16384 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 1 32768 2 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 9 128 512 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 5 2048 32 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 13 8 8192 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 3 8192 8 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 11 32 2048 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 7 512 128 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 15 2 32768 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)

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
  have key := fun (S M N : ℕ) (hS : S ≤ 15) (hMN : M * N = 65536) (hMpos : 0 < M)
      (hMeq : M = 2 ^ (16 - S)) (hNeq : N = 2 ^ S) (hMlt : M < p) hin htot hv =>
    sra_close_su16_0_case (cb4 := cb4) (cb5 := cb5) S hS M N hMN hMpos hMeq hNeq hMlt hv hin htot
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3 h_b0_dec h_b1_dec h_b2_dec h_b3_dec
  rcases b_cb0 with rfl | rfl <;> rcases b_cb1 with rfl | rfl <;>
    rcases b_cb2 with rfl | rfl <;> rcases b_cb3 with rfl | rfl
  · exact key 0 65536 1 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 8 256 256 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 4 4096 16 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 12 16 4096 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 2 16384 4 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 10 64 1024 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 6 1024 64 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 14 4 16384 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 1 32768 2 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 9 128 512 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 5 2048 32 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 13 8 8192 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 3 8192 8 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 11 32 2048 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 7 512 128 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 15 2 32768 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)

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
  have key := fun (S M N : ℕ) (hS : S ≤ 15) (hMN : M * N = 65536) (hMpos : 0 < M)
      (hMeq : M = 2 ^ (16 - S)) (hNeq : N = 2 ^ S) (hMlt : M < p) hin htot hv =>
    sra_close_su16_1_case (cb4 := cb4) (cb5 := cb5) S hS M N hMN hMpos hMeq hNeq hMlt hv hin htot
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3 h_b0_dec h_b1_dec h_b2_dec h_b3_dec
  rcases b_cb0 with rfl | rfl <;> rcases b_cb1 with rfl | rfl <;>
    rcases b_cb2 with rfl | rfl <;> rcases b_cb3 with rfl | rfl
  · exact key 0 65536 1 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 8 256 256 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 4 4096 16 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 12 16 4096 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 2 16384 4 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 10 64 1024 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 6 1024 64 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 14 4 16384 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 1 32768 2 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 9 128 512 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 5 2048 32 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 13 8 8192 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 3 8192 8 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 11 32 2048 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 7 512 128 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 15 2 32768 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)

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
  have key := fun (S M N : ℕ) (hS : S ≤ 15) (hMN : M * N = 65536) (hMpos : 0 < M)
      (hMeq : M = 2 ^ (16 - S)) (hNeq : N = 2 ^ S) (hMlt : M < p) hin htot hv =>
    sra_close_su16_2_case (cb4 := cb4) (cb5 := cb5) S hS M N hMN hMpos hMeq hNeq hMlt hv hin htot
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3 h_b0_dec h_b1_dec h_b2_dec h_b3_dec
  rcases b_cb0 with rfl | rfl <;> rcases b_cb1 with rfl | rfl <;>
    rcases b_cb2 with rfl | rfl <;> rcases b_cb3 with rfl | rfl
  · exact key 0 65536 1 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 8 256 256 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 4 4096 16 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 12 16 4096 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 2 16384 4 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 10 64 1024 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 6 1024 64 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 14 4 16384 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 1 32768 2 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 9 128 512 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 5 2048 32 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 13 8 8192 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 3 8192 8 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 11 32 2048 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 7 512 128 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 15 2 32768 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)

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
  have key := fun (S M N : ℕ) (hS : S ≤ 15) (hMN : M * N = 65536) (hMpos : 0 < M)
      (hMeq : M = 2 ^ (16 - S)) (hNeq : N = 2 ^ S) (hMlt : M < p) hin htot hv =>
    sra_close_su16_3_case (cb4 := cb4) (cb5 := cb5) S hS M N hMN hMpos hMeq hNeq hMlt hv hin htot
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3 h_b0_dec h_b1_dec h_b2_dec h_b3_dec
  rcases b_cb0 with rfl | rfl <;> rcases b_cb1 with rfl | rfl <;>
    rcases b_cb2 with rfl | rfl <;> rcases b_cb3 with rfl | rfl
  · exact key 0 65536 1 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 8 256 256 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 4 4096 16 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 12 16 4096 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 2 16384 4 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 10 64 1024 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 6 1024 64 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 14 4 16384 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 1 32768 2 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 9 128 512 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 5 2048 32 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 13 8 8192 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 3 8192 8 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 11 32 2048 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 7 512 128 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 15 2 32768 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4, hcb5]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)

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
  have key := fun (S M N : ℕ) (hS : S ≤ 15) (hMN : M * N = 65536) (hMpos : 0 < M)
      (hMeq : M = 2 ^ (16 - S)) (hNeq : N = 2 ^ S) (hMlt : M < p) hin htot hv =>
    srlw_close_su16_0_case (cb4 := cb4) S hS M N hMN hMpos hMeq hNeq hMlt hv hin htot
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
  rcases b_cb0 with rfl | rfl <;> rcases b_cb1 with rfl | rfl <;>
    rcases b_cb2 with rfl | rfl <;> rcases b_cb3 with rfl | rfl
  · exact key 0 65536 1 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 8 256 256 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 4 4096 16 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 12 16 4096 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 2 16384 4 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 10 64 1024 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 6 1024 64 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 14 4 16384 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 1 32768 2 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 9 128 512 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 5 2048 32 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 13 8 8192 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 3 8192 8 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 11 32 2048 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 7 512 128 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 15 2 32768 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)

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
  have key := fun (S M N : ℕ) (hS : S ≤ 15) (hMN : M * N = 65536) (hMpos : 0 < M)
      (hMeq : M = 2 ^ (16 - S)) (hNeq : N = 2 ^ S) (hMlt : M < p) hin htot hv =>
    srlw_close_su16_1_case (cb4 := cb4) S hS M N hMN hMpos hMeq hNeq hMlt hv hin htot
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
  rcases b_cb0 with rfl | rfl <;> rcases b_cb1 with rfl | rfl <;>
    rcases b_cb2 with rfl | rfl <;> rcases b_cb3 with rfl | rfl
  · exact key 0 65536 1 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 8 256 256 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 4 4096 16 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 12 16 4096 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 2 16384 4 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 10 64 1024 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 6 1024 64 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 14 4 16384 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 1 32768 2 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 9 128 512 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 5 2048 32 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 13 8 8192 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 3 8192 8 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 11 32 2048 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 7 512 128 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 15 2 32768 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)

/-- SRAW (arithmetic word, 32-bit) negative arm, byte-shift 0: dispatch to
`sraw_close_su16_0_case_msb1`. -/
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
  have key := fun (S M N : ℕ) (hS : S ≤ 15) (hMN : M * N = 65536) (hMpos : 0 < M)
      (hMeq : M = 2 ^ (16 - S)) (hNeq : N = 2 ^ S) (hMlt : M < p) hin htot hv =>
    sraw_close_su16_0_case_msb1 (cb4 := cb4) S hS M N hMN hMpos hMeq hNeq hMlt hv hin htot
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
  rcases b_cb0 with rfl | rfl <;> rcases b_cb1 with rfl | rfl <;>
    rcases b_cb2 with rfl | rfl <;> rcases b_cb3 with rfl | rfl
  · exact key 0 65536 1 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 8 256 256 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 4 4096 16 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 12 16 4096 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 2 16384 4 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 10 64 1024 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 6 1024 64 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 14 4 16384 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 1 32768 2 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 9 128 512 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 5 2048 32 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 13 8 8192 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 3 8192 8 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 11 32 2048 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 7 512 128 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 15 2 32768 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)

/-- SRAW (arithmetic word, 32-bit) negative arm, byte-shift 1: dispatch to
`sraw_close_su16_1_case_msb1`. -/
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
  have key := fun (S M N : ℕ) (hS : S ≤ 15) (hMN : M * N = 65536) (hMpos : 0 < M)
      (hMeq : M = 2 ^ (16 - S)) (hNeq : N = 2 ^ S) (hMlt : M < p) hin htot hv =>
    sraw_close_su16_1_case_msb1 (cb4 := cb4) S hS M N hMN hMpos hMeq hNeq hMlt hv hin htot
      lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
  rcases b_cb0 with rfl | rfl <;> rcases b_cb1 with rfl | rfl <;>
    rcases b_cb2 with rfl | rfl <;> rcases b_cb3 with rfl | rfl
  · exact key 0 65536 1 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 8 256 256 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 4 4096 16 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 12 16 4096 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 2 16384 4 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 10 64 1024 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 6 1024 64 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 14 4 16384 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 1 32768 2 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 9 128 512 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 5 2048 32 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 13 8 8192 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 3 8192 8 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 11 32 2048 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 7 512 128 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)
  · exact key 15 2 32768 (by omega) (by decide) (by omega) rfl rfl (by omega) (by push_cast; ring1)
      (by rw [hcb4]; push_cast; ring1) (by rw [eq_v0123, eq_v012, eq_v01]; push_cast; ring1)

end SP1Clean.ShiftRightMath
