import SP1Clean.Foundations.Word
import SP1Clean.Foundations.HWord
import SP1Clean.Foundations.Bitwise
import SP1Clean.Operations.ShiftBounds
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases

/-! # Native shift-left arithmetic core

Pure field/`ℕ`-arithmetic lemmas bridging SP1's `ShiftLeft` limb/byte decomposition to the `BitVec`
left shift, stated over loose `Word`/`ZMod p` variables (not a structured `cols`). The keystone:
after field-dividing the per-limb bit-split by `v0123` (invertible), every term is `< 2 ^ 17`, so
the `ℕ`-lift needs no stronger field bound. Used by `ShiftLeftChip`'s soundness. -/

namespace SP1Clean.ShiftLeftCore

open SP1Clean (Word HWord)
open SP1Clean.ShiftBounds

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## Field constants for the shift-amount modulus -/

@[simp] lemma val_64_zmod_p [NeZero p] : (64 : ZMod p).val = 64 := by
  have : (131072 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  exact ZMod.val_natCast_of_lt (show (64 : ℕ) < p by omega)

lemma val_64_ne_zero [NeZero p] : (64 : ZMod p) ≠ 0 := by
  have h : (64 : ZMod p).val = 64 := val_64_zmod_p
  intro hz; rw [hz] at h; simp at h

/-! ## Shift-amount decomposition and field-division cancellation -/

/-- From `((c0 - m) * 64⁻¹).val < 1024`, conclude `c0 ≡ m (mod 64)` — ties the witnessed `c_bits`
decomposition `m` to the low 6 bits of the shift-amount source `c0` (`extractLsb 5 0`). -/
lemma is_mod_64 {c0 m : ZMod p}
    (h_m_lt : m.val < 64) (_h_c0_lt : c0.val < 65536)
    (h_diff : ((c0 - m) * (64 : ZMod p)⁻¹).val < 1024) :
    c0.val % 64 = m.val := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  set k := (c0 - m) * (64 : ZMod p)⁻¹ with k_def
  have h_k_lt : k.val < 1024 := h_diff
  have h_64_ne : (64 : ZMod p) ≠ 0 := val_64_ne_zero
  have h_diff_eq : c0 - m = k * 64 := by rw [k_def]; field_simp
  have h_c0_eq : c0 = m + k * 64 := by linear_combination h_diff_eq
  have h_k64_val : (k * 64).val = k.val * 64 := by
    rw [show (64 : ZMod p) = ((64 : ℕ) : ZMod p) from by push_cast; rfl]
    rw [ZMod.val_mul_of_lt]
    · rw [show ((64 : ℕ) : ZMod p).val = 64 from val_64_zmod_p]
    · rw [show ((64 : ℕ) : ZMod p).val = 64 from val_64_zmod_p]
      have : k.val * 64 < 1024 * 64 := Nat.mul_lt_mul_of_lt_of_le h_k_lt (le_refl 64) (by omega)
      omega
  have h_c0_val : c0.val = m.val + k.val * 64 := by
    have : c0.val = (m + k * 64).val := by rw [h_c0_eq]
    rw [this, ZMod.val_add_of_lt]
    · rw [h_k64_val]
    · rw [h_k64_val]; omega
  rw [h_c0_val]; omega

/-- Field-divide the per-limb bit-split by the (invertible) power `x = v0123`: `a * x = b * 65536 + c * x`
becomes `a = b * (65536 / x.val) + c`, where `65536 / x.val = 2 ^ (16 - bitShift)`. After this the terms
are `< 2 ^ 17`, so the `ℕ`-lift needs only `2 ^ 17 < p`. -/
lemma cancel_mul_65536 {a b c x : ZMod p}
    (h_x_dvd : x.val ∣ 65536) (h_x_pos : 0 < x.val) :
    a * x = b * 65536 + c * x → a = b * (((65536 / x.val : ℕ) : ZMod p)) + c := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  intro h_eq
  set z : ℕ := 65536 / x.val with z_def
  have h_x_le : x.val ≤ 65536 := Nat.le_of_dvd (by omega) h_x_dvd
  have h_z_pos : 0 < z := Nat.div_pos h_x_le h_x_pos
  have h_xz : x.val * z = 65536 := by rw [z_def, Nat.mul_div_cancel' h_x_dvd]
  have h_xz_zmod : x * ((z : ℕ) : ZMod p) = 65536 := by
    have : ((x.val : ZMod p)) * ((z : ℕ) : ZMod p) = ((x.val * z : ℕ) : ZMod p) := by push_cast; ring
    rw [ZMod.natCast_zmod_val] at this
    rw [this, h_xz]; push_cast; rfl
  have h_eq2 : a * x = (b * ((z : ℕ) : ZMod p) + c) * x := by
    rw [← h_xz_zmod] at h_eq; linear_combination h_eq
  have h_x_ne : x ≠ 0 := by
    intro h; have : x.val = 0 := by rw [h]; exact ZMod.val_zero
    omega
  exact mul_right_cancel₀ h_x_ne h_eq2

/-! ## The within-byte (bit) shift identity -/

set_option maxHeartbeats 4000000 in
set_option linter.unusedVariables false in
/-- The within-byte-shift keystone: given the four per-limb decompositions `b_j = hl_j * N + ll_j` with the
range bounds (`ll_j < N`, `hl_j < M`, `M * N = 65536`, `v0123.val = M`), the reassembled `limb_result`
equals `b <<< bitShift` mod `2 ^ 64` (i.e. `b.toNat * M % 2 ^ 64`). The ~85-line `.val` computation, once. -/
lemma sll_within_byte_shift
    (M N : ℕ) (h_MN : M * N = 65536) (h_M_pos : 0 < M)
    {b0 b1 b2 b3 ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 v0123 : ZMod p}
    (h_v_val : v0123.val = M)
    (lt_ll0 : ll0.val < N) (lt_ll1 : ll1.val < N)
    (lt_ll2 : ll2.val < N) (lt_ll3 : ll3.val < N)
    (lt_lh0 : hl0.val < M) (lt_lh1 : hl1.val < M)
    (lt_lh2 : hl2.val < M) (lt_lh3 : hl3.val < M)
    (h_b0 : b0 = hl0 * ((N : ℕ) : ZMod p) + ll0)
    (h_b1 : b1 = hl1 * ((N : ℕ) : ZMod p) + ll1)
    (h_b2 : b2 = hl2 * ((N : ℕ) : ZMod p) + ll2)
    (h_b3 : b3 = hl3 * ((N : ℕ) : ZMod p) + ll3) :
    (Word.toBitVec64 #v[ll0 * v0123, ll1 * v0123 + hl0, ll2 * v0123 + hl1,
                              ll3 * v0123 + hl2]).toNat
    = (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat * M % 2 ^ 64 := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_ll0_mul : (ll0 * v0123).val = ll0.val * M := mul_v_val h_MN h_v_val lt_ll0
  have h_b0_val : b0.val = hl0.val * N + ll0.val := by rw [h_b0]; exact hi_lo_val h_MN lt_lh0 lt_ll0
  have h_b1_val : b1.val = hl1.val * N + ll1.val := by rw [h_b1]; exact hi_lo_val h_MN lt_lh1 lt_ll1
  have h_b2_val : b2.val = hl2.val * N + ll2.val := by rw [h_b2]; exact hi_lo_val h_MN lt_lh2 lt_ll2
  have h_b3_val : b3.val = hl3.val * N + ll3.val := by rw [h_b3]; exact hi_lo_val h_MN lt_lh3 lt_ll3
  have h_compose1_val : (ll1 * v0123 + hl0).val = ll1.val * M + hl0.val :=
    mul_v_add_val h_MN h_v_val lt_ll1 lt_lh0
  have h_compose2_val : (ll2 * v0123 + hl1).val = ll2.val * M + hl1.val :=
    mul_v_add_val h_MN h_v_val lt_ll2 lt_lh1
  have h_compose3_val : (ll3 * v0123 + hl2).val = ll3.val * M + hl2.val :=
    mul_v_add_val h_MN h_v_val lt_ll3 lt_lh2
  unfold Word.toBitVec64
  simp only [BitVec.toNat_ofNat, Word.toNat_def, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  rw [h_ll0_mul, h_compose1_val, h_compose2_val, h_compose3_val,
      h_b0_val, h_b1_val, h_b2_val, h_b3_val]
  have h_key : (hl0.val * N + ll0.val + (hl1.val * N + ll1.val) * 2 ^ 16
                + (hl2.val * N + ll2.val) * 2 ^ 32 + (hl3.val * N + ll3.val) * 2 ^ 48) * M
              = (ll0.val * M + (ll1.val * M + hl0.val) * 2 ^ 16
                + (ll2.val * M + hl1.val) * 2 ^ 32 + (ll3.val * M + hl2.val) * 2 ^ 48)
                + hl3.val * 2 ^ 64 := by
    linear_combination
      (hl0.val + hl1.val * 2 ^ 16 + hl2.val * 2 ^ 32 + hl3.val * 2 ^ 48) * h_MN
  rw [Nat.mod_mul_mod, h_key, Nat.add_mul_mod_self_right]

set_option maxHeartbeats 4000000 in
set_option linter.unusedVariables false in
/-- Byte-shift=3 variant: the limb_result lands in the top limb only. -/
lemma sll_within_byte_shift_3
    (M N : ℕ) (h_MN : M * N = 65536) (h_M_pos : 0 < M)
    {b0 b1 b2 b3 ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 v0123 : ZMod p}
    (h_v_val : v0123.val = M)
    (lt_ll0 : ll0.val < N) (lt_ll1 : ll1.val < N)
    (lt_ll2 : ll2.val < N) (lt_ll3 : ll3.val < N)
    (lt_lh0 : hl0.val < M) (lt_lh1 : hl1.val < M)
    (lt_lh2 : hl2.val < M) (lt_lh3 : hl3.val < M)
    (h_b0 : b0 = hl0 * ((N : ℕ) : ZMod p) + ll0)
    (h_b1 : b1 = hl1 * ((N : ℕ) : ZMod p) + ll1)
    (h_b2 : b2 = hl2 * ((N : ℕ) : ZMod p) + ll2)
    (h_b3 : b3 = hl3 * ((N : ℕ) : ZMod p) + ll3) :
    (Word.toBitVec64 #v[0, 0, 0, ll0 * v0123]).toNat
    = (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat * M * 2 ^ 48 % 2 ^ 64 := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_ll0_mul : (ll0 * v0123).val = ll0.val * M := mul_v_val h_MN h_v_val lt_ll0
  have h_b0_val : b0.val = hl0.val * N + ll0.val := by rw [h_b0]; exact hi_lo_val h_MN lt_lh0 lt_ll0
  have h_b1_val : b1.val = hl1.val * N + ll1.val := by rw [h_b1]; exact hi_lo_val h_MN lt_lh1 lt_ll1
  have h_b2_val : b2.val = hl2.val * N + ll2.val := by rw [h_b2]; exact hi_lo_val h_MN lt_lh2 lt_ll2
  have h_b3_val : b3.val = hl3.val * N + ll3.val := by rw [h_b3]; exact hi_lo_val h_MN lt_lh3 lt_ll3
  unfold Word.toBitVec64
  simp only [BitVec.toNat_ofNat, Word.toNat_def, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, ZMod.val_zero,
    zero_mul, zero_add]
  rw [h_ll0_mul, h_b0_val, h_b1_val, h_b2_val, h_b3_val]
  have h_key : (hl0.val * N + ll0.val + (hl1.val * N + ll1.val) * 2 ^ 16
                + (hl2.val * N + ll2.val) * 2 ^ 32 + (hl3.val * N + ll3.val) * 2 ^ 48) * M
                * 2 ^ 48
              = ll0.val * M * 2 ^ 48
                + (hl0.val + ll1.val * M + hl1.val * 2 ^ 16 + ll2.val * M * 2 ^ 16
                   + hl2.val * 2 ^ 32 + ll3.val * M * 2 ^ 32 + hl3.val * 2 ^ 48) * 2 ^ 64 := by
    linear_combination
      (hl0.val + hl1.val * 2 ^ 16 + hl2.val * 2 ^ 32 + hl3.val * 2 ^ 48) * 2 ^ 48 * h_MN
  conv_rhs => rw [Nat.mul_assoc, Nat.mod_mul_mod, ← Nat.mul_assoc]
  rw [h_key, Nat.add_mul_mod_self_right]

set_option maxHeartbeats 4000000 in
set_option linter.unusedVariables false in
/-- Byte-shift=2 variant. -/
lemma sll_within_byte_shift_2
    (M N : ℕ) (h_MN : M * N = 65536) (h_M_pos : 0 < M)
    {b0 b1 b2 b3 ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 v0123 : ZMod p}
    (h_v_val : v0123.val = M)
    (lt_ll0 : ll0.val < N) (lt_ll1 : ll1.val < N)
    (lt_ll2 : ll2.val < N) (lt_ll3 : ll3.val < N)
    (lt_lh0 : hl0.val < M) (lt_lh1 : hl1.val < M)
    (lt_lh2 : hl2.val < M) (lt_lh3 : hl3.val < M)
    (h_b0 : b0 = hl0 * ((N : ℕ) : ZMod p) + ll0)
    (h_b1 : b1 = hl1 * ((N : ℕ) : ZMod p) + ll1)
    (h_b2 : b2 = hl2 * ((N : ℕ) : ZMod p) + ll2)
    (h_b3 : b3 = hl3 * ((N : ℕ) : ZMod p) + ll3) :
    (Word.toBitVec64 #v[0, 0, ll0 * v0123, ll1 * v0123 + hl0]).toNat
    = (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat * M * 2 ^ 32 % 2 ^ 64 := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_ll0_mul : (ll0 * v0123).val = ll0.val * M := mul_v_val h_MN h_v_val lt_ll0
  have h_b0_val : b0.val = hl0.val * N + ll0.val := by rw [h_b0]; exact hi_lo_val h_MN lt_lh0 lt_ll0
  have h_b1_val : b1.val = hl1.val * N + ll1.val := by rw [h_b1]; exact hi_lo_val h_MN lt_lh1 lt_ll1
  have h_b2_val : b2.val = hl2.val * N + ll2.val := by rw [h_b2]; exact hi_lo_val h_MN lt_lh2 lt_ll2
  have h_b3_val : b3.val = hl3.val * N + ll3.val := by rw [h_b3]; exact hi_lo_val h_MN lt_lh3 lt_ll3
  have h_compose1_val : (ll1 * v0123 + hl0).val = ll1.val * M + hl0.val :=
    mul_v_add_val h_MN h_v_val lt_ll1 lt_lh0
  unfold Word.toBitVec64
  simp only [BitVec.toNat_ofNat, Word.toNat_def, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, ZMod.val_zero,
    zero_mul, zero_add]
  rw [h_ll0_mul, h_compose1_val, h_b0_val, h_b1_val, h_b2_val, h_b3_val]
  have h_key : (hl0.val * N + ll0.val + (hl1.val * N + ll1.val) * 2 ^ 16
                + (hl2.val * N + ll2.val) * 2 ^ 32 + (hl3.val * N + ll3.val) * 2 ^ 48) * M
                * 2 ^ 32
              = ll0.val * M * 2 ^ 32 + (ll1.val * M + hl0.val) * 2 ^ 48
                + (hl1.val + ll2.val * M + hl2.val * 2 ^ 16 + ll3.val * M * 2 ^ 16
                   + hl3.val * 2 ^ 32) * 2 ^ 64 := by
    linear_combination
      (hl0.val + hl1.val * 2 ^ 16 + hl2.val * 2 ^ 32 + hl3.val * 2 ^ 48) * 2 ^ 32 * h_MN
  conv_rhs => rw [Nat.mul_assoc, Nat.mod_mul_mod, ← Nat.mul_assoc]
  rw [h_key, Nat.add_mul_mod_self_right]

set_option maxHeartbeats 4000000 in
set_option linter.unusedVariables false in
/-- Byte-shift=1 variant. -/
lemma sll_within_byte_shift_1
    (M N : ℕ) (h_MN : M * N = 65536) (h_M_pos : 0 < M)
    {b0 b1 b2 b3 ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 v0123 : ZMod p}
    (h_v_val : v0123.val = M)
    (lt_ll0 : ll0.val < N) (lt_ll1 : ll1.val < N)
    (lt_ll2 : ll2.val < N) (lt_ll3 : ll3.val < N)
    (lt_lh0 : hl0.val < M) (lt_lh1 : hl1.val < M)
    (lt_lh2 : hl2.val < M) (lt_lh3 : hl3.val < M)
    (h_b0 : b0 = hl0 * ((N : ℕ) : ZMod p) + ll0)
    (h_b1 : b1 = hl1 * ((N : ℕ) : ZMod p) + ll1)
    (h_b2 : b2 = hl2 * ((N : ℕ) : ZMod p) + ll2)
    (h_b3 : b3 = hl3 * ((N : ℕ) : ZMod p) + ll3) :
    (Word.toBitVec64 #v[0, ll0 * v0123, ll1 * v0123 + hl0, ll2 * v0123 + hl1]).toNat
    = (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat * M * 2 ^ 16 % 2 ^ 64 := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_ll0_mul : (ll0 * v0123).val = ll0.val * M := mul_v_val h_MN h_v_val lt_ll0
  have h_b0_val : b0.val = hl0.val * N + ll0.val := by rw [h_b0]; exact hi_lo_val h_MN lt_lh0 lt_ll0
  have h_b1_val : b1.val = hl1.val * N + ll1.val := by rw [h_b1]; exact hi_lo_val h_MN lt_lh1 lt_ll1
  have h_b2_val : b2.val = hl2.val * N + ll2.val := by rw [h_b2]; exact hi_lo_val h_MN lt_lh2 lt_ll2
  have h_b3_val : b3.val = hl3.val * N + ll3.val := by rw [h_b3]; exact hi_lo_val h_MN lt_lh3 lt_ll3
  have h_compose1_val : (ll1 * v0123 + hl0).val = ll1.val * M + hl0.val :=
    mul_v_add_val h_MN h_v_val lt_ll1 lt_lh0
  have h_compose2_val : (ll2 * v0123 + hl1).val = ll2.val * M + hl1.val :=
    mul_v_add_val h_MN h_v_val lt_ll2 lt_lh1
  unfold Word.toBitVec64
  simp only [BitVec.toNat_ofNat, Word.toNat_def, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, ZMod.val_zero,
    zero_add]
  rw [h_ll0_mul, h_compose1_val, h_compose2_val, h_b0_val, h_b1_val, h_b2_val, h_b3_val]
  have h_key : (hl0.val * N + ll0.val + (hl1.val * N + ll1.val) * 2 ^ 16
                + (hl2.val * N + ll2.val) * 2 ^ 32 + (hl3.val * N + ll3.val) * 2 ^ 48) * M
                * 2 ^ 16
              = ll0.val * M * 2 ^ 16 + (ll1.val * M + hl0.val) * 2 ^ 32
                + (ll2.val * M + hl1.val) * 2 ^ 48
                + (hl2.val + ll3.val * M + hl3.val * 2 ^ 16) * 2 ^ 64 := by
    linear_combination
      (hl0.val + hl1.val * 2 ^ 16 + hl2.val * 2 ^ 32 + hl3.val * 2 ^ 48) * 2 ^ 16 * h_MN
  conv_rhs => rw [Nat.mul_assoc, Nat.mod_mul_mod, ← Nat.mul_assoc]
  rw [h_key, Nat.add_mul_mod_self_right]

/-! ## Byte-shift placement wrappers (one per `(cb4, cb5)` combination) -/

set_option maxHeartbeats 4000000 in
/-- `cb4=cb5=0` (byte_shift=0): `limb_result` placed at limb 0. -/
lemma sll_close_cb4cb5_zero_case
    (S : ℕ) (h_S_le : S ≤ 15) (M N : ℕ)
    (h_MN : M * N = 65536) (h_M_pos : 0 < M) (h_M_eq : M = 2 ^ S)
    (h_N_eq : N = 2 ^ (16 - S))
    {cb0 cb1 cb2 cb3 cb4 cb5 v0123 b0 b1 b2 b3
      ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 : ZMod p}
    (h_v_val : v0123.val = M)
    (h_inner_eq : cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8
                  = ((S : ℕ) : ZMod p))
    (h_total_eq : cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32
                  = ((S : ℕ) : ZMod p))
    (lt_ll0 : ll0.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_lh0 : hl0.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (lt_ll1 : ll1.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_lh1 : hl1.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (lt_ll2 : ll2.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_lh2 : hl2.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (lt_ll3 : ll3.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_lh3 : hl3.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (h_b0_dec : b0 * v0123 = hl0 * ((65536 : ℕ) : ZMod p) + ll0 * v0123)
    (h_b1_dec : b1 * v0123 = hl1 * ((65536 : ℕ) : ZMod p) + ll1 * v0123)
    (h_b2_dec : b2 * v0123 = hl2 * ((65536 : ℕ) : ZMod p) + ll2 * v0123)
    (h_b3_dec : b3 * v0123 = hl3 * ((65536 : ℕ) : ZMod p) + ll3 * v0123) :
    (Word.toBitVec64 #v[ll0 * v0123, ll1 * v0123 + hl0, ll2 * v0123 + hl1,
                              ll3 * v0123 + hl2]).toNat
    = (Word.toBitVec64 #v[b0, b1, b2, b3]
        <<< (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val).toNat
        := by
  rw [BitVec.toNat_shiftLeft]
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_inner_val : (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                      + cb3 * 8 : ZMod p).val = S := by
    rw [h_inner_eq]; exact ZMod.val_natCast_of_lt (by omega)
  have h_inner_hi_val : (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                + cb3 * 8) : ZMod p).val = 16 - S := by
    rw [show (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
              + cb3 * 8) : ZMod p) = (((16 - S) : ℕ) : ZMod p) from by
      rw [h_inner_eq, Nat.cast_sub (by omega : S ≤ 16)]; push_cast; ring]
    exact ZMod.val_natCast_of_lt (by omega)
  rw [h_inner_val] at lt_lh0 lt_lh1 lt_lh2 lt_lh3
  rw [h_inner_hi_val] at lt_ll0 lt_ll1 lt_ll2 lt_ll3
  have h_total_val : (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val
                      = S := by
    rw [h_total_eq]; exact ZMod.val_natCast_of_lt (by omega)
  rw [h_total_val]
  have hdvd : v0123.val ∣ 65536 := by rw [h_v_val]; exact ⟨N, h_MN.symm⟩
  have hpos : 0 < v0123.val := by rw [h_v_val]; exact h_M_pos
  have h_b0' := cancel_mul_65536 hdvd hpos h_b0_dec
  have h_b1' := cancel_mul_65536 hdvd hpos h_b1_dec
  have h_b2' := cancel_mul_65536 hdvd hpos h_b2_dec
  have h_b3' := cancel_mul_65536 hdvd hpos h_b3_dec
  rw [h_v_val] at h_b0' h_b1' h_b2' h_b3'
  rw [show (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat <<< S
          = (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat * M from by
        rw [Nat.shiftLeft_eq, h_M_eq]]
  have h_div_eq : (65536 : ℕ) / M = N := by
    rw [← h_MN]; exact Nat.mul_div_cancel_left N h_M_pos
  rw [h_div_eq] at h_b0' h_b1' h_b2' h_b3'
  have h_lt_ll0 : ll0.val < N := by rw [h_N_eq]; exact lt_ll0
  have h_lt_ll1 : ll1.val < N := by rw [h_N_eq]; exact lt_ll1
  have h_lt_ll2 : ll2.val < N := by rw [h_N_eq]; exact lt_ll2
  have h_lt_ll3 : ll3.val < N := by rw [h_N_eq]; exact lt_ll3
  have h_lt_lh0 : hl0.val < M := by rw [h_M_eq]; exact lt_lh0
  have h_lt_lh1 : hl1.val < M := by rw [h_M_eq]; exact lt_lh1
  have h_lt_lh2 : hl2.val < M := by rw [h_M_eq]; exact lt_lh2
  have h_lt_lh3 : hl3.val < M := by rw [h_M_eq]; exact lt_lh3
  exact sll_within_byte_shift M N h_MN h_M_pos h_v_val
    h_lt_ll0 h_lt_ll1 h_lt_ll2 h_lt_ll3 h_lt_lh0 h_lt_lh1 h_lt_lh2 h_lt_lh3
    h_b0' h_b1' h_b2' h_b3'

set_option maxHeartbeats 4000000 in
/-- `cb4=cb5=1` (byte_shift=3): `limb_result` placed at limb 3 only. -/
lemma sll_close_cb4cb5_one_one_case
    (S : ℕ) (h_S_le : S ≤ 15) (M N : ℕ)
    (h_MN : M * N = 65536) (h_M_pos : 0 < M) (h_M_eq : M = 2 ^ S)
    (h_N_eq : N = 2 ^ (16 - S))
    {cb0 cb1 cb2 cb3 cb4 cb5 v0123 b0 b1 b2 b3
      ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 : ZMod p}
    (h_v_val : v0123.val = M)
    (h_inner_eq : cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8
                  = ((S : ℕ) : ZMod p))
    (h_total_eq : cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32
                  = (((S + 48) : ℕ) : ZMod p))
    (lt_ll0 : ll0.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_lh0 : hl0.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (lt_ll1 : ll1.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_lh1 : hl1.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (lt_ll2 : ll2.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_lh2 : hl2.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (lt_ll3 : ll3.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_lh3 : hl3.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (h_b0_dec : b0 * v0123 = hl0 * ((65536 : ℕ) : ZMod p) + ll0 * v0123)
    (h_b1_dec : b1 * v0123 = hl1 * ((65536 : ℕ) : ZMod p) + ll1 * v0123)
    (h_b2_dec : b2 * v0123 = hl2 * ((65536 : ℕ) : ZMod p) + ll2 * v0123)
    (h_b3_dec : b3 * v0123 = hl3 * ((65536 : ℕ) : ZMod p) + ll3 * v0123) :
    (Word.toBitVec64 #v[0, 0, 0, ll0 * v0123]).toNat
    = (Word.toBitVec64 #v[b0, b1, b2, b3]
        <<< (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val).toNat
        := by
  rw [BitVec.toNat_shiftLeft]
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_inner_val : (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                      + cb3 * 8 : ZMod p).val = S := by
    rw [h_inner_eq]; exact ZMod.val_natCast_of_lt (by omega)
  have h_inner_hi_val : (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                + cb3 * 8) : ZMod p).val = 16 - S := by
    rw [show (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
              + cb3 * 8) : ZMod p) = (((16 - S) : ℕ) : ZMod p) from by
      rw [h_inner_eq, Nat.cast_sub (by omega : S ≤ 16)]; push_cast; ring]
    exact ZMod.val_natCast_of_lt (by omega)
  rw [h_inner_val] at lt_lh0 lt_lh1 lt_lh2 lt_lh3
  rw [h_inner_hi_val] at lt_ll0 lt_ll1 lt_ll2 lt_ll3
  have h_total_val : (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val
                      = S + 48 := by
    rw [h_total_eq]; exact ZMod.val_natCast_of_lt (by omega)
  rw [h_total_val]
  have hdvd : v0123.val ∣ 65536 := by rw [h_v_val]; exact ⟨N, h_MN.symm⟩
  have hpos : 0 < v0123.val := by rw [h_v_val]; exact h_M_pos
  have h_b0' := cancel_mul_65536 hdvd hpos h_b0_dec
  have h_b1' := cancel_mul_65536 hdvd hpos h_b1_dec
  have h_b2' := cancel_mul_65536 hdvd hpos h_b2_dec
  have h_b3' := cancel_mul_65536 hdvd hpos h_b3_dec
  rw [h_v_val] at h_b0' h_b1' h_b2' h_b3'
  rw [show (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat <<< (S + 48)
          = (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat * M * 2 ^ 48 from by
        rw [Nat.shiftLeft_eq, h_M_eq, pow_add, ← Nat.mul_assoc]]
  have h_div_eq : (65536 : ℕ) / M = N := by
    rw [← h_MN]; exact Nat.mul_div_cancel_left N h_M_pos
  rw [h_div_eq] at h_b0' h_b1' h_b2' h_b3'
  have h_lt_ll0 : ll0.val < N := by rw [h_N_eq]; exact lt_ll0
  have h_lt_ll1 : ll1.val < N := by rw [h_N_eq]; exact lt_ll1
  have h_lt_ll2 : ll2.val < N := by rw [h_N_eq]; exact lt_ll2
  have h_lt_ll3 : ll3.val < N := by rw [h_N_eq]; exact lt_ll3
  have h_lt_lh0 : hl0.val < M := by rw [h_M_eq]; exact lt_lh0
  have h_lt_lh1 : hl1.val < M := by rw [h_M_eq]; exact lt_lh1
  have h_lt_lh2 : hl2.val < M := by rw [h_M_eq]; exact lt_lh2
  have h_lt_lh3 : hl3.val < M := by rw [h_M_eq]; exact lt_lh3
  exact sll_within_byte_shift_3 M N h_MN h_M_pos h_v_val
    h_lt_ll0 h_lt_ll1 h_lt_ll2 h_lt_ll3 h_lt_lh0 h_lt_lh1 h_lt_lh2 h_lt_lh3
    h_b0' h_b1' h_b2' h_b3'

set_option maxHeartbeats 4000000 in
/-- `cb4=0, cb5=1` (byte_shift=2): `limb_result` placed at limb 2. -/
lemma sll_close_cb4cb5_zero_one_case
    (S : ℕ) (h_S_le : S ≤ 15) (M N : ℕ)
    (h_MN : M * N = 65536) (h_M_pos : 0 < M) (h_M_eq : M = 2 ^ S)
    (h_N_eq : N = 2 ^ (16 - S))
    {cb0 cb1 cb2 cb3 cb4 cb5 v0123 b0 b1 b2 b3
      ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 : ZMod p}
    (h_v_val : v0123.val = M)
    (h_inner_eq : cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8
                  = ((S : ℕ) : ZMod p))
    (h_total_eq : cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32
                  = (((S + 32) : ℕ) : ZMod p))
    (lt_ll0 : ll0.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_lh0 : hl0.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (lt_ll1 : ll1.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_lh1 : hl1.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (lt_ll2 : ll2.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_lh2 : hl2.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (lt_ll3 : ll3.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_lh3 : hl3.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (h_b0_dec : b0 * v0123 = hl0 * ((65536 : ℕ) : ZMod p) + ll0 * v0123)
    (h_b1_dec : b1 * v0123 = hl1 * ((65536 : ℕ) : ZMod p) + ll1 * v0123)
    (h_b2_dec : b2 * v0123 = hl2 * ((65536 : ℕ) : ZMod p) + ll2 * v0123)
    (h_b3_dec : b3 * v0123 = hl3 * ((65536 : ℕ) : ZMod p) + ll3 * v0123) :
    (Word.toBitVec64 #v[0, 0, ll0 * v0123, ll1 * v0123 + hl0]).toNat
    = (Word.toBitVec64 #v[b0, b1, b2, b3]
        <<< (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val).toNat
        := by
  rw [BitVec.toNat_shiftLeft]
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_inner_val : (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                      + cb3 * 8 : ZMod p).val = S := by
    rw [h_inner_eq]; exact ZMod.val_natCast_of_lt (by omega)
  have h_inner_hi_val : (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                + cb3 * 8) : ZMod p).val = 16 - S := by
    rw [show (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
              + cb3 * 8) : ZMod p) = (((16 - S) : ℕ) : ZMod p) from by
      rw [h_inner_eq, Nat.cast_sub (by omega : S ≤ 16)]; push_cast; ring]
    exact ZMod.val_natCast_of_lt (by omega)
  rw [h_inner_val] at lt_lh0 lt_lh1 lt_lh2 lt_lh3
  rw [h_inner_hi_val] at lt_ll0 lt_ll1 lt_ll2 lt_ll3
  have h_total_val : (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val
                      = S + 32 := by
    rw [h_total_eq]; exact ZMod.val_natCast_of_lt (by omega)
  rw [h_total_val]
  have hdvd : v0123.val ∣ 65536 := by rw [h_v_val]; exact ⟨N, h_MN.symm⟩
  have hpos : 0 < v0123.val := by rw [h_v_val]; exact h_M_pos
  have h_b0' := cancel_mul_65536 hdvd hpos h_b0_dec
  have h_b1' := cancel_mul_65536 hdvd hpos h_b1_dec
  have h_b2' := cancel_mul_65536 hdvd hpos h_b2_dec
  have h_b3' := cancel_mul_65536 hdvd hpos h_b3_dec
  rw [h_v_val] at h_b0' h_b1' h_b2' h_b3'
  rw [show (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat <<< (S + 32)
          = (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat * M * 2 ^ 32 from by
        rw [Nat.shiftLeft_eq, h_M_eq, pow_add, ← Nat.mul_assoc]]
  have h_div_eq : (65536 : ℕ) / M = N := by
    rw [← h_MN]; exact Nat.mul_div_cancel_left N h_M_pos
  rw [h_div_eq] at h_b0' h_b1' h_b2' h_b3'
  have h_lt_ll0 : ll0.val < N := by rw [h_N_eq]; exact lt_ll0
  have h_lt_ll1 : ll1.val < N := by rw [h_N_eq]; exact lt_ll1
  have h_lt_ll2 : ll2.val < N := by rw [h_N_eq]; exact lt_ll2
  have h_lt_ll3 : ll3.val < N := by rw [h_N_eq]; exact lt_ll3
  have h_lt_lh0 : hl0.val < M := by rw [h_M_eq]; exact lt_lh0
  have h_lt_lh1 : hl1.val < M := by rw [h_M_eq]; exact lt_lh1
  have h_lt_lh2 : hl2.val < M := by rw [h_M_eq]; exact lt_lh2
  have h_lt_lh3 : hl3.val < M := by rw [h_M_eq]; exact lt_lh3
  exact sll_within_byte_shift_2 M N h_MN h_M_pos h_v_val
    h_lt_ll0 h_lt_ll1 h_lt_ll2 h_lt_ll3 h_lt_lh0 h_lt_lh1 h_lt_lh2 h_lt_lh3
    h_b0' h_b1' h_b2' h_b3'

set_option maxHeartbeats 4000000 in
/-- `cb4=1, cb5=0` (byte_shift=1): `limb_result` placed at limb 1. -/
lemma sll_close_cb4cb5_one_zero_case
    (S : ℕ) (h_S_le : S ≤ 15) (M N : ℕ)
    (h_MN : M * N = 65536) (h_M_pos : 0 < M) (h_M_eq : M = 2 ^ S)
    (h_N_eq : N = 2 ^ (16 - S))
    {cb0 cb1 cb2 cb3 cb4 cb5 v0123 b0 b1 b2 b3
      ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 : ZMod p}
    (h_v_val : v0123.val = M)
    (h_inner_eq : cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8
                  = ((S : ℕ) : ZMod p))
    (h_total_eq : cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32
                  = (((S + 16) : ℕ) : ZMod p))
    (lt_ll0 : ll0.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_lh0 : hl0.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (lt_ll1 : ll1.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_lh1 : hl1.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (lt_ll2 : ll2.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_lh2 : hl2.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (lt_ll3 : ll3.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_lh3 : hl3.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (h_b0_dec : b0 * v0123 = hl0 * ((65536 : ℕ) : ZMod p) + ll0 * v0123)
    (h_b1_dec : b1 * v0123 = hl1 * ((65536 : ℕ) : ZMod p) + ll1 * v0123)
    (h_b2_dec : b2 * v0123 = hl2 * ((65536 : ℕ) : ZMod p) + ll2 * v0123)
    (h_b3_dec : b3 * v0123 = hl3 * ((65536 : ℕ) : ZMod p) + ll3 * v0123) :
    (Word.toBitVec64 #v[0, ll0 * v0123, ll1 * v0123 + hl0, ll2 * v0123 + hl1]).toNat
    = (Word.toBitVec64 #v[b0, b1, b2, b3]
        <<< (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val).toNat
        := by
  rw [BitVec.toNat_shiftLeft]
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_inner_val : (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                      + cb3 * 8 : ZMod p).val = S := by
    rw [h_inner_eq]; exact ZMod.val_natCast_of_lt (by omega)
  have h_inner_hi_val : (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                + cb3 * 8) : ZMod p).val = 16 - S := by
    rw [show (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
              + cb3 * 8) : ZMod p) = (((16 - S) : ℕ) : ZMod p) from by
      rw [h_inner_eq, Nat.cast_sub (by omega : S ≤ 16)]; push_cast; ring]
    exact ZMod.val_natCast_of_lt (by omega)
  rw [h_inner_val] at lt_lh0 lt_lh1 lt_lh2 lt_lh3
  rw [h_inner_hi_val] at lt_ll0 lt_ll1 lt_ll2 lt_ll3
  have h_total_val : (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val
                      = S + 16 := by
    rw [h_total_eq]; exact ZMod.val_natCast_of_lt (by omega)
  rw [h_total_val]
  have hdvd : v0123.val ∣ 65536 := by rw [h_v_val]; exact ⟨N, h_MN.symm⟩
  have hpos : 0 < v0123.val := by rw [h_v_val]; exact h_M_pos
  have h_b0' := cancel_mul_65536 hdvd hpos h_b0_dec
  have h_b1' := cancel_mul_65536 hdvd hpos h_b1_dec
  have h_b2' := cancel_mul_65536 hdvd hpos h_b2_dec
  have h_b3' := cancel_mul_65536 hdvd hpos h_b3_dec
  rw [h_v_val] at h_b0' h_b1' h_b2' h_b3'
  rw [show (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat <<< (S + 16)
          = (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat * M * 2 ^ 16 from by
        rw [Nat.shiftLeft_eq, h_M_eq, pow_add, ← Nat.mul_assoc]]
  have h_div_eq : (65536 : ℕ) / M = N := by
    rw [← h_MN]; exact Nat.mul_div_cancel_left N h_M_pos
  rw [h_div_eq] at h_b0' h_b1' h_b2' h_b3'
  have h_lt_ll0 : ll0.val < N := by rw [h_N_eq]; exact lt_ll0
  have h_lt_ll1 : ll1.val < N := by rw [h_N_eq]; exact lt_ll1
  have h_lt_ll2 : ll2.val < N := by rw [h_N_eq]; exact lt_ll2
  have h_lt_ll3 : ll3.val < N := by rw [h_N_eq]; exact lt_ll3
  have h_lt_lh0 : hl0.val < M := by rw [h_M_eq]; exact lt_lh0
  have h_lt_lh1 : hl1.val < M := by rw [h_M_eq]; exact lt_lh1
  have h_lt_lh2 : hl2.val < M := by rw [h_M_eq]; exact lt_lh2
  have h_lt_lh3 : hl3.val < M := by rw [h_M_eq]; exact lt_lh3
  exact sll_within_byte_shift_1 M N h_MN h_M_pos h_v_val
    h_lt_ll0 h_lt_ll1 h_lt_ll2 h_lt_ll3 h_lt_lh0 h_lt_lh1 h_lt_lh2 h_lt_lh3
    h_b0' h_b1' h_b2' h_b3'

/-! ## The `v0123` power encoding -/

/-- `(2 ^ S : ZMod p).val = 2 ^ S` for `S ≤ 15` (the power fits below `2 ^ 17 < p`). Stated through a
`ZMod p`-equation hypothesis so the 16-way enumeration can discharge it by `push_cast; norm_num`. -/
lemma val_eq_pow {S : ℕ} (hS : S ≤ 15) {x : ZMod p} (hx : x = ((2 ^ S : ℕ) : ZMod p)) :
    x.val = 2 ^ S := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have hlt : (2 : ℕ) ^ S < p := by
    have h2S : (2 : ℕ) ^ S ≤ 2 ^ 15 := Nat.pow_le_pow_right (by norm_num) hS
    have e15 : (2 : ℕ) ^ 15 = 32768 := by norm_num
    have e17 : (2 : ℕ) ^ 17 = 131072 := by norm_num
    omega
  subst hx
  exact ZMod.val_natCast_of_lt hlt

/-- The power encoding `v0123 = (cb0+1)(3cb1+1)(15cb2+1)(255cb3+1)` evaluates to `2 ^ S` where `S` is the
low-four shift-amount bits `cb0 + 2cb1 + 4cb2 + 8cb3` — the keystone tying the witnessed `v0123` to a
concrete power. Proved by enumerating the 16 boolean `cb`-patterns. -/
lemma v0123_pow {cb0 cb1 cb2 cb3 v01 v012 v0123 : ZMod p}
    (hb0 : cb0 = 0 ∨ cb0 = 1) (hb1 : cb1 = 0 ∨ cb1 = 1)
    (hb2 : cb2 = 0 ∨ cb2 = 1) (hb3 : cb3 = 0 ∨ cb3 = 1)
    (hv01 : v01 = (cb0 + 1) * (cb1 * 3 + 1))
    (hv012 : v012 = v01 * (cb2 * 15 + 1))
    (hv0123 : v0123 = v012 * (cb3 * 255 + 1)) :
    ∃ S : ℕ, S ≤ 15 ∧ v0123.val = 2 ^ S ∧
      cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8 = ((S : ℕ) : ZMod p) := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have hv : v0123 = (cb0 + 1) * (cb1 * 3 + 1) * (cb2 * 15 + 1) * (cb3 * 255 + 1) := by
    rw [hv0123, hv012, hv01]
  rw [hv]
  rcases hb0 with h0 | h0 <;> rcases hb1 with h1 | h1 <;>
    rcases hb2 with h2 | h2 <;> rcases hb3 with h3 | h3 <;> subst h0 h1 h2 h3
  -- 16 goals in `(cb0,cb1,cb2,cb3)` lexicographic order; witness `S = cb0+2cb1+4cb2+8cb3`.
  · exact ⟨0, by norm_num, val_eq_pow (by norm_num) (by push_cast; ring), by push_cast; ring⟩
  · exact ⟨8, by norm_num, val_eq_pow (by norm_num) (by push_cast; ring), by push_cast; ring⟩
  · exact ⟨4, by norm_num, val_eq_pow (by norm_num) (by push_cast; ring), by push_cast; ring⟩
  · exact ⟨12, by norm_num, val_eq_pow (by norm_num) (by push_cast; ring), by push_cast; ring⟩
  · exact ⟨2, by norm_num, val_eq_pow (by norm_num) (by push_cast; ring), by push_cast; ring⟩
  · exact ⟨10, by norm_num, val_eq_pow (by norm_num) (by push_cast; ring), by push_cast; ring⟩
  · exact ⟨6, by norm_num, val_eq_pow (by norm_num) (by push_cast; ring), by push_cast; ring⟩
  · exact ⟨14, by norm_num, val_eq_pow (by norm_num) (by push_cast; ring), by push_cast; ring⟩
  · exact ⟨1, by norm_num, val_eq_pow (by norm_num) (by push_cast; ring), by push_cast; ring⟩
  · exact ⟨9, by norm_num, val_eq_pow (by norm_num) (by push_cast; ring), by push_cast; ring⟩
  · exact ⟨5, by norm_num, val_eq_pow (by norm_num) (by push_cast; ring), by push_cast; ring⟩
  · exact ⟨13, by norm_num, val_eq_pow (by norm_num) (by push_cast; ring), by push_cast; ring⟩
  · exact ⟨3, by norm_num, val_eq_pow (by norm_num) (by push_cast; ring), by push_cast; ring⟩
  · exact ⟨11, by norm_num, val_eq_pow (by norm_num) (by push_cast; ring), by push_cast; ring⟩
  · exact ⟨7, by norm_num, val_eq_pow (by norm_num) (by push_cast; ring), by push_cast; ring⟩
  · exact ⟨15, by norm_num, val_eq_pow (by norm_num) (by push_cast; ring), by push_cast; ring⟩

/-! ## Shift-amount bound and the full SLL placement assembly -/

/-- Each `cb_i ∈ {0,1}`, so the weighted shift-amount sum `cb0 + 2cb1 + 4cb2 + 8cb3 + 16cb4 + 32cb5`
has `.val < 64` (no field wrap below `2 ^ 17 < p`). Mirrors sp1-lean's `h_cb_sum_lt`. -/
lemma cb_sum6_val_lt_64 {cb0 cb1 cb2 cb3 cb4 cb5 : ZMod p}
    (hb0 : cb0 = 0 ∨ cb0 = 1) (hb1 : cb1 = 0 ∨ cb1 = 1) (hb2 : cb2 = 0 ∨ cb2 = 1)
    (hb3 : cb3 = 0 ∨ cb3 = 1) (hb4 : cb4 = 0 ∨ cb4 = 1) (hb5 : cb5 = 0 ∨ cb5 = 1) :
    (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val < 64 := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_v0 : (0 : ZMod p).val = 0 := ZMod.val_zero
  have h_v1 : (1 : ZMod p).val = 1 := ZMod.val_one p
  have h_v2 : (2 : ZMod p).val = 2 := val_2_zmod_p
  have h_v4 : (4 : ZMod p).val = 4 := by
    rw [show (4 : ZMod p) = ((4 : ℕ) : ZMod p) from by push_cast; rfl]
    exact ZMod.val_natCast_of_lt (by omega)
  have h_v8 : (8 : ZMod p).val = 8 := by
    rw [show (8 : ZMod p) = ((8 : ℕ) : ZMod p) from by push_cast; rfl]
    exact ZMod.val_natCast_of_lt (by omega)
  have h_v16 : (16 : ZMod p).val = 16 := by
    rw [show (16 : ZMod p) = ((16 : ℕ) : ZMod p) from by push_cast; rfl]
    exact ZMod.val_natCast_of_lt (by omega)
  have h_v32 : (32 : ZMod p).val = 32 := by
    rw [show (32 : ZMod p) = ((32 : ℕ) : ZMod p) from by push_cast; rfl]
    exact ZMod.val_natCast_of_lt (by omega)
  have hc0 : cb0.val ≤ 1 := by rcases hb0 with h | h <;> rw [h] <;> simp [h_v0, h_v1]
  have hc1 : cb1.val ≤ 1 := by rcases hb1 with h | h <;> rw [h] <;> simp [h_v0, h_v1]
  have hc2 : cb2.val ≤ 1 := by rcases hb2 with h | h <;> rw [h] <;> simp [h_v0, h_v1]
  have hc3 : cb3.val ≤ 1 := by rcases hb3 with h | h <;> rw [h] <;> simp [h_v0, h_v1]
  have hc4 : cb4.val ≤ 1 := by rcases hb4 with h | h <;> rw [h] <;> simp [h_v0, h_v1]
  have hc5 : cb5.val ≤ 1 := by rcases hb5 with h | h <;> rw [h] <;> simp [h_v0, h_v1]
  have m1 : (cb1 * 2).val ≤ 2 := by
    rw [ZMod.val_mul_of_lt] <;> rw [h_v2] <;> omega
  have m2 : (cb2 * 4).val ≤ 4 := by
    rw [ZMod.val_mul_of_lt] <;> rw [h_v4] <;> omega
  have m3 : (cb3 * 8).val ≤ 8 := by
    rw [ZMod.val_mul_of_lt] <;> rw [h_v8] <;> omega
  have m4 : (cb4 * 16).val ≤ 16 := by
    rw [ZMod.val_mul_of_lt] <;> rw [h_v16] <;> omega
  have m5 : (cb5 * 32).val ≤ 32 := by
    rw [ZMod.val_mul_of_lt] <;> rw [h_v32] <;> omega
  have s1 : (cb0 + cb1 * 2).val ≤ 3 := by
    rw [ZMod.val_add_of_lt] <;> omega
  have s2 : (cb0 + cb1 * 2 + cb2 * 4).val ≤ 7 := by
    rw [ZMod.val_add_of_lt] <;> omega
  have s3 : (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8).val ≤ 15 := by
    rw [ZMod.val_add_of_lt] <;> omega
  have s4 : (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16).val ≤ 31 := by
    rw [ZMod.val_add_of_lt] <;> omega
  rw [ZMod.val_add_of_lt] <;> omega

omit [Fact (2 ^ 17 < p)] in
/-- `s * k = 0` with `k ≠ 0` forces `s = 0` (used to read the one-hot byte-shift selector). Avoids
`mul_eq_zero` (which misfires on `ZMod p`) via `mul_right_cancel₀`. -/
lemma eq_zero_of_mul_const {s k : ZMod p} (hk : k ≠ 0) (h : s * k = 0) : s = 0 :=
  mul_right_cancel₀ hk (by rw [h, zero_mul])

omit [Fact (2 ^ 17 < p)] in
/-- `(toBitVec64 w).toNat % 64 = w[0].val % 64` — the low-6-bit shift amount depends only on the bottom
limb. Lifted to a top-level lemma so the kernel walks the `2 ^ 16/32/48` literals once (keeps the chip
soundness term clear of the inline `2 ^ N` deep-recursion landmine). -/
lemma toBitVec64_toNat_mod64 {w : Word (ZMod p)} (hw : Word.isU64 w) :
    (Word.toBitVec64 w).toNat % 64 = w[0].val % 64 := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  rw [Word.toBitVec64_toNat hw, Word.toNat_def,
    show (2:ℕ)^16 = 65536 from by norm_num, show (2:ℕ)^32 = 4294967296 from by norm_num,
    show (2:ℕ)^48 = 281474976710656 from by norm_num]
  omega

set_option maxHeartbeats 4000000 in
/-- **SLL placement assembly.** Given the witnessed shift columns satisfying the inline constraints
(bit decomposition, `v0123` power `M = 2^S`, the one-hot byte-shift selector, the per-limb bit-splits and
`limb_result` reassembly, and the `is_sll`-collapsed output placements), the output word equals
`op_b <<< (c0.val % 64)`. The four byte-shift positions are dispatched to the matching
`sll_close_cb4cb5_*_case`. Pure field/`Word` statement — the chip soundness feeds it the evaluated
columns. -/
lemma sll_assembly
    {a0 a1 a2 a3 b0 b1 b2 b3 c0 cb0 cb1 cb2 cb3 cb4 cb5 v0123
     s0 s1 s2 s3 ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 lr0 lr1 lr2 lr3 : ZMod p}
    (S : ℕ) (hS_le : S ≤ 15) (M N : ℕ) (hMN : M * N = 65536) (hM_pos : 0 < M)
    (hM_eq : M = 2 ^ S) (hN_eq : N = 2 ^ (16 - S))
    (h_v0123_val : v0123.val = M)
    (h_inner : cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8 = ((S : ℕ) : ZMod p))
    (hb_cb4 : cb4 = 0 ∨ cb4 = 1) (hb_cb5 : cb5 = 0 ∨ cb5 = 1)
    (h_c0_lt : c0.val < 65536)
    (h_cb_sum_lt : (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val < 64)
    (h_diff : ((c0 - (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32)) * (64 : ZMod p)⁻¹).val < 1024)
    (h_s0sel : s0 * (cb4 + cb5 * 2 - 0) = 0) (h_s1sel : s1 * (cb4 + cb5 * 2 - 1) = 0)
    (h_s2sel : s2 * (cb4 + cb5 * 2 - 2) = 0) (h_s3sel : s3 * (cb4 + cb5 * 2 - 3) = 0)
    (h_ssum : s0 + s1 + s2 + s3 = 1)
    (h_b0dec : b0 * v0123 = hl0 * ((65536 : ℕ) : ZMod p) + ll0 * v0123)
    (h_b1dec : b1 * v0123 = hl1 * ((65536 : ℕ) : ZMod p) + ll1 * v0123)
    (h_b2dec : b2 * v0123 = hl2 * ((65536 : ℕ) : ZMod p) + ll2 * v0123)
    (h_b3dec : b3 * v0123 = hl3 * ((65536 : ℕ) : ZMod p) + ll3 * v0123)
    (h_lr0 : lr0 = ll0 * v0123) (h_lr1 : lr1 = ll1 * v0123 + hl0)
    (h_lr2 : lr2 = ll2 * v0123 + hl1) (h_lr3 : lr3 = ll3 * v0123 + hl2)
    (h_ll0 : ll0.val < N) (h_hl0 : hl0.val < M) (h_ll1 : ll1.val < N) (h_hl1 : hl1.val < M)
    (h_ll2 : ll2.val < N) (h_hl2 : hl2.val < M) (h_ll3 : ll3.val < N) (h_hl3 : hl3.val < M)
    (h_p00 : s0 * (a0 - lr0) = 0) (h_p01 : s0 * (a1 - lr1) = 0)
    (h_p02 : s0 * (a2 - lr2) = 0) (h_p03 : s0 * (a3 - lr3) = 0)
    (h_p10 : s1 * a0 = 0) (h_p11 : s1 * (a1 - lr0) = 0)
    (h_p12 : s1 * (a2 - lr1) = 0) (h_p13 : s1 * (a3 - lr2) = 0)
    (h_p20 : s2 * a0 = 0) (h_p21 : s2 * a1 = 0)
    (h_p22 : s2 * (a2 - lr0) = 0) (h_p23 : s2 * (a3 - lr1) = 0)
    (h_p30 : s3 * a0 = 0) (h_p31 : s3 * a1 = 0)
    (h_p32 : s3 * a2 = 0) (h_p33 : s3 * (a3 - lr0) = 0) :
    Word.toBitVec64 #v[a0, a1, a2, a3]
      = Word.toBitVec64 #v[b0, b1, b2, b3] <<< (c0.val % 64) := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  -- Small nonzero field constants for reading the one-hot selectors.
  have hv2 : (2 : ZMod p).val = 2 := val_2_zmod_p
  have hv3 : (3 : ZMod p).val = 3 := by
    rw [show (3 : ZMod p) = ((3 : ℕ) : ZMod p) from by push_cast; rfl]
    exact ZMod.val_natCast_of_lt (by omega)
  have n1 : (1 : ZMod p) ≠ 0 := one_ne_zero
  have n2 : (2 : ZMod p) ≠ 0 := fun h => by rw [h, ZMod.val_zero] at hv2; omega
  have n3 : (3 : ZMod p) ≠ 0 := fun h => by rw [h, ZMod.val_zero] at hv3; omega
  -- The shift amount: c0 mod 64 equals the witnessed cb-sum.
  have h_mod : c0.val % 64 = (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val :=
    is_mod_64 h_cb_sum_lt h_c0_lt h_diff
  rw [h_mod]
  apply BitVec.eq_of_toNat_eq
  -- Exponent `.val`s in close-lemma form.
  have hMexp : (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8 : ZMod p).val = S := by
    rw [h_inner]; exact ZMod.val_natCast_of_lt (by omega)
  have hNexp : ((16 : ZMod p) - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8)).val
      = 16 - S := by
    rw [h_inner, show (16 : ZMod p) - ((S : ℕ) : ZMod p) = (((16 - S : ℕ)) : ZMod p) from by
      rw [Nat.cast_sub (show S ≤ 16 by omega)]; push_cast; ring]
    exact ZMod.val_natCast_of_lt (by omega)
  -- Convert the plain `< N` / `< M` bounds into the close-lemma exponent form.
  have hll0' : ll0.val < 2 ^ ((16 : ZMod p) - (cb0 + cb1 * ((2:ℕ):ZMod p) + cb2 * ((4:ℕ):ZMod p) + cb3 * 8)).val := by
    rw [hNexp, ← hN_eq]; exact h_ll0
  have hll1' : ll1.val < 2 ^ ((16 : ZMod p) - (cb0 + cb1 * ((2:ℕ):ZMod p) + cb2 * ((4:ℕ):ZMod p) + cb3 * 8)).val := by
    rw [hNexp, ← hN_eq]; exact h_ll1
  have hll2' : ll2.val < 2 ^ ((16 : ZMod p) - (cb0 + cb1 * ((2:ℕ):ZMod p) + cb2 * ((4:ℕ):ZMod p) + cb3 * 8)).val := by
    rw [hNexp, ← hN_eq]; exact h_ll2
  have hll3' : ll3.val < 2 ^ ((16 : ZMod p) - (cb0 + cb1 * ((2:ℕ):ZMod p) + cb2 * ((4:ℕ):ZMod p) + cb3 * 8)).val := by
    rw [hNexp, ← hN_eq]; exact h_ll3
  have hhl0' : hl0.val < 2 ^ (cb0 + cb1 * ((2:ℕ):ZMod p) + cb2 * ((4:ℕ):ZMod p) + cb3 * 8 : ZMod p).val := by
    rw [hMexp, ← hM_eq]; exact h_hl0
  have hhl1' : hl1.val < 2 ^ (cb0 + cb1 * ((2:ℕ):ZMod p) + cb2 * ((4:ℕ):ZMod p) + cb3 * 8 : ZMod p).val := by
    rw [hMexp, ← hM_eq]; exact h_hl1
  have hhl2' : hl2.val < 2 ^ (cb0 + cb1 * ((2:ℕ):ZMod p) + cb2 * ((4:ℕ):ZMod p) + cb3 * 8 : ZMod p).val := by
    rw [hMexp, ← hM_eq]; exact h_hl2
  have hhl3' : hl3.val < 2 ^ (cb0 + cb1 * ((2:ℕ):ZMod p) + cb2 * ((4:ℕ):ZMod p) + cb3 * 8 : ZMod p).val := by
    rw [hMexp, ← hM_eq]; exact h_hl3
  -- Dispatch on the byte-shift position `cb4 + 2·cb5`.
  rcases hb_cb4 with h4 | h4 <;> rcases hb_cb5 with h5 | h5
  · -- cb4 = 0, cb5 = 0 → byteShift = 0 → s0 = 1.
    rw [h4, h5] at h_s1sel h_s2sel h_s3sel
    have hs1 : s1 = 0 := eq_zero_of_mul_const (h := h_s1sel)
      (hk := by rw [show ((0:ZMod p) + 0 * 2 - 1) = -1 from by ring]; exact neg_ne_zero.mpr n1)
    have hs2 : s2 = 0 := eq_zero_of_mul_const (h := h_s2sel)
      (hk := by rw [show ((0:ZMod p) + 0 * 2 - 2) = -2 from by ring]; exact neg_ne_zero.mpr n2)
    have hs3 : s3 = 0 := eq_zero_of_mul_const (h := h_s3sel)
      (hk := by rw [show ((0:ZMod p) + 0 * 2 - 3) = -3 from by ring]; exact neg_ne_zero.mpr n3)
    have hs0 : s0 = 1 := by rw [hs1, hs2, hs3] at h_ssum; linear_combination h_ssum
    have ha0 : a0 = lr0 := by rw [hs0, one_mul] at h_p00; linear_combination h_p00
    have ha1 : a1 = lr1 := by rw [hs0, one_mul] at h_p01; linear_combination h_p01
    have ha2 : a2 = lr2 := by rw [hs0, one_mul] at h_p02; linear_combination h_p02
    have ha3 : a3 = lr3 := by rw [hs0, one_mul] at h_p03; linear_combination h_p03
    have htot : cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32 = ((S : ℕ) : ZMod p) := by
      rw [h4, h5]; push_cast at h_inner ⊢; linear_combination h_inner
    rw [ha0, ha1, ha2, ha3, h_lr0, h_lr1, h_lr2, h_lr3]
    exact sll_close_cb4cb5_zero_case S hS_le M N hMN hM_pos hM_eq hN_eq h_v0123_val h_inner htot
      hll0' hhl0' hll1' hhl1' hll2' hhl2' hll3' hhl3' h_b0dec h_b1dec h_b2dec h_b3dec
  · -- cb4 = 0, cb5 = 1 → byteShift = 2 → s2 = 1.
    rw [h4, h5] at h_s0sel h_s1sel h_s3sel
    have hs0 : s0 = 0 := eq_zero_of_mul_const (h := h_s0sel)
      (hk := by rw [show ((0:ZMod p) + 1 * 2 - 0) = 2 from by ring]; exact n2)
    have hs1 : s1 = 0 := eq_zero_of_mul_const (h := h_s1sel)
      (hk := by rw [show ((0:ZMod p) + 1 * 2 - 1) = 1 from by ring]; exact n1)
    have hs3 : s3 = 0 := eq_zero_of_mul_const (h := h_s3sel)
      (hk := by rw [show ((0:ZMod p) + 1 * 2 - 3) = -1 from by ring]; exact neg_ne_zero.mpr n1)
    have hs2 : s2 = 1 := by rw [hs0, hs1, hs3] at h_ssum; linear_combination h_ssum
    have ha0 : a0 = 0 := by rw [hs2, one_mul] at h_p20; exact h_p20
    have ha1 : a1 = 0 := by rw [hs2, one_mul] at h_p21; exact h_p21
    have ha2 : a2 = lr0 := by rw [hs2, one_mul] at h_p22; linear_combination h_p22
    have ha3 : a3 = lr1 := by rw [hs2, one_mul] at h_p23; linear_combination h_p23
    have htot : cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32 = (((S + 32) : ℕ) : ZMod p) := by
      rw [h4, h5]; push_cast at h_inner ⊢; linear_combination h_inner
    rw [ha0, ha1, ha2, ha3, h_lr0, h_lr1]
    exact sll_close_cb4cb5_zero_one_case S hS_le M N hMN hM_pos hM_eq hN_eq h_v0123_val h_inner htot
      hll0' hhl0' hll1' hhl1' hll2' hhl2' hll3' hhl3' h_b0dec h_b1dec h_b2dec h_b3dec
  · -- cb4 = 1, cb5 = 0 → byteShift = 1 → s1 = 1.
    rw [h4, h5] at h_s0sel h_s2sel h_s3sel
    have hs0 : s0 = 0 := eq_zero_of_mul_const (h := h_s0sel)
      (hk := by rw [show ((1:ZMod p) + 0 * 2 - 0) = 1 from by ring]; exact n1)
    have hs2 : s2 = 0 := eq_zero_of_mul_const (h := h_s2sel)
      (hk := by rw [show ((1:ZMod p) + 0 * 2 - 2) = -1 from by ring]; exact neg_ne_zero.mpr n1)
    have hs3 : s3 = 0 := eq_zero_of_mul_const (h := h_s3sel)
      (hk := by rw [show ((1:ZMod p) + 0 * 2 - 3) = -2 from by ring]; exact neg_ne_zero.mpr n2)
    have hs1 : s1 = 1 := by rw [hs0, hs2, hs3] at h_ssum; linear_combination h_ssum
    have ha0 : a0 = 0 := by rw [hs1, one_mul] at h_p10; exact h_p10
    have ha1 : a1 = lr0 := by rw [hs1, one_mul] at h_p11; linear_combination h_p11
    have ha2 : a2 = lr1 := by rw [hs1, one_mul] at h_p12; linear_combination h_p12
    have ha3 : a3 = lr2 := by rw [hs1, one_mul] at h_p13; linear_combination h_p13
    have htot : cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32 = (((S + 16) : ℕ) : ZMod p) := by
      rw [h4, h5]; push_cast at h_inner ⊢; linear_combination h_inner
    rw [ha0, ha1, ha2, ha3, h_lr0, h_lr1, h_lr2]
    exact sll_close_cb4cb5_one_zero_case S hS_le M N hMN hM_pos hM_eq hN_eq h_v0123_val h_inner htot
      hll0' hhl0' hll1' hhl1' hll2' hhl2' hll3' hhl3' h_b0dec h_b1dec h_b2dec h_b3dec
  · -- cb4 = 1, cb5 = 1 → byteShift = 3 → s3 = 1.
    rw [h4, h5] at h_s0sel h_s1sel h_s2sel
    have hs0 : s0 = 0 := eq_zero_of_mul_const (h := h_s0sel)
      (hk := by rw [show ((1:ZMod p) + 1 * 2 - 0) = 3 from by ring]; exact n3)
    have hs1 : s1 = 0 := eq_zero_of_mul_const (h := h_s1sel)
      (hk := by rw [show ((1:ZMod p) + 1 * 2 - 1) = 2 from by ring]; exact n2)
    have hs2 : s2 = 0 := eq_zero_of_mul_const (h := h_s2sel)
      (hk := by rw [show ((1:ZMod p) + 1 * 2 - 2) = 1 from by ring]; exact n1)
    have hs3 : s3 = 1 := by rw [hs0, hs1, hs2] at h_ssum; linear_combination h_ssum
    have ha0 : a0 = 0 := by rw [hs3, one_mul] at h_p30; exact h_p30
    have ha1 : a1 = 0 := by rw [hs3, one_mul] at h_p31; exact h_p31
    have ha2 : a2 = 0 := by rw [hs3, one_mul] at h_p32; exact h_p32
    have ha3 : a3 = lr0 := by rw [hs3, one_mul] at h_p33; linear_combination h_p33
    have htot : cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32 = (((S + 48) : ℕ) : ZMod p) := by
      rw [h4, h5]; push_cast at h_inner ⊢; linear_combination h_inner
    rw [ha0, ha1, ha2, ha3, h_lr0]
    exact sll_close_cb4cb5_one_one_case S hS_le M N hMN hM_pos hM_eq hN_eq h_v0123_val h_inner htot
      hll0' hhl0' hll1' hhl1' hll2' hhl2' hll3' hhl3' h_b0dec h_b1dec h_b2dec h_b3dec

/-! ## SLLW (32-bit shift-left-word) within-byte identities and assembly

The 2-limb (`HWord`, 32-bit) analogs of the SLL machinery, used by the SLLW soundness branch. The shift
amount is the low **5** bits of `c0` (`cb0 + 2cb1 + 4cb2 + 8cb3 + 16cb4`, no `cb5`), the byte-shift is
`cb4 ∈ {0,1}` (since `is_sll = 0`), and the 64-bit result is the **sign extension** of the 32-bit shifted
value — realised natively via `Word.toBitVec64_signExtend_word` (the high two limbs are `msb * 65535`). -/

set_option maxHeartbeats 4000000 in
/-- HWord (2-limb, 32-bit) analog of `sll_within_byte_shift`: byte_shift=0 within-byte identity. -/
lemma sllw_within_byte_shift
    (M N : ℕ) (h_MN : M * N = 65536) (h_M_pos : 0 < M)
    {b0 b1 ll0 ll1 hl0 hl1 v0123 : ZMod p}
    (h_v_val : v0123.val = M)
    (lt_ll0 : ll0.val < N) (lt_ll1 : ll1.val < N)
    (lt_lh0 : hl0.val < M) (lt_lh1 : hl1.val < M)
    (h_b0 : b0 = hl0 * ((N : ℕ) : ZMod p) + ll0)
    (h_b1 : b1 = hl1 * ((N : ℕ) : ZMod p) + ll1) :
    (HWord.toBitVec32 #v[ll0 * v0123, ll1 * v0123 + hl0]).toNat
    = (HWord.toBitVec32 #v[b0, b1]).toNat * M % 2 ^ 32 := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_N_lt_p : N < p := by nlinarith [h_MN]
  have h_N_val : ((N : ℕ) : ZMod p).val = N := ZMod.val_natCast_of_lt h_N_lt_p
  have h_NM : N * M = 65536 := by linarith [h_MN, Nat.mul_comm M N]
  have h_ll0_mul : (ll0 * v0123).val = ll0.val * M := by
    rw [ZMod.val_mul_of_lt, h_v_val]; rw [h_v_val]; nlinarith [lt_ll0, h_MN]
  have h_ll1_mul : (ll1 * v0123).val = ll1.val * M := by
    rw [ZMod.val_mul_of_lt, h_v_val]; rw [h_v_val]; nlinarith [lt_ll1, h_MN]
  have h_hl0_mul : (hl0 * ((N : ℕ) : ZMod p)).val = hl0.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh0, h_MN, h_NM]
  have h_hl1_mul : (hl1 * ((N : ℕ) : ZMod p)).val = hl1.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh1, h_MN, h_NM]
  have h_b0_val : b0.val = hl0.val * N + ll0.val := by
    rw [h_b0, ZMod.val_add_of_lt]
    · rw [h_hl0_mul]
    · rw [h_hl0_mul]; nlinarith [lt_ll0, lt_lh0, h_MN, h_NM]
  have h_b1_val : b1.val = hl1.val * N + ll1.val := by
    rw [h_b1, ZMod.val_add_of_lt]
    · rw [h_hl1_mul]
    · rw [h_hl1_mul]; nlinarith [lt_ll1, lt_lh1, h_MN, h_NM]
  have h_compose1_val : (ll1 * v0123 + hl0).val = ll1.val * M + hl0.val := by
    rw [ZMod.val_add_of_lt]
    · rw [h_ll1_mul]
    · rw [h_ll1_mul]; nlinarith [lt_ll1, lt_lh0, h_MN]
  unfold HWord.toBitVec32
  simp only [BitVec.toNat_ofNat, HWord.toNat, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  rw [h_ll0_mul, h_compose1_val, h_b0_val, h_b1_val]
  have h_key : (hl0.val * N + ll0.val + (hl1.val * N + ll1.val) * 2 ^ 16) * M
              = (ll0.val * M + (ll1.val * M + hl0.val) * 2 ^ 16) + hl1.val * 2 ^ 32 := by
    linear_combination (hl0.val + hl1.val * 2 ^ 16) * h_MN
  rw [Nat.mod_mul_mod, h_key, Nat.add_mul_mod_self_right]

set_option maxHeartbeats 4000000 in
/-- HWord analog of `sll_within_byte_shift_1`: byte_shift=1 within-byte identity (low limb zero). -/
lemma sllw_within_byte_shift_1
    (M N : ℕ) (h_MN : M * N = 65536) (h_M_pos : 0 < M)
    {b0 b1 ll0 ll1 hl0 hl1 v0123 : ZMod p}
    (h_v_val : v0123.val = M)
    (lt_ll0 : ll0.val < N) (lt_ll1 : ll1.val < N)
    (lt_lh0 : hl0.val < M) (lt_lh1 : hl1.val < M)
    (h_b0 : b0 = hl0 * ((N : ℕ) : ZMod p) + ll0)
    (h_b1 : b1 = hl1 * ((N : ℕ) : ZMod p) + ll1) :
    (HWord.toBitVec32 #v[0, ll0 * v0123]).toNat
    = (HWord.toBitVec32 #v[b0, b1]).toNat * M * 2 ^ 16 % 2 ^ 32 := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_N_lt_p : N < p := by nlinarith [h_MN]
  have h_N_val : ((N : ℕ) : ZMod p).val = N := ZMod.val_natCast_of_lt h_N_lt_p
  have h_NM : N * M = 65536 := by linarith [h_MN, Nat.mul_comm M N]
  have h_ll0_mul : (ll0 * v0123).val = ll0.val * M := by
    rw [ZMod.val_mul_of_lt, h_v_val]; rw [h_v_val]; nlinarith [lt_ll0, h_MN]
  have h_hl0_mul : (hl0 * ((N : ℕ) : ZMod p)).val = hl0.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh0, h_MN, h_NM]
  have h_hl1_mul : (hl1 * ((N : ℕ) : ZMod p)).val = hl1.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh1, h_MN, h_NM]
  have h_b0_val : b0.val = hl0.val * N + ll0.val := by
    rw [h_b0, ZMod.val_add_of_lt]
    · rw [h_hl0_mul]
    · rw [h_hl0_mul]; nlinarith [lt_ll0, lt_lh0, h_MN, h_NM]
  have h_b1_val : b1.val = hl1.val * N + ll1.val := by
    rw [h_b1, ZMod.val_add_of_lt]
    · rw [h_hl1_mul]
    · rw [h_hl1_mul]; nlinarith [lt_ll1, lt_lh1, h_MN, h_NM]
  unfold HWord.toBitVec32
  simp only [BitVec.toNat_ofNat, HWord.toNat, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, ZMod.val_zero,
    zero_add]
  rw [h_ll0_mul, h_b0_val, h_b1_val]
  have h_key : (hl0.val * N + ll0.val + (hl1.val * N + ll1.val) * 2 ^ 16) * M * 2 ^ 16
              = ll0.val * M * 2 ^ 16 + (hl0.val + ll1.val * M + hl1.val * 2 ^ 16) * 2 ^ 32 := by
    linear_combination (hl0.val + hl1.val * 2 ^ 16) * 2 ^ 16 * h_MN
  conv_rhs => rw [Nat.mul_assoc, Nat.mod_mul_mod, ← Nat.mul_assoc]
  rw [h_key, Nat.add_mul_mod_self_right]

set_option maxHeartbeats 4000000 in
/-- SLLW `cb4=0` close-case wrapper: combines `cancel_mul_65536`, the exponent `.val` normalization,
and the `<<<`-to-`*` bridge for the byte_shift=0 32-bit shift identity. -/
lemma sllw_close_cb4_zero_case
    (S : ℕ) (h_S_le : S ≤ 15) (M N : ℕ)
    (h_MN : M * N = 65536) (h_M_pos : 0 < M) (h_M_eq : M = 2 ^ S)
    (h_N_eq : N = 2 ^ (16 - S))
    {cb0 cb1 cb2 cb3 cb4 v0123 b0 b1 ll0 ll1 hl0 hl1 : ZMod p}
    (h_v_val : v0123.val = M)
    (h_inner_eq : cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8
                  = ((S : ℕ) : ZMod p))
    (h_total_eq : cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16
                  = ((S : ℕ) : ZMod p))
    (lt_ll0 : ll0.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_lh0 : hl0.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (lt_ll1 : ll1.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_lh1 : hl1.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (h_b0_dec : b0 * v0123 = hl0 * ((65536 : ℕ) : ZMod p) + ll0 * v0123)
    (h_b1_dec : b1 * v0123 = hl1 * ((65536 : ℕ) : ZMod p) + ll1 * v0123) :
    (HWord.toBitVec32 #v[ll0 * v0123, ll1 * v0123 + hl0]).toNat
    = (HWord.toBitVec32 #v[b0, b1]).toNat
        <<< (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16).val
      % 2 ^ 32 := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_inner_val : (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                      + cb3 * 8 : ZMod p).val = S := by
    rw [h_inner_eq]; exact ZMod.val_natCast_of_lt (by omega)
  have h_inner_hi_val : (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                + cb3 * 8) : ZMod p).val = 16 - S := by
    rw [show (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
              + cb3 * 8) : ZMod p) = (((16 - S) : ℕ) : ZMod p) from by
      rw [h_inner_eq, Nat.cast_sub (by omega : S ≤ 16)]; push_cast; ring]
    exact ZMod.val_natCast_of_lt (by omega)
  rw [h_inner_val] at lt_lh0 lt_lh1
  rw [h_inner_hi_val] at lt_ll0 lt_ll1
  have h_total_val : (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16).val = S := by
    rw [h_total_eq]; exact ZMod.val_natCast_of_lt (by omega)
  rw [h_total_val]
  have hdvd : v0123.val ∣ 65536 := by rw [h_v_val]; exact ⟨N, h_MN.symm⟩
  have hpos : 0 < v0123.val := by rw [h_v_val]; exact h_M_pos
  have h_b0' := cancel_mul_65536 hdvd hpos h_b0_dec
  have h_b1' := cancel_mul_65536 hdvd hpos h_b1_dec
  rw [h_v_val] at h_b0' h_b1'
  rw [show (HWord.toBitVec32 #v[b0, b1]).toNat <<< S
          = (HWord.toBitVec32 #v[b0, b1]).toNat * M from by
        rw [Nat.shiftLeft_eq, h_M_eq]]
  have h_div_eq : (65536 : ℕ) / M = N := by
    rw [← h_MN]; exact Nat.mul_div_cancel_left N h_M_pos
  rw [h_div_eq] at h_b0' h_b1'
  have h_lt_ll0 : ll0.val < N := by rw [h_N_eq]; exact lt_ll0
  have h_lt_ll1 : ll1.val < N := by rw [h_N_eq]; exact lt_ll1
  have h_lt_lh0 : hl0.val < M := by rw [h_M_eq]; exact lt_lh0
  have h_lt_lh1 : hl1.val < M := by rw [h_M_eq]; exact lt_lh1
  exact sllw_within_byte_shift M N h_MN h_M_pos h_v_val
    h_lt_ll0 h_lt_ll1 h_lt_lh0 h_lt_lh1 h_b0' h_b1'

set_option maxHeartbeats 4000000 in
/-- SLLW `cb4=1` close-case wrapper (byte_shift=1, total shift `S + 16`). -/
lemma sllw_close_cb4_one_case
    (S : ℕ) (h_S_le : S ≤ 15) (M N : ℕ)
    (h_MN : M * N = 65536) (h_M_pos : 0 < M) (h_M_eq : M = 2 ^ S)
    (h_N_eq : N = 2 ^ (16 - S))
    {cb0 cb1 cb2 cb3 cb4 v0123 b0 b1 ll0 ll1 hl0 hl1 : ZMod p}
    (h_v_val : v0123.val = M)
    (h_inner_eq : cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8
                  = ((S : ℕ) : ZMod p))
    (h_total_eq : cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16
                  = (((S + 16) : ℕ) : ZMod p))
    (lt_ll0 : ll0.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_lh0 : hl0.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (lt_ll1 : ll1.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_lh1 : hl1.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (h_b0_dec : b0 * v0123 = hl0 * ((65536 : ℕ) : ZMod p) + ll0 * v0123)
    (h_b1_dec : b1 * v0123 = hl1 * ((65536 : ℕ) : ZMod p) + ll1 * v0123) :
    (HWord.toBitVec32 #v[0, ll0 * v0123]).toNat
    = (HWord.toBitVec32 #v[b0, b1]).toNat
        <<< (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16).val
      % 2 ^ 32 := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_inner_val : (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                      + cb3 * 8 : ZMod p).val = S := by
    rw [h_inner_eq]; exact ZMod.val_natCast_of_lt (by omega)
  have h_inner_hi_val : (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                + cb3 * 8) : ZMod p).val = 16 - S := by
    rw [show (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
              + cb3 * 8) : ZMod p) = (((16 - S) : ℕ) : ZMod p) from by
      rw [h_inner_eq, Nat.cast_sub (by omega : S ≤ 16)]; push_cast; ring]
    exact ZMod.val_natCast_of_lt (by omega)
  rw [h_inner_val] at lt_lh0 lt_lh1
  rw [h_inner_hi_val] at lt_ll0 lt_ll1
  have h_total_val : (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16).val = S + 16 := by
    rw [h_total_eq]; exact ZMod.val_natCast_of_lt (by omega)
  rw [h_total_val]
  have hdvd : v0123.val ∣ 65536 := by rw [h_v_val]; exact ⟨N, h_MN.symm⟩
  have hpos : 0 < v0123.val := by rw [h_v_val]; exact h_M_pos
  have h_b0' := cancel_mul_65536 hdvd hpos h_b0_dec
  have h_b1' := cancel_mul_65536 hdvd hpos h_b1_dec
  rw [h_v_val] at h_b0' h_b1'
  rw [show (HWord.toBitVec32 #v[b0, b1]).toNat <<< (S + 16)
          = (HWord.toBitVec32 #v[b0, b1]).toNat * M * 2 ^ 16 from by
        rw [Nat.shiftLeft_eq, h_M_eq, pow_add, ← Nat.mul_assoc]]
  have h_div_eq : (65536 : ℕ) / M = N := by
    rw [← h_MN]; exact Nat.mul_div_cancel_left N h_M_pos
  rw [h_div_eq] at h_b0' h_b1'
  have h_lt_ll0 : ll0.val < N := by rw [h_N_eq]; exact lt_ll0
  have h_lt_ll1 : ll1.val < N := by rw [h_N_eq]; exact lt_ll1
  have h_lt_lh0 : hl0.val < M := by rw [h_M_eq]; exact lt_lh0
  have h_lt_lh1 : hl1.val < M := by rw [h_M_eq]; exact lt_lh1
  exact sllw_within_byte_shift_1 M N h_MN h_M_pos h_v_val
    h_lt_ll0 h_lt_ll1 h_lt_lh0 h_lt_lh1 h_b0' h_b1'

set_option maxHeartbeats 800000 in
/-- SLLW per-sub-case closer for `cb4 = 0` (byte_shift=0): the 64-bit output word
`#v[ll0·v, ll1·v+hl0, msb·65535, msb·65535]` equals the sign extension of the 32-bit shifted input. The
sign fill is discharged natively via `Word.toBitVec64_signExtend_word`. -/
lemma sllw_subcase_cb4_zero
    (S : ℕ) (h_S_le : S ≤ 15) (M N : ℕ)
    (h_MN : M * N = 65536) (h_M_pos : 0 < M) (h_M_eq : M = 2 ^ S)
    (h_N_eq : N = 2 ^ (16 - S))
    {cb0 cb1 cb2 cb3 cb4 v0123 b0 b1 c0 c1 a2 a3 ll0 ll1 hl0 hl1 msb : ZMod p}
    (h_v_val : v0123.val = M)
    (h_inner_eq : cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8
                  = ((S : ℕ) : ZMod p))
    (h_total_eq : cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16
                  = ((S : ℕ) : ZMod p))
    (lt_ll0 : ll0.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_lh0 : hl0.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (lt_ll1 : ll1.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_lh1 : hl1.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (h_b0_dec : b0 * v0123 = hl0 * ((65536 : ℕ) : ZMod p) + ll0 * v0123)
    (h_b1_dec : b1 * v0123 = hl1 * ((65536 : ℕ) : ZMod p) + ll1 * v0123)
    (_h_b0_lt : b0.val < 65536) (_h_b1_lt : b1.val < 65536)
    (h_c0_lt : c0.val < 65536) (h_c1_lt : c1.val < 65536)
    (h_msb_a1 : msb = if (ll1 * v0123 + hl0).val ≥ 32768 then 1 else 0)
    (h_a2_eq : a2 = msb * 65535) (h_a3_eq : a3 = msb * 65535)
    (h_c_mod_32 : c0.val % 32 = (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16).val) :
    Word.toBitVec64 #v[ll0 * v0123, ll1 * v0123 + hl0, a2, a3]
      = BitVec.signExtend 64 (HWord.toBitVec32 #v[b0, b1] <<<
                              BitVec.setWidth 5 (HWord.toBitVec32 #v[c0, c1])) := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_inner_val : (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                      + cb3 * 8 : ZMod p).val = S := by
    rw [h_inner_eq]; exact ZMod.val_natCast_of_lt (by omega)
  have h_inner_hi_val : (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                + cb3 * 8) : ZMod p).val = 16 - S := by
    rw [show (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
              + cb3 * 8) : ZMod p) = (((16 - S) : ℕ) : ZMod p) from by
      rw [h_inner_eq, Nat.cast_sub (by omega : S ≤ 16)]; push_cast; ring]
    exact ZMod.val_natCast_of_lt (by omega)
  have h_lt_ll0_N : ll0.val < N := by rw [h_N_eq]; rw [h_inner_hi_val] at lt_ll0; exact lt_ll0
  have h_lt_ll1_N : ll1.val < N := by rw [h_N_eq]; rw [h_inner_hi_val] at lt_ll1; exact lt_ll1
  have h_lt_lh0_M : hl0.val < M := by rw [h_M_eq]; rw [h_inner_val] at lt_lh0; exact lt_lh0
  -- bounds on the placed limbs
  have h_ll0v_val : (ll0 * v0123).val = ll0.val * M := by
    rw [ZMod.val_mul_of_lt, h_v_val]; rw [h_v_val]; nlinarith [h_lt_ll0_N, h_MN]
  have h_ll0v_lt : (ll0 * v0123).val < 65536 := by rw [h_ll0v_val]; nlinarith [h_lt_ll0_N, h_MN]
  have h_ll1v_val : (ll1 * v0123).val = ll1.val * M := by
    rw [ZMod.val_mul_of_lt, h_v_val]; rw [h_v_val]; nlinarith [h_lt_ll1_N, h_MN]
  have h_compose_val : (ll1 * v0123 + hl0).val = ll1.val * M + hl0.val := by
    rw [ZMod.val_add_of_lt, h_ll1v_val]; rw [h_ll1v_val]; nlinarith [h_lt_ll1_N, h_lt_lh0_M, h_MN]
  have h_compose_lt : (ll1 * v0123 + hl0).val < 65536 := by
    rw [h_compose_val]; nlinarith [h_lt_ll1_N, h_lt_lh0_M, h_MN]
  have is_U32_a : HWord.isU32 #v[ll0 * v0123, ll1 * v0123 + hl0] :=
    HWord.isU32_of_cases (by simpa using h_ll0v_lt) (by simpa using h_compose_lt)
  have is_U32_c' : HWord.isU32 #v[c0, c1] :=
    HWord.isU32_of_cases (by simpa using h_c0_lt) (by simpa using h_c1_lt)
  -- 32-bit shift identity at the toNat level
  have h_shift_nat : (HWord.toBitVec32 #v[ll0 * v0123, ll1 * v0123 + hl0]).toNat
                   = (HWord.toBitVec32 #v[b0, b1]).toNat
                       <<< (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16).val
                     % 2 ^ 32 :=
    sllw_close_cb4_zero_case S h_S_le M N h_MN h_M_pos h_M_eq h_N_eq
      h_v_val h_inner_eq h_total_eq lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
  -- lift to a BitVec shift equality
  have h_shift : HWord.toBitVec32 #v[ll0 * v0123, ll1 * v0123 + hl0]
              = HWord.toBitVec32 #v[b0, b1] <<<
                  BitVec.setWidth 5 (HWord.toBitVec32 #v[c0, c1]) := by
    rw [← BitVec.toNat_inj]
    simp only [BitVec.toNat_shiftLeft, BitVec.shiftLeft_eq', BitVec.toNat_setWidth]
    rw [HWord.toBitVec32_toNat is_U32_c']
    have h_c_toNat : HWord.toNat #v[c0, c1] % 2 ^ 5 = c0.val % 32 := by simp [HWord.toNat]; omega
    rw [h_c_toNat, h_c_mod_32]
    exact h_shift_nat
  rw [← h_shift]
  -- the 32-bit value's toNat in limb form
  have hX : (HWord.toBitVec32 #v[ll0 * v0123, ll1 * v0123 + hl0]).toNat
          = (ll0 * v0123).val + (ll1 * v0123 + hl0).val * 2 ^ 16 := by
    rw [HWord.toBitVec32_toNat is_U32_a]; rfl
  exact SP1Clean.toBitVec64_signExtend_word
    #v[ll0 * v0123, ll1 * v0123 + hl0, a2, a3]
    (HWord.toBitVec32 #v[ll0 * v0123, ll1 * v0123 + hl0]) msb
    (by simpa using h_ll0v_lt) (by simpa using h_compose_lt) (by simpa using h_msb_a1)
    (by simpa using h_a2_eq) (by simpa using h_a3_eq) hX

set_option maxHeartbeats 800000 in
/-- SLLW per-sub-case closer for `cb4 = 1` (byte_shift=1): `#v[0, ll0·v, msb·65535, msb·65535]`. -/
lemma sllw_subcase_cb4_one
    (S : ℕ) (h_S_le : S ≤ 15) (M N : ℕ)
    (h_MN : M * N = 65536) (h_M_pos : 0 < M) (h_M_eq : M = 2 ^ S)
    (h_N_eq : N = 2 ^ (16 - S))
    {cb0 cb1 cb2 cb3 cb4 v0123 b0 b1 c0 c1 a2 a3 ll0 ll1 hl0 hl1 msb : ZMod p}
    (h_v_val : v0123.val = M)
    (h_inner_eq : cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8
                  = ((S : ℕ) : ZMod p))
    (h_total_eq : cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16
                  = (((S + 16) : ℕ) : ZMod p))
    (lt_ll0 : ll0.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_lh0 : hl0.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (lt_ll1 : ll1.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_lh1 : hl1.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (h_b0_dec : b0 * v0123 = hl0 * ((65536 : ℕ) : ZMod p) + ll0 * v0123)
    (h_b1_dec : b1 * v0123 = hl1 * ((65536 : ℕ) : ZMod p) + ll1 * v0123)
    (_h_b0_lt : b0.val < 65536) (_h_b1_lt : b1.val < 65536)
    (h_c0_lt : c0.val < 65536) (h_c1_lt : c1.val < 65536)
    (h_msb_a1 : msb = if (ll0 * v0123).val ≥ 32768 then 1 else 0)
    (h_a2_eq : a2 = msb * 65535) (h_a3_eq : a3 = msb * 65535)
    (h_c_mod_32 : c0.val % 32 = (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16).val) :
    Word.toBitVec64 #v[0, ll0 * v0123, a2, a3]
      = BitVec.signExtend 64 (HWord.toBitVec32 #v[b0, b1] <<<
                              BitVec.setWidth 5 (HWord.toBitVec32 #v[c0, c1])) := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_inner_val : (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                      + cb3 * 8 : ZMod p).val = S := by
    rw [h_inner_eq]; exact ZMod.val_natCast_of_lt (by omega)
  have h_inner_hi_val : (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                + cb3 * 8) : ZMod p).val = 16 - S := by
    rw [show (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
              + cb3 * 8) : ZMod p) = (((16 - S) : ℕ) : ZMod p) from by
      rw [h_inner_eq, Nat.cast_sub (by omega : S ≤ 16)]; push_cast; ring]
    exact ZMod.val_natCast_of_lt (by omega)
  have h_lt_ll0_N : ll0.val < N := by rw [h_N_eq]; rw [h_inner_hi_val] at lt_ll0; exact lt_ll0
  have h_ll0v_val : (ll0 * v0123).val = ll0.val * M := by
    rw [ZMod.val_mul_of_lt, h_v_val]; rw [h_v_val]; nlinarith [h_lt_ll0_N, h_MN]
  have h_ll0v_lt : (ll0 * v0123).val < 65536 := by rw [h_ll0v_val]; nlinarith [h_lt_ll0_N, h_MN]
  have is_U32_a : HWord.isU32 #v[(0 : ZMod p), ll0 * v0123] :=
    HWord.isU32_of_cases (by simp [ZMod.val_zero]) (by simpa using h_ll0v_lt)
  have is_U32_c' : HWord.isU32 #v[c0, c1] :=
    HWord.isU32_of_cases (by simpa using h_c0_lt) (by simpa using h_c1_lt)
  have h_shift_nat : (HWord.toBitVec32 #v[(0 : ZMod p), ll0 * v0123]).toNat
                   = (HWord.toBitVec32 #v[b0, b1]).toNat
                       <<< (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16).val
                     % 2 ^ 32 :=
    sllw_close_cb4_one_case S h_S_le M N h_MN h_M_pos h_M_eq h_N_eq
      h_v_val h_inner_eq h_total_eq lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
  have h_shift : HWord.toBitVec32 #v[(0 : ZMod p), ll0 * v0123]
              = HWord.toBitVec32 #v[b0, b1] <<<
                  BitVec.setWidth 5 (HWord.toBitVec32 #v[c0, c1]) := by
    rw [← BitVec.toNat_inj]
    simp only [BitVec.toNat_shiftLeft, BitVec.shiftLeft_eq', BitVec.toNat_setWidth]
    rw [HWord.toBitVec32_toNat is_U32_c']
    have h_c_toNat : HWord.toNat #v[c0, c1] % 2 ^ 5 = c0.val % 32 := by simp [HWord.toNat]; omega
    rw [h_c_toNat, h_c_mod_32]
    exact h_shift_nat
  rw [← h_shift]
  have hX : (HWord.toBitVec32 #v[(0 : ZMod p), ll0 * v0123]).toNat
          = (0 : ZMod p).val + (ll0 * v0123).val * 2 ^ 16 := by
    rw [HWord.toBitVec32_toNat is_U32_a]; rfl
  exact SP1Clean.toBitVec64_signExtend_word
    #v[(0 : ZMod p), ll0 * v0123, a2, a3]
    (HWord.toBitVec32 #v[(0 : ZMod p), ll0 * v0123]) msb
    (by simp [ZMod.val_zero]) (by simpa using h_ll0v_lt) (by simpa using h_msb_a1)
    (by simpa using h_a2_eq) (by simpa using h_a3_eq) hX

set_option linter.unusedSectionVars false in
/-- The `c0 % 32` projection: from `c0 % 64 = (5-bit sum) + cb5·32` (with the 5-bit sum `< 32`), get
`c0 % 32 = (5-bit sum)`. -/
lemma c0_mod32_of_mod64 [NeZero p] {c0 cbsum5 cb5 : ZMod p}
    (h_mod64 : c0.val % 64 = (cbsum5 + cb5 * 32).val)
    (h5 : cb5 = 0 ∨ cb5 = 1) (h_cbsum5_lt : cbsum5.val < 32)
    (h_v32 : (32 : ZMod p).val = 32) (h_p : 64 < p) :
    c0.val % 32 = cbsum5.val := by
  have h_cb5v : cb5.val ≤ 1 := by rcases h5 with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]
  have h_mul : (cb5 * 32).val = cb5.val * 32 := by
    have hlt : cb5.val * (32 : ZMod p).val < p := by rw [h_v32]; omega
    rw [ZMod.val_mul_of_lt hlt, h_v32]
  have h_add : (cbsum5 + cb5 * 32).val = cbsum5.val + cb5.val * 32 := by
    have hlt : cbsum5.val + (cb5 * 32).val < p := by rw [h_mul]; omega
    rw [ZMod.val_add_of_lt hlt, h_mul]
  rw [h_add] at h_mod64
  omega

/-- The SLLW result limb 1 (`a1`) is a 16-bit value: on the real `is_sllw` row it equals either
`lr1 = ll1·v + hl0` (byte_shift=0) or `lr0 = ll0·v` (byte_shift=1), both `< 2^16` from the
`lower/higher_limb` ranges. Feeds the U16MSB sub-assertion's operand bound (the SLLW branch and the
channel-requirement tail). -/
lemma sllw_a1_bound
    {a1 cb4 s0 s1 s2 s3 ll0 ll1 hl0 lr0 lr1 v0123 : ZMod p}
    (M N : ℕ) (hMN : M * N = 65536) (h_v0123_val : v0123.val = M)
    (hb_cb4 : cb4 = 0 ∨ cb4 = 1)
    (h_s0sel : s0 * (cb4 - 0) = 0) (h_s1sel : s1 * (cb4 - 1) = 0)
    (h_s2sel : s2 * (cb4 - 2) = 0) (h_s3sel : s3 * (cb4 - 3) = 0)
    (h_ssum : s0 + s1 + s2 + s3 = 1)
    (h_lr0 : lr0 = ll0 * v0123) (h_lr1 : lr1 = ll1 * v0123 + hl0)
    (h_ll0 : ll0.val < N) (h_hl0 : hl0.val < M) (h_ll1 : ll1.val < N)
    (h_p01 : s0 * (a1 - lr1) = 0) (h_p11 : s1 * (a1 - lr0) = 0) :
    a1.val < 65536 := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have hv2 : (2 : ZMod p).val = 2 := val_2_zmod_p
  have hv3 : (3 : ZMod p).val = 3 := by
    rw [show (3 : ZMod p) = ((3 : ℕ) : ZMod p) from by push_cast; rfl]
    exact ZMod.val_natCast_of_lt (by omega)
  have n1 : (1 : ZMod p) ≠ 0 := one_ne_zero
  have n2 : (2 : ZMod p) ≠ 0 := fun h => by rw [h, ZMod.val_zero] at hv2; omega
  have n3 : (3 : ZMod p) ≠ 0 := fun h => by rw [h, ZMod.val_zero] at hv3; omega
  rcases hb_cb4 with h4 | h4
  · rw [h4] at h_s1sel h_s2sel h_s3sel
    have hs1 : s1 = 0 := eq_zero_of_mul_const (h := h_s1sel)
      (hk := by rw [show ((0:ZMod p) - 1) = -1 from by ring]; exact neg_ne_zero.mpr n1)
    have hs2 : s2 = 0 := eq_zero_of_mul_const (h := h_s2sel)
      (hk := by rw [show ((0:ZMod p) - 2) = -2 from by ring]; exact neg_ne_zero.mpr n2)
    have hs3 : s3 = 0 := eq_zero_of_mul_const (h := h_s3sel)
      (hk := by rw [show ((0:ZMod p) - 3) = -3 from by ring]; exact neg_ne_zero.mpr n3)
    have hs0 : s0 = 1 := by rw [hs1, hs2, hs3] at h_ssum; linear_combination h_ssum
    have ha1 : a1 = ll1 * v0123 + hl0 := by rw [hs0, one_mul] at h_p01; rw [h_lr1] at h_p01; linear_combination h_p01
    have h_ll1v : (ll1 * v0123).val = ll1.val * M := by
      rw [ZMod.val_mul_of_lt, h_v0123_val]; rw [h_v0123_val]; nlinarith [h_ll1, hMN]
    have : (ll1 * v0123 + hl0).val = ll1.val * M + hl0.val := by
      rw [ZMod.val_add_of_lt, h_ll1v]; rw [h_ll1v]; nlinarith [h_ll1, h_hl0, hMN]
    rw [ha1, this]; nlinarith [h_ll1, h_hl0, hMN]
  · rw [h4] at h_s0sel h_s2sel h_s3sel
    have hs0 : s0 = 0 := eq_zero_of_mul_const (h := h_s0sel)
      (hk := by rw [show ((1:ZMod p) - 0) = 1 from by ring]; exact n1)
    have hs2 : s2 = 0 := eq_zero_of_mul_const (h := h_s2sel)
      (hk := by rw [show ((1:ZMod p) - 2) = -1 from by ring]; exact neg_ne_zero.mpr n1)
    have hs3 : s3 = 0 := eq_zero_of_mul_const (h := h_s3sel)
      (hk := by rw [show ((1:ZMod p) - 3) = -2 from by ring]; exact neg_ne_zero.mpr n2)
    have hs1 : s1 = 1 := by rw [hs0, hs2, hs3] at h_ssum; linear_combination h_ssum
    have ha1 : a1 = ll0 * v0123 := by rw [hs1, one_mul] at h_p11; rw [h_lr0] at h_p11; linear_combination h_p11
    have h_ll0v : (ll0 * v0123).val = ll0.val * M := by
      rw [ZMod.val_mul_of_lt, h_v0123_val]; rw [h_v0123_val]; nlinarith [h_ll0, hMN]
    rw [ha1, h_ll0v]; nlinarith [h_ll0, hMN]

set_option maxHeartbeats 4000000 in
/-- **SLLW placement assembly.** The SLLW analog of `sll_assembly`: given the witnessed shift columns
(`is_sll = 0`, so byte-shift `= cb4 ∈ {0,1}`, a 5-bit shift amount, the `lower/higher_limb` bit-splits on
the low two limbs, and the `sllw_msb`-driven sign fill on the high two limbs), the output word is the
sign extension of the 32-bit shift of `op_b`'s low half by `c0 mod 32`. Two byte-shift positions dispatched
to `sllw_subcase_cb4_{zero,one}`. Pure field/`Word`/`HWord` statement, fed the evaluated columns. -/
lemma sllw_assembly
    {a0 a1 a2 a3 b0 b1 c0 c1 cb0 cb1 cb2 cb3 cb4 cb5 v0123
     s0 s1 s2 s3 ll0 ll1 hl0 hl1 lr0 lr1 msb : ZMod p}
    (S : ℕ) (hS_le : S ≤ 15) (M N : ℕ) (hMN : M * N = 65536) (hM_pos : 0 < M)
    (hM_eq : M = 2 ^ S) (hN_eq : N = 2 ^ (16 - S))
    (h_v0123_val : v0123.val = M)
    (h_inner : cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8 = ((S : ℕ) : ZMod p))
    (hb_cb4 : cb4 = 0 ∨ cb4 = 1) (hb_cb5 : cb5 = 0 ∨ cb5 = 1)
    (h_c0_lt : c0.val < 65536) (h_c1_lt : c1.val < 65536)
    (h_b0_lt : b0.val < 65536) (h_b1_lt : b1.val < 65536)
    (h_cb_sum_lt : (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val < 64)
    (h_diff : ((c0 - (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32)) * (64 : ZMod p)⁻¹).val < 1024)
    (h_s0sel : s0 * (cb4 - 0) = 0) (h_s1sel : s1 * (cb4 - 1) = 0)
    (h_s2sel : s2 * (cb4 - 2) = 0) (h_s3sel : s3 * (cb4 - 3) = 0)
    (h_ssum : s0 + s1 + s2 + s3 = 1)
    (h_b0dec : b0 * v0123 = hl0 * ((65536 : ℕ) : ZMod p) + ll0 * v0123)
    (h_b1dec : b1 * v0123 = hl1 * ((65536 : ℕ) : ZMod p) + ll1 * v0123)
    (h_lr0 : lr0 = ll0 * v0123) (h_lr1 : lr1 = ll1 * v0123 + hl0)
    (h_ll0 : ll0.val < N) (h_hl0 : hl0.val < M) (h_ll1 : ll1.val < N) (h_hl1 : hl1.val < M)
    (h_p00 : s0 * (a0 - lr0) = 0) (h_p01 : s0 * (a1 - lr1) = 0)
    (h_p10 : s1 * a0 = 0) (h_p11 : s1 * (a1 - lr0) = 0)
    (h_msb_a1 : msb = if a1.val ≥ 32768 then 1 else 0)
    (h_a2 : a2 = msb * 65535) (h_a3 : a3 = msb * 65535) :
    Word.toBitVec64 #v[a0, a1, a2, a3]
      = BitVec.signExtend 64 (HWord.toBitVec32 #v[b0, b1] <<<
                              BitVec.setWidth 5 (HWord.toBitVec32 #v[c0, c1])) := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have hv2 : (2 : ZMod p).val = 2 := val_2_zmod_p
  have hv3 : (3 : ZMod p).val = 3 := by
    rw [show (3 : ZMod p) = ((3 : ℕ) : ZMod p) from by push_cast; rfl]
    exact ZMod.val_natCast_of_lt (by omega)
  have hv32 : (32 : ZMod p).val = 32 := by
    rw [show (32 : ZMod p) = ((32 : ℕ) : ZMod p) from by push_cast; rfl]
    exact ZMod.val_natCast_of_lt (by omega)
  have n1 : (1 : ZMod p) ≠ 0 := one_ne_zero
  have n2 : (2 : ZMod p) ≠ 0 := fun h => by rw [h, ZMod.val_zero] at hv2; omega
  have n3 : (3 : ZMod p) ≠ 0 := fun h => by rw [h, ZMod.val_zero] at hv3; omega
  -- The shift amount: c0 mod 64 equals the 6-bit cb-sum.
  have h_mod64 : c0.val % 64 = (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val :=
    is_mod_64 h_cb_sum_lt h_c0_lt h_diff
  -- Exponent `.val`s in close-lemma form (shared across the byte-shift cases).
  have hMexp : (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8 : ZMod p).val = S := by
    rw [h_inner]; exact ZMod.val_natCast_of_lt (by omega)
  have hNexp : ((16 : ZMod p) - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8)).val
      = 16 - S := by
    rw [h_inner, show (16 : ZMod p) - ((S : ℕ) : ZMod p) = (((16 - S : ℕ)) : ZMod p) from by
      rw [Nat.cast_sub (show S ≤ 16 by omega)]; push_cast; ring]
    exact ZMod.val_natCast_of_lt (by omega)
  have hll0' : ll0.val < 2 ^ (16 - (cb0 + cb1 * ((2:ℕ):ZMod p) + cb2 * ((4:ℕ):ZMod p) + cb3 * 8) : ZMod p).val := by
    rw [hNexp, ← hN_eq]; exact h_ll0
  have hll1' : ll1.val < 2 ^ (16 - (cb0 + cb1 * ((2:ℕ):ZMod p) + cb2 * ((4:ℕ):ZMod p) + cb3 * 8) : ZMod p).val := by
    rw [hNexp, ← hN_eq]; exact h_ll1
  have hhl0' : hl0.val < 2 ^ (cb0 + cb1 * ((2:ℕ):ZMod p) + cb2 * ((4:ℕ):ZMod p) + cb3 * 8 : ZMod p).val := by
    rw [hMexp, ← hM_eq]; exact h_hl0
  have hhl1' : hl1.val < 2 ^ (cb0 + cb1 * ((2:ℕ):ZMod p) + cb2 * ((4:ℕ):ZMod p) + cb3 * 8 : ZMod p).val := by
    rw [hMexp, ← hM_eq]; exact h_hl1
  -- the plain-coefficient inner sum (for cbsum5 `.val`)
  have h_inner_plain : cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 = ((S : ℕ) : ZMod p) := by
    push_cast at h_inner ⊢; linear_combination h_inner
  -- Dispatch on the byte-shift position `cb4` (placement) and `cb5` (the `c0 % 32` projection).
  rcases hb_cb4 with h4 | h4
  · -- cb4 = 0 (byte_shift = 0) → s0 = 1.
    rw [h4] at h_s1sel h_s2sel h_s3sel
    have hs1 : s1 = 0 := eq_zero_of_mul_const (h := h_s1sel)
      (hk := by rw [show ((0:ZMod p) - 1) = -1 from by ring]; exact neg_ne_zero.mpr n1)
    have hs2 : s2 = 0 := eq_zero_of_mul_const (h := h_s2sel)
      (hk := by rw [show ((0:ZMod p) - 2) = -2 from by ring]; exact neg_ne_zero.mpr n2)
    have hs3 : s3 = 0 := eq_zero_of_mul_const (h := h_s3sel)
      (hk := by rw [show ((0:ZMod p) - 3) = -3 from by ring]; exact neg_ne_zero.mpr n3)
    have hs0 : s0 = 1 := by rw [hs1, hs2, hs3] at h_ssum; linear_combination h_ssum
    have ha0 : a0 = lr0 := by rw [hs0, one_mul] at h_p00; linear_combination h_p00
    have ha1 : a1 = lr1 := by rw [hs0, one_mul] at h_p01; linear_combination h_p01
    have h_total : cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 = ((S : ℕ) : ZMod p) := by
      rw [h4]; push_cast at h_inner_plain ⊢; linear_combination h_inner_plain
    have h_cbsum5_lt : (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16).val < 32 := by
      rw [h_total]; rw [ZMod.val_natCast_of_lt (by omega)]; omega
    have h_c_mod_32 : c0.val % 32 = (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16).val :=
      c0_mod32_of_mod64 h_mod64 hb_cb5 h_cbsum5_lt hv32 (by omega)
    rw [ha0, ha1, h_lr0, h_lr1]
    -- a1 = lr1 = ll1*v + hl0, so the msb hypothesis is about (ll1*v + hl0).
    have h_msb' : msb = if (ll1 * v0123 + hl0).val ≥ 32768 then 1 else 0 := by
      rw [h_msb_a1, ha1, h_lr1]
    exact sllw_subcase_cb4_zero S hS_le M N hMN hM_pos hM_eq hN_eq h_v0123_val h_inner h_total
      hll0' hhl0' hll1' hhl1' h_b0dec h_b1dec h_b0_lt h_b1_lt h_c0_lt h_c1_lt
      h_msb' h_a2 h_a3 h_c_mod_32
  · -- cb4 = 1 (byte_shift = 1) → s1 = 1.
    rw [h4] at h_s0sel h_s2sel h_s3sel
    have hs0 : s0 = 0 := eq_zero_of_mul_const (h := h_s0sel)
      (hk := by rw [show ((1:ZMod p) - 0) = 1 from by ring]; exact n1)
    have hs2 : s2 = 0 := eq_zero_of_mul_const (h := h_s2sel)
      (hk := by rw [show ((1:ZMod p) - 2) = -1 from by ring]; exact neg_ne_zero.mpr n1)
    have hs3 : s3 = 0 := eq_zero_of_mul_const (h := h_s3sel)
      (hk := by rw [show ((1:ZMod p) - 3) = -2 from by ring]; exact neg_ne_zero.mpr n2)
    have hs1 : s1 = 1 := by rw [hs0, hs2, hs3] at h_ssum; linear_combination h_ssum
    have ha0 : a0 = 0 := by rw [hs1, one_mul] at h_p10; exact h_p10
    have ha1 : a1 = lr0 := by rw [hs1, one_mul] at h_p11; linear_combination h_p11
    have h_total : cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 = (((S + 16) : ℕ) : ZMod p) := by
      rw [h4]; push_cast at h_inner_plain ⊢; linear_combination h_inner_plain
    have h_cbsum5_lt : (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16).val < 32 := by
      rw [h_total]; rw [ZMod.val_natCast_of_lt (by omega)]; omega
    have h_c_mod_32 : c0.val % 32 = (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16).val :=
      c0_mod32_of_mod64 h_mod64 hb_cb5 h_cbsum5_lt hv32 (by omega)
    rw [ha0, ha1, h_lr0]
    have h_msb' : msb = if (ll0 * v0123).val ≥ 32768 then 1 else 0 := by
      rw [h_msb_a1, ha1, h_lr0]
    exact sllw_subcase_cb4_one S hS_le M N hMN hM_pos hM_eq hN_eq h_v0123_val h_inner h_total
      hll0' hhl0' hll1' hhl1' h_b0dec h_b1dec h_b0_lt h_b1_lt h_c0_lt h_c1_lt
      h_msb' h_a2 h_a3 h_c_mod_32

/-! ## `RV64.sllw` ↔ `HWord` bridge helpers (the low-32-bit / 5-bit-shamt extractions) -/

set_option linter.unusedSectionVars false in
/-- The low 32 bits of a `Word`'s `toBitVec64` are its first two limbs as an `HWord`. -/
lemma extractLsb32_toBitVec64 {w : Word (ZMod p)} (hw : Word.isU64 w) :
    BitVec.extractLsb' 0 32 (Word.toBitVec64 w) = HWord.toBitVec32 #v[w[0], w[1]] := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h0, h1, h2, h3⟩ := Word.lt_cases_of_isU64 hw
  rw [← BitVec.toNat_inj]
  unfold BitVec.extractLsb'
  rw [BitVec.toNat_ofNat, Nat.shiftRight_zero, Word.toBitVec64_toNat hw, Word.toNat_def,
      HWord.toBitVec32_toNat (HWord.isU32_of_cases h0 h1), HWord.toNat]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  rw [show (2:ℕ)^16 = 65536 from by norm_num, show (2:ℕ)^32 = 4294967296 from by norm_num,
      show (2:ℕ)^48 = 281474976710656 from by norm_num]
  omega

set_option linter.unusedSectionVars false in
/-- The 5-bit shift amount extracted from a `Word`'s low 32 bits is the low 5 bits of its first limb. -/
lemma extractLsb5_toBitVec64 {c : Word (ZMod p)} (hc : Word.isU64 c) :
    BitVec.extractLsb' 0 5 (BitVec.extractLsb' 0 32 (Word.toBitVec64 c))
      = BitVec.setWidth 5 (HWord.toBitVec32 #v[c[0], c[1]]) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h0, h1, h2, h3⟩ := Word.lt_cases_of_isU64 hc
  rw [BitVec.extractLsb'_extractLsb'_of_le (by omega), ← BitVec.toNat_inj]
  unfold BitVec.extractLsb'
  rw [BitVec.toNat_ofNat, Nat.shiftRight_zero, BitVec.toNat_setWidth, Word.toBitVec64_toNat hc,
      Word.toNat_def, HWord.toBitVec32_toNat (HWord.isU32_of_cases h0 h1), HWord.toNat]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  rw [show (2:ℕ)^16 = 65536 from by norm_num, show (2:ℕ)^32 = 4294967296 from by norm_num,
      show (2:ℕ)^48 = 281474976710656 from by norm_num, show (2:ℕ)^5 = 32 from by norm_num]
  omega

/-! ## Completeness: the `populate` witness generators (SP1 `event_to_row`)

Field-generic witness generators computing every shift column from the operand words `b`/`c` (the register
read-backs), mirroring `../sp1/crates/core/machine/src/alu/sll/mod.rs`. The output word `a` is built as the
*placement of the recomputed `limb_result`* (so the placement asserts hold by construction, no forward shift
math), and the sign bit `msb` is the high bit of the placed limb 1. Used by `Chips/ShiftLeftChip.lean`'s
`main`/`completeness`. -/

/-- High bit of a 16-bit limb (`a.val / 2^15`), as a field element — SP1's `populate_msb`. -/
def popMsbBit (a : ZMod p) : ZMod p := ((a.val / 32768 : ℕ) : ZMod p)

/-- The six shift-amount bits of `c`'s bottom limb. -/
def popCbits (c : Word (ZMod p)) : Vector (ZMod p) 6 :=
  let s := (c[0]).val
  #v[(((s >>> 0) &&& 1 : ℕ) : ZMod p), (((s >>> 1) &&& 1 : ℕ) : ZMod p),
     (((s >>> 2) &&& 1 : ℕ) : ZMod p), (((s >>> 3) &&& 1 : ℕ) : ZMod p),
     (((s >>> 4) &&& 1 : ℕ) : ZMod p), (((s >>> 5) &&& 1 : ℕ) : ZMod p)]

/-- The three power encodings `2^(c%4)`, `2^(c%8)`, `2^(c%16)`. -/
def popV (c : Word (ZMod p)) : Vector (ZMod p) 3 :=
  let s := (c[0]).val
  #v[((2 ^ (s % 4) : ℕ) : ZMod p), ((2 ^ (s % 8) : ℕ) : ZMod p), ((2 ^ (s % 16) : ℕ) : ZMod p)]

/-- The per-limb low part `b[i] mod 2^(16 - bitShift)`. -/
def popLower (b c : Word (ZMod p)) : Word (ZMod p) :=
  let bs := (c[0]).val % 16
  #v[(((b[0]).val % 2 ^ (16 - bs) : ℕ) : ZMod p), (((b[1]).val % 2 ^ (16 - bs) : ℕ) : ZMod p),
     (((b[2]).val % 2 ^ (16 - bs) : ℕ) : ZMod p), (((b[3]).val % 2 ^ (16 - bs) : ℕ) : ZMod p)]

/-- The per-limb high part `b[i] / 2^(16 - bitShift)`. -/
def popHigher (b c : Word (ZMod p)) : Word (ZMod p) :=
  let bs := (c[0]).val % 16
  #v[(((b[0]).val / 2 ^ (16 - bs) : ℕ) : ZMod p), (((b[1]).val / 2 ^ (16 - bs) : ℕ) : ZMod p),
     (((b[2]).val / 2 ^ (16 - bs) : ℕ) : ZMod p), (((b[3]).val / 2 ^ (16 - bs) : ℕ) : ZMod p)]

/-- The reassembled `limb_result[i] = lower[i]·v0123 (+ higher[i-1])`. -/
def popLimbResult (b c : Word (ZMod p)) : Word (ZMod p) :=
  let lo := popLower b c; let hi := popHigher b c; let v := (popV c)[2]
  #v[lo[0] * v, lo[1] * v + hi[0], lo[2] * v + hi[1], lo[3] * v + hi[2]]

/-- The byte-shift amount `(c>>4)&1 + 2·((c>>5)&1)·is_sll` as a `ℕ` (`sllN ∈ {0,1}`). -/
def popByteShift (c : Word (ZMod p)) (sllN : ℕ) : ℕ :=
  (((c[0]).val >>> 4) &&& 1) + 2 * (((c[0]).val >>> 5) &&& 1) * sllN

/-- The one-hot byte-shift selector. -/
def popShiftU16 (c : Word (ZMod p)) (sll : ZMod p) : Vector (ZMod p) 4 :=
  let bs := popByteShift c (if sll = 1 then 1 else 0)
  #v[(if bs = 0 then 1 else 0 : ZMod p), (if bs = 1 then 1 else 0 : ZMod p),
     (if bs = 2 then 1 else 0 : ZMod p), (if bs = 3 then 1 else 0 : ZMod p)]

/-- The SLLW result limb 1 (the placed limb, before sign fill). -/
def popSllwA1 (b c : Word (ZMod p)) : ZMod p :=
  let lr := popLimbResult b c
  if ((c[0]).val >>> 4) &&& 1 = 0 then lr[1] else lr[0]

/-- The sign bit `msb` (SLLW only). -/
def popMsb (b c : Word (ZMod p)) (sllw : ZMod p) : ZMod p :=
  if sllw = 1 then popMsbBit (popSllwA1 b c) else 0

/-- The output word `a`: the placement of `limb_result` at the byte-shift offset (SLL), the low-2 placement
plus `msb·65535` sign fill (SLLW), or zero (padding). -/
def popA (b c : Word (ZMod p)) (sll sllw : ZMod p) : Word (ZMod p) :=
  let lr := popLimbResult b c
  if sll = 1 then
    match (((c[0]).val >>> 4) &&& 1) + 2 * (((c[0]).val >>> 5) &&& 1) with
    | 0 => #v[lr[0], lr[1], lr[2], lr[3]]
    | 1 => #v[0, lr[0], lr[1], lr[2]]
    | 2 => #v[0, 0, lr[0], lr[1]]
    | _ => #v[0, 0, 0, lr[0]]
  else if sllw = 1 then
    let m := popMsbBit (popSllwA1 b c)
    if ((c[0]).val >>> 4) &&& 1 = 0 then #v[lr[0], lr[1], m * 65535, m * 65535]
    else #v[0, lr[0], m * 65535, m * 65535]
  else #v[0, 0, 0, 0]

end SP1Clean.ShiftLeftCore
