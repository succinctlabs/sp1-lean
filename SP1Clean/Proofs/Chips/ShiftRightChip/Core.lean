import SP1Clean.Math.Word
import SP1Clean.Native.Operations.ShiftBounds
import Mathlib.Tactic

/-! # ShiftRight native arithmetic — the SRL math layer

Pure-arithmetic lemmas for SP1's `ShiftRight` proof, stated against bare `ZMod p`
+ `SP1Clean.Word.toBitVec64` (layout-agnostic). Local `val_N` field-constant helpers are defined below.

Carries the **SRL** chain: `is_mod_64`, `cancel_mul_65536(_zero)`, `cb_sum_val_eq`,
`bool_mul_65535_lt`, the four `srl_within_byte_shift*` division identities, and the four
`srl_close_su16_*_case` wrappers (`(toBitVec64 limb_result).toNat = (toBitVec64 b).toNat / 2^shamt`).
The SRA/SRLW/SRAW chains (needing the `HWord` 32-bit half-word and the sign-fill identities) follow. -/

namespace SP1Clean.ShiftRightMath
open SP1Clean
open SP1Clean.ShiftBounds

-- Heavy `nlinarith`/`omega`/`linear_combination` Nat-arithmetic proofs.
-- Repeated per-limb `.val`/bound `nlinarith` goals live in `ShiftBounds`;
-- the SRA/SRLW dispatch chains are the heaviest users left.
-- Ceiling measured (not guessed) by lowering the real limit, per Clean's
-- `doc/performance-problems.md` §"Measuring honestly": the file's floor sits between the 200000
-- default (fails at `sra_close_su16_3_case`, `whnf`/`isDefEq`) and 400000; 2000000 keeps a ~5x
-- margin. Do not raise it — fold the blowup instead.
set_option maxHeartbeats 2000000
-- Some ported close-lemma signatures keep hypotheses (e.g. `h_v_val`) for interface uniformity
-- across the byte-shift cases even where a given case's proof does not consume them.
set_option linter.unusedVariables false

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

-- Field constants `val_4/8/16/32/64_zmod_p` now live in `Math/Word.lean`; `val_64_ne_zero` is local.
lemma val_64_ne_zero : (64 : ZMod p) ≠ 0 := by
  have h : (64 : ZMod p).val = 64 := val_64_zmod_p
  intro hz; rw [hz] at h; simp at h

/-- From `((c0 - m) * 64⁻¹).val < 1024`, conclude `c0 ≡ m (mod 64)`. -/
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
      have : k.val * 64 < 1024 * 64 := by
        exact Nat.mul_lt_mul_of_lt_of_le h_k_lt (le_refl 64) (by omega)
      omega
  have h_c0_val : c0.val = m.val + k.val * 64 := by
    have : c0.val = (m + k * 64).val := by rw [h_c0_eq]
    rw [this, ZMod.val_add_of_lt]
    · rw [h_k64_val]
    · rw [h_k64_val]; omega
  rw [h_c0_val]; omega

/-- `ZMod p` (`p > 2^17`) has no wrap to undo for products ≤
65536^2 < 2^32 < p. -/
lemma cancel_mul_65536 {a b c x : ZMod p}
    (h_x_dvd : x.val ∣ 65536) (h_x_pos : 0 < x.val) :
    a * x = b * 65536 + c * x → a = b * (((65536 / x.val : ℕ) : ZMod p)) + c := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  intro h_eq
  set z : ℕ := 65536 / x.val with z_def
  have h_x_le : x.val ≤ 65536 := Nat.le_of_dvd (by omega) h_x_dvd
  have _h_z_pos : 0 < z := Nat.div_pos h_x_le h_x_pos
  have _h_z_lt : z ≤ 65536 := by rw [z_def]; exact Nat.div_le_self _ _
  have h_xz : x.val * z = 65536 := by rw [z_def, Nat.mul_div_cancel' h_x_dvd]
  have h_xz_zmod : x * ((z : ℕ) : ZMod p) = 65536 := by
    have : ((x.val : ZMod p)) * ((z : ℕ) : ZMod p) = ((x.val * z : ℕ) : ZMod p) := by
      push_cast; ring
    rw [ZMod.natCast_zmod_val] at this
    rw [this, h_xz]; push_cast; rfl
  have h_eq2 : a * x = (b * ((z : ℕ) : ZMod p) + c) * x := by
    rw [← h_xz_zmod] at h_eq; linear_combination h_eq
  have h_x_ne : x ≠ 0 := by
    intro h; have : x.val = 0 := by rw [h]; exact ZMod.val_zero
    omega
  exact mul_right_cancel₀ h_x_ne h_eq2

/-- Polymorphic version of `cancel_mul_65536_v2`: zero-RHS form. -/
lemma cancel_mul_65536_zero {b c x : ZMod p}
    (h_x_dvd : x.val ∣ 65536) (h_x_pos : 0 < x.val) :
    b * 65536 + c * x = 0 → b * (((65536 / x.val : ℕ) : ZMod p)) + c = 0 := by
  intro h_eq
  have := cancel_mul_65536 h_x_dvd h_x_pos (a := 0) (b := b) (c := c)
  rw [zero_mul] at this; symm; exact this h_eq.symm

/-- Computes `(cb0 + cb1*2 + cb2*4 + cb3*8 + cb4*16 + cb5*32).val` in ZMod p
when each cb_i ∈ {0, 1}, asserting no wrap (sum ≤ 63 < p since p > 2^17). The
RHS is the natural sum-of-vals form. Reused by every spec.* to bridge
`is_mod_64`'s ZMod premise to a Nat equation. -/
lemma cb_sum_val_eq {cb0 cb1 cb2 cb3 cb4 cb5 : ZMod p}
    (b_cb0 : cb0 = 0 ∨ cb0 = 1) (b_cb1 : cb1 = 0 ∨ cb1 = 1)
    (b_cb2 : cb2 = 0 ∨ cb2 = 1) (b_cb3 : cb3 = 0 ∨ cb3 = 1)
    (b_cb4 : cb4 = 0 ∨ cb4 = 1) (b_cb5 : cb5 = 0 ∨ cb5 = 1) :
    (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32 : ZMod p).val =
      cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 + cb4.val * 16 + cb5.val * 32 := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  haveI : Fact (1 < p) := ⟨by omega⟩
  have hb0 : cb0.val ≤ 1 := by rcases b_cb0 with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]
  have hb1 : cb1.val ≤ 1 := by rcases b_cb1 with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]
  have hb2 : cb2.val ≤ 1 := by rcases b_cb2 with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]
  have hb3 : cb3.val ≤ 1 := by rcases b_cb3 with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]
  have hb4 : cb4.val ≤ 1 := by rcases b_cb4 with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]
  have hb5 : cb5.val ≤ 1 := by rcases b_cb5 with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]
  have m1 : (cb1 * 2 : ZMod p).val = cb1.val * 2 := by
    rw [ZMod.val_mul_of_lt] <;> rw [val_2_zmod_p]; omega
  have m2 : (cb2 * 4 : ZMod p).val = cb2.val * 4 := by
    rw [ZMod.val_mul_of_lt] <;> rw [val_4_zmod_p]; omega
  have m3 : (cb3 * 8 : ZMod p).val = cb3.val * 8 := by
    rw [ZMod.val_mul_of_lt] <;> rw [val_8_zmod_p]; omega
  have m4 : (cb4 * 16 : ZMod p).val = cb4.val * 16 := by
    rw [ZMod.val_mul_of_lt] <;> rw [val_16_zmod_p]; omega
  have m5 : (cb5 * 32 : ZMod p).val = cb5.val * 32 := by
    rw [ZMod.val_mul_of_lt] <;> rw [val_32_zmod_p]; omega
  have a1 : (cb0 + cb1 * 2 : ZMod p).val = cb0.val + cb1.val * 2 := by
    rw [ZMod.val_add_of_lt] <;> rw [m1]; omega
  have a2 : (cb0 + cb1 * 2 + cb2 * 4 : ZMod p).val =
      cb0.val + cb1.val * 2 + cb2.val * 4 := by
    rw [ZMod.val_add_of_lt] <;> rw [a1, m2]; omega
  have a3 : (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 : ZMod p).val =
      cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 := by
    rw [ZMod.val_add_of_lt] <;> rw [a2, m3]; omega
  have a4 : (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 : ZMod p).val =
      cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 + cb4.val * 16 := by
    rw [ZMod.val_add_of_lt] <;> rw [a3, m4]; omega
  rw [ZMod.val_add_of_lt] <;> rw [a4, m5]; omega

/-- The five-bit `c_bits` sum's `val`, in natural-sum form (the SRLW/SRAW shift count, mod 32). -/
lemma cb_sum5_val_eq {cb0 cb1 cb2 cb3 cb4 : ZMod p}
    (b_cb0 : cb0 = 0 ∨ cb0 = 1) (b_cb1 : cb1 = 0 ∨ cb1 = 1)
    (b_cb2 : cb2 = 0 ∨ cb2 = 1) (b_cb3 : cb3 = 0 ∨ cb3 = 1)
    (b_cb4 : cb4 = 0 ∨ cb4 = 1) :
    (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 : ZMod p).val =
      cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 + cb4.val * 16 := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have hb0 : cb0.val ≤ 1 := by rcases b_cb0 with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]
  have hb1 : cb1.val ≤ 1 := by rcases b_cb1 with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]
  have hb2 : cb2.val ≤ 1 := by rcases b_cb2 with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]
  have hb3 : cb3.val ≤ 1 := by rcases b_cb3 with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]
  have hb4 : cb4.val ≤ 1 := by rcases b_cb4 with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]
  have m1 : (cb1 * 2 : ZMod p).val = cb1.val * 2 := by
    rw [ZMod.val_mul_of_lt] <;> rw [val_2_zmod_p]; omega
  have m2 : (cb2 * 4 : ZMod p).val = cb2.val * 4 := by
    rw [ZMod.val_mul_of_lt] <;> rw [val_4_zmod_p]; omega
  have m3 : (cb3 * 8 : ZMod p).val = cb3.val * 8 := by
    rw [ZMod.val_mul_of_lt] <;> rw [val_8_zmod_p]; omega
  have m4 : (cb4 * 16 : ZMod p).val = cb4.val * 16 := by
    rw [ZMod.val_mul_of_lt] <;> rw [val_16_zmod_p]; omega
  have a1 : (cb0 + cb1 * 2 : ZMod p).val = cb0.val + cb1.val * 2 := by
    rw [ZMod.val_add_of_lt] <;> rw [m1]; omega
  have a2 : (cb0 + cb1 * 2 + cb2 * 4 : ZMod p).val = cb0.val + cb1.val * 2 + cb2.val * 4 := by
    rw [ZMod.val_add_of_lt] <;> rw [a1, m2]; omega
  have a3 : (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 : ZMod p).val =
      cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 := by
    rw [ZMod.val_add_of_lt] <;> rw [a2, m3]; omega
  rw [ZMod.val_add_of_lt] <;> rw [a3, m4]; omega

/-- **SRLW/SRAW shift-count bridge (mod 32).** The low five `c_bits` carry `c0.val % 32`, the
shift amount RV64 `srlw`/`sraw` use. Derived from the 6-bit `is_mod_64` via mod-of-mod (`% 32 = % 64 % 32`)
— `cb5` need not be zero. -/
lemma is_mod_32 {c0 cb0 cb1 cb2 cb3 cb4 cb5 : ZMod p}
    (b_cb0 : cb0 = 0 ∨ cb0 = 1) (b_cb1 : cb1 = 0 ∨ cb1 = 1) (b_cb2 : cb2 = 0 ∨ cb2 = 1)
    (b_cb3 : cb3 = 0 ∨ cb3 = 1) (b_cb4 : cb4 = 0 ∨ cb4 = 1) (b_cb5 : cb5 = 0 ∨ cb5 = 1)
    (h_c0_lt : c0.val < 65536)
    (h_diff : ((c0 - (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32))
        * (64 : ZMod p)⁻¹).val < 1024) :
    c0.val % 32 = (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 : ZMod p).val := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h6 := cb_sum_val_eq b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
  have h5 := cb_sum5_val_eq b_cb0 b_cb1 b_cb2 b_cb3 b_cb4
  have hb0 : cb0.val ≤ 1 := by rcases b_cb0 with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]
  have hb1 : cb1.val ≤ 1 := by rcases b_cb1 with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]
  have hb2 : cb2.val ≤ 1 := by rcases b_cb2 with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]
  have hb3 : cb3.val ≤ 1 := by rcases b_cb3 with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]
  have hb4 : cb4.val ≤ 1 := by rcases b_cb4 with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]
  have hb5 : cb5.val ≤ 1 := by rcases b_cb5 with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]
  have h_sum6_lt : (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32 : ZMod p).val < 64 := by
    rw [h6]; omega
  have h64 := is_mod_64 h_sum6_lt h_c0_lt h_diff
  have h_dvd : c0.val % 32 = c0.val % 64 % 32 := by rw [Nat.mod_mod_of_dvd]; exact ⟨2, rfl⟩
  rw [h_dvd, h64, h6, h5]; omega

/-- For booleans b ∈ {0, 1}, the product b · 65535 has val < 65536. -/
lemma bool_mul_65535_lt {b : ZMod p} (hb : b = 0 ∨ b = 1) :
    (b * 65535).val < 65536 := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  rcases hb with h | h
  · rw [h, zero_mul]; simp [ZMod.val_zero]
  · rw [h, one_mul]
    have : ((65535 : ℕ) : ZMod p).val = 65535 := ZMod.val_natCast_of_lt (by omega)
    have h_cast : (65535 : ZMod p) = ((65535 : ℕ) : ZMod p) := by push_cast; rfl
    rw [h_cast, this]; omega

/-- Within-byte right-shift identity for byte_shift=0. Given the cancellation
decomposition `b_j = hl_j * N + ll_j` (with `hl_j < M`, `ll_j < N`, `M*N=65536`,
and `v0123.val = M`), the 4-limb output vector `[hl_j + ll_{j+1}·v0123, ..., hl_3]`
equals the input shifted right by `S = log2(N)` bits.

This is the SR mirror of `sll_within_byte_shift` (ShiftLeft/Common.lean:96).
The role of M/N is swapped from SLL: in SR, `v0123 = 2^(16-S) = M`, and the shift
factor is `N = 2^S`. The output composes `hl_j + ll_{j+1}·v0123` (carries down for
right-shift) instead of `ll_j·v0123 + hl_{j-1}` (carries up for left-shift). -/
lemma srl_within_byte_shift {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
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
    (Word.toBitVec64 #v[hl0 + ll1 * v0123, hl1 + ll2 * v0123,
                              hl2 + ll3 * v0123, hl3]).toNat
    = (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat / N := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_N_pos : 0 < N := N_pos h_MN
  -- b_j.val = hl_j.val * N + ll_j.val
  have h_b0_val : b0.val = hl0.val * N + ll0.val := by rw [h_b0]; exact hi_lo_val h_MN lt_lh0 lt_ll0
  have h_b1_val : b1.val = hl1.val * N + ll1.val := by rw [h_b1]; exact hi_lo_val h_MN lt_lh1 lt_ll1
  have h_b2_val : b2.val = hl2.val * N + ll2.val := by rw [h_b2]; exact hi_lo_val h_MN lt_lh2 lt_ll2
  have h_b3_val : b3.val = hl3.val * N + ll3.val := by rw [h_b3]; exact hi_lo_val h_MN lt_lh3 lt_ll3
  -- (hl_j + ll_{j+1} * v0123).val for j = 0, 1, 2
  have h_compose0_val : (hl0 + ll1 * v0123).val = hl0.val + ll1.val * M :=
    lo_hi_val h_MN h_v_val lt_lh0 lt_ll1
  have h_compose1_val : (hl1 + ll2 * v0123).val = hl1.val + ll2.val * M :=
    lo_hi_val h_MN h_v_val lt_lh1 lt_ll2
  have h_compose2_val : (hl2 + ll3 * v0123).val = hl2.val + ll3.val * M :=
    lo_hi_val h_MN h_v_val lt_lh2 lt_ll3
  unfold Word.toBitVec64
  simp only [BitVec.toNat_ofNat, Word.toNat_def, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  rw [h_compose0_val, h_compose1_val, h_compose2_val,
      h_b0_val, h_b1_val, h_b2_val, h_b3_val]
  -- Per-byte bounds (used for the final mod_eq_of_lt steps).
  have h_b0_lt : hl0.val * N + ll0.val < 65536 := hi_lo_lt h_MN lt_lh0 lt_ll0
  have h_b1_lt : hl1.val * N + ll1.val < 65536 := hi_lo_lt h_MN lt_lh1 lt_ll1
  have h_b2_lt : hl2.val * N + ll2.val < 65536 := hi_lo_lt h_MN lt_lh2 lt_ll2
  have h_b3_lt : hl3.val * N + ll3.val < 65536 := hi_lo_lt h_MN lt_lh3 lt_ll3
  have h_lhs0_lt : hl0.val + ll1.val * M < 65536 := lo_hi_lt h_MN lt_lh0 lt_ll1
  have h_lhs1_lt : hl1.val + ll2.val * M < 65536 := lo_hi_lt h_MN lt_lh1 lt_ll2
  have h_lhs2_lt : hl2.val + ll3.val * M < 65536 := lo_hi_lt h_MN lt_lh2 lt_ll3
  have h_lhs3_lt : hl3.val < 65536 := lt_65536_of_lt_M h_MN lt_lh3
  -- Both sides fit in 2^64.
  have h_B_lt : (hl0.val * N + ll0.val) + (hl1.val * N + ll1.val) * 2 ^ 16
              + (hl2.val * N + ll2.val) * 2 ^ 32 + (hl3.val * N + ll3.val) * 2 ^ 48 < 2 ^ 64 := by
    omega
  have h_L_lt : (hl0.val + ll1.val * M) + (hl1.val + ll2.val * M) * 2 ^ 16
              + (hl2.val + ll3.val * M) * 2 ^ 32 + hl3.val * 2 ^ 48 < 2 ^ 64 := by
    omega
  -- Key Nat identity: N * L_inner + ll0.val = B_inner.
  have h_key : N * ((hl0.val + ll1.val * M) + (hl1.val + ll2.val * M) * 2 ^ 16
                + (hl2.val + ll3.val * M) * 2 ^ 32 + hl3.val * 2 ^ 48) + ll0.val
            = (hl0.val * N + ll0.val) + (hl1.val * N + ll1.val) * 2 ^ 16
              + (hl2.val * N + ll2.val) * 2 ^ 32 + (hl3.val * N + ll3.val) * 2 ^ 48 := by
    linear_combination
      (ll1.val + ll2.val * 2 ^ 16 + ll3.val * 2 ^ 32) * h_MN
  -- Goal: L_inner % 2^64 = B_inner % 2^64 / N % 2^64.
  rw [Nat.mod_eq_of_lt h_L_lt, Nat.mod_eq_of_lt h_B_lt, ← h_key]
  -- Goal: L_inner = (N * L_inner + ll0.val) / N % 2^64.
  rw [Nat.add_comm (N * _) ll0.val, Nat.mul_comm N _,
      Nat.add_mul_div_right _ _ h_N_pos, Nat.div_eq_of_lt lt_ll0, Nat.zero_add]

/-- Byte-shift=1 variant of `srl_within_byte_shift`. The output vector starts
at byte index 1 of the within-byte result; the high byte is 0. Total shift = S+16,
so divisor = N * 2^16. -/
lemma srl_within_byte_shift_1 {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
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
    (Word.toBitVec64 #v[hl1 + ll2 * v0123, hl2 + ll3 * v0123, hl3, 0]).toNat
    = (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat / (N * 2 ^ 16) := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_NM : N * M = 65536 := by linarith [h_MN, Nat.mul_comm M N]
  have h_N_pos : 0 < N := N_pos h_MN
  have h_b0_val : b0.val = hl0.val * N + ll0.val := by rw [h_b0]; exact hi_lo_val h_MN lt_lh0 lt_ll0
  have h_b1_val : b1.val = hl1.val * N + ll1.val := by rw [h_b1]; exact hi_lo_val h_MN lt_lh1 lt_ll1
  have h_b2_val : b2.val = hl2.val * N + ll2.val := by rw [h_b2]; exact hi_lo_val h_MN lt_lh2 lt_ll2
  have h_b3_val : b3.val = hl3.val * N + ll3.val := by rw [h_b3]; exact hi_lo_val h_MN lt_lh3 lt_ll3
  have h_compose1_val : (hl1 + ll2 * v0123).val = hl1.val + ll2.val * M :=
    lo_hi_val h_MN h_v_val lt_lh1 lt_ll2
  have h_compose2_val : (hl2 + ll3 * v0123).val = hl2.val + ll3.val * M :=
    lo_hi_val h_MN h_v_val lt_lh2 lt_ll3
  unfold Word.toBitVec64
  simp only [BitVec.toNat_ofNat, Word.toNat_def, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, ZMod.val_zero,
    zero_mul, add_zero]
  rw [h_compose1_val, h_compose2_val,
      h_b0_val, h_b1_val, h_b2_val, h_b3_val]
  have h_b0_lt : hl0.val * N + ll0.val < 65536 := hi_lo_lt h_MN lt_lh0 lt_ll0
  have h_b1_lt : hl1.val * N + ll1.val < 65536 := hi_lo_lt h_MN lt_lh1 lt_ll1
  have h_b2_lt : hl2.val * N + ll2.val < 65536 := hi_lo_lt h_MN lt_lh2 lt_ll2
  have h_b3_lt : hl3.val * N + ll3.val < 65536 := hi_lo_lt h_MN lt_lh3 lt_ll3
  have h_lhs1_lt : hl1.val + ll2.val * M < 65536 := lo_hi_lt h_MN lt_lh1 lt_ll2
  have h_lhs2_lt : hl2.val + ll3.val * M < 65536 := lo_hi_lt h_MN lt_lh2 lt_ll3
  have h_lhs3_lt : hl3.val < 65536 := lt_65536_of_lt_M h_MN lt_lh3
  have h_B_lt : (hl0.val * N + ll0.val) + (hl1.val * N + ll1.val) * 2 ^ 16
              + (hl2.val * N + ll2.val) * 2 ^ 32 + (hl3.val * N + ll3.val) * 2 ^ 48 < 2 ^ 64 := by
    omega
  have h_L_lt : (hl1.val + ll2.val * M) + (hl2.val + ll3.val * M) * 2 ^ 16 + hl3.val * 2 ^ 32 < 2 ^ 64 := by
    omega
  have h_rem_lt : (hl0.val * N + ll0.val) + 2 ^ 16 * ll1.val < N * 2 ^ 16 := by
    nlinarith [lt_lh0, lt_ll0, lt_ll1, h_MN, h_NM, h_N_pos]
  have h_NM16_pos : 0 < N * 2 ^ 16 := Nat.mul_pos h_N_pos (by omega)
  -- Key identity: (N * 2^16) * L_1 + (b_0 + 2^16 * ll_1) = B.
  have h_key : (N * 2 ^ 16) * ((hl1.val + ll2.val * M) + (hl2.val + ll3.val * M) * 2 ^ 16
                + hl3.val * 2 ^ 32) + ((hl0.val * N + ll0.val) + 2 ^ 16 * ll1.val)
            = (hl0.val * N + ll0.val) + (hl1.val * N + ll1.val) * 2 ^ 16
              + (hl2.val * N + ll2.val) * 2 ^ 32 + (hl3.val * N + ll3.val) * 2 ^ 48 := by
    linear_combination
      (ll2.val + ll3.val * 2 ^ 16) * 2 ^ 16 * h_MN
  rw [Nat.mod_eq_of_lt h_L_lt, Nat.mod_eq_of_lt h_B_lt, ← h_key]
  rw [Nat.add_comm ((N * 2 ^ 16) * _) _, Nat.mul_comm (N * 2 ^ 16) _,
      Nat.add_mul_div_right _ _ h_NM16_pos, Nat.div_eq_of_lt h_rem_lt, Nat.zero_add]

/-- Byte-shift=2 variant. Output starts at byte index 2; top two bytes are 0.
Total shift = S + 32, so divisor = N * 2^32. -/
lemma srl_within_byte_shift_2 {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
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
    (Word.toBitVec64 #v[hl2 + ll3 * v0123, hl3, 0, 0]).toNat
    = (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat / (N * 2 ^ 32) := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_NM : N * M = 65536 := by linarith [h_MN, Nat.mul_comm M N]
  have h_N_pos : 0 < N := N_pos h_MN
  have h_b0_val : b0.val = hl0.val * N + ll0.val := by rw [h_b0]; exact hi_lo_val h_MN lt_lh0 lt_ll0
  have h_b1_val : b1.val = hl1.val * N + ll1.val := by rw [h_b1]; exact hi_lo_val h_MN lt_lh1 lt_ll1
  have h_b2_val : b2.val = hl2.val * N + ll2.val := by rw [h_b2]; exact hi_lo_val h_MN lt_lh2 lt_ll2
  have h_b3_val : b3.val = hl3.val * N + ll3.val := by rw [h_b3]; exact hi_lo_val h_MN lt_lh3 lt_ll3
  have h_compose2_val : (hl2 + ll3 * v0123).val = hl2.val + ll3.val * M :=
    lo_hi_val h_MN h_v_val lt_lh2 lt_ll3
  unfold Word.toBitVec64
  simp only [BitVec.toNat_ofNat, Word.toNat_def, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, ZMod.val_zero,
    zero_mul, add_zero]
  rw [h_compose2_val,
      h_b0_val, h_b1_val, h_b2_val, h_b3_val]
  have h_b0_lt : hl0.val * N + ll0.val < 65536 := hi_lo_lt h_MN lt_lh0 lt_ll0
  have h_b1_lt : hl1.val * N + ll1.val < 65536 := hi_lo_lt h_MN lt_lh1 lt_ll1
  have h_b2_lt : hl2.val * N + ll2.val < 65536 := hi_lo_lt h_MN lt_lh2 lt_ll2
  have h_b3_lt : hl3.val * N + ll3.val < 65536 := hi_lo_lt h_MN lt_lh3 lt_ll3
  have h_lhs2_lt : hl2.val + ll3.val * M < 65536 := lo_hi_lt h_MN lt_lh2 lt_ll3
  have h_lhs3_lt : hl3.val < 65536 := lt_65536_of_lt_M h_MN lt_lh3
  have h_B_lt : (hl0.val * N + ll0.val) + (hl1.val * N + ll1.val) * 2 ^ 16
              + (hl2.val * N + ll2.val) * 2 ^ 32 + (hl3.val * N + ll3.val) * 2 ^ 48 < 2 ^ 64 := by
    omega
  have h_L_lt : (hl2.val + ll3.val * M) + hl3.val * 2 ^ 16 < 2 ^ 64 := by
    omega
  have h_rem_lt : ((hl0.val * N + ll0.val) + (hl1.val * N + ll1.val) * 2 ^ 16) + 2 ^ 32 * ll2.val < N * 2 ^ 32 := by
    nlinarith [lt_lh0, lt_ll0, lt_lh1, lt_ll1, lt_ll2, h_MN, h_NM, h_N_pos]
  have h_NM32_pos : 0 < N * 2 ^ 32 := Nat.mul_pos h_N_pos (by omega)
  have h_key : (N * 2 ^ 32) * ((hl2.val + ll3.val * M) + hl3.val * 2 ^ 16)
              + (((hl0.val * N + ll0.val) + (hl1.val * N + ll1.val) * 2 ^ 16) + 2 ^ 32 * ll2.val)
            = (hl0.val * N + ll0.val) + (hl1.val * N + ll1.val) * 2 ^ 16
              + (hl2.val * N + ll2.val) * 2 ^ 32 + (hl3.val * N + ll3.val) * 2 ^ 48 := by
    linear_combination
      ll3.val * 2 ^ 32 * h_MN
  rw [Nat.mod_eq_of_lt h_L_lt, Nat.mod_eq_of_lt h_B_lt, ← h_key]
  rw [Nat.add_comm ((N * 2 ^ 32) * _) _, Nat.mul_comm (N * 2 ^ 32) _,
      Nat.add_mul_div_right _ _ h_NM32_pos, Nat.div_eq_of_lt h_rem_lt, Nat.zero_add]

/-- Byte-shift=3 variant. Output is just `hl_3` in byte 0; bytes 1, 2, 3 are 0.
Total shift = S + 48, so divisor = N * 2^48. -/
lemma srl_within_byte_shift_3 {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
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
    (Word.toBitVec64 #v[hl3, 0, 0, 0]).toNat
    = (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat / (N * 2 ^ 48) := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_NM : N * M = 65536 := by linarith [h_MN, Nat.mul_comm M N]
  have h_N_pos : 0 < N := N_pos h_MN
  have h_b0_val : b0.val = hl0.val * N + ll0.val := by rw [h_b0]; exact hi_lo_val h_MN lt_lh0 lt_ll0
  have h_b1_val : b1.val = hl1.val * N + ll1.val := by rw [h_b1]; exact hi_lo_val h_MN lt_lh1 lt_ll1
  have h_b2_val : b2.val = hl2.val * N + ll2.val := by rw [h_b2]; exact hi_lo_val h_MN lt_lh2 lt_ll2
  have h_b3_val : b3.val = hl3.val * N + ll3.val := by rw [h_b3]; exact hi_lo_val h_MN lt_lh3 lt_ll3
  unfold Word.toBitVec64
  simp only [BitVec.toNat_ofNat, Word.toNat_def, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, ZMod.val_zero,
    zero_mul, add_zero]
  rw [h_b0_val, h_b1_val, h_b2_val, h_b3_val]
  have h_b0_lt : hl0.val * N + ll0.val < 65536 := hi_lo_lt h_MN lt_lh0 lt_ll0
  have h_b1_lt : hl1.val * N + ll1.val < 65536 := hi_lo_lt h_MN lt_lh1 lt_ll1
  have h_b2_lt : hl2.val * N + ll2.val < 65536 := hi_lo_lt h_MN lt_lh2 lt_ll2
  have h_b3_lt : hl3.val * N + ll3.val < 65536 := hi_lo_lt h_MN lt_lh3 lt_ll3
  have h_lhs0_lt : hl3.val < 65536 := lt_65536_of_lt_M h_MN lt_lh3
  have h_B_lt : (hl0.val * N + ll0.val) + (hl1.val * N + ll1.val) * 2 ^ 16
              + (hl2.val * N + ll2.val) * 2 ^ 32 + (hl3.val * N + ll3.val) * 2 ^ 48 < 2 ^ 64 := by
    omega
  have h_L_lt : hl3.val < 2 ^ 64 := by omega
  have h_rem_lt : ((hl0.val * N + ll0.val) + (hl1.val * N + ll1.val) * 2 ^ 16
                 + (hl2.val * N + ll2.val) * 2 ^ 32) + 2 ^ 48 * ll3.val < N * 2 ^ 48 := by
    nlinarith [lt_lh0, lt_ll0, lt_lh1, lt_ll1, lt_lh2, lt_ll2, lt_ll3, h_MN, h_NM, h_N_pos]
  have h_NM48_pos : 0 < N * 2 ^ 48 := Nat.mul_pos h_N_pos (by omega)
  have h_key : (N * 2 ^ 48) * hl3.val
              + (((hl0.val * N + ll0.val) + (hl1.val * N + ll1.val) * 2 ^ 16
                 + (hl2.val * N + ll2.val) * 2 ^ 32) + 2 ^ 48 * ll3.val)
            = (hl0.val * N + ll0.val) + (hl1.val * N + ll1.val) * 2 ^ 16
              + (hl2.val * N + ll2.val) * 2 ^ 32 + (hl3.val * N + ll3.val) * 2 ^ 48 := by
    ring
  rw [Nat.mod_eq_of_lt h_L_lt, Nat.mod_eq_of_lt h_B_lt, ← h_key]
  rw [Nat.add_comm ((N * 2 ^ 48) * _) _, Nat.mul_comm (N * 2 ^ 48) _,
      Nat.add_mul_div_right _ _ h_NM48_pos, Nat.div_eq_of_lt h_rem_lt, Nat.zero_add]

/-! ## Shared `c_bits`-exponent `val` bridges

Each was a byte-identical `have` block repeated once per byte-shift / word variant in the close-case
wrappers below. Both are pure `ZMod.val`/`Nat` arithmetic — no `2 ^ 64` / `BitVec` reduction — so
the kernel checks the body once and each use is a plain instantiation. Mirrors
`ShiftLeftCore.inner_val`/`inner_hi_val`. -/

/-- The bit-decomposition exponent `(cb0 + 2cb1 + 4cb2 + 8cb3).val = S` (the within-byte shift
count), shared by every close-case wrapper. -/
lemma inner_val {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    {S : ℕ} (hS_le : S ≤ 16) {cb0 cb1 cb2 cb3 : ZMod p}
    (h_inner_eq : cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8
                  = ((S : ℕ) : ZMod p)) :
    (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8 : ZMod p).val = S := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  rw [h_inner_eq]; exact ZMod.val_natCast_of_lt (by omega)

/-- The complementary high exponent `(16 - (cb0 + 2cb1 + 4cb2 + 8cb3)).val = 16 - S`. -/
lemma inner_hi_val {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    {S : ℕ} (hS_le : S ≤ 16) {cb0 cb1 cb2 cb3 : ZMod p}
    (h_inner_eq : cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8
                  = ((S : ℕ) : ZMod p)) :
    (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
            + cb3 * 8) : ZMod p).val = 16 - S := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  rw [show (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
            + cb3 * 8) : ZMod p) = (((16 - S) : ℕ) : ZMod p) from by
    rw [h_inner_eq, Nat.cast_sub hS_le]; push_cast; ring]
  exact ZMod.val_natCast_of_lt (by omega)

/-- Convenience wrapper for `spec.srl_common`'s `byte_shift=0` case (su160 = 1).
Combines `cancel_mul_65536`, bound normalization, and the `>>>`-to-`/` bridge
so each within-byte sub-case can be closed by providing only the cb_i substitution
facts and the numeric (S, M, N) triple.

Mirrors `sll_close_cb4cb5_zero_case` (ShiftLeft/Common.lean:185); the role-swap
between SLL and SR puts `M = 2^(16-S)` (the v0123 value) and `N = 2^S` (the shift
amount factor) — opposite of SLL where `M = 2^S` and `N = 2^(16-S)`. -/
lemma srl_close_su16_0_case {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (S : ℕ) (h_S_le : S ≤ 15) (M N : ℕ)
    (h_MN : M * N = 65536) (h_M_pos : 0 < M) (h_M_eq : M = 2 ^ (16 - S))
    (h_N_eq : N = 2 ^ S)
    {cb0 cb1 cb2 cb3 cb4 cb5 v0123 b0 b1 b2 b3
      ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 : ZMod p}
    (h_M_lt_p : M < p) (h_v0123_explicit : v0123 = ((M : ℕ) : ZMod p))
    (h_inner_eq : cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8
                  = ((S : ℕ) : ZMod p))
    (h_total_eq : cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32
                  = ((S : ℕ) : ZMod p))
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
                              hl2 + ll3 * v0123, hl3]).toNat
    = (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat
        / 2 ^ (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_v_val : v0123.val = M := by
    rw [h_v0123_explicit]; exact ZMod.val_natCast_of_lt h_M_lt_p
  -- Normalize bounds using h_inner_eq. For SR, ll < 2^S (the inner sum), hl < 2^(16-S).
  have h_inner_val := inner_val (by omega) h_inner_eq
  have h_inner_hi_val := inner_hi_val (by omega) h_inner_eq
  rw [h_inner_val] at lt_ll0 lt_ll1 lt_ll2 lt_ll3
  rw [h_inner_hi_val] at lt_lh0 lt_lh1 lt_lh2 lt_lh3
  -- Total shift = S.
  have h_total_val : (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val
                      = S := by
    rw [h_total_eq]; exact ZMod.val_natCast_of_lt (by omega)
  rw [h_total_val]
  -- Apply cancel_mul_65536 to extract b_j = hl_j * N + ll_j.
  have hdvd : v0123.val ∣ 65536 := by rw [h_v_val]; exact ⟨N, h_MN.symm⟩
  have hpos : 0 < v0123.val := by rw [h_v_val]; exact h_M_pos
  have h_b0' := cancel_mul_65536 hdvd hpos h_b0_dec
  have h_b1' := cancel_mul_65536 hdvd hpos h_b1_dec
  have h_b2' := cancel_mul_65536 hdvd hpos h_b2_dec
  have h_b3' := cancel_mul_65536 hdvd hpos h_b3_dec
  rw [h_v_val] at h_b0' h_b1' h_b2' h_b3'
  -- Bridge `/ 2^S` to `/ N`.
  rw [show (2 : ℕ) ^ S = N from h_N_eq.symm]
  -- Replace `65536/M` in h_b_j' with `N`.
  have h_div_eq : (65536 : ℕ) / M = N := by
    rw [← h_MN]; exact Nat.mul_div_cancel_left N h_M_pos
  rw [h_div_eq] at h_b0' h_b1' h_b2' h_b3'
  -- Convert bounds from `2^S`/`2^(16-S)` to `N`/`M`.
  have h_lt_ll0 : ll0.val < N := by rw [h_N_eq]; exact lt_ll0
  have h_lt_ll1 : ll1.val < N := by rw [h_N_eq]; exact lt_ll1
  have h_lt_ll2 : ll2.val < N := by rw [h_N_eq]; exact lt_ll2
  have h_lt_ll3 : ll3.val < N := by rw [h_N_eq]; exact lt_ll3
  have h_lt_lh0 : hl0.val < M := by rw [h_M_eq]; exact lt_lh0
  have h_lt_lh1 : hl1.val < M := by rw [h_M_eq]; exact lt_lh1
  have h_lt_lh2 : hl2.val < M := by rw [h_M_eq]; exact lt_lh2
  have h_lt_lh3 : hl3.val < M := by rw [h_M_eq]; exact lt_lh3
  exact srl_within_byte_shift M N h_MN h_M_pos h_v_val
    h_lt_ll0 h_lt_ll1 h_lt_ll2 h_lt_ll3 h_lt_lh0 h_lt_lh1 h_lt_lh2 h_lt_lh3
    h_b0' h_b1' h_b2' h_b3'

/-- Wrapper for `spec.srl_common`'s `byte_shift=1` case (su161 = 1, cb4=1, cb5=0).
Total shift = S + 16. -/
lemma srl_close_su16_1_case {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (S : ℕ) (h_S_le : S ≤ 15) (M N : ℕ)
    (h_MN : M * N = 65536) (h_M_pos : 0 < M) (h_M_eq : M = 2 ^ (16 - S))
    (h_N_eq : N = 2 ^ S)
    {cb0 cb1 cb2 cb3 cb4 cb5 v0123 b0 b1 b2 b3
      ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 : ZMod p}
    (h_M_lt_p : M < p) (h_v0123_explicit : v0123 = ((M : ℕ) : ZMod p))
    (h_inner_eq : cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8
                  = ((S : ℕ) : ZMod p))
    (h_total_eq : cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32
                  = (((S + 16) : ℕ) : ZMod p))
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
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_v_val : v0123.val = M := by
    rw [h_v0123_explicit]; exact ZMod.val_natCast_of_lt h_M_lt_p
  have h_inner_val := inner_val (by omega) h_inner_eq
  have h_inner_hi_val := inner_hi_val (by omega) h_inner_eq
  rw [h_inner_val] at lt_ll0 lt_ll1 lt_ll2 lt_ll3
  rw [h_inner_hi_val] at lt_lh0 lt_lh1 lt_lh2 lt_lh3
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
  -- Bridge `/ 2^(S+16)` to `/ (N * 2^16)`.
  rw [show (2 : ℕ) ^ (S + 16) = N * 2 ^ 16 from by rw [pow_add, h_N_eq]]
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
  exact srl_within_byte_shift_1 M N h_MN h_M_pos h_v_val
    h_lt_ll0 h_lt_ll1 h_lt_ll2 h_lt_ll3 h_lt_lh0 h_lt_lh1 h_lt_lh2 h_lt_lh3
    h_b0' h_b1' h_b2' h_b3'

/-- Wrapper for `spec.srl_common`'s `byte_shift=2` case (su162 = 1, cb4=0, cb5=1).
Total shift = S + 32. -/
lemma srl_close_su16_2_case {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (S : ℕ) (h_S_le : S ≤ 15) (M N : ℕ)
    (h_MN : M * N = 65536) (h_M_pos : 0 < M) (h_M_eq : M = 2 ^ (16 - S))
    (h_N_eq : N = 2 ^ S)
    {cb0 cb1 cb2 cb3 cb4 cb5 v0123 b0 b1 b2 b3
      ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 : ZMod p}
    (h_M_lt_p : M < p) (h_v0123_explicit : v0123 = ((M : ℕ) : ZMod p))
    (h_inner_eq : cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8
                  = ((S : ℕ) : ZMod p))
    (h_total_eq : cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32
                  = (((S + 32) : ℕ) : ZMod p))
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
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_v_val : v0123.val = M := by
    rw [h_v0123_explicit]; exact ZMod.val_natCast_of_lt h_M_lt_p
  have h_inner_val := inner_val (by omega) h_inner_eq
  have h_inner_hi_val := inner_hi_val (by omega) h_inner_eq
  rw [h_inner_val] at lt_ll0 lt_ll1 lt_ll2 lt_ll3
  rw [h_inner_hi_val] at lt_lh0 lt_lh1 lt_lh2 lt_lh3
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
  rw [show (2 : ℕ) ^ (S + 32) = N * 2 ^ 32 from by rw [pow_add, h_N_eq]]
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
  exact srl_within_byte_shift_2 M N h_MN h_M_pos h_v_val
    h_lt_ll0 h_lt_ll1 h_lt_ll2 h_lt_ll3 h_lt_lh0 h_lt_lh1 h_lt_lh2 h_lt_lh3
    h_b0' h_b1' h_b2' h_b3'

/-- Wrapper for `spec.srl_common`'s `byte_shift=3` case (su163 = 1, cb4=1, cb5=1).
Total shift = S + 48. -/
lemma srl_close_su16_3_case {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (S : ℕ) (h_S_le : S ≤ 15) (M N : ℕ)
    (h_MN : M * N = 65536) (h_M_pos : 0 < M) (h_M_eq : M = 2 ^ (16 - S))
    (h_N_eq : N = 2 ^ S)
    {cb0 cb1 cb2 cb3 cb4 cb5 v0123 b0 b1 b2 b3
      ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 : ZMod p}
    (h_M_lt_p : M < p) (h_v0123_explicit : v0123 = ((M : ℕ) : ZMod p))
    (h_inner_eq : cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8
                  = ((S : ℕ) : ZMod p))
    (h_total_eq : cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32
                  = (((S + 48) : ℕ) : ZMod p))
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
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_v_val : v0123.val = M := by
    rw [h_v0123_explicit]; exact ZMod.val_natCast_of_lt h_M_lt_p
  have h_inner_val := inner_val (by omega) h_inner_eq
  have h_inner_hi_val := inner_hi_val (by omega) h_inner_eq
  rw [h_inner_val] at lt_ll0 lt_ll1 lt_ll2 lt_ll3
  rw [h_inner_hi_val] at lt_lh0 lt_lh1 lt_lh2 lt_lh3
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
  rw [show (2 : ℕ) ^ (S + 48) = N * 2 ^ 48 from by rw [pow_add, h_N_eq]]
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
  exact srl_within_byte_shift_3 M N h_MN h_M_pos h_v_val
    h_lt_ll0 h_lt_ll1 h_lt_ll2 h_lt_ll3 h_lt_lh0 h_lt_lh1 h_lt_lh2 h_lt_lh3
    h_b0' h_b1' h_b2' h_b3'

/-! ## SRA chain (arithmetic right shift): sign-fill on top of the SRL division -/

/-- Bridge `(Word.toBitVec64 b).msb` to a Nat predicate on the high limb.
For a U64-bounded word, the 64-bit BitVec's msb (bit 63) sits in the high limb
`b[3]` (which occupies bit positions 48..63 of the combined Nat). Used by SRA/SRAW
proofs to bridge `BitVec.sshiftRight` semantics (case-splits on msb) to the
`U16MSBOperation` constraint on `b[3]` (case-splits on `b[3].val ≥ 32768 = 2^15`). -/
lemma toBitVec64_msb_eq_b3_ge {p : ℕ} [NeZero p]
    {b : Word (ZMod p)} (h_isU64 : Word.isU64 b) :
    (Word.toBitVec64 b).msb = decide (b[3].val ≥ 32768) := by
  have ⟨b0_16, b1_16, b2_16, b3_16⟩ := Word.lt_cases_of_isU64 h_isU64
  rw [BitVec.msb_eq_decide, Word.toBitVec64_toNat h_isU64, Word.toNat_def]
  -- Goal: decide (2^(64-1) ≤ b0+b1*2^16+b2*2^32+b3*2^48) = decide (b3 ≥ 32768)
  -- Substitute concrete numerics so omega can close.
  have e16 : (2 : ℕ) ^ 16 = 65536 := by decide
  have e32 : (2 : ℕ) ^ 32 = 4294967296 := by decide
  have e48 : (2 : ℕ) ^ 48 = 281474976710656 := by decide
  have e63 : (2 : ℕ) ^ (64 - 1) = 9223372036854775808 := by decide
  rw [e16, e32, e48, e63] at *
  congr 1; apply propext; omega

/-- Generic bound for the lr_j limb form: given the byte decomposition `hl < M`,
`ll < N` with `M*N = 65536` and `v0123.val = M`, conclude `(hl + ll*v0123).val < 65536`.
This is the poly analog of `limb_16_of_cancel` (Common.lean:81) but as a generic
parameterized bound rather than a 16-way case split — callers supply (M, N) per
sub-case. -/
lemma limb_16_lt_aux {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (M N : ℕ) (h_MN : M * N = 65536) (h_M_pos : 0 < M)
    {hl ll v0123 : ZMod p}
    (h_v0123_eq : v0123.val = M)
    (lt_hl : hl.val < M) (lt_ll : ll.val < N) :
    (hl + ll * v0123).val < 65536 := by
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  have hp : 2 ^ 17 < p := Fact.out
  have h_N_pos : 0 < N := by nlinarith [h_MN, h_M_pos]
  have h_ll_v_lt_p : ll.val * v0123.val < p := by
    rw [h_v0123_eq]; nlinarith [h_MN, lt_ll, h_M_pos]
  have h_ll_v_val : (ll * v0123).val = ll.val * v0123.val :=
    ZMod.val_mul_of_lt h_ll_v_lt_p
  have h_add_lt_p : hl.val + (ll * v0123).val < p := by
    rw [h_ll_v_val, h_v0123_eq]; nlinarith [lt_hl, lt_ll, h_MN, h_M_pos]
  have h_add_val : (hl + ll * v0123).val = hl.val + (ll * v0123).val :=
    ZMod.val_add_of_lt h_add_lt_p
  rw [h_add_val, h_ll_v_val, h_v0123_eq]
  nlinarith [lt_hl, lt_ll, h_MN, h_M_pos]

/-- Per-pattern bound for the lr_j limb form expressed in cb-shape. Used by
`ops_U64_a_local`'s `lr_blast` helper to discharge each of 16 cb-patterns
without re-deriving bound-form conversions inside each leaf. Callers supply
(S, M, N) plus the substituted `h_inner_eq` and `h_v0123_explicit` from the
`hcb0..hcb3` rcases; the lemma converts the cb-shape bounds to (M, N) form and
delegates to `limb_16_lt_aux`. -/
lemma lr_blast_per_pattern {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (S M N : ℕ) (h_S_le : S ≤ 16) (h_MN : M * N = 65536) (h_M_pos : 0 < M)
    (h_M_eq : M = 2 ^ (16 - S)) (h_N_eq : N = 2 ^ S)
    {cb0 cb1 cb2 cb3 v0123 hl ll : ZMod p}
    (h_inner_eq : cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8
                  = ((S : ℕ) : ZMod p))
    (h_v0123_explicit : v0123 = ((M : ℕ) : ZMod p))
    (lt_hl : hl.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                  + cb3 * 8) : ZMod p).val)
    (lt_ll : ll.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                            + cb3 * 8 : ZMod p).val) :
    (hl + ll * v0123).val < 65536 := by
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  have hp : 2 ^ 17 < p := Fact.out
  have h_N_pos : 0 < N := by nlinarith [h_MN, h_M_pos]
  have h_M_lt_p : M < p := by nlinarith [h_MN, h_N_pos, hp]
  have h_v_val : v0123.val = M := by
    rw [h_v0123_explicit]; exact ZMod.val_natCast_of_lt h_M_lt_p
  rw [inner_val h_S_le h_inner_eq, ← h_N_eq] at lt_ll
  rw [inner_hi_val h_S_le h_inner_eq, ← h_M_eq] at lt_hl
  exact limb_16_lt_aux M N h_MN h_M_pos h_v_val lt_hl lt_ll

/-- **Limb-result bound (16-way).** Each `limb_result` limb `hl + ll * v0123` — the within-byte shifted
reassembly — is `< 65536`, dispatching the 16 `c_bits` patterns to `lr_blast_per_pattern`. Used by the
SRLW/SRAW output-limb range obligations (`a[0]`, `a[1] < 2^16`) the sign-extension keystone needs. -/
lemma limb_result_lt {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    {cb0 cb1 cb2 cb3 v01 v012 v0123 hl ll : ZMod p}
    (b_cb0 : cb0 = 0 ∨ cb0 = 1) (b_cb1 : cb1 = 0 ∨ cb1 = 1)
    (b_cb2 : cb2 = 0 ∨ cb2 = 1) (b_cb3 : cb3 = 0 ∨ cb3 = 1)
    (eq_v01 : v01 = (1 + -cb0 + 1) * 2 * ((1 + -cb1) * 3 + 1))
    (eq_v012 : v012 = v01 * ((1 + -cb2) * 15 + 1))
    (eq_v0123 : v0123 = v012 * ((1 + -cb3) * 255 + 1))
    (lt_hl : hl.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                  + cb3 * 8) : ZMod p).val)
    (lt_ll : ll.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                            + cb3 * 8 : ZMod p).val) :
    (hl + ll * v0123).val < 65536 := by
  rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
    rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3 <;>
    first
    | exact lr_blast_per_pattern 0 65536 1 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        lt_hl lt_ll
    | exact lr_blast_per_pattern 1 32768 2 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        lt_hl lt_ll
    | exact lr_blast_per_pattern 2 16384 4 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        lt_hl lt_ll
    | exact lr_blast_per_pattern 3 8192 8 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        lt_hl lt_ll
    | exact lr_blast_per_pattern 4 4096 16 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        lt_hl lt_ll
    | exact lr_blast_per_pattern 5 2048 32 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        lt_hl lt_ll
    | exact lr_blast_per_pattern 6 1024 64 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        lt_hl lt_ll
    | exact lr_blast_per_pattern 7 512 128 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        lt_hl lt_ll
    | exact lr_blast_per_pattern 8 256 256 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        lt_hl lt_ll
    | exact lr_blast_per_pattern 9 128 512 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        lt_hl lt_ll
    | exact lr_blast_per_pattern 10 64 1024 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        lt_hl lt_ll
    | exact lr_blast_per_pattern 11 32 2048 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        lt_hl lt_ll
    | exact lr_blast_per_pattern 12 16 4096 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        lt_hl lt_ll
    | exact lr_blast_per_pattern 13 8 8192 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        lt_hl lt_ll
    | exact lr_blast_per_pattern 14 4 16384 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        lt_hl lt_ll
    | exact lr_blast_per_pattern 15 2 32768 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        lt_hl lt_ll

/-- **Sign-fill per-pattern bound.** For the SRAW negative arm, the sign-extended limb
`hl + (65536 - v0123)` (with `v0123 = M = 2^(16-S)`, `hl < M`) is `< 65536`. Converts the
cb-shape high-limb bound to `(M, N)` form and bounds the complemented sum. -/
lemma sf_blast_per_pattern {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (S M N : ℕ) (h_S_le : S ≤ 16) (h_MN : M * N = 65536) (h_M_pos : 0 < M)
    (h_M_eq : M = 2 ^ (16 - S)) (h_N_eq : N = 2 ^ S)
    {cb0 cb1 cb2 cb3 v0123 hl : ZMod p}
    (h_inner_eq : cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8
                  = ((S : ℕ) : ZMod p))
    (h_v0123_explicit : v0123 = ((M : ℕ) : ZMod p))
    (lt_hl : hl.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                  + cb3 * 8) : ZMod p).val) :
    (hl + (((65536 : ℕ) : ZMod p) - v0123)).val < 65536 := by
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  have hp : 2 ^ 17 < p := Fact.out
  have h_N_pos : 0 < N := by nlinarith [h_MN, h_M_pos]
  have h_M_lt_p : M < p := by nlinarith [h_MN, h_N_pos, hp]
  have hMle : M ≤ 65536 := Nat.le_of_dvd (by norm_num) ⟨N, h_MN.symm⟩
  rw [inner_hi_val h_S_le h_inner_eq, ← h_M_eq] at lt_hl
  have hsub_cast : (((65536 : ℕ) : ZMod p) - v0123) = ((65536 - M : ℕ) : ZMod p) := by
    rw [h_v0123_explicit, Nat.cast_sub hMle]
  rw [hsub_cast]
  have hc_val : ((65536 - M : ℕ) : ZMod p).val = 65536 - M :=
    ZMod.val_natCast_of_lt (by omega)
  have h_add_lt_p : hl.val + ((65536 - M : ℕ) : ZMod p).val < p := by rw [hc_val]; omega
  have h_add_val : (hl + ((65536 - M : ℕ) : ZMod p)).val
      = hl.val + ((65536 - M : ℕ) : ZMod p).val := ZMod.val_add_of_lt h_add_lt_p
  rw [h_add_val, hc_val]; omega

/-- **Sign-fill bound (16-way).** The SRAW sign-extended output limb `hl + (65536 - v0123)` is
`< 65536`, dispatching the 16 `c_bits` patterns to `sf_blast_per_pattern`. The `hr0`/`hr1`
obligations of `sraw_div_to_bitvec_true`'s `signExtend` keystone on the negative arm. -/
lemma sign_fill_lt {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    {cb0 cb1 cb2 cb3 v01 v012 v0123 hl : ZMod p}
    (b_cb0 : cb0 = 0 ∨ cb0 = 1) (b_cb1 : cb1 = 0 ∨ cb1 = 1)
    (b_cb2 : cb2 = 0 ∨ cb2 = 1) (b_cb3 : cb3 = 0 ∨ cb3 = 1)
    (eq_v01 : v01 = (1 + -cb0 + 1) * 2 * ((1 + -cb1) * 3 + 1))
    (eq_v012 : v012 = v01 * ((1 + -cb2) * 15 + 1))
    (eq_v0123 : v0123 = v012 * ((1 + -cb3) * 255 + 1))
    (lt_hl : hl.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                  + cb3 * 8) : ZMod p).val) :
    (hl + (((65536 : ℕ) : ZMod p) - v0123)).val < 65536 := by
  rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
    rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3 <;>
    first
    | exact sf_blast_per_pattern 0 65536 1 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        lt_hl
    | exact sf_blast_per_pattern 1 32768 2 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        lt_hl
    | exact sf_blast_per_pattern 2 16384 4 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        lt_hl
    | exact sf_blast_per_pattern 3 8192 8 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        lt_hl
    | exact sf_blast_per_pattern 4 4096 16 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        lt_hl
    | exact sf_blast_per_pattern 5 2048 32 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        lt_hl
    | exact sf_blast_per_pattern 6 1024 64 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        lt_hl
    | exact sf_blast_per_pattern 7 512 128 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        lt_hl
    | exact sf_blast_per_pattern 8 256 256 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        lt_hl
    | exact sf_blast_per_pattern 9 128 512 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        lt_hl
    | exact sf_blast_per_pattern 10 64 1024 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        lt_hl
    | exact sf_blast_per_pattern 11 32 2048 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        lt_hl
    | exact sf_blast_per_pattern 12 16 4096 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        lt_hl
    | exact sf_blast_per_pattern 13 8 8192 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        lt_hl
    | exact sf_blast_per_pattern 14 4 16384 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        lt_hl
    | exact sf_blast_per_pattern 15 2 32768 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        lt_hl

/-- **De-gated split forces zero (16-way).** When the limb-2 (or limb-3) split `hl * 65536 + ll * v0123`
is constrained to `0` — which happens on the W path, where the high-limb split asserts carry the `e14 = 0`
factor — both halves are zero (`v0123 = 2^(16-S) ≠ 0` and both in byte range). Used to drop the spurious
`ll2·v0123` term from `limb_result[1]` on SRLW/SRAW rows. -/
lemma higher_lower_zero {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    {cb0 cb1 cb2 cb3 v01 v012 v0123 hl ll : ZMod p}
    (b_cb0 : cb0 = 0 ∨ cb0 = 1) (b_cb1 : cb1 = 0 ∨ cb1 = 1)
    (b_cb2 : cb2 = 0 ∨ cb2 = 1) (b_cb3 : cb3 = 0 ∨ cb3 = 1)
    (eq_v01 : v01 = (1 + -cb0 + 1) * 2 * ((1 + -cb1) * 3 + 1))
    (eq_v012 : v012 = v01 * ((1 + -cb2) * 15 + 1))
    (eq_v0123 : v0123 = v012 * ((1 + -cb3) * 255 + 1))
    (lt_hl : hl.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                  + cb3 * 8) : ZMod p).val)
    (lt_ll : ll.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                            + cb3 * 8 : ZMod p).val)
    (h_dec : hl * 65536 + ll * v0123 = 0) :
    hl = 0 ∧ ll = 0 := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have zero_aux : ∀ (M N : ℕ), M * N = 65536 → 0 < M →
      v0123 = ((M : ℕ) : ZMod p) → hl.val < M → ll.val < N →
      hl * 65536 + ll * v0123 = 0 → hl = 0 ∧ ll = 0 := by
    intro M N h_MN h_M_pos h_v0123_eq h_hl_lt h_ll_lt h_eq
    have h_N_pos : 0 < N := by nlinarith [h_MN, h_M_pos]
    have h_M_dvd : M ∣ 65536 := ⟨N, h_MN.symm⟩
    have h_M_le : M ≤ 65536 := Nat.le_of_dvd (by omega) h_M_dvd
    have h_N_le : N ≤ 65536 := by nlinarith [h_MN, h_M_pos]
    have h_N_lt_p : N < p := by omega
    have h_v0123_val : v0123.val = M := by
      rw [h_v0123_eq]; exact ZMod.val_natCast_of_lt (by omega)
    have h_v0123_dvd : v0123.val ∣ 65536 := by rw [h_v0123_val]; exact h_M_dvd
    have h_v0123_pos : 0 < v0123.val := by rw [h_v0123_val]; exact h_M_pos
    have h_cancel := cancel_mul_65536_zero h_v0123_dvd h_v0123_pos h_eq
    rw [h_v0123_val] at h_cancel
    have h_quot_eq : 65536 / M = N := by
      rw [← h_MN]; exact Nat.mul_div_cancel_left N h_M_pos
    rw [h_quot_eq] at h_cancel
    have h_hl_N_lt : hl.val * N < 65536 := by nlinarith [h_hl_lt, h_MN, h_M_pos, h_N_pos]
    have h_hl_N_val : (hl * ((N : ℕ) : ZMod p)).val = hl.val * N := by
      rw [ZMod.val_mul_of_lt]
      · rw [ZMod.val_natCast_of_lt h_N_lt_p]
      · rw [ZMod.val_natCast_of_lt h_N_lt_p]; omega
    have h_sum_val : (hl * ((N : ℕ) : ZMod p) + ll).val = hl.val * N + ll.val := by
      rw [ZMod.val_add_of_lt]
      · rw [h_hl_N_val]
      · rw [h_hl_N_val]; omega
    have h_zero_val : (hl * ((N : ℕ) : ZMod p) + ll).val = 0 := by
      rw [h_cancel]; exact ZMod.val_zero
    rw [h_sum_val] at h_zero_val
    have h_hl_val_zero : hl.val = 0 := by
      have h_prod_zero : hl.val * N = 0 := by omega
      exact (Nat.mul_eq_zero.mp h_prod_zero).resolve_right (by omega)
    have h_ll_val_zero : ll.val = 0 := by omega
    exact ⟨(ZMod.val_eq_zero hl).mp h_hl_val_zero, (ZMod.val_eq_zero ll).mp h_ll_val_zero⟩
  have cb_aux : ∀ (_lt_hl : hl.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p)
                  + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8) : ZMod p).val)
      (_lt_ll : ll.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
      (S M N : ℕ), S ≤ 15 → M * N = 65536 → 0 < M →
      (2 : ℕ) ^ (16 - S) = M → (2 : ℕ) ^ S = N →
      v0123 = ((M : ℕ) : ZMod p) →
      (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8 : ZMod p)
        = ((S : ℕ) : ZMod p) →
      hl = 0 ∧ ll = 0 := by
    intro lt_hl' lt_ll' S M N h_S_le h_MN h_M_pos h_M_eq h_N_eq h_v0123_eq h_cb_sum_eq
    have h_S_le_16 : S ≤ 16 := by omega
    rw [inner_hi_val h_S_le_16 h_cb_sum_eq, h_M_eq] at lt_hl'
    rw [inner_val h_S_le_16 h_cb_sum_eq, h_N_eq] at lt_ll'
    exact zero_aux M N h_MN h_M_pos h_v0123_eq lt_hl' lt_ll' h_dec
  rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
    rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3 <;>
    first
    | exact cb_aux lt_hl lt_ll 0 65536 1 (by omega) (by decide) (by omega) (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
    | exact cb_aux lt_hl lt_ll 8 256 256 (by omega) (by decide) (by omega) (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
    | exact cb_aux lt_hl lt_ll 4 4096 16 (by omega) (by decide) (by omega) (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
    | exact cb_aux lt_hl lt_ll 12 16 4096 (by omega) (by decide) (by omega) (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
    | exact cb_aux lt_hl lt_ll 2 16384 4 (by omega) (by decide) (by omega) (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
    | exact cb_aux lt_hl lt_ll 10 64 1024 (by omega) (by decide) (by omega) (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
    | exact cb_aux lt_hl lt_ll 6 1024 64 (by omega) (by decide) (by omega) (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
    | exact cb_aux lt_hl lt_ll 14 4 16384 (by omega) (by decide) (by omega) (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
    | exact cb_aux lt_hl lt_ll 1 32768 2 (by omega) (by decide) (by omega) (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
    | exact cb_aux lt_hl lt_ll 9 128 512 (by omega) (by decide) (by omega) (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
    | exact cb_aux lt_hl lt_ll 5 2048 32 (by omega) (by decide) (by omega) (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
    | exact cb_aux lt_hl lt_ll 13 8 8192 (by omega) (by decide) (by omega) (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
    | exact cb_aux lt_hl lt_ll 3 8192 8 (by omega) (by decide) (by omega) (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
    | exact cb_aux lt_hl lt_ll 11 32 2048 (by omega) (by decide) (by omega) (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
    | exact cb_aux lt_hl lt_ll 7 512 128 (by omega) (by decide) (by omega) (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
    | exact cb_aux lt_hl lt_ll 15 2 32768 (by omega) (by decide) (by omega) (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring1)

/-- For `X < 2^W` and `K ∣ 2^W`, `X / K + 2^W - 2^W/K = 2^W - 1 - (2^W - 1 - X) / K`.
Used by `sra_close_su16_*_case` (W=64) and `sraw_close_su16_*_case_msb1` (W=32) to
bridge the SRL/SRLW `B/N` form to the SRA/SRAW `2^W - 1 - (2^W-1-B)/N` form coming
from `BitVec.toNat_sshiftRight_of_msb_true`. -/
lemma sra_div_identity_w (W X K : ℕ) (h_X : X < 2 ^ W) (h_K_pos : 0 < K)
    (h_K_dvd : K ∣ 2 ^ W) :
    X / K + 2 ^ W - 2 ^ W / K = 2 ^ W - 1 - (2 ^ W - 1 - X) / K := by
  obtain ⟨Q, hQ⟩ := h_K_dvd
  have h_div_2_W : (2 : ℕ) ^ W / K = Q := by
    rw [hQ]; exact Nat.mul_div_cancel_left Q h_K_pos
  have h_KQ : K * Q = 2 ^ W := hQ.symm
  set q := X / K with hq_def
  set r := X % K with hr_def
  have h_X_dec : K * q + r = X := Nat.div_add_mod X K
  have h_r_lt : r < K := Nat.mod_lt X h_K_pos
  have h_q_lt : q < Q := by
    have h_qK_le_X : q * K ≤ X := Nat.div_mul_le_self X K
    have h_X_lt_KQ : X < K * Q := by rw [← hQ]; exact h_X
    have h_qK_lt_KQ : q * K < Q * K := by
      calc q * K ≤ X := h_qK_le_X
        _ < K * Q := h_X_lt_KQ
        _ = Q * K := Nat.mul_comm _ _
    exact Nat.lt_of_mul_lt_mul_right h_qK_lt_KQ
  have h_q_succ_le_Q : q + 1 ≤ Q := h_q_lt
  have h_KQ_split : K * Q = K * q + K + K * (Q - q - 1) := by
    have h_Q_decomp : Q = (q + 1) + (Q - q - 1) := by omega
    calc K * Q = K * ((q + 1) + (Q - q - 1)) := by rw [← h_Q_decomp]
      _ = K * (q + 1) + K * (Q - q - 1) := by rw [Nat.mul_add]
      _ = K * q + K + K * (Q - q - 1) := by rw [Nat.mul_add, Nat.mul_one]
  have h_alg : 2 ^ W - 1 - X = K * (Q - q - 1) + (K - 1 - r) := by
    rw [← h_KQ]
    rw [h_KQ_split, ← h_X_dec]
    omega
  have h_div_eq : (2 ^ W - 1 - X) / K = Q - q - 1 := by
    rw [h_alg, Nat.mul_add_div h_K_pos]
    rw [Nat.div_eq_of_lt (by omega : K - 1 - r < K)]
    omega
  rw [h_div_2_W, h_div_eq]
  omega

/-- `2^S ∣ 2^W` when `S ≤ W`. -/
lemma sra_pow_dvd_w (W S : ℕ) (h_S : S ≤ W) : 2 ^ S ∣ 2 ^ W :=
  pow_dvd_pow 2 h_S

/-- `2^W / 2^S = 2^(W - S)` when `S ≤ W`. -/
lemma sra_pow_div_pow_w (W S : ℕ) (h_S : S ≤ W) : (2 : ℕ) ^ W / 2 ^ S = 2 ^ (W - S) := by
  rw [show (2 : ℕ) ^ W = 2 ^ S * 2 ^ (W - S) from by rw [← pow_add]; congr 1; omega]
  exact Nat.mul_div_cancel_left _ (by positivity)

/-- W=64 specialization of `sra_div_identity_w`. -/
lemma sra_div_identity_64 (X K : ℕ) (h_X : X < 2 ^ 64) (h_K_pos : 0 < K)
    (h_K_dvd : K ∣ 2 ^ 64) :
    X / K + 2 ^ 64 - 2 ^ 64 / K = 2 ^ 64 - 1 - (2 ^ 64 - 1 - X) / K :=
  sra_div_identity_w 64 X K h_X h_K_pos h_K_dvd

/-- W=32 specialization of `sra_div_identity_w`. -/
lemma sra_div_identity_32 (X K : ℕ) (h_X : X < 2 ^ 32) (h_K_pos : 0 < K)
    (h_K_dvd : K ∣ 2 ^ 32) :
    X / K + 2 ^ 32 - 2 ^ 32 / K = 2 ^ 32 - 1 - (2 ^ 32 - 1 - X) / K :=
  sra_div_identity_w 32 X K h_X h_K_pos h_K_dvd

/-- **Sign-fill high-limb `val`.** The SRA/SRAW sign-extended high limb `hl + (65536 - v0123)`
(with `v0123 = M = 2 ^ (16 - S)` and `hl < M`) has `val = hl.val + (65536 - M)`.

This was a byte-identical `have` block in each `sra_close_su16_*_case` /
`sraw_close_su16_*_case_msb1`; it is pure `ZMod.val`/`Nat` arithmetic (no `2 ^ 64` / `BitVec`
reduction), so hoisting it is kernel-neutral. Its conclusion is a downstream `rw` target — keep the
statement form exactly as written. -/
lemma sign_fill_limb_val {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (S : ℕ) (h_S_le : S ≤ 15) (M : ℕ) (h_M_eq : M = 2 ^ (16 - S)) (h_M_lt_p : M < p)
    {cb0 cb1 cb2 cb3 v0123 hl : ZMod p}
    (h_v0123_explicit : v0123 = ((M : ℕ) : ZMod p))
    (h_inner_eq : cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8
                  = ((S : ℕ) : ZMod p))
    (lt_hl : hl.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                  + cb3 * 8) : ZMod p).val) :
    (hl + (((65536 : ℕ) : ZMod p) - v0123)).val = hl.val + (65536 - M) := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_v_val : v0123.val = M := by
    rw [h_v0123_explicit]; exact ZMod.val_natCast_of_lt h_M_lt_p
  have h_M_le : M ≤ 65536 := by
    rw [h_M_eq, show (65536 : ℕ) = 2 ^ 16 from by decide]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have h_65536_val : ((65536 : ℕ) : ZMod p).val = 65536 := ZMod.val_natCast_of_lt (by omega)
  have h_sub_val : (((65536 : ℕ) : ZMod p) - v0123).val = 65536 - M := by
    rw [ZMod.val_sub]
    · rw [h_v_val, h_65536_val]
    · rw [h_v_val, h_65536_val]; exact h_M_le
  rw [inner_hi_val (by omega) h_inner_eq, ← h_M_eq] at lt_hl
  rw [ZMod.val_add_of_lt]
  · rw [h_sub_val]
  · rw [h_sub_val]; omega

/-- SRA byte_shift=0 (su160=1) close wrapper for the msb_b=1 arm.
Mirrors `srl_close_su16_0_case` but with the sign-extending output: the chip's
a3 = hl3 + (65536 - v0123) (correction baked in), and the conclusion is in the
signed-complement form from `BitVec.toNat_sshiftRight_of_msb_true`. -/
lemma sra_close_su16_0_case {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (S : ℕ) (h_S_le : S ≤ 15) (M N : ℕ)
    (h_MN : M * N = 65536) (h_M_pos : 0 < M) (h_M_eq : M = 2 ^ (16 - S))
    (h_N_eq : N = 2 ^ S)
    {cb0 cb1 cb2 cb3 cb4 cb5 v0123 b0 b1 b2 b3
      ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 : ZMod p}
    (h_M_lt_p : M < p) (h_v0123_explicit : v0123 = ((M : ℕ) : ZMod p))
    (h_inner_eq : cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8
                  = ((S : ℕ) : ZMod p))
    (h_total_eq : cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32
                  = ((S : ℕ) : ZMod p))
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
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  -- Get the SRL identity for the unsigned-quotient direction
  have h_srl := srl_close_su16_0_case S h_S_le M N h_MN h_M_pos h_M_eq h_N_eq
    h_M_lt_p h_v0123_explicit h_inner_eq h_total_eq
    lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
    h_b0_dec h_b1_dec h_b2_dec h_b3_dec
  -- The limb-3 sign-fill `val`, shared with the other byte-shift cases.
  have h_add3_val :=
    sign_fill_limb_val S h_S_le M h_M_eq h_M_lt_p h_v0123_explicit h_inner_eq lt_lh3
  -- cb-total val = S
  have h_total_val : (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val = S := by
    rw [h_total_eq]; exact ZMod.val_natCast_of_lt (by omega)
  -- Limb-3 bridge: SRA.toNat ≡ SRL.toNat + (65536 - M) * 2^48 (mod 2^64)
  have h_bridge : (Word.toBitVec64 #v[hl0 + ll1 * v0123, hl1 + ll2 * v0123,
                                            hl2 + ll3 * v0123,
                                            hl3 + (((65536 : ℕ) : ZMod p) - v0123)]).toNat
                = ((Word.toBitVec64 #v[hl0 + ll1 * v0123, hl1 + ll2 * v0123,
                                              hl2 + ll3 * v0123, hl3]).toNat
                   + (65536 - M) * 2 ^ 48) % 2 ^ 64 := by
    unfold Word.toBitVec64
    simp only [BitVec.toNat_ofNat, Word.toNat_def, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    rw [h_add3_val, Nat.mod_add_mod]
    congr 1; ring
  rw [h_bridge, h_srl, h_total_val]
  -- Apply sra_div_identity_64 to bridge to the signed-complement form
  have h_B_lt : (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat < 2 ^ 64 :=
    (Word.toBitVec64 #v[b0, b1, b2, b3]).isLt
  have h_2S_pos : 0 < (2 : ℕ) ^ S := Nat.two_pow_pos S
  have h_2S_dvd : (2 : ℕ) ^ S ∣ 2 ^ 64 := sra_pow_dvd_w 64 S (by omega)
  have h_div_2W : (2 : ℕ) ^ 64 / 2 ^ S = 2 ^ (64 - S) := sra_pow_div_pow_w 64 S (by omega)
  have h_sra_id := sra_div_identity_64 _ _ h_B_lt h_2S_pos h_2S_dvd
  rw [h_div_2W] at h_sra_id
  -- (65536 - M) * 2^48 = 2^64 - 2^(64 - S)
  have h_M_2_48 : M * 2 ^ 48 = 2 ^ (64 - S) := by
    rw [h_M_eq, ← Nat.pow_add]; congr 1; omega
  have h_65536_2_48 : (65536 : ℕ) * 2 ^ 48 = 2 ^ 64 := by decide
  have h_fill_eq : (65536 - M) * 2 ^ 48 = 2 ^ 64 - 2 ^ (64 - S) := by
    rw [Nat.sub_mul, h_M_2_48, h_65536_2_48]
  -- 2^(64-S) ≤ 2^64
  have h_2S_le_64 : (2 : ℕ) ^ (64 - S) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
  -- (B.toNat / 2^S + (65536 - M) * 2^48) = B.toNat/2^S + 2^64 - 2^(64-S), and that sum < 2^64
  rw [h_fill_eq]
  have h_div_lt : (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat / 2 ^ S < 2 ^ (64 - S) := by
    rw [Nat.div_lt_iff_lt_mul h_2S_pos,
        show (2 : ℕ) ^ (64 - S) * 2 ^ S = 2 ^ 64 from by rw [← Nat.pow_add]; congr 1; omega]
    exact h_B_lt
  have h_sum_lt : (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat / 2 ^ S
                  + (2 ^ 64 - 2 ^ (64 - S)) < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt h_sum_lt, ← Nat.add_sub_assoc h_2S_le_64]
  exact h_sra_id

/-- SRA byte_shift=1 (su161=1) close wrapper for the msb_b=1 arm. -/
lemma sra_close_su16_1_case {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (S : ℕ) (h_S_le : S ≤ 15) (M N : ℕ)
    (h_MN : M * N = 65536) (h_M_pos : 0 < M) (h_M_eq : M = 2 ^ (16 - S))
    (h_N_eq : N = 2 ^ S)
    {cb0 cb1 cb2 cb3 cb4 cb5 v0123 b0 b1 b2 b3
      ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 : ZMod p}
    (h_M_lt_p : M < p) (h_v0123_explicit : v0123 = ((M : ℕ) : ZMod p))
    (h_inner_eq : cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8
                  = ((S : ℕ) : ZMod p))
    (h_total_eq : cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32
                  = (((S + 16) : ℕ) : ZMod p))
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
                              hl3 + (((65536 : ℕ) : ZMod p) - v0123),
                              ((65535 : ℕ) : ZMod p)]).toNat
    = 2 ^ 64 - 1 - (2 ^ 64 - 1 - (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat)
        / 2 ^ (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_srl := srl_close_su16_1_case S h_S_le M N h_MN h_M_pos h_M_eq h_N_eq
    h_M_lt_p h_v0123_explicit h_inner_eq h_total_eq
    lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
    h_b0_dec h_b1_dec h_b2_dec h_b3_dec
  have h_65535_val : ((65535 : ℕ) : ZMod p).val = 65535 := ZMod.val_natCast_of_lt (by omega)
  have h_add3_val :=
    sign_fill_limb_val S h_S_le M h_M_eq h_M_lt_p h_v0123_explicit h_inner_eq lt_lh3
  have h_total_val : (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val
                      = S + 16 := by
    rw [h_total_eq]; exact ZMod.val_natCast_of_lt (by omega)
  -- Limb bridge: SRA.toNat ≡ SRL.toNat + ((65536-M)*2^32 + 65535*2^48) (mod 2^64).
  -- SRL output: #v[hl1+ll2*v0123, hl2+ll3*v0123, hl3, 0]
  -- SRA output: #v[hl1+ll2*v0123, hl2+ll3*v0123, hl3+(65536-v0123), 65535]
  have h_bridge : (Word.toBitVec64 #v[hl1 + ll2 * v0123, hl2 + ll3 * v0123,
                                            hl3 + (((65536 : ℕ) : ZMod p) - v0123),
                                            ((65535 : ℕ) : ZMod p)]).toNat
                = ((Word.toBitVec64 #v[hl1 + ll2 * v0123, hl2 + ll3 * v0123,
                                              hl3, 0]).toNat
                   + ((65536 - M) * 2 ^ 32 + 65535 * 2 ^ 48)) % 2 ^ 64 := by
    unfold Word.toBitVec64
    simp only [BitVec.toNat_ofNat, Word.toNat_def, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
      ZMod.val_zero]
    rw [h_add3_val, h_65535_val]; omega
  rw [h_bridge, h_srl, h_total_val]
  have h_B_lt : (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat < 2 ^ 64 :=
    (Word.toBitVec64 #v[b0, b1, b2, b3]).isLt
  have h_K_pos : 0 < (2 : ℕ) ^ (S + 16) := Nat.two_pow_pos (S + 16)
  have h_K_dvd : (2 : ℕ) ^ (S + 16) ∣ 2 ^ 64 := sra_pow_dvd_w 64 (S + 16) (by omega)
  have h_div_K : (2 : ℕ) ^ 64 / 2 ^ (S + 16) = 2 ^ (48 - S) := by
    rw [sra_pow_div_pow_w 64 (S + 16) (by omega)]; congr 1; omega
  have h_sra_id := sra_div_identity_64 _ _ h_B_lt h_K_pos h_K_dvd
  rw [h_div_K] at h_sra_id
  -- Fill identity: (65536-M)*2^32 + 65535*2^48 = 2^64 - 2^(48-S)
  have h_M_2_32 : M * 2 ^ 32 = 2 ^ (48 - S) := by
    rw [h_M_eq, ← Nat.pow_add]; congr 1; omega
  have h_65536_2_32 : (65536 : ℕ) * 2 ^ 32 = 2 ^ 48 := by decide
  have h_65535_2_48 : (65535 : ℕ) * 2 ^ 48 = 2 ^ 64 - 2 ^ 48 := by decide
  have h_fill_eq : (65536 - M) * 2 ^ 32 + 65535 * 2 ^ 48 = 2 ^ 64 - 2 ^ (48 - S) := by
    rw [Nat.sub_mul, h_M_2_32, h_65536_2_32, h_65535_2_48]
    have h_pow_le : (2 : ℕ) ^ (48 - S) ≤ 2 ^ 48 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have h_K_le_64 : (2 : ℕ) ^ (48 - S) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
  rw [h_fill_eq]
  have h_div_lt : (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat / 2 ^ (S + 16) < 2 ^ (48 - S) := by
    rw [Nat.div_lt_iff_lt_mul h_K_pos,
        show (2 : ℕ) ^ (48 - S) * 2 ^ (S + 16) = 2 ^ 64 from by rw [← Nat.pow_add]; congr 1; omega]
    exact h_B_lt
  have h_sum_lt : (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat / 2 ^ (S + 16)
                  + (2 ^ 64 - 2 ^ (48 - S)) < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt h_sum_lt, ← Nat.add_sub_assoc h_K_le_64]
  exact h_sra_id

/-- SRA byte_shift=2 (su162=1) close wrapper for the msb_b=1 arm. -/
lemma sra_close_su16_2_case {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (S : ℕ) (h_S_le : S ≤ 15) (M N : ℕ)
    (h_MN : M * N = 65536) (h_M_pos : 0 < M) (h_M_eq : M = 2 ^ (16 - S))
    (h_N_eq : N = 2 ^ S)
    {cb0 cb1 cb2 cb3 cb4 cb5 v0123 b0 b1 b2 b3
      ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 : ZMod p}
    (h_M_lt_p : M < p) (h_v0123_explicit : v0123 = ((M : ℕ) : ZMod p))
    (h_inner_eq : cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8
                  = ((S : ℕ) : ZMod p))
    (h_total_eq : cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32
                  = (((S + 32) : ℕ) : ZMod p))
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
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_srl := srl_close_su16_2_case S h_S_le M N h_MN h_M_pos h_M_eq h_N_eq
    h_M_lt_p h_v0123_explicit h_inner_eq h_total_eq
    lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
    h_b0_dec h_b1_dec h_b2_dec h_b3_dec
  have h_65535_val : ((65535 : ℕ) : ZMod p).val = 65535 := ZMod.val_natCast_of_lt (by omega)
  have h_add3_val :=
    sign_fill_limb_val S h_S_le M h_M_eq h_M_lt_p h_v0123_explicit h_inner_eq lt_lh3
  have h_total_val : (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val
                      = S + 32 := by
    rw [h_total_eq]; exact ZMod.val_natCast_of_lt (by omega)
  -- SRL output: #v[hl2+ll3*v0123, hl3, 0, 0]
  -- SRA output: #v[hl2+ll3*v0123, hl3+(65536-v0123), 65535, 65535]
  -- Fill = (65536-M)*2^16 + 65535*2^32 + 65535*2^48 = 2^64 - 2^(32-S)
  have h_bridge : (Word.toBitVec64 #v[hl2 + ll3 * v0123,
                                            hl3 + (((65536 : ℕ) : ZMod p) - v0123),
                                            ((65535 : ℕ) : ZMod p),
                                            ((65535 : ℕ) : ZMod p)]).toNat
                = ((Word.toBitVec64 #v[hl2 + ll3 * v0123, hl3, 0, 0]).toNat
                   + ((65536 - M) * 2 ^ 16 + 65535 * 2 ^ 32 + 65535 * 2 ^ 48)) % 2 ^ 64 := by
    unfold Word.toBitVec64
    simp only [BitVec.toNat_ofNat, Word.toNat_def, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
      ZMod.val_zero]
    rw [h_add3_val, h_65535_val]; omega
  rw [h_bridge, h_srl, h_total_val]
  have h_B_lt : (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat < 2 ^ 64 :=
    (Word.toBitVec64 #v[b0, b1, b2, b3]).isLt
  have h_K_pos : 0 < (2 : ℕ) ^ (S + 32) := Nat.two_pow_pos (S + 32)
  have h_K_dvd : (2 : ℕ) ^ (S + 32) ∣ 2 ^ 64 := sra_pow_dvd_w 64 (S + 32) (by omega)
  have h_div_K : (2 : ℕ) ^ 64 / 2 ^ (S + 32) = 2 ^ (32 - S) := by
    rw [sra_pow_div_pow_w 64 (S + 32) (by omega)]; congr 1; omega
  have h_sra_id := sra_div_identity_64 _ _ h_B_lt h_K_pos h_K_dvd
  rw [h_div_K] at h_sra_id
  -- Fill identity: (65536-M)*2^16 + 65535*2^32 + 65535*2^48 = 2^64 - 2^(32-S)
  have h_M_2_16 : M * 2 ^ 16 = 2 ^ (32 - S) := by
    rw [h_M_eq, ← Nat.pow_add]; congr 1; omega
  have h_65536_2_16 : (65536 : ℕ) * 2 ^ 16 = 2 ^ 32 := by decide
  have h_fill_eq : (65536 - M) * 2 ^ 16 + 65535 * 2 ^ 32 + 65535 * 2 ^ 48 = 2 ^ 64 - 2 ^ (32 - S) := by
    rw [Nat.sub_mul, h_M_2_16, h_65536_2_16]
    have h_pow_le : (2 : ℕ) ^ (32 - S) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) (by omega)
    have e1 : (65535 : ℕ) * 2 ^ 32 = 2 ^ 48 - 2 ^ 32 := by decide
    have e2 : (65535 : ℕ) * 2 ^ 48 = 2 ^ 64 - 2 ^ 48 := by decide
    omega
  have h_K_le_64 : (2 : ℕ) ^ (32 - S) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
  rw [h_fill_eq]
  have h_div_lt : (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat / 2 ^ (S + 32) < 2 ^ (32 - S) := by
    rw [Nat.div_lt_iff_lt_mul h_K_pos,
        show (2 : ℕ) ^ (32 - S) * 2 ^ (S + 32) = 2 ^ 64 from by rw [← Nat.pow_add]; congr 1; omega]
    exact h_B_lt
  have h_sum_lt : (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat / 2 ^ (S + 32)
                  + (2 ^ 64 - 2 ^ (32 - S)) < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt h_sum_lt, ← Nat.add_sub_assoc h_K_le_64]
  exact h_sra_id

/-- SRA byte_shift=3 (su163=1) close wrapper for the msb_b=1 arm. -/
lemma sra_close_su16_3_case {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (S : ℕ) (h_S_le : S ≤ 15) (M N : ℕ)
    (h_MN : M * N = 65536) (h_M_pos : 0 < M) (h_M_eq : M = 2 ^ (16 - S))
    (h_N_eq : N = 2 ^ S)
    {cb0 cb1 cb2 cb3 cb4 cb5 v0123 b0 b1 b2 b3
      ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 : ZMod p}
    (h_M_lt_p : M < p) (h_v0123_explicit : v0123 = ((M : ℕ) : ZMod p))
    (h_inner_eq : cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8
                  = ((S : ℕ) : ZMod p))
    (h_total_eq : cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32
                  = (((S + 48) : ℕ) : ZMod p))
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
                              ((65535 : ℕ) : ZMod p), ((65535 : ℕ) : ZMod p),
                              ((65535 : ℕ) : ZMod p)]).toNat
    = 2 ^ 64 - 1 - (2 ^ 64 - 1 - (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat)
        / 2 ^ (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_srl := srl_close_su16_3_case S h_S_le M N h_MN h_M_pos h_M_eq h_N_eq
    h_M_lt_p h_v0123_explicit h_inner_eq h_total_eq
    lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
    h_b0_dec h_b1_dec h_b2_dec h_b3_dec
  have h_65535_val : ((65535 : ℕ) : ZMod p).val = 65535 := ZMod.val_natCast_of_lt (by omega)
  have h_add3_val :=
    sign_fill_limb_val S h_S_le M h_M_eq h_M_lt_p h_v0123_explicit h_inner_eq lt_lh3
  have h_total_val : (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val
                      = S + 48 := by
    rw [h_total_eq]; exact ZMod.val_natCast_of_lt (by omega)
  -- SRL output: #v[hl3, 0, 0, 0]
  -- SRA output: #v[hl3+(65536-v0123), 65535, 65535, 65535]
  -- Fill = (65536-M) + 65535*2^16 + 65535*2^32 + 65535*2^48 = 2^64 - 2^(16-S)
  have h_bridge : (Word.toBitVec64 #v[hl3 + (((65536 : ℕ) : ZMod p) - v0123),
                                            ((65535 : ℕ) : ZMod p),
                                            ((65535 : ℕ) : ZMod p),
                                            ((65535 : ℕ) : ZMod p)]).toNat
                = ((Word.toBitVec64 #v[hl3, 0, 0, 0]).toNat
                   + ((65536 - M) + 65535 * 2 ^ 16 + 65535 * 2 ^ 32 + 65535 * 2 ^ 48)) % 2 ^ 64 := by
    unfold Word.toBitVec64
    simp only [BitVec.toNat_ofNat, Word.toNat_def, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
      ZMod.val_zero]
    rw [h_add3_val, h_65535_val]; omega
  rw [h_bridge, h_srl, h_total_val]
  have h_B_lt : (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat < 2 ^ 64 :=
    (Word.toBitVec64 #v[b0, b1, b2, b3]).isLt
  have h_K_pos : 0 < (2 : ℕ) ^ (S + 48) := Nat.two_pow_pos (S + 48)
  have h_K_dvd : (2 : ℕ) ^ (S + 48) ∣ 2 ^ 64 := sra_pow_dvd_w 64 (S + 48) (by omega)
  have h_div_K : (2 : ℕ) ^ 64 / 2 ^ (S + 48) = 2 ^ (16 - S) := by
    rw [sra_pow_div_pow_w 64 (S + 48) (by omega)]; congr 1; omega
  have h_sra_id := sra_div_identity_64 _ _ h_B_lt h_K_pos h_K_dvd
  rw [h_div_K] at h_sra_id
  -- Fill identity: (65536-M) + 65535*2^16 + 65535*2^32 + 65535*2^48 = 2^64 - 2^(16-S)
  have h_fill_eq : (65536 - M) + 65535 * 2 ^ 16 + 65535 * 2 ^ 32 + 65535 * 2 ^ 48
                  = 2 ^ 64 - 2 ^ (16 - S) := by
    rw [h_M_eq]
    have h_pow_le : (2 : ℕ) ^ (16 - S) ≤ 65536 := by
      rw [show (65536 : ℕ) = 2 ^ 16 from by decide]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have e1 : (65535 : ℕ) * 2 ^ 16 = 2 ^ 32 - 2 ^ 16 := by decide
    have e2 : (65535 : ℕ) * 2 ^ 32 = 2 ^ 48 - 2 ^ 32 := by decide
    have e3 : (65535 : ℕ) * 2 ^ 48 = 2 ^ 64 - 2 ^ 48 := by decide
    omega
  have h_K_le_64 : (2 : ℕ) ^ (16 - S) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
  rw [h_fill_eq]
  have h_div_lt : (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat / 2 ^ (S + 48) < 2 ^ (16 - S) := by
    rw [Nat.div_lt_iff_lt_mul h_K_pos,
        show (2 : ℕ) ^ (16 - S) * 2 ^ (S + 48) = 2 ^ 64 from by rw [← Nat.pow_add]; congr 1; omega]
    exact h_B_lt
  have h_sum_lt : (Word.toBitVec64 #v[b0, b1, b2, b3]).toNat / 2 ^ (S + 48)
                  + (2 ^ 64 - 2 ^ (16 - S)) < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt h_sum_lt, ← Nat.add_sub_assoc h_K_le_64]
  exact h_sra_id

/-! ## SRLW / SRAW chain (low-32 word variants): a 32-bit `HWord` shift, sign-extended to 64. -/

/-- A 32-bit value as two little-endian 16-bit limbs (SP1's `HWord`), for the low-32 word shifts. -/
@[reducible] def HWord (T : Type) := Vector T 2
namespace HWord
/-- Little-endian reassembly of a half-word to `ℕ`. -/
def toNat {p : ℕ} [NeZero p] (w : HWord (ZMod p)) : ℕ := w[0].val + w[1].val * 2 ^ 16
/-- The 32-bit value of the half-word. -/
def toBitVec32 {p : ℕ} [NeZero p] (w : HWord (ZMod p)) : BitVec 32 := BitVec.ofNat 32 (toNat w)
end HWord

lemma srlw_within_byte_shift {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (M N : ℕ) (h_MN : M * N = 65536) (h_M_pos : 0 < M)
    {b0 b1 ll0 ll1 hl0 hl1 v0123 : ZMod p}
    (h_v_val : v0123.val = M)
    (lt_ll0 : ll0.val < N) (lt_ll1 : ll1.val < N)
    (lt_lh0 : hl0.val < M) (lt_lh1 : hl1.val < M)
    (h_b0 : b0 = hl0 * ((N : ℕ) : ZMod p) + ll0)
    (h_b1 : b1 = hl1 * ((N : ℕ) : ZMod p) + ll1) :
    (HWord.toBitVec32 #v[hl0 + ll1 * v0123, hl1]).toNat
    = (HWord.toBitVec32 #v[b0, b1]).toNat / N := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_N_lt_p : N < p := by nlinarith [h_MN]
  have h_N_val : ((N : ℕ) : ZMod p).val = N := ZMod.val_natCast_of_lt h_N_lt_p
  have h_NM : N * M = 65536 := by linarith [h_MN, Nat.mul_comm M N]
  have h_N_pos : 0 < N := by nlinarith [h_MN, h_M_pos]
  -- val_mul bridges
  have h_ll1_mul : (ll1 * v0123).val = ll1.val * M := by
    rw [ZMod.val_mul_of_lt, h_v_val]; rw [h_v_val]; nlinarith [lt_ll1, h_MN]
  have h_hl0_mul : (hl0 * ((N : ℕ) : ZMod p)).val = hl0.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh0, h_MN, h_NM]
  have h_hl1_mul : (hl1 * ((N : ℕ) : ZMod p)).val = hl1.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh1, h_MN, h_NM]
  -- b_j.val = hl_j.val * N + ll_j.val
  have h_b0_val : b0.val = hl0.val * N + ll0.val := by
    rw [h_b0, ZMod.val_add_of_lt]
    · rw [h_hl0_mul]
    · rw [h_hl0_mul]; nlinarith [lt_ll0, lt_lh0, h_MN, h_NM]
  have h_b1_val : b1.val = hl1.val * N + ll1.val := by
    rw [h_b1, ZMod.val_add_of_lt]
    · rw [h_hl1_mul]
    · rw [h_hl1_mul]; nlinarith [lt_ll1, lt_lh1, h_MN, h_NM]
  have h_compose0_val : (hl0 + ll1 * v0123).val = hl0.val + ll1.val * M := by
    rw [ZMod.val_add_of_lt]
    · rw [h_ll1_mul]
    · rw [h_ll1_mul]; nlinarith [lt_lh0, lt_ll1, h_MN]
  unfold HWord.toBitVec32
  simp only [BitVec.toNat_ofNat, HWord.toNat, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  rw [h_compose0_val, h_b0_val, h_b1_val]
  -- Per-byte bounds.
  have h_b0_lt : hl0.val * N + ll0.val < 65536 := by nlinarith [lt_lh0, lt_ll0, h_MN]
  have h_b1_lt : hl1.val * N + ll1.val < 65536 := by nlinarith [lt_lh1, lt_ll1, h_MN]
  have h_lhs0_lt : hl0.val + ll1.val * M < 65536 := by nlinarith [lt_lh0, lt_ll1, h_MN]
  have h_lhs1_lt : hl1.val < 65536 := by nlinarith [lt_lh1, h_MN]
  -- Both sides fit in 2^32.
  have h_B_lt : (hl0.val * N + ll0.val) + (hl1.val * N + ll1.val) * 2 ^ 16 < 2 ^ 32 := by
    omega
  have h_L_lt : (hl0.val + ll1.val * M) + hl1.val * 2 ^ 16 < 2 ^ 32 := by omega
  -- Key Nat identity: N * L + ll0 = B.
  have h_key : N * ((hl0.val + ll1.val * M) + hl1.val * 2 ^ 16) + ll0.val
            = (hl0.val * N + ll0.val) + (hl1.val * N + ll1.val) * 2 ^ 16 := by
    linear_combination ll1.val * h_MN
  rw [Nat.mod_eq_of_lt h_L_lt, Nat.mod_eq_of_lt h_B_lt, ← h_key]
  rw [Nat.add_comm (N * _) ll0.val, Nat.mul_comm N _,
      Nat.add_mul_div_right _ _ h_N_pos, Nat.div_eq_of_lt lt_ll0, Nat.zero_add]

/-- 32-bit HWord byte_shift=1 variant. Total shift = S+16, divisor = N * 2^16.
The output `[hl1, 0]` is `b / (N * 2^16) = hl1` when the b1 decomposition holds. -/
lemma srlw_within_byte_shift_1 {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (M N : ℕ) (h_MN : M * N = 65536) (h_M_pos : 0 < M)
    {b0 b1 ll0 ll1 hl0 hl1 v0123 : ZMod p}
    (h_v_val : v0123.val = M)
    (lt_ll0 : ll0.val < N) (lt_ll1 : ll1.val < N)
    (lt_lh0 : hl0.val < M) (lt_lh1 : hl1.val < M)
    (h_b0 : b0 = hl0 * ((N : ℕ) : ZMod p) + ll0)
    (h_b1 : b1 = hl1 * ((N : ℕ) : ZMod p) + ll1) :
    (HWord.toBitVec32 #v[hl1, 0]).toNat
    = (HWord.toBitVec32 #v[b0, b1]).toNat / (N * 2 ^ 16) := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_N_lt_p : N < p := by nlinarith [h_MN]
  have h_N_val : ((N : ℕ) : ZMod p).val = N := ZMod.val_natCast_of_lt h_N_lt_p
  have h_NM : N * M = 65536 := by linarith [h_MN, Nat.mul_comm M N]
  have h_N_pos : 0 < N := by nlinarith [h_MN, h_M_pos]
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
    zero_mul, add_zero]
  rw [h_b0_val, h_b1_val]
  have h_b0_lt : hl0.val * N + ll0.val < 65536 := by nlinarith [lt_lh0, lt_ll0, h_MN]
  have h_b1_lt : hl1.val * N + ll1.val < 65536 := by nlinarith [lt_lh1, lt_ll1, h_MN]
  have h_hl1_lt : hl1.val < 65536 := by nlinarith [lt_lh1, h_MN]
  have h_B_lt : (hl0.val * N + ll0.val) + (hl1.val * N + ll1.val) * 2 ^ 16 < 2 ^ 32 := by
    omega
  have h_L_lt : hl1.val < 2 ^ 32 := by omega
  have h_rem_lt : (hl0.val * N + ll0.val) + 2 ^ 16 * ll1.val < N * 2 ^ 16 := by
    nlinarith [lt_lh0, lt_ll0, lt_ll1, h_MN, h_NM, h_N_pos]
  have h_NM16_pos : 0 < N * 2 ^ 16 := Nat.mul_pos h_N_pos (by omega)
  -- Key Nat identity: (N * 2^16) * hl1 + (b0 + 2^16 * ll1) = B.
  have h_key : (N * 2 ^ 16) * hl1.val + ((hl0.val * N + ll0.val) + 2 ^ 16 * ll1.val)
            = (hl0.val * N + ll0.val) + (hl1.val * N + ll1.val) * 2 ^ 16 := by
    ring
  rw [Nat.mod_eq_of_lt h_L_lt, Nat.mod_eq_of_lt h_B_lt, ← h_key]
  rw [Nat.add_comm ((N * 2 ^ 16) * _) _, Nat.mul_comm (N * 2 ^ 16) _,
      Nat.add_mul_div_right _ _ h_NM16_pos, Nat.div_eq_of_lt h_rem_lt, Nat.zero_add]

/-- Wrapper for `spec.srlw`/`spec.srliw`'s `cb4=0` byte-shift case
(byte_shift=0, S ≤ 15). The shift amount is the 5-bit sum `cb0+cb1*2+cb2*4+cb3*8+cb4*16`
(no cb5 because SRLW shift is 5-bit). Combines `cancel_mul_65536`, bound
normalization, and the 32-bit shift identity. -/
lemma srlw_close_su16_0_case {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (S : ℕ) (h_S_le : S ≤ 15) (M N : ℕ)
    (h_MN : M * N = 65536) (h_M_pos : 0 < M) (h_M_eq : M = 2 ^ (16 - S))
    (h_N_eq : N = 2 ^ S)
    {cb0 cb1 cb2 cb3 cb4 v0123 b0 b1 ll0 ll1 hl0 hl1 : ZMod p}
    (h_M_lt_p : M < p) (h_v0123_explicit : v0123 = ((M : ℕ) : ZMod p))
    (h_inner_eq : cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8
                  = ((S : ℕ) : ZMod p))
    (h_total_eq : cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16
                  = ((S : ℕ) : ZMod p))
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
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_v_val : v0123.val = M := by
    rw [h_v0123_explicit]; exact ZMod.val_natCast_of_lt h_M_lt_p
  have h_inner_val := inner_val (by omega) h_inner_eq
  have h_inner_hi_val := inner_hi_val (by omega) h_inner_eq
  rw [h_inner_val] at lt_ll0 lt_ll1
  rw [h_inner_hi_val] at lt_lh0 lt_lh1
  have h_total_val : (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16).val = S := by
    rw [h_total_eq]; exact ZMod.val_natCast_of_lt (by omega)
  rw [h_total_val]
  have hdvd : v0123.val ∣ 65536 := by rw [h_v_val]; exact ⟨N, h_MN.symm⟩
  have hpos : 0 < v0123.val := by rw [h_v_val]; exact h_M_pos
  have h_b0' := cancel_mul_65536 hdvd hpos h_b0_dec
  have h_b1' := cancel_mul_65536 hdvd hpos h_b1_dec
  rw [h_v_val] at h_b0' h_b1'
  rw [show (2 : ℕ) ^ S = N from h_N_eq.symm]
  have h_div_eq : (65536 : ℕ) / M = N := by
    rw [← h_MN]; exact Nat.mul_div_cancel_left N h_M_pos
  rw [h_div_eq] at h_b0' h_b1'
  have h_lt_ll0 : ll0.val < N := by rw [h_N_eq]; exact lt_ll0
  have h_lt_ll1 : ll1.val < N := by rw [h_N_eq]; exact lt_ll1
  have h_lt_lh0 : hl0.val < M := by rw [h_M_eq]; exact lt_lh0
  have h_lt_lh1 : hl1.val < M := by rw [h_M_eq]; exact lt_lh1
  exact srlw_within_byte_shift M N h_MN h_M_pos h_v_val
    h_lt_ll0 h_lt_ll1 h_lt_lh0 h_lt_lh1 h_b0' h_b1'

/-- Wrapper for `spec.srlw`/`spec.srliw`'s `cb4=1` byte-shift case
(byte_shift=1, S ∈ [16, 31]). The shift amount is `S + 16`; the 32-bit output is
`[hl1, 0]` because the high byte slides into bit position 0. -/
lemma srlw_close_su16_1_case {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (S : ℕ) (h_S_le : S ≤ 15) (M N : ℕ)
    (h_MN : M * N = 65536) (h_M_pos : 0 < M) (h_M_eq : M = 2 ^ (16 - S))
    (h_N_eq : N = 2 ^ S)
    {cb0 cb1 cb2 cb3 cb4 v0123 b0 b1 ll0 ll1 hl0 hl1 : ZMod p}
    (h_M_lt_p : M < p) (h_v0123_explicit : v0123 = ((M : ℕ) : ZMod p))
    (h_inner_eq : cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8
                  = ((S : ℕ) : ZMod p))
    (h_total_eq : cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16
                  = (((S + 16) : ℕ) : ZMod p))
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
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_v_val : v0123.val = M := by
    rw [h_v0123_explicit]; exact ZMod.val_natCast_of_lt h_M_lt_p
  have h_inner_val := inner_val (by omega) h_inner_eq
  have h_inner_hi_val := inner_hi_val (by omega) h_inner_eq
  rw [h_inner_val] at lt_ll0 lt_ll1
  rw [h_inner_hi_val] at lt_lh0 lt_lh1
  have h_total_val : (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16).val
                      = S + 16 := by
    rw [h_total_eq]; exact ZMod.val_natCast_of_lt (by omega)
  rw [h_total_val]
  have hdvd : v0123.val ∣ 65536 := by rw [h_v_val]; exact ⟨N, h_MN.symm⟩
  have hpos : 0 < v0123.val := by rw [h_v_val]; exact h_M_pos
  have h_b0' := cancel_mul_65536 hdvd hpos h_b0_dec
  have h_b1' := cancel_mul_65536 hdvd hpos h_b1_dec
  rw [h_v_val] at h_b0' h_b1'
  rw [show (2 : ℕ) ^ (S + 16) = N * 2 ^ 16 from by rw [pow_add, h_N_eq]]
  have h_div_eq : (65536 : ℕ) / M = N := by
    rw [← h_MN]; exact Nat.mul_div_cancel_left N h_M_pos
  rw [h_div_eq] at h_b0' h_b1'
  have h_lt_ll0 : ll0.val < N := by rw [h_N_eq]; exact lt_ll0
  have h_lt_ll1 : ll1.val < N := by rw [h_N_eq]; exact lt_ll1
  have h_lt_lh0 : hl0.val < M := by rw [h_M_eq]; exact lt_lh0
  have h_lt_lh1 : hl1.val < M := by rw [h_M_eq]; exact lt_lh1
  exact srlw_within_byte_shift_1 M N h_MN h_M_pos h_v_val
    h_lt_ll0 h_lt_ll1 h_lt_lh0 h_lt_lh1 h_b0' h_b1'

/-- SRAW byte_shift=0 (su160=1) close wrapper for the msb_b=1 arm. 32-bit version
of `sra_close_su16_0_case`. The chip's a1 = hl1 + (65536 - v0123) (sign-extension
correction), and the conclusion uses the signed-complement form from
`BitVec.toNat_sshiftRight_of_msb_true` at width 32. -/
lemma sraw_close_su16_0_case_msb1 {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (S : ℕ) (h_S_le : S ≤ 15) (M N : ℕ)
    (h_MN : M * N = 65536) (h_M_pos : 0 < M) (h_M_eq : M = 2 ^ (16 - S))
    (h_N_eq : N = 2 ^ S)
    {cb0 cb1 cb2 cb3 cb4 v0123 b0 b1 ll0 ll1 hl0 hl1 : ZMod p}
    (h_M_lt_p : M < p) (h_v0123_explicit : v0123 = ((M : ℕ) : ZMod p))
    (h_inner_eq : cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8
                  = ((S : ℕ) : ZMod p))
    (h_total_eq : cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16
                  = ((S : ℕ) : ZMod p))
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
    (HWord.toBitVec32 #v[hl0 + ll1 * v0123,
                                hl1 + (((65536 : ℕ) : ZMod p) - v0123)]).toNat
    = 2 ^ 32 - 1 - (2 ^ 32 - 1 - (HWord.toBitVec32 #v[b0, b1]).toNat)
        / 2 ^ (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16).val := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_srlw := srlw_close_su16_0_case S h_S_le M N h_MN h_M_pos h_M_eq h_N_eq
    h_M_lt_p h_v0123_explicit h_inner_eq h_total_eq
    lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
  have h_add1_val :=
    sign_fill_limb_val S h_S_le M h_M_eq h_M_lt_p h_v0123_explicit h_inner_eq lt_lh1
  have h_total_val : (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16).val = S := by
    rw [h_total_eq]; exact ZMod.val_natCast_of_lt (by omega)
  -- Limb-1 bridge: SRAW.toNat ≡ SRLW.toNat + (65536 - M) * 2^16 (mod 2^32).
  have h_bridge : (HWord.toBitVec32 #v[hl0 + ll1 * v0123,
                                              hl1 + (((65536 : ℕ) : ZMod p) - v0123)]).toNat
                = ((HWord.toBitVec32 #v[hl0 + ll1 * v0123, hl1]).toNat
                   + (65536 - M) * 2 ^ 16) % 2 ^ 32 := by
    unfold HWord.toBitVec32
    simp only [BitVec.toNat_ofNat, HWord.toNat, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    rw [h_add1_val]; omega
  rw [h_bridge, h_srlw, h_total_val]
  have h_B_lt : (HWord.toBitVec32 #v[b0, b1]).toNat < 2 ^ 32 :=
    (HWord.toBitVec32 #v[b0, b1]).isLt
  have h_2S_pos : 0 < (2 : ℕ) ^ S := Nat.two_pow_pos S
  have h_2S_dvd : (2 : ℕ) ^ S ∣ 2 ^ 32 := sra_pow_dvd_w 32 S (by omega)
  have h_div_2W : (2 : ℕ) ^ 32 / 2 ^ S = 2 ^ (32 - S) := sra_pow_div_pow_w 32 S (by omega)
  have h_sra_id := sra_div_identity_32 _ _ h_B_lt h_2S_pos h_2S_dvd
  rw [h_div_2W] at h_sra_id
  -- Fill: (65536 - M) * 2^16 = 2^32 - 2^(32 - S)
  have h_M_2_16 : M * 2 ^ 16 = 2 ^ (32 - S) := by
    rw [h_M_eq, ← Nat.pow_add]; congr 1; omega
  have h_65536_2_16 : (65536 : ℕ) * 2 ^ 16 = 2 ^ 32 := by decide
  have h_fill_eq : (65536 - M) * 2 ^ 16 = 2 ^ 32 - 2 ^ (32 - S) := by
    rw [Nat.sub_mul, h_M_2_16, h_65536_2_16]
  have h_2S_le_32 : (2 : ℕ) ^ (32 - S) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) (by omega)
  rw [h_fill_eq]
  have h_div_lt : (HWord.toBitVec32 #v[b0, b1]).toNat / 2 ^ S < 2 ^ (32 - S) := by
    rw [Nat.div_lt_iff_lt_mul h_2S_pos,
        show (2 : ℕ) ^ (32 - S) * 2 ^ S = 2 ^ 32 from by rw [← Nat.pow_add]; congr 1; omega]
    exact h_B_lt
  have h_sum_lt : (HWord.toBitVec32 #v[b0, b1]).toNat / 2 ^ S
                  + (2 ^ 32 - 2 ^ (32 - S)) < 2 ^ 32 := by omega
  rw [Nat.mod_eq_of_lt h_sum_lt, ← Nat.add_sub_assoc h_2S_le_32]
  exact h_sra_id

/-- SRAW byte_shift=1 (su161=1) close wrapper for the msb_b=1 arm. -/
lemma sraw_close_su16_1_case_msb1 {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (S : ℕ) (h_S_le : S ≤ 15) (M N : ℕ)
    (h_MN : M * N = 65536) (h_M_pos : 0 < M) (h_M_eq : M = 2 ^ (16 - S))
    (h_N_eq : N = 2 ^ S)
    {cb0 cb1 cb2 cb3 cb4 v0123 b0 b1 ll0 ll1 hl0 hl1 : ZMod p}
    (h_M_lt_p : M < p) (h_v0123_explicit : v0123 = ((M : ℕ) : ZMod p))
    (h_inner_eq : cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8
                  = ((S : ℕ) : ZMod p))
    (h_total_eq : cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16
                  = (((S + 16) : ℕ) : ZMod p))
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
    (HWord.toBitVec32 #v[hl1 + (((65536 : ℕ) : ZMod p) - v0123),
                                ((65535 : ℕ) : ZMod p)]).toNat
    = 2 ^ 32 - 1 - (2 ^ 32 - 1 - (HWord.toBitVec32 #v[b0, b1]).toNat)
        / 2 ^ (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16).val := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_srlw := srlw_close_su16_1_case S h_S_le M N h_MN h_M_pos h_M_eq h_N_eq
    h_M_lt_p h_v0123_explicit h_inner_eq h_total_eq
    lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
  have h_65535_val : ((65535 : ℕ) : ZMod p).val = 65535 := ZMod.val_natCast_of_lt (by omega)
  have h_add1_val :=
    sign_fill_limb_val S h_S_le M h_M_eq h_M_lt_p h_v0123_explicit h_inner_eq lt_lh1
  have h_total_val : (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16).val = S + 16 := by
    rw [h_total_eq]; exact ZMod.val_natCast_of_lt (by omega)
  -- SRLW output: #v[hl1, 0]. SRAW output: #v[hl1 + (65536-v0123), 65535].
  -- Fill = (65536 - M) + 65535 * 2^16 = 2^32 - 2^(16 - S).
  have h_bridge : (HWord.toBitVec32 #v[hl1 + (((65536 : ℕ) : ZMod p) - v0123),
                                              ((65535 : ℕ) : ZMod p)]).toNat
                = ((HWord.toBitVec32 #v[hl1, 0]).toNat
                   + ((65536 - M) + 65535 * 2 ^ 16)) % 2 ^ 32 := by
    unfold HWord.toBitVec32
    simp only [BitVec.toNat_ofNat, HWord.toNat, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
      ZMod.val_zero]
    rw [h_add1_val, h_65535_val]; omega
  rw [h_bridge, h_srlw, h_total_val]
  have h_B_lt : (HWord.toBitVec32 #v[b0, b1]).toNat < 2 ^ 32 :=
    (HWord.toBitVec32 #v[b0, b1]).isLt
  have h_K_pos : 0 < (2 : ℕ) ^ (S + 16) := Nat.two_pow_pos (S + 16)
  have h_K_dvd : (2 : ℕ) ^ (S + 16) ∣ 2 ^ 32 := sra_pow_dvd_w 32 (S + 16) (by omega)
  have h_div_K : (2 : ℕ) ^ 32 / 2 ^ (S + 16) = 2 ^ (16 - S) := by
    rw [sra_pow_div_pow_w 32 (S + 16) (by omega)]; congr 1; omega
  have h_sra_id := sra_div_identity_32 _ _ h_B_lt h_K_pos h_K_dvd
  rw [h_div_K] at h_sra_id
  -- Fill identity: (65536 - M) + 65535 * 2^16 = 2^32 - 2^(16 - S)
  have h_fill_eq : (65536 - M) + 65535 * 2 ^ 16 = 2 ^ 32 - 2 ^ (16 - S) := by
    rw [h_M_eq]
    have h_pow_le : (2 : ℕ) ^ (16 - S) ≤ 65536 := by
      rw [show (65536 : ℕ) = 2 ^ 16 from by decide]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have e1 : (65535 : ℕ) * 2 ^ 16 = 2 ^ 32 - 2 ^ 16 := by decide
    omega
  have h_K_le_32 : (2 : ℕ) ^ (16 - S) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) (by omega)
  rw [h_fill_eq]
  have h_div_lt : (HWord.toBitVec32 #v[b0, b1]).toNat / 2 ^ (S + 16) < 2 ^ (16 - S) := by
    rw [Nat.div_lt_iff_lt_mul h_K_pos,
        show (2 : ℕ) ^ (16 - S) * 2 ^ (S + 16) = 2 ^ 32 from by rw [← Nat.pow_add]; congr 1; omega]
    exact h_B_lt
  have h_sum_lt : (HWord.toBitVec32 #v[b0, b1]).toNat / 2 ^ (S + 16)
                  + (2 ^ 32 - 2 ^ (16 - S)) < 2 ^ 32 := by omega
  rw [Nat.mod_eq_of_lt h_sum_lt, ← Nat.add_sub_assoc h_K_le_32]
  exact h_sra_id

end SP1Clean.ShiftRightMath
