import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader
import SP1Chips.ShiftLeft.Constraints

namespace ShiftLeft

set_option linter.style.setOption false
-- Imbalanced goal tree: proof applies tactics per-focused-case.
set_option linter.style.multiGoal false
set_option maxHeartbeats 100000000

variable (Main : Vector (Fin KB) 65)
variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

section field_arithmetic

/-- Polymorphic version of `is_mod_64`. From `((c0 - m) * 64⁻¹).val < 1024`, conclude c0 ≡ m (mod 64).
Cleaner than Fin KB because no wrap to undo. -/
lemma is_mod_64_poly {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    {c0 m : ZMod p}
    (h_m_lt : m.val < 64) (_h_c0_lt : c0.val < 65536)
    (h_diff : ((c0 - m) * (64 : ZMod p)⁻¹).val < 1024) :
    c0.val % 64 = m.val := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  -- Let k = (c0 - m) * 64⁻¹. Then k.val < 1024.
  set k := (c0 - m) * (64 : ZMod p)⁻¹ with k_def
  have h_k_lt : k.val < 1024 := h_diff
  -- Multiply both sides by 64: c0 - m = k * 64, so c0 = m + k * 64.
  have h_64_ne : (64 : ZMod p) ≠ 0 := val_64_ne_zero
  have h_diff_eq : c0 - m = k * 64 := by
    rw [k_def]
    field_simp
  have h_c0_eq : c0 = m + k * 64 := by linear_combination h_diff_eq
  -- (m + k * 64).val = m.val + k.val * 64 (no wrap since m.val + k.val * 64 < 64 + 1024 * 64 = 65600 < p)
  have h_k64_val : (k * 64).val = k.val * 64 := by
    rw [show (64 : ZMod p) = ((64 : ℕ) : ZMod p) from by push_cast; rfl]
    rw [ZMod.val_mul_of_lt]
    · rw [show ((64 : ℕ) : ZMod p).val = 64 from val_64_zmod_p]
    · rw [show ((64 : ℕ) : ZMod p).val = 64 from val_64_zmod_p]
      -- k.val < 1024, so k.val * 64 < 65536 < p
      have h_k_lt' : k.val < 1024 := h_k_lt
      have : k.val * 64 < 1024 * 64 := by
        exact Nat.mul_lt_mul_of_lt_of_le h_k_lt' (le_refl 64) (by omega)
      omega
  have h_c0_val : c0.val = m.val + k.val * 64 := by
    have : c0.val = (m + k * 64).val := by rw [h_c0_eq]
    rw [this, ZMod.val_add_of_lt]
    · rw [h_k64_val]
    · rw [h_k64_val]
      omega
  rw [h_c0_val]
  omega

/-- Polymorphic version of `cancel_mul_65536`. Cleaner than Fin KB because `ZMod p` (`p > 2^17`)
has no wrap to undo for products up to 65536^2 < 2^32 < p. -/
lemma cancel_mul_65536_poly {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    {a b c x : ZMod p}
    (h_x_dvd : x.val ∣ 65536) (h_x_pos : 0 < x.val) :
    a * x = b * 65536 + c * x → a = b * (((65536 / x.val : ℕ) : ZMod p)) + c := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  intro h_eq
  -- Let z = 65536 / x.val. Then x.val * z = 65536, so as ZMod p elements: x * (z : ZMod p) = 65536.
  set z : ℕ := 65536 / x.val with z_def
  have h_x_le : x.val ≤ 65536 := Nat.le_of_dvd (by omega) h_x_dvd
  have h_z_pos : 0 < z := Nat.div_pos h_x_le h_x_pos
  have h_z_lt : z ≤ 65536 := by
    rw [z_def]; exact Nat.div_le_self _ _
  have h_xz : x.val * z = 65536 := by
    rw [z_def, Nat.mul_div_cancel' h_x_dvd]
  -- Cast x.val * z = 65536 to ZMod p.
  have h_xz_zmod : x * ((z : ℕ) : ZMod p) = 65536 := by
    have : ((x.val : ZMod p)) * ((z : ℕ) : ZMod p) = ((x.val * z : ℕ) : ZMod p) := by push_cast; ring
    rw [ZMod.natCast_zmod_val] at this
    rw [this, h_xz]
    push_cast; rfl
  -- Rewrite the hypothesis using h_xz_zmod: b * 65536 = b * (x * z) = (b * z) * x.
  have h_eq2 : a * x = (b * ((z : ℕ) : ZMod p) + c) * x := by
    rw [← h_xz_zmod] at h_eq
    linear_combination h_eq
  -- Need x ≠ 0 in ZMod p to cancel.
  have h_x_ne : x ≠ 0 := by
    intro h
    have : x.val = 0 := by rw [h]; exact ZMod.val_zero
    omega
  -- Cancel x.
  exact mul_right_cancel₀ h_x_ne h_eq2

/-- Helper for the within-byte-shift identity in spec.sll_poly. Parameterizes the 16-way
cb0..cb3 case split: for each combination, the witness `v0123 : ZMod p` has `v0123.val = M`
(some power of 2 in [1, 65536]) and `N = 65536 / M`. Given the four per-limb decomposition
constraints `b_j = hl_j * N + ll_j` and the appropriate bounds, this concludes the
shift identity at the toNat level. Saves ~85 lines of mechanical val computations per sub-case. -/
lemma sll_within_byte_shift_poly {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
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
    (Word.toBitVec64_poly #v[ll0 * v0123, ll1 * v0123 + hl0, ll2 * v0123 + hl1,
                              ll3 * v0123 + hl2]).toNat
    = (Word.toBitVec64_poly #v[b0, b1, b2, b3]).toNat * M % 2 ^ 64 := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_N_lt_p : N < p := by nlinarith [h_MN]
  have h_N_val : ((N : ℕ) : ZMod p).val = N := ZMod.val_natCast_of_lt h_N_lt_p
  have h_NM : N * M = 65536 := by linarith [h_MN, Nat.mul_comm M N]
  -- val_mul bridges for ll_j * v0123
  have h_ll0_mul : (ll0 * v0123).val = ll0.val * M := by
    rw [ZMod.val_mul_of_lt, h_v_val]; rw [h_v_val]; nlinarith [lt_ll0, h_MN]
  have h_ll1_mul : (ll1 * v0123).val = ll1.val * M := by
    rw [ZMod.val_mul_of_lt, h_v_val]; rw [h_v_val]; nlinarith [lt_ll1, h_MN]
  have h_ll2_mul : (ll2 * v0123).val = ll2.val * M := by
    rw [ZMod.val_mul_of_lt, h_v_val]; rw [h_v_val]; nlinarith [lt_ll2, h_MN]
  have h_ll3_mul : (ll3 * v0123).val = ll3.val * M := by
    rw [ZMod.val_mul_of_lt, h_v_val]; rw [h_v_val]; nlinarith [lt_ll3, h_MN]
  -- val_mul bridges for hl_j * ↑N
  have h_hl0_mul : (hl0 * ((N : ℕ) : ZMod p)).val = hl0.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh0, h_MN, h_NM]
  have h_hl1_mul : (hl1 * ((N : ℕ) : ZMod p)).val = hl1.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh1, h_MN, h_NM]
  have h_hl2_mul : (hl2 * ((N : ℕ) : ZMod p)).val = hl2.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh2, h_MN, h_NM]
  have h_hl3_mul : (hl3 * ((N : ℕ) : ZMod p)).val = hl3.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh3, h_MN, h_NM]
  -- b_j.val = hl_j.val * N + ll_j.val
  have h_b0_val : b0.val = hl0.val * N + ll0.val := by
    rw [h_b0, ZMod.val_add_of_lt]
    · rw [h_hl0_mul]
    · rw [h_hl0_mul]; nlinarith [lt_ll0, lt_lh0, h_MN, h_NM]
  have h_b1_val : b1.val = hl1.val * N + ll1.val := by
    rw [h_b1, ZMod.val_add_of_lt]
    · rw [h_hl1_mul]
    · rw [h_hl1_mul]; nlinarith [lt_ll1, lt_lh1, h_MN, h_NM]
  have h_b2_val : b2.val = hl2.val * N + ll2.val := by
    rw [h_b2, ZMod.val_add_of_lt]
    · rw [h_hl2_mul]
    · rw [h_hl2_mul]; nlinarith [lt_ll2, lt_lh2, h_MN, h_NM]
  have h_b3_val : b3.val = hl3.val * N + ll3.val := by
    rw [h_b3, ZMod.val_add_of_lt]
    · rw [h_hl3_mul]
    · rw [h_hl3_mul]; nlinarith [lt_ll3, lt_lh3, h_MN, h_NM]
  -- (ll_j * v0123 + hl_{j-1}).val
  have h_compose1_val : (ll1 * v0123 + hl0).val = ll1.val * M + hl0.val := by
    rw [ZMod.val_add_of_lt]
    · rw [h_ll1_mul]
    · rw [h_ll1_mul]; nlinarith [lt_ll1, lt_lh0, h_MN]
  have h_compose2_val : (ll2 * v0123 + hl1).val = ll2.val * M + hl1.val := by
    rw [ZMod.val_add_of_lt]
    · rw [h_ll2_mul]
    · rw [h_ll2_mul]; nlinarith [lt_ll2, lt_lh1, h_MN]
  have h_compose3_val : (ll3 * v0123 + hl2).val = ll3.val * M + hl2.val := by
    rw [ZMod.val_add_of_lt]
    · rw [h_ll3_mul]
    · rw [h_ll3_mul]; nlinarith [lt_ll3, lt_lh2, h_MN]
  -- Expand toBitVec64_poly.toNat and substitute.
  unfold Word.toBitVec64_poly
  simp only [BitVec.toNat_ofNat, Word.toNat_poly_def, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  rw [h_ll0_mul, h_compose1_val, h_compose2_val, h_compose3_val,
      h_b0_val, h_b1_val, h_b2_val, h_b3_val]
  -- Key identity: b_total * M = LHS_inner + hl_3.val * 2^64 (mod 2^64 the extra vanishes).
  -- Proof via linear_combination with coefficient on h_MN: M*N = 65536.
  have h_key : (hl0.val * N + ll0.val + (hl1.val * N + ll1.val) * 2 ^ 16
                + (hl2.val * N + ll2.val) * 2 ^ 32 + (hl3.val * N + ll3.val) * 2 ^ 48) * M
              = (ll0.val * M + (ll1.val * M + hl0.val) * 2 ^ 16
                + (ll2.val * M + hl1.val) * 2 ^ 32 + (ll3.val * M + hl2.val) * 2 ^ 48)
                + hl3.val * 2 ^ 64 := by
    linear_combination
      (hl0.val + hl1.val * 2 ^ 16 + hl2.val * 2 ^ 32 + hl3.val * 2 ^ 48) * h_MN
  rw [Nat.mod_mul_mod, h_key, Nat.add_mul_mod_self_right]

/-- Convenience wrapper for `spec.sll_poly`'s `cb4=cb5=0` byte-shift case: combines
`cancel_mul_65536_poly`, bound normalization, and the `<<<`-to-`*` bridge so each
sub-case can be closed by providing only the cb_i substitution facts and the
numeric (S, M, N) triple. -/
lemma sll_close_cb4cb5_zero_case {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
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
    (Word.toBitVec64_poly #v[ll0 * v0123, ll1 * v0123 + hl0, ll2 * v0123 + hl1,
                              ll3 * v0123 + hl2]).toNat
    = (Word.toBitVec64_poly #v[b0, b1, b2, b3]).toNat
        <<< (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val
      % 2 ^ 64 := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  -- Normalize bounds using h_inner_eq.
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
  -- Normalize the total shift to S.
  have h_total_val : (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val
                      = S := by
    rw [h_total_eq]; exact ZMod.val_natCast_of_lt (by omega)
  rw [h_total_val]
  -- Apply cancel_mul_65536_poly.
  have hdvd : v0123.val ∣ 65536 := by rw [h_v_val]; exact ⟨N, h_MN.symm⟩
  have hpos : 0 < v0123.val := by rw [h_v_val]; exact h_M_pos
  have h_b0' := cancel_mul_65536_poly hdvd hpos h_b0_dec
  have h_b1' := cancel_mul_65536_poly hdvd hpos h_b1_dec
  have h_b2' := cancel_mul_65536_poly hdvd hpos h_b2_dec
  have h_b3' := cancel_mul_65536_poly hdvd hpos h_b3_dec
  rw [h_v_val] at h_b0' h_b1' h_b2' h_b3'
  -- Bridge `<<< S` to `* M`.
  rw [show (Word.toBitVec64_poly #v[b0, b1, b2, b3]).toNat <<< S
          = (Word.toBitVec64_poly #v[b0, b1, b2, b3]).toNat * M from by
        rw [Nat.shiftLeft_eq, h_M_eq]]
  -- Apply within-byte-shift helper. Replace `65536/M` in h_b_j' with `N`.
  have h_div_eq : (65536 : ℕ) / M = N := by
    rw [← h_MN]; exact Nat.mul_div_cancel_left N h_M_pos
  rw [h_div_eq] at h_b0' h_b1' h_b2' h_b3'
  -- Convert the bounds from `2^(16-S)` / `2^S` form to `N` / `M` form.
  have h_lt_ll0 : ll0.val < N := by rw [h_N_eq]; exact lt_ll0
  have h_lt_ll1 : ll1.val < N := by rw [h_N_eq]; exact lt_ll1
  have h_lt_ll2 : ll2.val < N := by rw [h_N_eq]; exact lt_ll2
  have h_lt_ll3 : ll3.val < N := by rw [h_N_eq]; exact lt_ll3
  have h_lt_lh0 : hl0.val < M := by rw [h_M_eq]; exact lt_lh0
  have h_lt_lh1 : hl1.val < M := by rw [h_M_eq]; exact lt_lh1
  have h_lt_lh2 : hl2.val < M := by rw [h_M_eq]; exact lt_lh2
  have h_lt_lh3 : hl3.val < M := by rw [h_M_eq]; exact lt_lh3
  exact sll_within_byte_shift_poly M N h_MN h_M_pos h_v_val
    h_lt_ll0 h_lt_ll1 h_lt_ll2 h_lt_ll3 h_lt_lh0 h_lt_lh1 h_lt_lh2 h_lt_lh3
    h_b0' h_b1' h_b2' h_b3'

/-- Byte-shift=3 variant of `sll_within_byte_shift_poly`. Concludes the byte-shift=3
output (zeros in the first 3 limbs, `ll0 * v0123` in the 4th) equals
`b.toNat * M * 2^48 % 2^64`. -/
lemma sll_within_byte_shift_3_poly {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
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
    (Word.toBitVec64_poly #v[0, 0, 0, ll0 * v0123]).toNat
    = (Word.toBitVec64_poly #v[b0, b1, b2, b3]).toNat * M * 2 ^ 48 % 2 ^ 64 := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_N_lt_p : N < p := by nlinarith [h_MN]
  have h_N_val : ((N : ℕ) : ZMod p).val = N := ZMod.val_natCast_of_lt h_N_lt_p
  have h_NM : N * M = 65536 := by linarith [h_MN, Nat.mul_comm M N]
  -- val_mul for ll0 * v0123
  have h_ll0_mul : (ll0 * v0123).val = ll0.val * M := by
    rw [ZMod.val_mul_of_lt, h_v_val]; rw [h_v_val]; nlinarith [lt_ll0, h_MN]
  -- val_mul for hl_j * ↑N
  have h_hl0_mul : (hl0 * ((N : ℕ) : ZMod p)).val = hl0.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh0, h_MN, h_NM]
  have h_hl1_mul : (hl1 * ((N : ℕ) : ZMod p)).val = hl1.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh1, h_MN, h_NM]
  have h_hl2_mul : (hl2 * ((N : ℕ) : ZMod p)).val = hl2.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh2, h_MN, h_NM]
  have h_hl3_mul : (hl3 * ((N : ℕ) : ZMod p)).val = hl3.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh3, h_MN, h_NM]
  -- b_j.val = hl_j.val * N + ll_j.val
  have h_b0_val : b0.val = hl0.val * N + ll0.val := by
    rw [h_b0, ZMod.val_add_of_lt]
    · rw [h_hl0_mul]
    · rw [h_hl0_mul]; nlinarith [lt_ll0, lt_lh0, h_MN, h_NM]
  have h_b1_val : b1.val = hl1.val * N + ll1.val := by
    rw [h_b1, ZMod.val_add_of_lt]
    · rw [h_hl1_mul]
    · rw [h_hl1_mul]; nlinarith [lt_ll1, lt_lh1, h_MN, h_NM]
  have h_b2_val : b2.val = hl2.val * N + ll2.val := by
    rw [h_b2, ZMod.val_add_of_lt]
    · rw [h_hl2_mul]
    · rw [h_hl2_mul]; nlinarith [lt_ll2, lt_lh2, h_MN, h_NM]
  have h_b3_val : b3.val = hl3.val * N + ll3.val := by
    rw [h_b3, ZMod.val_add_of_lt]
    · rw [h_hl3_mul]
    · rw [h_hl3_mul]; nlinarith [lt_ll3, lt_lh3, h_MN, h_NM]
  -- Expand toBitVec64_poly.toNat for both sides.
  unfold Word.toBitVec64_poly
  simp only [BitVec.toNat_ofNat, Word.toNat_poly_def, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, ZMod.val_zero,
    zero_mul, zero_add]
  rw [h_ll0_mul, h_b0_val, h_b1_val, h_b2_val, h_b3_val]
  -- Key identity: b_total * M * 2^48 = (ll0 * M * 2^48) + 2^64 * K.
  have h_key : (hl0.val * N + ll0.val + (hl1.val * N + ll1.val) * 2 ^ 16
                + (hl2.val * N + ll2.val) * 2 ^ 32 + (hl3.val * N + ll3.val) * 2 ^ 48) * M
                * 2 ^ 48
              = ll0.val * M * 2 ^ 48
                + (hl0.val + ll1.val * M + hl1.val * 2 ^ 16 + ll2.val * M * 2 ^ 16
                   + hl2.val * 2 ^ 32 + ll3.val * M * 2 ^ 32 + hl3.val * 2 ^ 48) * 2 ^ 64 := by
    linear_combination
      (hl0.val + hl1.val * 2 ^ 16 + hl2.val * 2 ^ 32 + hl3.val * 2 ^ 48) * 2 ^ 48 * h_MN
  -- Remove inner `% 2^64` on the RHS via Nat.mul_assoc + Nat.mod_mul_mod.
  conv_rhs => rw [Nat.mul_assoc, Nat.mod_mul_mod, ← Nat.mul_assoc]
  rw [h_key, Nat.add_mul_mod_self_right]

/-- Byte-shift=2 variant. -/
lemma sll_within_byte_shift_2_poly {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
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
    (Word.toBitVec64_poly #v[0, 0, ll0 * v0123, ll1 * v0123 + hl0]).toNat
    = (Word.toBitVec64_poly #v[b0, b1, b2, b3]).toNat * M * 2 ^ 32 % 2 ^ 64 := by
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
  have h_hl2_mul : (hl2 * ((N : ℕ) : ZMod p)).val = hl2.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh2, h_MN, h_NM]
  have h_hl3_mul : (hl3 * ((N : ℕ) : ZMod p)).val = hl3.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh3, h_MN, h_NM]
  have h_b0_val : b0.val = hl0.val * N + ll0.val := by
    rw [h_b0, ZMod.val_add_of_lt]
    · rw [h_hl0_mul]
    · rw [h_hl0_mul]; nlinarith [lt_ll0, lt_lh0, h_MN, h_NM]
  have h_b1_val : b1.val = hl1.val * N + ll1.val := by
    rw [h_b1, ZMod.val_add_of_lt]
    · rw [h_hl1_mul]
    · rw [h_hl1_mul]; nlinarith [lt_ll1, lt_lh1, h_MN, h_NM]
  have h_b2_val : b2.val = hl2.val * N + ll2.val := by
    rw [h_b2, ZMod.val_add_of_lt]
    · rw [h_hl2_mul]
    · rw [h_hl2_mul]; nlinarith [lt_ll2, lt_lh2, h_MN, h_NM]
  have h_b3_val : b3.val = hl3.val * N + ll3.val := by
    rw [h_b3, ZMod.val_add_of_lt]
    · rw [h_hl3_mul]
    · rw [h_hl3_mul]; nlinarith [lt_ll3, lt_lh3, h_MN, h_NM]
  have h_compose1_val : (ll1 * v0123 + hl0).val = ll1.val * M + hl0.val := by
    rw [ZMod.val_add_of_lt]
    · rw [h_ll1_mul]
    · rw [h_ll1_mul]; nlinarith [lt_ll1, lt_lh0, h_MN]
  unfold Word.toBitVec64_poly
  simp only [BitVec.toNat_ofNat, Word.toNat_poly_def, Vector.getElem_mk,
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

/-- Byte-shift=1 variant. -/
lemma sll_within_byte_shift_1_poly {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
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
    (Word.toBitVec64_poly #v[0, ll0 * v0123, ll1 * v0123 + hl0, ll2 * v0123 + hl1]).toNat
    = (Word.toBitVec64_poly #v[b0, b1, b2, b3]).toNat * M * 2 ^ 16 % 2 ^ 64 := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_N_lt_p : N < p := by nlinarith [h_MN]
  have h_N_val : ((N : ℕ) : ZMod p).val = N := ZMod.val_natCast_of_lt h_N_lt_p
  have h_NM : N * M = 65536 := by linarith [h_MN, Nat.mul_comm M N]
  have h_ll0_mul : (ll0 * v0123).val = ll0.val * M := by
    rw [ZMod.val_mul_of_lt, h_v_val]; rw [h_v_val]; nlinarith [lt_ll0, h_MN]
  have h_ll1_mul : (ll1 * v0123).val = ll1.val * M := by
    rw [ZMod.val_mul_of_lt, h_v_val]; rw [h_v_val]; nlinarith [lt_ll1, h_MN]
  have h_ll2_mul : (ll2 * v0123).val = ll2.val * M := by
    rw [ZMod.val_mul_of_lt, h_v_val]; rw [h_v_val]; nlinarith [lt_ll2, h_MN]
  have h_hl0_mul : (hl0 * ((N : ℕ) : ZMod p)).val = hl0.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh0, h_MN, h_NM]
  have h_hl1_mul : (hl1 * ((N : ℕ) : ZMod p)).val = hl1.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh1, h_MN, h_NM]
  have h_hl2_mul : (hl2 * ((N : ℕ) : ZMod p)).val = hl2.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh2, h_MN, h_NM]
  have h_hl3_mul : (hl3 * ((N : ℕ) : ZMod p)).val = hl3.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh3, h_MN, h_NM]
  have h_b0_val : b0.val = hl0.val * N + ll0.val := by
    rw [h_b0, ZMod.val_add_of_lt]
    · rw [h_hl0_mul]
    · rw [h_hl0_mul]; nlinarith [lt_ll0, lt_lh0, h_MN, h_NM]
  have h_b1_val : b1.val = hl1.val * N + ll1.val := by
    rw [h_b1, ZMod.val_add_of_lt]
    · rw [h_hl1_mul]
    · rw [h_hl1_mul]; nlinarith [lt_ll1, lt_lh1, h_MN, h_NM]
  have h_b2_val : b2.val = hl2.val * N + ll2.val := by
    rw [h_b2, ZMod.val_add_of_lt]
    · rw [h_hl2_mul]
    · rw [h_hl2_mul]; nlinarith [lt_ll2, lt_lh2, h_MN, h_NM]
  have h_b3_val : b3.val = hl3.val * N + ll3.val := by
    rw [h_b3, ZMod.val_add_of_lt]
    · rw [h_hl3_mul]
    · rw [h_hl3_mul]; nlinarith [lt_ll3, lt_lh3, h_MN, h_NM]
  have h_compose1_val : (ll1 * v0123 + hl0).val = ll1.val * M + hl0.val := by
    rw [ZMod.val_add_of_lt]
    · rw [h_ll1_mul]
    · rw [h_ll1_mul]; nlinarith [lt_ll1, lt_lh0, h_MN]
  have h_compose2_val : (ll2 * v0123 + hl1).val = ll2.val * M + hl1.val := by
    rw [ZMod.val_add_of_lt]
    · rw [h_ll2_mul]
    · rw [h_ll2_mul]; nlinarith [lt_ll2, lt_lh1, h_MN]
  unfold Word.toBitVec64_poly
  simp only [BitVec.toNat_ofNat, Word.toNat_poly_def, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, ZMod.val_zero,
    zero_mul, zero_add]
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

/-- Wrapper for `spec.sll_poly`'s cb4=1, cb5=1 (byte_shift=3) case. -/
lemma sll_close_cb4cb5_one_one_case {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
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
    (Word.toBitVec64_poly #v[0, 0, 0, ll0 * v0123]).toNat
    = (Word.toBitVec64_poly #v[b0, b1, b2, b3]).toNat
        <<< (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val
      % 2 ^ 64 := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  -- Normalize bounds using h_inner_eq.
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
  -- Total shift = S + 48.
  have h_total_val : (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val
                      = S + 48 := by
    rw [h_total_eq]; exact ZMod.val_natCast_of_lt (by omega)
  rw [h_total_val]
  -- Apply cancel_mul_65536_poly.
  have hdvd : v0123.val ∣ 65536 := by rw [h_v_val]; exact ⟨N, h_MN.symm⟩
  have hpos : 0 < v0123.val := by rw [h_v_val]; exact h_M_pos
  have h_b0' := cancel_mul_65536_poly hdvd hpos h_b0_dec
  have h_b1' := cancel_mul_65536_poly hdvd hpos h_b1_dec
  have h_b2' := cancel_mul_65536_poly hdvd hpos h_b2_dec
  have h_b3' := cancel_mul_65536_poly hdvd hpos h_b3_dec
  rw [h_v_val] at h_b0' h_b1' h_b2' h_b3'
  -- Bridge `<<< (S + 48)` to `* M * 2^48`.
  rw [show (Word.toBitVec64_poly #v[b0, b1, b2, b3]).toNat <<< (S + 48)
          = (Word.toBitVec64_poly #v[b0, b1, b2, b3]).toNat * M * 2 ^ 48 from by
        rw [Nat.shiftLeft_eq, h_M_eq, pow_add, ← Nat.mul_assoc]]
  -- Replace `65536/M` in h_b_j' with `N`.
  have h_div_eq : (65536 : ℕ) / M = N := by
    rw [← h_MN]; exact Nat.mul_div_cancel_left N h_M_pos
  rw [h_div_eq] at h_b0' h_b1' h_b2' h_b3'
  -- Bounds to `< N` / `< M` form.
  have h_lt_ll0 : ll0.val < N := by rw [h_N_eq]; exact lt_ll0
  have h_lt_ll1 : ll1.val < N := by rw [h_N_eq]; exact lt_ll1
  have h_lt_ll2 : ll2.val < N := by rw [h_N_eq]; exact lt_ll2
  have h_lt_ll3 : ll3.val < N := by rw [h_N_eq]; exact lt_ll3
  have h_lt_lh0 : hl0.val < M := by rw [h_M_eq]; exact lt_lh0
  have h_lt_lh1 : hl1.val < M := by rw [h_M_eq]; exact lt_lh1
  have h_lt_lh2 : hl2.val < M := by rw [h_M_eq]; exact lt_lh2
  have h_lt_lh3 : hl3.val < M := by rw [h_M_eq]; exact lt_lh3
  exact sll_within_byte_shift_3_poly M N h_MN h_M_pos h_v_val
    h_lt_ll0 h_lt_ll1 h_lt_ll2 h_lt_ll3 h_lt_lh0 h_lt_lh1 h_lt_lh2 h_lt_lh3
    h_b0' h_b1' h_b2' h_b3'

/-- Wrapper for `spec.sll_poly`'s cb4=0, cb5=1 (byte_shift=2) case. -/
lemma sll_close_cb4cb5_zero_one_case {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
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
    (Word.toBitVec64_poly #v[0, 0, ll0 * v0123, ll1 * v0123 + hl0]).toNat
    = (Word.toBitVec64_poly #v[b0, b1, b2, b3]).toNat
        <<< (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val
      % 2 ^ 64 := by
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
  have h_b0' := cancel_mul_65536_poly hdvd hpos h_b0_dec
  have h_b1' := cancel_mul_65536_poly hdvd hpos h_b1_dec
  have h_b2' := cancel_mul_65536_poly hdvd hpos h_b2_dec
  have h_b3' := cancel_mul_65536_poly hdvd hpos h_b3_dec
  rw [h_v_val] at h_b0' h_b1' h_b2' h_b3'
  rw [show (Word.toBitVec64_poly #v[b0, b1, b2, b3]).toNat <<< (S + 32)
          = (Word.toBitVec64_poly #v[b0, b1, b2, b3]).toNat * M * 2 ^ 32 from by
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
  exact sll_within_byte_shift_2_poly M N h_MN h_M_pos h_v_val
    h_lt_ll0 h_lt_ll1 h_lt_ll2 h_lt_ll3 h_lt_lh0 h_lt_lh1 h_lt_lh2 h_lt_lh3
    h_b0' h_b1' h_b2' h_b3'

/-- Wrapper for `spec.sll_poly`'s cb4=1, cb5=0 (byte_shift=1) case. -/
lemma sll_close_cb4cb5_one_zero_case {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
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
    (Word.toBitVec64_poly #v[0, ll0 * v0123, ll1 * v0123 + hl0, ll2 * v0123 + hl1]).toNat
    = (Word.toBitVec64_poly #v[b0, b1, b2, b3]).toNat
        <<< (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val
      % 2 ^ 64 := by
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
  have h_b0' := cancel_mul_65536_poly hdvd hpos h_b0_dec
  have h_b1' := cancel_mul_65536_poly hdvd hpos h_b1_dec
  have h_b2' := cancel_mul_65536_poly hdvd hpos h_b2_dec
  have h_b3' := cancel_mul_65536_poly hdvd hpos h_b3_dec
  rw [h_v_val] at h_b0' h_b1' h_b2' h_b3'
  rw [show (Word.toBitVec64_poly #v[b0, b1, b2, b3]).toNat <<< (S + 16)
          = (Word.toBitVec64_poly #v[b0, b1, b2, b3]).toNat * M * 2 ^ 16 from by
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
  exact sll_within_byte_shift_1_poly M N h_MN h_M_pos h_v_val
    h_lt_ll0 h_lt_ll1 h_lt_ll2 h_lt_ll3 h_lt_lh0 h_lt_lh1 h_lt_lh2 h_lt_lh3
    h_b0' h_b1' h_b2' h_b3'

/-- HWord (2-limb, 32-bit) analog of `sll_within_byte_shift_poly`. Within-byte shift
identity for the cb4=0 (byte_shift=0) case of SLLW/SLLIW: the 32-bit output composed
from `ll_j` and `hl_j` limbs equals the 32-bit input shifted left by `S` bits, modulo
`2^32`. -/
lemma sllw_within_byte_shift_poly {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (M N : ℕ) (h_MN : M * N = 65536) (h_M_pos : 0 < M)
    {b0 b1 ll0 ll1 hl0 hl1 v0123 : ZMod p}
    (h_v_val : v0123.val = M)
    (lt_ll0 : ll0.val < N) (lt_ll1 : ll1.val < N)
    (lt_lh0 : hl0.val < M) (lt_lh1 : hl1.val < M)
    (h_b0 : b0 = hl0 * ((N : ℕ) : ZMod p) + ll0)
    (h_b1 : b1 = hl1 * ((N : ℕ) : ZMod p) + ll1) :
    (HWord.toBitVec32_poly #v[ll0 * v0123, ll1 * v0123 + hl0]).toNat
    = (HWord.toBitVec32_poly #v[b0, b1]).toNat * M % 2 ^ 32 := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_N_lt_p : N < p := by nlinarith [h_MN]
  have h_N_val : ((N : ℕ) : ZMod p).val = N := ZMod.val_natCast_of_lt h_N_lt_p
  have h_NM : N * M = 65536 := by linarith [h_MN, Nat.mul_comm M N]
  -- val_mul bridges
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
  unfold HWord.toBitVec32_poly
  simp only [BitVec.toNat_ofNat, HWord.toNat_poly, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  rw [h_ll0_mul, h_compose1_val, h_b0_val, h_b1_val]
  -- Key: (b_total.val) * M = LHS_inner + hl1.val * 2^32 (mod 2^32 the extra vanishes).
  have h_key : (hl0.val * N + ll0.val + (hl1.val * N + ll1.val) * 2 ^ 16) * M
              = (ll0.val * M + (ll1.val * M + hl0.val) * 2 ^ 16) + hl1.val * 2 ^ 32 := by
    linear_combination
      (hl0.val + hl1.val * 2 ^ 16) * h_MN
  rw [Nat.mod_mul_mod, h_key, Nat.add_mul_mod_self_right]

/-- HWord (2-limb, 32-bit) analog of `sll_within_byte_shift_1_poly`. Within-byte shift
identity for the cb4=1 (byte_shift=1) case of SLLW/SLLIW: the 32-bit output places
`ll0 * v0123` in the high 16-bit limb and zero in the low 16-bit limb. -/
lemma sllw_within_byte_shift_1_poly {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (M N : ℕ) (h_MN : M * N = 65536) (h_M_pos : 0 < M)
    {b0 b1 ll0 ll1 hl0 hl1 v0123 : ZMod p}
    (h_v_val : v0123.val = M)
    (lt_ll0 : ll0.val < N) (lt_ll1 : ll1.val < N)
    (lt_lh0 : hl0.val < M) (lt_lh1 : hl1.val < M)
    (h_b0 : b0 = hl0 * ((N : ℕ) : ZMod p) + ll0)
    (h_b1 : b1 = hl1 * ((N : ℕ) : ZMod p) + ll1) :
    (HWord.toBitVec32_poly #v[0, ll0 * v0123]).toNat
    = (HWord.toBitVec32_poly #v[b0, b1]).toNat * M * 2 ^ 16 % 2 ^ 32 := by
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
  unfold HWord.toBitVec32_poly
  simp only [BitVec.toNat_ofNat, HWord.toNat_poly, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, ZMod.val_zero,
    zero_mul, zero_add]
  rw [h_ll0_mul, h_b0_val, h_b1_val]
  have h_key : (hl0.val * N + ll0.val + (hl1.val * N + ll1.val) * 2 ^ 16) * M * 2 ^ 16
              = ll0.val * M * 2 ^ 16 + (hl0.val + ll1.val * M + hl1.val * 2 ^ 16) * 2 ^ 32 := by
    linear_combination
      (hl0.val + hl1.val * 2 ^ 16) * 2 ^ 16 * h_MN
  conv_rhs => rw [Nat.mul_assoc, Nat.mod_mul_mod, ← Nat.mul_assoc]
  rw [h_key, Nat.add_mul_mod_self_right]

/-- Convenience wrapper for `spec.sllw_poly`/`spec.slliw_poly`'s `cb4=0` byte-shift case
(byte_shift=0, S ≤ 15). The shift amount is the 5-bit sum `cb0+cb1*2+cb2*4+cb3*8+cb4*16`
(cb5 does not appear because the SLLW shift uses only the low 5 bits of c0). Combines
`cancel_mul_65536_poly`, bound normalization, and the `<<<`-to-`*` bridge for the 32-bit
shift identity. -/
lemma sllw_close_cb4_zero_case {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
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
    (HWord.toBitVec32_poly #v[ll0 * v0123, ll1 * v0123 + hl0]).toNat
    = (HWord.toBitVec32_poly #v[b0, b1]).toNat
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
  have h_b0' := cancel_mul_65536_poly hdvd hpos h_b0_dec
  have h_b1' := cancel_mul_65536_poly hdvd hpos h_b1_dec
  rw [h_v_val] at h_b0' h_b1'
  rw [show (HWord.toBitVec32_poly #v[b0, b1]).toNat <<< S
          = (HWord.toBitVec32_poly #v[b0, b1]).toNat * M from by
        rw [Nat.shiftLeft_eq, h_M_eq]]
  have h_div_eq : (65536 : ℕ) / M = N := by
    rw [← h_MN]; exact Nat.mul_div_cancel_left N h_M_pos
  rw [h_div_eq] at h_b0' h_b1'
  have h_lt_ll0 : ll0.val < N := by rw [h_N_eq]; exact lt_ll0
  have h_lt_ll1 : ll1.val < N := by rw [h_N_eq]; exact lt_ll1
  have h_lt_lh0 : hl0.val < M := by rw [h_M_eq]; exact lt_lh0
  have h_lt_lh1 : hl1.val < M := by rw [h_M_eq]; exact lt_lh1
  exact sllw_within_byte_shift_poly M N h_MN h_M_pos h_v_val
    h_lt_ll0 h_lt_ll1 h_lt_lh0 h_lt_lh1 h_b0' h_b1'

/-- Convenience wrapper for `spec.sllw_poly`/`spec.slliw_poly`'s `cb4=1` byte-shift case
(byte_shift=1, S ∈ [16, 31]). The shift amount is the 5-bit sum
`cb0+cb1*2+cb2*4+cb3*8+cb4*16` (cb5 does not appear). The 32-bit output places
`ll0 * v0123` in the high 16-bit limb and zero in the low 16-bit limb. -/
lemma sllw_close_cb4_one_case {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
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
    (HWord.toBitVec32_poly #v[0, ll0 * v0123]).toNat
    = (HWord.toBitVec32_poly #v[b0, b1]).toNat
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
  have h_b0' := cancel_mul_65536_poly hdvd hpos h_b0_dec
  have h_b1' := cancel_mul_65536_poly hdvd hpos h_b1_dec
  rw [h_v_val] at h_b0' h_b1'
  rw [show (HWord.toBitVec32_poly #v[b0, b1]).toNat <<< (S + 16)
          = (HWord.toBitVec32_poly #v[b0, b1]).toNat * M * 2 ^ 16 from by
        rw [Nat.shiftLeft_eq, h_M_eq, pow_add, ← Nat.mul_assoc]]
  have h_div_eq : (65536 : ℕ) / M = N := by
    rw [← h_MN]; exact Nat.mul_div_cancel_left N h_M_pos
  rw [h_div_eq] at h_b0' h_b1'
  have h_lt_ll0 : ll0.val < N := by rw [h_N_eq]; exact lt_ll0
  have h_lt_ll1 : ll1.val < N := by rw [h_N_eq]; exact lt_ll1
  have h_lt_lh0 : hl0.val < M := by rw [h_M_eq]; exact lt_lh0
  have h_lt_lh1 : hl1.val < M := by rw [h_M_eq]; exact lt_lh1
  exact sllw_within_byte_shift_1_poly M N h_MN h_M_pos h_v_val
    h_lt_ll0 h_lt_ll1 h_lt_lh0 h_lt_lh1 h_b0' h_b1'

/-- Helper for SLLW/SLLIW spec proofs. Given the chip's MSB constraint on `a1`
(`h_msb_constr`) plus the sign-extension constraints `a2 = msb * 65535` and
`a3 = msb * 65535`, conclude that both `a2` and `a3` equal the byte-form of
the BitVec MSB of `#v[a0, a1]` (i.e. `if msb then 65535 else 0`). This lets the
sllw proof match the canonical form produced by `HWord.sign_extend_32_to_64_msb_poly`. -/
lemma sllw_a2_a3_eq_msb_byte {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    {a0 a1 a2 a3 msb : ZMod p}
    (h_msb_a1 : List.Forall SP1Constraint.toProp_poly
      (U16MSBOperation.constraints a1 { msb := msb } 1))
    (h_a1_lt : a1.val < 65536)
    (h_a2_eq : msb * 65535 = a2)
    (h_a3_eq : msb * 65535 = a3)
    (is_U32_a : HWord.isU32_poly #v[a0, a1]) :
    a2 = (if (HWord.toBitVec32_poly #v[a0, a1]).msb = true then (65535 : ZMod p) else 0) ∧
    a3 = (if (HWord.toBitVec32_poly #v[a0, a1]).msb = true then (65535 : ZMod p) else 0) := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  -- Get msb = if a1.val ≥ 32768 then 1 else 0 from U16MSB.spec_poly
  have h_msb := U16MSBOperation.spec_poly h_a1_lt h_msb_a1
  dsimp only at h_msb
  -- Bridge a1.val ≥ 32768 to (HWord.toBitVec32_poly #v[a0, a1]).msb
  have ⟨h_a0_lt, _⟩ := HWord.lt_cases_of_isU32_poly is_U32_a
  have h_msb_iff : (HWord.toBitVec32_poly #v[a0, a1]).msb = true ↔ a1.val ≥ 32768 := by
    rw [← HWord.isNegative_poly_msb is_U32_a]
    simp [HWord.isNegative_poly]
  have h_msb_byte_eq : msb * 65535
                     = (if (HWord.toBitVec32_poly #v[a0, a1]).msb = true then (65535 : ZMod p) else 0) := by
    rw [h_msb]
    by_cases hge : a1.val ≥ 32768
    · simp only [if_pos hge, one_mul]
      rw [if_pos (h_msb_iff.mpr hge)]
    · simp only [if_neg hge, zero_mul]
      rw [if_neg (h_msb_iff.not.mpr hge)]
  exact ⟨by linear_combination -h_a2_eq + h_msb_byte_eq, by linear_combination -h_a3_eq + h_msb_byte_eq⟩

set_option maxHeartbeats 800000 in
-- Per-sub-case closing helper for spec.sllw_poly's `cb4 = 0` byte-shift branch
-- (byte_shift=0). 800K heartbeats: bound + sign-extend + helper chain.
lemma sllw_subcase_cb4_zero {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
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
    (h_b0_lt : b0.val < 65536) (h_b1_lt : b1.val < 65536)
    (h_c0_lt : c0.val < 65536) (h_c1_lt : c1.val < 65536)
    (h_msb_a1 : List.Forall SP1Constraint.toProp_poly
      (U16MSBOperation.constraints (ll1 * v0123 + hl0) { msb := msb } 1))
    (h_a2_eq : msb * 65535 = a2) (h_a3_eq : msb * 65535 = a3)
    (h_c_mod_32 : c0.val % 32 = (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16).val) :
    Word.toBitVec64_poly #v[ll0 * v0123, ll1 * v0123 + hl0, a2, a3]
      = BitVec.signExtend 64 (HWord.toBitVec32_poly #v[b0, b1] <<<
                              BitVec.setWidth 5 (HWord.toBitVec32_poly #v[c0, c1])) := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  -- Derive concrete bounds for ll0*v0123 and ll1*v0123 + hl0.
  have h_inner_val : (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                      + cb3 * 8 : ZMod p).val = S := by
    rw [h_inner_eq]; exact ZMod.val_natCast_of_lt (by omega)
  have h_inner_hi_val : (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                + cb3 * 8) : ZMod p).val = 16 - S := by
    rw [show (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
              + cb3 * 8) : ZMod p) = (((16 - S) : ℕ) : ZMod p) from by
      rw [h_inner_eq, Nat.cast_sub (by omega : S ≤ 16)]; push_cast; ring]
    exact ZMod.val_natCast_of_lt (by omega)
  -- Derive concrete-N/M bounds without mutating the originals (helper needs them as-is).
  have h_lt_ll0_N : ll0.val < N := by rw [h_N_eq]; rw [h_inner_hi_val] at lt_ll0; exact lt_ll0
  have h_lt_ll1_N : ll1.val < N := by rw [h_N_eq]; rw [h_inner_hi_val] at lt_ll1; exact lt_ll1
  have h_lt_lh0_M : hl0.val < M := by rw [h_M_eq]; rw [h_inner_val] at lt_lh0; exact lt_lh0
  have h_lt_lh1_M : hl1.val < M := by rw [h_M_eq]; rw [h_inner_val] at lt_lh1; exact lt_lh1
  -- Re-derive original-form bounds for the helper call.
  have lt_ll0' : ll0.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                       + cb3 * 8) : ZMod p).val := by rw [h_inner_hi_val, ← h_N_eq]; exact h_lt_ll0_N
  have lt_lh0' : hl0.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                  + cb3 * 8 : ZMod p).val := by rw [h_inner_val, ← h_M_eq]; exact h_lt_lh0_M
  have lt_ll1' : ll1.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                       + cb3 * 8) : ZMod p).val := by rw [h_inner_hi_val, ← h_N_eq]; exact h_lt_ll1_N
  have lt_lh1' : hl1.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                  + cb3 * 8 : ZMod p).val := by rw [h_inner_val, ← h_M_eq]; exact h_lt_lh1_M
  -- val of ll0 * v0123
  have h_ll0v_val : (ll0 * v0123).val = ll0.val * M := by
    rw [ZMod.val_mul_of_lt, h_v_val]
    rw [h_v_val]; nlinarith [h_lt_ll0_N, h_MN]
  have h_ll0v_lt : (ll0 * v0123).val < 65536 := by
    rw [h_ll0v_val]; nlinarith [h_lt_ll0_N, h_MN]
  -- val of ll1 * v0123 + hl0
  have h_ll1v_val : (ll1 * v0123).val = ll1.val * M := by
    rw [ZMod.val_mul_of_lt, h_v_val]
    rw [h_v_val]; nlinarith [h_lt_ll1_N, h_MN]
  have h_compose_val : (ll1 * v0123 + hl0).val = ll1.val * M + hl0.val := by
    rw [ZMod.val_add_of_lt, h_ll1v_val]
    rw [h_ll1v_val]; nlinarith [h_lt_ll1_N, h_lt_lh0_M, h_MN]
  have h_compose_lt : (ll1 * v0123 + hl0).val < 65536 := by
    rw [h_compose_val]; nlinarith [h_lt_ll1_N, h_lt_lh0_M, h_MN]
  -- is_U32_a
  have is_U32_a : HWord.isU32_poly #v[ll0 * v0123, ll1 * v0123 + hl0] :=
    HWord.isU32_of_cases_poly (by simpa using h_ll0v_lt) (by simpa using h_compose_lt)
  -- 32-bit shift identity at toNat level (via the existing helper).
  have h_shift_nat : (HWord.toBitVec32_poly #v[ll0 * v0123, ll1 * v0123 + hl0]).toNat
                   = (HWord.toBitVec32_poly #v[b0, b1]).toNat
                       <<< (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16).val
                     % 2 ^ 32 :=
    sllw_close_cb4_zero_case S h_S_le M N h_MN h_M_pos h_M_eq h_N_eq
      h_v_val h_inner_eq h_total_eq lt_ll0' lt_lh0' lt_ll1' lt_lh1' h_b0_dec h_b1_dec
  -- Convert to BitVec equality.
  have is_U32_b' : HWord.isU32_poly #v[b0, b1] :=
    HWord.isU32_of_cases_poly (by simpa using h_b0_lt) (by simpa using h_b1_lt)
  have is_U32_c' : HWord.isU32_poly #v[c0, c1] :=
    HWord.isU32_of_cases_poly (by simpa using h_c0_lt) (by simpa using h_c1_lt)
  have h_shift : HWord.toBitVec32_poly #v[ll0 * v0123, ll1 * v0123 + hl0]
              = HWord.toBitVec32_poly #v[b0, b1] <<<
                  BitVec.setWidth 5 (HWord.toBitVec32_poly #v[c0, c1]) := by
    rw [← BitVec.toNat_inj]
    simp only [BitVec.toNat_shiftLeft, BitVec.shiftLeft_eq', BitVec.toNat_setWidth]
    rw [HWord.toBitVec32_poly_toNat_poly is_U32_c']
    have h_c_toNat : HWord.toNat_poly #v[c0, c1] % 2 ^ 5 = c0.val % 32 := by
      simp [HWord.toNat_poly]; omega
    rw [h_c_toNat, h_c_mod_32]
    exact h_shift_nat
  -- Substitute the shift expression in the goal RHS.
  rw [← h_shift]
  -- Apply sign_extend_32_to_64_msb_poly.
  rw [HWord.sign_extend_32_to_64_msb_poly is_U32_a]
  -- Match a2, a3 against msb_byte.
  have ⟨h_a2_match, h_a3_match⟩ :=
    sllw_a2_a3_eq_msb_byte (a0 := ll0 * v0123) (a1 := ll1 * v0123 + hl0)
      h_msb_a1 h_compose_lt h_a2_eq h_a3_eq is_U32_a
  rw [h_a2_match, h_a3_match]
  rfl

set_option maxHeartbeats 800000 in
-- Per-sub-case closing helper for spec.sllw_poly's `cb4 = 1` byte-shift branch
-- (byte_shift=1). Mirror of `sllw_subcase_cb4_zero` with a0 = 0, a1 = ll0 * v0123.
lemma sllw_subcase_cb4_one {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
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
    (h_b0_lt : b0.val < 65536) (h_b1_lt : b1.val < 65536)
    (h_c0_lt : c0.val < 65536) (h_c1_lt : c1.val < 65536)
    (h_msb_a1 : List.Forall SP1Constraint.toProp_poly
      (U16MSBOperation.constraints (ll0 * v0123) { msb := msb } 1))
    (h_a2_eq : msb * 65535 = a2) (h_a3_eq : msb * 65535 = a3)
    (h_c_mod_32 : c0.val % 32 = (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16).val) :
    Word.toBitVec64_poly #v[0, ll0 * v0123, a2, a3]
      = BitVec.signExtend 64 (HWord.toBitVec32_poly #v[b0, b1] <<<
                              BitVec.setWidth 5 (HWord.toBitVec32_poly #v[c0, c1])) := by
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
  -- Derive concrete bounds without mutating originals (helper needs them as-is).
  have h_lt_ll0_N : ll0.val < N := by rw [h_N_eq]; rw [h_inner_hi_val] at lt_ll0; exact lt_ll0
  have h_lt_lh0_M : hl0.val < M := by rw [h_M_eq]; rw [h_inner_val] at lt_lh0; exact lt_lh0
  -- Re-derive original-form bounds for the helper call.
  have lt_ll0' : ll0.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                       + cb3 * 8) : ZMod p).val := by rw [h_inner_hi_val, ← h_N_eq]; exact h_lt_ll0_N
  have lt_lh0' : hl0.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                  + cb3 * 8 : ZMod p).val := by rw [h_inner_val, ← h_M_eq]; exact h_lt_lh0_M
  have h_lt_ll1_N : ll1.val < N := by rw [h_N_eq]; rw [h_inner_hi_val] at lt_ll1; exact lt_ll1
  have h_lt_lh1_M : hl1.val < M := by rw [h_M_eq]; rw [h_inner_val] at lt_lh1; exact lt_lh1
  have lt_ll1' : ll1.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                       + cb3 * 8) : ZMod p).val := by rw [h_inner_hi_val, ← h_N_eq]; exact h_lt_ll1_N
  have lt_lh1' : hl1.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                  + cb3 * 8 : ZMod p).val := by rw [h_inner_val, ← h_M_eq]; exact h_lt_lh1_M
  have h_ll0v_val : (ll0 * v0123).val = ll0.val * M := by
    rw [ZMod.val_mul_of_lt, h_v_val]
    rw [h_v_val]; nlinarith [h_lt_ll0_N, h_MN]
  have h_ll0v_lt : (ll0 * v0123).val < 65536 := by
    rw [h_ll0v_val]; nlinarith [h_lt_ll0_N, h_MN]
  -- is_U32_a: a0 = 0, a1 = ll0 * v0123. Need 0.val < 2^16 (trivial) and (ll0*v0123).val < 2^16.
  have is_U32_a : HWord.isU32_poly #v[(0 : ZMod p), ll0 * v0123] :=
    HWord.isU32_of_cases_poly (by simp [ZMod.val_zero]) (by simpa using h_ll0v_lt)
  -- 32-bit shift identity at toNat level.
  have h_shift_nat : (HWord.toBitVec32_poly #v[(0 : ZMod p), ll0 * v0123]).toNat
                   = (HWord.toBitVec32_poly #v[b0, b1]).toNat
                       <<< (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16).val
                     % 2 ^ 32 :=
    sllw_close_cb4_one_case S h_S_le M N h_MN h_M_pos h_M_eq h_N_eq
      h_v_val h_inner_eq h_total_eq lt_ll0' lt_lh0' lt_ll1' lt_lh1' h_b0_dec h_b1_dec
  -- Convert to BitVec equality.
  have is_U32_b' : HWord.isU32_poly #v[b0, b1] :=
    HWord.isU32_of_cases_poly (by simpa using h_b0_lt) (by simpa using h_b1_lt)
  have is_U32_c' : HWord.isU32_poly #v[c0, c1] :=
    HWord.isU32_of_cases_poly (by simpa using h_c0_lt) (by simpa using h_c1_lt)
  have h_shift : HWord.toBitVec32_poly #v[(0 : ZMod p), ll0 * v0123]
              = HWord.toBitVec32_poly #v[b0, b1] <<<
                  BitVec.setWidth 5 (HWord.toBitVec32_poly #v[c0, c1]) := by
    rw [← BitVec.toNat_inj]
    simp only [BitVec.toNat_shiftLeft, BitVec.shiftLeft_eq', BitVec.toNat_setWidth]
    rw [HWord.toBitVec32_poly_toNat_poly is_U32_c']
    have h_c_toNat : HWord.toNat_poly #v[c0, c1] % 2 ^ 5 = c0.val % 32 := by
      simp [HWord.toNat_poly]; omega
    rw [h_c_toNat, h_c_mod_32]
    exact h_shift_nat
  rw [← h_shift]
  rw [HWord.sign_extend_32_to_64_msb_poly is_U32_a]
  have ⟨h_a2_match, h_a3_match⟩ :=
    sllw_a2_a3_eq_msb_byte (a0 := (0 : ZMod p)) (a1 := ll0 * v0123)
      h_msb_a1 h_ll0v_lt h_a2_eq h_a3_eq is_U32_a
  rw [h_a2_match, h_a3_match]
  rfl

end field_arithmetic

section opcodes

omit [Fact (2 ^ 17 < p)] in
@[simp] def is_sll_poly (Main : Vector (ZMod p) 65) := Main[62] = 1 ∧ Main[31] = 0

omit [Fact (2 ^ 17 < p)] in
@[simp] def is_sllw_poly (Main : Vector (ZMod p) 65) := Main[63] = 1 ∧ Main[31] = 0

omit [Fact (2 ^ 17 < p)] in
@[simp] def is_slli_poly (Main : Vector (ZMod p) 65) := Main[62] = 1 ∧ Main[31] = 1

omit [Fact (2 ^ 17 < p)] in
@[simp] def is_slliw_poly (Main : Vector (ZMod p) 65) := Main[63] = 1 ∧ Main[31] = 1

lemma single_op_poly (Main : Vector (ZMod p) 65)
    (cstrs : (constraints Main).allHold_poly) :
    (Main[62] = 1 → Main[63] = 0) ∧ (Main[63] = 1 → Main[62] = 0) := by
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  change List.Forall SP1Constraint.toProp_poly (constraints Main) at cstrs
  rw [allHold_constraints_iff_poly] at cstrs
  obtain ⟨_, _, _, sum_disj, b_sll, b_sllw, _⟩ := cstrs
  have h_one_ne_zero : (1 : ZMod p) ≠ 0 := by
    have hp : 2 ^ 17 < p := Fact.out
    haveI : Fact (1 < p) := ⟨by omega⟩
    have h1 : (1 : ZMod p).val = 1 := ZMod.val_one p
    intro h; rw [h, ZMod.val_zero] at h1; exact one_ne_zero h1.symm
  have h_two_ne_zero : (2 : ZMod p) ≠ 0 := val_2_ne_zero
  refine ⟨fun h_sll => ?_, fun h_sllw => ?_⟩
  · rcases b_sllw with h | h
    · exact h
    · exfalso
      have : Main[62] + Main[63] = 2 := by rw [h_sll, h]; ring
      rcases sum_disj with hs | hs
      · apply h_two_ne_zero; linear_combination hs - this
      · apply h_one_ne_zero; linear_combination hs - this
  · rcases b_sll with h | h
    · exact h
    · exfalso
      have : Main[62] + Main[63] = 2 := by rw [h, h_sllw]; ring
      rcases sum_disj with hs | hs
      · apply h_two_ne_zero; linear_combination hs - this
      · apply h_one_ne_zero; linear_combination hs - this

/-- Derive `Main[62] + Main[63] = 1` from cstrs + `Main[62] = 1`. -/
lemma is_real_eq_one_of_sll (Main : Vector (ZMod p) 65)
    (cstrs : (constraints Main).allHold_poly) (h_sll : Main[62] = 1) :
    Main[62] + Main[63] = 1 := by
  have ⟨hno_sllw, _⟩ := single_op_poly Main cstrs
  rw [h_sll, hno_sllw h_sll]; ring

/-- Derive `Main[62] + Main[63] = 1` from cstrs + `Main[63] = 1`. -/
lemma is_real_eq_one_of_sllw (Main : Vector (ZMod p) 65)
    (cstrs : (constraints Main).allHold_poly) (h_sllw : Main[63] = 1) :
    Main[62] + Main[63] = 1 := by
  have ⟨_, hno_sll⟩ := single_op_poly Main cstrs
  rw [hno_sll h_sllw, h_sllw]; ring

end opcodes

section bounds

/-- Determine which opcode flag is set, given the sum constraint. -/
lemma sll_or_sllw_of_real (Main : Vector (ZMod p) 65)
    (cstrs : (constraints Main).allHold_poly)
    (h_real : Main[62] + Main[63] = 1) :
    Main[62] = 1 ∧ Main[63] = 0 ∨ Main[62] = 0 ∧ Main[63] = 1 := by
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  change List.Forall SP1Constraint.toProp_poly (constraints Main) at cstrs
  rw [allHold_constraints_iff_poly] at cstrs
  obtain ⟨_, _, _, _, b_62, b_63, _⟩ := cstrs
  have hp : 2 ^ 17 < p := Fact.out
  haveI : Fact (1 < p) := ⟨by omega⟩
  have h_one_val : (1 : ZMod p).val = 1 := ZMod.val_one p
  rcases b_62 with h62 | h62
  · -- Main[62] = 0, so Main[63] = 1
    have h63 : Main[63] = 1 := by
      have h := h_real; rw [h62, zero_add] at h; exact h
    exact Or.inr ⟨h62, h63⟩
  · -- Main[62] = 1
    have h63 : Main[63] = 0 := by
      rcases b_63 with h | h
      · exact h
      · exfalso
        have h_two_eq_one : (1 : ZMod p) + 1 = 1 := by
          have hh := h_real; rw [h62, h] at hh; exact hh
        have h_one_eq_zero : (1 : ZMod p) = 0 := by linear_combination h_two_eq_one
        rw [h_one_eq_zero, ZMod.val_zero] at h_one_val
        exact absurd h_one_val (by omega)
    exact Or.inl ⟨h62, h63⟩

set_option maxHeartbeats 8000000 in
-- ops_U64_b_c_poly: ALU iff for op_b, case-splits SLL vs SLLW for op_c's bound under imm=1.
lemma ops_U64_b_c_poly (Main : Vector (ZMod p) 65)
    (cstrs : (constraints Main).allHold_poly)
    (h_real : Main[62] + Main[63] = 1) :
    Word.isU64_poly #v[Main[15], Main[16], Main[17], Main[18]] ∧
    Word.isU64_poly #v[Main[25], Main[26], Main[27], Main[28]] := by
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  have hp : 2 ^ 17 < p := Fact.out
  have h_disj := sll_or_sllw_of_real Main cstrs h_real
  change List.Forall SP1Constraint.toProp_poly (constraints Main) at cstrs
  rw [allHold_constraints_iff_poly] at cstrs
  obtain ⟨_, _, alu, _⟩ := cstrs
  rw [ALUTypeReader.allHold_constraints_iff_is_real_poly h_real rfl] at alu
  -- Force projection reduction on the cols struct literal so destructure sees Main[i].
  dsimp only at alu
  obtain ⟨h_trusted, _, _, _, _, _, b_imm, _, _, _, _, _, _, _, _,
          _, h_is_U64_b, h_imm0, _, h_imm1_op_c⟩ := alu
  refine ⟨h_is_U64_b, ?_⟩
  rcases b_imm with h_imm0_eq | h_imm1_eq
  · exact (h_imm0 h_imm0_eq).2.2
  · -- imm = 1: op_c_memory.prev_value = op_c; trusted_instr gives c0 < 2^k, c1..c3 = 0
    have h_imm1_ne_0 : ¬ Main[31] = 0 := fun h0 => one_ne_zero (h_imm1_eq ▸ h0.symm).symm
    have ⟨e_25, e_26, e_27, e_28⟩ := h_imm1_op_c h_imm1_ne_0
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ] at e_25 e_26 e_27 e_28
    rw [e_25, e_26, e_27, e_28]
    -- Convert the imm=1 hypothesis to the form ALU iff uses.
    rcases h_disj with ⟨h_sll, h_no_sllw⟩ | ⟨h_no_sll, h_sllw⟩
    · -- SLL: opcode .val = 6
      have h_opc : ((Main[62] * 6 + Main[63] * 21 : ZMod p)).val = 6 := by
        rw [h_sll, h_no_sllw]
        have hp_lt : 131072 < p := by have := hp; omega
        have key : (1 * ((6 : ℕ) : ZMod p) + 0 * 21) = ((6 : ℕ) : ZMod p) := by push_cast; ring
        rw [key, ZMod.val_natCast_of_lt (show (6 : ℕ) < p by omega)]
      simp only [h_opc, show Opcode.ofNat 6 = .SLL from rfl,
        Opcode.trusted_instr_poly] at h_trusted
      have h_si : shift_i_type_constraints_poly Main[6] Main[14] 0 0 0 Main[21] Main[22] Main[23] Main[24] 0 Main[31] := by
        exact h_trusted.2 h_imm1_eq
      simp only [shift_i_type_constraints_poly] at h_si
      obtain ⟨_, _, h_c0_lt, h_c1, h_c2, h_c3⟩ := h_si
      apply Word.isU64_of_cases_poly
      · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero]
        have hp_lt : 131072 < p := by have := hp; omega
        have h64_pow : (2 ^ 6 : ZMod p).val = 64 := by
          rw [show (2 ^ 6 : ZMod p) = ((64 : ℕ) : ZMod p) from by push_cast; ring]
          exact ZMod.val_natCast_of_lt (by omega)
        have : Main[21].val < (2 ^ 6 : ZMod p).val := h_c0_lt
        rw [h64_pow] at this; omega
      · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
          List.getElem_cons_zero, h_c1, ZMod.val_zero]; omega
      · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
          List.getElem_cons_zero, h_c2, ZMod.val_zero]; omega
      · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
          List.getElem_cons_zero, h_c3, ZMod.val_zero]; omega
    · -- SLLW: opcode .val = 21
      have h_opc : ((Main[62] * 6 + Main[63] * 21 : ZMod p)).val = 21 := by
        rw [h_no_sll, h_sllw]
        have hp_lt : 131072 < p := by have := hp; omega
        have key : (0 * ((6 : ℕ) : ZMod p) + 1 * 21) = ((21 : ℕ) : ZMod p) := by push_cast; ring
        rw [key, ZMod.val_natCast_of_lt (show (21 : ℕ) < p by omega)]
      simp only [h_opc, show Opcode.ofNat 21 = .SLLW from rfl,
        Opcode.trusted_instr_poly] at h_trusted
      have h_wsi : w_shift_i_type_constraints_poly Main[6] Main[14] 0 0 0 Main[21] Main[22] Main[23] Main[24] 0 Main[31] := by
        exact h_trusted.2 h_imm1_eq
      simp only [w_shift_i_type_constraints_poly] at h_wsi
      obtain ⟨_, _, h_c0_lt, h_c1, h_c2, h_c3⟩ := h_wsi
      apply Word.isU64_of_cases_poly
      · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero]
        have hp_lt : 131072 < p := by have := hp; omega
        have h32_pow : (2 ^ 5 : ZMod p).val = 32 := by
          rw [show (2 ^ 5 : ZMod p) = ((32 : ℕ) : ZMod p) from by push_cast; ring]
          exact ZMod.val_natCast_of_lt (by omega)
        have : Main[21].val < (2 ^ 5 : ZMod p).val := h_c0_lt
        rw [h32_pow] at this; omega
      · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
          List.getElem_cons_zero, h_c1, ZMod.val_zero]; omega
      · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
          List.getElem_cons_zero, h_c2, ZMod.val_zero]; omega
      · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
          List.getElem_cons_zero, h_c3, ZMod.val_zero]; omega

set_option maxHeartbeats 16000000 in
-- bounds_poly threads the ALU iff and trusted_instr decomposition across the SLL vs SLLW opcode paths.
lemma bounds_poly (Main : Vector (ZMod p) 65)
    (cstrs : (constraints Main).allHold_poly)
    (h_real : Main[62] + Main[63] = 1) :
    let imm := Main[31]
    Main[6].val < 32 ∧ Main[14].val < 32 ∧ (imm = 0 → Main[21].val < 32) ∧
    Main[3].val < 65536 ∧
    Word.isU64_poly #v[Main[15], Main[16], Main[17], Main[18]] ∧
    Word.isU64_poly #v[Main[25], Main[26], Main[27], Main[28]] ∧
    (imm = 1 →
      (Main[21] = Main[25] ∧ Main[26] = 0 ∧ Main[27] = 0 ∧ Main[28] = 0 ∧
        ((Main[62] = 1 → Main[25].val < 64) ∧
         (Main[63] = 1 → Main[25].val < 32)))) ∧
    (Main[6] = 0 → Main[32] = 0 ∧ Main[33] = 0 ∧ Main[34] = 0 ∧ Main[35] = 0) := by
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  have hp : 2 ^ 17 < p := Fact.out
  have h_p_lt : 131072 < p := by omega
  have h32 : (32 : ZMod p).val = 32 := val_32_zmod_p
  have h65536 : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
  -- Get isU64 facts up front via ops_U64_b_c_poly.
  have ⟨is_U64_b, is_U64_c⟩ := ops_U64_b_c_poly Main cstrs h_real
  -- Get the opcode disjunction.
  have h_disj := sll_or_sllw_of_real Main cstrs h_real
  -- Open chip iff. Take only what we need.
  change List.Forall SP1Constraint.toProp_poly (constraints Main) at cstrs
  rw [allHold_constraints_iff_poly] at cstrs
  obtain ⟨_, _, alu, rest⟩ := cstrs
  -- Main[13] = 0 is the very last conjunct in the rest tuple. Extract by `And.right` chain via tauto/rfl.
  have h_M13 : Main[13] = 0 := by
    -- The structure of `rest` ends in `... ∧ Main[64] = Main[63] * Main[31] ∧ Main[13] = 0`.
    -- Use right_assoc projection.
    exact rest.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [ALUTypeReader.allHold_constraints_iff_is_real_poly h_real rfl] at alu
  dsimp only at alu
  obtain ⟨h_trusted, h_op_a_lt, _h_op_b_lt, _h_op_c_lts, _, h_op_a_0_iff, b_imm, _,
          h_pc0_lt, _, _, _, _, _, _, _, _, h_imm0, h_op_a_0_zeros, h_imm1_op_c⟩ := alu
  -- Item 1: Main[6].val < 32
  have h_a_lt : Main[6].val < 32 := by
    have : Main[6].val < (32 : ZMod p).val := h_op_a_lt
    rwa [h32] at this
  -- Item 4: Main[3].val < 65536
  have h_pc_lt : Main[3].val < 65536 := by
    have : Main[3].val < (65536 : ZMod p).val := h_pc0_lt
    rwa [h65536] at this
  -- Items 2, 3, 7 need the opcode case-split.
  rcases h_disj with ⟨h_sll, h_no_sllw⟩ | ⟨h_no_sll, h_sllw⟩
  · -- SLL case: opcode = 6
    have h_opc : ((Main[62] * 6 + Main[63] * 21 : ZMod p)).val = 6 := by
      rw [h_sll, h_no_sllw]
      have key : (1 * ((6 : ℕ) : ZMod p) + 0 * 21) = ((6 : ℕ) : ZMod p) := by push_cast; ring
      rw [key, ZMod.val_natCast_of_lt (show (6 : ℕ) < p by omega)]
    simp only [h_opc, show Opcode.ofNat 6 = .SLL from rfl,
      Opcode.trusted_instr_poly] at h_trusted
    -- For each goal, expose the right branch of h_trusted via b_imm
    refine ⟨h_a_lt, ?_, ?_, h_pc_lt, is_U64_b, is_U64_c, ?_, ?_⟩
    · -- Main[14].val < 32 from trusted_instr (either r_type or shift_i_type both give it)
      rcases b_imm with h_imm | h_imm
      · have ⟨_, ⟨h_lt, _⟩, _⟩ := h_trusted.1 h_imm
        have : Main[14].val < (32 : ZMod p).val := h_lt; rwa [h32] at this
      · have ⟨_, ⟨h_lt, _⟩, _⟩ := h_trusted.2 h_imm
        have : Main[14].val < (32 : ZMod p).val := h_lt; rwa [h32] at this
    · -- imm = 0 → Main[21].val < 32 from r_type's op_c[0] < 32
      intro h_imm0_eq
      have ⟨_, _, h_lt, _⟩ := h_trusted.1 h_imm0_eq
      have : Main[21].val < (32 : ZMod p).val := h_lt; rwa [h32] at this
    · -- imm = 1 → ...
      intro h_imm1_eq
      have h_imm1_ne_0 : ¬ Main[31] = 0 := fun h0 => one_ne_zero (h_imm1_eq ▸ h0.symm).symm
      have ⟨e_25, e_26, e_27, e_28⟩ := h_imm1_op_c h_imm1_ne_0
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ] at e_25 e_26 e_27 e_28
      have ⟨_, _, h_c0_lt, h_c1, h_c2, h_c3⟩ := h_trusted.2 h_imm1_eq
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ] at h_c1 h_c2 h_c3
      refine ⟨e_25.symm, e_26.trans h_c1, e_27.trans h_c2, e_28.trans h_c3, ?_, ?_⟩
      · intro _h_62_one
        rw [e_25]
        have h64_pow : (2 ^ 6 : ZMod p).val = 64 := by
          rw [show (2 ^ 6 : ZMod p) = ((64 : ℕ) : ZMod p) from by push_cast; ring]
          exact ZMod.val_natCast_of_lt (by omega)
        have : Main[21].val < (2 ^ 6 : ZMod p).val := h_c0_lt
        rw [h64_pow] at this; omega
      · intro h_63_one
        exfalso
        rw [h_no_sllw] at h_63_one
        exact zero_ne_one h_63_one
    · -- Main[6] = 0 → zeros. Use h_op_a_0_iff and h_M13.
      intro h_a0_eq
      exfalso
      have h13_eq_one : Main[13] = 1 := h_op_a_0_iff.mpr h_a0_eq
      rw [h_M13] at h13_eq_one
      exact zero_ne_one h13_eq_one
  · -- SLLW case: opcode = 21
    have h_opc : ((Main[62] * 6 + Main[63] * 21 : ZMod p)).val = 21 := by
      rw [h_no_sll, h_sllw]
      have key : (0 * ((6 : ℕ) : ZMod p) + 1 * 21) = ((21 : ℕ) : ZMod p) := by push_cast; ring
      rw [key, ZMod.val_natCast_of_lt (show (21 : ℕ) < p by omega)]
    simp only [h_opc, show Opcode.ofNat 21 = .SLLW from rfl,
      Opcode.trusted_instr_poly] at h_trusted
    refine ⟨h_a_lt, ?_, ?_, h_pc_lt, is_U64_b, is_U64_c, ?_, ?_⟩
    · rcases b_imm with h_imm | h_imm
      · have ⟨_, ⟨h_lt, _⟩, _⟩ := h_trusted.1 h_imm
        have : Main[14].val < (32 : ZMod p).val := h_lt; rwa [h32] at this
      · have ⟨_, ⟨h_lt, _⟩, _⟩ := h_trusted.2 h_imm
        have : Main[14].val < (32 : ZMod p).val := h_lt; rwa [h32] at this
    · intro h_imm0_eq
      have ⟨_, _, h_lt, _⟩ := h_trusted.1 h_imm0_eq
      have : Main[21].val < (32 : ZMod p).val := h_lt; rwa [h32] at this
    · intro h_imm1_eq
      have h_imm1_ne_0 : ¬ Main[31] = 0 := fun h0 => one_ne_zero (h_imm1_eq ▸ h0.symm).symm
      have ⟨e_25, e_26, e_27, e_28⟩ := h_imm1_op_c h_imm1_ne_0
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ] at e_25 e_26 e_27 e_28
      have ⟨_, _, h_c0_lt, h_c1, h_c2, h_c3⟩ := h_trusted.2 h_imm1_eq
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ] at h_c1 h_c2 h_c3
      refine ⟨e_25.symm, e_26.trans h_c1, e_27.trans h_c2, e_28.trans h_c3, ?_, ?_⟩
      · intro h_62_one
        exfalso
        rw [h_no_sll] at h_62_one
        exact zero_ne_one h_62_one
      · intro _h_63_one
        rw [e_25]
        have h32_pow : (2 ^ 5 : ZMod p).val = 32 := by
          rw [show (2 ^ 5 : ZMod p) = ((32 : ℕ) : ZMod p) from by push_cast; ring]
          exact ZMod.val_natCast_of_lt (by omega)
        have : Main[21].val < (2 ^ 5 : ZMod p).val := h_c0_lt
        rw [h32_pow] at this; omega
    · intro h_a0_eq
      exfalso
      have h13_eq_one : Main[13] = 1 := h_op_a_0_iff.mpr h_a0_eq
      rw [h_M13] at h13_eq_one
      exact zero_ne_one h13_eq_one

end bounds

section operands

@[simp] def sp1_op_a_poly (Main : Vector (ZMod p) 65) : BitVec 5 :=
  BitVec.ofNat 5 Main[6].val
@[simp] def sp1_op_b_poly (Main : Vector (ZMod p) 65) : BitVec 5 :=
  BitVec.ofNat 5 Main[14].val
@[simp] def sp1_op_c_poly (Main : Vector (ZMod p) 65) : BitVec 5 :=
  BitVec.ofNat 5 Main[21].val
@[simp] def sp1_op_c_imm_poly (Main : Vector (ZMod p) 65) : BitVec 6 :=
  BitVec.ofNat 6 Main[21].val
@[simp] def sp1_op_c_imm_w_poly (Main : Vector (ZMod p) 65) : BitVec 5 :=
  BitVec.ofNat 5 Main[21].val

end operands

end ShiftLeft
