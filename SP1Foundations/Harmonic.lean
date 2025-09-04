import Mathlib

section bitvec

theorem useless_signExtend (BB : ℕ) {x : Fin BB} {hx : x.val < 2^12} :
    let bx64 : BitVec 64 := BitVec.ofNatLT x (by linarith)
    bx64 % 4 = (BitVec.signExtend 64 (BitVec.ofNatLT (w := 12) x (by linarith))) % 4 := by
  sorry
  -- extract_lets bx64
  -- have hx_bb : x.val < BB := x.isLt
  -- have hx_64 : x.val < 2^64 := by omega

  -- -- Now prove using bit representation
  -- apply BitVec.eq_of_toNat_eq
  -- simp only [BitVec.toNat_umod, BitVec.toNat_ofNat]
  -- have h_bx64 : bx64.toNat = x.val := by
  --   simp [bx64, BitVec.toNat_ofNatLT]
  -- let bx12 : BitVec 12 := BitVec.ofNatLT x.val hx
  -- have h_bx12 : bx12.toNat = x.val := by
  --   simp [bx12, BitVec.toNat_ofNatLT]
  -- have h_sign_ext : (BitVec.signExtend 64 bx12).toNat % 4 = x.val % 4 := by
  --   simp only [BitVec.toNat_signExtend, BitVec.toNat_setWidth]
  --   split_ifs with hmsb
  --   · have hsub_mod : (2^64 - 2^12) % 4 = 0 := by norm_num
  --     rw [Nat.add_mod, hsub_mod, Nat.add_zero]
  --     have : bx12.toNat < 2^64 := by
  --       rw [h_bx12]
  --       exact hx_64
  --     rw [Nat.mod_eq_of_lt this, h_bx12, Nat.mod_mod_of_dvd]
  --     norm_num
  --   · simp [Nat.add_zero]
  --     have : bx12.toNat < 2^64 := by
  --       rw [h_bx12]
  --       exact hx_64
  --     rw [h_bx12]
  -- have h4 : (4 : BitVec 64).toNat = 4 := by simp
  -- rw [h4]
  -- rw [h_bx64]
  -- have : bx12 = BitVec.ofNatLT (w := 12) x.val hx := rfl
  -- rw [← this, ← h_sign_ext]

end bitvec

section int

lemma sign_cases (a : ℤ) : a.sign = if a < 0 then -1 else if a = 0 then 0 else 1 := by
  sorry
  -- by_cases a = 0
  -- . simp_all
  -- . by_cases 0 < a
  --   . rw [Int.sign_eq_one_of_pos (by omega)]; omega
  --   . rw [Int.sign_eq_neg_one_of_neg (by omega)]; omega

lemma div_overflow {x y : ℤ} :
  -9223372036854775808 ≤ x ∧ x < 9223372036854775808 →
    -9223372036854775808 ≤ y ∧ y < 9223372036854775808 →
      (9223372036854775808 ≤ x.tdiv y ↔ x = -9223372036854775808 ∧ y = -1) := by
  sorry
  -- intro hx hy
  -- constructor <;> intro hc
  -- have : (x.tdiv y).sign = 1 := by rw [Int.sign_cases, if_neg (by omega), if_neg (by omega)]
  -- rw [Int.sign_tdiv] at this
  -- split_ifs at this with hyp <;> [ simp_all; clear hyp ]
  -- . simp [Int.sign_cases] at this
  --   split_ifs at this <;> simp_all
  --   . suffices : -x = 9223372036854775808 ∧ -y = 1
  --     . omega
  --     . have eq : x.tdiv y = (-x).tdiv (-y) := by simp
  --       rw [eq, Int.tdiv_eq_ediv_of_nonneg (by omega)] at hc
  --       by_cases yone : -y = 1
  --       . simp_all; omega
  --       . have := @Int.ediv_lt_self_of_pos_of_ne_one (-x) (-y) (by omega) (by omega)
  --         omega
  --   . rw [Int.tdiv_eq_ediv_of_nonneg (by omega)] at hc
  --     by_cases yone : y = 1
  --     . simp_all; omega
  --     . have := @Int.ediv_lt_self_of_pos_of_ne_one x y (by omega) (by omega)
  --       omega
  -- . simp_all

end int

section field_arith

notation "BB" => 2013265921

lemma prime_BabyBearPrime : Nat.Prime BB := by native_decide

instance Fact_BBPrime : Fact (Nat.Prime BB) := ⟨prime_BabyBearPrime⟩
instance : NeZero BB := by constructor; decide

instance Fin.noZeroDivisors_of_prime (p : ℕ)
    [hp : Fact (Nat.Prime (p + 1))] : NoZeroDivisors (Fin (p + 1)) := by
  sorry
  -- refine IsDomain.to_noZeroDivisors (ZMod (p + 1))

instance : Field (Fin BB) := ZMod.instField BB
instance : NoZeroDivisors (Fin 2013265921) := Fin.noZeroDivisors_of_prime _ (hp := Fact_BBPrime)

@[simp] lemma mul_inv_16BB_eq_one_iff {x : Fin BB} :
    x * (65536 : Fin BB)⁻¹ = 1 ↔ x = 65536 := by rw [mul_inv_eq_one₀ (by trivial)]

@[simp] lemma inv_16BB_zero_or_one {x : Fin BB} :
    x * 65536⁻¹ = 0 ∨ x * 65536⁻¹ = 1 ↔ x = 0 ∨ x = 65536 := by aesop

set_option maxHeartbeats 1000000 in
lemma addrAddOperation_correct (a b : Vector (Fin BB) 4) (cols : Vector (Fin BB) 3)
  (ha : a[0].1 < 65536 ∧ a[1].1 < 65536 ∧ a[2].1 < 65536 ∧ a[3].1 < 65536)
  (hb : b[0].1 < 65536 ∧ b[1].1 < 65536 ∧ b[2].1 < 65536 ∧ b[3].1 < 65536)
  (h_cstrs :
    let carry0 : Fin BB := (a[0] + b[0] - cols[0]) * 65536⁻¹
    let carry1 : Fin BB := (a[1] + b[1] - cols[1] + carry0) * 65536⁻¹
    let carry2 : Fin BB := (a[2] + b[2] - cols[2] + carry1) * 65536⁻¹
    let carry3 : Fin BB := (a[3] + b[3] - 0 + carry2) * 65536⁻¹
    (carry0 = 0 ∨ carry0 = 1) ∧
    (carry1 = 0 ∨ carry1 = 1) ∧
    (carry2 = 0 ∨ carry2 = 1) ∧
    (carry3 = 0 ∨ carry3 = 1) ∧
    (cols[0].val < 65536) ∧
    (cols[1].val < 65536) ∧
    (cols[2].val < 65536)) :
    (a[0].val + a[1] * 65536 + ↑a[2] * 4294967296 + ↑a[3] * 281474976710656 +
      (↑b[0] + ↑b[1] * 65536 + ↑b[2] * 4294967296 + ↑b[3] * 281474976710656)) %
        18446744073709551616 < 281474976710656 := by
  sorry
  -- obtain ⟨h0, h1, h2, h3, hbd0, hbd1, hbd2⟩ := h_cstrs
  -- cases h0 <;> rename_i h0
  --   <;> simp [sub_eq_zero] at h0
  --   <;> simp [h0] at h1 h2 h3
  --   <;> cases h1 <;> rename_i h1
  --   <;> simp [sub_eq_zero] at h1
  --   <;> simp [h0, h1] at h2 h3
  --   <;> cases h2 <;> rename_i h2
  --   <;> simp [sub_eq_zero] at h2
  --   <;> simp [h0, h1, h2] at h3
  --   <;> cases h3 <;> rename_i h3
  --   <;> simp [sub_eq_zero] at h3
  --   <;> try omega

end field_arith
