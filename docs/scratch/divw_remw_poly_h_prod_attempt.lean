              have h_prod : HWord.toInt_poly #v[b0, b1] = HWord.toInt_poly #v[q0, q1] * HWord.toInt_poly #v[c0, c1] + HWord.toInt_poly #v[r0, r1] := by
                -- Bounds for sign-extension constants (msb_* ∈ {0,1}, * 65535 < 65536)
                have u16_msb_b_v : (msb_b * 65535).val < 65536 := by
                  rw [w_eq_msb_b]; split_ifs <;> simp [h0v, h65535_val]
                have u16_msb_c_v : (msb_c * 65535).val < 65536 := by
                  rw [w_eq_msb_c]; split_ifs <;> simp [h0v, h65535_val]
                have u16_msb_rem_v : (msb_rem * 65535).val < 65536 := by
                  rw [w_eq_msb_rem]; split_ifs <;> simp [h0v, h65535_val]
                have u16_msb_quot_v : (msb_quot * 65535).val < 65536 := by
                  rw [w_eq_msb_quot]; split_ifs <;> simp [h0v, h65535_val]
                have heq32_b1 : (32768 : ZMod p) ≤ b1 ↔ 32768 ≤ b1.val := by
                  change (32768 : ZMod p).val ≤ b1.val ↔ _; rw [h32768_val]
                have heq32_c1 : (32768 : ZMod p) ≤ c1 ↔ 32768 ≤ c1.val := by
                  change (32768 : ZMod p).val ≤ c1.val ↔ _; rw [h32768_val]
                obtain ⟨is_U64_ctql, ctq_low⟩ := main_mul_low
                -- 4-limb sign-extended forms of b, c, q, r as HWord.extend_poly _ true.
                have eq_eb : (#v[b0, b1, msb_b * 65535, msb_b * 65535] : Word (ZMod p)) =
                    HWord.extend_poly #v[b0, b1] true := by
                  simp [HWord.extend_poly, HWord.isNegative_poly, w_eq_msb_b, heq32_b1]
                have eq_er : (#v[r0, r1, msb_rem * 65535, msb_rem * 65535] : Word (ZMod p)) =
                    HWord.extend_poly #v[r0, r1] true := by
                  simp [HWord.extend_poly, HWord.isNegative_poly, w_eq_msb_rem, heq32_r1]
                have eq_eq : (#v[q0, q1, msb_quot * 65535, msb_quot * 65535] : Word (ZMod p)) =
                    HWord.extend_poly #v[q0, q1] true := by
                  simp [HWord.extend_poly, HWord.isNegative_poly, w_eq_msb_quot, heq32_q1]
                have eq_ec : (#v[c0, c1, msb_c * 65535, msb_c * 65535] : Word (ZMod p)) =
                    HWord.extend_poly #v[c0, c1] true := by
                  simp [HWord.extend_poly, HWord.isNegative_poly, w_eq_msb_c, heq32_c1]
                -- Stage B suffices: prove the 4-limb BitVec64 carry-chain equality.
                suffices bv_ctqr :
                  Word.toBitVec64_poly (#v[b0, b1, msb_b * 65535, msb_b * 65535] : Word (ZMod p)) =
                    Word.toBitVec64_poly (#v[ctq0, ctq1, ctq2, ctq3] : Word (ZMod p)) +
                    Word.toBitVec64_poly (#v[r0, r1, msb_rem * 65535, msb_rem * 65535] : Word (ZMod p)) by
                  -- Stage A: derive h_prod from bv_ctqr via signed multiplication.
                  rw [eq_eb, eq_er] at bv_ctqr
                  -- ctq_low : Word.toBitVec64_poly #v[ctq0..3] = execute_MUL_pure ... mop.MUL
                  -- The qbc2/3 in ctq_low's argument become msb_quot * 65535 after subst.
                  -- The c2/3 expression: c2 * (1 - is_word) + c_neg * is_word * 65535 with
                  -- is_word=1, c_neg=msb_c → 0 + msb_c * 65535 = msb_c * 65535.
                  simp [execute_MUL_pure, -BitVec.extractLsb] at ctq_low
                  -- bv_decide: extending to 128 bits with False vs True agrees on the low 64 bits
                  -- of multiplication.
                  have hext_eq : BitVec.extractLsb 63 0
                      ((Word.toBitVec64_poly (#v[q0, q1, msb_quot * 65535, msb_quot * 65535] : Word (ZMod p))).extend 128 False *
                       (Word.toBitVec64_poly (#v[c0, c1, msb_c * 65535, msb_c * 65535] : Word (ZMod p))).extend 128 False) =
                    BitVec.extractLsb 63 0
                      ((Word.toBitVec64_poly (#v[q0, q1, msb_quot * 65535, msb_quot * 65535] : Word (ZMod p))).extend 128 True *
                       (Word.toBitVec64_poly (#v[c0, c1, msb_c * 65535, msb_c * 65535] : Word (ZMod p))).extend 128 True) := by
                    simp [BitVec.extend, -BitVec.extractLsb]; bv_decide
                  rw [hext_eq] at ctq_low; clear hext_eq
                  rw [eq_eq, eq_ec] at ctq_low
                  simp only [← BitVec.toInt_inj] at ctq_low
                  have is_U32_ql' : HWord.isU32_poly (#v[q0, q1] : HWord (ZMod p)) := by
                    apply HWord.isU32_of_cases_poly <;> simpa
                  have is_U32_cl' : HWord.isU32_poly (#v[c0, c1] : HWord (ZMod p)) := by
                    apply HWord.isU32_of_cases_poly <;> simpa
                  have hmul_int :
                      ((HWord.extend_poly (#v[q0, q1] : HWord (ZMod p)) true).toBitVec64_poly.extend 128 True *
                       (HWord.extend_poly (#v[c0, c1] : HWord (ZMod p)) true).toBitVec64_poly.extend 128 True).toInt =
                      HWord.toInt_poly (#v[q0, q1] : HWord (ZMod p)) * HWord.toInt_poly (#v[c0, c1] : HWord (ZMod p)) := by
                    iterate 2 rw [HWord.extend_true_is_signExtend_poly (by assumption)]
                    simp [BitVec.extend, BitVec.toInt_signExtend_of_le]
                    iterate 2 rw [HWord.toBitVec32_poly_toInt_poly (by assumption)]
                    rw [Int.bmod_eq_of_le] <;> simp <;> nlinarith
                  rw [extractLsb_is_toInt (by rw [hmul_int]; nlinarith) (by rw [hmul_int]; nlinarith)] at ctq_low
                  rw [hmul_int] at ctq_low; clear hmul_int
                  simp [← BitVec.toInt_inj, ctq_low] at bv_ctqr
                  iterate 2 rw [HWord.extend_true_is_signExtend_poly (by assumption),
                                BitVec.toInt_signExtend_of_le (by simp),
                                HWord.toBitVec32_poly_toInt_poly (by assumption)] at bv_ctqr
                  rw [bv_ctqr]
                  rw [Int.bmod_eq_of_le] <;> simp <;> nlinarith
                · -- Stage B: prove bv_ctqr via 4-limb carry chain. Mirror divuw_remuw_poly's
                  -- pattern (hsum/eq/main_eq) but with sign-extension constants in upper limbs.
                  have hcs_b := HWord.lt_cases_of_isU32_poly is_U32_bl
                  have hcs_r := HWord.lt_cases_of_isU32_poly is_U32_rl
                  have hcs_c := HWord.lt_cases_of_isU32_poly is_U32_cl
                  have hcs_q := HWord.lt_cases_of_isU32_poly is_U32_ql
                  have hcs_ctq := Word.lt_cases_of_isU64_poly is_U64_ctql
                  obtain ⟨b0_lt, b1_lt⟩ := hcs_b
                  obtain ⟨c0_lt, c1_lt⟩ := hcs_c
                  obtain ⟨q0_lt, q1_lt⟩ := hcs_q
                  obtain ⟨r0_lt, r1_lt⟩ := hcs_r
                  obtain ⟨ctq0_lt, ctq1_lt, ctq2_lt, ctq3_lt⟩ := hcs_ctq
                  -- Rearrange `nof_eq_ctqpr_i` to `... + cry_{i-1} - cry_i * 65536` form.
                  rw [← add_sub_right_comm] at u16_ctqpr1 u16_ctqpr2 u16_ctqpr3
                                              nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3
                  -- Apply div_mod_decomposition_w_poly to get .val % / / forms.
                  rw [div_mod_decomposition_w_poly (by omega) (by omega : cry0.val < 2)] at nof_eq_ctqpr0
                  rw [div_mod_decomposition_w_poly (by omega) (by omega : cry1.val < 2)] at nof_eq_ctqpr1
                  rw [div_mod_decomposition_w_poly (by omega) (by omega : cry2.val < 2)] at nof_eq_ctqpr2
                  rw [div_mod_decomposition_w_poly (by omega) (by omega : cry3.val < 2)] at nof_eq_ctqpr3
                  -- Distribute .val over + via ZMod.val_add_of_lt.
                  have hsum01 : (ctq0 + r0).val = ctq0.val + r0.val :=
                    ZMod.val_add_of_lt (by omega)
                  have hsum1' : (ctq1 + r1).val = ctq1.val + r1.val :=
                    ZMod.val_add_of_lt (by omega)
                  have hsum1 : (ctq1 + r1 + cry0).val = ctq1.val + r1.val + cry0.val := by
                    rw [show (ctq1 + r1 + cry0) = (ctq1 + r1) + cry0 from rfl,
                        ZMod.val_add_of_lt (by rw [hsum1']; omega), hsum1']
                  have hsum2' : (ctq2 + msb_rem * 65535).val = ctq2.val + (msb_rem * 65535).val :=
                    ZMod.val_add_of_lt (by omega)
                  have hsum2 : (ctq2 + msb_rem * 65535 + cry1).val =
                      ctq2.val + (msb_rem * 65535).val + cry1.val := by
                    rw [show (ctq2 + msb_rem * 65535 + cry1) = (ctq2 + msb_rem * 65535) + cry1 from rfl,
                        ZMod.val_add_of_lt (by rw [hsum2']; omega), hsum2']
                  have hsum3' : (ctq3 + msb_rem * 65535).val = ctq3.val + (msb_rem * 65535).val :=
                    ZMod.val_add_of_lt (by omega)
                  have hsum3 : (ctq3 + msb_rem * 65535 + cry2).val =
                      ctq3.val + (msb_rem * 65535).val + cry2.val := by
                    rw [show (ctq3 + msb_rem * 65535 + cry2) = (ctq3 + msb_rem * 65535) + cry2 from rfl,
                        ZMod.val_add_of_lt (by rw [hsum3']; omega), hsum3']
                  -- Build clean Nat-side carry equations (eq_i : LHS = RHS).
                  have eq0 : b0.val + cry0.val * 65536 = ctq0.val + r0.val := by
                    obtain ⟨h1, h2⟩ := nof_eq_ctqpr0; rw [hsum01] at h1 h2; omega
                  have eq1 : b1.val + cry1.val * 65536 = ctq1.val + r1.val + cry0.val := by
                    obtain ⟨h1, h2⟩ := nof_eq_ctqpr1; rw [hsum1] at h1 h2; omega
                  have eq2 : (msb_b * 65535).val + cry2.val * 65536 =
                      ctq2.val + (msb_rem * 65535).val + cry1.val := by
                    obtain ⟨h1, h2⟩ := nof_eq_ctqpr2; rw [hsum2] at h1 h2; omega
                  have eq3 : (msb_b * 65535).val + cry3.val * 65536 =
                      ctq3.val + (msb_rem * 65535).val + cry2.val := by
                    obtain ⟨h1, h2⟩ := nof_eq_ctqpr3; rw [hsum3] at h1 h2; omega
                  -- Linear combination weighted by 2^(16i): the cry_{i} terms telescope.
                  have main_eq :
                      b0.val + b1.val * 65536 + (msb_b * 65535).val * 4294967296 +
                        (msb_b * 65535).val * 281474976710656 +
                        cry3.val * 18446744073709551616 =
                      ctq0.val + ctq1.val * 65536 + ctq2.val * 4294967296 +
                        ctq3.val * 281474976710656 +
                      (r0.val + r1.val * 65536 + (msb_rem * 65535).val * 4294967296 +
                        (msb_rem * 65535).val * 281474976710656) := by
                    omega
                  -- Lift to BitVec equality via ← BitVec.toNat_inj + BitVec.toNat_add.
                  rw [← BitVec.toNat_inj]
                  rw [BitVec.toNat_add]
                  rw [show Word.toBitVec64_poly (#v[b0, b1, msb_b * 65535, msb_b * 65535] : Word (ZMod p)) =
                        BitVec.ofNat 64 (b0.val + b1.val * 65536 +
                          (msb_b * 65535).val * 4294967296 +
                          (msb_b * 65535).val * 281474976710656) from by
                        simp [Word.toBitVec64_poly, Word.toNat_poly]]
                  rw [show Word.toBitVec64_poly (#v[ctq0, ctq1, ctq2, ctq3] : Word (ZMod p)) =
                        BitVec.ofNat 64 (ctq0.val + ctq1.val * 65536 +
                          ctq2.val * 4294967296 + ctq3.val * 281474976710656) from by
                        simp [Word.toBitVec64_poly, Word.toNat_poly]]
                  rw [show Word.toBitVec64_poly (#v[r0, r1, msb_rem * 65535, msb_rem * 65535] : Word (ZMod p)) =
                        BitVec.ofNat 64 (r0.val + r1.val * 65536 +
                          (msb_rem * 65535).val * 4294967296 +
                          (msb_rem * 65535).val * 281474976710656) from by
                        simp [Word.toBitVec64_poly, Word.toNat_poly]]
                  simp only [BitVec.toNat_ofNat]
                  omega
