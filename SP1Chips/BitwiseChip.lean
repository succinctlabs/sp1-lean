import SP1Operations

open BitVec

namespace BitwiseChip

section constraints

def constraints (Main : Vector BabyBear 33) : SP1ConstraintList :=
  let E0 : BabyBear := Main[30] + Main[31]
  let E1 : BabyBear := E0 + Main[32]
  let E2 : BabyBear := Main[30] - 1
  let E3 : BabyBear := Main[30] * E2
  let E4 : BabyBear := Main[31] - 1
  let E5 : BabyBear := Main[31] * E4
  let E6 : BabyBear := Main[32] - 1
  let E7 : BabyBear := Main[32] * E6
  let E8 : BabyBear := E1 - 1
  let E9 : BabyBear := E1 * E8
  let E10 : BabyBear := Main[30] * 2
  let E11 : BabyBear := Main[31] * 1
  let E12 : BabyBear := E10 + E11
  let E13 : BabyBear := Main[32] * 0
  let E14 : BabyBear := E12 + E13
  let E15 : BabyBear := Main[30] * 3
  let E16 : BabyBear := Main[31] * 4
  let E17 : BabyBear := E15 + E16
  let E18 : BabyBear := Main[32] * 5
  let E19 : BabyBear := E17 + E18
  let ⟨⟨⟨[E20, E21]⟩, _⟩, CS0⟩ := BitwiseU16Operation.constraints #v[Main[11], Main[12]] #v[Main[17], Main[18]] { b_low_bytes := { low_bytes := #v[Main[22], Main[23]] }, bitwise_operation := { result := #v[Main[26], Main[27], Main[28], Main[29]] }, c_low_bytes := { low_bytes := #v[Main[24], Main[25]] } } E14 E1
  let E22 : BabyBear := Main[3] + 4
  let CS1 : List SP1Constraint := CPUState.constraints { clk_0_16 := Main[2], clk_16_24 := Main[1], clk_high := Main[0], pc := Main[3] } E22 8 E1
  let E23 : BabyBear := Main[1] * 65536
  let E24 : BabyBear := Main[2] + E23
  let CS2 : List SP1Constraint := ALUTypeReader.constraints Main[0] E24 Main[3] E19 #v[E20, E21] { imm_c := Main[21], op_a := Main[4], op_a_0 := Main[9], op_a_memory := { access_timestamp := { diff_low_limb := Main[8], prev_low := Main[7] }, prev_value := #v[Main[5], Main[6]] }, op_b := Main[10], op_b_memory := { access_timestamp := { diff_low_limb := Main[14], prev_low := Main[13] }, prev_value := #v[Main[11], Main[12]] }, op_c := #v[Main[15], Main[16]], op_c_memory := { access_timestamp := { diff_low_limb := Main[20], prev_low := Main[19] }, prev_value := #v[Main[17], Main[18]] } } E1
  [
    .assertZero E3,
    .assertZero E5,
    .assertZero E7,
    .assertZero E9
  ] ++ CS0 ++ CS1 ++ CS2

lemma BitWiseU16_constraints_of_constraints (Main : Vector BabyBear 33)
    (h : (constraints Main).allHold) :
    (BitwiseU16Operation.constraints #v[Main[11], Main[12]] #v[Main[17], Main[18]]
      { b_low_bytes := { low_bytes := #v[Main[22], Main[23]] },
        bitwise_operation := { result := #v[Main[26], Main[27], Main[28], Main[29]] },
        c_low_bytes := { low_bytes := #v[Main[24], Main[25]] } }
        (Main[30] * 2 + Main[31] * 1)
        (Main[30] + Main[31] + Main[32])).2.allHold := by
  simp [constraints] at h
  simp [BitwiseU16Operation.constraints] at *
  tauto

def main_output (Main : Vector BabyBear 33) : BitVec 32 :=
  let E0 : BabyBear := Main[30] + Main[31]
  let E1 : BabyBear := E0 + Main[32]
  let E2 : BabyBear := Main[30] - 1
  let E3 : BabyBear := Main[30] * E2
  let E4 : BabyBear := Main[31] - 1
  let E5 : BabyBear := Main[31] * E4
  let E6 : BabyBear := Main[32] - 1
  let E7 : BabyBear := Main[32] * E6
  let E8 : BabyBear := E1 - 1
  let E9 : BabyBear := E1 * E8
  let E10 : BabyBear := Main[30] * 2
  let E11 : BabyBear := Main[31] * 1
  let E12 : BabyBear := E10 + E11
  let E13 : BabyBear := Main[32] * 0
  let E14 : BabyBear := E12 + E13
  let E15 : BabyBear := Main[30] * 3
  let E16 : BabyBear := Main[31] * 4
  let E17 : BabyBear := E15 + E16
  let E18 : BabyBear := Main[32] * 5
  let E19 : BabyBear := E17 + E18
  let ⟨⟨⟨[E20, E21]⟩, _⟩, CS0⟩ := BitwiseU16Operation.constraints
    #v[Main[11], Main[12]] #v[Main[17], Main[18]]
    { b_low_bytes := { low_bytes := #v[Main[22], Main[23]] },
      bitwise_operation := { result := #v[Main[26], Main[27], Main[28], Main[29]] },
      c_low_bytes := { low_bytes := #v[Main[24], Main[25]] } }
      E14
      E1
  BitVec.ofNat 32 (E20 + E21 * 65536)

end constraints

def specXor (Main : Vector BabyBear 33) : StateM SP1State Unit := do
  incrementPC
  let op_a := regidx.Regidx Main[4].val
  let op_b := regidx.Regidx Main[10].val
  let op_c := regidx.Regidx Main[15].val
  let b : BitVec 32 := (← get).2 op_b
  let c : BitVec 32 := (← get).2 op_c
  update_reg op_a (b ^^^ c)

def specAnd (Main : Vector BabyBear 33) : StateM SP1State Unit := do
  incrementPC
  let op_a := regidx.Regidx Main[4].val
  let op_b := regidx.Regidx Main[10].val
  let op_c := regidx.Regidx Main[15].val
  let b : BitVec 32 := (← get).2 op_b
  let c : BitVec 32 := (← get).2 op_c
  update_reg op_a (b &&& c)

def specOr (Main : Vector BabyBear 33) : StateM SP1State Unit := do
  incrementPC
  let op_a := regidx.Regidx Main[4].val
  let op_b := regidx.Regidx Main[10].val
  let op_c := regidx.Regidx Main[15].val
  let b : BitVec 32 := (← get).2 op_b
  let c : BitVec 32 := (← get).2 op_c
  update_reg op_a (b ||| c)

def sp1Bitwise (Main : Vector BabyBear 33) : StateM SP1State Unit := do
  incrementPC
  let op_a := regidx.Regidx Main[4].val
  update_reg op_a (main_output Main)

/-- If the constraints all hold, the column is real, and `op_b` and `op_c` are loaded
into the proper registers, then the add chip conforms to the spec. -/
theorem SP1BitwiseChip_xor_correct (Main : Vector BabyBear 33)
    (h_cstrs : SP1ConstraintList.allHold (constraints Main))
    (h_is_xor : Main[30] = 1) -- Is an `xor` operation
    (pc : BitVec 32) (reg_state : regidx → BitVec 32)
    (hmem₁ : reg_state (regidx.Regidx Main[10].val) = .ofNat 32 (Main[11] + Main[12] * 65536))
    (hmem₂ : reg_state (regidx.Regidx Main[15].val) = .ofNat 32 (Main[17] + Main[18] * 65536)) :
    (sp1Bitwise Main).run (pc, reg_state) = (specXor Main).run (pc, reg_state) := by
  unfold sp1Bitwise specXor
  rw [BitVec.natCast_eq_ofNat] at hmem₁ hmem₂

  have hbwu16 := BitWiseU16_constraints_of_constraints Main h_cstrs

  simp [constraints, BitwiseU16Operation.constraints] at h_cstrs
  obtain ⟨h1, h2, h3, h4, bw_cstrs, cpu_strs, adapter_cstrs⟩ := h_cstrs
  simp [h_is_xor, sub_eq_zero] at h1 h2 h3 h4

  have h31 : Main[31] = 0 := by
    rw [or_iff_not_imp_right] at h2
    refine h2 fun h2' => ?_
    rw [h2'] at h4
    cases h4 with
    | inl h4 =>
      cases h3 with
      | inl h3 =>
        simp [h3] at h4
      | inr h3 =>
        simp [h3] at h4
    | inr h4 =>
      cases h3 with
      | inl h3 =>
        simp [h3] at h4
      | inr h3 =>
        simp [h3] at h4
  have h32 : Main[32] = 0 := by
    rw [or_iff_not_imp_right] at h3
    refine h3 fun h3' => ?_
    rw [h3'] at h4
    cases h4 with
    | inl h4 =>
      cases h2 with
      | inl h2 =>
        simp [h2] at h4
      | inr h2 =>
        simp [h2] at h4
    | inr h4 =>
      cases h2 with
      | inl h2 =>
        simp [h2] at h4
      | inr h2 =>
        simp [h2] at h4

  simp [h_is_xor, h31, h32] at *

  have hbw0 := BitwiseOperation.lt_of_constraints _ _ _ 0 .XOR (Or.inr (Or.inr rfl)) bw_cstrs
  have hbw1 := BitwiseOperation.lt_of_constraints _ _ _ 1 .XOR (Or.inr (Or.inr rfl)) bw_cstrs
  have hbw2 := BitwiseOperation.lt_of_constraints _ _ _ 2 .XOR (Or.inr (Or.inr rfl)) bw_cstrs
  have hbw3 := BitwiseOperation.lt_of_constraints _ _ _ 3 .XOR (Or.inr (Or.inr rfl)) bw_cstrs

  have hxor0 := BitwiseOperation.eq_xor_of_constraints _ _ _ 0 bw_cstrs
  have hxor1 := BitwiseOperation.eq_xor_of_constraints _ _ _ 1 bw_cstrs
  have hxor2 := BitwiseOperation.eq_xor_of_constraints _ _ _ 2 bw_cstrs
  have hxor3 := BitwiseOperation.eq_xor_of_constraints _ _ _ 3 bw_cstrs

  simp at hbw0 hbw1 hbw2 hbw3 hxor0 hxor1 hxor2 hxor3

  -- The `RTypeReader` gives bounds on the size of previous memory values
  let op_b_memory_bound : Main[11].1 < 65536 ∧ Main[12].1 < 65536 :=
    ALUTypeReader.val_op_b_memory_lt_of_constraints adapter_cstrs
  let op_c_memory_bound : Main[17].1 < 65536 ∧ Main[18].1 < 65536 :=
    ALUTypeReader.val_op_c_memory_lt_of_constraints adapter_cstrs
  have hb1 : Main[11].val + Main[12].val * 65536 < 2 ^ 32 := by omega
  have hb2 : Main[17].val + Main[18].val * 65536 < 2 ^ 32 := by omega

  have htest := BitwiseU16Operation.eq_xor_word_sub_of_constraints _ _ _
    (by tauto) (by tauto) hbwu16
  have htest' := BitwiseU16Operation.eq_xor_word_sub_of_constraints' _ _ _
    (by tauto) (by tauto) hbwu16
  simp at htest htest'
  rw [hxor0, hxor1] at htest
  rw [hxor2, hxor3] at htest'

  -- simp [BabyBearPrime, BitVec.natCast_eq_ofNat, StateT.run_modify, StateT.run_bind,
  --   StateT.run_get, bind_pure_comp, map_pure, Prod.map_apply, id_eq]
  refine congr_arg (fun out => pure (_, (_, out))) (funext fun reg => ?_)
  by_cases hreg : (regidx.Regidx (BitVec.ofNat 5 ↑Main[4])) = reg
  · rw [hreg, Function.update_self, Function.update_self, hmem₁, hmem₂,]
    rw [main_output]
    simp [BitwiseU16Operation.constraints]

    have : (Main[25] + Main[29] * 256).val = Main[25].val + Main[29].val * 256 := by
      rw [Fin.val_add, Fin.val_mul]
      simp only [BabyBearPrime, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.add_mod_mod,
        Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd]
      have h25 := hbw3.1
      have h29 := hbw3.2.2
      simp at h29
      simp [Fin.lt_iff_val_lt_val] at h25
      have t : Main[25].val < 256 := by
        have := hbw2.2.2
        rw [Fin.lt_iff_val_lt_val] at this
        exact this
      omega
    rw [hxor0, hxor1, hxor2, hxor3]
    rw [htest, htest']
    rw [add_sub_assoc', add_sub_assoc']
    rw [add_sub_cancel_left, add_sub_cancel_left]
    simp [BitVec.ofNat_add, BitVec.ofNat_mul]
    rw [Fin.xor_val, Fin.xor_val]
    have h65536 : 65536 = 2 ^ 16 := rfl
    simp only [h65536] at op_b_memory_bound op_c_memory_bound

    rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]

    · rw [BitVec.ofNat_xor, BitVec.ofNat_xor]
      rw [BitVec.shiftLeft_xor_distrib]
      rw [ByteOpcode.bitVec_helper]
      · rw [BitVec.shiftLeft_xor_distrib]
      all_goals
      tauto
    · have := Nat.xor_lt_two_pow op_b_memory_bound.2 op_c_memory_bound.2
      refine lt_of_lt_of_le this ?_
      omega
    · have := Nat.xor_lt_two_pow op_b_memory_bound.1 op_c_memory_bound.1
      refine lt_of_lt_of_le this ?_
      omega
  · rw [Function.update_of_ne (Ne.symm hreg), Function.update_of_ne (Ne.symm hreg)]

#print axioms SP1BitwiseChip_xor_correct

-- dt: Essentially the same proof but should cleanup the above first

theorem SP1BitwiseChip_and_correct (Main : Vector BabyBear 33)
    (h_cstrs : SP1ConstraintList.allHold (constraints Main))
    (h_is_xor : Main[31] = 1) -- Is an `and` operation
    (pc : BitVec 32) (reg_state : regidx → BitVec 32)
    (hmem₁ : reg_state (regidx.Regidx Main[10].val) = .ofNat 32 (Main[11] + Main[12] * 65536))
    (hmem₂ : reg_state (regidx.Regidx Main[15].val) = .ofNat 32 (Main[17] + Main[18] * 65536)) :
    (sp1Bitwise Main).run (pc, reg_state) = (specAnd Main).run (pc, reg_state) := by
  sorry

theorem SP1BitwiseChip_or_correct (Main : Vector BabyBear 33)
    (h_cstrs : SP1ConstraintList.allHold (constraints Main))
    (h_is_xor : Main[32] = 1) -- Is an `xor` operation
    (pc : BitVec 32) (reg_state : regidx → BitVec 32)
    (hmem₁ : reg_state (regidx.Regidx Main[10].val) = .ofNat 32 (Main[11] + Main[12] * 65536))
    (hmem₂ : reg_state (regidx.Regidx Main[15].val) = .ofNat 32 (Main[17] + Main[18] * 65536)) :
    (sp1Bitwise Main).run (pc, reg_state) = (specOr Main).run (pc, reg_state) := by
  sorry

end BitwiseChip
