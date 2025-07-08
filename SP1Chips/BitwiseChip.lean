import SP1Operations

open BitVec

namespace BitwiseChip

section constraints

def constraints (Main : Vector (Fin BB) 33) : SP1ConstraintList :=
  let E0 : Fin BB := Main[30] + Main[31]
  let E1 : Fin BB := E0 + Main[32]
  let E2 : Fin BB := Main[30] - 1
  let E3 : Fin BB := Main[30] * E2
  let E4 : Fin BB := Main[31] - 1
  let E5 : Fin BB := Main[31] * E4
  let E6 : Fin BB := Main[32] - 1
  let E7 : Fin BB := Main[32] * E6
  let E8 : Fin BB := E1 - 1
  let E9 : Fin BB := E1 * E8
  let E10 : Fin BB := Main[30] * 2
  let E11 : Fin BB := Main[31] * 1
  let E12 : Fin BB := E10 + E11
  let E13 : Fin BB := Main[32] * 0
  let E14 : Fin BB := E12 + E13
  let E15 : Fin BB := Main[30] * 3
  let E16 : Fin BB := Main[31] * 4
  let E17 : Fin BB := E15 + E16
  let E18 : Fin BB := Main[32] * 5
  let E19 : Fin BB := E17 + E18
  let ⟨⟨⟨[E20, E21]⟩, _⟩, CS0⟩ := BitwiseU16Operation.constraints #v[Main[11], Main[12]] #v[Main[17], Main[18]] { b_low_bytes := { low_bytes := #v[Main[22], Main[23]] }, bitwise_operation := { result := #v[Main[26], Main[27], Main[28], Main[29]] }, c_low_bytes := { low_bytes := #v[Main[24], Main[25]] } } E14 E1
  let E22 : Fin BB := Main[3] + 4
  let CS1 : List SP1Constraint := CPUState.constraints { clk_0_16 := Main[2], clk_16_24 := Main[1], clk_high := Main[0], pc := Main[3] } E22 8 E1
  let E23 : Fin BB := Main[1] * 65536
  let E24 : Fin BB := Main[2] + E23
  let CS2 : List SP1Constraint := ALUTypeReader.constraints Main[0] E24 Main[3] E19 #v[E20, E21] { imm_c := Main[21], op_a := Main[4], op_a_0 := Main[9], op_a_memory := { access_timestamp := { diff_low_limb := Main[8], prev_low := Main[7] }, prev_value := #v[Main[5], Main[6]] }, op_b := Main[10], op_b_memory := { access_timestamp := { diff_low_limb := Main[14], prev_low := Main[13] }, prev_value := #v[Main[11], Main[12]] }, op_c := #v[Main[15], Main[16]], op_c_memory := { access_timestamp := { diff_low_limb := Main[20], prev_low := Main[19] }, prev_value := #v[Main[17], Main[18]] } } E1
  [
    .assertZero E3,
    .assertZero E5,
    .assertZero E7,
    .assertZero E9
  ] ++ CS0 ++ CS1 ++ CS2

lemma BitWiseU16_constraints_of_constraints (Main : Vector (Fin BB) 33)
    (h : (constraints Main).allHold) :
    (BitwiseU16Operation.constraints #v[Main[11], Main[12]] #v[Main[17], Main[18]]
      { b_low_bytes := { low_bytes := #v[Main[22], Main[23]] },
        bitwise_operation := { result := #v[Main[26], Main[27], Main[28], Main[29]] },
        c_low_bytes := { low_bytes := #v[Main[24], Main[25]] } }
        (Main[30] * 2 + Main[31] * 1)
        (Main[30] + Main[31] + Main[32])).2.allHold := by
  simp [constraints, BitwiseU16Operation.constraints] at *
  tauto

def main_output (Main : Vector (Fin BB) 33) : BitVec 32 :=
  let E0 : Fin BB := Main[30] + Main[31]
  let E1 : Fin BB := E0 + Main[32]
  let E2 : Fin BB := Main[30] - 1
  let E3 : Fin BB := Main[30] * E2
  let E4 : Fin BB := Main[31] - 1
  let E5 : Fin BB := Main[31] * E4
  let E6 : Fin BB := Main[32] - 1
  let E7 : Fin BB := Main[32] * E6
  let E8 : Fin BB := E1 - 1
  let E9 : Fin BB := E1 * E8
  let E10 : Fin BB := Main[30] * 2
  let E11 : Fin BB := Main[31] * 1
  let E12 : Fin BB := E10 + E11
  let E13 : Fin BB := Main[32] * 0
  let E14 : Fin BB := E12 + E13
  let E15 : Fin BB := Main[30] * 3
  let E16 : Fin BB := Main[31] * 4
  let E17 : Fin BB := E15 + E16
  let E18 : Fin BB := Main[32] * 5
  let E19 : Fin BB := E17 + E18
  let ⟨⟨⟨[E20, E21]⟩, _⟩, CS0⟩ := BitwiseU16Operation.constraints
    #v[Main[11], Main[12]] #v[Main[17], Main[18]]
    { b_low_bytes := { low_bytes := #v[Main[22], Main[23]] },
      bitwise_operation := { result := #v[Main[26], Main[27], Main[28], Main[29]] },
      c_low_bytes := { low_bytes := #v[Main[24], Main[25]] } }
      E14
      E1
  BitVec.ofNat 32 (E20 + E21 * 65536)

@[simp] lemma main_output_eq (Main : Vector (Fin BB) 33) : main_output Main =
    BitVec.ofNat 32 ((Main[26] + Main[27] * 256).1 + (Main[28] + Main[29] * 256).1 * 65536) := by
  simp [main_output, BitwiseU16Operation.constraints]

lemma is_unique_operation_of_constraints (Main : Vector (Fin BB) 33)
    (h : (constraints Main).allHold) :
    (Main[30] = 1 → Main[31] = 0 ∧ Main[32] = 0) ∧
      (Main[31] = 1 → Main[30] = 0 ∧ Main[32] = 0) ∧
        (Main[32] = 1 → Main[30] = 0 ∧ Main[31] = 0) := by
  simp [constraints, BitwiseU16Operation.constraints] at h
  obtain ⟨h1, h2, h3, h4, extra1, extra2, extra3⟩ := h
  clear extra1 extra2 extra3
  rw [sub_eq_zero] at h1 h2 h3 h4
  refine ⟨fun h_is_xor => ?_, fun h_is_or => ?_, fun h_is_and => ?_⟩
  · refine ⟨(or_iff_not_imp_right.1 h2) fun h_is_or => ?_,
      (or_iff_not_imp_right.1 h3) fun h_is_and => ?_⟩
    · cases h3 with | inl h | inr h => simp [h, h_is_xor, h_is_or] at h4
    · cases h2 with | inl h | inr h => simp [h, h_is_xor, h_is_and] at h4
  · refine ⟨(or_iff_not_imp_right.1 h1) fun h_is_xor => ?_,
      (or_iff_not_imp_right.1 h3) fun h_is_and => ?_⟩
    · cases h3 with | inl h | inr h => simp [h, h_is_or, h_is_xor] at h4
    · cases h1 with | inl h | inr h => simp [h, h_is_or, h_is_and] at h4
  · refine ⟨(or_iff_not_imp_right.1 h1) fun h_is_xor => ?_,
      (or_iff_not_imp_right.1 h2) fun h_is_or => ?_⟩
    · cases h2 with | inl h | inr h => simp [h, h_is_and, h_is_xor] at h4
    · cases h1 with | inl h | inr h => simp [h, h_is_and, h_is_or] at h4

end constraints

section specs

def specXor (op_a op_b op_c : regidx) : StateM SP1State Unit := do
  incrementPC
  let b : BitVec 32 ← get_reg op_b
  let c : BitVec 32 ← get_reg op_c
  update_reg op_a (b ^^^ c)

def specOr (op_a op_b op_c : regidx) : StateM SP1State Unit := do
  incrementPC
  let b : BitVec 32 ← get_reg op_b
  let c : BitVec 32 ← get_reg op_c
  update_reg op_a (b ||| c)

def specAnd (op_a op_b op_c : regidx) : StateM SP1State Unit := do
  incrementPC
  let b : BitVec 32 ← get_reg op_b
  let c : BitVec 32 ← get_reg op_c
  update_reg op_a (b &&& c)

end specs

def sp1Bitwise (Main : Vector (Fin BB) 33) : StateM SP1State Unit := do
  incrementPC
  let op_a := regidx.Regidx Main[4].val
  update_reg op_a (main_output Main)

/-- If the constraints all hold, `is_xor` is set to true, and `op_b` and `op_c` are loaded
into the proper registers, then the bitwise chip conforms to the xor spec. -/
theorem SP1BitwiseChip_xor_correct (Main : Vector (Fin BB) 33)
    (h_cstrs : SP1ConstraintList.allHold (constraints Main))
    (h_is_xor : Main[30] = 1) -- Is an `xor` operation
    (h_imm : Main[21] = 0) -- Not an immediate operation
    (pc : BitVec 32) (reg_state : regidx → BitVec 32) :
    let op_a := regidx.Regidx Main[4].val
    let op_b := regidx.Regidx Main[10].val
    let op_c := regidx.Regidx Main[15].val
    (reg_state op_b = .ofNat 32 (Main[11] + Main[12] * 65536)) →
    (reg_state op_c = .ofNat 32 (Main[17] + Main[18] * 65536)) →
      ((sp1Bitwise Main).run { pc := pc, regs := reg_state } = (specXor op_a op_b op_c).run { pc := pc, regs := reg_state }) := by
  simp only []
  intro hmem₁ hmem₂
  unfold sp1Bitwise specXor

  -- Because this is an `xor` it isn't and `and` or an `or`
  obtain ⟨h31, h32⟩ := (is_unique_operation_of_constraints Main h_cstrs).1 h_is_xor

  -- Break up the different parts of the constraints
  have hbwu16_cstrs := BitWiseU16_constraints_of_constraints Main h_cstrs
  simp [constraints, BitwiseU16Operation.constraints] at h_cstrs
  obtain ⟨h1, h2, h3, h4, bw_cstrs, cpu_cstrs, adapter_cstrs⟩ := h_cstrs
  simp [h_is_xor, h31, h32] at *

  -- The `BitwiseOperation` bounds the size of its inputs, and that they are actually `xor`s
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
  obtain ⟨h11, h12⟩ : Main[11].1 < 2^16 ∧ Main[12].1 < 2^16 :=
    ALUTypeReader.val_op_b_memory_lt_of_constraints adapter_cstrs
  obtain ⟨h17, h18⟩ : Main[17].1 < 2^16 ∧ Main[18].1 < 2^16 :=
    ALUTypeReader.val_op_c_memory_lt_of_constraints adapter_cstrs h_imm
  have h1218 : Main[12].val ^^^ Main[18].val < 2013265921 :=
    lt_of_lt_of_le (Nat.xor_lt_two_pow h12 h18) (by omega)
  have h1117 : Main[11].val ^^^ Main[17].val < 2013265921 :=
    lt_of_lt_of_le (Nat.xor_lt_two_pow h11 h17) (by omega)

  -- The `BitwiseU16Operation` constraints connects output values to `xor`
  have h27 : Main[27] * (256 : Fin BB) = (Main[11] ^^^ Main[17]) - Main[26] := by
    simpa using BitwiseU16Operation.eq_xor_word_sub_of_constraints _ _ _
      (by tauto) (by tauto) hbwu16_cstrs
  have h29 : Main[29] * (256 : Fin BB) = (Main[12] ^^^ Main[18]) - Main[28] := by
    simpa using BitwiseU16Operation.eq_xor_word_sub_of_constraints' _ _ _
      (by tauto) (by tauto) hbwu16_cstrs
  rw [hxor0, hxor1] at h27
  rw [hxor2, hxor3] at h29

  -- Suffices to show the new register map with cases on it being destination register
  refine congr_arg (fun st => pure ((), st)) ?_
  simp only [SP1State.mk.injEq]
  constructor
  · -- pc fields are equal
    simp [BitVec.ofNat]
  · -- regs fields
    funext reg
    simp [hmem₁, hmem₂, hxor0, hxor1, hxor2, hxor3, h27, h29,
      Nat.mod_eq_of_lt h1218, Nat.mod_eq_of_lt h1117,
      bitVec_helper_xor _ _ _ _ h11 h12 h17 h18,
      Fin.xor_val, ofNat_add, ofNat_mul, ofNat_xor]

/-- If the constraints all hold, `is_or` is set to true, and `op_b` and `op_c` are loaded
into the proper registers, then the bitwise chip conforms to the or spec. -/
theorem SP1BitwiseChip_or_correct (Main : Vector (Fin BB) 33)
    (h_cstrs : SP1ConstraintList.allHold (constraints Main))
    (h_is_or : Main[31] = 1) -- Is an `or` operation
    (h_imm : Main[21] = 0) -- Is not an immediate operation
    (pc : BitVec 32) (reg_state : regidx → BitVec 32) :
    let op_a := regidx.Regidx Main[4].val
    let op_b := regidx.Regidx Main[10].val
    let op_c := regidx.Regidx Main[15].val
    (reg_state op_b = .ofNat 32 (Main[11] + Main[12] * 65536)) →
    (reg_state op_c = .ofNat 32 (Main[17] + Main[18] * 65536)) →
      ((sp1Bitwise Main).run { pc := pc, regs := reg_state } = (specOr op_a op_b op_c).run { pc := pc, regs := reg_state }) := by
  simp only []
  intro hmem₁ hmem₂
  unfold sp1Bitwise specOr

  -- Because this is an `xor` it isn't and `and` or an `or`
  obtain ⟨h31, h32⟩ := (is_unique_operation_of_constraints Main h_cstrs).2.1 h_is_or

  -- Break up the different parts of the constraints
  have hbwu16_cstrs := BitWiseU16_constraints_of_constraints Main h_cstrs
  simp [constraints, BitwiseU16Operation.constraints] at h_cstrs
  obtain ⟨h1, h2, h3, h4, bw_cstrs, cpu_cstrs, adapter_cstrs⟩ := h_cstrs
  simp [h_is_or, h31, h32] at *

  -- The `BitwiseOperation` bounds the size of its inputs, and that they are actually `xor`s
  have hbw0 := BitwiseOperation.lt_of_constraints _ _ _ 0 .OR (Or.inr (Or.inl rfl)) bw_cstrs
  have hbw1 := BitwiseOperation.lt_of_constraints _ _ _ 1 .OR (Or.inr (Or.inl rfl)) bw_cstrs
  have hbw2 := BitwiseOperation.lt_of_constraints _ _ _ 2 .OR (Or.inr (Or.inl rfl)) bw_cstrs
  have hbw3 := BitwiseOperation.lt_of_constraints _ _ _ 3 .OR (Or.inr (Or.inl rfl)) bw_cstrs
  have hxor0 := BitwiseOperation.eq_or_of_constraints _ _ _ 0 bw_cstrs
  have hxor1 := BitwiseOperation.eq_or_of_constraints _ _ _ 1 bw_cstrs
  have hxor2 := BitwiseOperation.eq_or_of_constraints _ _ _ 2 bw_cstrs
  have hxor3 := BitwiseOperation.eq_or_of_constraints _ _ _ 3 bw_cstrs
  simp at hbw0 hbw1 hbw2 hbw3 hxor0 hxor1 hxor2 hxor3

  -- The `RTypeReader` gives bounds on the size of previous memory values
  obtain ⟨h11, h12⟩ : Main[11].1 < 2^16 ∧ Main[12].1 < 2^16 :=
    ALUTypeReader.val_op_b_memory_lt_of_constraints adapter_cstrs
  obtain ⟨h17, h18⟩ : Main[17].1 < 2^16 ∧ Main[18].1 < 2^16 :=
    ALUTypeReader.val_op_c_memory_lt_of_constraints adapter_cstrs h_imm
  have h1218 : Main[12].val ||| Main[18].val < 2013265921 :=
    lt_of_lt_of_le (Nat.or_lt_two_pow h12 h18) (by omega)
  have h1117 : Main[11].val ||| Main[17].val < 2013265921 :=
    lt_of_lt_of_le (Nat.or_lt_two_pow h11 h17) (by omega)

  -- The `BitwiseU16Operation` constraints connects output values to `xor`
  have h27 : Main[27] * (256 : Fin BB) = (Main[11] ||| Main[17]) - Main[26] := by
    simpa using BitwiseU16Operation.eq_or_word_sub_of_constraints _ _ _
      (by tauto) (by tauto) hbwu16_cstrs
  have h29 : Main[29] * (256 : Fin BB) = (Main[12] ||| Main[18]) - Main[28] := by
    simpa using BitwiseU16Operation.eq_or_word_sub_of_constraints' _ _ _
      (by tauto) (by tauto) hbwu16_cstrs
  rw [hxor0, hxor1] at h27
  rw [hxor2, hxor3] at h29

  refine congr_arg (fun st => pure ((), st)) ?_
  simp only [SP1State.mk.injEq]
  constructor
  · -- pc fields are equal
    simp [BitVec.ofNat]
  · -- regs fields
    funext reg
    simp [hmem₁, hmem₂, hxor0, hxor1, hxor2, hxor3, h27, h29,
      Nat.mod_eq_of_lt h1218, Nat.mod_eq_of_lt h1117,
      bitVec_helper_or _ _ _ _ h11 h12 h17 h18,
      Fin.or_val, ofNat_add, ofNat_mul, ofNat_or]

-- dt: could just hardcode "and" also, would be nice to avoid that

end BitwiseChip
