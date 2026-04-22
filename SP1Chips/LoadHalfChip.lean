import SP1Foundations
import SP1Chips.Load.LoadHalf.Constraints

open LeanRV64D.Functions Sail SailState

namespace Load

namespace LoadHalf

def sp1_op_a (Main : Vector (Fin KB) 46) : BitVec 5 :=
  BitVec.ofNat 5 Main[6]

def sp1_ob_b (Main : Vector (Fin KB) 46) : BitVec 5 :=
  BitVec.ofNat 5 Main[14]

def sp1_imm_c (Main : Vector (Fin KB) 46) : BitVec 12 :=
  BitVec.ofNat 12 Main[21]

def sp1_load_byte (Main : Vector (Fin KB) 46) : SailM ExecutionResult := do
  let op_a := sp1_op_a Main
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] + 4)
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[44] + 65280 * Main[45],
    65535 * Main[45], 65535 * Main[45], 65535 * Main[45]])
  return RETIRE_SUCCESS

noncomputable def spec_lb (imm : BitVec 12) (rs1 rs2 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_LOAD imm rs1 rs2 (is_unsigned := false) (width := 1)

set_option debug.skipKernelTC true in
set_option maxHeartbeats 2000000 in
theorem correct_lb (Main : Vector (Fin KB) 46)
    (s : SailState) (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (LoadHalf.constraints Main).allHold)
    (state_cstrs : (LoadHalf.constraints Main).initialState s)
    (h_is_lb : Main[45] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (sp1_imm_c Main)).toNat
      reg_val + offset + 1 < 2^64) :
    let op_a := sp1_op_a Main
    let op_b := sp1_ob_b Main
    let imm_c := sp1_imm_c Main
    (spec_lb imm_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_load_byte Main).run s := by
  extract_lets op_a op_b imm_c

  obtain ⟨h_mprv_disabled, h_cur_privilege, h_clint_base, h_clint_size,
    h_plat_ram_base, h_plat_rom_base⟩ := hs_config

  rw [SP1ConstraintList.allHold, allHold_constraints_iff_of_is_lb Main h_is_lb] at h_cstrs
  obtain ⟨h_addr, h39, h40, h41, h29, hb,
    h_cpu, h_reader, h36, h34, hds, h37, h38, hmem, hmem',
    h46, h48, h13, h30, h31, h32, h33, h34, h_offset⟩ := h_cstrs

  simp [ITypeReader.constraints] at h_reader
  have h25 : Main[25] = 1 := by omega
  simp [h25, SP1Constraint.toProp, Opcode.ofNat, Nat.ble, and_assoc] at h_reader
  obtain ⟨h14, h21, h6, rest⟩ := h_reader
  simp [Fin.lt_def] at rest

  have h2728 : ¬ (Main[27] = 0 ∧ Main[28] = 0) := by clear *- h29; aesop

  simp [LoadHalf.constraints, AddressOperation.constraints,
    SP1Constraint.toStateProp, AddrAddOperation.constraints,
    CPUState.constraints, ITypeReader.constraints, BitVec.ofNatLT_eq_ofNat,
    Opcode.ofNat, Nat.ble, h6, h14, h25, h2728, h46, h_is_lb] at state_cstrs
  obtain ⟨h_read_pc, h6_op_a, h14_op_a, hload⟩ := state_cstrs
  rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_read_pc

  have h6 : BitVec.ofNat 5 Main[6] ≠ 0#5 := by simp [← BitVec.toNat_inj]; omega

  have h_limb : Main[43] + ((Main[42] - Main[43]) * 2122383361) * 2^8 = Main[42] := by
    simp
    clear *- h34
    rw [inv_8BB_eq', mul_assoc, inv_mul_cancel₀ (by omega), mul_one]

    omega

  have h_low_limb : Main[43] = Main[42] &&& 0xFF := by
    have h255 : 255 = 2 ^ 8 - 1 := rfl
    simp only [← Fin.val_inj, Fin.and_val,
      Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod]
    rw [h255, Nat.and_two_pow_sub_one_eq_mod]
    clear *- h34 h_limb
    rw [← Fin.val_inj] at h_limb
    -- rw [h255, Nat.and_two_pow_sub_one_eq_mod]
    have := congr_arg (· % 256) h_limb
    refine trans ?_ this
    simp
    -- rw [Fin.val_add_eq_of_add_lt]
    · symm
      rw [Nat.mod_eq_iff]
      simp
      refine ⟨by omega, ?_⟩
      use ((Main[42] - Main[43]) * 2122383361).val
      rw [Fin.val_add_eq_of_add_lt]


      · rw [Fin.val_mul]
        rw [Nat.mod_eq_of_lt (by
          set k := (Main[42] - Main[43]) * 2122383361
          simp [Fin.lt_def] at h34
          omega
        ), add_comm, mul_comm]
        simp

      set k := (Main[42] - Main[43]) * 2122383361
      rw [Fin.val_mul]
      simp [Fin.lt_def] at h34
      rw [Nat.mod_eq_of_lt (by omega)]
      omega

  by_cases h_neg : (128 : Fin KB) ≤ Main[44]
  · have h_zero_extend : Main[45] = 1 := by
      clear *- h_neg h_offset; simp_all



    have h43 : BitVec.signExtend 64 (BitVec.ofNat 8 Main[42].val) =
        Word.toBitVec64 #v[Main[43] + 65280, 65535, 65535, 65535] := by
      have : 255 = 2 ^ 8 - 1 := rfl
      -- simp [h_low_limb, Word.toBitVec64, Word.toNat_def, ← BitVec.toNat_inj]
      -- rw [this, Nat.and_two_pow_sub_one_eq_mod]

      -- omega
    have h43' : BitVec.signExtend 64 (BitVec.ofNat 8 (Main[42].val >>> 8)) =
        Word.toBitVec64 #v[(Main[42] - Main[43]) * 2122383361 + 65280, 65535, 65535, 65535] := by
      stop
      have : 255 = 2 ^ 8 - 1 := rfl
      rw [inv_8BB_eq'] at h34
      simp [h_low_limb, ← BitVec.toNat_inj, Word.toBitVec64, Word.toNat_def]
      have hand : Main[42] &&& (255 : Fin KB) = Main[42] % 256 := by
        simp [← Fin.val_inj]
        rw [this, Nat.and_two_pow_sub_one_eq_mod]
      have h256 : Main[42] % (256 : Fin KB) ≤ Main[42] := by
        rw [Fin.le_iff_val_le_val]
        simp
        omega
      rw [inv_8BB_eq', Fin.mul_inv_pow2_eq_shiftRight (8 : Fin KB) (by decide) _,
        hand, shiftRight_eq_sub_mod]
      congr 1
      simp [Fin.mod_val]
      rw [Fin.sub_val_of_le h256, Nat.mod_eq_of_lt]
      simp
      have : ↑Main[42] - ↑Main[42] % 256 < 65536 := by
        clear *- h34 h_low_limb hand h256
        have := lt_65536_of_mul_inv_lt' _ h34.2

        rw [h_low_limb, hand] at this
        omega
      clear *- this h256
      rw [Fin.lt_def,
        Fin.sub_val_of_le h256] at this
      simp at this
      -- stop
      omega
      · rw [hand, Fin.sub_val_of_le h256]
        apply Nat.sub_mod_eq_zero_of_mod_eq
        simp

    have hu6421 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := by
      apply Word.isU64_of_cases <;> {clear *- rest; simp_all}

    -- Monadic manipulation
    simp [spec_lb, sp1_load_byte,
      sp1_op_a, sp1_ob_b, sp1_imm_c,
      op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
      EStateM.Result.map, execute_LOAD, h_read_pc, h6]

    rcases h39 with h39 | h39 <;>
      rcases h40 with h40 | h40 <;>
      rcases h41 with h41 | h41 <;>
      simp only [h40, Fin.isValue, zero_ne_one, h41, true_or, or_true, or_self, one_ne_zero,
        false_or, mul_one, Fin.sub_eq_add_neg, mul_zero, sub_zero, h39, add_assoc, neg_add_cancel,
        add_zero, Nat.cast_ofNat, zero_mul, Nat.cast_one, one_mul,
        zero_add] at h30 h31 h32 h33 hload h_offset

    all_goals
    · rw [run_vmem_read_of_width_1' (BitVec.ofNat 5 Main[14])
        (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]])
        _ (Word.toBitVec64 #v[if Main[39] = 1 then Main[42] >>> 8 else Main[42], 0, 0, 0])]

      · simp [h6, h_zero_extend, h_offset, extend_value, zero_extend, Sail.BitVec.zeroExtend,
          h43, h43', h39, h40, h41, bitVecToRegidxVal, ← Fin.sub_eq_add_neg]
      · simp only [Fin.isValue, isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs,
          or_true, implies_true]
      · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
      · simp only [is_aligned_vaddr, BitVec.toNat_add, Nat.reducePow, Int.natCast_emod, Nat.cast_add,
          Nat.cast_ofNat, Nat.cast_one, Int.tmod_one, BEq.rfl]
      · constructor <;> simpa [Std.ExtDHashMap.get_insert]
      · exact h_fits_in_mem
      · simp only [Fin.isValue, Word.setWidth8_toBitVec64, Vector.getElem_mk, List.getElem_toArray,
          List.getElem_cons_zero]
        simp [SP1Constraint.toProp] at hmem hmem'
        have := AddrAddOperation.spec_of_constraints _ _ (by simp_all only) hu6421 _ h_addr
        · obtain ⟨hu, haddr⟩ := this
          simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
            List.getElem_cons_succ, Fin.isValue] at haddr
          rw [← BitVec.toNat_inj, BitVec.toNat_add, Nat.mod_eq_of_lt] at haddr
          · rw [← h21, ← haddr, Word.toBitVec64, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by simp [Word.toNat]; omega)]
            clear *- h30 h31 h32 h33 hload
            simp_all [Fin.neg_def]
          · clear *- h_fits_in_mem h21
            simp [sp1_imm_c] at h_fits_in_mem
            rw [← h21] at h_fits_in_mem
            omega

  · have h_zero_extend : Main[45] = 0 := by
      clear *- h_neg h_offset; simp_all; omega

    have h43 : BitVec.setWidth 64 (BitVec.ofNat 8 Main[42].val) =
      Word.toBitVec64 #v[Main[43], 0, 0, 0] := by
      have : 255 = 2 ^ 8 - 1 := rfl
      simp [h_low_limb, Word.toBitVec64, Word.toNat_def, ← BitVec.toNat_inj]
      rw [this, Nat.and_two_pow_sub_one_eq_mod]
      omega
    have h43' : BitVec.setWidth 64 (BitVec.ofNat 8 (Main[42].val >>> 8)) =
        Word.toBitVec64 #v[(Main[42] - Main[43]) * 2122383361, 0, 0, 0] := by
      have : 255 = 2 ^ 8 - 1 := rfl
      rw [inv_8BB_eq'] at h34
      simp [h_low_limb, ← BitVec.toNat_inj, Word.toBitVec64, Word.toNat_def]
      have hand : Main[42] &&& (255 : Fin KB) = Main[42] % 256 := by
        simp [← Fin.val_inj]
        rw [this, Nat.and_two_pow_sub_one_eq_mod]
      have h256 : Main[42] % (256 : Fin KB) ≤ Main[42] := by
        rw [Fin.le_iff_val_le_val]
        simp
        omega
      rw [inv_8BB_eq', Fin.mul_inv_pow2_eq_shiftRight (8 : Fin KB) (by decide) _,
        hand, shiftRight_eq_sub_mod]
      congr 1
      simp [Fin.mod_val]
      rw [Fin.sub_val_of_le h256, Nat.mod_eq_of_lt]
      simp
      have : ↑Main[42] - ↑Main[42] % 256 < 65536 := by
        clear *- h34 h_low_limb hand h256
        have := lt_65536_of_mul_inv_lt' _ h34.2

        rw [h_low_limb, hand] at this
        omega
      clear *- this h256
      rw [Fin.lt_def,
        Fin.sub_val_of_le h256] at this
      simp at this
      -- stop
      omega
      · rw [hand, Fin.sub_val_of_le h256]
        apply Nat.sub_mod_eq_zero_of_mod_eq
        simp

    have hu6421 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := by
      apply Word.isU64_of_cases <;> {clear *- rest; simp_all}

    -- Monadic manipulation
    simp [spec_lb, sp1_load_byte,
      sp1_op_a, sp1_ob_b, sp1_imm_c,
      op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
      EStateM.Result.map, execute_LOAD, h_read_pc, h6]

    rcases h39 with h39 | h39 <;>
      rcases h40 with h40 | h40 <;>
      rcases h41 with h41 | h41 <;>
      simp only [h40, Fin.isValue, zero_ne_one, h41, true_or, or_true, or_self, one_ne_zero,
        false_or, mul_one, Fin.sub_eq_add_neg, mul_zero, sub_zero, h39, add_assoc, neg_add_cancel,
        add_zero, Nat.cast_ofNat, zero_mul, Nat.cast_one, one_mul,
        zero_add] at h30 h31 h32 h33 hload h_offset


    · rw [run_vmem_read_of_width_1' (BitVec.ofNat 5 Main[14])
        (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]])
        _ (Word.toBitVec64 #v[if Main[39] = 1 then Main[42] >>> 8 else Main[42], 0, 0, 0])]

      · simp [h6, h_zero_extend, h_offset, extend_value, zero_extend, Sail.BitVec.zeroExtend,
          h43, h43', h39, h40, h41, bitVecToRegidxVal, ← Fin.sub_eq_add_neg]
        rw [BitVec.signExtend_eq_setWidth_of_msb_false]
        · simp [h43', h43]
        · rw [BitVec.msb_eq_false_iff_two_mul_lt]
          clear *- h_neg h_offset h_limb h_low_limb
          simp

          simp [Fin.le_iff_val_le_val] at h_neg
          rw [h_offset.1, h_low_limb] at h_neg


      · simp only [Fin.isValue, isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs,
          or_true, implies_true]
      · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
      · simp only [is_aligned_vaddr, BitVec.toNat_add, Nat.reducePow, Int.natCast_emod, Nat.cast_add,
          Nat.cast_ofNat, Nat.cast_one, Int.tmod_one, BEq.rfl]
      · constructor <;> simpa [Std.ExtDHashMap.get_insert]
      · exact h_fits_in_mem
      · simp only [Fin.isValue, Word.setWidth8_toBitVec64, Vector.getElem_mk, List.getElem_toArray,
          List.getElem_cons_zero]
        simp [SP1Constraint.toProp] at hmem hmem'
        have := AddrAddOperation.spec_of_constraints _ _ (by simp_all only) hu6421 _ h_addr
        · obtain ⟨hu, haddr⟩ := this
          simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
            List.getElem_cons_succ, Fin.isValue] at haddr
          rw [← BitVec.toNat_inj, BitVec.toNat_add, Nat.mod_eq_of_lt] at haddr
          · rw [← h21, ← haddr, Word.toBitVec64, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by simp [Word.toNat]; omega)]
            clear *- h30 h31 h32 h33 hload
            simp_all [Fin.neg_def]
          · clear *- h_fits_in_mem h21
            simp [sp1_imm_c] at h_fits_in_mem
            rw [← h21] at h_fits_in_mem
            omega
    stop

noncomputable def spec_lbu (imm : BitVec 12) (rs1 rs2 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_LOAD imm rs1 rs2 (is_unsigned := true) (width := 1)

set_option maxHeartbeats 2000000
theorem correct_lbu (Main : Vector (Fin KB) 46)
    (s : SailState) (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (LoadHalf.constraints Main).allHold)
    (state_cstrs : (LoadHalf.constraints Main).initialState s)
    (h_is_lbu : Main[47] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (sp1_imm_c Main)).toNat
      reg_val + offset + 1 < 2^64) :
    let op_a := sp1_op_a Main
    let op_b := sp1_ob_b Main
    let imm_c := sp1_imm_c Main
    (spec_lbu imm_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_load_byte Main).run s := by
  extract_lets op_a op_b imm_c

  obtain ⟨h_mprv_disabled, h_cur_privilege, h_clint_base, h_clint_size,
    h_plat_ram_base, h_plat_rom_base⟩ := hs_config

  rw [SP1ConstraintList.allHold, allHold_constraints_iff_of_is_lbu Main h_is_lbu] at h_cstrs
  obtain ⟨h_addr, h39, h40, h41, h29, hb,
    h_cpu, h_reader, h36, h34, hds, h37, h38, hmem, hmem',
    h46, h48, h13, h30, h31, h32, h33, h34, h_offset⟩ := h_cstrs

  simp [ITypeReader.constraints] at h_reader
  have h25 : Main[25] = 1 := by omega
  simp [h25, SP1Constraint.toProp, Opcode.ofNat, Nat.ble, and_assoc] at h_reader
  obtain ⟨h14, h21, h6, rest⟩ := h_reader
  simp [Fin.lt_def] at rest

  have h2728 : ¬ (Main[27] = 0 ∧ Main[28] = 0) := by clear *- h29; aesop

  simp [LoadHalf.constraints, AddressOperation.constraints,
    SP1Constraint.toStateProp, AddrAddOperation.constraints,
    CPUState.constraints, ITypeReader.constraints, BitVec.ofNatLT_eq_ofNat,
    Opcode.ofNat, Nat.ble, h6, h14, h25, h2728, h46, h_is_lbu] at state_cstrs
  obtain ⟨h_read_pc, h6_op_a, h14_op_a, hload⟩ := state_cstrs
  rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_read_pc

  have h6 : BitVec.ofNat 5 Main[6] ≠ 0#5 := by simp [← BitVec.toNat_inj]; omega
  have h_zero_extend : Main[45] = 0 := by simp_all only

  have h_limb : Main[43] + ((Main[42] - Main[43]) * 2122383361) * 2^8 = Main[42] := by
    simp
    clear *- h34
    rw [inv_8BB_eq', mul_assoc, inv_mul_cancel₀ (by omega), mul_one]
    omega

  have h_low_limb : Main[43] = Main[42] &&& 0xFF := by
    have h255 : 255 = 2 ^ 8 - 1 := rfl
    simp only [← Fin.val_inj, Fin.and_val,
      Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod]
    rw [h255, Nat.and_two_pow_sub_one_eq_mod]
    clear *- h34 h_limb
    rw [← Fin.val_inj] at h_limb
    -- rw [h255, Nat.and_two_pow_sub_one_eq_mod]
    have := congr_arg (· % 256) h_limb
    refine trans ?_ this
    simp
    -- rw [Fin.val_add_eq_of_add_lt]
    · symm
      rw [Nat.mod_eq_iff]
      simp
      refine ⟨by omega, ?_⟩
      use ((Main[42] - Main[43]) * 2122383361).val
      rw [Fin.val_add_eq_of_add_lt]


      · rw [Fin.val_mul]
        rw [Nat.mod_eq_of_lt (by
          set k := (Main[42] - Main[43]) * 2122383361
          simp [Fin.lt_def] at h34
          omega
        ), add_comm, mul_comm]
        simp

      set k := (Main[42] - Main[43]) * 2122383361
      rw [Fin.val_mul]
      simp [Fin.lt_def] at h34
      rw [Nat.mod_eq_of_lt (by omega)]
      omega


  have h43 : BitVec.setWidth 64 (BitVec.ofNat 8 Main[42].val) =
      Word.toBitVec64 #v[Main[43], 0, 0, 0] := by
    have : 255 = 2 ^ 8 - 1 := rfl
    simp [h_low_limb, Word.toBitVec64, Word.toNat_def, ← BitVec.toNat_inj]
    rw [this, Nat.and_two_pow_sub_one_eq_mod]
    omega
  have h43' : BitVec.setWidth 64 (BitVec.ofNat 8 (Main[42].val >>> 8)) =
      Word.toBitVec64 #v[(Main[42] - Main[43]) * 2122383361, 0, 0, 0] := by
    have : 255 = 2 ^ 8 - 1 := rfl
    rw [inv_8BB_eq'] at h34
    simp [h_low_limb, ← BitVec.toNat_inj, Word.toBitVec64, Word.toNat_def]
    have hand : Main[42] &&& (255 : Fin KB) = Main[42] % 256 := by
      simp [← Fin.val_inj]
      rw [this, Nat.and_two_pow_sub_one_eq_mod]
    have h256 : Main[42] % (256 : Fin KB) ≤ Main[42] := by
      rw [Fin.le_iff_val_le_val]
      simp
      omega
    rw [inv_8BB_eq', Fin.mul_inv_pow2_eq_shiftRight (8 : Fin KB) (by decide) _,
      hand, shiftRight_eq_sub_mod]
    congr 1
    simp [Fin.mod_val]
    rw [Fin.sub_val_of_le h256, Nat.mod_eq_of_lt]
    simp
    have : ↑Main[42] - ↑Main[42] % 256 < 65536 := by
      clear *- h34 h_low_limb hand h256
      have := lt_65536_of_mul_inv_lt' _ h34.2

      rw [h_low_limb, hand] at this
      omega
    clear *- this h256
    rw [Fin.lt_def,
      Fin.sub_val_of_le h256] at this
    simp at this
    -- stop
    omega
    · rw [hand, Fin.sub_val_of_le h256]
      apply Nat.sub_mod_eq_zero_of_mod_eq
      simp

  have hu6421 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := by
    apply Word.isU64_of_cases <;> {clear *- rest; simp_all}

  -- Monadic manipulation
  simp [spec_lbu, sp1_load_byte,
    sp1_op_a, sp1_ob_b, sp1_imm_c,
    op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
    EStateM.Result.map, execute_LOAD, h_read_pc, h6]

  rcases h39 with h39 | h39 <;>
    rcases h40 with h40 | h40 <;>
    rcases h41 with h41 | h41 <;>
    simp only [h40, Fin.isValue, zero_ne_one, h41, true_or, or_true, or_self, one_ne_zero,
      false_or, mul_one, Fin.sub_eq_add_neg, mul_zero, sub_zero, h39, add_assoc, neg_add_cancel,
      add_zero, Nat.cast_ofNat, zero_mul, Nat.cast_one, one_mul,
      zero_add] at h30 h31 h32 h33 hload h_offset

  all_goals
  · rw [run_vmem_read_of_width_1' (BitVec.ofNat 5 Main[14])
      (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]])
      _ (Word.toBitVec64 #v[if Main[39] = 1 then Main[42] >>> 8 else Main[42], 0, 0, 0])]

    · simp [h6, h_zero_extend, h_offset, extend_value, zero_extend, Sail.BitVec.zeroExtend,
        h43, h43', h39, h40, h41, bitVecToRegidxVal, ← Fin.sub_eq_add_neg]

    · simp only [Fin.isValue, isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs,
        or_true, implies_true]
    · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
    · simp only [is_aligned_vaddr, BitVec.toNat_add, Nat.reducePow, Int.natCast_emod, Nat.cast_add,
        Nat.cast_ofNat, Nat.cast_one, Int.tmod_one, BEq.rfl]
    · constructor <;> simpa [Std.ExtDHashMap.get_insert]
    · exact h_fits_in_mem
    · simp only [Fin.isValue, Word.setWidth8_toBitVec64, Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero]
      simp [SP1Constraint.toProp] at hmem hmem'
      have := AddrAddOperation.spec_of_constraints _ _ (by simp_all only) hu6421 _ h_addr
      · obtain ⟨hu, haddr⟩ := this
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ, Fin.isValue] at haddr
        rw [← BitVec.toNat_inj, BitVec.toNat_add, Nat.mod_eq_of_lt] at haddr
        · rw [← h21, ← haddr, Word.toBitVec64, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by simp [Word.toNat]; omega)]
          clear *- h30 h31 h32 h33 hload
          simp_all [Fin.neg_def]
        · clear *- h_fits_in_mem h21
          simp [sp1_imm_c] at h_fits_in_mem
          rw [← h21] at h_fits_in_mem
          omega
