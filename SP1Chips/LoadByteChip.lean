import SP1Foundations
import SP1Chips.Load.LoadByte.Constraints
import SP1Operations.Operation.AddrAddOperation

open LeanRV64D.Functions Sail SailState

namespace Load

namespace LoadByte

def sp1_op_a (Main : Vector (Fin KB) 47) : BitVec 5 :=
  BitVec.ofNat 5 Main[6]

def sp1_ob_b (Main : Vector (Fin KB) 47) : BitVec 5 :=
  BitVec.ofNat 5 Main[14]

def sp1_imm_c (Main : Vector (Fin KB) 47) : BitVec 12 :=
  BitVec.ofNat 12 Main[21]

def sp1_load_byte (Main : Vector (Fin KB) 47) : SailM ExecutionResult := do
  let op_a := sp1_op_a Main
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] + 4)
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[43] + 65280 * Main[44],
    65535 * Main[44], 65535 * Main[44], 65535 * Main[44]])
  return RETIRE_SUCCESS

noncomputable def spec_lb (imm : BitVec 12) (rs1 rs2 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_LOAD imm rs1 rs2 (is_unsigned := false) (width := 1)

noncomputable def spec_lbu (imm : BitVec 12) (rs1 rs2 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_LOAD imm rs1 rs2 (is_unsigned := true) (width := 1)

-- correct_lb unfolds Load chip + Sail memory read spec
theorem correct_lb (Main : Vector (Fin KB) 47)
    (s : SailState) (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (LoadByte.constraints Main).allHold)
    (state_cstrs : (LoadByte.constraints Main).initialState s)
    (h_is_lb : Main[45] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (sp1_imm_c Main)).toNat
      reg_val + offset + 1 < 2 ^ 64)
    (h_below_clint :
      let reg_val := Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]
      let offset := BitVec.signExtend 64 (sp1_imm_c Main)
      BitVec.toNat (reg_val + offset) + 1 ≤ 33554432) :
    let op_a := sp1_op_a Main
    let op_b := sp1_ob_b Main
    let imm_c := sp1_imm_c Main
    (spec_lb imm_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_load_byte Main).run s := by
  extract_lets op_a op_b imm_c
  obtain ⟨h_mprv_disabled, h_cur_privilege⟩ := hs_config
  rw [SP1ConstraintList.allHold, allHold_constraints_iff_of_is_lb Main h_is_lb] at h_cstrs
  obtain ⟨h_addr, h38, h39, h40, h28, hb,
    h_cpu, h_reader, h35, h33', hds, h36, h37, hmem, hmem',
    h46_zero, h13, h29, h30, h31, h32, h34, h_offset⟩ := h_cstrs
  -- Extract reader facts
  simp [ITypeReader.constraints] at h_reader
  simp [SP1Constraint.toProp, Opcode.ofNat, Nat.ble, and_assoc] at h_reader
  obtain ⟨h14, h21, h6, rest⟩ := h_reader
  simp [Fin.lt_def] at rest
  have h2728 : ¬ (Main[26] = 0 ∧ Main[27] = 0) := by clear *- h28; aesop
  -- Extract initial-state facts
  simp [LoadByte.constraints, AddressOperation.constraints,
    SP1Constraint.toStateProp, AddrAddOperation.constraints,
    CPUState.constraints, ITypeReader.constraints, BitVec.ofNatLT_eq_ofNat,
    Opcode.ofNat, Nat.ble, h6, h14, h2728, h46_zero, h_is_lb] at state_cstrs
  obtain ⟨h_read_pc, h6_op_a, h14_op_a, hload⟩ := state_cstrs
  rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_read_pc
  have h6 : BitVec.ofNat 5 Main[6] ≠ 0#5 := by simp [← BitVec.toNat_inj]; omega
  -- The byte is bounded by 256 (it's one of the memory bytes)
  have h43_lt : Main[43].val < 256 := by clear *- h_offset; exact_mod_cast h_offset.2.1.2
  have h44_lt : Main[44].val < 256 := by clear *- h_offset; exact_mod_cast h_offset.2.1.1
  have h45_01 : Main[44] = 0 ∨ Main[44] = 1 := h_offset.2.2.1
  -- The immediate fits into a 12-bit word
  have hu6421 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := by
    apply Word.isU64_of_cases <;> {clear *- rest; simp_all}
  -- Key bounds
  have h42_lt : Main[42].val < 256 := by exact_mod_cast h34.1
  have h42hi_lt : ((Main[41] - Main[42]) * 2122383361).val < 256 := by exact_mod_cast h34.2
  -- Byte decomposition: Main[42] + high_byte * 256 = Main[41] in Fin KB, hence in Nat.
  have h_limb_fin : Main[42] + ((Main[41] - Main[42]) * 2122383361) * (2 ^ 8 : Fin KB) = Main[41] := by
    clear *- h34
    have h1 : (Main[41] - Main[42]) * 2122383361 * (2 ^ 8 : Fin KB) =
              (Main[41] - Main[42]) * ((2122383361 : Fin KB) * (2 ^ 8 : Fin KB)) := by ring
    have h2 : ((2122383361 : Fin KB) * (2 ^ 8 : Fin KB)) = 1 := by decide
    rw [h1, h2, mul_one]; ring
  have h_decomp : Main[41].val = Main[42].val + ((Main[41] - Main[42]) * 2122383361).val * 256 :=
    nat_decomp_of_inv8_decomp _ _ _ h_limb_fin h42_lt h42hi_lt
  -- We need to know that the address fits.
  have h21' : BitVec.signExtend 64 (BitVec.ofNat 12 (Main[21] : ℕ)) =
      Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] := h21.symm
  -- From AddrAddOperation: (reg_val + offset) = Word.toBitVec64 #v[Main[25], Main[26], Main[27], 0]
  have haddr_add := AddrAddOperation.spec_of_constraints _ _ (by
    clear *- rest; simp_all only) hu6421 _ h_addr
  obtain ⟨_, haddr_eq⟩ := haddr_add
  simp only [AddrAddOperation.spec, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ] at haddr_eq
  -- Simplify monadic form on the spec side
  simp [spec_lb, sp1_load_byte,
    sp1_op_a, sp1_ob_b, sp1_imm_c,
    op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
    EStateM.Result.map, execute_LOAD, h_read_pc, h6]
  rw [run_vmem_read_of_width_1' (BitVec.ofNat 5 Main[14])
    (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]])
    (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
    (BitVec.ofNat 8 Main[43].val)]
  -- Main goal: the equality after the memory read result is substituted
  · by_cases h_neg : (128 : Fin KB) ≤ Main[43]
    · -- Main[43] >= 128, Main[44] = 1
      have h44 : Main[44] = 1 := h_offset.2.2.2.mpr h_neg
      have hext : BitVec.signExtend 64 (BitVec.ofNat 8 Main[43].val) =
          Word.toBitVec64 #v[Main[43] + 65280, 65535, 65535, 65535] := by
        apply signExtend64_ofNat8_of_ge_128 Main[43] h43_lt
        exact_mod_cast h_neg
      simp [extend_value, sign_extend, Sail.BitVec.signExtend, bitVecToRegidxVal,
        hext, h44, mul_one]
    · -- Main[43] < 128, Main[44] = 0
      have h44 : Main[44] = 0 := by
        rcases h45_01 with h | h
        · exact h
        · exfalso; exact h_neg (h_offset.2.2.2.mp h)
      have h43_lt_128 : Main[43].val < 128 := by
        rw [Fin.le_def] at h_neg
        simp at h_neg
        exact_mod_cast h_neg
      have hext : BitVec.signExtend 64 (BitVec.ofNat 8 Main[43].val) =
          Word.toBitVec64 #v[Main[43], 0, 0, 0] :=
        signExtend64_ofNat8_of_lt_128 Main[43] h43_lt h43_lt_128
      simp [extend_value, sign_extend, Sail.BitVec.signExtend, bitVecToRegidxVal,
        hext, h44, mul_zero, add_zero]
  -- Side condition: isInitialized of post-write-pc state
  · simp only [Fin.isValue, isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs,
      or_true, implies_true]
  -- Side condition: get_reg? of op_b in post-write-pc state
  · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
  -- Side condition: is_aligned_vaddr for width 1 (always true)
  · simp only [is_aligned_vaddr, BitVec.toNat_add, Nat.reducePow, Int.natCast_emod, Nat.cast_add,
      Nat.cast_ofNat, Nat.cast_one, Int.tmod_one, BEq.rfl]
  -- Side condition: isValidMemConfig for post-write-pc state
  · constructor <;> simpa [Std.ExtDHashMap.get_insert]
  -- Side condition: fits in 2 ^ 64
  · exact h_fits_in_mem
  -- Side condition: below clint
  · exact h_below_clint
  -- Side condition: memory at addr contains byte Main[43].
  · -- First convert the address to the canonical form from haddr_eq.
    rw [h21']
    have haddr_nat :
        (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat +
            (Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]]).toNat =
          Word.toNat #v[Main[25], Main[26], Main[27], 0] := by
      have hfits :
          (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat +
              (Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]]).toNat < 2 ^ 64 := by
        have := h_fits_in_mem
        simp only [sp1_imm_c] at this
        rw [← h21] at this
        omega
      have := congr_arg BitVec.toNat haddr_eq
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt hfits] at this
      rw [← this, Word.toBitVec64, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by simp [Word.toNat]; omega)]
    change s.mem[_]? = _
    rw [haddr_nat]
    -- Now case-split on h38/h39/h40 to pick the right entry of hload
    obtain ⟨hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7⟩ := hload
    rcases h38 with h38 | h38 <;> rcases h39 with h39 | h39 <;> rcases h40 with h40 | h40
    all_goals (
      simp only [h38, h39, h40, Fin.isValue, zero_ne_one, one_ne_zero,
        or_true, true_or, or_self, or_false, false_or, mul_one, mul_zero, sub_zero,
        Fin.sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero, Nat.cast_ofNat,
        zero_mul, Nat.cast_one, one_mul, zero_add, neg_zero,
        hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7] at h29 h30 h31 h32 h_offset hL0 hL1 hL2 hL3 hL4 hL5 hL6 hL7 ⊢)
    -- case 000: h38=0,h39=0,h40=0 -> hL0 (byte Main[29])
    · rw [hL0]; congr 1; apply bitVec_ofNat8_eq_of_mod
      have := congr_arg Fin.val h_offset.1
      have := congr_arg Fin.val h29
      omega
    -- case 001: h38=0,h39=0,h40=1 -> hL4 (byte Main[31])
    · (conv_lhs => rw [show (Main[25] : Fin KB) = Main[25] + (-4 + 4) from by ring])
      rw [hL4]; congr 1; apply bitVec_ofNat8_eq_of_mod
      have := congr_arg Fin.val h_offset.1
      have := congr_arg Fin.val h31
      omega
    -- case 010: h38=0,h39=1,h40=0 -> hL2 (byte Main[30])
    · (conv_lhs => rw [show (Main[25] : Fin KB) = Main[25] + (-2 + 2) from by ring])
      rw [hL2]; congr 1; apply bitVec_ofNat8_eq_of_mod
      have := congr_arg Fin.val h_offset.1
      have := congr_arg Fin.val h30
      omega
    -- case 011: h38=0,h39=1,h40=1 -> hL6 (byte Main[32])
    · (conv_lhs => rw [show (Main[25] : Fin KB) = Main[25] + (-4 + (-2 + 6)) from by ring])
      rw [hL6]; congr 1; apply bitVec_ofNat8_eq_of_mod
      have := congr_arg Fin.val h_offset.1
      have := congr_arg Fin.val h32
      omega
    -- case 100: h38=1,h39=0,h40=0 -> hL1 (byte Main[29] >>> 8)
    · (conv_lhs => rw [show (Main[25] : Fin KB) = Main[25] + (-1 + 1) from by ring])
      rw [hL1]; congr 1; apply bitVec_ofNat8_eq_of_mod
      have hzero : ((1 + -1 : Fin KB) * Main[42]) = 0 := by
        change (0 : Fin KB) * Main[42] = 0; rw [zero_mul]
      have hsub : (Main[41] + -Main[42] : Fin KB) = Main[41] - Main[42] :=
        (sub_eq_add_neg Main[41] Main[42]).symm
      have h43_high : Main[43] = (Main[41] - Main[42]) * 2122383361 := by
        rw [h_offset.1, hsub, hzero, add_zero]
      have h44val : Main[43].val = ((Main[41] - Main[42]) * 2122383361).val :=
        congr_arg Fin.val h43_high
      have h30eq : Main[41].val = Main[29].val := congr_arg Fin.val h29
      rw [Nat.shiftRight_eq_div_pow]
      rw [h30eq, ← h44val] at h_decomp
      clear *- h_decomp h42_lt h43_lt
      omega
    -- case 101: h38=1,h39=0,h40=1 -> hL5 (byte Main[31] >>> 8)
    · (conv_lhs => rw [show (Main[25] : Fin KB) = Main[25] + (-4 + (-1 + 5)) from by ring])
      rw [hL5]; congr 1; apply bitVec_ofNat8_eq_of_mod
      have hzero : ((1 + -1 : Fin KB) * Main[42]) = 0 := by
        change (0 : Fin KB) * Main[42] = 0; rw [zero_mul]
      have hsub : (Main[41] + -Main[42] : Fin KB) = Main[41] - Main[42] :=
        (sub_eq_add_neg Main[41] Main[42]).symm
      have h43_high : Main[43] = (Main[41] - Main[42]) * 2122383361 := by
        rw [h_offset.1, hsub, hzero, add_zero]
      have h44val : Main[43].val = ((Main[41] - Main[42]) * 2122383361).val :=
        congr_arg Fin.val h43_high
      have h32eq : Main[41].val = Main[31].val := congr_arg Fin.val h31
      rw [Nat.shiftRight_eq_div_pow]
      rw [h32eq, ← h44val] at h_decomp
      clear *- h_decomp h42_lt h43_lt
      omega
    -- case 110: h38=1,h39=1,h40=0 -> hL3 (byte Main[30] >>> 8)
    · (conv_lhs => rw [show (Main[25] : Fin KB) = Main[25] + (-2 + (-1 + 3)) from by ring])
      rw [hL3]; congr 1; apply bitVec_ofNat8_eq_of_mod
      have hzero : ((1 + -1 : Fin KB) * Main[42]) = 0 := by
        change (0 : Fin KB) * Main[42] = 0; rw [zero_mul]
      have hsub : (Main[41] + -Main[42] : Fin KB) = Main[41] - Main[42] :=
        (sub_eq_add_neg Main[41] Main[42]).symm
      have h43_high : Main[43] = (Main[41] - Main[42]) * 2122383361 := by
        rw [h_offset.1, hsub, hzero, add_zero]
      have h44val : Main[43].val = ((Main[41] - Main[42]) * 2122383361).val :=
        congr_arg Fin.val h43_high
      have h31eq : Main[41].val = Main[30].val := congr_arg Fin.val h30
      rw [Nat.shiftRight_eq_div_pow]
      rw [h31eq, ← h44val] at h_decomp
      clear *- h_decomp h42_lt h43_lt
      omega
    -- case 111: h38=1,h39=1,h40=1 -> hL7 (byte Main[32] >>> 8)
    · (conv_lhs => rw [show (Main[25] : Fin KB) = Main[25] + (-4 + (-2 + (-1 + 7))) from by ring])
      rw [hL7]; congr 1; apply bitVec_ofNat8_eq_of_mod
      have hzero : ((1 + -1 : Fin KB) * Main[42]) = 0 := by
        change (0 : Fin KB) * Main[42] = 0; rw [zero_mul]
      have hsub : (Main[41] + -Main[42] : Fin KB) = Main[41] - Main[42] :=
        (sub_eq_add_neg Main[41] Main[42]).symm
      have h43_high : Main[43] = (Main[41] - Main[42]) * 2122383361 := by
        rw [h_offset.1, hsub, hzero, add_zero]
      have h44val : Main[43].val = ((Main[41] - Main[42]) * 2122383361).val :=
        congr_arg Fin.val h43_high
      have h33eq : Main[41].val = Main[32].val := congr_arg Fin.val h32
      rw [Nat.shiftRight_eq_div_pow]
      rw [h33eq, ← h44val] at h_decomp
      clear *- h_decomp h42_lt h43_lt
      omega

-- correct_lbu unfolds Load chip + Sail memory read spec
theorem correct_lbu (Main : Vector (Fin KB) 47)
    (s : SailState) (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (LoadByte.constraints Main).allHold)
    (state_cstrs : (LoadByte.constraints Main).initialState s)
    (h_is_lbu : Main[46] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (sp1_imm_c Main)).toNat
      reg_val + offset + 1 < 2 ^ 64)
    (h_below_clint :
      let reg_val := Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]
      let offset := BitVec.signExtend 64 (sp1_imm_c Main)
      BitVec.toNat (reg_val + offset) + 1 ≤ 33554432) :
    let op_a := sp1_op_a Main
    let op_b := sp1_ob_b Main
    let imm_c := sp1_imm_c Main
    (spec_lbu imm_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_load_byte Main).run s := by
  extract_lets op_a op_b imm_c
  obtain ⟨h_mprv_disabled, h_cur_privilege⟩ := hs_config
  rw [SP1ConstraintList.allHold, allHold_constraints_iff_of_is_lbu Main h_is_lbu] at h_cstrs
  obtain ⟨h_addr, h38, h39, h40, h28, hb,
    h_cpu, h_reader, h35, h33', hds, h36, h37, hmem, hmem',
    h45_zero, h13, h29, h30, h31, h32, h34, h_offset⟩ := h_cstrs
  -- Extract reader facts
  simp [ITypeReader.constraints] at h_reader
  simp [SP1Constraint.toProp, Opcode.ofNat, Nat.ble, and_assoc] at h_reader
  obtain ⟨h14, h21, h6, rest⟩ := h_reader
  simp [Fin.lt_def] at rest
  have h2728 : ¬ (Main[26] = 0 ∧ Main[27] = 0) := by clear *- h28; aesop
  -- Extract initial-state facts
  simp [LoadByte.constraints, AddressOperation.constraints,
    SP1Constraint.toStateProp, AddrAddOperation.constraints,
    CPUState.constraints, ITypeReader.constraints, BitVec.ofNatLT_eq_ofNat,
    Opcode.ofNat, Nat.ble, h6, h14, h2728, h45_zero, h_is_lbu] at state_cstrs
  obtain ⟨h_read_pc, h6_op_a, h14_op_a, hload⟩ := state_cstrs
  rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_read_pc
  have h6 : BitVec.ofNat 5 Main[6] ≠ 0#5 := by simp [← BitVec.toNat_inj]; omega
  have h44_zero : Main[44] = 0 := h_offset.2
  -- The immediate fits into a 12-bit word
  have hu6421 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := by
    apply Word.isU64_of_cases <;> {clear *- rest; simp_all}
  have h42_lt : Main[42].val < 256 := by exact_mod_cast h34.1
  have h42hi_lt : ((Main[41] - Main[42]) * 2122383361).val < 256 := by exact_mod_cast h34.2
  -- Main[43] < 256: derived from byte equation + h38 disjunction
  have h43_lt : Main[43].val < 256 := by
    rcases h38 with h38 | h38
    · -- Main[38] = 0 ⇒ Main[43] = Main[42]
      have heq : Main[43] = Main[42] := by
        have := h_offset.1; rw [h38] at this; simpa using this
      rw [heq]; exact h42_lt
    · -- Main[38] = 1 ⇒ Main[43] = (Main[41] - Main[42]) * 2122383361
      have heq : Main[43] = (Main[41] - Main[42]) * 2122383361 := by
        have := h_offset.1; rw [h38] at this; simpa using this
      rw [heq]; exact h42hi_lt
  have h_limb_fin : Main[42] + ((Main[41] - Main[42]) * 2122383361) * (2 ^ 8 : Fin KB) = Main[41] := by
    clear *- h34
    have h1 : (Main[41] - Main[42]) * 2122383361 * (2 ^ 8 : Fin KB) =
              (Main[41] - Main[42]) * ((2122383361 : Fin KB) * (2 ^ 8 : Fin KB)) := by ring
    have h2 : ((2122383361 : Fin KB) * (2 ^ 8 : Fin KB)) = 1 := by decide
    rw [h1, h2, mul_one]; ring
  have h_decomp : Main[41].val = Main[42].val + ((Main[41] - Main[42]) * 2122383361).val * 256 :=
    nat_decomp_of_inv8_decomp _ _ _ h_limb_fin h42_lt h42hi_lt
  have h21' : BitVec.signExtend 64 (BitVec.ofNat 12 (Main[21] : ℕ)) =
      Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] := h21.symm
  have haddr_add := AddrAddOperation.spec_of_constraints _ _ (by
    clear *- rest; simp_all only) hu6421 _ h_addr
  obtain ⟨_, haddr_eq⟩ := haddr_add
  simp only [AddrAddOperation.spec, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ] at haddr_eq
  simp [spec_lbu, sp1_load_byte,
    sp1_op_a, sp1_ob_b, sp1_imm_c,
    op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
    EStateM.Result.map, execute_LOAD, h_read_pc, h6]
  rw [run_vmem_read_of_width_1' (BitVec.ofNat 5 Main[14])
    (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]])
    (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
    (BitVec.ofNat 8 Main[43].val)]
  -- Main goal: zero-extend path (is_unsigned = true)
  · have hext : BitVec.setWidth 64 (BitVec.ofNat 8 Main[43].val) =
        Word.toBitVec64 #v[Main[43], 0, 0, 0] :=
      setWidth64_ofNat8 Main[43] h43_lt
    simp [extend_value, zero_extend, Sail.BitVec.zeroExtend, bitVecToRegidxVal,
      hext, h44_zero, mul_zero, add_zero]
  -- Side condition: isInitialized
  · simp only [Fin.isValue, isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs,
      or_true, implies_true]
  -- Side condition: get_reg? of op_b
  · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
  -- Side condition: is_aligned_vaddr for width 1
  · simp only [is_aligned_vaddr, BitVec.toNat_add, Nat.reducePow, Int.natCast_emod, Nat.cast_add,
      Nat.cast_ofNat, Nat.cast_one, Int.tmod_one, BEq.rfl]
  -- Side condition: isValidMemConfig
  · constructor <;> simpa [Std.ExtDHashMap.get_insert]
  -- Side condition: fits in 2 ^ 64
  · exact h_fits_in_mem
  -- Side condition: below clint
  · exact h_below_clint
  -- Side condition: memory at addr contains byte Main[43]
  · rw [h21']
    have haddr_nat :
        (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat +
            (Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]]).toNat =
          Word.toNat #v[Main[25], Main[26], Main[27], 0] := by
      have hfits :
          (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat +
              (Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]]).toNat < 2 ^ 64 := by
        have := h_fits_in_mem
        simp only [sp1_imm_c] at this
        rw [← h21] at this
        omega
      have := congr_arg BitVec.toNat haddr_eq
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt hfits] at this
      rw [← this, Word.toBitVec64, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by simp [Word.toNat]; omega)]
    change s.mem[_]? = _
    rw [haddr_nat]
    obtain ⟨hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7⟩ := hload
    rcases h38 with h38 | h38 <;> rcases h39 with h39 | h39 <;> rcases h40 with h40 | h40
    all_goals (
      simp only [h38, h39, h40, Fin.isValue, zero_ne_one, one_ne_zero,
        or_true, true_or, or_self, or_false, false_or, mul_one, mul_zero, sub_zero,
        Fin.sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero, Nat.cast_ofNat,
        zero_mul, Nat.cast_one, one_mul, zero_add, neg_zero,
        hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7] at h29 h30 h31 h32 h_offset hL0 hL1 hL2 hL3 hL4 hL5 hL6 hL7 ⊢)
    -- case 000: h38=0,h39=0,h40=0 -> hL0 (byte Main[29])
    · rw [hL0]; congr 1; apply bitVec_ofNat8_eq_of_mod
      have := congr_arg Fin.val h_offset.1
      have := congr_arg Fin.val h29
      omega
    -- case 001: h38=0,h39=0,h40=1 -> hL4 (byte Main[31])
    · (conv_lhs => rw [show (Main[25] : Fin KB) = Main[25] + (-4 + 4) from by ring])
      rw [hL4]; congr 1; apply bitVec_ofNat8_eq_of_mod
      have := congr_arg Fin.val h_offset.1
      have := congr_arg Fin.val h31
      omega
    -- case 010: h38=0,h39=1,h40=0 -> hL2 (byte Main[30])
    · (conv_lhs => rw [show (Main[25] : Fin KB) = Main[25] + (-2 + 2) from by ring])
      rw [hL2]; congr 1; apply bitVec_ofNat8_eq_of_mod
      have := congr_arg Fin.val h_offset.1
      have := congr_arg Fin.val h30
      omega
    -- case 011: h38=0,h39=1,h40=1 -> hL6 (byte Main[32])
    · (conv_lhs => rw [show (Main[25] : Fin KB) = Main[25] + (-4 + (-2 + 6)) from by ring])
      rw [hL6]; congr 1; apply bitVec_ofNat8_eq_of_mod
      have := congr_arg Fin.val h_offset.1
      have := congr_arg Fin.val h32
      omega
    -- case 100: h38=1,h39=0,h40=0 -> hL1 (byte Main[29] >>> 8)
    · (conv_lhs => rw [show (Main[25] : Fin KB) = Main[25] + (-1 + 1) from by ring])
      rw [hL1]; congr 1; apply bitVec_ofNat8_eq_of_mod
      have hzero : ((1 + -1 : Fin KB) * Main[42]) = 0 := by
        change (0 : Fin KB) * Main[42] = 0; rw [zero_mul]
      have hsub : (Main[41] + -Main[42] : Fin KB) = Main[41] - Main[42] :=
        (sub_eq_add_neg Main[41] Main[42]).symm
      have h43_high : Main[43] = (Main[41] - Main[42]) * 2122383361 := by
        rw [h_offset.1, hsub, hzero, add_zero]
      have h44val : Main[43].val = ((Main[41] - Main[42]) * 2122383361).val :=
        congr_arg Fin.val h43_high
      have h30eq : Main[41].val = Main[29].val := congr_arg Fin.val h29
      rw [Nat.shiftRight_eq_div_pow]
      rw [h30eq, ← h44val] at h_decomp
      clear *- h_decomp h42_lt h43_lt
      omega
    -- case 101: h38=1,h39=0,h40=1 -> hL5 (byte Main[31] >>> 8)
    · (conv_lhs => rw [show (Main[25] : Fin KB) = Main[25] + (-4 + (-1 + 5)) from by ring])
      rw [hL5]; congr 1; apply bitVec_ofNat8_eq_of_mod
      have hzero : ((1 + -1 : Fin KB) * Main[42]) = 0 := by
        change (0 : Fin KB) * Main[42] = 0; rw [zero_mul]
      have hsub : (Main[41] + -Main[42] : Fin KB) = Main[41] - Main[42] :=
        (sub_eq_add_neg Main[41] Main[42]).symm
      have h43_high : Main[43] = (Main[41] - Main[42]) * 2122383361 := by
        rw [h_offset.1, hsub, hzero, add_zero]
      have h44val : Main[43].val = ((Main[41] - Main[42]) * 2122383361).val :=
        congr_arg Fin.val h43_high
      have h32eq : Main[41].val = Main[31].val := congr_arg Fin.val h31
      rw [Nat.shiftRight_eq_div_pow]
      rw [h32eq, ← h44val] at h_decomp
      clear *- h_decomp h42_lt h43_lt
      omega
    -- case 110: h38=1,h39=1,h40=0 -> hL3 (byte Main[30] >>> 8)
    · (conv_lhs => rw [show (Main[25] : Fin KB) = Main[25] + (-2 + (-1 + 3)) from by ring])
      rw [hL3]; congr 1; apply bitVec_ofNat8_eq_of_mod
      have hzero : ((1 + -1 : Fin KB) * Main[42]) = 0 := by
        change (0 : Fin KB) * Main[42] = 0; rw [zero_mul]
      have hsub : (Main[41] + -Main[42] : Fin KB) = Main[41] - Main[42] :=
        (sub_eq_add_neg Main[41] Main[42]).symm
      have h43_high : Main[43] = (Main[41] - Main[42]) * 2122383361 := by
        rw [h_offset.1, hsub, hzero, add_zero]
      have h44val : Main[43].val = ((Main[41] - Main[42]) * 2122383361).val :=
        congr_arg Fin.val h43_high
      have h31eq : Main[41].val = Main[30].val := congr_arg Fin.val h30
      rw [Nat.shiftRight_eq_div_pow]
      rw [h31eq, ← h44val] at h_decomp
      clear *- h_decomp h42_lt h43_lt
      omega
    -- case 111: h38=1,h39=1,h40=1 -> hL7 (byte Main[32] >>> 8)
    · (conv_lhs => rw [show (Main[25] : Fin KB) = Main[25] + (-4 + (-2 + (-1 + 7))) from by ring])
      rw [hL7]; congr 1; apply bitVec_ofNat8_eq_of_mod
      have hzero : ((1 + -1 : Fin KB) * Main[42]) = 0 := by
        change (0 : Fin KB) * Main[42] = 0; rw [zero_mul]
      have hsub : (Main[41] + -Main[42] : Fin KB) = Main[41] - Main[42] :=
        (sub_eq_add_neg Main[41] Main[42]).symm
      have h43_high : Main[43] = (Main[41] - Main[42]) * 2122383361 := by
        rw [h_offset.1, hsub, hzero, add_zero]
      have h44val : Main[43].val = ((Main[41] - Main[42]) * 2122383361).val :=
        congr_arg Fin.val h43_high
      have h33eq : Main[41].val = Main[32].val := congr_arg Fin.val h32
      rw [Nat.shiftRight_eq_div_pow]
      rw [h33eq, ← h44val] at h_decomp
      clear *- h_decomp h42_lt h43_lt
      omega

end LoadByte

end Load
