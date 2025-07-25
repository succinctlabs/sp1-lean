import SP1Foundations
import SP1Operations.Operation.AddOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ITypeReader
import LeanRV64IM.RiscvInstsEnd

import SP1Chips.Jalr.Constraints

namespace Word

def toBitVec64LT (w : Word (Fin BB)) (h_w : w.isU64) : BitVec 64 :=
  BitVec.ofNatLT w.toNat (by
    simp [Word.toNat]
    have := h_w 0
    have := h_w 1
    have := h_w 2
    have := h_w 3
    simp at *
    linarith)

end Word

section

set_option autoImplicit false

namespace Jalr

open PreSail (SequentialState)
open LeanRV64IM.Functions

variable
  (Main : Vector (Fin BB) 38)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_real : Main[29] = 1)

def spec_jalr (imm : BitVec 12) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_JALR imm rs1 rd
  pure ()

def sp1_imm : BitVec 12 := BitVec.ofNat 12 Main[21].val
  -- by
  --   refine BitVec.ofNatLT
  --     (Main[21].val + Main[22].val * 2^16 + Main[23].val * 2^32 + Main[24].val * 2^48)
  --     ?_

  --   have reader_cstrs := by
  --     simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp] at cstrs
  --     exact cstrs.2.2.1

  --   clear cstrs
  --   simp [ITypeReader.constraints, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq, SP1Constraint.toProp] at reader_cstrs

  --   have trusted_instr_cstrs := reader_cstrs.1
  --   clear reader_cstrs

  --   aesop

def sp1_op_b : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[14] ?_
    simp

    have reader_cstrs := by
      simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp] at cstrs
      exact cstrs.2.2.1

    clear cstrs
    simp [ITypeReader.constraints, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq, SP1Constraint.toProp] at reader_cstrs

    have trusted_instr_cstrs := reader_cstrs.1
    clear reader_cstrs

    itauto

def sp1_op_a : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[6] ?_
    simp

    have reader_cstrs := by
      simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp] at cstrs
      exact cstrs.2.2.1

    clear cstrs
    simp [ITypeReader.constraints, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq, SP1Constraint.toProp] at reader_cstrs

    have trusted_instr_cstrs := reader_cstrs.1
    clear reader_cstrs

    itauto

def sp1_jalr : SailM Unit := do
  let op_a := sp1_op_a Main cstrs h_is_real
  SailState.write_reg op_a (Word.toBitVec64 #v[Main[34], Main[35], Main[36], Main[37]])
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[30], Main[31], Main[32], Main[33]])

-- attribute [simp] bind StateT.bind EStateM.bind get getThe MonadStateOf.get StateT.get EStateM.get modify modifyGet MonadStateOf.modifyGet StateT.modifyGet EStateM.modifyGet pure EStateM.pure

-- set_option maxHeartbeats 0 in
-- theorem correct
--   (state_cstrs : (constraints Main).initialState s) :
--   let imm := sp1_imm Main -- cstrs h_is_real
--   let op_b := sp1_op_b Main cstrs h_is_real
--   let op_a := sp1_op_a Main cstrs h_is_real
--   (spec_jalr imm (.Regidx op_b) (.Regidx op_a)).run s = (sp1_jalr Main cstrs h_is_real).run s
--   :=
--   by
--     extract_lets imm op_b op_a

--     -- pull out state constraints about the contents of register and pc reads
--     simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, AddOperation.constraints, ITypeReader.constraints, CPUState.constraints, h_is_real] at state_cstrs
--     obtain ⟨read_pc, ⟨op_b_val_plus_imm_mul4, ⟨read_op_a, read_op_b⟩⟩⟩ := state_cstrs

--     -- pull out constraints
--     simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp] at cstrs
--     obtain ⟨res_cstrs, ⟨pc_cstrs, ⟨reader_cstrs, ⟨inc_pc_cstrs, chip_cstrs⟩⟩⟩⟩ := cstrs

--     simp [ITypeReader.constraints, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq, SP1Constraint.toProp] at reader_cstrs
--     obtain ⟨⟨h_op_b, h_c_sign_extend⟩, ⟨h_op_a, ⟨_, ⟨⟨h_c_0, ⟨h_c_1, ⟨h_c_2, h_c_3⟩⟩⟩, ⟨op_a_0_is_bool, ⟨op_a_0_iff_op_a_is_0, ⟨pc_mul_4, ⟨h_pc_0, ⟨h_pc_1, h_pc_2⟩⟩⟩⟩⟩⟩⟩⟩⟩ := reader_cstrs.1
--     let read_op_b' := read_op_b h_op_b

--     have b_is_u64 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := reader_cstrs.2.2.2.2.2.2.2.2.2.2
--     let b_bv64 : BitVec 64 := Word.toBitVec64LT #v[Main[15], Main[16], Main[17], Main[18]] b_is_u64

--     have imm_is_u64 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := by
--       refine Word.isU64_of_cases #v[Main[21], Main[22], Main[23], Main[24]] h_c_0 h_c_1 h_c_2 h_c_3

--     have pc_is_u64 : Word.isU64 #v[Main[3], Main[4], Main[5], 0] := by
--       exact Word.isU64_of_cases #v[Main[3], Main[4], Main[5], 0] h_pc_0 h_pc_1 h_pc_2 (by simp)

--     have ⟨res_is_u64, h_res⟩ := (AddOperation.correct #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[21], Main[22], Main[23], Main[24]] { value := #v[Main[30], Main[31], Main[32], Main[33]] } Main[29] h_is_real res_cstrs) b_is_u64 imm_is_u64
--     rw [Word.toBitVec64_LT_eq_toNat res_is_u64, Word.toBitVec64_LT_eq_toNat b_is_u64, Word.toBitVec64_LT_eq_toNat imm_is_u64] at h_res
--     simp [Word.toNat, h_c_1, h_c_2, h_c_3] at h_res

--     -- simp [AddOperation.spec, Word.toBitVec64, Word.toNat] at h_res

--     clear res_cstrs reader_cstrs pc_cstrs

--     simp [spec_jalr, sp1_jalr, EStateM.run, execute_JALR,
--       op_a, op_b, imm, sp1_op_a, sp1_op_b, sp1_imm,
--       EStateM.run_bind]


--     simp [Sail.readReg, Sail.writeReg, PreSail.readReg, PreSail.writeReg]

--     simp [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, modify,
--       modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, read_pc]

--     simp only [EStateM.pure]

--     rw [SailState.get_reg?_is_rX]

--     simp [SailState.get_reg?, SequentialState.regs]

--     rw [Std.ExtDHashMap.get?_insert]

--     simp [SailState.reg_idx_never_nextPC, Option.toSailM]

--     simp [SailState.get_reg?] at read_op_b'

--     simp [bind, StateT.bind, EStateM.bind, get, getThe, MonadStateOf.get, StateT.get, EStateM.get, pure, EStateM.pure, StateT.map, EStateM.map, modify, modifyGet, EStateM.modifyGet, StateT.modifyGet, MonadStateOf.modifyGet]

--     rw [read_op_b']

--     simp

--     simp [bind, StateT.bind, EStateM.bind, get, getThe, MonadStateOf.get, StateT.get, EStateM.get, pure, EStateM.pure, StateT.map, EStateM.map, modify, modifyGet, EStateM.modifyGet, StateT.modifyGet, MonadStateOf.modifyGet]

--     simp [ext_control_check_addr, bits_of_virtaddr]

--     rw [Word.toBitVec64_LT_eq_toNat b_is_u64]

--     simp [Word.toNat]

--     simp [Opcode.ofNat, Nat.ble, Nat.beq] at op_b_val_plus_imm_mul4

--     rw [←BitVec.ofNatLT_eq_ofNat (w := 5) (n := Main[14].val) h_op_b] at op_b_val_plus_imm_mul4

--     rw [read_op_b h_op_b] at op_b_val_plus_imm_mul4

--     simp [Option.get!] at op_b_val_plus_imm_mul4

--     simp [Word.toBitVec64_LT_eq_toNat b_is_u64, Word.toNat] at op_b_val_plus_imm_mul4

--     simp [Word.toBitVec64_LT_eq_toNat imm_is_u64, Word.toNat] at op_b_val_plus_imm_mul4

--     simp [sign_extend, Sail.BitVec.signExtend]

--     rw [←h_c_sign_extend]

--     simp [Word.toBitVec64_LT_eq_toNat imm_is_u64, Word.toNat]

--     obtain ⟨op_b_plus_val_signExtend_imm_0, op_b_plus_val_signExtend_imm_1⟩ := BitVec.mul4_means_0_1_are_0 op_b_val_plus_imm_mul4

--     conv =>
--       lhs
--       arg 2
--       arg 1
--       simp [Sail.BitVec.update, Sail.BitVec.updateSubrange', Sail.BitVec.access]
--       simp [sign_extend, Sail.BitVec.signExtend]
--       rw [op_b_plus_val_signExtend_imm_1]
--       simp [bit_to_bool, bool_bit_backwards, BitVec.ofBool, cond]
--     simp [bind, StateT.bind, EStateM.bind, get, getThe, MonadStateOf.get, StateT.get, EStateM.get, pure, EStateM.pure, StateT.map, EStateM.map, modify, modifyGet, EStateM.modifyGet, StateT.modifyGet, MonadStateOf.modifyGet]

--     -- Now unfold the bind to substitute false
--     conv =>
--       lhs
--       arg 2
--       simp [EStateM.bind]

--     -- try to reduce currentlyEnabled
--     simp only [currentlyEnabled, hartSupports]
--     simp [Sail.readReg, PreSail.readReg]
--     simp [bind, StateT.bind, EStateM.bind, get, getThe, MonadStateOf.get, StateT.get, EStateM.get, pure, EStateM.pure, StateT.map, EStateM.map, modify, modifyGet, EStateM.modifyGet, StateT.modifyGet, MonadStateOf.modifyGet]

--     simp [SailState.sp1_no_misa]

--     -- Now simplify the mapped pure computation
--     conv =>
--       lhs
--       arg 2
--       intro s'
--       simp only [Functor.map]
--       change match EStateM.Result.ok false s' with
--         | EStateM.Result.ok a s => _
--         | EStateM.Result.error e s => EStateM.Result.error e s
--       simp

--     cases op_a_0_is_bool with
--     | inl op_a_0_is_0 =>
--         -- TODO(gzgz): god this is awful
--         have op_a_not_x0 : op_a ≠ 0 := by
--           simp only [op_a, sp1_op_a, BitVec.ofNatLT, ne_eq]
--           intro h
--           simp [op_a_0_is_0] at op_a_0_iff_op_a_is_0
--           apply op_a_0_iff_op_a_is_0
--           have := congrArg (·.toFin.val) h
--           simp at this
--           exact this
--         simp [op_a, sp1_op_a] at op_a_not_x0

--         simp [← bind_pure_comp]

--         simp only [bind, EStateM.bind, EStateM.pure, EStateM.get, EStateM.map, Bool.false_and,
--           cond_false, Std.ExtDHashMap.get?_insert_self, EStateM.modifyGet, pure]

--         rw [←SailState.wX_bits_is_regidx_write]
--         simp [SailState.regidx_write]
--         simp [op_a_not_x0]
--         simp [bind, StateT.bind, EStateM.bind, get, getThe, MonadStateOf.get, StateT.get, EStateM.get, pure, EStateM.pure, StateT.map, EStateM.map, modify, modifyGet, EStateM.modifyGet, StateT.modifyGet, MonadStateOf.modifyGet]


--         have pc_sum_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 < 2^64 :=
--           by
--             clear * - h_pc_0 h_pc_1 h_pc_2
--             simp at *
--             omega

--         rw [←(BitVec.ofNatLT_eq_ofNat pc_sum_u64)]
--         simp [bind, StateT.bind, EStateM.bind, get, getThe, MonadStateOf.get, StateT.get, EStateM.get, pure, EStateM.pure, StateT.map, EStateM.map, modify, modifyGet, EStateM.modifyGet, StateT.modifyGet, MonadStateOf.modifyGet]


--         rw [Word.toBitVec64_LT_eq_toNat res_is_u64]
--         simp [Word.toNat]
--         rw [h_res]
--         clear h_res

--         obtain ⟨a_write_is_u64, h_a_write⟩ :=
--           AddOperation.correct
--           #v[Main[3], Main[4], Main[5], 0]
--           #v[4, 0, 0, 0]
--           { value := #v[Main[34], Main[35], Main[36], Main[37]] }
--           (Main[29] - Main[13])
--           (by simp [h_is_real, op_a_0_is_0])
--           inc_pc_cstrs
--           pc_is_u64
--           (by simp [Word.isU64]; clear * - h_pc_0 h_pc_1 h_pc_2; trivial)
--         rw [Word.toBitVec64_LT_eq_toNat a_write_is_u64, Word.toBitVec64_LT_eq_toNat pc_is_u64] at h_a_write
--         conv at h_a_write =>
--           rhs
--           simp [Word.toBitVec64, Word.toNat]
--           rfl

--         rw [Word.toBitVec64_LT_eq_toNat a_write_is_u64]
--         simp
--         rw [h_a_write]

--         simp [SailState.write_reg, op_a_not_x0]
--         simp [bind, StateT.bind, EStateM.bind, get, getThe, MonadStateOf.get, StateT.get, EStateM.get, pure, EStateM.pure, StateT.map, EStateM.map, modify, modifyGet, EStateM.modifyGet, StateT.modifyGet, MonadStateOf.modifyGet]

--         apply Std.ExtDHashMap.ext_get?

--         intro idx
--         by_cases h_nextPC : Register.nextPC = idx
--         · rw [Std.ExtDHashMap.get?_insert]
--           simp [h_nextPC]
--           rw [Std.ExtDHashMap.get?_insert]
--           simp [h_nextPC]

--           simp [Sail.BitVec.update, Sail.BitVec.updateSubrange']
--           apply BitVec.helper
--           exact op_b_val_plus_imm_mul4

--         by_cases h_op_a : (reg_idx_to_Register op_a) = idx
--         · simp [op_a, sp1_op_a] at h_op_a

--           repeat (rw [Std.ExtDHashMap.get?_insert]; simp [h_nextPC, h_op_a])
--         simp [op_a, sp1_op_a] at h_op_a
--         repeat (rw [Std.ExtDHashMap.get?_insert]; simp [h_nextPC, h_op_a])
--     | inr op_a_0_is_1 =>
--         have op_a_is_x0 : op_a = 0 := by
--           clear * - op_a_0_iff_op_a_is_0 op_a_0_is_1
--           simp [op_a, sp1_op_a]
--           simp_all only [Fin.isValue, true_iff, Fin.coe_ofNat_eq_mod, Nat.zero_mod, BitVec.ofNatLT_zero]
--         simp [op_a, sp1_op_a] at op_a_is_x0

--         simp [← bind_pure_comp]
--         simp [bind, StateT.bind, EStateM.bind, get, getThe, MonadStateOf.get, StateT.get, EStateM.get, pure, EStateM.pure, StateT.map, EStateM.map, modify, modifyGet, EStateM.modifyGet, StateT.modifyGet, MonadStateOf.modifyGet]
--         simp [wX_bits, wX, op_a_is_x0]
--         simp [bind, StateT.bind, EStateM.bind, get, getThe, MonadStateOf.get, StateT.get, EStateM.get, pure, EStateM.pure, StateT.map, EStateM.map, modify, modifyGet, EStateM.modifyGet, StateT.modifyGet, MonadStateOf.modifyGet]


--         have pc_sum_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 < 2^64 :=
--           by
--             clear * - h_pc_0 h_pc_1 h_pc_2
--             simp at *
--             omega

--         conv =>
--           rhs
--           arg 2
--           simp [SailState.write_reg]
--         simp [op_a_0_is_1] at chip_cstrs
--         obtain ⟨_, ⟨_, ⟨_, ⟨op_a3_is_0, ⟨op_a0_is_0, ⟨op_a1_is_0, op_a2_is_0⟩⟩⟩⟩⟩⟩ := chip_cstrs
--         simp [op_a0_is_0, op_a3_is_0, op_a1_is_0, op_a2_is_0]
--         conv =>
--           rhs
--           arg 2
--           simp [Word.toBitVec64, Word.toNat]
--         simp [bind, StateT.bind, EStateM.bind, get, getThe, MonadStateOf.get, StateT.get, EStateM.get, pure, EStateM.pure, StateT.map, EStateM.map, modify, modifyGet, EStateM.modifyGet, StateT.modifyGet, MonadStateOf.modifyGet]
--         -- move this block above before the `simp` and you can simp fine...

--         rw [Word.toBitVec64_LT_eq_toNat res_is_u64]
--         simp [Word.toNat]
--         rw [h_res]
--         clear h_res
--         refine congr_arg (s.regs.insert Register.nextPC) ?_
--         simp [Sail.BitVec.update, Sail.BitVec.updateSubrange']
--         apply BitVec.helper
--         exact op_b_val_plus_imm_mul4

/-
⊢ 18446744073709551614#64 &&&
    (↑Main[15] + ↑Main[16] * 65536 + ↑Main[17] * 4294967296 + ↑Main[18] * 281474976710656)#'⋯ + (↑Main[21])#'⋯ =
  (↑Main[15] + ↑Main[16] * 65536 + ↑Main[17] * 4294967296 + ↑Main[18] * 281474976710656)#'⋯ + (↑Main[21])#'⋯
-/
lemma BitVec_helper (x : BitVec 64) (hx : x[0] = 0) :
    18446744073709551614#64 &&& x = x := by
  sorry

set_option maxHeartbeats 0 in
theorem correct_cleanup
    (state_cstrs : (constraints Main).initialState s)
    (h_misa : Register.misa ∈ s.regs) :
    let imm := sp1_imm Main -- cstrs h_is_real
    let op_b := sp1_op_b Main cstrs h_is_real
    let op_a := sp1_op_a Main cstrs h_is_real
    (spec_jalr imm (.Regidx op_b) (.Regidx op_a)).run s = (sp1_jalr Main cstrs h_is_real).run s := by
  extract_lets imm op_b op_a

  -- pull out state constraints about the contents of register and pc reads
  simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, AddOperation.constraints, ITypeReader.constraints, CPUState.constraints, h_is_real] at state_cstrs
  obtain ⟨read_pc, ⟨op_b_val_plus_imm_mul4, ⟨read_op_a, read_op_b⟩⟩⟩ := state_cstrs

  -- pull out constraints
  simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp] at cstrs
  obtain ⟨res_cstrs, ⟨pc_cstrs, ⟨reader_cstrs, ⟨inc_pc_cstrs, chip_cstrs⟩⟩⟩⟩ := cstrs

  simp [ITypeReader.constraints, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq, SP1Constraint.toProp] at reader_cstrs
  obtain ⟨⟨h_op_b, h_c_sign_extend⟩, ⟨h_op_a, ⟨_, ⟨⟨h_c_0, ⟨h_c_1, ⟨h_c_2, h_c_3⟩⟩⟩, ⟨op_a_0_is_bool, ⟨op_a_0_iff_op_a_is_0, ⟨pc_mul_4, ⟨h_pc_0, ⟨h_pc_1, h_pc_2⟩⟩⟩⟩⟩⟩⟩⟩⟩ := reader_cstrs.1
  let read_op_b' := read_op_b h_op_b

  have b_is_u64 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := reader_cstrs.2.2.2.2.2.2.2.2.2.2
  let b_bv64 : BitVec 64 := Word.toBitVec64LT #v[Main[15], Main[16], Main[17], Main[18]] b_is_u64

  have imm_is_u64 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := by
    refine Word.isU64_of_cases #v[Main[21], Main[22], Main[23], Main[24]] h_c_0 h_c_1 h_c_2 h_c_3

  have pc_is_u64 : Word.isU64 #v[Main[3], Main[4], Main[5], 0] := by
    exact Word.isU64_of_cases #v[Main[3], Main[4], Main[5], 0] h_pc_0 h_pc_1 h_pc_2 (by simp)

  have ⟨res_is_u64, h_res⟩ := (AddOperation.correct #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[21], Main[22], Main[23], Main[24]] { value := #v[Main[30], Main[31], Main[32], Main[33]] } Main[29] h_is_real res_cstrs) b_is_u64 imm_is_u64
  -- rw [Word.toBitVec64_LT_eq_toNat res_is_u64, Word.toBitVec64_LT_eq_toNat b_is_u64, Word.toBitVec64_LT_eq_toNat imm_is_u64] at h_res
  -- simp [Word.toNat, h_c_1, h_c_2, h_c_3] at h_res

  have h_4_is_u64 : Word.isU64 #v[4,0,0,0] :=
    Word.isU64_of_cases _ (by trivial) (by trivial) (by trivial) (by trivial)

  have hmod4 : (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] +
                sign_extend (BitVec.ofNat 12 Main[21]))[1] = false := by sorry

  have hmod2 : (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] +
      Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]])[0] = 0 := by sorry

  clear res_cstrs reader_cstrs pc_cstrs

  simp [spec_jalr, sp1_jalr, execute_JALR,
    op_a, op_b, imm, sp1_op_a, sp1_op_b, sp1_imm, EStateM.run_bind]
  -- `simp` refuses to apply this itself
  rw [run_readReg]
  simp only [read_pc, hmod4, read_op_b', run_rX_bits, get_reg?_insert_nextPC, ext_control_check_addr,
    Sail.BitVec.access, bit_to_bool, Sail.BitVec.update, Sail.BitVec.updateSubrange',
    bits_of_virtaddr, BitVec.reduceAllOnes, BitVec.truncate_eq_setWidth, BitVec.reduceSetWidth,
    BitVec.shiftLeft_zero, BitVec.reduceNot, BitVec.setWidth_zero, BitVec.or_zero,
    Nat.one_lt_ofNat, getElem!_pos, BitVec.getElem_and, BitVec.reduceGetElem, Bool.true_and,
    BitVec.ofBool, BitVec.ofNat_eq_ofNat, cond_false, EStateM.run_bind,
    run_bool_bit_backwards, Bool.false_and, EStateM.run_map, run_writeReg, EStateM.Result.map_ok,
    currentlyEnabled, hartSupports, Bool.false_and, Bool.false_or, Bool.and_self,
    BitVec.ofNat_eq_ofNat, bind_pure_comp, Functor.map_map, EStateM.run_map]
  rw [map_const_run_readReg _ _ (by simp [h_misa])]
  simp only
  rw [run_readReg]
  simp only [Std.ExtDHashMap.get?_insert_self, run_wX_bits, BitVec.ofNat_eq_ofNat, sign_extend,
    Sail.BitVec.signExtend, ← h_c_sign_extend, EStateM.Result.map_ok]
  stop
  cases op_a_0_is_bool with
  | inl op_a_0_is_0 => {
    have h6 : Main[6] ≠ 0 := by simp_all
    have h6' : ∀ p : ↑Main[6] < 2 ^ 5, (BitVec.ofNatLT Main[6].val p : BitVec 5) ≠ 0#5 := by
      refine fun p h => h6 ?_
      simp [← BitVec.toFin_inj] at h
      rw [← Fin.val_inj] at h
      simpa using h
    simp only [h6', ↓reduceIte, LawfulMonadStateOf.insert_insert_insert_cancel,
      EStateM.Result.ok.injEq, SequentialState.mk.injEq, and_self, and_true, true_and]
    rw [BitVec_helper _ hmod2, h_res]
    refine congr_fun ?_ _
    have htemp : Main[29] - Main[13] = 1 := by simp [op_a_0_is_0, h_is_real]
    have := AddOperation.correct _ _ _ _ htemp inc_pc_cstrs
    specialize this pc_is_u64 h_4_is_u64
    rw [this.2]
    simp [BitVec.ofNat, Word.toBitVec64, Word.toNat]
    rfl
  }
  | inr op_a_0_is_1 => {
    have h6 : Main[6] = 0 := by simp_all
    have hl : Word.toBitVec64 #v[Main[34], Main[35], Main[36], Main[37]] = 0#64 := by
      simp [op_a_0_is_1, sub_eq_zero] at chip_cstrs
      obtain ⟨_, _, ⟨ha, hb, hc, hd⟩⟩ := chip_cstrs
      simp [ha, hb, hc, hd, Word.toBitVec64, ← BitVec.toFin_inj, Word.toNat]
    simp [h6, hl]
    rw [h_res, BitVec_helper]
    exact hmod2
  }

#eval BitVec.allOnes 64

end Jalr

#print axioms Jalr.correct_cleanup

end
