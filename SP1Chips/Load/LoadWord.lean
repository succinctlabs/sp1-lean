import SP1Foundations
import SP1Chips.Load.LoadWord.Constraints
import LeanRV64IM.Specialization
import LeanRV64IM.RiscvMem
import LeanRV64IM.RiscvInstsEnd

open LeanRV64IM.Functions

namespace Load

namespace LoadWord

instance : ReflBEq Privilege where
  rfl := by
    intro a
    cases a <;> trivial

instance : ReflBEq SATPMode where
  rfl := by
    intro a
    cases a <;> trivial

variable
  (Main : Vector (Fin BB) 44)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_lw : Main[42] = 1)

private theorem is_lw_eq_not_lwu
  (cstrs : (constraints Main).allHold)
  (h_is_lw : Main[42] = 1)
  -- (h_is_real : Main[28] + Main[29] + Main[30] + Main[31] + Main[32] + Main[33] = 1)
  : Main[43] = 0 := by
  simp [constraints, SP1ConstraintList.allHold, List.Forall, AddressOperation.constraints, h_is_lw, sub_eq_zero] at cstrs
  have h_is_lwu_is_bool : Main[43] = 0 ∨ Main[43] = 1 := by simp_all only
  cases h_is_lwu_is_bool
  · assumption
  rename_i h_is_lwu
  simp [h_is_lwu] at cstrs

def spec_lw (imm : BitVec 12) (rs2 rs1 : regidx) : SailM ExecutionResult :=
  do
    Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
    execute_LOAD imm rs2 rs1 false 4

def sp1_op_a : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[6] ?_
    show Main[6] < 32

    have h_not_lwu : Main[43] = 0 := is_lw_eq_not_lwu Main cstrs h_is_lw
    simp [constraints, AddressOperation.constraints, AddrAddOperation.constraints, CPUState.constraints, ITypeReader.constraints, SP1Constraint.toProp, List.Forall, h_is_lw, h_not_lwu] at cstrs
    simp_all only

def sp1_op_b : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[14] ?_
    show Main[14] < 32

    have h_not_lwu : Main[43] = 0 := is_lw_eq_not_lwu Main cstrs h_is_lw
    simp [constraints, AddressOperation.constraints, AddrAddOperation.constraints, CPUState.constraints, ITypeReader.constraints, SP1Constraint.toProp, List.Forall, h_is_lw, h_not_lwu, Opcode.ofNat, ByteOpcode.ofNat, Nat.beq, Nat.ble] at cstrs
    simp_all only

def sp1_imm : BitVec 12 := BitVec.ofNat 12 Main[21].val

def sp1_lw : SailM ExecutionResult :=
  do
    let op_a := sp1_op_a Main cstrs h_is_lw
    Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
    Sail.write_reg op_a (Word.toBitVec64 #v[Main[39], Main[40], Main[41] * 65536, Main[42] * 65536])
    pure RETIRE_SUCCESS

attribute [simp] bind StateT.bind ExceptT.bind EStateM.bind ExceptT.bindCont get getThe MonadStateOf.get StateT.get EStateM.get pure StateT.pure ExceptT.pure EStateM.pure Functor.map StateT.map ExceptT.map EStateM.map modify modifyGet EStateM.modifyGet StateT.modifyGet MonadStateOf.modifyGet liftM monadLift MonadLift.monadLift ExceptT.lift StateT.lift ExceptT.mk StateT.run ExceptT.run EStateM.run Sail.SailME.run

set_option debug.skipKernelTC true in
set_option maxHeartbeats 20000000 in
theorem correct
  (Main : Vector (Fin BB) 44)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (state_cstrs : (constraints Main).initialState s)
  (h_is_lw : Main[42] = 1)
  (h_mstatus : s.regs.get? Register.mstatus = some 0)
  (h_priv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
  (mem0 mem1 mem2 mem3 : BitVec 8)
  -- assumptions!
  : let op_a := sp1_op_a Main cstrs h_is_lw
    let op_b := sp1_op_b Main cstrs h_is_lw
    let op_c := sp1_imm Main
    (spec_lw op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_lw Main cstrs h_is_lw).run s
  := by
    extract_lets op_a op_b op_c
    have h_not_lwu : Main[43] = 0 := is_lw_eq_not_lwu Main cstrs h_is_lw

    simp [constraints, AddressOperation.constraints, AddrAddOperation.constraints, U16MSBOperation.constraints, CPUState.constraints, ITypeReader.constraints, SP1Constraint.toStateProp, List.Forall, h_is_lw, h_not_lwu, Opcode.ofNat, ByteOpcode.ofNat, Nat.beq, Nat.ble] at state_cstrs
    obtain ⟨h_read_pc, h_read_op_a', h_read_op_b', h_read_mem⟩ := state_cstrs

    have h_op_a_is_reg : Main[6] < 32 :=
      by
        simp [constraints, AddressOperation.constraints, AddrAddOperation.constraints, CPUState.constraints, ITypeReader.constraints, SP1Constraint.toProp, List.Forall, h_is_lw, h_not_lwu, Opcode.ofNat, ByteOpcode.ofNat, Nat.beq, Nat.ble] at cstrs
        simp_all only
    have h_read_op_a := h_read_op_a' h_op_a_is_reg
    clear h_read_op_a'
    have h_op_b_is_reg : Main[14] < 32 :=
      by
        simp [constraints, AddressOperation.constraints, AddrAddOperation.constraints, CPUState.constraints, ITypeReader.constraints, SP1Constraint.toProp, List.Forall, h_is_lw, h_not_lwu, Opcode.ofNat, ByteOpcode.ofNat, Nat.beq, Nat.ble] at cstrs
        simp_all only
    have h_read_op_b := h_read_op_b' h_op_b_is_reg
    clear h_read_op_b'

    simp [spec_lw, execute_LOAD]

    simp [Sail.readReg, PreSail.readReg, h_read_pc]

    simp [Sail.assert, PreSail.assert, LeanRV64IM.Functions.xlen_bytes]

    simp [vmem_read]
    simp [ext_data_get_addr]
    simp [op_b, sp1_op_b]

    simp [Sail.writeReg, PreSail.writeReg, Sail.rX_bits_eq_get_reg?_no_run, h_read_op_b, Option.elim, Option.toSailM] 

    simp [check_misaligned, LeanRV64IM.Functions.plat_enable_misaligned_access, LeanRV64IM.Functions.not]

    have h_op_c_is_signExtend : Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] = BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) := by
      simp [constraints, AddressOperation.constraints, AddrAddOperation.constraints, CPUState.constraints, ITypeReader.constraints, SP1Constraint.toProp, List.Forall, h_is_lw, h_not_lwu, Opcode.ofNat, ByteOpcode.ofNat, Nat.beq, Nat.ble] at cstrs
      simp_all only

    -- TODO(gzgz): will come from `state_cstrs`
    have h_trusted_aligned : ((s.get_reg? (BitVec.ofNat 5 Main[14].val)).get! + Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]]) % 4 = 0 := by sorry
    rw [←BitVec.ofNatLT_eq_ofNat h_op_b_is_reg, h_read_op_b, h_op_c_is_signExtend, Option.get!_some] at h_trusted_aligned

    have h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + sign_extend op_c)) 4 = true := by
      unfold is_aligned_vaddr
      simp only [op_b, op_c, sp1_op_b, sp1_imm, sign_extend, Sail.BitVec.signExtend]
      clear * - h_trusted_aligned
      simp [BitVec.add_def, BitVec.umod_def, BitVec.ofNat, BitVec.ofNatLT] at h_trusted_aligned
      -- simp [BitVec.add_def, Int.tmod_def]
      simp only [beq_iff_eq]
      sorry

    simp [h_is_aligned, split_misaligned, bits_of_virtaddr]
    
    simp [untilFuelM, untilFuelM.go, Sail.assert, PreSail.assert]

    simp [translateAddr]
    simp [Sail.readReg, PreSail.readReg, Std.ExtDHashMap.get?_insert, h_mstatus, h_priv]
    simp [effectivePrivilege, _get_Mstatus_MPRV, Sail.BitVec.extractLsb, translationMode]

    clear * - h_mstatus h_priv mem0 mem1 mem2 mem3

    have h_read_mem0 : s.mem[(Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + sign_extend op_c).toNat]? = some mem0 := by sorry
    have h_read_mem1 : s.mem[(Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + sign_extend op_c).toNat + 1]? = some mem1 := by sorry
    have h_read_mem2 : s.mem[(Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + sign_extend op_c).toNat + 2]? = some mem2 := by sorry
    have h_read_mem3 : s.mem[(Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + sign_extend op_c).toNat + 3]? = some mem3 := by sorry

    have h_always_within_ram : within_phys_mem (physaddr.Physaddr (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + sign_extend op_c)) 4 = pure true := by
      sorry

    -- TODO(gzgz): comes from chip_cstrs
    have h_op_a_not_x0 : op_a ≠ 0#5 := by sorry

    simp [-BitVec.toNat_add, mem_read, Sail.readReg, PreSail.readReg, Std.ExtDHashMap.get?_insert, h_mstatus, h_priv, effectivePrivilege, _get_Mstatus_MPRV, Sail.BitVec.extractLsb, translationMode, mem_read_priv, mem_read_priv_meta, checked_mem_read, phys_access_check, bits_of_virtaddr, LeanRV64IM.Functions.sys_pmp_count, within_mmio_readable, get_config_rvfi, Sail.BitVec.addInt, zero_extend, Sail.BitVec.zeroExtend, h_always_within_ram, ext_check_phys_mem_read, phys_mem_read, read_kind_of_flags, read_ram, Sail.sail_mem_read, PreSail.sail_mem_read, PreSail.readBytes, PreSail.readByte, h_read_mem0, h_read_mem1, h_read_mem2, h_read_mem3, MemoryOpResult_drop_meta, h_op_a_not_x0]

    simp [misaligned_order, sys_misaligned_order_decreasing, extend_value, sign_extend, Sail.BitVec.signExtend]
    sorry

end LoadWord

end Load
