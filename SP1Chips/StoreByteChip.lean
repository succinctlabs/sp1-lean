import SP1Foundations
import SP1Chips.Store.StoreByte.Constraints
import SP1Operations.Operation.AddrAddOperation

open LeanRV64D.Functions Sail SailState

attribute [simp] LeanRV64D.Functions.xlen_bytes Sail.assert PreSail.assert
  ext_data_get_addr check_misaligned
  LeanRV64D.Functions.plat_enable_misaligned_access
  split_misaligned misaligned_order
  allowed_misaligned sys_misaligned_order_decreasing
  get_config_print_platform
  LeanRV64D.Functions.xlen
  _get_Mstatus_MPP _get_Mstatus_MPRV
  privLevel_of_bits default_write_acc

namespace Store

namespace StoreByte

noncomputable def spec_sb (imm : BitVec 12) (rs1 rs2 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  let width : ℕ := 1 -- single byte
  execute_STORE imm rs1 rs2 width

def sp1_op_a (Main : Vector (Fin KB) 52) : BitVec 5 :=
  BitVec.ofNat 5 Main[6]

def sp1_ob_b (Main : Vector (Fin KB) 52) : BitVec 5 :=
  BitVec.ofNat 5 Main[14]

def sp1_imm_c (Main : Vector (Fin KB) 52) : BitVec 12 :=
  BitVec.ofNat 12 (Word.toNat #v[Main[21], Main[22], Main[23], Main[24]])

def sp1_sb (Main : Vector (Fin KB) 52) : SailM ExecutionResult := do
  let op_a := sp1_op_a Main
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  let addr : BitVec 64 := Word.toBitVec64 #v[Main[26], Main[27], Main[28], 0]
  Sail.write_ram 64 1 0#64 addr (Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]])
  return RETIRE_SUCCESS

lemma run_vmem_write_of_width_1'
    (rs_addr_bv : BitVec 5)
    (reg_val : BitVec 64) -- thing inside `rs_addr_bv`
    (offset : BitVec 64)
    (data : BitVec 8) -- bigger for others
    (s : SailState)
    (hs : SailState.isInitialized s)
    (h_reg_val : s.get_reg? rs_addr_bv = some reg_val)
    (h_aligned : is_aligned_vaddr (virtaddr.Virtaddr (reg_val + offset)) 1 = true) ---width
    (hconfig : SailState.isValidMemConfig s hs)
    (h_does_fit : reg_val.toNat + offset.toNat + 1 ≤ --width
      (s.regs.get Register.plat_ram_size (hs _)).toNat) :
    (vmem_write (.Regidx rs_addr_bv) offset 1 data
      (AccessType.Write Data) false false false).run s = .ok (.Ok true)
        { s with mem := s.mem.insert (reg_val + offset).toNat data } := by
  obtain ⟨h_mprv_disabled, h_cur_privilege, h_clint_base, h_clint_size,
    h_plat_ram_base, h_plat_rom_base⟩ := hconfig
  have hmachine : (Privilege.Machine == Privilege.Machine) = true := rfl
  have hsatp_bare : (SATPMode.Bare == SATPMode.Bare) = true := rfl
  have hfetch : (AccessType.Write Data != AccessType.InstructionFetch ()) = true := rfl
  simp [vmem_write, vmem_write_addr, SailME.run, h_reg_val, h_aligned]
  simp [untilFuelM, untilFuelM.go]
  simp [translateAddr, translationMode, effectivePrivilege]
  simp [run_readReg_of_isInitialized s _ hs, Std.ExtDHashMap.get?_eq_some_get (hs _)]
  simp [privLevel_bits_backwards]
  simp [h_mprv_disabled, h_cur_privilege, hmachine, hsatp_bare]
  simp [mem_write_ea, write_kind_of_flags, mem_write_value, mem_write_value_meta]
  simp [run_readReg_of_isInitialized s _ hs, Std.ExtDHashMap.get?_eq_some_get (hs _)]
  simp [effectivePrivilege, hfetch, h_mprv_disabled]
  simp [mem_write_value_priv_meta, checked_mem_write, h_cur_privilege, phys_access_check, SailME.run]
  simp [LeanRV64D.Functions.sys_pmp_count, pmp_check_machine reg_val offset s hs]
  simp [run_within_mmio_writable_mmio reg_val offset 1 (by omega) s hs h_clint_base h_clint_size]
  simp [zero_extend, BitVec.addInt, Sail.BitVec.zeroExtend]
  simp [run_within_phys_mem reg_val offset 1 s hs h_plat_ram_base h_plat_rom_base h_does_fit]
  simp [write_kind_of_flags, phys_mem_write, LeanRV64D.Functions.write_ram,
    sail_mem_write, PreSail.sail_mem_write, PreSail.writeBytes,
    PreSail.writeByte, Except.map, BitVec.addInt]

set_option debug.skipKernelTC true in
theorem correct (Main : Vector (Fin KB) 52)
    (s : SailState) (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (StoreByte.constraints Main).allHold)
    (state_cstrs : (StoreByte.constraints Main).initialState s)
    (h_is_real : Main[50] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (sp1_imm_c Main)).toNat
      let ram_size := (s.regs.get Register.plat_ram_size (hs _)).toNat
      reg_val + offset + 1 ≤ ram_size) :
    let op_a := sp1_op_a Main
    let op_b := sp1_ob_b Main
    let imm_c := sp1_imm_c Main
    (spec_sb imm_c (.Regidx op_a) (.Regidx op_b)).run s = (sp1_sb Main).run s := by
  extract_lets op_a op_b imm_c

  -- Extract the facts about the config registers in the state
  obtain ⟨h_mprv_disabled, h_cur_privilege, h_clint_base, h_clint_size,
    h_plat_ram_base, h_plat_rom_base⟩ := hs_config

  -- Extract the main constraints from the chip
  rw [StoreByte.constraints] at h_cstrs
  simp [SP1ConstraintList.allHold] at h_cstrs
  simp [AddressOperation.constraints, sub_eq_zero, h_is_real] at h_cstrs
  obtain ⟨h_add_addr, h49, h38, h39, h40, h49, h_cpu, h_reader, h_cstrs⟩ := h_cstrs

  -- Extract constraints about the state of operations
  simp [StoreByte.constraints, AddressOperation.constraints,
    SP1Constraint.toStateProp, AddrAddOperation.constraints,
    CPUState.constraints, ITypeReaderImmutable.constraints,
    Opcode.ofNat, Nat.ble, h_is_real] at state_cstrs
  obtain ⟨h_read_pc, h6_op_a, h14_op_a, h_imm_state⟩ := state_cstrs
  rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_read_pc

  -- Extract constraints about the reader
  simp [ITypeReaderImmutable.constraints,
      SP1Constraint.toProp, Opcode.ofNat, Nat.ble] at h_reader
  have h25 : Main[25] = 1 := by simp_all only [sub_eq_zero]
  simp [h25] at *
  have h_imm_c : Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] =
      BitVec.signExtend 64 (BitVec.ofNat 12 Main[21]) := by clear *- h_reader; simp_all only
  have h6_32 : Main[6] < 32 := by clear *- h_reader; simp_all only
  have h14_32 : Main[14] < 32 := by clear *- h_reader; simp_all only
  specialize h6_op_a h6_32
  specialize h14_op_a h14_32
  have h15u64 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := by
    clear *- h_reader; simp_all only
  have h21u64 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := by
    clear *- h_reader; apply Word.isU64_of_cases <;> (simp; omega)

  -- Extract constraints about the addr add
  have haddr_add := AddrAddOperation.spec_of_constraints _ _ h15u64 h21u64 _ h_add_addr

  -- Simplify the monadic computation
  simp [spec_sb]
  simp [run_readReg_of_isInitialized s _ hs]
  simp [h_read_pc]
  simp [execute_STORE]
  simp only [BitVec.ofNatLT_eq_ofNat] at h6_op_a h14_op_a
  simp [op_a, sp1_op_a, h6_op_a]
  simp [op_b, sp1_ob_b, h14_op_a]
  simp [AddrAddOperation.spec] at haddr_add
  simp [sp1_sb, haddr_add.2]

  -- Apply the main helper lemma
  rw [run_vmem_write_of_width_1' (BitVec.ofNat 5 Main[14])
    (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]])
    (BitVec.signExtend 64 imm_c)
    (Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]])]

  -- Arithmetic Caclulations
  · simp [sp1_sb, h_imm_c, imm_c, Sail.write_ram, PreSail.write_ram,
      PreSail.writeBytes, PreSail.writeByte]
    constructor
    · simp [Word.toBitVec64, Word.toNat, Fin.val_add]
      refine congr_arg (BitVec.ofNat 64) ?_
      simp [BitVec.toNat_ofNat]
      omega
    · apply congr_arg₂ s.mem.insert
      · simp [Word.toBitVec64, Word.toNat, sp1_imm_c,
          BitVec.ofNat_add]
        congr 4
        simp [BitVec.toNat_eq]
        omega
      · simp [BitVec.toNat_eq]

  -- Other hypothesis for the lemma
  · simp [SailState.isInitialized, hs]
  · simpa using h14_op_a
  · simp [is_aligned_vaddr]
  · constructor <;> simpa [Std.ExtDHashMap.get_insert]
  · simpa [Std.ExtDHashMap.get_insert]

end StoreByte

end Store
