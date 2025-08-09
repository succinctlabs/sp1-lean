import SP1Foundations
import SP1Chips.Load.LoadWord.Constraints
import SP1Operations.Operation.AddrAddOperation
import LeanRV64IM.Specialization
import LeanRV64IM.RiscvMem
import LeanRV64IM.RiscvInstsEnd

instance : Lean.Grind.NoNatZeroDivisors (Fin BB) where
  no_nat_zero_divisors := sorry

open LeanRV64IM.Functions

lemma Sail.run_writeReg_no_run (reg : Register) (v : RegisterType reg) :
    (Sail.writeReg reg v) s =
      .ok PUnit.unit { s with regs := s.regs.insert reg v} := rfl

namespace Sail

lemma run_write_reg_no_run (idx : BitVec 5) (val : BitVec 64) :
    (write_reg idx val) =
      let reg : Register := reg_idx_to_Register idx
      if idx = 0#5 then if val = 0#64 then pure () else throw Sail.Error.Unreachable
        else Sail.writeReg reg (bitVecToRegidxVal idx val) := by
  unfold write_reg; aesop

end Sail

namespace BitVec

set_option maxHeartbeats 4000000 in
theorem u64_limbs_add_is_append {x y z a : ℕ}
  (hx : x < 65536)
  (hy : y < 65536)
  (hz : z < 65536)
  (ha : a < 65536)
  : BitVec.ofNat 64 (x + y <<< 16 + z <<< 32 + a <<< 48)
  = (BitVec.ofNatLT (w := 16) a ha)
    ++ (BitVec.ofNatLT (w := 16) z hz)
    ++ (BitVec.ofNatLT (w := 16) y hy)
    ++ (BitVec.ofNatLT (w := 16) x hx)
  := by
    -- rw [←BitVec.ofNatLT_eq_ofNat (by simp [Nat.shiftLeft_eq]; omega)]
    -- rw [BitVec.append_def]
    -- rw [BitVec.append_def]
    -- rw [BitVec.append_def]
    -- simp [BitVec.shiftLeftZeroExtend]
    -- unfold BitVec.setWidth
    -- simp only [Nat.reduceLeDiff, ↓reduceDIte]
    -- unfold BitVec.setWidth'
    sorry

end BitVec

attribute [simp] bind StateT.bind ExceptT.bind EStateM.bind ExceptT.bindCont get getThe MonadStateOf.get StateT.get EStateM.get pure StateT.pure ExceptT.pure EStateM.pure Functor.map StateT.map ExceptT.map EStateM.map modify modifyGet EStateM.modifyGet StateT.modifyGet MonadStateOf.modifyGet liftM monadLift MonadLift.monadLift ExceptT.lift StateT.lift ExceptT.mk StateT.run ExceptT.run EStateM.run Sail.SailME.run

-- attribute [-simp] Sail.wX_bits_eq_writeReg

attribute [grind] BitVec.toNat_ofNatLT

namespace Load

namespace LoadWord

namespace LW

open BitVec

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
    Sail.write_reg op_a (Word.toBitVec64 #v[Main[39], Main[40], Main[41] * 65535, Main[41] * 65535])
    pure RETIRE_SUCCESS

-- set_option debug.skipKernelTC true in
set_option maxHeartbeats 4000000 in
set_option pp.proofs false in
set_option diagnostics false in
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

    simp [-Word.add_toBitVec64_mod4, constraints, AddressOperation.constraints, AddrAddOperation.constraints, U16MSBOperation.constraints, CPUState.constraints, ITypeReader.constraints, SP1Constraint.toStateProp, List.Forall, h_is_lw, h_not_lwu, Opcode.ofNat, ByteOpcode.ofNat, Nat.beq, Nat.ble] at state_cstrs
    obtain ⟨h_read_pc, ⟨h_trusted_read, h_read_addr_within_range⟩, h_read_op_a, h_read_op_b, h_read_mem⟩ := state_cstrs

    simp [constraints, AddressOperation.constraints, SP1Constraint.toProp, List.Forall, h_is_lw, h_not_lwu, Opcode.ofNat, ByteOpcode.ofNat, Nat.beq, Nat.ble, sub_eq_zero] at cstrs
    obtain ⟨addr_add_cstrs, addr_cstr0, addr_cstr1, addr_cstr2, msb_cstrs, cpu_cstrs, reader_cstrs, chip_cstrs⟩ := cstrs

    simp [ITypeReader.constraints, SP1Constraint.toProp, List.Forall, Opcode.ofNat, ByteOpcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs
    stop
    have h_op_a_is_reg : Main[6] < 32 := by simp_all only
    simp [h_op_a_is_reg] at h_read_op_a
    have h_op_b_is_reg : Main[14] < 32 := by simp_all only
    simp [h_op_b_is_reg] at h_read_op_b
    -- simp [-Word.add_toBitVec64_mod4, ←BitVec.ofNatLT_eq_ofNat (w := 5) (n := Main[14].val) h_op_b_is_reg, h_read_op_b] at h_trusted_read
    rw [←BitVec.ofNatLT_eq_ofNat (w := 5) (n := Main[14].val) h_op_b_is_reg, h_read_op_b, Option.get!_some] at h_trusted_read
    rw [←BitVec.ofNatLT_eq_ofNat h_op_b_is_reg, h_read_op_b, Option.get!_some] at h_read_addr_within_range

    have h_mem_read_is_u64 : Word.isU64 #v[Main[29], Main[30], Main[31], Main[32]] := by simp_all only [chip_cstrs]

    have h_over_addr : Main[26] ≠ 0 ∨ Main[27] ≠ 0 :=
      by
        by_contra!
        clear * - addr_cstr1 this
        obtain ⟨h_limb1_0, h_limb2_0⟩ := this
        simp [h_limb1_0, h_limb2_0] at addr_cstr1
    simp [not_and_or.mpr h_over_addr] at h_read_mem
    obtain ⟨h_read_limb0, h_read_limb1, h_read_limb2, h_read_limb3⟩ := h_read_mem

    have h_op_c_is_signExtend : Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] = BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) := by
      simp [constraints, AddressOperation.constraints, AddrAddOperation.constraints, CPUState.constraints, ITypeReader.constraints, SP1Constraint.toProp, List.Forall, h_is_lw, h_not_lwu, Opcode.ofNat, ByteOpcode.ofNat, Nat.beq, Nat.ble] at cstrs
      simp_all only

    have h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64 op_c)) 4 = true := by
      unfold is_aligned_vaddr
      simp only [op_b, op_c, sp1_op_b, sp1_imm, sign_extend, Sail.BitVec.signExtend]
      rw [h_op_c_is_signExtend] at h_trusted_read
      clear * - h_trusted_read
      have := congrArg BitVec.toNat h_trusted_read
      simp [-Word.toBitVec64_add_mod4, BitVec.toNat_umod, BitVec.ofNat_toNat] at this
      simp only [beq_iff_eq]
      rw [←Int.ofNat_tmod]
      -- praise Confucius this works
      bv_omega

    have h_op_a_not_x0 : op_a ≠ 0#5 := by
      simp [op_a, sp1_op_a, BitVec.ofNatLT, BitVec.ofNat]
      have h_imm_c_is_0 : Main[13] = 0 := by simp_all only [chip_cstrs]
      have h_imm_c_iff_op_a_x0 : Main[13] = 1 ↔ Main[6] = 0 := by
        simp_all only [reader_cstrs]
      rw [Fin.mk_eq_mk]
      simp
      clear * - h_imm_c_is_0 h_imm_c_iff_op_a_x0
      aesop

    simp [op_a, sp1_op_a] at h_op_a_not_x0
    have h_pc0 : Main[3].val < 65536 := by clear * - reader_cstrs; show Main[3] < 65536; simp_all only
    have h_pc1 : Main[4].val < 65536 := by clear * - reader_cstrs; show Main[4] < 65536; simp_all only
    have h_pc2 : Main[5].val < 65536 := by clear * - reader_cstrs; show Main[5] < 65536; simp_all only
    have h_pc_is_u64 : Main[3].val + Main[4].val <<< 16 + Main[5].val <<< 32 < 2^64 := by
      simp
      clear * - h_pc0 h_pc1 h_pc2
      omega

    obtain ⟨h_add_addr_limb0, h_add_addr_limb1, h_add_addr_limb2, h_addr_add_spec⟩ :=
      AddrAddOperation.correct
      _ _ _ _ (by simp)
      addr_add_cstrs
      (by simp_all only [reader_cstrs])
      (Word.isU64_of_cases _
        (by clear * - reader_cstrs; simp; show Main[21] < 65536; simp_all only [reader_cstrs])
        (by clear * - reader_cstrs; simp; show Main[22] < 65536; simp_all only [reader_cstrs])
        (by clear * - reader_cstrs; simp; show Main[23] < 65536; simp_all only [reader_cstrs])
        (by clear * - reader_cstrs; simp; show Main[24] < 65536; simp_all only [reader_cstrs])
        )
    simp at h_add_addr_limb0 h_add_addr_limb1 h_add_addr_limb2 h_addr_add_spec

    cases addr_cstr0
    · rename_i h_no_shift
      simp [h_no_shift] at chip_cstrs h_read_limb0 h_read_limb1 h_read_limb2 h_read_limb3 addr_cstr2

      obtain ⟨h_limb0_mem0, h_limb0_mem1⟩ := h_read_limb0
      obtain ⟨h_limb1_mem2, h_limb1_mem3⟩ := h_read_limb1

      have h_read_mem0 : s.mem[(Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + signExtend 64 op_c).toNat]? = some (BitVec.truncate 8 (BitVec.ofNat 16 ↑Main[29])) := by
        simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
        rw [←h_op_c_is_signExtend, ←h_addr_add_spec]
        clear * - h_limb0_mem0 h_add_addr_limb0 h_add_addr_limb1 h_add_addr_limb2
        simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
        rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
        simp [BitVec.ofNatLT_toNat]
        simp [Word.toNat] at h_limb0_mem0
        grind

      have h_read_mem1 : s.mem[(Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + signExtend 64 op_c).toNat + 1]? = some (BitVec.truncate 8 ((BitVec.ofNat 16 ↑Main[29]) >>> 8)) := by
        simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
        rw [←h_op_c_is_signExtend, ←h_addr_add_spec]
        clear * - h_limb0_mem1 h_add_addr_limb0 h_add_addr_limb1 h_add_addr_limb2
        simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
        rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
        simp [BitVec.ofNatLT_toNat]
        simp [Word.toNat] at h_limb0_mem1
        grind

      have h_read_mem2 : s.mem[(Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + signExtend 64 op_c).toNat + 2]? = some (BitVec.truncate 8 (BitVec.ofNat 16 ↑Main[30])) := by
        simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
        rw [←h_op_c_is_signExtend, ←h_addr_add_spec]
        clear * - h_limb1_mem2 h_add_addr_limb0 h_add_addr_limb1 h_add_addr_limb2
        simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
        rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
        simp [BitVec.ofNatLT_toNat]
        simp [Word.toNat] at h_limb1_mem2
        grind

      have h_read_mem3 : s.mem[(Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + signExtend 64 op_c).toNat + 3]? = some (BitVec.truncate 8 ((BitVec.ofNat 16 ↑Main[30]) >>> 8)) := by
        simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
        rw [←h_op_c_is_signExtend, ←h_addr_add_spec]
        clear * - h_limb1_mem3 h_add_addr_limb0 h_add_addr_limb1 h_add_addr_limb2
        simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
        rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
        simp [BitVec.ofNatLT_toNat]
        simp [Word.toNat] at h_limb1_mem3
        grind

      have h_limb0_is_u16 : Main[29].val < 2^16 := h_mem_read_is_u64 0
      have h_limb1_is_u16 : Main[30].val < 2^16 := h_mem_read_is_u64 1
      simp only [←BitVec.ofNatLT_eq_ofNat h_limb0_is_u16, ←BitVec.ofNatLT_eq_ofNat h_limb1_is_u16] at h_read_mem0 h_read_mem1 h_read_mem2 h_read_mem3

      simp [-BitVec.toNat_add, spec_lw, execute_LOAD, Sail.readReg, PreSail.readReg, h_read_pc, Sail.assert, PreSail.assert,
           LeanRV64IM.Functions.xlen_bytes, vmem_read, ext_data_get_addr, op_b, sp1_op_b, Sail.writeReg,
           PreSail.writeReg, Sail.rX_bits_eq_get_reg?_no_run, h_read_op_b, Option.elim, Option.toSailM,
           check_misaligned, LeanRV64IM.Functions.plat_enable_misaligned_access, LeanRV64IM.Functions.not,
           h_is_aligned, split_misaligned, bits_of_virtaddr, untilFuelM, untilFuelM.go, Sail.assert, PreSail.assert,
           translateAddr, Std.ExtDHashMap.get?_insert, h_mstatus, h_priv, effectivePrivilege, _get_Mstatus_MPRV,
           Sail.BitVec.extractLsb, translationMode, mem_read, Sail.readReg, PreSail.readReg, Sail.BitVec.extractLsb,
           translationMode, mem_read_priv, mem_read_priv_meta, checked_mem_read, phys_access_check, bits_of_virtaddr,
           LeanRV64IM.Functions.sys_pmp_count, within_mmio_readable, get_config_rvfi, Sail.BitVec.addInt, zero_extend,
           Sail.BitVec.zeroExtend, within_phys_mem, ext_check_phys_mem_read, phys_mem_read, read_kind_of_flags,
           read_ram, Sail.sail_mem_read, PreSail.sail_mem_read, PreSail.readBytes, PreSail.readByte, h_read_mem0,
           h_read_mem1, h_read_mem2, h_read_mem3, MemoryOpResult_drop_meta, h_op_a_not_x0, misaligned_order,
           sys_misaligned_order_decreasing, extend_value, sign_extend, Sail.BitVec.signExtend, sp1_lw, op_a, sp1_op_a,
           Sail.run_write_reg_no_run, h_op_a_not_x0]

      have h_correct_limb0 : Main[39] = Main[29] := by simp_all only [chip_cstrs]
      have h_correct_limb1 : Main[40] = Main[30] := by simp_all only [chip_cstrs]
      rw [h_correct_limb0, h_correct_limb1]

      -- nextPC write
      simp [Word.toBitVec64, Word.toNat]
      rw [←BitVec.ofNatLT_eq_ofNat h_pc_is_u64]
      simp [BitVec.add_def]
      have : (↑(Main[3] + 4) + ↑Main[4] <<< 16 + ↑Main[5] <<< 32 : ℕ) = ↑Main[3] + ↑Main[4] <<< 16 + ↑Main[5] <<< 32 + 4 := by
        simp [Fin.add_def]
        rw [Nat.mod_eq_of_lt (by clear * - h_pc0; linarith)]
        ring_nf
      rw [this]
      clear this
      simp [op_a]

      apply congrArg
      apply congrArg

      -- op_a/rd write
      simp [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', default]
      sorry

    · rename_i h_shift
      simp [h_shift] at chip_cstrs h_read_limb0 h_read_limb1 h_read_limb2 h_read_limb3 addr_cstr2

      let h_addr_limb0_ge4 : Main[25] >= 4 :=
        by
          clear * - addr_cstr2
          by_contra!
          convert_to Main[25].val < 4 at this
          simp [Fin.lt_def, Fin.mul_def, Fin.sub_def] at addr_cstr2
          interval_cases Main[25].val
          <;> simp at addr_cstr2

      obtain ⟨h_limb2_mem0, h_limb2_mem1⟩ := h_read_limb2
      obtain ⟨h_limb3_mem2, h_limb3_mem3⟩ := h_read_limb3

      have h_read_mem0 : s.mem[(Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + signExtend 64 op_c).toNat]? = some (BitVec.truncate 8 (BitVec.ofNat 16 ↑Main[31])) := by
        simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
        rw [←h_op_c_is_signExtend, ←h_addr_add_spec]
        clear * - h_limb2_mem0 h_add_addr_limb0 h_add_addr_limb1 h_add_addr_limb2 h_addr_limb0_ge4
        simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
        rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
        simp [BitVec.ofNatLT_toNat]
        simp [Word.toNat] at h_limb2_mem0
        simp [Fin.sub_val_of_le h_addr_limb0_ge4] at h_limb2_mem0
        clear * - h_limb2_mem0 h_addr_limb0_ge4
        convert_to Main[25].val ≥ 4 at h_addr_limb0_ge4
        grind

      have h_read_mem1 : s.mem[(Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + signExtend 64 op_c).toNat + 1]? = some (BitVec.truncate 8 ((BitVec.ofNat 16 ↑Main[31]) >>> 8)) := by
        simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
        rw [←h_op_c_is_signExtend]
        rw [←h_addr_add_spec]
        clear * - h_limb2_mem1 h_add_addr_limb0 h_add_addr_limb1 h_add_addr_limb2 h_addr_limb0_ge4
        simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
        rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
        simp [BitVec.ofNatLT_toNat]
        simp [Word.toNat] at h_limb2_mem1
        simp [Fin.sub_val_of_le h_addr_limb0_ge4] at h_limb2_mem1
        convert_to Main[25].val ≥ 4 at h_addr_limb0_ge4
        grind

      have h_read_mem2 : s.mem[(Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + signExtend 64 op_c).toNat + 2]? = some (BitVec.truncate 8 ((BitVec.ofNat 16 ↑Main[32]))) := by
        simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
        rw [←h_op_c_is_signExtend]
        rw [←h_addr_add_spec]
        clear * - h_limb3_mem2 h_add_addr_limb0 h_add_addr_limb1 h_add_addr_limb2 h_addr_limb0_ge4
        simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
        rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
        simp [BitVec.ofNatLT_toNat]
        simp [Word.toNat] at h_limb3_mem2
        simp [Fin.sub_val_of_le h_addr_limb0_ge4] at h_limb3_mem2
        convert_to Main[25].val ≥ 4 at h_addr_limb0_ge4
        grind

      have h_read_mem3 : s.mem[(Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + signExtend 64 op_c).toNat + 3]? = some (BitVec.truncate 8 (((BitVec.ofNat 16 ↑Main[32])) >>> 8)) := by
        simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
        simp [Word.toNat] at h_limb3_mem3
        simp [Fin.sub_val_of_le h_addr_limb0_ge4] at h_limb3_mem3
        convert_to Main[25].val ≥ 4 at h_addr_limb0_ge4
        rw [←h_op_c_is_signExtend]
        rw [←h_addr_add_spec]
        clear * - h_limb3_mem3 h_add_addr_limb0 h_add_addr_limb1 h_add_addr_limb2 h_addr_limb0_ge4
        simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
        rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
        simp [BitVec.toNat_ofNatLT]
        grind

      have h_limb2_is_u16 : Main[31].val < 2^16 := h_mem_read_is_u64 2
      have h_limb3_is_u16 : Main[32].val < 2^16 := h_mem_read_is_u64 3
      simp only [←BitVec.ofNatLT_eq_ofNat h_limb2_is_u16, ←BitVec.ofNatLT_eq_ofNat h_limb3_is_u16] at h_read_mem0 h_read_mem1 h_read_mem2 h_read_mem3

      simp [-BitVec.toNat_add, spec_lw, execute_LOAD, Sail.readReg, PreSail.readReg, h_read_pc, Sail.assert, PreSail.assert,
           LeanRV64IM.Functions.xlen_bytes, vmem_read, ext_data_get_addr, op_b, sp1_op_b, Sail.writeReg,
           PreSail.writeReg, Sail.rX_bits_eq_get_reg?_no_run, h_read_op_b, Option.elim, Option.toSailM,
           check_misaligned, LeanRV64IM.Functions.plat_enable_misaligned_access, LeanRV64IM.Functions.not,
           h_is_aligned, split_misaligned, bits_of_virtaddr, untilFuelM, untilFuelM.go, Sail.assert, PreSail.assert,
           translateAddr, Std.ExtDHashMap.get?_insert, h_mstatus, h_priv, effectivePrivilege, _get_Mstatus_MPRV,
           Sail.BitVec.extractLsb, translationMode, mem_read, Sail.readReg, PreSail.readReg, Sail.BitVec.extractLsb,
           translationMode, mem_read_priv, mem_read_priv_meta, checked_mem_read, phys_access_check, bits_of_virtaddr,
           LeanRV64IM.Functions.sys_pmp_count, within_mmio_readable, get_config_rvfi, Sail.BitVec.addInt, zero_extend,
           Sail.BitVec.zeroExtend, within_phys_mem, ext_check_phys_mem_read, phys_mem_read, read_kind_of_flags,
           read_ram, Sail.sail_mem_read, PreSail.sail_mem_read, PreSail.readBytes, PreSail.readByte, h_read_mem0,
           h_read_mem1, h_read_mem2, h_read_mem3, MemoryOpResult_drop_meta, h_op_a_not_x0, misaligned_order,
           sys_misaligned_order_decreasing, extend_value, sign_extend, Sail.BitVec.signExtend, sp1_lw, op_a, sp1_op_a,
           Sail.run_write_reg_no_run, h_op_a_not_x0]

      have h_correct_limb0 : Main[39] = Main[31] := by simp_all only [chip_cstrs]
      have h_correct_limb1 : Main[40] = Main[32] := by simp_all only [chip_cstrs]
      rw [h_correct_limb0, h_correct_limb1]

      -- nextPC write
      simp [Word.toBitVec64, Word.toNat]
      rw [←BitVec.ofNatLT_eq_ofNat h_pc_is_u64]
      simp [BitVec.add_def]
      have : (↑(Main[3] + 4) + ↑Main[4] <<< 16 + ↑Main[5] <<< 32 : ℕ) = ↑Main[3] + ↑Main[4] <<< 16 + ↑Main[5] <<< 32 + 4 := by
        simp [Fin.add_def]
        rw [Nat.mod_eq_of_lt (by clear * - h_pc0; linarith)]
        ring_nf
      rw [this]
      clear this
      simp [op_a]

      apply congrArg
      apply congrArg

      -- op_a/rd write
      simp [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', default]
      sorry

lemma helper2
  {x : Fin BB}
  (hx : x < 65536)
  (hmul : (x * 1761607681).val < 8192)
  : x % 8 = 0
  := by
    convert_to x.val < 65536 at hx
    simp [Fin.mod_def]
    simp [Fin.mul_def, Fin.lt_def] at hmul

    -- Use the Division Algorithm: x.val = 8 * q + r where 0 ≤ r < 8
    set q := x.val / 8
    set r := x.val % 8
    have hx_eq : x.val = 8 * q + r := by
      conv_lhs => rw [← Nat.div_add_mod x.val 8]
    have hr_lt : r < 8 := Nat.mod_lt x.val (by norm_num : 0 < 8)

    -- Key fact: 8 * 1761607681 ≡ 1 (mod BB)
    have h_inv : (8 * 1761607681) % BB = 1 := by norm_num

    have :=
      calc ↑x * 1761607681 % BB = (8 * q + r) * 1761607681 % BB := by rw [hx_eq]
                              _ = (8 * q * 1761607681 + r * 1761607681) % BB := by ring_nf
                              _ = (8 * q * 1761607681 % BB + r * 1761607681) % BB := by simp
                              _ = ((8 * 1761607681) * q % BB + r * 1761607681) % BB := by ring_nf
                              _ = ((8 * 1761607681) % BB * q % BB + r * 1761607681) % BB := by rw [Nat.mod_mul_mod]
                              _ = (1 * q % BB + r * 1761607681) % BB := by simp
                              _ = (q % BB + r * 1761607681) % BB := by simp
                              _ = (q + r * 1761607681) % BB := by simp
    simp at this
    rw [this] at hmul
    clear this h_inv

    -- Case on the 8 possible values of r
    interval_cases r
    -- Case r = 0
    · rfl
    -- Case 1 ≤ r < 8
    all_goals
      simp at hmul
      omega

end LW


namespace LWU

open BitVec

variable
  (Main : Vector (Fin BB) 44)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_lwu : Main[43] = 1)

private theorem is_lwu_eq_not_lw
  (cstrs : (constraints Main).allHold)
  (h_is_lwu : Main[43] = 1)
  -- (h_is_real : Main[28] + Main[29] + Main[30] + Main[31] + Main[32] + Main[33] = 1)
  : Main[42] = 0 := by
  simp [constraints, SP1ConstraintList.allHold, List.Forall, AddressOperation.constraints, h_is_lwu, sub_eq_zero] at cstrs
  have h_is_lw_is_bool : Main[42] = 0 ∨ Main[42] = 1 := by simp_all only
  cases h_is_lw_is_bool
  · assumption
  rename_i h_is_lwu
  simp [h_is_lwu] at cstrs

def spec_lwu (imm : BitVec 12) (rs2 rs1 : regidx) : SailM ExecutionResult :=
  do
    Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
    execute_LOAD imm rs2 rs1 true 4

def sp1_op_a : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[6] ?_
    show Main[6] < 32

    have h_not_lw : Main[42] = 0 := is_lwu_eq_not_lw Main cstrs h_is_lwu
    simp [constraints, AddressOperation.constraints, AddrAddOperation.constraints, CPUState.constraints, ITypeReader.constraints, SP1Constraint.toProp, List.Forall, h_is_lwu, h_not_lw] at cstrs
    simp_all only

def sp1_op_b : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[14] ?_
    show Main[14] < 32

    have h_not_lw : Main[42] = 0 := is_lwu_eq_not_lw Main cstrs h_is_lwu
    simp [constraints, AddressOperation.constraints, AddrAddOperation.constraints, CPUState.constraints, ITypeReader.constraints, SP1Constraint.toProp, List.Forall, h_is_lwu, h_not_lw, Opcode.ofNat, Nat.ble, Nat.beq] at cstrs
    simp_all only

def sp1_imm : BitVec 12 := BitVec.ofNat 12 Main[21].val

def sp1_lwu : SailM ExecutionResult :=
  do
    let op_a := sp1_op_a Main cstrs h_is_lwu
    Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
    Sail.write_reg op_a (Word.toBitVec64 #v[Main[39], Main[40], Main[41] * 65535, Main[41] * 65535])
    pure RETIRE_SUCCESS

-- set_option debug.skipKernelTC true in
set_option maxHeartbeats 4000000 in
set_option pp.proofs false in
set_option diagnostics false in
theorem correct
  (Main : Vector (Fin BB) 44)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (state_cstrs : (constraints Main).initialState s)
  (h_is_lwu : Main[43] = 1)
  (h_mstatus : s.regs.get? Register.mstatus = some 0)
  (h_priv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
  (mem0 mem1 mem2 mem3 : BitVec 8)
  -- assumptions!
  : let op_a := sp1_op_a Main cstrs h_is_lwu
    let op_b := sp1_op_b Main cstrs h_is_lwu
    let op_c := sp1_imm Main
    (spec_lwu op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_lwu Main cstrs h_is_lwu).run s
  := by
    extract_lets op_a op_b op_c
    have h_not_lw : Main[42] = 0 := is_lwu_eq_not_lw Main cstrs h_is_lwu

    simp [-Word.add_toBitVec64_mod4, constraints, AddressOperation.constraints, AddrAddOperation.constraints, U16MSBOperation.constraints, CPUState.constraints, ITypeReader.constraints, SP1Constraint.toStateProp, List.Forall, h_is_lwu, h_not_lw, Opcode.ofNat, ByteOpcode.ofNat, Nat.beq, Nat.ble] at state_cstrs
    obtain ⟨h_read_pc, ⟨h_trusted_read, h_read_addr_within_range⟩, h_read_op_a, h_read_op_b, h_read_mem⟩ := state_cstrs

    simp [constraints, AddressOperation.constraints, SP1Constraint.toProp, List.Forall, h_is_lwu, h_not_lw, Opcode.ofNat, ByteOpcode.ofNat, Nat.beq, Nat.ble, sub_eq_zero] at cstrs
    obtain ⟨addr_add_cstrs, addr_cstr0, addr_cstr1, addr_cstr2, msb_cstrs, cpu_cstrs, reader_cstrs, chip_cstrs⟩ := cstrs

    simp [ITypeReader.constraints, SP1Constraint.toProp, List.Forall, Opcode.ofNat, ByteOpcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs
    stop
    have h_op_a_is_reg : Main[6] < 32 := by simp_all only
    simp [h_op_a_is_reg] at h_read_op_a
    have h_op_b_is_reg : Main[14] < 32 := by simp_all only
    simp [h_op_b_is_reg] at h_read_op_b
    -- simp [-Word.add_toBitVec64_mod4, ←BitVec.ofNatLT_eq_ofNat (w := 5) (n := Main[14].val) h_op_b_is_reg, h_read_op_b] at h_trusted_read
    rw [←BitVec.ofNatLT_eq_ofNat (w := 5) (n := Main[14].val) h_op_b_is_reg, h_read_op_b, Option.get!_some] at h_trusted_read
    rw [←BitVec.ofNatLT_eq_ofNat h_op_b_is_reg, h_read_op_b, Option.get!_some] at h_read_addr_within_range

    have h_mem_read_is_u64 : Word.isU64 #v[Main[29], Main[30], Main[31], Main[32]] := by simp_all only [chip_cstrs]

    have h_over_addr : Main[26] ≠ 0 ∨ Main[27] ≠ 0 :=
      by
        by_contra!
        clear * - addr_cstr1 this
        obtain ⟨h_limb1_0, h_limb2_0⟩ := this
        simp [h_limb1_0, h_limb2_0] at addr_cstr1
    simp [not_and_or.mpr h_over_addr] at h_read_mem
    obtain ⟨h_read_limb0, h_read_limb1, h_read_limb2, h_read_limb3⟩ := h_read_mem

    have h_op_c_is_signExtend : Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] = BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) := by
      simp [constraints, AddressOperation.constraints, AddrAddOperation.constraints, CPUState.constraints, ITypeReader.constraints, SP1Constraint.toProp, List.Forall, h_is_lwu, h_not_lw, Opcode.ofNat, ByteOpcode.ofNat, Nat.beq, Nat.ble] at cstrs
      simp_all only

    have h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64 op_c)) 4 = true := by
      unfold is_aligned_vaddr
      simp only [op_b, op_c, sp1_op_b, sp1_imm, sign_extend, Sail.BitVec.signExtend]
      rw [h_op_c_is_signExtend] at h_trusted_read
      clear * - h_trusted_read
      have := congrArg BitVec.toNat h_trusted_read
      simp [-Word.toBitVec64_add_mod4, BitVec.toNat_umod, BitVec.ofNat_toNat] at this
      simp only [beq_iff_eq]
      rw [←Int.ofNat_tmod]
      -- praise Confucius this works
      bv_omega

    have h_op_a_not_x0 : op_a ≠ 0#5 := by
      simp [op_a, sp1_op_a, BitVec.ofNatLT, BitVec.ofNat]
      have h_imm_c_is_0 : Main[13] = 0 := by simp_all only [chip_cstrs]
      have h_imm_c_iff_op_a_x0 : Main[13] = 1 ↔ Main[6] = 0 := by
        simp_all only [reader_cstrs]
      rw [Fin.mk_eq_mk]
      simp
      clear * - h_imm_c_is_0 h_imm_c_iff_op_a_x0
      aesop

    simp [op_a, sp1_op_a] at h_op_a_not_x0
    have h_pc0 : Main[3].val < 65536 := by clear * - reader_cstrs; show Main[3] < 65536; simp_all only
    have h_pc1 : Main[4].val < 65536 := by clear * - reader_cstrs; show Main[4] < 65536; simp_all only
    have h_pc2 : Main[5].val < 65536 := by clear * - reader_cstrs; show Main[5] < 65536; simp_all only
    have h_pc_is_u64 : Main[3].val + Main[4].val <<< 16 + Main[5].val <<< 32 < 2^64 := by
      simp
      clear * - h_pc0 h_pc1 h_pc2
      omega

    obtain ⟨h_add_addr_limb0, h_add_addr_limb1, h_add_addr_limb2, h_addr_add_spec⟩ :=
      AddrAddOperation.correct
      _ _ _ _ (by simp)
      addr_add_cstrs
      (by simp_all only [reader_cstrs])
      (Word.isU64_of_cases _
        (by clear * - reader_cstrs; simp; show Main[21] < 65536; simp_all only [reader_cstrs])
        (by clear * - reader_cstrs; simp; show Main[22] < 65536; simp_all only [reader_cstrs])
        (by clear * - reader_cstrs; simp; show Main[23] < 65536; simp_all only [reader_cstrs])
        (by clear * - reader_cstrs; simp; show Main[24] < 65536; simp_all only [reader_cstrs])
        )
    simp at h_add_addr_limb0 h_add_addr_limb1 h_add_addr_limb2 h_addr_add_spec

    cases addr_cstr0
    · rename_i h_no_shift
      simp [h_no_shift] at chip_cstrs h_read_limb0 h_read_limb1 h_read_limb2 h_read_limb3 addr_cstr2

      obtain ⟨h_limb0_mem0, h_limb0_mem1⟩ := h_read_limb0
      obtain ⟨h_limb1_mem2, h_limb1_mem3⟩ := h_read_limb1

      have h_read_mem0 : s.mem[(Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + signExtend 64 op_c).toNat]? = some (BitVec.truncate 8 (BitVec.ofNat 16 ↑Main[29])) := by
        simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
        rw [←h_op_c_is_signExtend, ←h_addr_add_spec]
        clear * - h_limb0_mem0 h_add_addr_limb0 h_add_addr_limb1 h_add_addr_limb2
        simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
        rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
        simp [BitVec.ofNatLT_toNat]
        simp [Word.toNat] at h_limb0_mem0
        grind

      have h_read_mem1 : s.mem[(Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + signExtend 64 op_c).toNat + 1]? = some (BitVec.truncate 8 ((BitVec.ofNat 16 ↑Main[29]) >>> 8)) := by
        simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
        rw [←h_op_c_is_signExtend, ←h_addr_add_spec]
        clear * - h_limb0_mem1 h_add_addr_limb0 h_add_addr_limb1 h_add_addr_limb2
        simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
        rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
        simp [BitVec.ofNatLT_toNat]
        simp [Word.toNat] at h_limb0_mem1
        grind

      have h_read_mem2 : s.mem[(Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + signExtend 64 op_c).toNat + 2]? = some (BitVec.truncate 8 (BitVec.ofNat 16 ↑Main[30])) := by
        simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
        rw [←h_op_c_is_signExtend, ←h_addr_add_spec]
        clear * - h_limb1_mem2 h_add_addr_limb0 h_add_addr_limb1 h_add_addr_limb2
        simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
        rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
        simp [BitVec.ofNatLT_toNat]
        simp [Word.toNat] at h_limb1_mem2
        grind

      have h_read_mem3 : s.mem[(Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + signExtend 64 op_c).toNat + 3]? = some (BitVec.truncate 8 ((BitVec.ofNat 16 ↑Main[30]) >>> 8)) := by
        simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
        rw [←h_op_c_is_signExtend, ←h_addr_add_spec]
        clear * - h_limb1_mem3 h_add_addr_limb0 h_add_addr_limb1 h_add_addr_limb2
        simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
        rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
        simp [BitVec.ofNatLT_toNat]
        simp [Word.toNat] at h_limb1_mem3
        grind

      have h_limb0_is_u16 : Main[29].val < 2^16 := h_mem_read_is_u64 0
      have h_limb1_is_u16 : Main[30].val < 2^16 := h_mem_read_is_u64 1
      simp only [←BitVec.ofNatLT_eq_ofNat h_limb0_is_u16, ←BitVec.ofNatLT_eq_ofNat h_limb1_is_u16] at h_read_mem0 h_read_mem1 h_read_mem2 h_read_mem3

      simp [-BitVec.toNat_add, spec_lwu, execute_LOAD, Sail.readReg, PreSail.readReg, h_read_pc, Sail.assert, PreSail.assert,
           LeanRV64IM.Functions.xlen_bytes, vmem_read, ext_data_get_addr, op_b, sp1_op_b, Sail.writeReg,
           PreSail.writeReg, Sail.rX_bits_eq_get_reg?_no_run, h_read_op_b, Option.elim, Option.toSailM,
           check_misaligned, LeanRV64IM.Functions.plat_enable_misaligned_access, LeanRV64IM.Functions.not,
           h_is_aligned, split_misaligned, bits_of_virtaddr, untilFuelM, untilFuelM.go, Sail.assert, PreSail.assert,
           translateAddr, Std.ExtDHashMap.get?_insert, h_mstatus, h_priv, effectivePrivilege, _get_Mstatus_MPRV,
           Sail.BitVec.extractLsb, translationMode, mem_read, Sail.readReg, PreSail.readReg, Sail.BitVec.extractLsb,
           translationMode, mem_read_priv, mem_read_priv_meta, checked_mem_read, phys_access_check, bits_of_virtaddr,
           LeanRV64IM.Functions.sys_pmp_count, within_mmio_readable, get_config_rvfi, Sail.BitVec.addInt, zero_extend,
           Sail.BitVec.zeroExtend, within_phys_mem, ext_check_phys_mem_read, phys_mem_read, read_kind_of_flags,
           read_ram, Sail.sail_mem_read, PreSail.sail_mem_read, PreSail.readBytes, PreSail.readByte, h_read_mem0,
           h_read_mem1, h_read_mem2, h_read_mem3, MemoryOpResult_drop_meta, h_op_a_not_x0, misaligned_order,
           sys_misaligned_order_decreasing, extend_value, sign_extend, Sail.BitVec.signExtend, sp1_lwu, op_a, sp1_op_a,
           Sail.run_write_reg_no_run, h_op_a_not_x0]

      have h_correct_limb0 : Main[39] = Main[29] := by simp_all only [chip_cstrs]
      have h_correct_limb1 : Main[40] = Main[30] := by simp_all only [chip_cstrs]
      rw [h_correct_limb0, h_correct_limb1]

      -- nextPC write
      simp [Word.toBitVec64, Word.toNat]
      rw [←BitVec.ofNatLT_eq_ofNat h_pc_is_u64]
      simp [BitVec.add_def]
      have : (↑(Main[3] + 4) + ↑Main[4] <<< 16 + ↑Main[5] <<< 32 : ℕ) = ↑Main[3] + ↑Main[4] <<< 16 + ↑Main[5] <<< 32 + 4 := by
        simp [Fin.add_def]
        rw [Nat.mod_eq_of_lt (by clear * - h_pc0; linarith)]
        ring_nf
      rw [this]
      clear this
      simp [op_a]

      apply congrArg
      apply congrArg

      -- op_a/rd write
      simp [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', default]
      sorry

    · rename_i h_shift
      simp [h_shift] at chip_cstrs h_read_limb0 h_read_limb1 h_read_limb2 h_read_limb3 addr_cstr2

      let h_addr_limb0_ge4 : Main[25] >= 4 :=
        by
          clear * - addr_cstr2
          by_contra!
          convert_to Main[25].val < 4 at this
          simp [Fin.lt_def, Fin.mul_def, Fin.sub_def] at addr_cstr2
          interval_cases Main[25].val
          <;> simp at addr_cstr2

      obtain ⟨h_limb2_mem0, h_limb2_mem1⟩ := h_read_limb2
      obtain ⟨h_limb3_mem2, h_limb3_mem3⟩ := h_read_limb3

      have h_read_mem0 : s.mem[(Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + signExtend 64 op_c).toNat]? = some (BitVec.truncate 8 (BitVec.ofNat 16 ↑Main[31])) := by
        simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
        rw [←h_op_c_is_signExtend, ←h_addr_add_spec]
        clear * - h_limb2_mem0 h_add_addr_limb0 h_add_addr_limb1 h_add_addr_limb2 h_addr_limb0_ge4
        simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
        rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
        simp [BitVec.ofNatLT_toNat]
        simp [Word.toNat] at h_limb2_mem0
        simp [Fin.sub_val_of_le h_addr_limb0_ge4] at h_limb2_mem0
        clear * - h_limb2_mem0 h_addr_limb0_ge4
        convert_to Main[25].val ≥ 4 at h_addr_limb0_ge4
        grind

      have h_read_mem1 : s.mem[(Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + signExtend 64 op_c).toNat + 1]? = some (BitVec.truncate 8 ((BitVec.ofNat 16 ↑Main[31]) >>> 8)) := by
        simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
        rw [←h_op_c_is_signExtend]
        rw [←h_addr_add_spec]
        clear * - h_limb2_mem1 h_add_addr_limb0 h_add_addr_limb1 h_add_addr_limb2 h_addr_limb0_ge4
        simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
        rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
        simp [BitVec.ofNatLT_toNat]
        simp [Word.toNat] at h_limb2_mem1
        simp [Fin.sub_val_of_le h_addr_limb0_ge4] at h_limb2_mem1
        convert_to Main[25].val ≥ 4 at h_addr_limb0_ge4
        grind

      have h_read_mem2 : s.mem[(Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + signExtend 64 op_c).toNat + 2]? = some (BitVec.truncate 8 ((BitVec.ofNat 16 ↑Main[32]))) := by
        simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
        rw [←h_op_c_is_signExtend]
        rw [←h_addr_add_spec]
        clear * - h_limb3_mem2 h_add_addr_limb0 h_add_addr_limb1 h_add_addr_limb2 h_addr_limb0_ge4
        simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
        rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
        simp [BitVec.ofNatLT_toNat]
        simp [Word.toNat] at h_limb3_mem2
        simp [Fin.sub_val_of_le h_addr_limb0_ge4] at h_limb3_mem2
        convert_to Main[25].val ≥ 4 at h_addr_limb0_ge4
        grind

      have h_read_mem3 : s.mem[(Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + signExtend 64 op_c).toNat + 3]? = some (BitVec.truncate 8 (((BitVec.ofNat 16 ↑Main[32])) >>> 8)) := by
        simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
        simp [Word.toNat] at h_limb3_mem3
        simp [Fin.sub_val_of_le h_addr_limb0_ge4] at h_limb3_mem3
        convert_to Main[25].val ≥ 4 at h_addr_limb0_ge4
        rw [←h_op_c_is_signExtend]
        rw [←h_addr_add_spec]
        clear * - h_limb3_mem3 h_add_addr_limb0 h_add_addr_limb1 h_add_addr_limb2 h_addr_limb0_ge4
        simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
        rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
        simp [BitVec.toNat_ofNatLT]
        grind

      have h_limb2_is_u16 : Main[31].val < 2^16 := h_mem_read_is_u64 2
      have h_limb3_is_u16 : Main[32].val < 2^16 := h_mem_read_is_u64 3
      simp only [←BitVec.ofNatLT_eq_ofNat h_limb2_is_u16, ←BitVec.ofNatLT_eq_ofNat h_limb3_is_u16] at h_read_mem0 h_read_mem1 h_read_mem2 h_read_mem3

      simp [-BitVec.toNat_add, spec_lwu, execute_LOAD, Sail.readReg, PreSail.readReg, h_read_pc, Sail.assert, PreSail.assert,
           LeanRV64IM.Functions.xlen_bytes, vmem_read, ext_data_get_addr, op_b, sp1_op_b, Sail.writeReg,
           PreSail.writeReg, Sail.rX_bits_eq_get_reg?_no_run, h_read_op_b, Option.elim, Option.toSailM,
           check_misaligned, LeanRV64IM.Functions.plat_enable_misaligned_access, LeanRV64IM.Functions.not,
           h_is_aligned, split_misaligned, bits_of_virtaddr, untilFuelM, untilFuelM.go, Sail.assert, PreSail.assert,
           translateAddr, Std.ExtDHashMap.get?_insert, h_mstatus, h_priv, effectivePrivilege, _get_Mstatus_MPRV,
           Sail.BitVec.extractLsb, translationMode, mem_read, Sail.readReg, PreSail.readReg, Sail.BitVec.extractLsb,
           translationMode, mem_read_priv, mem_read_priv_meta, checked_mem_read, phys_access_check, bits_of_virtaddr,
           LeanRV64IM.Functions.sys_pmp_count, within_mmio_readable, get_config_rvfi, Sail.BitVec.addInt, zero_extend,
           Sail.BitVec.zeroExtend, within_phys_mem, ext_check_phys_mem_read, phys_mem_read, read_kind_of_flags,
           read_ram, Sail.sail_mem_read, PreSail.sail_mem_read, PreSail.readBytes, PreSail.readByte, h_read_mem0,
           h_read_mem1, h_read_mem2, h_read_mem3, MemoryOpResult_drop_meta, h_op_a_not_x0, misaligned_order,
           sys_misaligned_order_decreasing, extend_value, sign_extend, Sail.BitVec.signExtend, sp1_lwu, op_a, sp1_op_a,
           Sail.run_write_reg_no_run, h_op_a_not_x0]

      have h_correct_limb0 : Main[39] = Main[31] := by simp_all only [chip_cstrs]
      have h_correct_limb1 : Main[40] = Main[32] := by simp_all only [chip_cstrs]
      rw [h_correct_limb0, h_correct_limb1]

      -- nextPC write
      simp [Word.toBitVec64, Word.toNat]
      rw [←BitVec.ofNatLT_eq_ofNat h_pc_is_u64]
      simp [BitVec.add_def]
      have : (↑(Main[3] + 4) + ↑Main[4] <<< 16 + ↑Main[5] <<< 32 : ℕ) = ↑Main[3] + ↑Main[4] <<< 16 + ↑Main[5] <<< 32 + 4 := by
        simp [Fin.add_def]
        rw [Nat.mod_eq_of_lt (by clear * - h_pc0; linarith)]
        ring_nf
      rw [this]
      clear this
      simp [op_a]

      apply congrArg
      apply congrArg

      -- op_a/rd write
      simp [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', default]
      sorry

end LWU

end LoadWord

end Load
