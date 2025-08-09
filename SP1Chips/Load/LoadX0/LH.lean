import SP1Foundations
import SP1Chips.Load.LoadX0.Constraints
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

attribute [simp] bind StateT.bind ExceptT.bind EStateM.bind ExceptT.bindCont get getThe MonadStateOf.get StateT.get EStateM.get pure StateT.pure ExceptT.pure EStateM.pure Functor.map StateT.map ExceptT.map EStateM.map modify modifyGet EStateM.modifyGet StateT.modifyGet MonadStateOf.modifyGet liftM monadLift MonadLift.monadLift ExceptT.lift StateT.lift ExceptT.mk StateT.run ExceptT.run EStateM.run Sail.SailME.run

-- attribute [-simp] Sail.wX_bits_eq_writeReg

attribute [grind] BitVec.toNat_ofNatLT

namespace Load

namespace LoadX0

variable
  (Main : Vector (Fin BB) 48)
  (s : SailState)
  (cstrs : (constraints Main).allHold)

namespace LH

open BitVec

variable
  (h_is_lh : Main[43] = 1)

def spec_lh (imm : BitVec 12) (rs2 rs1 : regidx) : SailM ExecutionResult :=
  do
    Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
    execute_LOAD imm rs2 rs1 false 2

def sp1_op_a : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[6] ?_
    show Main[6] < 32
    have ⟨h_lb, h_lbu, h_lh, h_lhu, h_lw, h_lwu, h_ld⟩ := (h_exactly_one Main cstrs).2.2.1 h_is_lh
    simp [constraints, AddressOperation.constraints, ITypeReaderImmutable.constraints, SP1Constraint.toProp, List.Forall, h_lb, h_lbu, h_lh, h_lhu, h_lw, h_lwu, h_ld] at cstrs
    simp_all only

def sp1_op_b : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[14] ?_
    show Main[14] < 32
    have ⟨h_lb, h_lbu, h_lh, h_lhu, h_lw, h_lwu, h_ld⟩ := (h_exactly_one Main cstrs).2.2.1 h_is_lh
    simp [constraints, AddressOperation.constraints, ITypeReaderImmutable.constraints, SP1Constraint.toProp, List.Forall, h_lb, h_lbu, h_lh, h_lhu, h_lw, h_lwu, h_ld, Opcode.ofNat, Nat.ble, Nat.beq] at cstrs
    simp_all only

def sp1_lh : SailM ExecutionResult := do
    let op_a := sp1_op_a Main cstrs h_is_lh
    Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
    -- This is `op_a_memory.prev_value` per `eval_op_a_immutable` in SP1
    Sail.write_reg op_a (Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]])
    pure RETIRE_SUCCESS

set_option maxHeartbeats 4000000 in
set_option pp.proofs false in
set_option diagnostics false in
theorem correct_x0
  (Main : Vector (Fin BB) 48)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (state_cstrs : (constraints Main).initialState s)
  (h_is_lh : Main[43] = 1)
  (h_mstatus : s.regs.get? Register.mstatus = some 0)
  (h_priv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
  : let op_a := sp1_op_a Main cstrs h_is_lh
    let op_b := sp1_op_b Main cstrs h_is_lh
    let op_c := sp1_imm Main
    (spec_lh op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_lh Main cstrs h_is_lh).run s
  := by
    extract_lets op_a op_b op_c

    have ⟨h_lb, h_lbu, h_lh, h_lhu, h_lw, h_lwu, h_ld⟩ := (h_exactly_one Main cstrs).2.2.1 h_is_lh
    stop
    simp [-Word.add_toBitVec64_mod4, constraints, AddressOperation.constraints, AddrAddOperation.constraints, CPUState.constraints, ITypeReaderImmutable.constraints, SP1Constraint.toStateProp, List.Forall, h_lb, h_lbu, h_lh, h_lhu, h_lw, h_lwu, h_ld, Opcode.ofNat, ByteOpcode.ofNat, Nat.beq, Nat.ble] at state_cstrs
    obtain ⟨h_read_pc, ⟨h_trusted_read, h_read_addr_within_range⟩, h_read_op_a, h_read_op_b, h_read_mem⟩ := state_cstrs

    simp [constraints, AddressOperation.constraints, SP1Constraint.toProp, List.Forall, h_is_lh, h_lb, h_lbu, h_lh, h_lhu, h_lw, h_lwu, h_ld, Opcode.ofNat, ByteOpcode.ofNat, Nat.beq, Nat.ble, sub_eq_zero] at cstrs
    obtain ⟨addr_add_cstrs, h_addr_shift0, h_addr_shift1, h_addr_shift2, addr_cstr0, addr_cstr1, cpu_cstrs, reader_cstrs, chip_cstrs⟩ := cstrs

    simp [ITypeReaderImmutable.constraints, SP1Constraint.toProp, List.Forall, Opcode.ofNat, ByteOpcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs

    have h_op_a_is_reg : Main[6] < 32 := by simp_all only
    simp [h_op_a_is_reg] at h_read_op_a
    have h_op_b_is_reg : Main[14] < 32 := by simp_all only
    simp [h_op_b_is_reg] at h_read_op_b
    -- simp [-Word.add_toBitVec64_mod4, ←BitVec.ofNatLT_eq_ofNat (w := 5) (n := Main[14].val) h_op_b_is_reg, h_read_op_b] at h_trusted_read
    rw [←BitVec.ofNatLT_eq_ofNat (w := 5) (n := Main[14].val) h_op_b_is_reg, h_read_op_b, Option.get!_some] at h_trusted_read
    rw [←BitVec.ofNatLT_eq_ofNat h_op_b_is_reg, h_read_op_b, Option.get!_some] at h_read_addr_within_range

    have h_mem_read_is_u64 : Word.isU64 #v[Main[29], Main[30], Main[31], Main[32]] := by simp_all only [chip_cstrs]

    have h_addr_no_shift0 : Main[38] = 0 := by simp_all only
    simp [h_addr_no_shift0] at addr_cstr1

    have h_over_addr : Main[26] ≠ 0 ∨ Main[27] ≠ 0 :=
      by
        by_contra!
        obtain ⟨h_limb1_0, h_limb2_0⟩ := this
        simp [h_limb1_0, h_limb2_0] at addr_cstr0
    simp [not_and_or.mpr h_over_addr, Word.toNat, h_addr_no_shift0] at h_read_mem
    obtain ⟨h_read_limb0, h_read_limb1, h_read_limb2, h_read_limb3⟩ := h_read_mem

    have h_op_c_is_signExtend : Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] = BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) := by
      simp_all only

    have h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64 op_c)) 2 = true := by
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


    have h_imm_c_is_0 : Main[13] = 1 := by simp_all only [chip_cstrs]
    simp [h_imm_c_is_0] at reader_cstrs
    have h_op_a_x0 : op_a = 0#5 :=
      by
        simp [op_a, sp1_op_a, BitVec.ofNatLT, BitVec.ofNat]
        clear * - h_imm_c_is_0 reader_cstrs
        aesop

    have h_op_a_limb0_is_0 : Main[7] = 0 := by simp_all only [reader_cstrs]
    have h_op_a_limb1_is_0 : Main[8] = 0 := by simp_all only [reader_cstrs]
    have h_op_a_limb2_is_0 : Main[9] = 0 := by simp_all only [reader_cstrs]
    have h_op_a_limb3_is_0 : Main[10] = 0 := by simp_all only [reader_cstrs]
    have h_op_a_val_is_0 : Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]] = 0#64 :=
      by
        simp [h_op_a_limb0_is_0, h_op_a_limb1_is_0, h_op_a_limb2_is_0, h_op_a_limb3_is_0, Word.toBitVec64, Word.toNat]

    simp [op_a, sp1_op_a] at h_op_a_x0
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

    have h_limb0_is_u16 : Main[29].val < 2^16 := h_mem_read_is_u64 0
    have h_limb1_is_u16 : Main[30].val < 2^16 := h_mem_read_is_u64 1
    have h_limb2_is_u16 : Main[31].val < 2^16 := h_mem_read_is_u64 2
    have h_limb3_is_u16 : Main[32].val < 2^16 := h_mem_read_is_u64 3

    cases h_addr_shift1
    <;> rename_i h_shift1
    <;> cases h_addr_shift2
    <;> rename_i h_shift2
    <;> simp [h_shift1, h_shift2] at chip_cstrs h_read_limb0 h_read_limb1 h_read_limb2 h_read_limb3 addr_cstr1
    <;> [
      -- case offset 0
      (
        obtain
          ⟨h_read_mem0, h_read_mem1⟩
          : s.mem[(Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + signExtend 64 op_c).toNat]? = some (BitVec.truncate 8 (BitVec.ofNat 16 ↑Main[29]))
          ∧ s.mem[(Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + signExtend 64 op_c).toNat + 1]? = some (BitVec.truncate 8 ((BitVec.ofNat 16 ↑Main[29]) >>> 8))
          := by
            simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
            rw [←h_op_c_is_signExtend, ←h_addr_add_spec]
            clear * - h_read_limb0 h_read_limb1 h_read_limb2 h_read_limb3
            simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
            rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
            simp [BitVec.ofNatLT_toNat]
            split_ands <;> grind
      );

      -- case offset 4
      (
        let h_addr_limb0_ge4 : Main[25] >= 4 :=
          by
            clear * - addr_cstr1
            by_contra!
            convert_to Main[25].val < 4 at this
            simp [Fin.lt_def, Fin.mul_def, Fin.sub_def] at addr_cstr1
            interval_cases Main[25].val
            <;> simp at addr_cstr1

        obtain
          ⟨h_read_mem0, h_read_mem1, h_read_mem2, h_read_mem3⟩
          : s.mem[(Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + signExtend 64 op_c).toNat]? = some (BitVec.truncate 8 (BitVec.ofNat 16 ↑Main[31]))
          ∧ s.mem[(Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + signExtend 64 op_c).toNat + 1]? = some (BitVec.truncate 8 ((BitVec.ofNat 16 ↑Main[31]) >>> 8))
          ∧ s.mem[(Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + signExtend 64 op_c).toNat + 2]? = some (BitVec.truncate 8 (BitVec.ofNat 16 ↑Main[32]))
          ∧ s.mem[(Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + signExtend 64 op_c).toNat + 3]? = some (BitVec.truncate 8 ((BitVec.ofNat 16 ↑Main[32]) >>> 8))
          := by
            simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
            rw [←h_op_c_is_signExtend, ←h_addr_add_spec]
            clear * - h_addr_limb0_ge4 h_read_limb0 h_read_limb1 h_read_limb2 h_read_limb3
            simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
            rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
            simp [BitVec.ofNatLT_toNat]
            simp [Fin.sub_val_of_le h_addr_limb0_ge4] at *
            convert_to Main[25].val ≥ 4 at h_addr_limb0_ge4
            split_ands <;> grind
      );

      -- case offset 2
      (
        let h_addr_limb0_ge2 : Main[25] >= 2 :=
          by
            clear * - addr_cstr1
            by_contra!
            convert_to Main[25].val < 2 at this
            simp [Fin.lt_def, Fin.mul_def, Fin.sub_def] at addr_cstr1
            interval_cases Main[25].val
            <;> simp at addr_cstr1

        obtain
          ⟨h_read_mem0, h_read_mem1⟩
          : s.mem[(Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + signExtend 64 op_c).toNat]? = some (BitVec.truncate 8 (BitVec.ofNat 16 ↑Main[30]))
          ∧ s.mem[(Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + signExtend 64 op_c).toNat + 1]? = some (BitVec.truncate 8 ((BitVec.ofNat 16 ↑Main[30]) >>> 8))
          := by
            simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
            rw [←h_op_c_is_signExtend, ←h_addr_add_spec]
            clear * - h_addr_limb0_ge2 h_read_limb0 h_read_limb1 h_read_limb2 h_read_limb3
            simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
            rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
            simp [BitVec.ofNatLT_toNat]
            simp [Fin.sub_val_of_le h_addr_limb0_ge2] at *
            convert_to Main[25].val ≥ 2 at h_addr_limb0_ge2
            split_ands <;> grind
      );

      -- case offset 6
      (
        let h_addr_limb0_ge6 : Main[25] >= 6 :=
          by
            clear * - addr_cstr1
            by_contra!
            convert_to Main[25].val < 6 at this
            simp [Fin.lt_def, Fin.mul_def, Fin.sub_def] at addr_cstr1
            interval_cases Main[25].val
            <;> simp at addr_cstr1

        let h_addr_limb0_sub4_ge2 : Main[25] - 4 >= 2 :=
          by
            clear * - h_addr_limb0_ge6
            simp at h_addr_limb0_ge6 ⊢
            all_goals omega

        let h_addr_limb0_ge4 : Main[25] >= 4 :=
          by
            clear * - h_addr_limb0_ge6
            simp at h_addr_limb0_ge6 ⊢
            all_goals omega

        obtain
          ⟨h_read_mem0, h_read_mem1⟩
          : s.mem[(Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + signExtend 64 op_c).toNat]? = some (BitVec.truncate 8 (BitVec.ofNat 16 ↑Main[32]))
          ∧ s.mem[(Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + signExtend 64 op_c).toNat + 1]? = some (BitVec.truncate 8 ((BitVec.ofNat 16 ↑Main[32]) >>> 8))
          := by
            simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
            rw [←h_op_c_is_signExtend, ←h_addr_add_spec]
            clear * - h_addr_limb0_ge6 h_addr_limb0_ge4 h_addr_limb0_sub4_ge2 h_read_limb0 h_read_limb1 h_read_limb2 h_read_limb3
            simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
            rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
            simp [BitVec.ofNatLT_toNat]
            simp [Fin.sub_val_of_le h_addr_limb0_sub4_ge2, Fin.sub_val_of_le h_addr_limb0_ge4] at *
            convert_to Main[25].val ≥ 6 at h_addr_limb0_ge6
            convert_to Main[25].val ≥ 4 at h_addr_limb0_ge4
            split_ands <;> grind
      )
    ]

    <;> simp only [
          ←BitVec.ofNatLT_eq_ofNat h_limb0_is_u16,
          ←BitVec.ofNatLT_eq_ofNat h_limb1_is_u16,
          ←BitVec.ofNatLT_eq_ofNat h_limb2_is_u16,
          ←BitVec.ofNatLT_eq_ofNat h_limb3_is_u16
          ] at h_read_mem0 h_read_mem1

    <;> simp [-BitVec.toNat_add, spec_lh, execute_LOAD, Sail.readReg, PreSail.readReg, h_read_pc, Sail.assert, PreSail.assert,
         LeanRV64IM.Functions.xlen_bytes, vmem_read, ext_data_get_addr, op_b, sp1_op_b, Sail.writeReg,
         PreSail.writeReg, Sail.rX_bits_eq_get_reg?_no_run, h_read_op_b, Option.elim, Option.toSailM,
         h_is_aligned, check_misaligned, LeanRV64IM.Functions.plat_enable_misaligned_access, LeanRV64IM.Functions.not,
         split_misaligned, bits_of_virtaddr, untilFuelM, untilFuelM.go, Sail.assert, PreSail.assert,
         translateAddr, Std.ExtDHashMap.get?_insert, h_mstatus, h_priv, effectivePrivilege, _get_Mstatus_MPRV,
         Sail.BitVec.extractLsb, translationMode, mem_read, Sail.readReg, PreSail.readReg, Sail.BitVec.extractLsb,
         translationMode, mem_read_priv, mem_read_priv_meta, checked_mem_read, phys_access_check, bits_of_virtaddr,
         LeanRV64IM.Functions.sys_pmp_count, within_mmio_readable, get_config_rvfi, Sail.BitVec.addInt, zero_extend,
         Sail.BitVec.zeroExtend, within_phys_mem, ext_check_phys_mem_read, phys_mem_read, read_kind_of_flags,
         read_ram, Sail.sail_mem_read, PreSail.sail_mem_read, PreSail.readBytes, PreSail.readByte, h_read_mem0, h_read_mem1,
         MemoryOpResult_drop_meta, h_op_a_x0, h_op_a_val_is_0, misaligned_order,
         sys_misaligned_order_decreasing, extend_value, sign_extend, Sail.BitVec.signExtend, sp1_lh, op_a, sp1_op_a,
         Sail.run_write_reg_no_run]

    all_goals
      simp [Word.toBitVec64, Word.toNat]
      rw [←BitVec.ofNatLT_eq_ofNat h_pc_is_u64]
      simp [BitVec.add_def]
      have : (↑(Main[3] + 4) + ↑Main[4] <<< 16 + ↑Main[5] <<< 32 : ℕ) = ↑Main[3] + ↑Main[4] <<< 16 + ↑Main[5] <<< 32 + 4 := by
        simp [Fin.add_def]
        rw [Nat.mod_eq_of_lt (by clear * - h_pc0; linarith)]
        ring_nf
      rw [this]

end LH

end LoadX0

end Load
