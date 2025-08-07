import SP1Foundations
import SP1Chips.Load.LoadByte.Constraints
import SP1Operations.Operation.AddrAddOperation
import LeanRV64IM.Specialization
import LeanRV64IM.RiscvMem
import LeanRV64IM.RiscvInstsEnd

syntax:max term noWs "[" withoutPosition(term) "]$" : term
macro_rules | `($x[$i]$) => `(getElem $x $i (by simp))

instance : Lean.Grind.NoNatZeroDivisors (Fin BB) where
  no_nat_zero_divisors := sorry

open LeanRV64IM.Functions

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

namespace LoadByte

open BitVec

namespace LB

variable
  (Main : Vector (Fin BB) 47)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_lb : Main[45] = 1)

private theorem is_lb_eq_not_lbu
  (cstrs : (constraints Main).allHold)
  (h_is_lb : Main[45] = 1)
  -- (h_is_real : Main[28] + Main[29] + Main[30] + Main[31] + Main[32] + Main[33] = 1)
  : Main[46] = 0 := by
  simp [constraints, SP1ConstraintList.allHold, List.Forall, AddressOperation.constraints, h_is_lb, sub_eq_zero] at cstrs
  have h_is_lw_is_bool : Main[46] = 0 ∨ Main[46] = 1 := by simp_all only
  cases h_is_lw_is_bool
  · assumption
  rename_i h_is_lw
  simp [h_is_lw] at cstrs

def spec_lb (imm : BitVec 12) (rs2 rs1 : regidx) : SailM ExecutionResult :=
  do
    Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
    execute_LOAD imm rs2 rs1 false 1

def sp1_op_a : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[6] ?_
    show Main[6] < 32

    have h_not_lw : Main[46] = 0 := is_lb_eq_not_lbu Main cstrs h_is_lb
    simp [constraints, AddressOperation.constraints, AddrAddOperation.constraints, CPUState.constraints, ITypeReader.constraints, SP1Constraint.toProp, List.Forall, h_is_lb, h_not_lw] at cstrs
    simp_all only

def sp1_op_b : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[14] ?_
    show Main[14] < 32

    have h_not_lw : Main[46] = 0 := is_lb_eq_not_lbu Main cstrs h_is_lb
    simp [constraints, AddressOperation.constraints, AddrAddOperation.constraints, CPUState.constraints, ITypeReader.constraints, SP1Constraint.toProp, List.Forall, h_is_lb, h_not_lw, Opcode.ofNat, Nat.ble, Nat.beq] at cstrs
    simp_all only

def sp1_imm : BitVec 12 := BitVec.ofNat 12 Main[21].val

def sp1_lb : SailM ExecutionResult :=
  do
    let op_a := sp1_op_a Main cstrs h_is_lb
    let E71 : Fin BB := 65280 * Main[44]
    let E72 : Fin BB := Main[43] + E71
    let E73 : Fin BB := 65535 * Main[44]
    let E74 : Fin BB := 65535 * Main[44]
    let E75 : Fin BB := 65535 * Main[44]
    Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
    Sail.write_reg op_a (Word.toBitVec64 #v[E72, E73, E74, E75])
    pure RETIRE_SUCCESS

set_option maxHeartbeats 4000000 in
set_option pp.proofs false in
set_option diagnostics false in
theorem correct
  (Main : Vector (Fin BB) 47)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (state_cstrs : (constraints Main).initialState s)
  (h_is_lb : Main[45] = 1)
  (h_mstatus : s.regs.get? Register.mstatus = some 0)
  (h_priv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
  (mem0 mem1 mem2 mem3 : BitVec 8)
  -- assumptions!
  : let op_a := sp1_op_a Main cstrs h_is_lb
    let op_b := sp1_op_b Main cstrs h_is_lb
    let op_c := sp1_imm Main
    (spec_lb op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_lb Main cstrs h_is_lb).run s
  := by
    extract_lets op_a op_b op_c
    have h_not_lbu : Main[46] = 0 := is_lb_eq_not_lbu Main cstrs h_is_lb

    simp [-Word.add_toBitVec64_mod4, constraints, AddressOperation.constraints, AddrAddOperation.constraints, CPUState.constraints, ITypeReader.constraints, SP1Constraint.toStateProp, List.Forall, h_is_lb, h_not_lbu, Opcode.ofNat, ByteOpcode.ofNat, Nat.beq, Nat.ble] at state_cstrs
    obtain ⟨h_read_pc, h_read_addr_within_range, h_read_op_a, h_read_op_b, h_read_mem⟩ := state_cstrs

    simp [constraints, AddressOperation.constraints, SP1Constraint.toProp, List.Forall, h_is_lb, h_not_lbu, Opcode.ofNat, ByteOpcode.ofNat, Nat.beq, Nat.ble, sub_eq_zero] at cstrs
    obtain ⟨addr_add_cstrs, h_addr_shift0, h_addr_shift1, h_addr_shift2, addr_cstr0, addr_cstr1, cpu_cstrs, reader_cstrs, chip_cstrs⟩ := cstrs

    simp [ITypeReader.constraints, SP1Constraint.toProp, List.Forall, Opcode.ofNat, ByteOpcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs

    have h_op_a_is_reg : Main[6]$ < 32 := by simp_all only
    simp [h_op_a_is_reg] at h_read_op_a
    have h_op_b_is_reg : Main[14]$ < 32 := by simp_all only
    simp [h_op_b_is_reg] at h_read_op_b
    -- simp [-Word.add_toBitVec64_mod4, ←BitVec.ofNatLT_eq_ofNat (w := 5) (n := Main[14].val) h_op_b_is_reg, h_read_op_b] at h_trusted_read
    rw [←BitVec.ofNatLT_eq_ofNat h_op_b_is_reg, h_read_op_b, Option.get!_some] at h_read_addr_within_range

    have h_mem_read_is_u64 : Word.isU64 #v[Main[29]$, Main[30]$, Main[31]$, Main[32]$] := by simp_all only [chip_cstrs]

    have h_over_addr : Main[26]$ ≠ 0 ∨ Main[27]$ ≠ 0 :=
      by
        by_contra!
        obtain ⟨h_limb1_0, h_limb2_0⟩ := this
        simp [h_limb1_0, h_limb2_0] at addr_cstr0
    simp [not_and_or.mpr h_over_addr, Word.toNat] at h_read_mem
    obtain ⟨h_read_limb0, h_read_limb1, h_read_limb2, h_read_limb3⟩ := h_read_mem

    have h_op_c_is_signExtend : Word.toBitVec64 #v[Main[21]$, Main[22]$, Main[23]$, Main[24]$] = BitVec.signExtend 64 (BitVec.ofNat 12 Main[21]$.val) := by
      simp [constraints, AddressOperation.constraints, AddrAddOperation.constraints, CPUState.constraints, ITypeReader.constraints, SP1Constraint.toProp, List.Forall, h_is_lb, h_not_lbu, Opcode.ofNat, ByteOpcode.ofNat, Nat.beq, Nat.ble] at cstrs
      simp_all only

    have h_op_a_not_x0 : op_a ≠ 0#5 := by
      simp [op_a, sp1_op_a, BitVec.ofNatLT, BitVec.ofNat]
      have h_imm_c_is_0 : Main[13]$ = 0 := by simp_all only [chip_cstrs]
      have h_imm_c_iff_op_a_x0 : Main[13]$ = 1 ↔ Main[6]$ = 0 := by
        simp_all only [reader_cstrs]
      rw [Fin.mk_eq_mk]
      simp
      clear * - h_imm_c_is_0 h_imm_c_iff_op_a_x0
      aesop

    simp [op_a, sp1_op_a] at h_op_a_not_x0
    have h_pc0 : Main[3]$.val < 65536 := by clear * - reader_cstrs; show Main[3] < 65536; simp_all only
    have h_pc1 : Main[4]$.val < 65536 := by clear * - reader_cstrs; show Main[4] < 65536; simp_all only
    have h_pc2 : Main[5]$.val < 65536 := by clear * - reader_cstrs; show Main[5] < 65536; simp_all only
    have h_pc_is_u64 : Main[3]$.val + Main[4]$.val <<< 16 + Main[5]$.val <<< 32 < 2^64 := by
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
      (by exact h_read_addr_within_range) -- TODO(gzgz): not exceeding memory bounds, this should come from AddrAdd but we trust this too
    simp at h_add_addr_limb0 h_add_addr_limb1 h_add_addr_limb2 h_addr_add_spec

    have h_limb0_is_u16 : Main[29]$.val < 2^16 := h_mem_read_is_u64 0
    have h_limb1_is_u16 : Main[30]$.val < 2^16 := h_mem_read_is_u64 1
    have h_limb2_is_u16 : Main[31]$.val < 2^16 := h_mem_read_is_u64 2
    have h_limb3_is_u16 : Main[32]$.val < 2^16 := h_mem_read_is_u64 3

    cases h_addr_shift0
    <;> rename_i h_shift0
    <;> cases h_addr_shift1
    <;> rename_i h_shift1
    <;> cases h_addr_shift2
    <;> rename_i h_shift2
    <;> simp [h_shift0, h_shift1, h_shift2] at chip_cstrs h_read_limb0 h_read_limb1 h_read_limb2 h_read_limb3 addr_cstr1

    <;> [
      -- case offset 0
      ( skip
        obtain h_read_mem : s.mem[(Word.toBitVec64 #v[Main[15]$, Main[16]$, Main[17]$, Main[18]$] + signExtend 64 op_c).toNat]? = some (setWidth 8 (BitVec.ofNat 16 ↑Main[29]$)) :=
          by
            simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
            rw [←h_op_c_is_signExtend, ←h_addr_add_spec]
            clear * - h_read_limb0 h_read_limb1 h_read_limb2 h_read_limb3
            simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
            rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
            simp [BitVec.ofNatLT_toNat]
            grind
      );

      -- case offset 4
      ( skip
        let h_addr_limb0_ge4 : Main[25]$ >= 4 :=
          by
            clear * - addr_cstr1
            by_contra!
            convert_to Main[25].val < 4 at this
            simp [Fin.lt_def, Fin.mul_def, Fin.sub_def] at addr_cstr1
            interval_cases Main[25].val
            <;> simp at addr_cstr1

        obtain h_read_mem : s.mem[(Word.toBitVec64 #v[Main[15]$, Main[16]$, Main[17]$, Main[18]$] + signExtend 64 op_c).toNat]? = some (setWidth 8 (BitVec.ofNat 16 ↑Main[31]$)) :=
          by
            simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
            rw [←h_op_c_is_signExtend, ←h_addr_add_spec]
            clear * - h_addr_limb0_ge4 h_read_limb0 h_read_limb1 h_read_limb2 h_read_limb3
            simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
            rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
            simp [BitVec.ofNatLT_toNat]
            simp [Fin.sub_val_of_le h_addr_limb0_ge4] at *
            convert_to Main[25]$.val ≥ 4 at h_addr_limb0_ge4
            grind
      );

      -- case offset 2
      ( skip
        let h_addr_limb0_ge2 : Main[25]$ >= 2 :=
          by
            clear * - addr_cstr1
            by_contra!
            convert_to Main[25].val < 2 at this
            simp [Fin.lt_def, Fin.mul_def, Fin.sub_def] at addr_cstr1
            interval_cases Main[25].val
            <;> simp at addr_cstr1

        obtain h_read_mem : s.mem[(Word.toBitVec64 #v[Main[15]$, Main[16]$, Main[17]$, Main[18]$] + signExtend 64 op_c).toNat]? = some (setWidth 8 (BitVec.ofNat 16 ↑Main[30]$)) :=
          by
            simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
            rw [←h_op_c_is_signExtend, ←h_addr_add_spec]
            clear * - h_addr_limb0_ge2 h_read_limb0 h_read_limb1 h_read_limb2 h_read_limb3
            simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
            rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
            simp [BitVec.ofNatLT_toNat]
            simp [Fin.sub_val_of_le h_addr_limb0_ge2] at *
            convert_to Main[25]$.val ≥ 2 at h_addr_limb0_ge2
            grind
      );

      -- case offset 6
      ( skip
        let h_addr_limb0_ge6 : Main[25]$ >= 6 :=
          by
            clear * - addr_cstr1
            by_contra!
            convert_to Main[25].val < 6 at this
            simp [Fin.lt_def, Fin.mul_def, Fin.sub_def] at addr_cstr1
            interval_cases Main[25].val
            <;> simp at addr_cstr1

        let h_addr_limb0_sub4_ge2 : Main[25]$ - 4 >= 2 :=
          by
            clear * - h_addr_limb0_ge6
            simp at h_addr_limb0_ge6 ⊢ 
            all_goals omega

        let h_addr_limb0_ge4 : Main[25]$ >= 4 :=
          by
            clear * - h_addr_limb0_ge6
            simp at h_addr_limb0_ge6 ⊢ 
            all_goals omega

        obtain h_read_mem : s.mem[(Word.toBitVec64 #v[Main[15]$, Main[16]$, Main[17]$, Main[18]$] + signExtend 64 op_c).toNat]? = some (BitVec.truncate 8 (BitVec.ofNat 16 ↑Main[32]$))
          := by
            simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
            rw [←h_op_c_is_signExtend, ←h_addr_add_spec]
            clear * - h_addr_limb0_ge6 h_addr_limb0_ge4 h_addr_limb0_sub4_ge2 h_read_limb0 h_read_limb1 h_read_limb2 h_read_limb3
            simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
            rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
            simp [BitVec.ofNatLT_toNat]
            simp [Fin.sub_val_of_le h_addr_limb0_sub4_ge2, Fin.sub_val_of_le h_addr_limb0_ge4] at *
            convert_to Main[25]$.val ≥ 6 at h_addr_limb0_ge6
            convert_to Main[25]$.val ≥ 4 at h_addr_limb0_ge4
            grind
      );

      -- case offset 1
      ( skip
        let h_addr_limb0_ge1 : Main[25]$ >= 1 :=
          by
            clear * - addr_cstr1
            by_contra!
            convert_to Main[25].val < 1 at this
            simp [Fin.lt_def, Fin.mul_def, Fin.sub_def] at addr_cstr1
            interval_cases Main[25].val
            simp at addr_cstr1

        obtain h_read_mem : s.mem[(Word.toBitVec64 #v[Main[15]$, Main[16]$, Main[17]$, Main[18]$] + signExtend 64 op_c).toNat]? = some (setWidth 8 (BitVec.ofNat 16 ↑Main[29]$ >>> 8)) :=
          by
            simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
            rw [←h_op_c_is_signExtend, ←h_addr_add_spec]
            clear * - h_addr_limb0_ge1 h_read_limb0 h_read_limb1 h_read_limb2 h_read_limb3
            simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
            rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
            simp [BitVec.ofNatLT_toNat]
            simp [Fin.sub_val_of_le h_addr_limb0_ge1] at *
            convert_to Main[25]$.val ≥ 1 at h_addr_limb0_ge1
            grind
      );

      -- case offset 5
      ( skip
        let h_addr_limb0_ge5 : Main[25]$ >= 5 :=
          by
            clear * - addr_cstr1
            by_contra!
            convert_to Main[25].val < 5 at this
            simp [Fin.lt_def, Fin.mul_def, Fin.sub_def] at addr_cstr1
            interval_cases Main[25].val
            <;> simp at addr_cstr1

        let h_addr_limb0_sub4_ge1 : Main[25]$ - 4 >= 1 :=
          by
            clear * - h_addr_limb0_ge5
            simp at h_addr_limb0_ge5 ⊢ 
            all_goals omega

        let h_addr_limb0_ge4 : Main[25]$ >= 4 :=
          by
            clear * - h_addr_limb0_ge5
            simp at h_addr_limb0_ge5 ⊢ 
            all_goals omega

        obtain h_read_mem : s.mem[(Word.toBitVec64 #v[Main[15]$, Main[16]$, Main[17]$, Main[18]$] + signExtend 64 op_c).toNat]? = some (BitVec.truncate 8 (BitVec.ofNat 16 ↑Main[31]$ >>> 8))
          := by
            simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
            rw [←h_op_c_is_signExtend, ←h_addr_add_spec]
            clear * - h_addr_limb0_ge5 h_addr_limb0_ge4 h_addr_limb0_sub4_ge1 h_read_limb0 h_read_limb1 h_read_limb2 h_read_limb3
            simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
            rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
            simp [BitVec.ofNatLT_toNat]
            simp [Fin.sub_val_of_le h_addr_limb0_sub4_ge1, Fin.sub_val_of_le h_addr_limb0_ge4] at *
            convert_to Main[25]$.val ≥ 5 at h_addr_limb0_ge5
            convert_to Main[25]$.val ≥ 4 at h_addr_limb0_ge4
            grind
      );

      -- case offset 3
      ( skip
        let h_addr_limb0_ge3 : Main[25]$ >= 3 :=
          by
            clear * - addr_cstr1
            by_contra!
            convert_to Main[25].val < 3 at this
            simp [Fin.lt_def, Fin.mul_def, Fin.sub_def] at addr_cstr1
            interval_cases Main[25].val
            <;> simp at addr_cstr1

        let h_addr_limb0_sub2_ge1 : Main[25]$ - 2 >= 1 :=
          by
            clear * - h_addr_limb0_ge3
            simp at h_addr_limb0_ge3 ⊢ 
            all_goals omega

        let h_addr_limb0_ge2 : Main[25]$ >= 2 :=
          by
            clear * - h_addr_limb0_ge3
            simp at h_addr_limb0_ge3 ⊢ 
            all_goals omega

        obtain h_read_mem : s.mem[(Word.toBitVec64 #v[Main[15]$, Main[16]$, Main[17]$, Main[18]$] + signExtend 64 op_c).toNat]? = some (BitVec.truncate 8 (BitVec.ofNat 16 ↑Main[30]$ >>> 8))
          := by
            simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
            rw [←h_op_c_is_signExtend, ←h_addr_add_spec]
            clear * - h_addr_limb0_ge3 h_addr_limb0_ge2 h_addr_limb0_sub2_ge1 h_read_limb0 h_read_limb1 h_read_limb2 h_read_limb3
            simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
            rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
            simp [BitVec.ofNatLT_toNat]
            simp [Fin.sub_val_of_le h_addr_limb0_sub2_ge1, Fin.sub_val_of_le h_addr_limb0_ge2] at *
            convert_to Main[25]$.val ≥ 3 at h_addr_limb0_ge3
            convert_to Main[25]$.val ≥ 2 at h_addr_limb0_ge2
            grind
      );

      ( skip
        let h_addr_limb0_ge7 : Main[25]$ >= 7 :=
          by
            clear * - addr_cstr1
            by_contra!
            convert_to Main[25].val < 7 at this
            simp [Fin.lt_def, Fin.mul_def, Fin.sub_def] at addr_cstr1
            interval_cases Main[25].val
            <;> simp at addr_cstr1

        let h_addr_limb0_sub4_sub2_ge1 : Main[25]$ - 4 - 2 >= 1 :=
          by
            clear * - h_addr_limb0_ge7
            simp at h_addr_limb0_ge7 ⊢ 
            all_goals omega

        let h_addr_limb0_sub4_ge2 : Main[25]$ - 4 >= 2 :=
          by
            clear * - h_addr_limb0_ge7
            simp at h_addr_limb0_ge7 ⊢ 
            all_goals omega

        let h_addr_limb0_ge4 : Main[25]$ >= 4 :=
          by
            clear * - h_addr_limb0_ge7
            simp at h_addr_limb0_ge7 ⊢ 
            all_goals omega
        
        obtain h_read_mem : s.mem[(Word.toBitVec64 #v[Main[15]$, Main[16]$, Main[17]$, Main[18]$] + signExtend 64 op_c).toNat]? = some (BitVec.truncate 8 (BitVec.ofNat 16 ↑Main[32]$ >>> 8))
          := by
            simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
            rw [←h_op_c_is_signExtend, ←h_addr_add_spec]
            clear * - h_addr_limb0_ge7 h_addr_limb0_ge4 h_addr_limb0_sub4_ge2 h_addr_limb0_sub4_sub2_ge1 h_read_limb0 h_read_limb1 h_read_limb2 h_read_limb3
            simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
            rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
            simp [BitVec.ofNatLT_toNat]
            simp [Fin.sub_val_of_le h_addr_limb0_sub4_sub2_ge1, Fin.sub_val_of_le h_addr_limb0_sub4_ge2, Fin.sub_val_of_le h_addr_limb0_ge4] at *
            convert_to Main[25]$.val ≥ 7 at h_addr_limb0_ge7
            grind
      )
    ]

    <;> simp only [
          ←BitVec.ofNatLT_eq_ofNat h_limb0_is_u16,
          ←BitVec.ofNatLT_eq_ofNat h_limb1_is_u16,
          ←BitVec.ofNatLT_eq_ofNat h_limb2_is_u16,
          ←BitVec.ofNatLT_eq_ofNat h_limb3_is_u16
        ] at h_read_mem

    <;> simp [-BitVec.toNat_add, spec_lb, execute_LOAD, Sail.readReg, PreSail.readReg, h_read_pc, Sail.assert, PreSail.assert,
           LeanRV64IM.Functions.xlen_bytes, vmem_read, ext_data_get_addr, op_b, sp1_op_b, Sail.writeReg,
           PreSail.writeReg, Sail.rX_bits_eq_get_reg?_no_run, h_read_op_b, Option.elim, Option.toSailM,
           is_aligned_vaddr, check_misaligned, LeanRV64IM.Functions.plat_enable_misaligned_access, LeanRV64IM.Functions.not,
           split_misaligned, bits_of_virtaddr, untilFuelM, untilFuelM.go, Sail.assert, PreSail.assert,
           translateAddr, Std.ExtDHashMap.get?_insert, h_mstatus, h_priv, effectivePrivilege, _get_Mstatus_MPRV,
           Sail.BitVec.extractLsb, translationMode, mem_read, Sail.readReg, PreSail.readReg, Sail.BitVec.extractLsb,
           translationMode, mem_read_priv, mem_read_priv_meta, checked_mem_read, phys_access_check, bits_of_virtaddr,
           LeanRV64IM.Functions.sys_pmp_count, within_mmio_readable, get_config_rvfi, Sail.BitVec.addInt, zero_extend,
           Sail.BitVec.zeroExtend, within_phys_mem, ext_check_phys_mem_read, phys_mem_read, read_kind_of_flags,
           read_ram, Sail.sail_mem_read, PreSail.sail_mem_read, PreSail.readBytes, PreSail.readByte, h_read_mem,
           MemoryOpResult_drop_meta, h_op_a_not_x0, misaligned_order,
           sys_misaligned_order_decreasing, extend_value, sign_extend, Sail.BitVec.signExtend, sp1_lb, op_a, sp1_op_a,
           Sail.run_write_reg_no_run, h_op_a_not_x0]

    <;> [
      (have h_correct_limb : Main[41]$ = Main[29]$ := by clear * - chip_cstrs; simp_all only [chip_cstrs]);
      (have h_correct_limb : Main[41]$ = Main[31]$ := by clear * - chip_cstrs; simp_all only [chip_cstrs]);
      (have h_correct_limb : Main[41]$ = Main[30]$ := by clear * - chip_cstrs; simp_all only [chip_cstrs]);
      (have h_correct_limb : Main[41]$ = Main[32]$ := by clear * - chip_cstrs; simp_all only [chip_cstrs]);
      (have h_correct_limb : Main[41]$ = Main[29]$ := by clear * - chip_cstrs; simp_all only [chip_cstrs]);
      (have h_correct_limb : Main[41]$ = Main[31]$ := by clear * - chip_cstrs; simp_all only [chip_cstrs]);
      (have h_correct_limb : Main[41]$ = Main[30]$ := by clear * - chip_cstrs; simp_all only [chip_cstrs]);
      (have h_correct_limb : Main[41]$ = Main[32]$ := by clear * - chip_cstrs; simp_all only [chip_cstrs])
    ]

    any_goals
      -- nextPC write
      simp [Word.toBitVec64, Word.toNat]
      rw [←BitVec.ofNatLT_eq_ofNat h_pc_is_u64]
      simp [BitVec.add_def]
      have : (↑(Main[3]$ + 4) + ↑Main[4]$ <<< 16 + ↑Main[5]$ <<< 32 : ℕ) = ↑Main[3]$ + ↑Main[4]$ <<< 16 + ↑Main[5]$ <<< 32 + 4 := by
        simp [Fin.add_def]
        rw [Nat.mod_eq_of_lt (by clear * - h_pc0; linarith)]
        ring_nf
      rw [this]
      clear this
      simp [op_a]

      apply congrArg
      apply congrArg

    -- TODO(gzgz): needs another proof on: byte1 = selected_limb >>> 8 from below
    -- ```rust
    -- let byte0 = local.selected_limb_low_byte;
    -- let byte1 = (local.selected_limb - byte0) * AB::F::from_canonical_u32(1 << 8).inverse();
    -- builder.slice_range_check_u8(&[byte0.into(), byte1.clone()], is_real.clone());
    -- ```
    -- 
    -- only bitvec goals remaining
    all_goals
      sorry

end LB


namespace LBU

variable
  (Main : Vector (Fin BB) 47)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_lbu : Main[46] = 1)

private theorem is_lbu_eq_not_lb
  (cstrs : (constraints Main).allHold)
  (h_is_lbu : Main[46] = 1)
  -- (h_is_real : Main[28] + Main[29] + Main[30] + Main[31] + Main[32] + Main[33] = 1)
  : Main[45] = 0 := by
  simp [constraints, SP1ConstraintList.allHold, List.Forall, AddressOperation.constraints, h_is_lbu, sub_eq_zero] at cstrs
  have h_is_lbu_is_bool : Main[45] = 0 ∨ Main[45] = 1 := by simp_all only
  cases h_is_lbu_is_bool
  · assumption
  rename_i h_is_lbu
  simp [h_is_lbu] at cstrs

def spec_lbu (imm : BitVec 12) (rs2 rs1 : regidx) : SailM ExecutionResult :=
  do
    Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
    execute_LOAD imm rs2 rs1 true 1

def sp1_op_a : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[6] ?_
    show Main[6] < 32

    have h_not_lb : Main[45] = 0 := is_lbu_eq_not_lb Main cstrs h_is_lbu
    simp [constraints, AddressOperation.constraints, AddrAddOperation.constraints, CPUState.constraints, ITypeReader.constraints, SP1Constraint.toProp, List.Forall, h_is_lbu, h_not_lb] at cstrs
    simp_all only

def sp1_op_b : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[14] ?_
    show Main[14] < 32

    have h_not_lb : Main[45] = 0 := is_lbu_eq_not_lb Main cstrs h_is_lbu
    simp [constraints, AddressOperation.constraints, AddrAddOperation.constraints, CPUState.constraints, ITypeReader.constraints, SP1Constraint.toProp, List.Forall, h_is_lbu, h_not_lb, Opcode.ofNat, Nat.ble, Nat.beq] at cstrs
    simp_all only

def sp1_imm : BitVec 12 := BitVec.ofNat 12 Main[21].val

def sp1_lbu : SailM ExecutionResult :=
  do
    let op_a := sp1_op_a Main cstrs h_is_lbu
    let E71 : Fin BB := 65280 * Main[44]
    let E72 : Fin BB := Main[43] + E71
    let E73 : Fin BB := 65535 * Main[44]
    let E74 : Fin BB := 65535 * Main[44]
    let E75 : Fin BB := 65535 * Main[44]
    Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
    Sail.write_reg op_a (Word.toBitVec64 #v[E72, E73, E74, E75])
    pure RETIRE_SUCCESS

set_option maxHeartbeats 4000000 in
set_option pp.proofs false in
set_option diagnostics false in
theorem correct
  (Main : Vector (Fin BB) 47)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (state_cstrs : (constraints Main).initialState s)
  (h_is_lbu : Main[46] = 1)
  (h_mstatus : s.regs.get? Register.mstatus = some 0)
  (h_priv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
  (mem0 mem1 mem2 mem3 : BitVec 8)
  -- assumptions!
  : let op_a := sp1_op_a Main cstrs h_is_lbu
    let op_b := sp1_op_b Main cstrs h_is_lbu
    let op_c := sp1_imm Main
    (spec_lbu op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_lbu Main cstrs h_is_lbu).run s
  := by
    extract_lets op_a op_b op_c
    have h_not_lb : Main[45] = 0 := is_lbu_eq_not_lb Main cstrs h_is_lbu

    simp [-Word.add_toBitVec64_mod4, constraints, AddressOperation.constraints, AddrAddOperation.constraints, CPUState.constraints, ITypeReader.constraints, SP1Constraint.toStateProp, List.Forall, h_is_lbu, h_not_lb, Opcode.ofNat, ByteOpcode.ofNat, Nat.beq, Nat.ble] at state_cstrs
    obtain ⟨h_read_pc, h_read_addr_within_range, h_read_op_a, h_read_op_b, h_read_mem⟩ := state_cstrs

    simp [constraints, AddressOperation.constraints, SP1Constraint.toProp, List.Forall, h_is_lbu, h_not_lb, Opcode.ofNat, ByteOpcode.ofNat, Nat.beq, Nat.ble, sub_eq_zero] at cstrs
    obtain ⟨addr_add_cstrs, h_addr_shift0, h_addr_shift1, h_addr_shift2, addr_cstr0, addr_cstr1, cpu_cstrs, reader_cstrs, chip_cstrs⟩ := cstrs

    simp [ITypeReader.constraints, SP1Constraint.toProp, List.Forall, Opcode.ofNat, ByteOpcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs

    have h_op_a_is_reg : Main[6]$ < 32 := by simp_all only
    simp [h_op_a_is_reg] at h_read_op_a
    have h_op_b_is_reg : Main[14]$ < 32 := by simp_all only
    simp [h_op_b_is_reg] at h_read_op_b
    -- simp [-Word.add_toBitVec64_mod4, ←BitVec.ofNatLT_eq_ofNat (w := 5) (n := Main[14].val) h_op_b_is_reg, h_read_op_b] at h_trusted_read
    rw [←BitVec.ofNatLT_eq_ofNat h_op_b_is_reg, h_read_op_b, Option.get!_some] at h_read_addr_within_range

    have h_mem_read_is_u64 : Word.isU64 #v[Main[29]$, Main[30]$, Main[31]$, Main[32]$] := by simp_all only [chip_cstrs]

    have h_over_addr : Main[26]$ ≠ 0 ∨ Main[27]$ ≠ 0 :=
      by
        by_contra!
        obtain ⟨h_limb1_0, h_limb2_0⟩ := this
        simp [h_limb1_0, h_limb2_0] at addr_cstr0
    simp [not_and_or.mpr h_over_addr, Word.toNat] at h_read_mem
    obtain ⟨h_read_limb0, h_read_limb1, h_read_limb2, h_read_limb3⟩ := h_read_mem

    have h_op_c_is_signExtend : Word.toBitVec64 #v[Main[21]$, Main[22]$, Main[23]$, Main[24]$] = BitVec.signExtend 64 (BitVec.ofNat 12 Main[21]$.val) := by
      simp [constraints, AddressOperation.constraints, AddrAddOperation.constraints, CPUState.constraints, ITypeReader.constraints, SP1Constraint.toProp, List.Forall, h_is_lbu, h_not_lb, Opcode.ofNat, ByteOpcode.ofNat, Nat.beq, Nat.ble] at cstrs
      simp_all only

    have h_op_a_not_x0 : op_a ≠ 0#5 := by
      simp [op_a, sp1_op_a, BitVec.ofNatLT, BitVec.ofNat]
      have h_imm_c_is_0 : Main[13]$ = 0 := by simp_all only [chip_cstrs]
      have h_imm_c_iff_op_a_x0 : Main[13]$ = 1 ↔ Main[6]$ = 0 := by
        simp_all only [reader_cstrs]
      rw [Fin.mk_eq_mk]
      simp
      clear * - h_imm_c_is_0 h_imm_c_iff_op_a_x0
      aesop

    simp [op_a, sp1_op_a] at h_op_a_not_x0
    have h_pc0 : Main[3]$.val < 65536 := by clear * - reader_cstrs; show Main[3] < 65536; simp_all only
    have h_pc1 : Main[4]$.val < 65536 := by clear * - reader_cstrs; show Main[4] < 65536; simp_all only
    have h_pc2 : Main[5]$.val < 65536 := by clear * - reader_cstrs; show Main[5] < 65536; simp_all only
    have h_pc_is_u64 : Main[3]$.val + Main[4]$.val <<< 16 + Main[5]$.val <<< 32 < 2^64 := by
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
      (by exact h_read_addr_within_range) -- TODO(gzgz): not exceeding memory bounds, this should come from AddrAdd but we trust this too
    simp at h_add_addr_limb0 h_add_addr_limb1 h_add_addr_limb2 h_addr_add_spec

    have h_limb0_is_u16 : Main[29]$.val < 2^16 := h_mem_read_is_u64 0
    have h_limb1_is_u16 : Main[30]$.val < 2^16 := h_mem_read_is_u64 1
    have h_limb2_is_u16 : Main[31]$.val < 2^16 := h_mem_read_is_u64 2
    have h_limb3_is_u16 : Main[32]$.val < 2^16 := h_mem_read_is_u64 3

    cases h_addr_shift0
    <;> rename_i h_shift0
    <;> cases h_addr_shift1
    <;> rename_i h_shift1
    <;> cases h_addr_shift2
    <;> rename_i h_shift2
    <;> simp [h_shift0, h_shift1, h_shift2] at chip_cstrs h_read_limb0 h_read_limb1 h_read_limb2 h_read_limb3 addr_cstr1

    <;> [
      -- case offset 0
      ( skip
        obtain h_read_mem : s.mem[(Word.toBitVec64 #v[Main[15]$, Main[16]$, Main[17]$, Main[18]$] + signExtend 64 op_c).toNat]? = some (setWidth 8 (BitVec.ofNat 16 ↑Main[29]$)) :=
          by
            simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
            rw [←h_op_c_is_signExtend, ←h_addr_add_spec]
            clear * - h_read_limb0 h_read_limb1 h_read_limb2 h_read_limb3
            simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
            rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
            simp [BitVec.ofNatLT_toNat]
            grind
      );

      -- case offset 4
      ( skip
        let h_addr_limb0_ge4 : Main[25]$ >= 4 :=
          by
            clear * - addr_cstr1
            by_contra!
            convert_to Main[25].val < 4 at this
            simp [Fin.lt_def, Fin.mul_def, Fin.sub_def] at addr_cstr1
            interval_cases Main[25].val
            <;> simp at addr_cstr1

        obtain h_read_mem : s.mem[(Word.toBitVec64 #v[Main[15]$, Main[16]$, Main[17]$, Main[18]$] + signExtend 64 op_c).toNat]? = some (setWidth 8 (BitVec.ofNat 16 ↑Main[31]$)) :=
          by
            simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
            rw [←h_op_c_is_signExtend, ←h_addr_add_spec]
            clear * - h_addr_limb0_ge4 h_read_limb0 h_read_limb1 h_read_limb2 h_read_limb3
            simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
            rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
            simp [BitVec.ofNatLT_toNat]
            simp [Fin.sub_val_of_le h_addr_limb0_ge4] at *
            convert_to Main[25]$.val ≥ 4 at h_addr_limb0_ge4
            grind
      );

      -- case offset 2
      ( skip
        let h_addr_limb0_ge2 : Main[25]$ >= 2 :=
          by
            clear * - addr_cstr1
            by_contra!
            convert_to Main[25].val < 2 at this
            simp [Fin.lt_def, Fin.mul_def, Fin.sub_def] at addr_cstr1
            interval_cases Main[25].val
            <;> simp at addr_cstr1

        obtain h_read_mem : s.mem[(Word.toBitVec64 #v[Main[15]$, Main[16]$, Main[17]$, Main[18]$] + signExtend 64 op_c).toNat]? = some (setWidth 8 (BitVec.ofNat 16 ↑Main[30]$)) :=
          by
            simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
            rw [←h_op_c_is_signExtend, ←h_addr_add_spec]
            clear * - h_addr_limb0_ge2 h_read_limb0 h_read_limb1 h_read_limb2 h_read_limb3
            simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
            rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
            simp [BitVec.ofNatLT_toNat]
            simp [Fin.sub_val_of_le h_addr_limb0_ge2] at *
            convert_to Main[25]$.val ≥ 2 at h_addr_limb0_ge2
            grind
      );

      -- case offset 6
      ( skip
        let h_addr_limb0_ge6 : Main[25]$ >= 6 :=
          by
            clear * - addr_cstr1
            by_contra!
            convert_to Main[25].val < 6 at this
            simp [Fin.lt_def, Fin.mul_def, Fin.sub_def] at addr_cstr1
            interval_cases Main[25].val
            <;> simp at addr_cstr1

        let h_addr_limb0_sub4_ge2 : Main[25]$ - 4 >= 2 :=
          by
            clear * - h_addr_limb0_ge6
            simp at h_addr_limb0_ge6 ⊢ 
            all_goals omega

        let h_addr_limb0_ge4 : Main[25]$ >= 4 :=
          by
            clear * - h_addr_limb0_ge6
            simp at h_addr_limb0_ge6 ⊢ 
            all_goals omega

        obtain h_read_mem : s.mem[(Word.toBitVec64 #v[Main[15]$, Main[16]$, Main[17]$, Main[18]$] + signExtend 64 op_c).toNat]? = some (BitVec.truncate 8 (BitVec.ofNat 16 ↑Main[32]$))
          := by
            simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
            rw [←h_op_c_is_signExtend, ←h_addr_add_spec]
            clear * - h_addr_limb0_ge6 h_addr_limb0_ge4 h_addr_limb0_sub4_ge2 h_read_limb0 h_read_limb1 h_read_limb2 h_read_limb3
            simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
            rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
            simp [BitVec.ofNatLT_toNat]
            simp [Fin.sub_val_of_le h_addr_limb0_sub4_ge2, Fin.sub_val_of_le h_addr_limb0_ge4] at *
            convert_to Main[25]$.val ≥ 6 at h_addr_limb0_ge6
            convert_to Main[25]$.val ≥ 4 at h_addr_limb0_ge4
            grind
      );

      -- case offset 1
      ( skip
        let h_addr_limb0_ge1 : Main[25]$ >= 1 :=
          by
            clear * - addr_cstr1
            by_contra!
            convert_to Main[25].val < 1 at this
            simp [Fin.lt_def, Fin.mul_def, Fin.sub_def] at addr_cstr1
            interval_cases Main[25].val
            simp at addr_cstr1

        obtain h_read_mem : s.mem[(Word.toBitVec64 #v[Main[15]$, Main[16]$, Main[17]$, Main[18]$] + signExtend 64 op_c).toNat]? = some (setWidth 8 (BitVec.ofNat 16 ↑Main[29]$ >>> 8)) :=
          by
            simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
            rw [←h_op_c_is_signExtend, ←h_addr_add_spec]
            clear * - h_addr_limb0_ge1 h_read_limb0 h_read_limb1 h_read_limb2 h_read_limb3
            simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
            rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
            simp [BitVec.ofNatLT_toNat]
            simp [Fin.sub_val_of_le h_addr_limb0_ge1] at *
            convert_to Main[25]$.val ≥ 1 at h_addr_limb0_ge1
            grind
      );

      -- case offset 5
      ( skip
        let h_addr_limb0_ge5 : Main[25]$ >= 5 :=
          by
            clear * - addr_cstr1
            by_contra!
            convert_to Main[25].val < 5 at this
            simp [Fin.lt_def, Fin.mul_def, Fin.sub_def] at addr_cstr1
            interval_cases Main[25].val
            <;> simp at addr_cstr1

        let h_addr_limb0_sub4_ge1 : Main[25]$ - 4 >= 1 :=
          by
            clear * - h_addr_limb0_ge5
            simp at h_addr_limb0_ge5 ⊢ 
            all_goals omega

        let h_addr_limb0_ge4 : Main[25]$ >= 4 :=
          by
            clear * - h_addr_limb0_ge5
            simp at h_addr_limb0_ge5 ⊢ 
            all_goals omega

        obtain h_read_mem : s.mem[(Word.toBitVec64 #v[Main[15]$, Main[16]$, Main[17]$, Main[18]$] + signExtend 64 op_c).toNat]? = some (BitVec.truncate 8 (BitVec.ofNat 16 ↑Main[31]$ >>> 8))
          := by
            simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
            rw [←h_op_c_is_signExtend, ←h_addr_add_spec]
            clear * - h_addr_limb0_ge5 h_addr_limb0_ge4 h_addr_limb0_sub4_ge1 h_read_limb0 h_read_limb1 h_read_limb2 h_read_limb3
            simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
            rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
            simp [BitVec.ofNatLT_toNat]
            simp [Fin.sub_val_of_le h_addr_limb0_sub4_ge1, Fin.sub_val_of_le h_addr_limb0_ge4] at *
            convert_to Main[25]$.val ≥ 5 at h_addr_limb0_ge5
            convert_to Main[25]$.val ≥ 4 at h_addr_limb0_ge4
            grind
      );

      -- case offset 3
      ( skip
        let h_addr_limb0_ge3 : Main[25]$ >= 3 :=
          by
            clear * - addr_cstr1
            by_contra!
            convert_to Main[25].val < 3 at this
            simp [Fin.lt_def, Fin.mul_def, Fin.sub_def] at addr_cstr1
            interval_cases Main[25].val
            <;> simp at addr_cstr1

        let h_addr_limb0_sub2_ge1 : Main[25]$ - 2 >= 1 :=
          by
            clear * - h_addr_limb0_ge3
            simp at h_addr_limb0_ge3 ⊢ 
            all_goals omega

        let h_addr_limb0_ge2 : Main[25]$ >= 2 :=
          by
            clear * - h_addr_limb0_ge3
            simp at h_addr_limb0_ge3 ⊢ 
            all_goals omega

        obtain h_read_mem : s.mem[(Word.toBitVec64 #v[Main[15]$, Main[16]$, Main[17]$, Main[18]$] + signExtend 64 op_c).toNat]? = some (BitVec.truncate 8 (BitVec.ofNat 16 ↑Main[30]$ >>> 8))
          := by
            simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
            rw [←h_op_c_is_signExtend, ←h_addr_add_spec]
            clear * - h_addr_limb0_ge3 h_addr_limb0_ge2 h_addr_limb0_sub2_ge1 h_read_limb0 h_read_limb1 h_read_limb2 h_read_limb3
            simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
            rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
            simp [BitVec.ofNatLT_toNat]
            simp [Fin.sub_val_of_le h_addr_limb0_sub2_ge1, Fin.sub_val_of_le h_addr_limb0_ge2] at *
            convert_to Main[25]$.val ≥ 3 at h_addr_limb0_ge3
            convert_to Main[25]$.val ≥ 2 at h_addr_limb0_ge2
            grind
      );

      ( skip
        let h_addr_limb0_ge7 : Main[25]$ >= 7 :=
          by
            clear * - addr_cstr1
            by_contra!
            convert_to Main[25].val < 7 at this
            simp [Fin.lt_def, Fin.mul_def, Fin.sub_def] at addr_cstr1
            interval_cases Main[25].val
            <;> simp at addr_cstr1

        let h_addr_limb0_sub4_sub2_ge1 : Main[25]$ - 4 - 2 >= 1 :=
          by
            clear * - h_addr_limb0_ge7
            simp at h_addr_limb0_ge7 ⊢ 
            all_goals omega

        let h_addr_limb0_sub4_ge2 : Main[25]$ - 4 >= 2 :=
          by
            clear * - h_addr_limb0_ge7
            simp at h_addr_limb0_ge7 ⊢ 
            all_goals omega

        let h_addr_limb0_ge4 : Main[25]$ >= 4 :=
          by
            clear * - h_addr_limb0_ge7
            simp at h_addr_limb0_ge7 ⊢ 
            all_goals omega
        
        obtain h_read_mem : s.mem[(Word.toBitVec64 #v[Main[15]$, Main[16]$, Main[17]$, Main[18]$] + signExtend 64 op_c).toNat]? = some (BitVec.truncate 8 (BitVec.ofNat 16 ↑Main[32]$ >>> 8))
          := by
            simp only [op_c, sp1_imm, sign_extend, Sail.BitVec.signExtend]
            rw [←h_op_c_is_signExtend, ←h_addr_add_spec]
            clear * - h_addr_limb0_ge7 h_addr_limb0_ge4 h_addr_limb0_sub4_ge2 h_addr_limb0_sub4_sub2_ge1 h_read_limb0 h_read_limb1 h_read_limb2 h_read_limb3
            simp [-BitVec.toNat_ofNat, Word.toBitVec64, Word.toNat]
            rw [←BitVec.ofNatLT_eq_ofNat (by omega)]
            simp [BitVec.ofNatLT_toNat]
            simp [Fin.sub_val_of_le h_addr_limb0_sub4_sub2_ge1, Fin.sub_val_of_le h_addr_limb0_sub4_ge2, Fin.sub_val_of_le h_addr_limb0_ge4] at *
            convert_to Main[25]$.val ≥ 7 at h_addr_limb0_ge7
            grind
      )
    ]

    <;> simp only [
          ←BitVec.ofNatLT_eq_ofNat h_limb0_is_u16,
          ←BitVec.ofNatLT_eq_ofNat h_limb1_is_u16,
          ←BitVec.ofNatLT_eq_ofNat h_limb2_is_u16,
          ←BitVec.ofNatLT_eq_ofNat h_limb3_is_u16
        ] at h_read_mem

    <;> simp [-BitVec.toNat_add, spec_lbu, execute_LOAD, Sail.readReg, PreSail.readReg, h_read_pc, Sail.assert, PreSail.assert,
           LeanRV64IM.Functions.xlen_bytes, vmem_read, ext_data_get_addr, op_b, sp1_op_b, Sail.writeReg,
           PreSail.writeReg, Sail.rX_bits_eq_get_reg?_no_run, h_read_op_b, Option.elim, Option.toSailM,
           is_aligned_vaddr, check_misaligned, LeanRV64IM.Functions.plat_enable_misaligned_access, LeanRV64IM.Functions.not,
           split_misaligned, bits_of_virtaddr, untilFuelM, untilFuelM.go, Sail.assert, PreSail.assert,
           translateAddr, Std.ExtDHashMap.get?_insert, h_mstatus, h_priv, effectivePrivilege, _get_Mstatus_MPRV,
           Sail.BitVec.extractLsb, translationMode, mem_read, Sail.readReg, PreSail.readReg, Sail.BitVec.extractLsb,
           translationMode, mem_read_priv, mem_read_priv_meta, checked_mem_read, phys_access_check, bits_of_virtaddr,
           LeanRV64IM.Functions.sys_pmp_count, within_mmio_readable, get_config_rvfi, Sail.BitVec.addInt, zero_extend,
           Sail.BitVec.zeroExtend, within_phys_mem, ext_check_phys_mem_read, phys_mem_read, read_kind_of_flags,
           read_ram, Sail.sail_mem_read, PreSail.sail_mem_read, PreSail.readBytes, PreSail.readByte, h_read_mem,
           MemoryOpResult_drop_meta, h_op_a_not_x0, misaligned_order,
           sys_misaligned_order_decreasing, extend_value, sign_extend, Sail.BitVec.signExtend, sp1_lbu, op_a, sp1_op_a,
           Sail.run_write_reg_no_run, h_op_a_not_x0]

    <;> [
      (have h_correct_limb : Main[41]$ = Main[29]$ := by clear * - chip_cstrs; simp_all only [chip_cstrs]);
      (have h_correct_limb : Main[41]$ = Main[31]$ := by clear * - chip_cstrs; simp_all only [chip_cstrs]);
      (have h_correct_limb : Main[41]$ = Main[30]$ := by clear * - chip_cstrs; simp_all only [chip_cstrs]);
      (have h_correct_limb : Main[41]$ = Main[32]$ := by clear * - chip_cstrs; simp_all only [chip_cstrs]);
      (have h_correct_limb : Main[41]$ = Main[29]$ := by clear * - chip_cstrs; simp_all only [chip_cstrs]);
      (have h_correct_limb : Main[41]$ = Main[31]$ := by clear * - chip_cstrs; simp_all only [chip_cstrs]);
      (have h_correct_limb : Main[41]$ = Main[30]$ := by clear * - chip_cstrs; simp_all only [chip_cstrs]);
      (have h_correct_limb : Main[41]$ = Main[32]$ := by clear * - chip_cstrs; simp_all only [chip_cstrs])
    ]

    any_goals
      -- nextPC write
      simp [Word.toBitVec64, Word.toNat]
      rw [←BitVec.ofNatLT_eq_ofNat h_pc_is_u64]
      simp [BitVec.add_def]
      have : (↑(Main[3]$ + 4) + ↑Main[4]$ <<< 16 + ↑Main[5]$ <<< 32 : ℕ) = ↑Main[3]$ + ↑Main[4]$ <<< 16 + ↑Main[5]$ <<< 32 + 4 := by
        simp [Fin.add_def]
        rw [Nat.mod_eq_of_lt (by clear * - h_pc0; linarith)]
        ring_nf
      rw [this]
      clear this
      simp [op_a]

      apply congrArg
      apply congrArg

    -- TODO(gzgz): needs another proof on: byte1 = selected_limb >>> 8 from below
    -- ```rust
    -- let byte0 = local.selected_limb_low_byte;
    -- let byte1 = (local.selected_limb - byte0) * AB::F::from_canonical_u32(1 << 8).inverse();
    -- builder.slice_range_check_u8(&[byte0.into(), byte1.clone()], is_real.clone());
    -- ```
    -- 
    -- only bitvec goals remaining
    all_goals
      sorry

end LBU

end LoadByte

end Load
