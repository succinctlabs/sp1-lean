import SP1Foundations
import SP1Chips.Branch.Constraints
import LeanRV64IM.RiscvInstsEnd

set_option autoImplicit false

namespace Branch

open Sail SailState BitVec LeanRV64IM.Functions

variable
  (Main : Vector (Fin BB) 45)
  (cstrs : (constraints Main).allHold)
  (s : SailState)

private theorem helper {x : BitVec 64}
  : (fun _ => RETIRE_SUCCESS) <$> writeReg Register.nextPC x =
    (do
      writeReg Register.nextPC x
      pure RETIRE_SUCCESS)
  :=
  by
    simp [writeReg, PreSail.writeReg]

namespace BLTU

variable
  (h_is_bltu : Main[32]$ = 1)

private theorem h_Main32_is_bltu
  (cstrs : (constraints Main).allHold)
  (h_is_bltu : Main[32]$ = 1)
  : Main[28]$ = 0 ∧ Main[29]$ = 0 ∧ Main[30]$ = 0 ∧ Main[31]$ = 0 ∧ Main[33]$ = 0 := by
  simp [SP1ConstraintList.allHold, Branch.constraints] at cstrs
  obtain ⟨_, _, _, ⟨h_28, h_29, h_30, h_31, h_32, h_33, h_all_add, _⟩⟩ := cstrs
  clear * - h_is_bltu h_28 h_29 h_30 h_31 h_32 h_33 h_all_add
  rw [sub_eq_zero] at *
  split_ands
  <;> cases h_28 <;> rename_i h_28
  <;> cases h_29 <;> rename_i h_29
  <;> cases h_30 <;> rename_i h_30
  <;> cases h_31 <;> rename_i h_31
  <;> cases h_33 <;> rename_i h_33
  <;> rw [h_is_bltu, h_28, h_29, h_30, h_31, h_33] at h_all_add
  <;> trivial

-- TODO(gzgz): not being able to get away with `ExecutionResult`?
-- I guess that makes sense...
def spec_bltu (imm : (BitVec 13)) (rs2 : regidx) (rs1 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_BTYPE imm rs2 rs1 bop.BLTU

def sp1_op_a : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[6]$.val ?_
    show Main[6]$ < 32
    obtain ⟨h_28, h_29, h_30, h_31, h_33⟩ := h_Main32_is_bltu Main cstrs h_is_bltu
    simp [SP1ConstraintList.allHold, Branch.constraints] at cstrs
    obtain ⟨_, reader_cstrs, _, _⟩ := cstrs
    simp [SP1ConstraintList.allHold, ITypeReaderImmutable.constraints, SP1Constraint.toProp, h_is_bltu, h_28, h_29, h_30, h_31, h_33, Opcode.ofNat, Nat.beq, Nat.ble] at reader_cstrs
    simp_all only

def sp1_op_b : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[14]$.val ?_
    show Main[14]$ < 32
    obtain ⟨h_28, h_29, h_30, h_31, h_33⟩ := h_Main32_is_bltu Main cstrs h_is_bltu
    simp [SP1ConstraintList.allHold, Branch.constraints] at cstrs
    obtain ⟨_, reader_cstrs, _, _⟩ := cstrs
    simp [SP1ConstraintList.allHold, ITypeReaderImmutable.constraints, SP1Constraint.toProp, h_is_bltu, h_28, h_29, h_30, h_31, h_33, Opcode.ofNat, Nat.beq, Nat.ble] at reader_cstrs
    simp_all only

-- TODO(gzgz): check that I don't have to Main[21]$ <<< 1 first.
def sp1_imm : BitVec 13 := BitVec.ofNat 13 Main[21]$

def sp1_bltu : SailM ExecutionResult := do
  writeReg Register.nextPC (Word.toBitVec64 #v[Main[25]$, Main[26]$, Main[27]$, 0])
  pure RETIRE_SUCCESS

set_option maxHeartbeats 2000000 in
theorem correct_bltu
  (Main : Vector (Fin BB) 45)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (state_cstrs : (constraints Main).initialState s)
  (h_is_bltu : Main[32]$ = 1)
  (h_misa : Register.misa ∈ s.regs)
  : let imm := sp1_imm Main
    let op_b := sp1_op_b Main cstrs h_is_bltu
    let op_a := sp1_op_a Main cstrs h_is_bltu
  (spec_bltu imm (.Regidx op_b) (.Regidx op_a)).run s = (sp1_bltu Main).run s
  := by
    extract_lets
    rename_i imm op_b op_a

    obtain ⟨h_28, h_29, h_30, h_31, h_33⟩ := h_Main32_is_bltu Main cstrs h_is_bltu
    have h_is_real : Main[28]$ + Main[29]$ + Main[30]$ + Main[31]$ + Main[32]$ + Main[33]$ = 1 :=
      by
        aesop

    have h_opcode : (Main[28]$ * 27 + Main[29]$ * 28 + Main[30]$ * 29 + Main[31]$ * 30 + Main[32]$ * 31 + Main[33]$ * 32) = 31 :=
      by
        aesop

    simp [SP1ConstraintList.allHold, Branch.constraints] at cstrs
    obtain ⟨cpu_cstrs, reader_cstrs, lt_cstrs, chip_cstrs⟩ := cstrs
    clear cpu_cstrs
    simp [ITypeReaderImmutable.constraints, SP1Constraint.toProp, h_is_bltu, h_28, h_29, h_30, h_31, h_33, h_is_real, h_opcode, Opcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs

    let op_a_is_u64 : Word.isU64 #v[Main[7]$, Main[8]$, Main[9]$, Main[10]$] := by simp_all only
    let op_b_is_u64 : Word.isU64 #v[Main[15]$, Main[16]$, Main[17]$, Main[18]$] := by simp_all only
    let op_a_val := Word.toBitVec64 #v[Main[7]$, Main[8]$, Main[9]$, Main[10]$]
    let op_b_val := Word.toBitVec64 #v[Main[15]$, Main[16]$, Main[17]$, Main[18]$]
    have h_imm_0 : Main[21]$.val < 65536 := by show Main[21]$ < 65536; simp_all only
    have h_imm_1 : Main[22]$.val < 65536 := by show Main[22]$ < 65536; simp_all only
    have h_imm_2 : Main[23]$.val < 65536 := by show Main[23]$ < 65536; simp_all only
    have h_imm_3 : Main[24]$.val < 65536 := by show Main[24]$ < 65536; simp_all only
    -- have h_imm_is_u64 : Main[21]$.val + Main[22]$.val <<< 16 + ↑Main[23]$ <<< 32 + ↑Main[24]$  < 2^64 := by omega
    have op_c_is_u64 : Word.isU64 #v[Main[21]$, Main[22]$, Main[23]$, Main[24]$] :=
      by exact Word.isU64_of_cases _ h_imm_0 h_imm_1 h_imm_2 h_imm_3

    have spec_lt :=
      LtOperationSigned.spec.branch
        #v[Main[7]$, Main[8]$, Main[9]$, Main[10]$]
        #v[Main[15]$, Main[16]$, Main[17]$, Main[18]$]
        _
        _
        _
        lt_cstrs
        h_is_real
        op_a_is_u64
        op_b_is_u64
    simp [LtOperationSigned.spec.branch.def] at spec_lt
    clear lt_cstrs

    have h_op_a_is_reg : Main[6]$ < 32 := by simp_all only
    have h_op_b_is_reg : Main[14]$ < 32 := by simp_all only
    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, CPUState.constraints, ITypeReaderImmutable.constraints, LtOperationSigned.constraints, LtOperationUnsigned.constraints, U16MSBOperation.constraints, U16CompareOperation.constraints, h_is_real, h_is_bltu, h_28, h_29, h_30, h_31, h_33, Opcode.ofNat, Nat.ble, Nat.beq] at state_cstrs
    obtain ⟨h_pc_read, h_op_a_read, h_op_b_read⟩ := state_cstrs
    have h_op_a_read' := h_op_a_read h_op_a_is_reg
    have h_op_b_read' := h_op_b_read h_op_b_is_reg

    simp [spec_bltu, sp1_bltu, execute_BTYPE]
    simpM
    simp [Sail.readReg, PreSail.readReg]
    rw [h_pc_read]
    simp [EStateM.run]
    simpM

    simp [op_a, sp1_op_a]
    rw [h_op_a_read']
    simpM

    simp [op_b, sp1_op_b]
    rw [h_op_b_read']
    simpM
    simp [ext_control_check_pc]

    by_cases BitVec.ult op_a_val op_b_val
    ·
      rename_i h_ltu
      simp [zopz0zI_u]
      have h_neq : op_a_val ≠ op_b_val :=
        by
          have h_ult_prop : op_a_val < op_b_val := BitVec.ult_iff_lt.mp h_ltu
          clear * - h_ult_prop
          intro h
          rw [h] at h_ult_prop
          simp_all only [BitVec.lt_irrefl, op_b_val]
      simp [op_a_val, op_b_val, BitVec.ult] at h_ltu h_neq
      simp [h_ltu]
      simpM
      simp [h_neq, BitVec.ult, h_ltu, h_30, h_31] at spec_lt
      clear h_ltu
      simp [bit_to_bool, bits_of_virtaddr, bool_bit_backwards]
      rw [Std.ExtDHashMap.get?_insert]
      simp
      rw [h_pc_read]
      simp only [EStateM.pure]
      -- stop

      have h_trusted_signExtend :
        Word.toBitVec64 #v[Main[21]$, Main[22]$, Main[23]$, Main[24]$]
        = BitVec.signExtend 64 (BitVec.ofNat 13 Main[21]$)
        := by simp_all only

      -- have h_trusted_signExtend
      --   := reader_cstrs.1.1.2

      have h_ltuxt_pc_is_mul4 : (Word.toBitVec64 #v[Main[3]$, Main[4]$, Main[5]$, 0] + sign_extend imm) % 4 = 0 := by
        simp [Word.toBitVec64, Word.toNat]
        apply add_mod4_eq_zero_of_mod4_eq_zero
        · show _ % 4#64 = 0#64
          rw [BitVec.ofNat64_mod_4_eq_zero_iff]
          have h_pc0_nat_mul4 : Main[3]$.val % 4 = 0 :=
            by
              have : Main[3]$ % 4 = 0 := by simp_all only
              rw [Fin.mod_def, ← Fin.val_inj] at this
              exact this
          clear * - h_pc0_nat_mul4
          omega
        · simp [sign_extend, Sail.BitVec.signExtend, imm, sp1_imm]
          rw [←h_trusted_signExtend]
          simp [Word.toBitVec64, Word.toNat]
          have h_pc0_mul4 : Main[21]$.val % 4 = 0 := by simp_all only
          omega
      obtain ⟨h_ltuxt_pc_b0, h_ltuxt_pc_b1⟩ := mul4_means_0_1_are_0 h_ltuxt_pc_is_mul4
      simp [Sail.BitVec.access] at *
      rw [h_ltuxt_pc_b1]
      simpM

      have : ∀ v, ((fun _ => false) <$> readReg Register.misa).run
          {s with regs := s.regs.insert Register.nextPC v} =
          .ok false {s with regs := s.regs.insert Register.nextPC v} := by
        intro v
        rw [EStateM.run_map]
        rw [map_const_run_readReg]
        simp only [Std.ExtDHashMap.isSome_get?_eq_contains, Std.ExtDHashMap.contains_iff_mem,
          Std.ExtDHashMap.mem_insert, beq_iff_eq, reduceCtorEq, false_or]
        exact h_misa
      unfold EStateM.run at this
      simp [currentlyEnabled, hartSupports, this]
      clear this

      -- THIS IS SO CURSED! WHY DO I NEED THIS WRAPPER?!
      -- simp [writeReg, PreSail.writeReg]
      -- simpM
      -- rw [map_pure (fun a ↦ RETIRE_SUCCESS)]
      rw [helper]

      simpM
      simp [writeReg, PreSail.writeReg]
      simpM
      apply congrArg

      -- This should come from the spec of LtOperationSigned

      have h_is_neq : Main[36]$ + Main[37]$ + Main[38]$ + Main[39]$ = 1 :=
        by
          clear * - spec_lt
          aesop
      have h_is_lt : Main[35]$ = 1 := by clear * - spec_lt; simp_all only

      simp [h_is_bltu, h_neq, h_is_lt, h_is_neq, h_28, h_29, h_30, h_31, h_33, h_is_real, h_opcode, Opcode.ofNat, Nat.ble, Nat.beq] at chip_cstrs
      simp [sub_eq_zero] at chip_cstrs
      have h_is_branching : Main[34]$ = 1 := by simp_all only
      simp [h_is_branching] at chip_cstrs

      obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs

      have h_pc_0 : Main[3]$.val < 65536 := by show Main[3]$ < 65536; simp_all only
      have h_pc_1 : Main[4]$.val < 65536 := by show Main[4]$ < 65536; simp_all only
      have h_pc_2 : Main[5]$.val < 65536 := by show Main[5]$ < 65536; simp_all only

      have h_pc_is_u64 : Main[3]$.val + Main[4]$.val * 65536 + Main[5]$.val * 4294967296 < 2^64 := by omega
      -- rw [←BitVec.ofNatLT_eq_ofNat h_pc_is_u64]

      simp [Word.toBitVec64, Word.toNat]
      have h_ltuxtpc_is_u64 : Main[25]$.val + Main[26]$.val * 65536 + Main[27]$.val * 4294967296 < 2^64 := by omega
      -- rw [←BitVec.ofNatLT_eq_ofNat h_ltuxtpc_is_u64]

      have trusted_imm : Word.toBitVec64 #v[Main[21]$, Main[22]$, Main[23]$, Main[24]$] =
        BitVec.signExtend 64 (BitVec.ofNat 13 ↑Main[21]$) := by simp_all only
      simp [imm, sp1_imm, sign_extend, Sail.BitVec.signExtend]
      rw [←trusted_imm]

      -- simp [Word.toBitVec64, Word.toNat]
      -- rw [←BitVec.ofNatLT_eq_ofNat h_imm_is_u64]

      simp [BitVec.add_def]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      simp [Nat.shiftLeft_eq, Word.toBitVec64, Word.toNat]

      clear * - h_pc_0 h_pc_1 h_pc_2 h_imm_0 h_imm_1 h_imm_2 h_imm_3 h_limb0 h_limb1 h_limb2 h_limb3 h_bound_checks
      omega
      -- sorry
    rename_i h_geu
    by_cases op_a_val = op_b_val
    · rename_i h_eq
      simp [zopz0zI_u]
      simp only [op_a_val, op_b_val, BitVec.ult] at h_eq h_geu
      simp [h_geu]
      simpM
      apply congrArg

      simp [h_eq, BitVec.ult, h_geu, h_is_bltu, h_28, h_29, h_30, h_31, h_33, h_is_real, h_opcode, Opcode.ofNat, Nat.ble, Nat.beq] at chip_cstrs

      -- This should come from the spec of LtOperationSigned
      simp [h_eq, BitVec.ult, h_geu, h_30, h_31] at spec_lt
      have h_is_eq : (Main[36]$ + Main[37]$ + Main[38]$ + Main[39]$) = 0 :=
        by
          clear * - spec_lt
          aesop
      have h_is_ge : Main[35]$ = 0 := by clear * - spec_lt; simp_all only

      simp [h_is_eq, sub_eq_zero] at chip_cstrs
      have h_no_branching : Main[34]$ = 0 := by simp_all only
      simp [h_no_branching] at chip_cstrs

      obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs

      have h_pc_0 : Main[3]$.val < 65536 := by show Main[3]$ < 65536; clear * - reader_cstrs; simp_all only
      have h_pc_1 : Main[4]$.val < 65536 := by show Main[4]$ < 65536; clear * - reader_cstrs; simp_all only
      have h_pc_2 : Main[5]$.val < 65536 := by show Main[5]$ < 65536; clear * - reader_cstrs; simp_all only
      have h_pc_is_u64 : Main[3]$.val + Main[4]$.val * 65536 + Main[5]$.val * 4294967296 < 2^64 := by omega
      simp [BitVec.add_def]
      have h_pc_add4_is_u64 : Main[3]$.val + Main[4]$.val * 65536 + Main[5]$.val * 4294967296 + 4 < 2^64 := by omega
      simp [Word.toBitVec64, Word.toNat]
      have h_ltuxtpc_is_u64 : Main[25]$.val + Main[26]$.val * 65536 + Main[27]$.val * 4294967296 < 2^64 := by omega
      clear * - h_pc_0 h_pc_1 h_pc_2 h_bound_checks h_limb0 h_limb1 h_limb2 h_limb3
      simp [BitVec.ofNat, Nat.shiftLeft_eq]
      refine congr_arg _ ?_
      omega

    rename_i h_eq
    simp [zopz0zI_u]
    simp only [op_a_val, op_b_val, BitVec.ult] at h_eq h_geu
    simp [h_geu]
    simpM
    apply congrArg

    simp [h_eq, BitVec.ult, h_geu, h_is_bltu, h_28, h_29, h_30, h_31, h_33, h_is_real, h_opcode, Opcode.ofNat, Nat.ble, Nat.beq] at chip_cstrs

    -- This should come from the spec of LtOperationSigned
    simp [h_eq, BitVec.ult, h_geu, h_30, h_31] at spec_lt
    have h_is_neq : (Main[36]$ + Main[37]$ + Main[38]$ + Main[39]$) = 1 :=
      by
        clear * - spec_lt
        aesop
    have h_is_ge : Main[35]$ = 0 := by clear * - spec_lt; simp_all only

    simp [h_is_neq, sub_eq_zero] at chip_cstrs
    have h_no_branching : Main[34]$ = 0 := by simp_all only
    simp [h_no_branching] at chip_cstrs

    obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs

    have h_pc_0 : Main[3]$.val < 65536 := by show Main[3]$ < 65536; clear * - reader_cstrs; simp_all only
    have h_pc_1 : Main[4]$.val < 65536 := by show Main[4]$ < 65536; clear * - reader_cstrs; simp_all only
    have h_pc_2 : Main[5]$.val < 65536 := by show Main[5]$ < 65536; clear * - reader_cstrs; simp_all only
    have h_pc_is_u64 : Main[3]$.val + Main[4]$.val * 65536 + Main[5]$.val * 4294967296 < 2^64 := by omega
    simp [BitVec.add_def]
    have h_pc_add4_is_u64 : Main[3]$.val + Main[4]$.val * 65536 + Main[5]$.val * 4294967296 + 4 < 2^64 := by omega
    simp [Word.toBitVec64, Word.toNat]
    have h_ltuxtpc_is_u64 : Main[25]$.val + Main[26]$.val * 65536 + Main[27]$.val * 4294967296 < 2^64 := by omega
    clear * - h_pc_0 h_pc_1 h_pc_2 h_bound_checks h_limb0 h_limb1 h_limb2 h_limb3
    simp [BitVec.ofNat, Nat.shiftLeft_eq]
    refine congr_arg _ ?_

    omega

end BLTU

end Branch
