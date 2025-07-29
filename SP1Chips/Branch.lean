import SP1Foundations
import SP1Chips.Branch.Constraints
import LeanRV64IM.RiscvInstsEnd

set_option autoImplicit false

macro "simpM'" : tactic => `(tactic| simp [bind, StateT.bind, EStateM.bind, get, getThe, MonadStateOf.get, StateT.get, EStateM.get, pure, EStateM.pure, StateT.map, EStateM.map, modify, modifyGet, EStateM.modifyGet, StateT.modifyGet, MonadStateOf.modifyGet, EStateM.run])

namespace Branch

open Sail SailState BitVec LeanRV64IM.Functions

variable
  (Main : Vector (Fin BB) 45)
  (cstrs : (constraints Main).allHold)
  (s : SailState)
  -- (h_is_real : Main[28] + Main[29] + Main[30] + Main[31] + Main[32] + Main[33] = 1)

-- include Main cstrs s h_is_real

section beq

variable
  (h_is_beq : Main[28] = 1)

theorem helper {x : BitVec 64}
  : (fun _ => RETIRE_SUCCESS) <$> writeReg Register.nextPC x = 
    (do
      writeReg Register.nextPC x
      pure RETIRE_SUCCESS)
  :=
  by
    simp [writeReg, PreSail.writeReg]

theorem h_Main28_is_beq
  (cstrs : (constraints Main).allHold)
  (h_is_beq : Main[28] = 1)
  -- (h_is_real : Main[28] + Main[29] + Main[30] + Main[31] + Main[32] + Main[33] = 1)
  : Main[29] = 0 ∧ Main[30] = 0 ∧ Main[31] = 0 ∧ Main[32] = 0 ∧ Main[33] = 0 := by
  simp [SP1ConstraintList.allHold, Branch.constraints] at cstrs
  obtain ⟨_, _, _, ⟨h_28, h_29, h_30, h_31, h_32, h_33, _⟩⟩ := cstrs
  clear * - h_28 h_29 h_30 h_31 h_32 h_33
  stop
  split_ands
  · sorry
  all_goals sorry

-- TODO(gzgz): not being able to get away with `ExecutionResult`?
-- I guess that makes sense...
def spec_beq (imm : (BitVec 13)) (rs2 : regidx) (rs1 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_BTYPE imm rs2 rs1 bop.BEQ

def sp1_op_a : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[6].val ?_
    show Main[6] < 32
    obtain ⟨h_29, h_30, h_31, h_32, h_33⟩ := h_Main28_is_beq Main cstrs h_is_beq
    simp [SP1ConstraintList.allHold, Branch.constraints] at cstrs
    obtain ⟨_, reader_cstrs, _, _⟩ := cstrs
    simp [SP1ConstraintList.allHold, ITypeReaderImmutable.constraints, SP1Constraint.toProp, h_is_beq, h_29, h_30, h_31, h_32, h_33, Opcode.ofNat, Nat.beq, Nat.ble] at reader_cstrs
    -- extract_from_and reader_cstrs
    simp_all only

def sp1_op_b : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[14].val ?_
    show Main[14] < 32
    obtain ⟨h_29, h_30, h_31, h_32, h_33⟩ := h_Main28_is_beq Main cstrs h_is_beq
    simp [SP1ConstraintList.allHold, Branch.constraints] at cstrs
    obtain ⟨_, reader_cstrs, _, _⟩ := cstrs
    simp [SP1ConstraintList.allHold, ITypeReaderImmutable.constraints, SP1Constraint.toProp, h_is_beq, h_29, h_30, h_31, h_32, h_33, Opcode.ofNat, Nat.beq, Nat.ble] at reader_cstrs
    -- extract_from_and reader_cstrs
    simp_all only

-- TODO(gzgz): check that I don't have to Main[21] <<< 1 first.
def sp1_imm : BitVec 13 := BitVec.ofNat 13 Main[21]

def sp1_beq : SailM ExecutionResult := do
  writeReg Register.nextPC (Word.toBitVec64 #v[Main[25], Main[26], Main[27], 0])
  pure RETIRE_SUCCESS

set_option debug.skipKernelTC true in
set_option maxHeartbeats 2000000 in
theorem correct
  (Main : Vector (Fin BB) 45)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (state_cstrs : (constraints Main).initialState s)
  (h_is_beq : Main[28] = 1)
  (h_misa : s.regs.get? Register.misa = 0#64)
  : let imm := sp1_imm Main
    let op_b := sp1_op_b Main cstrs h_is_beq
    let op_a := sp1_op_a Main cstrs h_is_beq
  (spec_beq imm (.Regidx op_b) (.Regidx op_a)).run s = (sp1_beq Main).run s
  := by
    extract_lets
    rename_i imm op_b op_a

    obtain ⟨h_29, h_30, h_31, h_32, h_33⟩ := h_Main28_is_beq Main cstrs h_is_beq
    have h_is_real : Main[28] + Main[29] + Main[30] + Main[31] + Main[32] + Main[33] = 1 :=
      by
        aesop

    have h_opcode : (Main[28] * 27 + Main[29] * 28 + Main[30] * 29 + Main[31] * 30 + Main[32] * 31 + Main[33] * 32) = 27 :=
      by
        aesop

    simp [SP1ConstraintList.allHold, Branch.constraints] at cstrs
    obtain ⟨cpu_cstrs, reader_cstrs, lt_cstrs, chip_cstrs⟩ := cstrs
    clear cpu_cstrs lt_cstrs
    simp [ITypeReaderImmutable.constraints, SP1Constraint.toProp, h_is_beq, h_29, h_30, h_31, h_32, h_33, h_is_real, h_opcode, Opcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs

    let op_a_is_u64 : Word.isU64 #v[Main[7], Main[8], Main[9], Main[10]] := by simp_all only
    let op_b_is_u64 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := by simp_all only
    let op_a_val := Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]]
    let op_b_val := Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]
    have h_imm_0 : Main[21].val < 65536 := by show Main[21] < 65536; simp_all only
    have h_imm_1 : Main[22].val < 65536 := by show Main[22] < 65536; simp_all only
    have h_imm_2 : Main[23].val < 65536 := by show Main[23] < 65536; simp_all only
    have h_imm_3 : Main[24].val < 65536 := by show Main[24] < 65536; simp_all only
    have h_imm_is_u64 : Main[21].val + Main[22].val * 65536 + ↑Main[23] * 4294967296 + ↑Main[24] * 281474976710656 < 2^64 := by omega
    -- repeat (rw [Word.toBitVec64_LT_eq_toNat])

    have h_op_a_is_reg : Main[6] < 32 := by simp_all only
    have h_op_b_is_reg : Main[14] < 32 := by simp_all only
    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, CPUState.constraints, ITypeReaderImmutable.constraints, LtOperationSigned.constraints, LtOperationUnsigned.constraints, U16MSBOperation.constraints, U16CompareOperation.constraints, h_is_real, h_is_beq, h_29, h_30, h_31, h_32, h_33, Opcode.ofNat, Nat.ble, Nat.beq] at state_cstrs
    obtain ⟨h_pc_read, h_op_a_read, h_op_b_read⟩ := state_cstrs
    have h_op_a_read' := h_op_a_read h_op_a_is_reg
    have h_op_b_read' := h_op_b_read h_op_b_is_reg

    simp [spec_beq, sp1_beq, execute_BTYPE]
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

    by_cases h_eq : op_a_val = op_b_val <;> simp [op_a_val, op_b_val] at h_eq
    · simp [h_eq]
      simpM
      simp [bit_to_bool, bits_of_virtaddr, bool_bit_backwards]
      rw [Std.ExtDHashMap.get?_insert]
      simp
      rw [h_pc_read]
      simp only [EStateM.pure]
      -- conv =>
      --   lhs
      --   arg 2
      --   simp only
      --   rfl
      -- conv =>
      --   lhs
      --   arg 2
      --   simp [EStateM.pure]
      --   rfl
      -- -- deep kernel recursion????
      -- simp only

      have h_trusted_signExtend :
        Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]]
        = BitVec.signExtend 64 (BitVec.ofNat 13 Main[21])
        := by simp_all only

      have h_next_pc_is_mul4 : (BitVec.ofNat 64 (Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296) + sign_extend imm) % 4 = 0 := by
        apply add_mod4_eq_zero_of_mod4_eq_zero 
        · show _ % 4#64 = 0#64
          rw [BitVec.ofNat64_mod_4_eq_zero_iff]
          have h_pc0_nat_mul4 : Main[3].val % 4 = 0 :=
            by
              rw [←BitVec.Nat_mul4_eq_FinBB_mul4]
              simp_all only
          clear * - h_pc0_nat_mul4
          omega
        · simp [sign_extend, Sail.BitVec.signExtend, imm, sp1_imm]
          rw [←h_trusted_signExtend]
          simp [Word.toBitVec64, Word.toNat]
          have h_pc0_mul4 : Main[21].val % 4 = 0 := by simp_all only
          omega
      obtain ⟨h_next_pc_b0, h_next_pc_b1⟩ := mul4_means_0_1_are_0 h_next_pc_is_mul4
      simp [Sail.BitVec.access]
      rw [h_next_pc_b1]
      simpM

      -- simp [currentlyEnabled, hartSupports]
      -- have h_all_misa : readReg Register.misa = 0#64 := by sorry
      -- stop
      -- simpM'

      have h_no_zca : currentlyEnabled extension.Ext_Zca = pure false := by sorry
      rw [h_no_zca]
      simpM

      -- THIS IS SO CURSED! WHY DO I NEED THIS WRAPPER?!
      -- simp [writeReg, PreSail.writeReg]
      -- simpM'
      -- rw [map_pure (fun a ↦ RETIRE_SUCCESS)]
      rw [helper]

      simpM
      simp [writeReg, PreSail.writeReg]
      simpM
      apply congrArg

      -- This should come from the spec of LtOperationSigned
      have h_not_branching : Main[36] + Main[37] + Main[38] + Main[39] = 0 := by sorry

      simp [h_is_beq, h_29, h_30, h_31, h_32, h_33, h_is_real, h_opcode, Opcode.ofNat, Nat.ble, Nat.beq] at chip_cstrs
      rw [h_not_branching] at chip_cstrs
      simp [sub_eq_zero] at chip_cstrs
      have h_is_branching : Main[34] = 1 := by simp_all only
      simp [h_is_branching] at chip_cstrs

      obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs

      have h_pc_0 : Main[3].val < 65536 := by show Main[3] < 65536; simp_all only
      have h_pc_1 : Main[4].val < 65536 := by show Main[4] < 65536; simp_all only
      have h_pc_2 : Main[5].val < 65536 := by show Main[5] < 65536; simp_all only

      have h_pc_is_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 < 2^64 := by omega
      rw [←BitVec.ofNatLT_eq_ofNat h_pc_is_u64]
      -- simp [BitVec.add_def]
      -- have h_pc_add4_is_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 + 4 < 2^64 := by omega
      -- rw [←BitVec.ofNatLT_eq_ofNat h_pc_add4_is_u64]

      simp [Word.toBitVec64, Word.toNat]
      have h_nextpc_is_u64 : Main[25].val + Main[26].val * 65536 + Main[27].val * 4294967296 < 2^64 := by omega
      rw [←BitVec.ofNatLT_eq_ofNat h_nextpc_is_u64]

      have trusted_imm : Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] =
        BitVec.signExtend 64 (BitVec.ofNat 13 ↑Main[21]) := by simp_all only
      simp [imm, sp1_imm, sign_extend, Sail.BitVec.signExtend]
      rw [←trusted_imm]

      -- have h_imm_is_u64 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] :=
      --   by
      --     refine Word.isU64_of_cases #v[Main[21], Main[22], Main[23], Main[24]] ?_ ?_ ?_ ?_
      --     · exact h_imm_0
      --     · exact h_imm_1
      --     · exact h_imm_2
      --     · exact h_imm_3
      -- have h_imm_0 : Main[21].val < 65536 := by show Main[21] < 65536; simp_all only
      -- have h_imm_1 : Main[22].val < 65536 := by show Main[22] < 65536; simp_all only
      -- have h_imm_2 : Main[23].val < 65536 := by show Main[23] < 65536; simp_all only
      -- have h_imm_3 : Main[24].val < 65536 := by show Main[24] < 65536; simp_all only
      simp [Word.toBitVec64, Word.toNat]
      rw [←BitVec.ofNatLT_eq_ofNat h_imm_is_u64]

      simp [BitVec.add_def]

      have trusted_add :
        (Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296) + (Main[21].val + Main[22].val * 65536 + Main[23].val * 4294967296 + Main[24].val * 281474976710656) < 2^48 := by sorry
      have h_added_is_u64 : (Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296) + (Main[21].val + Main[22].val * 65536 + Main[23].val * 4294967296 + Main[24].val * 281474976710656) < 2^64 := by
        -- clear * - trusted_add
        simp_all
        omega

      rw [←BitVec.ofNatLT_eq_ofNat h_added_is_u64]
      simp [BitVec.ofNatLT]
      clear * - h_pc_0 h_pc_1 h_pc_2 h_imm_0 h_imm_1 h_imm_2 h_imm_3 trusted_add h_limb0 h_limb1 h_limb2 h_limb3 h_bound_checks

      omega
    · simp [not_beq_of_ne h_eq]
      simpM'
      apply congrArg

      simp [h_is_beq, h_29, h_30, h_31, h_32, h_33, h_is_real, h_opcode, Opcode.ofNat, Nat.ble, Nat.beq] at chip_cstrs
      -- repeat (rw [sub_eq_zero] at chip_cstrs)

      -- This should come from the spec of LtOperationSigned
      have h_not_branching : (1 : Fin BB) - (Main[36] + Main[37] + Main[38] + Main[39]) = 0 := by sorry
      rw [h_not_branching, sub_eq_zero, sub_eq_zero] at chip_cstrs
      have h_is_branching : Main[34] = 0 := by simp_all only
      simp [h_is_branching] at chip_cstrs

      obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs
      simp [sub_eq_zero] at h_limb0 h_limb1 h_limb2 h_limb3

      have h_pc_0 : Main[3].val < 65536 := by show Main[3] < 65536; simp_all only
      have h_pc_1 : Main[4].val < 65536 := by show Main[4] < 65536; simp_all only
      have h_pc_2 : Main[5].val < 65536 := by show Main[5] < 65536; simp_all only
      have h_pc_is_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 < 2^64 := by omega
      rw [←BitVec.ofNatLT_eq_ofNat h_pc_is_u64]
      simp [BitVec.add_def]
      have h_pc_add4_is_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 + 4 < 2^64 := by omega
      rw [←BitVec.ofNatLT_eq_ofNat h_pc_add4_is_u64]

      simp [Word.toBitVec64, Word.toNat]
      have h_nextpc_is_u64 : Main[25].val + Main[26].val * 65536 + Main[27].val * 4294967296 < 2^64 := by omega
      rw [←BitVec.ofNatLT_eq_ofNat h_nextpc_is_u64]

      simp [BitVec.ofNatLT]
      clear * - h_pc_0 h_pc_1 h_pc_2 h_bound_checks h_limb0 h_limb1 h_limb2 h_limb3

      omega

end beq

end Branch
