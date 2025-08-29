import SP1Foundations
import SP1Chips.Branch.Constraints
import LeanRV64D.RiscvInstsEnd

set_option autoImplicit false

/-
All the other branch instruction proofs essentially mirrors BEQ's approach.
Therefore, most of the comments in this file are preserved so that if something
breaks we might still recover by peaking at the history of how we arrived at the
original proof.
-/

namespace Branch

open Sail SailState BitVec LeanRV64D.Functions

namespace BEQ

variable
  (Main : Vector (Fin BB) 45)
  (cstrs : (constraints Main).allHold)
  (s : SailState)
  (h_is_beq : Main[28] = 1)

private theorem h_Main28_is_beq
  (cstrs : (constraints Main).allHold)
  (h_is_beq : Main[28] = 1)
  -- (h_is_real : Main[28] + Main[29] + Main[30] + Main[31] + Main[32] + Main[33] = 1)
  : Main[29] = 0 ∧ Main[30] = 0 ∧ Main[31] = 0 ∧ Main[32] = 0 ∧ Main[33] = 0 := by
  simp [SP1ConstraintList.allHold, Branch.constraints] at cstrs
  obtain ⟨_, _, _, ⟨h_28, h_29, h_30, h_31, h_32, h_33, h_all_add, _⟩⟩ := cstrs
  clear * - h_is_beq h_29 h_30 h_31 h_32 h_33 h_all_add
  rw [sub_eq_zero] at *
  split_ands
  <;> cases h_29 <;> rename_i h_29
  <;> cases h_30 <;> rename_i h_30
  <;> cases h_31 <;> rename_i h_31
  <;> cases h_32 <;> rename_i h_32
  <;> cases h_33 <;> rename_i h_33
  <;> rw [h_is_beq, h_29, h_30, h_31, h_32, h_33] at h_all_add
  <;> trivial

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
    simp_all only

def sp1_op_b : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[14].val ?_
    show Main[14] < 32
    obtain ⟨h_29, h_30, h_31, h_32, h_33⟩ := h_Main28_is_beq Main cstrs h_is_beq
    simp [SP1ConstraintList.allHold, Branch.constraints] at cstrs
    obtain ⟨_, reader_cstrs, _, _⟩ := cstrs
    simp [SP1ConstraintList.allHold, ITypeReaderImmutable.constraints, SP1Constraint.toProp, h_is_beq, h_29, h_30, h_31, h_32, h_33, Opcode.ofNat, Nat.beq, Nat.ble] at reader_cstrs
    simp_all only

def sp1_imm : BitVec 13 := BitVec.ofNat 13 Main[21]

def sp1_beq : SailM ExecutionResult := do
  writeReg Register.nextPC (Word.toBitVec64 #v[Main[25], Main[26], Main[27], 0])
  pure RETIRE_SUCCESS

set_option debug.skipKernelTC true in
set_option maxHeartbeats 2000000 in
theorem correct_beq
    (Main : Vector (Fin BB) 45)
    (s : SailState)
    (cstrs : (constraints Main).allHold)
    (state_cstrs : (constraints Main).initialState s)
    (h_is_beq : Main[28] = 1)
    (h_misa : Register.misa ∈ s.regs) :
    let imm := sp1_imm Main
    let op_b := sp1_op_b Main cstrs h_is_beq
    let op_a := sp1_op_a Main cstrs h_is_beq
    (spec_beq imm (.Regidx op_b) (.Regidx op_a)).run s = (sp1_beq Main).run s := by
  extract_lets imm op_b op_a
  obtain ⟨h_29, h_30, h_31, h_32, h_33⟩ := h_Main28_is_beq Main cstrs h_is_beq

  simp [SP1ConstraintList.allHold, Branch.constraints] at cstrs
  obtain ⟨_, reader_cstrs, lt_cstrs, chip_cstrs⟩ := cstrs

  -- simplify reader constraints
  simp [ITypeReaderImmutable.constraints, SP1Constraint.toProp,
    h_is_beq, h_29, h_30, h_31, h_32, h_33, Opcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs

  -- Introduce bounds on values
  have op_a_is_u64 : Word.isU64 #v[Main[7], Main[8], Main[9], Main[10]] := by simp_all only
  have op_b_is_u64 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := by simp_all only
  let op_a_val := Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]]
  let op_b_val := Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]
  have h_imm_0 : Main[21].val < 65536 := by show Main[21] < 65536; simp_all only
  have h_imm_1 : Main[22].val < 65536 := by show Main[22] < 65536; simp_all only
  have h_imm_2 : Main[23].val < 65536 := by show Main[23] < 65536; simp_all only
  have h_imm_3 : Main[24].val < 65536 := by show Main[24] < 65536; simp_all only
  have h_imm_is_u64 : Main[21].val + Main[22].val * 65536 + ↑Main[23] * 4294967296 + ↑Main[24] * 281474976710656 < 2^64 := by omega
  have op_c_is_u64 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := Word.isU64_of_cases h_imm_0 h_imm_1 h_imm_2 h_imm_3
  have h_pc_0 : Main[3].val < 65536 := by show Main[3] < 65536; aesop
  have h_pc_1 : Main[4].val < 65536 := by show Main[4] < 65536; aesop
  have h_pc_2 : Main[5].val < 65536 := by show Main[5] < 65536; aesop
  have h_pc_is_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 < 2^64 := by omega
  have h_pc_add4_is_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 + 4 < 2^64 := by omega
  have h_nextpc_is_u64 : Main[25].val + Main[26].val * 65536 + Main[27].val * 4294967296 < 2^64 := by omega

  -- construct alignment assumption
  have h_next_pc_is_mul4 : (BitVec.ofNat 64 (Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296) + sign_extend imm) % 4 = 0 := by
    have h_pc0_nat_mul4 : Main[3].val % 4 = 0 := by
      have : Main[3] % 4 = 0 := by aesop
      rwa [Fin.mod_def, ← Fin.val_inj] at this
    have h_trusted_signExtend : Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] =
      BitVec.signExtend 64 (BitVec.ofNat 13 Main[21]) := by aesop
    have h_pc0_mul4 : Main[21].val % 4 = 0 := by aesop
    apply add_mod4_eq_zero_of_mod4_eq_zero
    · show _ % 4#64 = 0#64
      rw [BitVec.ofNat64_mod_4_eq_zero_iff]
      clear * - h_pc0_nat_mul4
      omega
    · simp [sign_extend, Sail.BitVec.signExtend, imm, sp1_imm, ←h_trusted_signExtend,
        Word.toBitVec64, Word.toNat]
      omega
  obtain ⟨h_next_pc_b0, h_next_pc_b1⟩ := mul4_means_0_1_are_0 h_next_pc_is_mul4
  simp_all

  -- simplify lt operation constraints
  have spec_lt := LtOperationSigned.spec.branch op_a_is_u64 op_b_is_u64 lt_cstrs
  clear lt_cstrs
  simp [LtOperationSigned.spec.branch.def] at spec_lt

  -- simplify state constraints
  simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall,
    CPUState.constraints, ITypeReaderImmutable.constraints, LtOperationSigned.constraints,
    LtOperationUnsigned.constraints, U16MSBOperation.constraints, U16CompareOperation.constraints,
    h_is_beq, h_29, h_30, h_31, h_32, h_33, Opcode.ofNat, Nat.ble, Nat.beq] at state_cstrs
  obtain ⟨h_pc_read, h_op_a_read, h_op_b_read⟩ := state_cstrs
  specialize h_op_a_read (by simp_all only)
  specialize h_op_b_read (by simp_all only)

  -- simplify main goal
  simp [spec_beq, sp1_beq, execute_BTYPE]
  rw [run_readReg]

  simp [h_pc_read]
  simp [op_a, sp1_op_a, h_op_a_read]
  simp [op_b, sp1_op_b, h_op_b_read]

  by_cases h_eq : op_a_val = op_b_val <;> simp [op_a_val, op_b_val] at h_eq
  · have h_is_eq : Main[36] + Main[37] + Main[38] + Main[39] = 0 := by
      simp [h_eq, h_30, h_31] at spec_lt
      clear * - spec_lt
      aesop
    rw [h_is_eq] at chip_cstrs
    simp [sub_eq_zero] at chip_cstrs
    have h_is_branching : Main[34] = 1 := by aesop
    simp [h_is_branching] at chip_cstrs
    obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs

    simp [h_eq, h_pc_read]
    rw [run_readReg]
    simp [Std.ExtDHashMap.get?_insert, h_pc_read, h_next_pc_b1,
      jump_to, assert, PreSail.assert, ofBool, h_next_pc_b0]
    rw [run_readReg]
    simp [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_eq_some_get h_misa]

    refine congr_arg (s.regs.insert Register.nextPC) ?_

    rw [←BitVec.ofNatLT_eq_ofNat h_pc_is_u64]
    simp [Word.toBitVec64, Word.toNat]
    rw [←BitVec.ofNatLT_eq_ofNat h_nextpc_is_u64]

    have trusted_imm : Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] =
      BitVec.signExtend 64 (BitVec.ofNat 13 ↑Main[21]) := by aesop
    simp [imm, sp1_imm, sign_extend]
    rw [←trusted_imm]

    simp [Word.toBitVec64, Word.toNat]
    rw [←BitVec.ofNatLT_eq_ofNat h_imm_is_u64]
    simp [BitVec.add_def]

    apply BitVec.eq_of_toNat_eq

    simp [BitVec.toNat_ofNat, BitVec.toNat_ofNatLT]

    clear * - h_pc_0 h_pc_1 h_pc_2 h_imm_0 h_imm_1 h_imm_2 h_imm_3 h_limb0 h_limb1 h_limb2 h_limb3 h_bound_checks
    omega

  · have h_is_neq : (Main[36] + Main[37] + Main[38] + Main[39]) = 1 :=
      by
        simp [h_eq, h_30, h_31] at spec_lt
        clear * - spec_lt
        aesop
    rw [h_is_neq] at chip_cstrs
    simp [sub_eq_zero] at chip_cstrs
    have h_is_branching : Main[34] = 0 := by aesop
    simp [h_is_branching] at chip_cstrs

    simp [h_eq]

    refine congr_arg (s.regs.insert Register.nextPC) ?_

    obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs

    rw [←BitVec.ofNatLT_eq_ofNat h_pc_is_u64]

    simp [BitVec.add_def]

    rw [←BitVec.ofNatLT_eq_ofNat h_pc_add4_is_u64]

    simp [Word.toBitVec64, Word.toNat]

    rw [←BitVec.ofNatLT_eq_ofNat h_nextpc_is_u64]

    simp [BitVec.ofNatLT]

    clear * - h_pc_0 h_pc_1 h_pc_2 h_bound_checks h_limb0 h_limb1 h_limb2 h_limb3
    omega


end BEQ

end Branch
