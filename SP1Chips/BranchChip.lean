import SP1Foundations
import SP1Chips.Branch.Constraints

namespace Branch

open Sail SailState BitVec LeanRV64D.Functions

attribute [simp] jump_to assert PreSail.assert ofBool
  zopz0zI_s zopz0zKzJ_s zopz0zKzJ_u zopz0zI_u

-- Close the branching-case address equation `PC + signExtend imm = #v[Main[26..28], 0]`
-- by converting sign-extended immediate to its limb form (via `reader_cstrs`), pushing the
-- BitVec equality down to `Nat` arithmetic, and discharging with `omega` over the PC, immediate,
-- and chip-output limb bounds plus the `h_limb0..h_limb3, h_bound_checks` chip constraints.
-- The macro expects the ambient setup from each `correct_b*` proof: local `imm` let-binding,
-- `reader_cstrs`, `h_pc_0..h_pc_2`, `h_imm_0..h_imm_3`, `h_limb0..h_limb3`, `h_bound_checks`, `h26`.
set_option hygiene false in
local macro "close_branch_addr_eq" : tactic => `(tactic| (
  unfold imm
  rw [sp1_imm, ← reader_cstrs.1.1.1]
  simp [Word.toBitVec64, Word.toNat_def, ← BitVec.toNat_inj]
  clear * - h26 h_pc_0 h_pc_1 h_pc_2 h_imm_0 h_imm_1 h_imm_2 h_imm_3
    h_limb0 h_limb1 h_limb2 h_limb3 h_bound_checks
  omega))

variable (Main : Vector (Fin KB) 46)

def sp1_op_a : BitVec 5 := BitVec.ofNat 5 Main[6]

def sp1_op_b : BitVec 5 := BitVec.ofNat 5 Main[14]

def sp1_imm : BitVec 13 := BitVec.ofNat 13 Main[21]

def sp1_branch : SailM ExecutionResult := do
  writeReg Register.nextPC (Word.toBitVec64 #v[Main[26], Main[27], Main[28], 0])
  pure RETIRE_SUCCESS

namespace BEQ

noncomputable def spec_beq (imm : (BitVec 13)) (rs2 : regidx) (rs1 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_BTYPE imm rs2 rs1 bop.BEQ

set_option debug.skipKernelTC true in
set_option maxHeartbeats 2000000 in
-- correctness proof across all 6 branch-opcode cases
theorem correct_beq
    (Main : Vector (Fin KB) 46)
    (s : SailState) (hs : s.isInitialized)
    (h_is_beq : Main[29] = 1)
    (cstrs : (constraints Main).allHold)
    (state_cstrs : (constraints Main).initialState s) :
    let imm := sp1_imm Main
    let op_b := .Regidx (sp1_op_b Main)
    let op_a := .Regidx (sp1_op_a Main)
    (spec_beq imm op_b op_a).run s = (sp1_branch Main).run s := by
  extract_lets imm op_b op_a
  have h_is_real : is_real Main := by simp [is_real, h_is_beq]
  have h25 : Main[25] = 1 := is_trusted_of_constraints Main cstrs h_is_real
  have h_sign_extend := eq_signExtend_of_is_real Main cstrs h_is_real
  have h_next_pc_is_mul4 : (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] +
    BitVec.signExtend 64 imm) % 4 = 0 := add_signExtend_of_constraints Main cstrs h_is_real
  obtain ⟨h_next_pc_b0, h_next_pc_b1⟩ := mul4_means_0_1_are_0 h_next_pc_is_mul4
  obtain ⟨h_28, h_30, h_31, h_32, h_33⟩ := (single_op Main cstrs).1 h_is_beq
  simp [SP1ConstraintList.allHold, Branch.constraints] at cstrs
  obtain ⟨_, reader_cstrs, lt_cstrs, chip_cstrs⟩ := cstrs
  simp_all only [h25]
  -- simplify reader constraints
  simp [ITypeReaderImmutable.constraints, SP1Constraint.toProp,
    h_is_beq, h_28, h_30, h_31, h_32, h_33, Opcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs
  -- Introduce bounds on values
  have op_a_is_u64 : Word.isU64 #v[Main[7], Main[8], Main[9], Main[10]] := by simp_all only
  have op_b_is_u64 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := by simp_all only
  let op_a_val := Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]]
  let op_b_val := Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]
  have h6 : Main[6] < 32 := by aesop
  have h14 : Main[14] < 32 := by aesop
  have h_imm_0 : Main[21].val < 65536 := by change Main[21] < 65536; simp_all only
  have h_imm_1 : Main[22].val < 65536 := by change Main[22] < 65536; simp_all only
  have h_imm_2 : Main[23].val < 65536 := by change Main[23] < 65536; simp_all only
  have h_imm_3 : Main[24].val < 65536 := by change Main[24] < 65536; simp_all only
  have h_imm_is_u64 : Main[21].val + Main[22].val * 65536 + ↑Main[23] * 4294967296 + ↑Main[24] * 281474976710656 < 2^64 := by omega
  have op_c_is_u64 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := Word.isU64_of_cases h_imm_0 h_imm_1 h_imm_2 h_imm_3
  have h_pc_0 : Main[3].val < 65536 := by change Main[3] < 65536; aesop
  have h_pc_1 : Main[4].val < 65536 := by change Main[4] < 65536; aesop
  have h_pc_2 : Main[5].val < 65536 := by change Main[5] < 65536; aesop
  have h_pc_is_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 < 2^64 := by omega
  have h_pc_add4_is_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 + 4 < 2^64 := by omega
  have h_nextpc_is_u64 : Main[26].val + Main[27].val * 65536 + Main[28].val * 4294967296 < 2^64 := by omega
  simp_all
  -- simplify lt operation constraints
  have spec_lt := LtOperationSigned.spec.branch op_a_is_u64 op_b_is_u64 lt_cstrs
  clear lt_cstrs
  simp [LtOperationSigned.spec.branch.def] at spec_lt
  -- simplify state constraints
  simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall,
    CPUState.constraints, ITypeReaderImmutable.constraints, LtOperationSigned.constraints,
    LtOperationUnsigned.constraints, U16MSBOperation.constraints, U16CompareOperation.constraints,
    h_is_beq, h6, h14, h_28, h_30, h_31, h_32, h_33, Opcode.ofNat, Nat.ble, Nat.beq] at state_cstrs
  obtain ⟨h_pc_read, h_op_a_read, h_op_b_read⟩ := state_cstrs
  specialize h_op_a_read
  specialize h_op_b_read
  -- simplify main goal
  simp [spec_beq, sp1_branch, execute_BTYPE]
  rw [run_readReg]
  simp [h_pc_read]
  simp_all only [BitVec.ofNatLT_eq_ofNat]
  simp [op_a, sp1_op_a, h_op_a_read, op_b, sp1_op_b, h_op_b_read]
  by_cases h_eq : op_a_val = op_b_val <;> simp [op_a_val, op_b_val] at h_eq
  · simp [h_eq]
    rw [run_readReg]
    simp [Std.ExtDHashMap.get?_insert, h_pc_read, h_next_pc_b0, h_next_pc_b1]
    rw [SailME_run_readReg_map_writeReg _ Register.misa Register.nextPC
      (by simp [Std.ExtDHashMap.get?_insert]; exact hs Register.misa) _ _]
    simp only [Std.ExtDHashMap.insert_insert]
    have h_is_eq : Main[37] + Main[38] + Main[39] + Main[40] = 0 := by
      clear *- spec_lt h_eq h_30 h_31; simp_all
    have h_is_branching : Main[35] = 1 := by
      clear *- h_is_eq chip_cstrs; simp_all [sub_eq_zero]
    simp [h_is_branching, sub_eq_zero, h_is_eq] at chip_cstrs
    obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs
    have h26 : Main[26].val < 65536 := by
      clear *- h_bound_checks; simp_all [inv_2BB_eq']
    have h_addr_eq : Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] + BitVec.signExtend 64 imm
        = Word.toBitVec64 #v[Main[26], Main[27], Main[28], 0] := by
      close_branch_addr_eq
    rw [h_addr_eq]
  · have h_is_neq : (Main[37] + Main[38] + Main[39] + Main[40]) = 1 := by
      clear *- spec_lt h_eq h_30 h_31; simp_all
    simp [h_is_neq, sub_eq_zero] at chip_cstrs
    have h_is_branching : Main[35] = 0 := by
      clear *- h_is_neq chip_cstrs; simp_all [sub_eq_zero]
    simp [h_is_branching] at chip_cstrs
    simp [h_eq]
    obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs
    have h26 : Main[26].val < 65536 := by
      clear *- h_bound_checks; simp_all [inv_2BB_eq']
    simp [BitVec.add_def, Word.toBitVec64, Word.toNat, ← BitVec.toNat_inj]
    clear * - h26 h_pc_0 h_pc_1 h_pc_2 h_bound_checks h_limb0 h_limb1 h_limb2 h_limb3
    omega

end BEQ

namespace BNE

noncomputable def spec_bne (imm : (BitVec 13)) (rs2 : regidx) (rs1 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_BTYPE imm rs2 rs1 bop.BNE

set_option debug.skipKernelTC true in
set_option maxHeartbeats 2000000 in
-- correctness proof across all 6 branch-opcode cases
theorem correct_bne
    (Main : Vector (Fin KB) 46)
    (s : SailState) (hs : s.isInitialized)
    (h_is_bne : Main[30] = 1)
    (cstrs : (constraints Main).allHold)
    (state_cstrs : (constraints Main).initialState s) :
    let imm := sp1_imm Main
    let op_b := .Regidx (sp1_op_b Main)
    let op_a := .Regidx (sp1_op_a Main)
    (spec_bne imm op_b op_a).run s = (sp1_branch Main).run s := by
  extract_lets imm op_b op_a
  have h_is_real : is_real Main := by simp [is_real, h_is_bne]
  have h25 : Main[25] = 1 := is_trusted_of_constraints Main cstrs h_is_real
  have h_sign_extend := eq_signExtend_of_is_real Main cstrs h_is_real
  have h_next_pc_is_mul4 : (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] +
    BitVec.signExtend 64 imm) % 4 = 0 := add_signExtend_of_constraints Main cstrs h_is_real
  obtain ⟨h_next_pc_b0, h_next_pc_b1⟩ := mul4_means_0_1_are_0 h_next_pc_is_mul4
  obtain ⟨h_28, h_30, h_31, h_32, h_33⟩ := (single_op Main cstrs).2.1 h_is_bne
  simp [SP1ConstraintList.allHold, Branch.constraints] at cstrs
  obtain ⟨_, reader_cstrs, lt_cstrs, chip_cstrs⟩ := cstrs
  simp_all only [h25]
  -- simplify reader constraints
  simp [ITypeReaderImmutable.constraints, SP1Constraint.toProp,
    h_is_bne, h_28, h_30, h_31, h_32, h_33, Opcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs
  -- Introduce bounds on values
  have op_a_is_u64 : Word.isU64 #v[Main[7], Main[8], Main[9], Main[10]] := by simp_all only
  have op_b_is_u64 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := by simp_all only
  let op_a_val := Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]]
  let op_b_val := Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]
  have h6 : Main[6] < 32 := by aesop
  have h14 : Main[14] < 32 := by aesop
  have h_imm_0 : Main[21].val < 65536 := by change Main[21] < 65536; simp_all only
  have h_imm_1 : Main[22].val < 65536 := by change Main[22] < 65536; simp_all only
  have h_imm_2 : Main[23].val < 65536 := by change Main[23] < 65536; simp_all only
  have h_imm_3 : Main[24].val < 65536 := by change Main[24] < 65536; simp_all only
  have h_imm_is_u64 : Main[21].val + Main[22].val * 65536 + ↑Main[23] * 4294967296 + ↑Main[24] * 281474976710656 < 2^64 := by omega
  have op_c_is_u64 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := Word.isU64_of_cases h_imm_0 h_imm_1 h_imm_2 h_imm_3
  have h_pc_0 : Main[3].val < 65536 := by change Main[3] < 65536; aesop
  have h_pc_1 : Main[4].val < 65536 := by change Main[4] < 65536; aesop
  have h_pc_2 : Main[5].val < 65536 := by change Main[5] < 65536; aesop
  have h_pc_is_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 < 2^64 := by omega
  have h_pc_add4_is_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 + 4 < 2^64 := by omega
  have h_nextpc_is_u64 : Main[26].val + Main[27].val * 65536 + Main[28].val * 4294967296 < 2^64 := by omega
  simp_all
  -- simplify lt operation constraints
  have spec_lt := LtOperationSigned.spec.branch op_a_is_u64 op_b_is_u64 lt_cstrs
  clear lt_cstrs
  simp [LtOperationSigned.spec.branch.def] at spec_lt
  -- simplify state constraints
  simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall,
    CPUState.constraints, ITypeReaderImmutable.constraints, LtOperationSigned.constraints,
    LtOperationUnsigned.constraints, U16MSBOperation.constraints, U16CompareOperation.constraints,
    h_is_bne, h6, h14, h_28, h_30, h_31, h_32, h_33, Opcode.ofNat, Nat.ble, Nat.beq] at state_cstrs
  obtain ⟨h_pc_read, h_op_a_read, h_op_b_read⟩ := state_cstrs
  specialize h_op_a_read
  specialize h_op_b_read
  -- simplify main goal
  simp [spec_bne, sp1_branch, execute_BTYPE]
  rw [run_readReg]
  simp [h_pc_read]
  simp_all only [BitVec.ofNatLT_eq_ofNat]
  simp [op_a, sp1_op_a, h_op_a_read, op_b, sp1_op_b, h_op_b_read]
  by_cases h_eq : op_a_val ≠ op_b_val <;> simp [op_a_val, op_b_val] at h_eq
  · simp [h_eq]
    rw [run_readReg]
    simp [Std.ExtDHashMap.get?_insert, h_pc_read, h_next_pc_b0, h_next_pc_b1]
    rw [SailME_run_readReg_map_writeReg _ Register.misa Register.nextPC
      (by simp [Std.ExtDHashMap.get?_insert]; exact hs Register.misa) _ _]
    simp only [Std.ExtDHashMap.insert_insert]
    have h_is_eq : Main[37] + Main[38] + Main[39] + Main[40] = 1 := by
      clear *- spec_lt h_eq h_30 h_31; simp_all
    have h_is_branching : Main[35] = 1 := by
      clear *- h_is_eq chip_cstrs; simp_all [sub_eq_zero]
    simp [h_is_branching, sub_eq_zero, h_is_eq] at chip_cstrs
    obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs
    have h26 : Main[26].val < 65536 := by
      clear *- h_bound_checks; simp_all [inv_2BB_eq']
    have h_addr_eq : Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] + BitVec.signExtend 64 imm
        = Word.toBitVec64 #v[Main[26], Main[27], Main[28], 0] := by
      close_branch_addr_eq
    rw [h_addr_eq]
  · have h_is_neq : (Main[37] + Main[38] + Main[39] + Main[40]) = 0 := by
      clear *- spec_lt h_eq h_30 h_31; simp_all
    simp [h_is_neq, sub_eq_zero] at chip_cstrs
    have h_is_branching : Main[35] = 0 := by
      clear *- chip_cstrs; simp_all [sub_eq_zero]
    simp [h_is_branching] at chip_cstrs
    simp [h_eq]
    obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs
    have h26 : Main[26].val < 65536 := by
      clear *- h_bound_checks; simp_all [inv_2BB_eq']
    simp [BitVec.add_def, Word.toBitVec64, Word.toNat, ← BitVec.toNat_inj]
    clear * - h26 h_pc_0 h_pc_1 h_pc_2 h_bound_checks h_limb0 h_limb1 h_limb2 h_limb3
    omega

end BNE

namespace BLT

noncomputable def spec_blt (imm : (BitVec 13)) (rs2 : regidx) (rs1 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_BTYPE imm rs2 rs1 bop.BLT

set_option debug.skipKernelTC true in
set_option maxHeartbeats 2000000 in
-- correctness proof across all 6 branch-opcode cases
theorem correct_blt
    (Main : Vector (Fin KB) 46)
    (s : SailState) (hs : s.isInitialized)
    (h_is_blt : Main[31] = 1)
    (cstrs : (constraints Main).allHold)
    (state_cstrs : (constraints Main).initialState s) :
    let imm := sp1_imm Main
    let op_b := .Regidx (sp1_op_b Main)
    let op_a := .Regidx (sp1_op_a Main)
    (spec_blt imm op_b op_a).run s = (sp1_branch Main).run s := by
  extract_lets imm op_b op_a
  have h_is_real : is_real Main := by simp [is_real, h_is_blt]
  have h25 : Main[25] = 1 := is_trusted_of_constraints Main cstrs h_is_real
  have h_sign_extend := eq_signExtend_of_is_real Main cstrs h_is_real
  have h_next_pc_is_mul4 : (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] +
    BitVec.signExtend 64 imm) % 4 = 0 := add_signExtend_of_constraints Main cstrs h_is_real
  obtain ⟨h_next_pc_b0, h_next_pc_b1⟩ := mul4_means_0_1_are_0 h_next_pc_is_mul4
  obtain ⟨h_28, h_30, h_31, h_32, h_33⟩ := (single_op Main cstrs).2.2.1 h_is_blt
  simp [SP1ConstraintList.allHold, Branch.constraints] at cstrs
  obtain ⟨_, reader_cstrs, lt_cstrs, chip_cstrs⟩ := cstrs
  simp_all only [h25]
  -- simplify reader constraints
  simp [ITypeReaderImmutable.constraints, SP1Constraint.toProp,
    h_is_blt, h_28, h_30, h_31, h_32, h_33, Opcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs
  -- Introduce bounds on values
  have op_a_is_u64 : Word.isU64 #v[Main[7], Main[8], Main[9], Main[10]] := by simp_all only
  have op_b_is_u64 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := by simp_all only
  let op_a_val := Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]]
  let op_b_val := Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]
  have h6 : Main[6] < 32 := by aesop
  have h14 : Main[14] < 32 := by aesop
  have h_imm_0 : Main[21].val < 65536 := by change Main[21] < 65536; simp_all only
  have h_imm_1 : Main[22].val < 65536 := by change Main[22] < 65536; simp_all only
  have h_imm_2 : Main[23].val < 65536 := by change Main[23] < 65536; simp_all only
  have h_imm_3 : Main[24].val < 65536 := by change Main[24] < 65536; simp_all only
  have h_imm_is_u64 : Main[21].val + Main[22].val * 65536 + ↑Main[23] * 4294967296 + ↑Main[24] * 281474976710656 < 2^64 := by omega
  have op_c_is_u64 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := Word.isU64_of_cases h_imm_0 h_imm_1 h_imm_2 h_imm_3
  have h_pc_0 : Main[3].val < 65536 := by change Main[3] < 65536; aesop
  have h_pc_1 : Main[4].val < 65536 := by change Main[4] < 65536; aesop
  have h_pc_2 : Main[5].val < 65536 := by change Main[5] < 65536; aesop
  have h_pc_is_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 < 2^64 := by omega
  have h_pc_add4_is_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 + 4 < 2^64 := by omega
  have h_nextpc_is_u64 : Main[26].val + Main[27].val * 65536 + Main[28].val * 4294967296 < 2^64 := by omega
  simp_all
  -- simplify lt operation constraints
  have spec_lt := LtOperationSigned.spec.branch op_a_is_u64 op_b_is_u64 lt_cstrs
  clear lt_cstrs
  simp [LtOperationSigned.spec.branch.def] at spec_lt
  -- simplify state constraints
  simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall,
    CPUState.constraints, ITypeReaderImmutable.constraints, LtOperationSigned.constraints,
    LtOperationUnsigned.constraints, U16MSBOperation.constraints, U16CompareOperation.constraints,
    h_is_blt, h6, h14, h_28, h_30, h_31, h_32, h_33, Opcode.ofNat, Nat.ble, Nat.beq] at state_cstrs
  obtain ⟨h_pc_read, h_op_a_read, h_op_b_read⟩ := state_cstrs
  specialize h_op_a_read
  specialize h_op_b_read
  -- simplify main goal
  simp [spec_blt, sp1_branch, execute_BTYPE]
  rw [run_readReg]
  simp [h_pc_read]
  simp_all only [BitVec.ofNatLT_eq_ofNat]
  simp [op_a, sp1_op_a, h_op_a_read, op_b, sp1_op_b, h_op_b_read]
  by_cases h_eq : op_a_val.toInt < op_b_val.toInt <;> simp only [op_a_val, op_b_val] at h_eq
  · simp [h_eq]
    rw [run_readReg]
    simp [Std.ExtDHashMap.get?_insert, h_pc_read, h_next_pc_b0, h_next_pc_b1]
    rw [SailME_run_readReg_map_writeReg _ Register.misa Register.nextPC
      (by simp [Std.ExtDHashMap.get?_insert]; exact hs Register.misa) _ _]
    simp only [Std.ExtDHashMap.insert_insert]
    have h_ne : (Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]]) ≠
        (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]) := by
      clear *- h_eq; aesop
    simp [h_ne, h_eq, BitVec.slt] at spec_lt
    have h36 : Main[36] = 1 := by simp_all only
    have h_is_branching : Main[35] = 1 := by
      clear *- chip_cstrs h36; simp_all [sub_eq_zero]
    simp [h_is_branching, sub_eq_zero, h36] at chip_cstrs
    obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs
    have h26 : Main[26].val < 65536 := by
      clear *- h_bound_checks; simp_all [inv_2BB_eq']
    have h_addr_eq : Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] + BitVec.signExtend 64 imm
        = Word.toBitVec64 #v[Main[26], Main[27], Main[28], 0] := by
      close_branch_addr_eq
    rw [h_addr_eq]
  · simp [h_eq]
    simp [h_eq, BitVec.slt] at spec_lt
    have h36 : Main[36] = 0 := by simp_all only
    have h35 : Main[35] = 0 := by clear *- chip_cstrs h36; simp_all
    simp [h35, h36, sub_eq_zero] at chip_cstrs
    obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs
    have h26 : Main[26].val < 65536 := by
      clear *- h_bound_checks; simp_all [inv_2BB_eq']
    simp [BitVec.add_def, Word.toBitVec64, Word.toNat, ← BitVec.toNat_inj]
    clear * - h26 h_pc_0 h_pc_1 h_pc_2 h_bound_checks h_limb0 h_limb1 h_limb2 h_limb3
    omega

end BLT

namespace BGE

noncomputable def spec_bge (imm : (BitVec 13)) (rs2 : regidx) (rs1 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_BTYPE imm rs2 rs1 bop.BGE

set_option debug.skipKernelTC true in
set_option maxHeartbeats 2000000 in
-- correctness proof across all 6 branch-opcode cases
theorem correct_bge
    (Main : Vector (Fin KB) 46)
    (s : SailState) (hs : s.isInitialized)
    (h_is_bge : Main[32] = 1)
    (cstrs : (constraints Main).allHold)
    (state_cstrs : (constraints Main).initialState s) :
    let imm := sp1_imm Main
    let op_b := .Regidx (sp1_op_b Main)
    let op_a := .Regidx (sp1_op_a Main)
    (spec_bge imm op_b op_a).run s = (sp1_branch Main).run s := by
  extract_lets imm op_b op_a
  have h_is_real : is_real Main := by simp [is_real, h_is_bge]
  have h25 : Main[25] = 1 := is_trusted_of_constraints Main cstrs h_is_real
  have h_sign_extend := eq_signExtend_of_is_real Main cstrs h_is_real
  have h_next_pc_is_mul4 : (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] +
    BitVec.signExtend 64 imm) % 4 = 0 := add_signExtend_of_constraints Main cstrs h_is_real
  obtain ⟨h_next_pc_b0, h_next_pc_b1⟩ := mul4_means_0_1_are_0 h_next_pc_is_mul4
  obtain ⟨h_28, h_30, h_31, h_32, h_33⟩ := (single_op Main cstrs).2.2.2.1 h_is_bge
  simp [SP1ConstraintList.allHold, Branch.constraints] at cstrs
  obtain ⟨_, reader_cstrs, lt_cstrs, chip_cstrs⟩ := cstrs
  simp_all only [h25]
  -- simplify reader constraints
  simp [ITypeReaderImmutable.constraints, SP1Constraint.toProp,
    h_is_bge, h_28, h_30, h_31, h_32, h_33, Opcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs
  -- Introduce bounds on values
  have op_a_is_u64 : Word.isU64 #v[Main[7], Main[8], Main[9], Main[10]] := by simp_all only
  have op_b_is_u64 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := by simp_all only
  let op_a_val := Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]]
  let op_b_val := Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]
  have h6 : Main[6] < 32 := by aesop
  have h14 : Main[14] < 32 := by aesop
  have h_imm_0 : Main[21].val < 65536 := by change Main[21] < 65536; simp_all only
  have h_imm_1 : Main[22].val < 65536 := by change Main[22] < 65536; simp_all only
  have h_imm_2 : Main[23].val < 65536 := by change Main[23] < 65536; simp_all only
  have h_imm_3 : Main[24].val < 65536 := by change Main[24] < 65536; simp_all only
  have h_imm_is_u64 : Main[21].val + Main[22].val * 65536 + ↑Main[23] * 4294967296 + ↑Main[24] * 281474976710656 < 2^64 := by omega
  have op_c_is_u64 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := Word.isU64_of_cases h_imm_0 h_imm_1 h_imm_2 h_imm_3
  have h_pc_0 : Main[3].val < 65536 := by change Main[3] < 65536; aesop
  have h_pc_1 : Main[4].val < 65536 := by change Main[4] < 65536; aesop
  have h_pc_2 : Main[5].val < 65536 := by change Main[5] < 65536; aesop
  have h_pc_is_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 < 2^64 := by omega
  have h_pc_add4_is_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 + 4 < 2^64 := by omega
  have h_nextpc_is_u64 : Main[26].val + Main[27].val * 65536 + Main[28].val * 4294967296 < 2^64 := by omega
  simp_all
  -- simplify lt operation constraints
  have spec_lt := LtOperationSigned.spec.branch op_a_is_u64 op_b_is_u64 lt_cstrs
  clear lt_cstrs
  simp [LtOperationSigned.spec.branch.def] at spec_lt
  -- simplify state constraints
  simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall,
    CPUState.constraints, ITypeReaderImmutable.constraints, LtOperationSigned.constraints,
    LtOperationUnsigned.constraints, U16MSBOperation.constraints, U16CompareOperation.constraints,
    h_is_bge, h6, h14, h_28, h_30, h_31, h_32, h_33, Opcode.ofNat, Nat.ble, Nat.beq] at state_cstrs
  obtain ⟨h_pc_read, h_op_a_read, h_op_b_read⟩ := state_cstrs
  specialize h_op_a_read
  specialize h_op_b_read
  -- simplify main goal
  simp [spec_bge, sp1_branch, execute_BTYPE]
  rw [run_readReg]
  simp [h_pc_read]
  simp_all only [BitVec.ofNatLT_eq_ofNat]
  simp [op_a, sp1_op_a, h_op_a_read, op_b, sp1_op_b, h_op_b_read]
  by_cases h_eq : op_a_val.toInt ≥ op_b_val.toInt <;> simp only [op_a_val, op_b_val] at h_eq
  · simp [h_eq]
    rw [run_readReg]
    simp [Std.ExtDHashMap.get?_insert, h_pc_read, h_next_pc_b0, h_next_pc_b1]
    rw [SailME_run_readReg_map_writeReg _ Register.misa Register.nextPC
      (by simp [Std.ExtDHashMap.get?_insert]; exact hs Register.misa) _ _]
    simp only [Std.ExtDHashMap.insert_insert]
    have h_ne : ¬ ((Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]]).toInt <
        (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toInt) := by
      clear *- h_eq; omega
    simp [h_ne, h_eq, BitVec.slt] at spec_lt
    have h36 : Main[36] = 0 := by simp_all only
    have h_is_branching : Main[35] = 1 := by
      clear *- chip_cstrs h36; simp_all [sub_eq_zero]
    simp [h_is_branching, sub_eq_zero, h36] at chip_cstrs
    obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs
    have h26 : Main[26].val < 65536 := by
      clear *- h_bound_checks; simp_all [inv_2BB_eq']
    have h_addr_eq : Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] + BitVec.signExtend 64 imm
        = Word.toBitVec64 #v[Main[26], Main[27], Main[28], 0] := by
      close_branch_addr_eq
    rw [h_addr_eq]
  · simp [h_eq]
    have h_ne : ((Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]]).toInt <
        (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toInt) := by
      clear *- h_eq; omega
    simp [h_eq, h_ne, BitVec.slt] at spec_lt
    have h36 : Main[36] = 1 := by simp_all only
    have h35 : Main[35] = 0 := by clear *- chip_cstrs h36; simp_all
    simp [h35, h36, sub_eq_zero] at chip_cstrs
    obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs
    have h26 : Main[26].val < 65536 := by
      clear *- h_bound_checks; simp_all [inv_2BB_eq']
    simp [BitVec.add_def, Word.toBitVec64, Word.toNat, ← BitVec.toNat_inj]
    clear * - h26 h_pc_0 h_pc_1 h_pc_2 h_bound_checks h_limb0 h_limb1 h_limb2 h_limb3
    omega

end BGE

namespace BLTU

noncomputable def spec_bltu (imm : (BitVec 13)) (rs2 : regidx) (rs1 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_BTYPE imm rs2 rs1 bop.BLTU

set_option debug.skipKernelTC true in
set_option maxHeartbeats 2000000 in
-- correctness proof across all 6 branch-opcode cases
theorem correct_bltu
    (Main : Vector (Fin KB) 46)
    (s : SailState) (hs : s.isInitialized)
    (h_is_bltu : Main[33] = 1)
    (cstrs : (constraints Main).allHold)
    (state_cstrs : (constraints Main).initialState s) :
    let imm := sp1_imm Main
    let op_b := .Regidx (sp1_op_b Main)
    let op_a := .Regidx (sp1_op_a Main)
    (spec_bltu imm op_b op_a).run s = (sp1_branch Main).run s := by
  extract_lets imm op_b op_a
  have h_is_real : is_real Main := by simp [is_real, h_is_bltu]
  have h25 : Main[25] = 1 := is_trusted_of_constraints Main cstrs h_is_real
  have h_sign_extend := eq_signExtend_of_is_real Main cstrs h_is_real
  have h_next_pc_is_mul4 : (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] +
    BitVec.signExtend 64 imm) % 4 = 0 := add_signExtend_of_constraints Main cstrs h_is_real
  obtain ⟨h_next_pc_b0, h_next_pc_b1⟩ := mul4_means_0_1_are_0 h_next_pc_is_mul4
  obtain ⟨h_28, h_30, h_31, h_32, h_33⟩ := (single_op Main cstrs).2.2.2.2.1 h_is_bltu
  simp [SP1ConstraintList.allHold, Branch.constraints] at cstrs
  obtain ⟨_, reader_cstrs, lt_cstrs, chip_cstrs⟩ := cstrs
  simp_all only [h25]
  -- simplify reader constraints
  simp [ITypeReaderImmutable.constraints, SP1Constraint.toProp,
    h_is_bltu, h_28, h_30, h_31, h_32, h_33, Opcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs
  -- Introduce bounds on values
  have op_a_is_u64 : Word.isU64 #v[Main[7], Main[8], Main[9], Main[10]] := by simp_all only
  have op_b_is_u64 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := by simp_all only
  let op_a_val := Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]]
  let op_b_val := Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]
  have h6 : Main[6] < 32 := by aesop
  have h14 : Main[14] < 32 := by aesop
  have h_imm_0 : Main[21].val < 65536 := by change Main[21] < 65536; simp_all only
  have h_imm_1 : Main[22].val < 65536 := by change Main[22] < 65536; simp_all only
  have h_imm_2 : Main[23].val < 65536 := by change Main[23] < 65536; simp_all only
  have h_imm_3 : Main[24].val < 65536 := by change Main[24] < 65536; simp_all only
  have h_imm_is_u64 : Main[21].val + Main[22].val * 65536 + ↑Main[23] * 4294967296 + ↑Main[24] * 281474976710656 < 2^64 := by omega
  have op_c_is_u64 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := Word.isU64_of_cases h_imm_0 h_imm_1 h_imm_2 h_imm_3
  have h_pc_0 : Main[3].val < 65536 := by change Main[3] < 65536; aesop
  have h_pc_1 : Main[4].val < 65536 := by change Main[4] < 65536; aesop
  have h_pc_2 : Main[5].val < 65536 := by change Main[5] < 65536; aesop
  have h_pc_is_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 < 2^64 := by omega
  have h_pc_add4_is_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 + 4 < 2^64 := by omega
  have h_nextpc_is_u64 : Main[26].val + Main[27].val * 65536 + Main[28].val * 4294967296 < 2^64 := by omega
  simp_all
  -- simplify lt operation constraints
  have spec_lt := LtOperationSigned.spec.branch op_a_is_u64 op_b_is_u64 lt_cstrs
  clear lt_cstrs
  simp [LtOperationSigned.spec.branch.def] at spec_lt
  -- simplify state constraints
  simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall,
    CPUState.constraints, ITypeReaderImmutable.constraints, LtOperationSigned.constraints,
    LtOperationUnsigned.constraints, U16MSBOperation.constraints, U16CompareOperation.constraints,
    h_is_bltu, h6, h14, h_28, h_30, h_31, h_32, h_33, Opcode.ofNat, Nat.ble, Nat.beq] at state_cstrs
  obtain ⟨h_pc_read, h_op_a_read, h_op_b_read⟩ := state_cstrs
  specialize h_op_a_read
  specialize h_op_b_read
  -- simplify main goal
  simp [spec_bltu, sp1_branch, execute_BTYPE]
  rw [run_readReg]
  simp [h_pc_read]
  simp_all only [BitVec.ofNatLT_eq_ofNat]
  simp [op_a, sp1_op_a, h_op_a_read, op_b, sp1_op_b, h_op_b_read]
  by_cases h_eq : op_a_val.toNat < op_b_val.toNat <;> simp only [op_a_val, op_b_val] at h_eq
  · simp [h_eq]
    rw [run_readReg]
    simp [Std.ExtDHashMap.get?_insert, h_pc_read, h_next_pc_b0, h_next_pc_b1]
    rw [SailME_run_readReg_map_writeReg _ Register.misa Register.nextPC
      (by simp [Std.ExtDHashMap.get?_insert]; exact hs Register.misa) _ _]
    simp only [Std.ExtDHashMap.insert_insert]
    have h_ne : ((Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]]).toNat <
        (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat) := by
      clear *- h_eq; omega
    simp [h_ne, h_eq, BitVec.ult] at spec_lt
    have h36 : Main[36] = 1 := by simp_all only
    have h_is_branching : Main[35] = 1 := by
      clear *- chip_cstrs h36; simp_all [sub_eq_zero]
    simp [h_is_branching, sub_eq_zero, h36] at chip_cstrs
    obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs
    have h26 : Main[26].val < 65536 := by
      clear *- h_bound_checks; simp_all [inv_2BB_eq']
    have h_addr_eq : Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] + BitVec.signExtend 64 imm
        = Word.toBitVec64 #v[Main[26], Main[27], Main[28], 0] := by
      close_branch_addr_eq
    rw [h_addr_eq]
  · simp [h_eq]
    have h_ne : ¬ ((Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]]).toNat <
        (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat) := by
      clear *- h_eq; omega
    simp [h_eq, h_ne, BitVec.ult] at spec_lt
    have h36 : Main[36] = 0 := by simp_all only
    have h35 : Main[35] = 0 := by clear *- chip_cstrs h36; simp_all
    simp [h35, h36, sub_eq_zero] at chip_cstrs
    obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs
    have h26 : Main[26].val < 65536 := by
      clear *- h_bound_checks; simp_all [inv_2BB_eq']
    simp [BitVec.add_def, Word.toBitVec64, Word.toNat, ← BitVec.toNat_inj]
    clear * - h26 h_pc_0 h_pc_1 h_pc_2 h_bound_checks h_limb0 h_limb1 h_limb2 h_limb3
    omega

end BLTU

namespace BGEU

noncomputable def spec_bgeu (imm : (BitVec 13)) (rs2 : regidx) (rs1 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_BTYPE imm rs2 rs1 bop.BGEU

set_option debug.skipKernelTC true in
set_option maxHeartbeats 2000000 in
-- correctness proof across all 6 branch-opcode cases
theorem correct_bgeu
    (Main : Vector (Fin KB) 46)
    (s : SailState) (hs : s.isInitialized)
    (h_is_bgeu : Main[34] = 1)
    (cstrs : (constraints Main).allHold)
    (state_cstrs : (constraints Main).initialState s) :
    let imm := sp1_imm Main
    let op_b := .Regidx (sp1_op_b Main)
    let op_a := .Regidx (sp1_op_a Main)
    (spec_bgeu imm op_b op_a).run s = (sp1_branch Main).run s := by
  extract_lets imm op_b op_a
  have h_is_real : is_real Main := by simp [is_real, h_is_bgeu]
  have h25 : Main[25] = 1 := is_trusted_of_constraints Main cstrs h_is_real
  have h_sign_extend := eq_signExtend_of_is_real Main cstrs h_is_real
  have h_next_pc_is_mul4 : (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] +
    BitVec.signExtend 64 imm) % 4 = 0 := add_signExtend_of_constraints Main cstrs h_is_real
  obtain ⟨h_next_pc_b0, h_next_pc_b1⟩ := mul4_means_0_1_are_0 h_next_pc_is_mul4
  obtain ⟨h_28, h_30, h_31, h_32, h_33⟩ := (single_op Main cstrs).2.2.2.2.2 h_is_bgeu
  simp [SP1ConstraintList.allHold, Branch.constraints] at cstrs
  obtain ⟨_, reader_cstrs, lt_cstrs, chip_cstrs⟩ := cstrs
  simp_all only [h25]
  -- simplify reader constraints
  simp [ITypeReaderImmutable.constraints, SP1Constraint.toProp,
    h_is_bgeu, h_28, h_30, h_31, h_32, h_33, Opcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs
  -- Introduce bounds on values
  have op_a_is_u64 : Word.isU64 #v[Main[7], Main[8], Main[9], Main[10]] := by simp_all only
  have op_b_is_u64 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := by simp_all only
  let op_a_val := Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]]
  let op_b_val := Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]
  have h6 : Main[6] < 32 := by aesop
  have h14 : Main[14] < 32 := by aesop
  have h_imm_0 : Main[21].val < 65536 := by change Main[21] < 65536; simp_all only
  have h_imm_1 : Main[22].val < 65536 := by change Main[22] < 65536; simp_all only
  have h_imm_2 : Main[23].val < 65536 := by change Main[23] < 65536; simp_all only
  have h_imm_3 : Main[24].val < 65536 := by change Main[24] < 65536; simp_all only
  have h_imm_is_u64 : Main[21].val + Main[22].val * 65536 + ↑Main[23] * 4294967296 + ↑Main[24] * 281474976710656 < 2^64 := by omega
  have op_c_is_u64 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := Word.isU64_of_cases h_imm_0 h_imm_1 h_imm_2 h_imm_3
  have h_pc_0 : Main[3].val < 65536 := by change Main[3] < 65536; aesop
  have h_pc_1 : Main[4].val < 65536 := by change Main[4] < 65536; aesop
  have h_pc_2 : Main[5].val < 65536 := by change Main[5] < 65536; aesop
  have h_pc_is_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 < 2^64 := by omega
  have h_pc_add4_is_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 + 4 < 2^64 := by omega
  have h_nextpc_is_u64 : Main[26].val + Main[27].val * 65536 + Main[28].val * 4294967296 < 2^64 := by omega
  simp_all
  -- simplify lt operation constraints
  have spec_lt := LtOperationSigned.spec.branch op_a_is_u64 op_b_is_u64 lt_cstrs
  clear lt_cstrs
  simp [LtOperationSigned.spec.branch.def] at spec_lt
  -- simplify state constraints
  simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall,
    CPUState.constraints, ITypeReaderImmutable.constraints, LtOperationSigned.constraints,
    LtOperationUnsigned.constraints, U16MSBOperation.constraints, U16CompareOperation.constraints,
    h_is_bgeu, h6, h14, h_28, h_30, h_31, h_32, h_33, Opcode.ofNat, Nat.ble, Nat.beq] at state_cstrs
  obtain ⟨h_pc_read, h_op_a_read, h_op_b_read⟩ := state_cstrs
  specialize h_op_a_read
  specialize h_op_b_read
  -- simplify main goal
  simp [spec_bgeu, sp1_branch, execute_BTYPE]
  rw [run_readReg]
  simp [h_pc_read]
  simp_all only [BitVec.ofNatLT_eq_ofNat]
  simp [op_a, sp1_op_a, h_op_a_read, op_b, sp1_op_b, h_op_b_read]
  by_cases h_eq : op_a_val.toNat ≥ op_b_val.toNat <;> simp only [op_a_val, op_b_val] at h_eq
  · simp [h_eq]
    rw [run_readReg]
    simp [Std.ExtDHashMap.get?_insert, h_pc_read, h_next_pc_b0, h_next_pc_b1]
    rw [SailME_run_readReg_map_writeReg _ Register.misa Register.nextPC
      (by simp [Std.ExtDHashMap.get?_insert]; exact hs Register.misa) _ _]
    simp only [Std.ExtDHashMap.insert_insert]
    have h_ne : ¬ ((Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]]).toNat <
        (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat) := by
      clear *- h_eq; omega
    simp [h_ne, h_eq, BitVec.ult] at spec_lt
    have h36 : Main[36] = 0 := by simp_all only
    have h_is_branching : Main[35] = 1 := by
      clear *- chip_cstrs h36; simp_all [sub_eq_zero]
    simp [h_is_branching, sub_eq_zero, h36] at chip_cstrs
    obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs
    have h26 : Main[26].val < 65536 := by
      clear *- h_bound_checks; simp_all [inv_2BB_eq']
    have h_addr_eq : Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] + BitVec.signExtend 64 imm
        = Word.toBitVec64 #v[Main[26], Main[27], Main[28], 0] := by
      close_branch_addr_eq
    rw [h_addr_eq]
  · simp [h_eq]
    have h_ne : ((Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]]).toNat <
        (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat) := by
      clear *- h_eq; omega
    simp [h_eq, h_ne, BitVec.ult] at spec_lt
    have h36 : Main[36] = 1 := by simp_all only
    have h35 : Main[35] = 0 := by clear *- chip_cstrs h36; simp_all
    simp [h35, h36, sub_eq_zero] at chip_cstrs
    obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs
    have h26 : Main[26].val < 65536 := by
      clear *- h_bound_checks; simp_all [inv_2BB_eq']
    simp [BitVec.add_def, Word.toBitVec64, Word.toNat, ← BitVec.toNat_inj]
    clear * - h26 h_pc_0 h_pc_1 h_pc_2 h_bound_checks h_limb0 h_limb1 h_limb2 h_limb3
    omega

end BGEU

end Branch
