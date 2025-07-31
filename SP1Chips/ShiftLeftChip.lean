import SP1Foundations
import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader
import SP1Chips.ShiftLeft.Constraints

open LeanRV64IM.Functions
open BitVec

namespace Sll

open ShiftLeft

variable
  (Main : Vector (Fin BB) 65)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_sll : is_sll Main)

def spec_sll (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.SLL
  pure ()

def sp1_op_a : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[6] ?_
    simp
    show Main[6] < 32

    rw [SP1ConstraintList.allHold, allHold_constraints_iff_sll h_is_sll] at cstrs
    obtain ⟨ lt_op, cpu, alu, rest ⟩ := cstrs
    simp [ALUTypeReader.constraints, SP1Constraint.toProp] at alu
    simp_all [Opcode.ofNat, Nat.ble, Nat.beq]

def sp1_op_b : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[14] ?_
    simp
    show Main[14] < 32

    have alu_cstrs := by
      simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp] at cstrs
      exact cstrs.2.2.1

    rw [SP1ConstraintList.allHold, allHold_constraints_iff_sll h_is_sll] at cstrs
    obtain ⟨ lt_op, cpu, alu, rest ⟩ := cstrs
    simp [ALUTypeReader.constraints, SP1Constraint.toProp] at alu
    simp_all [Opcode.ofNat, Nat.ble, Nat.beq]

def sp1_op_c : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[21] ?_
    simp
    show Main[21] < 32

    rw [SP1ConstraintList.allHold, allHold_constraints_iff_sll h_is_sll] at cstrs
    obtain ⟨ lt_op, cpu, alu, rest ⟩ := cstrs
    simp [ALUTypeReader.constraints, SP1Constraint.toProp] at alu
    simp_all [Opcode.ofNat, Nat.ble, Nat.beq]

def sp1_sll : SailM Unit := do
  let op_a := sp1_op_a Main cstrs h_is_sll
  -- TODO(gzgz): we can obtain this from the constraint compiler
  -- This comes from the Interaction.state in CPUState
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] + 4)
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]])

set_option maxHeartbeats 1000000 in
theorem correct_sll
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main cstrs h_is_sll
  let op_b := sp1_op_b Main cstrs h_is_sll
  let op_a := sp1_op_a Main cstrs h_is_sll
  (spec_sll (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_sll Main cstrs h_is_sll).run s
  := by
    -- Obtain and simplify state and pure constraints
    simp [SP1ConstraintList.allHold] at cstrs; simp [is_sll] at h_is_sll
    have spec := spec.sll h_is_sll cstrs
    rw [allHold_constraints_iff_sll h_is_sll] at cstrs
    obtain ⟨ eq_m62, eq_m31 ⟩ := h_is_sll
    obtain ⟨ msb_cstrs, cpu_cstrs, alu_cstrs,
             b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5,
             diff,
             eq_su160, b_su160, eq_su161, b_su161, eq_su162, b_su162, eq_su163, b_su163,
             one_of_su16,
             eq_v01, eq_v012, eq_v0123,
             lt_ll0, lt_hl0, h_b0_dec,
             lt_ll1, lt_hl1, h_b1_dec,
             lt_ll2, lt_hl2, h_b2_dec,
             lt_ll3, lt_hl3, h_b3_dec,
             eq_lr0, eq_lr1, eq_lr2, eq_lr3,
             sll_00, sll_01, sll_02, sll_03, sll_04, sll_05, sll_06, sll_07, sll_08, sll_09, sll_10, sll_11, sll_12, sll_13, sll_14, sll_15,
             eq_m63, eq_m64 ⟩ := cstrs
    rw [ALUTypeReader.allHold_constraints_iff_is_real (by rfl)] at alu_cstrs
    simp [Opcode.ofNat, Nat.ble, Nat.beq] at alu_cstrs
    obtain ⟨ h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, is_U64_b, ⟨ h15, h16, is_U64_c ⟩, h17 ⟩ := alu_cstrs

    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨throwaway, read_pc, trusted_instr_state, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear throwaway; simp_all
    simp [Opcode.ofNat, Nat.ble, Nat.beq] at *; simp_all

    -- Now the monadic manipulation
    simp [spec_sll, sp1_sll, execute, execute_RTYPE']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . rw [← spec]; simp [Word.toBitVec64, Word.toNat]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [exec_RTYPE_pure_bv_to_w _ _ _ (by omega) (by omega)]
      simp [Word.toBitVec64, Word.toNat]
      rfl

end Sll

namespace Slli

open ShiftLeft

variable
  (Main : Vector (Fin BB) 65)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_slli : is_slli Main)

def spec_slli (shamt : BitVec 6) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_SHIFTIOP shamt rs1 rd sop.SLLI
  pure ()

def sp1_op_a : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[6] ?_
    simp
    show Main[6] < 32

    rw [SP1ConstraintList.allHold, allHold_constraints_iff_slli h_is_slli] at cstrs
    obtain ⟨ lt_op, cpu, alu, rest ⟩ := cstrs
    simp [ALUTypeReader.constraints, SP1Constraint.toProp] at alu
    simp_all [Opcode.ofNat, Nat.ble, Nat.beq]

def sp1_op_b : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[14] ?_
    simp
    show Main[14] < 32

    have alu_cstrs := by
      simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp] at cstrs
      exact cstrs.2.2.1

    rw [SP1ConstraintList.allHold, allHold_constraints_iff_slli h_is_slli] at cstrs
    obtain ⟨ lt_op, cpu, alu, rest ⟩ := cstrs
    simp [ALUTypeReader.constraints, SP1Constraint.toProp] at alu
    simp_all [Opcode.ofNat, Nat.ble, Nat.beq]

def sp1_op_c : BitVec 6 := BitVec.ofNat 6 Main[21]

def sp1_slli : SailM Unit := do
  let op_a := sp1_op_a Main cstrs h_is_slli
  -- TODO(gzgz): we can obtain this from the constraint compiler
  -- This comes from the Interaction.state in CPUState
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] + 4)
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]])

set_option maxHeartbeats 1000000 in
theorem correct_sll
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main
  let op_b := sp1_op_b Main cstrs h_is_slli
  let op_a := sp1_op_a Main cstrs h_is_slli
  (spec_slli op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_slli Main cstrs h_is_slli).run s
  := by
    -- Obtain and simplify state and pure constraints
    simp [SP1ConstraintList.allHold] at cstrs; simp [is_sll] at h_is_slli
    have spec := spec.slli h_is_slli cstrs
    rw [allHold_constraints_iff_slli h_is_slli] at cstrs
    obtain ⟨ eq_m62, eq_m31 ⟩ := h_is_slli
    obtain ⟨ msb_cstrs, cpu_cstrs, alu_cstrs,
             b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5,
             diff,
             eq_su160, b_su160, eq_su161, b_su161, eq_su162, b_su162, eq_su163, b_su163,
             one_of_su16,
             eq_v01, eq_v012, eq_v0123,
             lt_ll0, lt_hl0, h_b0_dec,
             lt_ll1, lt_hl1, h_b1_dec,
             lt_ll2, lt_hl2, h_b2_dec,
             lt_ll3, lt_hl3, h_b3_dec,
             eq_lr0, eq_lr1, eq_lr2, eq_lr3,
             sll_00, sll_01, sll_02, sll_03, sll_04, sll_05, sll_06, sll_07, sll_08, sll_09, sll_10, sll_11, sll_12, sll_13, sll_14, sll_15,
             eq_m63, eq_m64 ⟩ := cstrs
    rw [ALUTypeReader.allHold_constraints_iff_is_real (by rfl)] at alu_cstrs
    simp [Opcode.ofNat, Nat.ble, Nat.beq] at alu_cstrs
    obtain ⟨ ⟨ h0, hc0, hc1, hc2, hc3 ⟩, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, is_U64_b, h15, eq_c0, eq_c1, eq_c2, eq_c3 ⟩ := alu_cstrs

    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨throwaway, read_pc, trusted_instr_state, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear throwaway; simp_all
    simp [Opcode.ofNat, Nat.ble, Nat.beq] at *; simp_all

    -- Now the monadic manipulation
    simp [spec_slli, sp1_slli, execute, execute_SHIFTIOP']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b]
    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . rw [← spec]; simp [Word.toBitVec64, Word.toNat]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [exec_SHIFTIOP_pure_bv_to_w _ _ _ is_U64_b]
      simp [Word.toBitVec64, Word.toNat]
      rfl

end Slli

namespace Sllw

open ShiftLeft

variable
  (Main : Vector (Fin BB) 65)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_sllw : is_sllw Main)

def spec_sllw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPEW rs2 rs1 rd ropw.SLLW
  pure ()

def sp1_op_a : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[6] ?_
    simp
    show Main[6] < 32

    rw [SP1ConstraintList.allHold, allHold_constraints_iff_sllw h_is_sllw] at cstrs
    obtain ⟨ lt_op, cpu, alu, rest ⟩ := cstrs
    simp [ALUTypeReader.constraints, SP1Constraint.toProp] at alu
    simp_all [Opcode.ofNat, Nat.ble, Nat.beq]

def sp1_op_b : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[14] ?_
    simp
    show Main[14] < 32

    have alu_cstrs := by
      simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp] at cstrs
      exact cstrs.2.2.1

    rw [SP1ConstraintList.allHold, allHold_constraints_iff_sllw h_is_sllw] at cstrs
    obtain ⟨ lt_op, cpu, alu, rest ⟩ := cstrs
    simp [ALUTypeReader.constraints, SP1Constraint.toProp] at alu
    simp_all [Opcode.ofNat, Nat.ble, Nat.beq]

def sp1_op_c : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[21] ?_
    simp
    show Main[21] < 32

    rw [SP1ConstraintList.allHold, allHold_constraints_iff_sllw h_is_sllw] at cstrs
    obtain ⟨ lt_op, cpu, alu, rest ⟩ := cstrs
    simp [ALUTypeReader.constraints, SP1Constraint.toProp] at alu
    simp_all [Opcode.ofNat, Nat.ble, Nat.beq]

def sp1_sllw : SailM Unit := do
  let op_a := sp1_op_a Main cstrs h_is_sllw
  -- TODO(gzgz): we can obtain this from the constraint compiler
  -- This comes from the Interaction.state in CPUState
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] + 4)
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]])

set_option maxHeartbeats 1000000 in
theorem correct_sll
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main cstrs h_is_sllw
  let op_b := sp1_op_b Main cstrs h_is_sllw
  let op_a := sp1_op_a Main cstrs h_is_sllw
  (spec_sllw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_sllw Main cstrs h_is_sllw).run s
  := by
    -- Obtain and simplify state and pure constraints
    simp [SP1ConstraintList.allHold] at cstrs; simp [is_sll] at h_is_sllw
    have spec := spec.sllw h_is_sllw cstrs
    rw [allHold_constraints_iff_sllw h_is_sllw] at cstrs
    obtain ⟨ eq_m63, eq_m31 ⟩ := h_is_sllw
    obtain ⟨ msb_cstrs, cpu_cstrs, alu_cstrs,
             b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5,
             diff,
             eq_su160, b_su160, eq_su161, b_su161, eq_su162, b_su162, eq_su163, b_su163,
             one_of_su16,
             eq_v01, eq_v012, eq_v0123,
             lt_ll0, lt_hl0, h_b0_dec,
             lt_ll1, lt_hl1, h_b1_dec,
             lt_ll2, lt_hl2, h_b2_dec,
             lt_ll3, lt_hl3, h_b3_dec,
             eq_lr0, eq_lr1, eq_lr2, eq_lr3,
             sllw_00, sllw_01, sllw_02, sllw_03, sllw_04, sllw_05,
             eq_m62, eq_m64 ⟩ := cstrs
    rw [ALUTypeReader.allHold_constraints_iff_is_real (by rfl)] at alu_cstrs
    simp [Opcode.ofNat, Nat.ble, Nat.beq] at alu_cstrs
    obtain ⟨ h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, is_U64_b, ⟨ h15, h16, is_U64_c ⟩, h17 ⟩ := alu_cstrs

    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨throwaway, read_pc, trusted_instr_state, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear throwaway; simp_all
    simp [Opcode.ofNat, Nat.ble, Nat.beq] at *; simp_all

    -- Now the monadic manipulation
    simp [spec_sllw, sp1_sllw, execute, execute_RTYPEW']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . rw [← spec]; simp [Word.toBitVec64, Word.toNat]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [exec_RTYPEW_pure_bv_to_w _ _ _ (by omega) (by omega)]
      simp [Word.toBitVec64, Word.toNat]
      rfl

end Sllw

namespace Slliw

open ShiftLeft

variable
  (Main : Vector (Fin BB) 65)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_slliw : is_slliw Main)

def spec_slliw (shamt : BitVec 6) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_SHIFTIWOP shamt rs1 rd sopw.SLLIW
  pure ()

def sp1_op_a : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[6] ?_
    simp
    show Main[6] < 32

    rw [SP1ConstraintList.allHold, allHold_constraints_iff_slliw h_is_slliw] at cstrs
    obtain ⟨ lt_op, cpu, alu, rest ⟩ := cstrs
    simp [ALUTypeReader.constraints, SP1Constraint.toProp] at alu
    simp_all [Opcode.ofNat, Nat.ble, Nat.beq]

def sp1_op_b : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[14] ?_
    simp
    show Main[14] < 32

    have alu_cstrs := by
      simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp] at cstrs
      exact cstrs.2.2.1

    rw [SP1ConstraintList.allHold, allHold_constraints_iff_slliw h_is_slliw] at cstrs
    obtain ⟨ lt_op, cpu, alu, rest ⟩ := cstrs
    simp [ALUTypeReader.constraints, SP1Constraint.toProp] at alu
    simp_all [Opcode.ofNat, Nat.ble, Nat.beq]

def sp1_op_c : BitVec 6 := BitVec.ofNat 6 Main[21]

def sp1_slliw : SailM Unit := do
  let op_a := sp1_op_a Main cstrs h_is_slliw
  -- TODO(gzgz): we can obtain this from the constraint compiler
  -- This comes from the Interaction.state in CPUState
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] + 4)
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]])

set_option maxHeartbeats 1000000 in
theorem correct_sll
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main
  let op_b := sp1_op_b Main cstrs h_is_slliw
  let op_a := sp1_op_a Main cstrs h_is_slliw
  (spec_slliw op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_slliw Main cstrs h_is_slliw).run s
  := by
    -- Obtain and simplify state and pure constraints
    simp [SP1ConstraintList.allHold] at cstrs; simp [is_sll] at h_is_slliw
    have ⟨ m25, m26, m27, m28, spec ⟩ := spec.slliw h_is_slliw cstrs
    rw [allHold_constraints_iff_slliw h_is_slliw] at cstrs
    obtain ⟨ eq_m63, eq_m31 ⟩ := h_is_slliw
    obtain ⟨ msb_cstrs, cpu_cstrs, alu_cstrs,
             b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5,
             diff,
             eq_su160, b_su160, eq_su161, b_su161, eq_su162, b_su162, eq_su163, b_su163,
             one_of_su16,
             eq_v01, eq_v012, eq_v0123,
             lt_ll0, lt_hl0, h_b0_dec,
             lt_ll1, lt_hl1, h_b1_dec,
             lt_ll2, lt_hl2, h_b2_dec,
             lt_ll3, lt_hl3, h_b3_dec,
             eq_lr0, eq_lr1, eq_lr2, eq_lr3,
             sllw_00, sllw_01, sllw_02, sllw_03, sllw_04, sllw_05,
             eq_m62, eq_m64 ⟩ := cstrs
    rw [ALUTypeReader.allHold_constraints_iff_is_real (by rfl)] at alu_cstrs
    simp [Opcode.ofNat, Nat.ble, Nat.beq] at alu_cstrs
    obtain ⟨ ⟨ h0, hc0, hc1, hc2, hc3 ⟩, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, is_U64_b, h15, eq_c0, eq_c1, eq_c2, eq_c3 ⟩ := alu_cstrs

    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, CPUState.constraints, ALUTypeReader.constraints] at state_cstrs
    obtain ⟨throwaway, read_pc, trusted_instr_state, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    clear throwaway; simp_all
    simp [Opcode.ofNat, Nat.ble, Nat.beq] at *; simp_all

    -- Now the monadic manipulation
    simp [spec_slliw, sp1_slliw, execute, execute_SHIFTIWOP']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b]
    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    . rw [← spec]; simp [Word.toBitVec64, Word.toNat]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [exec_SHIFTIWOP_pure_bv_to_w _ _ _ is_U64_b]
      simp [Word.toBitVec64, Word.toNat]
      congr; simpa

end Slliw
