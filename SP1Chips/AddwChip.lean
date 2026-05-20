import SP1Operations.Operation.AddwOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader
import SP1Chips.Addw.Constraints

open LeanRV64D.Functions
open BitVec

namespace Addw

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 36)
  (s : SailState)

noncomputable def spec_addw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPEW rs2 rs1 rd ropw.ADDW
  pure ()

def sp1_op_a : BitVec 5 := BitVec.ofNat 5 Main[6].val

def sp1_op_b : BitVec 5 := BitVec.ofNat 5 Main[14].val

def sp1_op_c : BitVec 5 := BitVec.ofNat 5 Main[21].val

def sp1_addw : SailM Unit := do
  let op_a := sp1_op_a Main
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[32], Main[33], Main[34] * 65535, Main[34] * 65535])

open Sail

set_option maxHeartbeats 1600000 in
-- Sign-extend manipulation in the non-zero op_a branch sits well above
-- the default 200K heartbeat budget (matches SubwChip).
theorem correct_addw
  (cstrs : (constraints Main).allHold_poly)
  (h_is_real : Main[35] = 1)
  (h_is_addw : Main[31] = 0)
  (state_cstrs : (constraints Main).initialState_poly s) :
  let op_c := sp1_op_c Main
  let op_b := sp1_op_b Main
  let op_a := sp1_op_a Main
  (spec_addw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_addw Main).run s
  := by
    simp [constraints] at cstrs
    obtain ⟨addw_op_cstrs, cpu_cstrs, alu_cstrs, _⟩ := cstrs
    haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    have h19_lt : (19 : ℕ) < p := by
      have h := Fact.out (p := 2 ^ 17 < p)
      have : (19 : ℕ) < 2 ^ 17 := by decide
      omega
    have h19_val : (19 : ZMod p).val = 19 := ZMod.val_natCast_of_lt h19_lt
    rw [CPUState.allHold_constraints_iff_is_real_poly h_is_real] at cpu_cstrs
    simp [ALUTypeReader.allHold_constraints_iff_is_real_poly h_is_real rfl,
      Opcode.ofNat, Nat.ble, h19_val] at alu_cstrs
    -- ADDW arm: imm_c = 0, so r_type clause activates and op_c memory clause applies
    have h_imm_c : Main[31] = 0 := h_is_addw
    simp [h_imm_c] at alu_cstrs
    obtain ⟨trusted_instr_prop, h_op_a_lt, h_op_b_lt, ⟨c0, c1, c2, c3⟩,
            _h_a0_bool, h_a0_iff,
            _pc_mod, _h3_lt, _h4_lt, _h5_lt,
            _h12_lt, _h20_lt, _h_clk_b, _h_clk_a,
            _is_U64_a, is_U64_b,
            ⟨_h_clk_c, _h30_lt, is_U64_c⟩,
            h_op_a_0_zero⟩ := alu_cstrs
    have h32 : (32 : ZMod p).val = 32 := val_32_zmod_p
    have h6 : Main[6].val < 32 := by
      have : Main[6].val < (32 : ZMod p).val := h_op_a_lt
      rwa [h32] at this
    have h14 : Main[14].val < 32 := by
      have : Main[14].val < (32 : ZMod p).val := trusted_instr_prop.1
      rwa [h32] at this
    have h21 : Main[21].val < 32 := by
      have : Main[21].val < (32 : ZMod p).val := trusted_instr_prop.2.1
      rwa [h32] at this
    simp [SP1ConstraintList.initialState_poly, constraints, SP1Constraint.toStateProp,
      List.Forall, AddwOperation.constraints, CPUState.constraints, ALUTypeReader.constraints,
      U16MSBOperation.constraints, h6, h14, h21, h_is_real, h_imm_c] at state_cstrs
    obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    rw [h_is_real] at *
    apply AddwOperation.spec_poly is_U64_b is_U64_c at addw_op_cstrs
    obtain ⟨is_U32_val, is_addw, is_msb⟩ := addw_op_cstrs
    simp [BitVec.ofNatLT_eq_ofNat] at *
    -- Now the monadic manipulation
    simp [spec_addw, sp1_addw, execute_RTYPEW']
    rw [run_readReg, read_pc]
    simp [sp1_op_b, read_op_b]
    simp [sp1_op_c, read_op_c]
    simp [sp1_op_a]
    rw [exec_RTYPEW_pure_bv_to_w_poly _ _ _ is_U64_b is_U64_c]
    simp only [execute_RTYPEW_pure_w_poly, execute_RTYPEW_pure_32_w_poly,
      LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend]
    rw [← is_addw, HWord.sign_extend_32_to_64_msb_poly is_U32_val]
    by_cases h_is_op_a_0 : Main[6] = 0
    · simp_all
    · simp_all
      have h6_val : Main[6].val ≠ 0 := by
        intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
      have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
        intro heq
        rw [← BitVec.toNat_inj] at heq
        simp at heq
        omega
      rw [if_neg h_bv_neq, if_neg h_bv_neq]
      have hp_lt : 131072 < p := by
        have := Fact.out (p := 2 ^ 17 < p)
        have h17 : (2 : ℕ) ^ 17 = 131072 := by decide
        omega
      have h_pc3 : Main[3].val < 65536 := by
        have h3 : Main[3] < (65536 : ZMod p) := by simp_all
        have : Main[3].val < (65536 : ZMod p).val := h3
        rwa [val_65536_zmod_p] at this
      rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
          Word.toBitVec64_lowLimb_add_nat _ _ _ _ 4 (by omega),
          show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
      simp [bitVecToRegidxVal]

end Addw

namespace Addiw

open Addw Sail

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 36)
  (s : SailState)

noncomputable def spec_addiw (imm : BitVec 12) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_ADDIW imm rs1 rd
  pure ()

def sp1_op_a : BitVec 5 := BitVec.ofNat 5 Main[6].val

def sp1_op_b : BitVec 5 := BitVec.ofNat 5 Main[14].val

def sp1_op_c : BitVec 12 := BitVec.ofNat 12 Main[21].val

def sp1_addiw : SailM Unit := do
  let op_a := sp1_op_a Main
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[32], Main[33], Main[34] * 65535, Main[34] * 65535])

set_option maxHeartbeats 1600000 in
-- Sign-extend manipulation in the non-zero op_a branch sits well above
-- the default 200K heartbeat budget (matches SubwChip).
theorem correct_addw
  (cstrs : (constraints Main).allHold_poly)
  (h_is_real : Main[35] = 1)
  (h_is_addiw : Main[31] = 1)
  (state_cstrs : (constraints Main).initialState_poly s) :
  let op_c := sp1_op_c Main
  let op_b := sp1_op_b Main
  let op_a := sp1_op_a Main
  (spec_addiw op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_addiw Main).run s
  := by
    simp [constraints] at cstrs
    obtain ⟨addw_op_cstrs, cpu_cstrs, alu_cstrs, _⟩ := cstrs
    haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    have h19_lt : (19 : ℕ) < p := by
      have h := Fact.out (p := 2 ^ 17 < p)
      have : (19 : ℕ) < 2 ^ 17 := by decide
      omega
    have h19_val : (19 : ZMod p).val = 19 := ZMod.val_natCast_of_lt h19_lt
    rw [CPUState.allHold_constraints_iff_is_real_poly h_is_real] at cpu_cstrs
    simp [ALUTypeReader.allHold_constraints_iff_is_real_poly h_is_real rfl,
      Opcode.ofNat, Nat.ble, h19_val] at alu_cstrs
    -- ADDIW arm: imm_c = 1, so i_type clause activates and op_c memory ≡ op_c imm
    have h_imm_c : Main[31] = 1 := h_is_addiw
    simp [h_imm_c] at alu_cstrs
    obtain ⟨trusted_instr_prop, h_op_a_lt, h_op_b_lt, ⟨c0, c1, c2, c3⟩,
            _h_a0_bool, h_a0_iff,
            _pc_mod, _h3_lt, _h4_lt, _h5_lt,
            _h12_lt, _h20_lt, _h_clk_b, _h_clk_a,
            _is_U64_a, is_U64_b,
            h_op_a_0_zero, h25_eq, h26_eq, h27_eq, h28_eq⟩ := alu_cstrs
    have h32 : (32 : ZMod p).val = 32 := val_32_zmod_p
    have h65 : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
    have h6 : Main[6].val < 32 := by
      have : Main[6].val < (32 : ZMod p).val := h_op_a_lt
      rwa [h32] at this
    have h14 : Main[14].val < 32 := by
      have : Main[14].val < (32 : ZMod p).val := trusted_instr_prop.1
      rwa [h32] at this
    have h21 : Main[21].val < 65536 := by
      have : Main[21].val < (65536 : ZMod p).val := c0
      rwa [h65] at this
    have h22 : Main[22].val < 65536 := by
      have : Main[22].val < (65536 : ZMod p).val := c1
      rwa [h65] at this
    have h23 : Main[23].val < 65536 := by
      have : Main[23].val < (65536 : ZMod p).val := c2
      rwa [h65] at this
    have h24 : Main[24].val < 65536 := by
      have : Main[24].val < (65536 : ZMod p).val := c3
      rwa [h65] at this
    -- The AddwOperation receives op_c_memory.prev_value (Main[25..28]); via h_op_c_eq
    -- these equal cols.op_c[0..3] (Main[21..24]), which we have bounds for.
    have h_op_c_imm_isU64 : Word.isU64_poly #v[Main[25], Main[26], Main[27], Main[28]] := by
      rw [h25_eq, h26_eq, h27_eq, h28_eq]
      exact Word.isU64_of_cases_poly h21 h22 h23 h24
    simp [SP1ConstraintList.initialState_poly, constraints, SP1Constraint.toStateProp,
      List.Forall, AddwOperation.constraints, CPUState.constraints, ALUTypeReader.constraints,
      U16MSBOperation.constraints, h6, h14, h_is_real, h_imm_c] at state_cstrs
    obtain ⟨read_pc, _read_op_a, read_op_b⟩ := state_cstrs
    rw [h_is_real] at *
    apply AddwOperation.spec_poly is_U64_b h_op_c_imm_isU64 at addw_op_cstrs
    obtain ⟨is_U32_val, is_addiw, is_msb⟩ := addw_op_cstrs
    obtain ⟨h_f, h_imm_c_consts⟩ := trusted_instr_prop
    simp [BitVec.ofNatLT_eq_ofNat] at *
    -- Now the monadic manipulation
    simp [spec_addiw, sp1_addiw, execute_ADDIW']
    rw [run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b]
    -- Bridge: the immediate's signExtend matches Word.toBitVec64 of op_c_memory
    -- (which equals the op_c imm vector by h25_eq..h28_eq).
    have h_signExt_eq :
        signExtend 64 (BitVec.ofNat 12 Main[21].val) =
          Word.toBitVec64 #v[Main[25], Main[26], Main[27], Main[28]] := by
      rw [h25_eq, h26_eq, h27_eq, h28_eq, ← h_imm_c_consts]
    rw [h_signExt_eq]
    rw [exec_RTYPEW_pure_bv_to_w_poly _ _ _ is_U64_b h_op_c_imm_isU64]
    simp only [execute_RTYPEW_pure_w_poly, execute_RTYPEW_pure_32_w_poly,
      LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend]
    rw [← is_addiw, HWord.sign_extend_32_to_64_msb_poly is_U32_val]
    by_cases h_is_op_a_0 : Main[6] = 0
    · simp_all
    · simp_all
      have h6_val : Main[6].val ≠ 0 := by
        intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
      have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
        intro heq
        rw [← BitVec.toNat_inj] at heq
        simp at heq
        omega
      rw [if_neg h_bv_neq, if_neg h_bv_neq]
      have hp_lt : 131072 < p := by
        have := Fact.out (p := 2 ^ 17 < p)
        have h17 : (2 : ℕ) ^ 17 = 131072 := by decide
        omega
      have h_pc3 : Main[3].val < 65536 := by
        have h3 : Main[3] < (65536 : ZMod p) := by simp_all
        have : Main[3].val < (65536 : ZMod p).val := h3
        rwa [val_65536_zmod_p] at this
      rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
          Word.toBitVec64_lowLimb_add_nat _ _ _ _ 4 (by omega),
          show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
      simp [bitVecToRegidxVal]

end Addiw
