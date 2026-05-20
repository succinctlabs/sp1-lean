import SP1Foundations
import SP1Operations.Operation.BitwiseU16Operation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader
import SP1Chips.Bitwise.Constraints

open LeanRV64D.Functions BitVec

set_option linter.style.setOption false
set_option linter.style.longLine false

/-! ### Shared helpers used by all 6 Bitwise chip arms.

The Bitwise chip's `Constraints.lean` declares a single `allHold_constraints_iff_poly`
covering all 6 variants; per-variant chip arms apply the iff plus `single_op_poly`
to collapse to the active variant, then bridge through `BitwiseU16Operation.spec.{xor,or,and}_poly`. -/

namespace Bitwise


variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 51)

-- Unified SP1 implementation for the Bitwise chip. All six variants
-- (xor, or, and, xori, ori, andi) write the same Main result columns to op_a; the
-- chip's constraints determine which Sail spec those columns implement.
def sp1_bitwise : SailM Unit := do
  let op_a : BitVec 5 := BitVec.ofNat 5 Main[6].val
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[40] + Main[41] * 256, Main[42] + Main[43] * 256, Main[44] + Main[45] * 256, Main[46] + Main[47] * 256])

end Bitwise

namespace Xor

open Bitwise

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 51)
  (s : SailState)

noncomputable def spec_xor (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.XOR
  pure ()

def sp1_op_a : BitVec 5 := BitVec.ofNat 5 Main[6].val
def sp1_op_b : BitVec 5 := BitVec.ofNat 5 Main[14].val
def sp1_op_c : BitVec 5 := BitVec.ofNat 5 Main[21].val

open Sail

set_option maxHeartbeats 1600000 in
-- BitwiseU16Operation spec_poly bridge plus PC arithmetic exceeds default 200K.
theorem correct_xor
  (cstrs : (constraints Main).allHold_poly)
  (h_is_xor : is_xor_poly Main)
  (state_cstrs : (constraints Main).initialState_poly s) :
  let op_c := sp1_op_c Main
  let op_b := sp1_op_b Main
  let op_a := sp1_op_a Main
  (spec_xor (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (Bitwise.sp1_bitwise Main).run s
  := by
    simp [SP1ConstraintList.allHold_poly] at cstrs
    rw [allHold_constraints_iff_poly] at cstrs
    obtain ⟨h_bop, cpu_cstrs, alu_cstrs, b_xor, b_or, b_and, one_of, _h13⟩ := cstrs
    obtain ⟨h_M48, h_imm_c⟩ := h_is_xor
    haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    have h_is_real : Main[48] + Main[49] + Main[50] = 1 :=
      sum_eq_one_of_eq_one_left h_M48 b_or b_and one_of
    have ⟨h_M49, h_M50⟩ := (single_op_poly Main b_xor b_or b_and h_is_real).1 h_M48
    have h3_lt : (3 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    have h3_val : (3 : ZMod p).val = 3 := ZMod.val_natCast_of_lt h3_lt
    rw [CPUState.allHold_constraints_iff_is_real_poly h_is_real] at cpu_cstrs
    rw [ALUTypeReader.allHold_constraints_iff_is_real_poly h_is_real rfl] at alu_cstrs
    simp [h_M48, h_M49, h_M50, Opcode.ofNat, Nat.ble, h3_val, h_imm_c] at alu_cstrs
    obtain ⟨trusted_instr_prop, h_op_a_lt, h_op_b_lt, _h_c_bnds,
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
    -- Bridge: BitwiseU16Operation.constraints takes (xor opcode = 2, is_real = 1).
    -- Substituting Main[48]=1, Main[49]=Main[50]=0 reduces the call to opcode 2 / is_real 1.
    have h_xor_args : (Main[48] * 2 + Main[49] * 1 + Main[50] * 0 : ZMod p) = 2 := by
      rw [h_M48, h_M49, h_M50]; push_cast; ring
    have h_real_args : Main[48] + Main[49] + Main[50] = (1 : ZMod p) := h_is_real
    rw [h_xor_args, h_real_args] at h_bop
    apply BitwiseU16Operation.spec.xor_poly is_U64_b is_U64_c at h_bop
    simp [BitwiseU16Operation.constraints, U16toU8OperationUnsafe.constraints,
      BitwiseOperation.constraints] at h_bop
    simp [SP1ConstraintList.initialState_poly, constraints, SP1Constraint.toStateProp,
      List.Forall, BitwiseU16Operation.constraints, U16toU8OperationUnsafe.constraints,
      BitwiseOperation.constraints,
      CPUState.constraints, ALUTypeReader.constraints,
      h6, h14, h21, h_is_real, h_imm_c] at state_cstrs
    obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    simp only [BitVec.ofNatLT_eq_ofNat] at *
    simp [spec_xor, Bitwise.sp1_bitwise, execute_RTYPE']
    rw [run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    rw [exec_RTYPE_pure_bv_to_w_poly _ _ _ is_U64_b is_U64_c]
    simp only [execute_RTYPE_pure_w_poly]
    rw [← h_bop]
    have hp_lt : 2 ^ 17 < p := Fact.out
    have h_pc3 : Main[3].val < 65536 := by
      have h3 : Main[3] < (65536 : ZMod p) := by simp_all
      have : Main[3].val < (65536 : ZMod p).val := h3
      rwa [val_65536_zmod_p] at this
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    by_cases h_is_op_a_0 : Main[6] = 0
    · simp_all
    · simp_all
      have h6_val : Main[6].val ≠ 0 := by
        intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
      have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
        intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
      rw [if_neg h_bv_neq, if_neg h_bv_neq]
      simp [bitVecToRegidxVal]

end Xor

namespace Or

open Bitwise

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 51)
  (s : SailState)

noncomputable def spec_or (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.OR
  pure ()

def sp1_op_a : BitVec 5 := BitVec.ofNat 5 Main[6].val
def sp1_op_b : BitVec 5 := BitVec.ofNat 5 Main[14].val
def sp1_op_c : BitVec 5 := BitVec.ofNat 5 Main[21].val

open Sail

set_option maxHeartbeats 1600000 in
-- BitwiseU16Operation OR-spec_poly bridge plus PC arithmetic exceeds default 200K.
theorem correct_or
  (cstrs : (constraints Main).allHold_poly)
  (h_is_or : is_or_poly Main)
  (state_cstrs : (constraints Main).initialState_poly s) :
  let op_c := sp1_op_c Main
  let op_b := sp1_op_b Main
  let op_a := sp1_op_a Main
  (spec_or (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (Bitwise.sp1_bitwise Main).run s
  := by
    simp [SP1ConstraintList.allHold_poly] at cstrs
    rw [allHold_constraints_iff_poly] at cstrs
    obtain ⟨h_bop, cpu_cstrs, alu_cstrs, b_xor, b_or, b_and, one_of, _h13⟩ := cstrs
    obtain ⟨h_M49, h_imm_c⟩ := h_is_or
    haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    have h_is_real : Main[48] + Main[49] + Main[50] = 1 :=
      sum_eq_one_of_eq_one_mid h_M49 b_xor b_and one_of
    have ⟨h_M48, h_M50⟩ := (single_op_poly Main b_xor b_or b_and h_is_real).2.1 h_M49
    have h4_lt : (4 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    have h4_val : (4 : ZMod p).val = 4 := ZMod.val_natCast_of_lt h4_lt
    rw [CPUState.allHold_constraints_iff_is_real_poly h_is_real] at cpu_cstrs
    rw [ALUTypeReader.allHold_constraints_iff_is_real_poly h_is_real rfl] at alu_cstrs
    simp [h_M48, h_M49, h_M50, Opcode.ofNat, Nat.ble, h4_val, h_imm_c] at alu_cstrs
    obtain ⟨trusted_instr_prop, h_op_a_lt, h_op_b_lt, _h_c_bnds,
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
    have h_or_args : (Main[48] * 2 + Main[49] * 1 + Main[50] * 0 : ZMod p) = 1 := by
      rw [h_M48, h_M49, h_M50]; push_cast; ring
    have h_real_args : Main[48] + Main[49] + Main[50] = (1 : ZMod p) := h_is_real
    rw [h_or_args, h_real_args] at h_bop
    apply BitwiseU16Operation.spec.or_poly is_U64_b is_U64_c at h_bop
    simp [BitwiseU16Operation.constraints, U16toU8OperationUnsafe.constraints,
      BitwiseOperation.constraints] at h_bop
    simp [SP1ConstraintList.initialState_poly, constraints, SP1Constraint.toStateProp,
      List.Forall, BitwiseU16Operation.constraints, U16toU8OperationUnsafe.constraints,
      BitwiseOperation.constraints,
      CPUState.constraints, ALUTypeReader.constraints,
      h6, h14, h21, h_is_real, h_imm_c] at state_cstrs
    obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    simp only [BitVec.ofNatLT_eq_ofNat] at *
    simp [spec_or, Bitwise.sp1_bitwise, execute_RTYPE']
    rw [run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    rw [exec_RTYPE_pure_bv_to_w_poly _ _ _ is_U64_b is_U64_c]
    simp only [execute_RTYPE_pure_w_poly]
    rw [← h_bop]
    have hp_lt : 2 ^ 17 < p := Fact.out
    have h_pc3 : Main[3].val < 65536 := by
      have h3 : Main[3] < (65536 : ZMod p) := by simp_all
      have : Main[3].val < (65536 : ZMod p).val := h3
      rwa [val_65536_zmod_p] at this
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    by_cases h_is_op_a_0 : Main[6] = 0
    · simp_all
    · simp_all
      have h6_val : Main[6].val ≠ 0 := by
        intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
      have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
        intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
      rw [if_neg h_bv_neq, if_neg h_bv_neq]
      simp [bitVecToRegidxVal]

end Or

namespace And

open Bitwise

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 51)
  (s : SailState)

noncomputable def spec_and (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.AND
  pure ()

def sp1_op_a : BitVec 5 := BitVec.ofNat 5 Main[6].val
def sp1_op_b : BitVec 5 := BitVec.ofNat 5 Main[14].val
def sp1_op_c : BitVec 5 := BitVec.ofNat 5 Main[21].val

open Sail

set_option maxHeartbeats 1600000 in
-- BitwiseU16Operation AND-spec_poly bridge plus PC arithmetic exceeds default 200K.
theorem correct_and
  (cstrs : (constraints Main).allHold_poly)
  (h_is_and : is_and_poly Main)
  (state_cstrs : (constraints Main).initialState_poly s) :
  let op_c := sp1_op_c Main
  let op_b := sp1_op_b Main
  let op_a := sp1_op_a Main
  (spec_and (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (Bitwise.sp1_bitwise Main).run s
  := by
    simp [SP1ConstraintList.allHold_poly] at cstrs
    rw [allHold_constraints_iff_poly] at cstrs
    obtain ⟨h_bop, cpu_cstrs, alu_cstrs, b_xor, b_or, b_and, one_of, _h13⟩ := cstrs
    obtain ⟨h_M50, h_imm_c⟩ := h_is_and
    haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    have h_is_real : Main[48] + Main[49] + Main[50] = 1 :=
      sum_eq_one_of_eq_one_right h_M50 b_xor b_or one_of
    have ⟨h_M48, h_M49⟩ := (single_op_poly Main b_xor b_or b_and h_is_real).2.2 h_M50
    have h5_lt : (5 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    have h5_val : (5 : ZMod p).val = 5 := ZMod.val_natCast_of_lt h5_lt
    rw [CPUState.allHold_constraints_iff_is_real_poly h_is_real] at cpu_cstrs
    rw [ALUTypeReader.allHold_constraints_iff_is_real_poly h_is_real rfl] at alu_cstrs
    simp [h_M48, h_M49, h_M50, Opcode.ofNat, Nat.ble, h5_val, h_imm_c] at alu_cstrs
    obtain ⟨trusted_instr_prop, h_op_a_lt, h_op_b_lt, _h_c_bnds,
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
    have h_and_args : (Main[48] * 2 + Main[49] * 1 + Main[50] * 0 : ZMod p) = 0 := by
      rw [h_M48, h_M49, h_M50]; push_cast; ring
    have h_real_args : Main[48] + Main[49] + Main[50] = (1 : ZMod p) := h_is_real
    rw [h_and_args, h_real_args] at h_bop
    apply BitwiseU16Operation.spec.and_poly is_U64_b is_U64_c at h_bop
    simp [BitwiseU16Operation.constraints, U16toU8OperationUnsafe.constraints,
      BitwiseOperation.constraints] at h_bop
    simp [SP1ConstraintList.initialState_poly, constraints, SP1Constraint.toStateProp,
      List.Forall, BitwiseU16Operation.constraints, U16toU8OperationUnsafe.constraints,
      BitwiseOperation.constraints,
      CPUState.constraints, ALUTypeReader.constraints,
      h6, h14, h21, h_is_real, h_imm_c] at state_cstrs
    obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    simp only [BitVec.ofNatLT_eq_ofNat] at *
    simp [spec_and, Bitwise.sp1_bitwise, execute_RTYPE']
    rw [run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    rw [exec_RTYPE_pure_bv_to_w_poly _ _ _ is_U64_b is_U64_c]
    simp only [execute_RTYPE_pure_w_poly]
    rw [← h_bop]
    have hp_lt : 2 ^ 17 < p := Fact.out
    have h_pc3 : Main[3].val < 65536 := by
      have h3 : Main[3] < (65536 : ZMod p) := by simp_all
      have : Main[3].val < (65536 : ZMod p).val := h3
      rwa [val_65536_zmod_p] at this
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    by_cases h_is_op_a_0 : Main[6] = 0
    · simp_all
    · simp_all
      have h6_val : Main[6].val ≠ 0 := by
        intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
      have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
        intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
      rw [if_neg h_bv_neq, if_neg h_bv_neq]
      simp [bitVecToRegidxVal]

end And

namespace Xori

open Bitwise

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 51)
  (s : SailState)

noncomputable def spec_xori (imm : BitVec 12) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_ITYPE imm rs1 rd iop.XORI
  pure ()

def sp1_op_a : BitVec 5 := BitVec.ofNat 5 Main[6].val
def sp1_op_b : BitVec 5 := BitVec.ofNat 5 Main[14].val
def sp1_op_c : BitVec 12 := BitVec.ofNat 12 Main[21].val

open Sail

set_option maxHeartbeats 1600000 in
-- I-type signExtend bridge plus BitwiseU16Operation spec_poly chain.
theorem correct_xori
  (cstrs : (constraints Main).allHold_poly)
  (h_is_xori : is_xori_poly Main)
  (state_cstrs : (constraints Main).initialState_poly s) :
  let op_c := sp1_op_c Main
  let op_b := sp1_op_b Main
  let op_a := sp1_op_a Main
  (spec_xori op_c (.Regidx op_b) (.Regidx op_a)).run s = (Bitwise.sp1_bitwise Main).run s
  := by
    simp [SP1ConstraintList.allHold_poly] at cstrs
    rw [allHold_constraints_iff_poly] at cstrs
    obtain ⟨h_bop, cpu_cstrs, alu_cstrs, b_xor, b_or, b_and, one_of, _h13⟩ := cstrs
    obtain ⟨h_M48, h_imm_c⟩ := h_is_xori
    haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    have h_is_real : Main[48] + Main[49] + Main[50] = 1 :=
      sum_eq_one_of_eq_one_left h_M48 b_or b_and one_of
    have ⟨h_M49, h_M50⟩ := (single_op_poly Main b_xor b_or b_and h_is_real).1 h_M48
    have h3_lt : (3 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    have h3_val : (3 : ZMod p).val = 3 := ZMod.val_natCast_of_lt h3_lt
    rw [CPUState.allHold_constraints_iff_is_real_poly h_is_real] at cpu_cstrs
    rw [ALUTypeReader.allHold_constraints_iff_is_real_poly h_is_real rfl] at alu_cstrs
    simp [h_M48, h_M49, h_M50, Opcode.ofNat, Nat.ble, h3_val, h_imm_c] at alu_cstrs
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
    have h_op_c_imm_isU64 : Word.isU64_poly #v[Main[25], Main[26], Main[27], Main[28]] := by
      rw [h25_eq, h26_eq, h27_eq, h28_eq]
      exact Word.isU64_of_cases_poly h21 h22 h23 h24
    obtain ⟨h_f, h_imm_c_consts⟩ := trusted_instr_prop
    have h_xor_args : (Main[48] * 2 + Main[49] * 1 + Main[50] * 0 : ZMod p) = 2 := by
      rw [h_M48, h_M49, h_M50]; push_cast; ring
    have h_real_args : Main[48] + Main[49] + Main[50] = (1 : ZMod p) := h_is_real
    rw [h_xor_args, h_real_args] at h_bop
    apply BitwiseU16Operation.spec.xor_poly is_U64_b h_op_c_imm_isU64 at h_bop
    simp [BitwiseU16Operation.constraints, U16toU8OperationUnsafe.constraints,
      BitwiseOperation.constraints] at h_bop
    simp [SP1ConstraintList.initialState_poly, constraints, SP1Constraint.toStateProp,
      List.Forall, BitwiseU16Operation.constraints, U16toU8OperationUnsafe.constraints,
      BitwiseOperation.constraints,
      CPUState.constraints, ALUTypeReader.constraints,
      h6, h14, h_is_real, h_imm_c] at state_cstrs
    obtain ⟨read_pc, _read_op_a, read_op_b⟩ := state_cstrs
    simp only [BitVec.ofNatLT_eq_ofNat] at *
    simp [spec_xori, Bitwise.sp1_bitwise, execute_ITYPE']
    rw [run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b]
    have h_signExt_eq :
        signExtend 64 (BitVec.ofNat 12 Main[21].val) =
          Word.toBitVec64 #v[Main[25], Main[26], Main[27], Main[28]] := by
      rw [h25_eq, h26_eq, h27_eq, h28_eq, ← h_imm_c_consts]
    rw [h_signExt_eq]
    rw [exec_ITYPE_pure_bv_to_w_poly _ _ _ is_U64_b h_op_c_imm_isU64]
    simp only [execute_ITYPE_pure_w_poly, execute_RTYPE_pure_w_poly]
    rw [← h_bop]
    have hp_lt : 2 ^ 17 < p := Fact.out
    have h_pc3 : Main[3].val < 65536 := by
      have h3 : Main[3] < (65536 : ZMod p) := by simp_all
      have : Main[3].val < (65536 : ZMod p).val := h3
      rwa [val_65536_zmod_p] at this
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    by_cases h_is_op_a_0 : Main[6] = 0
    · simp_all
    · simp_all
      have h6_val : Main[6].val ≠ 0 := by
        intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
      have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
        intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
      rw [if_neg h_bv_neq, if_neg h_bv_neq]
      simp [bitVecToRegidxVal]

end Xori

namespace Ori

open Bitwise

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 51)
  (s : SailState)

noncomputable def spec_ori (imm : BitVec 12) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_ITYPE imm rs1 rd iop.ORI
  pure ()

def sp1_op_a : BitVec 5 := BitVec.ofNat 5 Main[6].val
def sp1_op_b : BitVec 5 := BitVec.ofNat 5 Main[14].val
def sp1_op_c : BitVec 12 := BitVec.ofNat 12 Main[21].val

open Sail

set_option maxHeartbeats 1600000 in
-- I-type ORI variant: signExtend bridge + spec.or_poly bridge.
theorem correct_ori
  (cstrs : (constraints Main).allHold_poly)
  (h_is_ori : is_ori_poly Main)
  (state_cstrs : (constraints Main).initialState_poly s) :
  let op_c := sp1_op_c Main
  let op_b := sp1_op_b Main
  let op_a := sp1_op_a Main
  (spec_ori op_c (.Regidx op_b) (.Regidx op_a)).run s = (Bitwise.sp1_bitwise Main).run s
  := by
    simp [SP1ConstraintList.allHold_poly] at cstrs
    rw [allHold_constraints_iff_poly] at cstrs
    obtain ⟨h_bop, cpu_cstrs, alu_cstrs, b_xor, b_or, b_and, one_of, _h13⟩ := cstrs
    obtain ⟨h_M49, h_imm_c⟩ := h_is_ori
    haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    have h_is_real : Main[48] + Main[49] + Main[50] = 1 :=
      sum_eq_one_of_eq_one_mid h_M49 b_xor b_and one_of
    have ⟨h_M48, h_M50⟩ := (single_op_poly Main b_xor b_or b_and h_is_real).2.1 h_M49
    have h4_lt : (4 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    have h4_val : (4 : ZMod p).val = 4 := ZMod.val_natCast_of_lt h4_lt
    rw [CPUState.allHold_constraints_iff_is_real_poly h_is_real] at cpu_cstrs
    rw [ALUTypeReader.allHold_constraints_iff_is_real_poly h_is_real rfl] at alu_cstrs
    simp [h_M48, h_M49, h_M50, Opcode.ofNat, Nat.ble, h4_val, h_imm_c] at alu_cstrs
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
    have h_op_c_imm_isU64 : Word.isU64_poly #v[Main[25], Main[26], Main[27], Main[28]] := by
      rw [h25_eq, h26_eq, h27_eq, h28_eq]
      exact Word.isU64_of_cases_poly h21 h22 h23 h24
    obtain ⟨h_f, h_imm_c_consts⟩ := trusted_instr_prop
    have h_or_args : (Main[48] * 2 + Main[49] * 1 + Main[50] * 0 : ZMod p) = 1 := by
      rw [h_M48, h_M49, h_M50]; push_cast; ring
    have h_real_args : Main[48] + Main[49] + Main[50] = (1 : ZMod p) := h_is_real
    rw [h_or_args, h_real_args] at h_bop
    apply BitwiseU16Operation.spec.or_poly is_U64_b h_op_c_imm_isU64 at h_bop
    simp [BitwiseU16Operation.constraints, U16toU8OperationUnsafe.constraints,
      BitwiseOperation.constraints] at h_bop
    simp [SP1ConstraintList.initialState_poly, constraints, SP1Constraint.toStateProp,
      List.Forall, BitwiseU16Operation.constraints, U16toU8OperationUnsafe.constraints,
      BitwiseOperation.constraints,
      CPUState.constraints, ALUTypeReader.constraints,
      h6, h14, h_is_real, h_imm_c] at state_cstrs
    obtain ⟨read_pc, _read_op_a, read_op_b⟩ := state_cstrs
    simp only [BitVec.ofNatLT_eq_ofNat] at *
    simp [spec_ori, Bitwise.sp1_bitwise, execute_ITYPE']
    rw [run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b]
    have h_signExt_eq :
        signExtend 64 (BitVec.ofNat 12 Main[21].val) =
          Word.toBitVec64 #v[Main[25], Main[26], Main[27], Main[28]] := by
      rw [h25_eq, h26_eq, h27_eq, h28_eq, ← h_imm_c_consts]
    rw [h_signExt_eq]
    rw [exec_ITYPE_pure_bv_to_w_poly _ _ _ is_U64_b h_op_c_imm_isU64]
    simp only [execute_ITYPE_pure_w_poly, execute_RTYPE_pure_w_poly]
    rw [← h_bop]
    have hp_lt : 2 ^ 17 < p := Fact.out
    have h_pc3 : Main[3].val < 65536 := by
      have h3 : Main[3] < (65536 : ZMod p) := by simp_all
      have : Main[3].val < (65536 : ZMod p).val := h3
      rwa [val_65536_zmod_p] at this
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    by_cases h_is_op_a_0 : Main[6] = 0
    · simp_all
    · simp_all
      have h6_val : Main[6].val ≠ 0 := by
        intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
      have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
        intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
      rw [if_neg h_bv_neq, if_neg h_bv_neq]
      simp [bitVecToRegidxVal]

end Ori

namespace Andi

open Bitwise

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 51)
  (s : SailState)

noncomputable def spec_andi (imm : BitVec 12) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_ITYPE imm rs1 rd iop.ANDI
  pure ()

def sp1_op_a : BitVec 5 := BitVec.ofNat 5 Main[6].val
def sp1_op_b : BitVec 5 := BitVec.ofNat 5 Main[14].val
def sp1_op_c : BitVec 12 := BitVec.ofNat 12 Main[21].val

open Sail

set_option maxHeartbeats 1600000 in
-- I-type ANDI variant: signExtend bridge + spec.and_poly bridge.
theorem correct_andi
  (cstrs : (constraints Main).allHold_poly)
  (h_is_andi : is_andi_poly Main)
  (state_cstrs : (constraints Main).initialState_poly s) :
  let op_c := sp1_op_c Main
  let op_b := sp1_op_b Main
  let op_a := sp1_op_a Main
  (spec_andi op_c (.Regidx op_b) (.Regidx op_a)).run s = (Bitwise.sp1_bitwise Main).run s
  := by
    simp [SP1ConstraintList.allHold_poly] at cstrs
    rw [allHold_constraints_iff_poly] at cstrs
    obtain ⟨h_bop, cpu_cstrs, alu_cstrs, b_xor, b_or, b_and, one_of, _h13⟩ := cstrs
    obtain ⟨h_M50, h_imm_c⟩ := h_is_andi
    haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    have h_is_real : Main[48] + Main[49] + Main[50] = 1 :=
      sum_eq_one_of_eq_one_right h_M50 b_xor b_or one_of
    have ⟨h_M48, h_M49⟩ := (single_op_poly Main b_xor b_or b_and h_is_real).2.2 h_M50
    have h5_lt : (5 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    have h5_val : (5 : ZMod p).val = 5 := ZMod.val_natCast_of_lt h5_lt
    rw [CPUState.allHold_constraints_iff_is_real_poly h_is_real] at cpu_cstrs
    rw [ALUTypeReader.allHold_constraints_iff_is_real_poly h_is_real rfl] at alu_cstrs
    simp [h_M48, h_M49, h_M50, Opcode.ofNat, Nat.ble, h5_val, h_imm_c] at alu_cstrs
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
    have h_op_c_imm_isU64 : Word.isU64_poly #v[Main[25], Main[26], Main[27], Main[28]] := by
      rw [h25_eq, h26_eq, h27_eq, h28_eq]
      exact Word.isU64_of_cases_poly h21 h22 h23 h24
    obtain ⟨h_f, h_imm_c_consts⟩ := trusted_instr_prop
    have h_and_args : (Main[48] * 2 + Main[49] * 1 + Main[50] * 0 : ZMod p) = 0 := by
      rw [h_M48, h_M49, h_M50]; push_cast; ring
    have h_real_args : Main[48] + Main[49] + Main[50] = (1 : ZMod p) := h_is_real
    rw [h_and_args, h_real_args] at h_bop
    apply BitwiseU16Operation.spec.and_poly is_U64_b h_op_c_imm_isU64 at h_bop
    simp [BitwiseU16Operation.constraints, U16toU8OperationUnsafe.constraints,
      BitwiseOperation.constraints] at h_bop
    simp [SP1ConstraintList.initialState_poly, constraints, SP1Constraint.toStateProp,
      List.Forall, BitwiseU16Operation.constraints, U16toU8OperationUnsafe.constraints,
      BitwiseOperation.constraints,
      CPUState.constraints, ALUTypeReader.constraints,
      h6, h14, h_is_real, h_imm_c] at state_cstrs
    obtain ⟨read_pc, _read_op_a, read_op_b⟩ := state_cstrs
    simp only [BitVec.ofNatLT_eq_ofNat] at *
    simp [spec_andi, Bitwise.sp1_bitwise, execute_ITYPE']
    rw [run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b]
    have h_signExt_eq :
        signExtend 64 (BitVec.ofNat 12 Main[21].val) =
          Word.toBitVec64 #v[Main[25], Main[26], Main[27], Main[28]] := by
      rw [h25_eq, h26_eq, h27_eq, h28_eq, ← h_imm_c_consts]
    rw [h_signExt_eq]
    rw [exec_ITYPE_pure_bv_to_w_poly _ _ _ is_U64_b h_op_c_imm_isU64]
    simp only [execute_ITYPE_pure_w_poly, execute_RTYPE_pure_w_poly]
    rw [← h_bop]
    have hp_lt : 2 ^ 17 < p := Fact.out
    have h_pc3 : Main[3].val < 65536 := by
      have h3 : Main[3] < (65536 : ZMod p) := by simp_all
      have : Main[3].val < (65536 : ZMod p).val := h3
      rwa [val_65536_zmod_p] at this
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    by_cases h_is_op_a_0 : Main[6] = 0
    · simp_all
    · simp_all
      have h6_val : Main[6].val ≠ 0 := by
        intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
      have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
        intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
      rw [if_neg h_bv_neq, if_neg h_bv_neq]
      simp [bitVecToRegidxVal]

end Andi
