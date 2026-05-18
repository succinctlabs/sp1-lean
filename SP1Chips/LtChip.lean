import SP1Foundations
import SP1Operations.Compare.LtOperationSigned
import SP1Operations.Compare.LtOperationUnsigned
import SP1Operations.Compare.U16CompareOperation
import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader
import SP1Chips.Lt.Constraints

open LeanRV64D.Functions BitVec

namespace Lt

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 44)

-- Unified SP1 implementation for the Lt chip. All four variants (slt, sltu,
-- slti, sltiu) write the same Main result columns to op_a; the chip's
-- constraints determine which Sail spec those columns implement.
def sp1_lt : SailM Unit := do
  let op_a : BitVec 5 := BitVec.ofNat 5 Main[6].val
  Sail.writeReg Register.nextPC (Word.toBitVec64_poly #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64_poly #v[Main[34], 0, 0, 0])

end Lt

namespace Slt

open Lt

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 44)
  (s : SailState)

noncomputable def spec_slt (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.SLT
  pure ()

def sp1_op_a : BitVec 5 := BitVec.ofNat 5 Main[6].val

def sp1_op_b : BitVec 5 := BitVec.ofNat 5 Main[14].val

def sp1_op_c : BitVec 5 := BitVec.ofNat 5 Main[21].val

open Sail

set_option maxHeartbeats 1600000 in
-- The signed/unsigned bridge plus PC-arithmetic exceeds the default 200K
-- budget; matches Sub/Add chip recipes where we elevate.
theorem correct_slt
  (cstrs : (constraints Main).allHold_poly)
  (h_is_slt : is_slt_poly Main)
  (state_cstrs : (constraints Main).initialState_poly s) :
  let op_c := sp1_op_c Main
  let op_b := sp1_op_b Main
  let op_a := sp1_op_a Main
  (spec_slt (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (Lt.sp1_lt Main).run s
  := by
    simp [SP1ConstraintList.allHold_poly] at cstrs
    rw [allHold_constraints_iff_slt_poly Main h_is_slt] at cstrs
    obtain ⟨lt_op_cstrs, cpu_cstrs, alu_cstrs, h_M33, _h13⟩ := cstrs
    obtain ⟨h_M32, h_imm_c⟩ := h_is_slt
    haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    have h_is_real : Main[32] + Main[33] = 1 := by rw [h_M32, h_M33]; ring
    have h9_lt : (9 : ℕ) < p := by
      have h2 := Fact.out (p := 2 ^ 17 < p)
      have h_dec : (9 : ℕ) < 2 ^ 17 := by decide
      omega
    have h9_val : (9 : ZMod p).val = 9 := ZMod.val_natCast_of_lt h9_lt
    rw [CPUState.allHold_constraints_iff_is_real_poly h_is_real] at cpu_cstrs
    rw [ALUTypeReader.allHold_constraints_iff_is_real_poly h_is_real rfl] at alu_cstrs
    simp [h_M32, h_M33, Opcode.ofNat, Nat.ble, h9_val, h_imm_c] at alu_cstrs
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
    simp [SP1ConstraintList.initialState_poly, constraints, SP1Constraint.toStateProp_poly,
      List.Forall, LtOperationSigned.constraints, LtOperationUnsigned.constraints,
      U16MSBOperation.constraints, U16CompareOperation.constraints,
      CPUState.constraints, ALUTypeReader.constraints,
      h6, h14, h21, h_is_real, h_imm_c] at state_cstrs
    obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    -- LtOperationSigned consumes is_signed=Main[32]=1, is_real=Main[32]+Main[33]=1
    rw [h_M32, h_M33] at lt_op_cstrs
    rw [show (1 : ZMod p) + 0 = 1 from by ring] at lt_op_cstrs
    apply LtOperationSigned.spec.signed_poly is_U64_b is_U64_c at lt_op_cstrs
    -- Goal: bridge cols.bit (= Main[34]) ↔ if/then/else result
    simp only [BitVec.ofNatLT_eq_ofNat] at *
    -- Now the monadic manipulation
    simp [spec_slt, Lt.sp1_lt, execute_RTYPE']
    rw [run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    by_cases h_is_op_a_0 : Main[6] = 0
    · simp_all
    · simp_all
      have h6_val : Main[6].val ≠ 0 := by
        intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
      have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
        intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
      rw [if_neg h_bv_neq, if_neg h_bv_neq]
      rw [exec_RTYPE_pure_bv_to_w_poly _ _ _ is_U64_b is_U64_c]
      simp only [execute_RTYPE_pure_w_poly]
      -- PC arithmetic: bridge `+ 4#64` to `Main[3] + 4` low-limb form
      have hp_lt : 2 ^ 17 < p := Fact.out
      have h_pc3 : Main[3].val < 65536 := by
        have h3 : Main[3] < (65536 : ZMod p) := by simp_all
        have : Main[3].val < (65536 : ZMod p).val := h3
        rwa [val_65536_zmod_p] at this
      rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
          Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
          show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
      -- Bridge: Word.toBitVec64_poly #v[(if cond then 1 else 0), 0, 0, 0] = if cond then 1#64 else 0#64
      rw [show Word.toBitVec64_poly (p := p)
              #v[(if Word.toInt_poly #v[Main[15], Main[16], Main[17], Main[18]] <
                       Word.toInt_poly #v[Main[25], Main[26], Main[27], Main[28]] then
                    (1 : ZMod p) else 0), 0, 0, 0]
                = if Word.toInt_poly #v[Main[15], Main[16], Main[17], Main[18]] <
                       Word.toInt_poly #v[Main[25], Main[26], Main[27], Main[28]] then
                    1#64 else 0#64 from by
            split_ifs <;>
              simp [Word.toBitVec64_poly, Word.toNat_poly_def, ZMod.val_one, ZMod.val_zero]]
      simp [bitVecToRegidxVal]

end Slt

namespace Sltu

open Lt

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 44)
  (s : SailState)

noncomputable def spec_sltu (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.SLTU
  pure ()

def sp1_op_a : BitVec 5 := BitVec.ofNat 5 Main[6].val
def sp1_op_b : BitVec 5 := BitVec.ofNat 5 Main[14].val
def sp1_op_c : BitVec 5 := BitVec.ofNat 5 Main[21].val

open Sail

set_option maxHeartbeats 1600000 in
-- The unsigned-comparison spec bridge plus PC arithmetic exceeds the default
-- 200K budget; matches Slt's elevation.
theorem correct_sltu
  (cstrs : (constraints Main).allHold_poly)
  (h_is_sltu : is_sltu_poly Main)
  (state_cstrs : (constraints Main).initialState_poly s) :
  let op_c := sp1_op_c Main
  let op_b := sp1_op_b Main
  let op_a := sp1_op_a Main
  (spec_sltu (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (Lt.sp1_lt Main).run s
  := by
    simp [SP1ConstraintList.allHold_poly] at cstrs
    rw [allHold_constraints_iff_sltu_poly Main h_is_sltu] at cstrs
    obtain ⟨lt_op_cstrs, cpu_cstrs, alu_cstrs, h_M32, _h13⟩ := cstrs
    obtain ⟨h_M33, h_imm_c⟩ := h_is_sltu
    haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    have h_is_real : Main[32] + Main[33] = 1 := by rw [h_M32, h_M33]; ring
    have h10_lt : (10 : ℕ) < p := by
      have h2 := Fact.out (p := 2 ^ 17 < p)
      have h_dec : (10 : ℕ) < 2 ^ 17 := by decide
      omega
    have h10_val : (10 : ZMod p).val = 10 := ZMod.val_natCast_of_lt h10_lt
    rw [CPUState.allHold_constraints_iff_is_real_poly h_is_real] at cpu_cstrs
    rw [ALUTypeReader.allHold_constraints_iff_is_real_poly h_is_real rfl] at alu_cstrs
    simp [h_M32, h_M33, Opcode.ofNat, Nat.ble, h10_val, h_imm_c] at alu_cstrs
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
    simp [SP1ConstraintList.initialState_poly, constraints, SP1Constraint.toStateProp_poly,
      List.Forall, LtOperationSigned.constraints, LtOperationUnsigned.constraints,
      U16MSBOperation.constraints, U16CompareOperation.constraints,
      CPUState.constraints, ALUTypeReader.constraints,
      h6, h14, h21, h_is_real, h_imm_c] at state_cstrs
    obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    -- LtOperationSigned consumes is_signed=Main[32]=0, is_real=Main[32]+Main[33]=1
    rw [h_M32, h_M33] at lt_op_cstrs
    rw [show (0 : ZMod p) + 1 = 1 from by ring] at lt_op_cstrs
    apply LtOperationSigned.spec.unsigned_poly is_U64_b is_U64_c at lt_op_cstrs
    simp only [BitVec.ofNatLT_eq_ofNat] at *
    simp [spec_sltu, Lt.sp1_lt, execute_RTYPE']
    rw [run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    by_cases h_is_op_a_0 : Main[6] = 0
    · simp_all
    · simp_all
      have h6_val : Main[6].val ≠ 0 := by
        intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
      have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
        intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
      rw [if_neg h_bv_neq, if_neg h_bv_neq]
      rw [exec_RTYPE_pure_bv_to_w_poly _ _ _ is_U64_b is_U64_c]
      simp only [execute_RTYPE_pure_w_poly]
      have hp_lt : 2 ^ 17 < p := Fact.out
      have h_pc3 : Main[3].val < 65536 := by
        have h3 : Main[3] < (65536 : ZMod p) := by simp_all
        have : Main[3].val < (65536 : ZMod p).val := h3
        rwa [val_65536_zmod_p] at this
      rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
          Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
          show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
      rw [show Word.toBitVec64_poly (p := p)
              #v[(if Word.toNat_poly #v[Main[15], Main[16], Main[17], Main[18]] <
                       Word.toNat_poly #v[Main[25], Main[26], Main[27], Main[28]] then
                    (1 : ZMod p) else 0), 0, 0, 0]
                = if Word.toNat_poly #v[Main[15], Main[16], Main[17], Main[18]] <
                       Word.toNat_poly #v[Main[25], Main[26], Main[27], Main[28]] then
                    1#64 else 0#64 from by
            split_ifs <;>
              simp [Word.toBitVec64_poly, Word.toNat_poly_def, ZMod.val_one, ZMod.val_zero]]
      simp [bitVecToRegidxVal]

end Sltu

namespace Slti

open Lt

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 44)
  (s : SailState)

noncomputable def spec_slti (imm : BitVec 12) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_ITYPE imm rs1 rd iop.SLTI
  pure ()

def sp1_op_a : BitVec 5 := BitVec.ofNat 5 Main[6].val
def sp1_op_b : BitVec 5 := BitVec.ofNat 5 Main[14].val
def sp1_op_c : BitVec 12 := BitVec.ofNat 12 Main[21].val

open Sail

set_option maxHeartbeats 1600000 in
-- The signed I-type bridge through the signExtend immediate adds another
-- layer of struct unfolding on top of the spec.signed_poly chain; default
-- 200K budget is insufficient.
theorem correct_slti
  (cstrs : (constraints Main).allHold_poly)
  (h_is_slti : is_slti_poly Main)
  (state_cstrs : (constraints Main).initialState_poly s) :
  let op_c := sp1_op_c Main
  let op_b := sp1_op_b Main
  let op_a := sp1_op_a Main
  (spec_slti op_c (.Regidx op_b) (.Regidx op_a)).run s = (Lt.sp1_lt Main).run s
  := by
    simp [SP1ConstraintList.allHold_poly] at cstrs
    rw [allHold_constraints_iff_slti_poly Main h_is_slti] at cstrs
    obtain ⟨lt_op_cstrs, cpu_cstrs, alu_cstrs, h_M33, _h13⟩ := cstrs
    obtain ⟨h_M32, h_imm_c⟩ := h_is_slti
    haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    have h_is_real : Main[32] + Main[33] = 1 := by rw [h_M32, h_M33]; ring
    have h9_lt : (9 : ℕ) < p := by
      have h2 := Fact.out (p := 2 ^ 17 < p)
      have h_dec : (9 : ℕ) < 2 ^ 17 := by decide
      omega
    have h9_val : (9 : ZMod p).val = 9 := ZMod.val_natCast_of_lt h9_lt
    rw [CPUState.allHold_constraints_iff_is_real_poly h_is_real] at cpu_cstrs
    rw [ALUTypeReader.allHold_constraints_iff_is_real_poly h_is_real rfl] at alu_cstrs
    simp [h_M32, h_M33, Opcode.ofNat, Nat.ble, h9_val, h_imm_c] at alu_cstrs
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
    simp [SP1ConstraintList.initialState_poly, constraints, SP1Constraint.toStateProp_poly,
      List.Forall, LtOperationSigned.constraints, LtOperationUnsigned.constraints,
      U16MSBOperation.constraints, U16CompareOperation.constraints,
      CPUState.constraints, ALUTypeReader.constraints,
      h6, h14, h_is_real, h_imm_c] at state_cstrs
    obtain ⟨read_pc, _read_op_a, read_op_b⟩ := state_cstrs
    rw [h_M32, h_M33] at lt_op_cstrs
    rw [show (1 : ZMod p) + 0 = 1 from by ring] at lt_op_cstrs
    apply LtOperationSigned.spec.signed_poly is_U64_b h_op_c_imm_isU64 at lt_op_cstrs
    simp only [BitVec.ofNatLT_eq_ofNat] at *
    simp [spec_slti, Lt.sp1_lt, execute_ITYPE']
    rw [run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b]
    -- Bridge: signExtend 64 (BitVec.ofNat 12 op_c) = toBitVec64_poly #v[Main[25..28]]
    have h_signExt_eq :
        signExtend 64 (BitVec.ofNat 12 Main[21].val) =
          Word.toBitVec64_poly #v[Main[25], Main[26], Main[27], Main[28]] := by
      rw [h25_eq, h26_eq, h27_eq, h28_eq, ← h_imm_c_consts]
    rw [h_signExt_eq]
    rw [exec_ITYPE_pure_bv_to_w_poly _ _ _ is_U64_b h_op_c_imm_isU64]
    simp only [execute_ITYPE_pure_w_poly, execute_RTYPE_pure_w_poly]
    by_cases h_is_op_a_0 : Main[6] = 0
    · simp_all
    · simp_all
      have h6_val : Main[6].val ≠ 0 := by
        intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
      have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
        intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
      rw [if_neg h_bv_neq, if_neg h_bv_neq]
      have hp_lt : 2 ^ 17 < p := Fact.out
      have h_pc3 : Main[3].val < 65536 := by
        have h3 : Main[3] < (65536 : ZMod p) := by simp_all
        have : Main[3].val < (65536 : ZMod p).val := h3
        rwa [val_65536_zmod_p] at this
      rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
          Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
          show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
      rw [show Word.toBitVec64_poly (p := p)
              #v[(if Word.toInt_poly #v[Main[15], Main[16], Main[17], Main[18]] <
                       Word.toInt_poly #v[Main[21], Main[22], Main[23], Main[24]] then
                    (1 : ZMod p) else 0), 0, 0, 0]
                = if Word.toInt_poly #v[Main[15], Main[16], Main[17], Main[18]] <
                       Word.toInt_poly #v[Main[21], Main[22], Main[23], Main[24]] then
                    1#64 else 0#64 from by
            split_ifs <;>
              simp [Word.toBitVec64_poly, Word.toNat_poly_def, ZMod.val_one, ZMod.val_zero]]
      simp [bitVecToRegidxVal]

end Slti

namespace Sltiu

open Lt

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 44)
  (s : SailState)

noncomputable def spec_sltiu (imm : BitVec 12) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_ITYPE imm rs1 rd iop.SLTIU
  pure ()

def sp1_op_a : BitVec 5 := BitVec.ofNat 5 Main[6].val
def sp1_op_b : BitVec 5 := BitVec.ofNat 5 Main[14].val
def sp1_op_c : BitVec 12 := BitVec.ofNat 12 Main[21].val

open Sail

set_option maxHeartbeats 1600000 in
-- Unsigned I-type variant: signExtend immediate bridge + spec.unsigned_poly
-- chain pushes elaboration above the default 200K budget.
theorem correct_sltiu
  (cstrs : (constraints Main).allHold_poly)
  (h_is_sltiu : is_sltiu_poly Main)
  (state_cstrs : (constraints Main).initialState_poly s) :
  let op_c := sp1_op_c Main
  let op_b := sp1_op_b Main
  let op_a := sp1_op_a Main
  (spec_sltiu op_c (.Regidx op_b) (.Regidx op_a)).run s = (Lt.sp1_lt Main).run s
  := by
    simp [SP1ConstraintList.allHold_poly] at cstrs
    rw [allHold_constraints_iff_sltiu_poly Main h_is_sltiu] at cstrs
    obtain ⟨lt_op_cstrs, cpu_cstrs, alu_cstrs, h_M32, _h13⟩ := cstrs
    obtain ⟨h_M33, h_imm_c⟩ := h_is_sltiu
    haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    have h_is_real : Main[32] + Main[33] = 1 := by rw [h_M32, h_M33]; ring
    have h10_lt : (10 : ℕ) < p := by
      have h2 := Fact.out (p := 2 ^ 17 < p)
      have h_dec : (10 : ℕ) < 2 ^ 17 := by decide
      omega
    have h10_val : (10 : ZMod p).val = 10 := ZMod.val_natCast_of_lt h10_lt
    rw [CPUState.allHold_constraints_iff_is_real_poly h_is_real] at cpu_cstrs
    rw [ALUTypeReader.allHold_constraints_iff_is_real_poly h_is_real rfl] at alu_cstrs
    simp [h_M32, h_M33, Opcode.ofNat, Nat.ble, h10_val, h_imm_c] at alu_cstrs
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
    simp [SP1ConstraintList.initialState_poly, constraints, SP1Constraint.toStateProp_poly,
      List.Forall, LtOperationSigned.constraints, LtOperationUnsigned.constraints,
      U16MSBOperation.constraints, U16CompareOperation.constraints,
      CPUState.constraints, ALUTypeReader.constraints,
      h6, h14, h_is_real, h_imm_c] at state_cstrs
    obtain ⟨read_pc, _read_op_a, read_op_b⟩ := state_cstrs
    rw [h_M32, h_M33] at lt_op_cstrs
    rw [show (0 : ZMod p) + 1 = 1 from by ring] at lt_op_cstrs
    apply LtOperationSigned.spec.unsigned_poly is_U64_b h_op_c_imm_isU64 at lt_op_cstrs
    simp only [BitVec.ofNatLT_eq_ofNat] at *
    simp [spec_sltiu, Lt.sp1_lt, execute_ITYPE']
    rw [run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b]
    have h_signExt_eq :
        signExtend 64 (BitVec.ofNat 12 Main[21].val) =
          Word.toBitVec64_poly #v[Main[25], Main[26], Main[27], Main[28]] := by
      rw [h25_eq, h26_eq, h27_eq, h28_eq, ← h_imm_c_consts]
    rw [h_signExt_eq]
    rw [exec_ITYPE_pure_bv_to_w_poly _ _ _ is_U64_b h_op_c_imm_isU64]
    simp only [execute_ITYPE_pure_w_poly, execute_RTYPE_pure_w_poly]
    by_cases h_is_op_a_0 : Main[6] = 0
    · simp_all
    · simp_all
      have h6_val : Main[6].val ≠ 0 := by
        intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
      have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
        intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
      rw [if_neg h_bv_neq, if_neg h_bv_neq]
      have hp_lt : 2 ^ 17 < p := Fact.out
      have h_pc3 : Main[3].val < 65536 := by
        have h3 : Main[3] < (65536 : ZMod p) := by simp_all
        have : Main[3].val < (65536 : ZMod p).val := h3
        rwa [val_65536_zmod_p] at this
      rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
          Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
          show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
      rw [show Word.toBitVec64_poly (p := p)
              #v[(if Word.toNat_poly #v[Main[15], Main[16], Main[17], Main[18]] <
                       Word.toNat_poly #v[Main[21], Main[22], Main[23], Main[24]] then
                    (1 : ZMod p) else 0), 0, 0, 0]
                = if Word.toNat_poly #v[Main[15], Main[16], Main[17], Main[18]] <
                       Word.toNat_poly #v[Main[21], Main[22], Main[23], Main[24]] then
                    1#64 else 0#64 from by
            split_ifs <;>
              simp [Word.toBitVec64_poly, Word.toNat_poly_def, ZMod.val_one, ZMod.val_zero]]
      simp [bitVecToRegidxVal]

end Sltiu
