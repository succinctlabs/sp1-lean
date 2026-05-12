import SP1Operations.Operation.AddOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ITypeReader
import SP1Chips.Addi.Constraints

import SP1Chips.Add.Constraints

open LeanRV64D.Functions BitVec

namespace Addi

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 30)
  (s : SailState)

noncomputable def spec_addi (imm : BitVec 12) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_ITYPE imm rs1 rd iop.ADDI
  pure ()

def sp1_op_a : BitVec 5 := BitVec.ofNat 5 Main[6].val

def sp1_op_b : BitVec 5 := BitVec.ofNat 5 Main[14].val

def sp1_op_c : BitVec 12 := BitVec.ofNat 12 Main[21].val

def sp1_addi : SailM Unit := do
  let op_a := sp1_op_a Main
  Sail.writeReg Register.nextPC (Word.toBitVec64_poly #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64_poly #v[Main[25], Main[26], Main[27], Main[28]])

open Sail

theorem correct_addi
  (cstrs : (constraints Main).allHold_poly)
  (h_is_real : Main[29] = 1)
  (state_cstrs : (constraints Main).initialState_poly s) :
  let op_c := sp1_op_c Main
  let op_b := sp1_op_b Main
  let op_a := sp1_op_a Main
  (spec_addi op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_addi Main).run s
  := by
    simp [constraints] at cstrs
    obtain ⟨add_op_cstrs, cpu_cstrs, reader_cstrs, _⟩ := cstrs
    haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    haveI hp1 : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    have h1_val : (1 : ZMod p).val = 1 := ZMod.val_one p
    rw [CPUState.allHold_constraints_iff_is_real_poly h_is_real] at cpu_cstrs
    simp [ITypeReader.allHold_constraints_iff_is_real_poly h_is_real h_is_real,
      Opcode.ofNat, Nat.ble, h1_val] at reader_cstrs
    obtain ⟨trusted_instr_prop, h_op_a_lt, h_op_b_lt, c0, c1, c2, c3,
            _h_a0_bool, h_a0_iff,
            _pc_mod, _h3_lt, _h4_lt, _h5_lt,
            _h12_lt, _h20_lt, _h_clk_b, _h_clk_a,
            _is_U64_a, is_U64_b, h_op_a_0_zero⟩ := reader_cstrs
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
    have h_op_c_imm_isU64 : Word.isU64_poly #v[Main[21], Main[22], Main[23], Main[24]] :=
      Word.isU64_of_cases_poly h21 h22 h23 h24
    simp [SP1ConstraintList.initialState_poly, constraints, SP1Constraint.toStateProp_poly,
      List.Forall, AddOperation.constraints, CPUState.constraints, ITypeReader.constraints,
      h6, h14, h_is_real] at state_cstrs
    obtain ⟨read_pc, read_op_b, read_op_c⟩ := state_cstrs
    rw [h_is_real] at *
    apply AddOperation.spec_poly is_U64_b h_op_c_imm_isU64 at add_op_cstrs
    obtain ⟨is_U64_val, is_add⟩ := add_op_cstrs
    simp [BitVec.ofNatLT_eq_ofNat] at *
    -- Now the monadic manipulation
    simp [spec_addi, sp1_addi, execute_ITYPE']
    rw [run_readReg, read_pc]
    simp [sp1_op_b]
    simp [sp1_op_c, read_op_c]
    simp [sp1_op_a]
    by_cases h_is_op_a_0 : Main[6] = 0
    · simp_all
    · simp_all
      have h6_val : Main[6].val ≠ 0 := by
        intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
      rw [if_neg (by simp [← BitVec.toNat_inj]; omega)]
      rw [if_neg (by simp [← BitVec.toNat_inj]; omega)]
      -- Push the signExtend immediate back to toBitVec64_poly form, then bridge
      -- via exec_ITYPE_pure_bv_to_w_poly so the spec's execute reduces to the
      -- same sum form the SP1 side already has (`is_add` was applied via
      -- simp_all to rewrite the result limbs).
      rw [← trusted_instr_prop.2]
      rw [exec_ITYPE_pure_bv_to_w_poly _ _ _ is_U64_b h_op_c_imm_isU64]
      simp only [execute_ITYPE_pure_w_poly, execute_RTYPE_pure_w_poly, rop_of_iop]
      -- Bridge `+ 4#64` to limb-0 addition via the generic helper.
      have hp_lt : 2 ^ 17 < p := Fact.out
      have h_pc3 : Main[3].val < 65536 := by
        have h3 : Main[3] < (65536 : ZMod p) := by simp_all
        have : Main[3].val < (65536 : ZMod p).val := h3
        rwa [val_65536_zmod_p] at this
      rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
          Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
          show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
      simp [bitVecToRegidxVal]

end Addi
