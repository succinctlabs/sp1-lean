import SP1Foundations
import SP1Operations.Operation.SubOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.RTypeReader

import SP1Chips.Sub.Constraints

open LeanRV64D.Functions BitVec

namespace Sub

set_option linter.style.setOption false
set_option linter.style.longLine false

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 33)
  (s : SailState)

noncomputable def spec_sub (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.SUB
  pure ()

def sp1_op_a : BitVec 5 := BitVec.ofNat 5 Main[6].val

def sp1_op_b : BitVec 5 := BitVec.ofNat 5 Main[14].val

def sp1_op_c : BitVec 5 := BitVec.ofNat 5 Main[21].val

def sp1_sub : SailM Unit := do
  let op_a := sp1_op_a Main
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[28], Main[29], Main[30], Main[31]])

open Sail

theorem correct_sub
  (cstrs : (constraints Main).allHold_poly)
  (h_is_real : Main[32] = 1)
  (state_cstrs : (constraints Main).initialState_poly s) :
  let op_c := sp1_op_c Main
  let op_b := sp1_op_b Main
  let op_a := sp1_op_a Main
  (spec_sub (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_sub Main).run s
  := by
    simp [constraints] at cstrs
    obtain ⟨sub_op_cstrs, cpu_cstrs, reader_cstrs, rest⟩ := cstrs
    rw [CPUState.allHold_constraints_iff_is_real_poly h_is_real] at cpu_cstrs
    simp [RTypeReader.allHold_constraints_iff_is_real_poly h_is_real h_is_real,
      Opcode.ofNat, Nat.ble] at reader_cstrs
    obtain ⟨trusted_instr_prop, h_op_a_lt, _, _, _, _, _, ⟨⟨_, _, ⟨_, is_U64_b, is_U64_c⟩⟩, _⟩⟩ := reader_cstrs
    haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    have h32 : (32 : ZMod p).val = 32 := val_32_zmod_p
    have h6 : Main[6].val < 32 := by
      have : Main[6].val < (32 : ZMod p).val := h_op_a_lt
      rwa [h32] at this
    have h14 : Main[14].val < 32 := by
      have : Main[14].val < (32 : ZMod p).val := trusted_instr_prop.1
      rwa [h32] at this
    have h21 : Main[21].val < 32 := by
      have : Main[21].val < (32 : ZMod p).val := trusted_instr_prop.2
      rwa [h32] at this
    simp [SP1ConstraintList.initialState_poly, constraints, SP1Constraint.toStateProp,
      List.Forall, SubOperation.constraints, CPUState.constraints, RTypeReader.constraints,
      h6, h14, h21, h_is_real] at state_cstrs
    obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    rw [h_is_real] at *
    apply SubOperation.spec_poly is_U64_b is_U64_c at sub_op_cstrs
    obtain ⟨is_U64_val, is_sub⟩ := sub_op_cstrs
    simp [BitVec.ofNatLT_eq_ofNat] at *
    -- Now the monadic manipulation
    simp [spec_sub, sp1_sub, execute_RTYPE']
    rw [run_readReg, read_pc]
    simp [sp1_op_b, read_op_b]
    simp [sp1_op_c, read_op_c]
    simp [sp1_op_a]
    by_cases h_is_op_a_0 : Main[6] = 0
    · simp_all
    · simp_all
      have h6_val : Main[6].val ≠ 0 := by
        intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
      rw [if_neg (by simp [← BitVec.toNat_inj]; omega)]
      rw [if_neg (by simp [← BitVec.toNat_inj]; omega)]
      -- Bridge `execute_RTYPE_pure` to the toBitVec64 subtraction form
      rw [exec_RTYPE_pure_bv_to_w_poly _ _ _ is_U64_b is_U64_c]
      simp only [execute_RTYPE_pure_w_poly]
      -- Bridge `+ 4#64` to limb-0 addition via the generic helper.
      have hp_lt : 2 ^ 17 < p := Fact.out
      have h_pc3 : Main[3].val < 65536 := by
        have h3 : Main[3] < (65536 : ZMod p) := by simp_all
        have : Main[3].val < (65536 : ZMod p).val := h3
        rwa [val_65536_zmod_p] at this
      rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
          Word.toBitVec64_lowLimb_add_nat _ _ _ _ 4 (by omega),
          show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl, ← is_sub]
      simp [bitVecToRegidxVal]

end Sub
