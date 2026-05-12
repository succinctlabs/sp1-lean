import SP1Foundations
import SP1Operations.Operation.SubwOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.RTypeReader
import SP1Chips.Subw.Constraints

open LeanRV64D.Functions BitVec

namespace Subw

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 32)
  (s : SailState)

noncomputable def spec_subw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPEW rs2 rs1 rd ropw.SUBW
  pure ()

def sp1_op_a : BitVec 5 := BitVec.ofNat 5 Main[6].val

def sp1_op_b : BitVec 5 := BitVec.ofNat 5 Main[14].val

def sp1_op_c : BitVec 5 := BitVec.ofNat 5 Main[21].val

def sp1_subw : SailM Unit := do
  let op_a := sp1_op_a Main
  Sail.writeReg Register.nextPC (Word.toBitVec64_poly #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64_poly #v[Main[28], Main[29], Main[30] * 65535, Main[30] * 65535])

open Sail

set_option maxHeartbeats 1600000 in
-- Subw migration's BitVec/sign-extend manipulation in the non-zero
-- op_a branch sits well above the default 200K heartbeat budget.
theorem correct_subw
  (cstrs : (constraints Main).allHold_poly)
  (h_is_real : Main[31] = 1)
  (state_cstrs : (constraints Main).initialState_poly s) :
  let op_c := sp1_op_c Main
  let op_b := sp1_op_b Main
  let op_a := sp1_op_a Main
  (spec_subw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_subw Main).run s
  := by
    simp [constraints] at cstrs
    obtain ⟨subw_op_cstrs, cpu_cstrs, reader_cstrs, _⟩ := cstrs
    haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    have h20_lt : (20 : ℕ) < p := by
      have h := Fact.out (p := 2 ^ 17 < p)
      have : (20 : ℕ) < 2 ^ 17 := by decide
      omega
    have h20_val : (20 : ZMod p).val = 20 := ZMod.val_natCast_of_lt h20_lt
    rw [CPUState.allHold_constraints_iff_is_real_poly h_is_real] at cpu_cstrs
    simp [RTypeReader.allHold_constraints_iff_is_real_poly h_is_real h_is_real,
      Opcode.ofNat, Nat.ble, h20_val] at reader_cstrs
    obtain ⟨trusted_instr_prop, h_op_a_lt, _, _, _, _, _, ⟨⟨_, _, ⟨_, is_U64_b, is_U64_c⟩⟩, _⟩⟩ := reader_cstrs
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
    simp [SP1ConstraintList.initialState_poly, constraints, SP1Constraint.toStateProp_poly,
      List.Forall, SubwOperation.constraints, CPUState.constraints, RTypeReader.constraints,
      U16MSBOperation.constraints, h6, h14, h21, h_is_real] at state_cstrs
    obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
    rw [h_is_real] at *
    apply SubwOperation.spec_poly is_U64_b is_U64_c at subw_op_cstrs
    obtain ⟨is_U32_val, is_subw, is_msb⟩ := subw_op_cstrs
    simp [BitVec.ofNatLT_eq_ofNat] at *
    -- Now the monadic manipulation
    simp [spec_subw, sp1_subw, execute_RTYPEW']
    rw [run_readReg, read_pc]
    simp [sp1_op_b, read_op_b]
    simp [sp1_op_c, read_op_c]
    simp [sp1_op_a]
    -- Bridge `execute_RTYPEW_pure` to the `_w_poly` form, then push `is_subw` into
    -- `is_msb` so simp_all-driven Main[30] rewrites produce the `execute` form
    -- (which `← is_subw` later flips uniformly to the `toBitVec32` form).
    rw [exec_RTYPEW_pure_bv_to_w_poly _ _ _ is_U64_b is_U64_c]
    -- Push the sign-extend rewrite through the spec BEFORE the by_cases /
    -- simp_all so simp_all only sees the unfolded form.
    simp only [execute_RTYPEW_pure_w_poly, execute_RTYPEW_pure_32_w_poly,
      LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend]
    rw [← is_subw, HWord.sign_extend_32_to_64_msb_poly is_U32_val]
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
      -- Bridge `+ 4#64` to limb-0 addition via the generic helper.
      have hp_lt : 131072 < p := by
        have := Fact.out (p := 2 ^ 17 < p)
        have h17 : (2 : ℕ) ^ 17 = 131072 := by decide
        omega
      have h_pc3 : Main[3].val < 65536 := by
        have h3 : Main[3] < (65536 : ZMod p) := by simp_all
        have : Main[3].val < (65536 : ZMod p).val := h3
        rwa [val_65536_zmod_p] at this
      rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
          Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
          show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
      simp [bitVecToRegidxVal]

end Subw
