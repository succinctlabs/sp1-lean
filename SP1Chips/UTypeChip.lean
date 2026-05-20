import SP1Operations.Operation.AddOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.JTypeReader
import SP1Chips.UType.Constraints

open LeanRV64D.Functions BitVec Sail

namespace UType

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 31)
  (s : SailState)

/-- The destination register `rd` extracted from the trace. -/
def sp1_op_a : BitVec 5 := BitVec.ofNat 5 Main[6].val

/-- The 20-bit U-type immediate, recovered from the high 20 bits of the
constrained 32-bit immediate stored in `Main[14]`/`Main[15]`. -/
def sp1_op_b : BitVec 20 :=
  BitVec.ofNat 20 (Main[14].val / 4096 + Main[15].val * 16)

/-- Sail spec for AUIPC, with `nextPC` advanced. -/
def spec_auipc (imm : BitVec 20) (rd : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_UTYPE imm rd uop.AUIPC

/-- Sail spec for LUI, with `nextPC` advanced. -/
def spec_lui (imm : BitVec 20) (rd : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_UTYPE imm rd uop.LUI

/-- The SP1 implementation: shared between AUIPC and LUI; the addend (`pc` for
AUIPC, `0` for LUI) is built into the trace via `Main[22..24]`. -/
def sp1_utype : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg (sp1_op_a Main)
                 (Word.toBitVec64 #v[Main[25], Main[26], Main[27], Main[28]])
  return RETIRE_SUCCESS

-- Internal helper: from the trusted-instr divisibility + sign-extension equality,
-- the `Word.toBitVec64` of `Main[14..17]` equals the Sail-style
-- `signExtend 64 (imm +++ 0#12)` where `imm` is the 20-bit immediate recovered by
-- `sp1_op_b`. Polymorphic counterpart of `toBitVec64_eq_signExtend_sp1_op_b`.
set_option linter.unusedSectionVars false in
private lemma toBitVec64_eq_signExtend_sp1_op_b_poly
    (_h14_lt : Main[14].val < 65536) (_h15_lt : Main[15].val < 65536)
    (h_div : Main[14].val % 2 ^ 12 = 0)
    (h_se : BitVec.signExtend 64 (BitVec.ofNat 32 (Main[14].val + Main[15].val * 65536)) =
            Word.toBitVec64 #v[Main[14], Main[15], Main[16], Main[17]]) :
    Word.toBitVec64 #v[Main[14], Main[15], Main[16], Main[17]] =
      BitVec.signExtend 64 (sp1_op_b Main +++ 0#12) := by
  rw [← h_se]
  congr 1
  apply BitVec.toNat_inj.mp
  simp [sp1_op_b, BitVec.toNat_ofNat]
  have h14_div : Main[14].val / 4096 * 4096 = Main[14].val := by
    have := Nat.div_add_mod Main[14].val 4096
    omega
  rw [BitVec.toNat_append]; simp; omega

set_option maxHeartbeats 1600000 in
-- Sign-extend manipulation in the non-zero op_a branch sits well above
-- the default 200K heartbeat budget (matches AddwChip).
theorem correct_lui
    (cstrs : (constraints Main).allHold_poly)
    (h_is_real : Main[30] = 1)
    (h_is_lui : Main[29] = 0)
    (state_cstrs : (constraints Main).initialState_poly s) :
    let rd := sp1_op_a Main
    (spec_lui (sp1_op_b Main) (.Regidx rd)).run s = (sp1_utype Main).run s := by
  simp only []
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  -- Split the constraints into the four pieces.
  simp [constraints] at cstrs
  obtain ⟨_, add_op_cstrs, reader_cstrs, rest⟩ := cstrs
  -- Apply JTypeReader iff_poly.
  rw [JTypeReader.allHold_constraints_iff_is_real_poly h_is_real h_is_real] at reader_cstrs
  -- Specialize the addend to LUI's 0 word and reduce the opcode to LUI.
  have h49_lt : (49 : ℕ) < p := by
    have h := Fact.out (p := 2 ^ 17 < p)
    have : (49 : ℕ) < 2 ^ 17 := by decide
    omega
  have h49_val : (49 : ZMod p).val = 49 := ZMod.val_natCast_of_lt h49_lt
  simp [h_is_lui, h_is_real, show (Opcode.ofNat 49) = Opcode.LUI from rfl,
    Opcode.trusted_instr_poly, h49_val] at add_op_cstrs reader_cstrs
  -- LUI's addend is the zero word: from rest, Main[22..24] = 0.
  obtain ⟨h22, h23, h24⟩ : Main[22] = 0 ∧ Main[23] = 0 ∧ Main[24] = 0 := by
    rcases rest with ⟨_, _, h22, h23, h24, _⟩
    refine ⟨?_, ?_, ?_⟩ <;> simp [h_is_lui, sub_eq_zero] at h22 h23 h24 <;> assumption
  rw [h22, h23, h24] at add_op_cstrs
  -- Destructure the reader iff RHS into named facts.
  obtain ⟨⟨h_div, h_se⟩, h6_lt, h14_lt, h15_lt, h16_lt, h17_lt,
          _h18, _h19, _h20, _h21,
          _h13_bool, h_a0_iff,
          _hpc_mod, h3_lt, h4_lt, h5_lt,
          _h12, _hts, _h_prev_isU64, h_op_a_0_zero⟩ := reader_cstrs
  -- Convert ZMod-level limb bounds to Nat .val < 65536.
  have h65k : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
  have lt65k : ∀ (x : ZMod p), x < (65536 : ZMod p) → x.val < 65536 :=
    fun x h => by have : x.val < (65536 : ZMod p).val := h; rwa [h65k] at this
  have h32_val : (32 : ZMod p).val = 32 := val_32_zmod_p
  have h14_val_lt : Main[14].val < 65536 := lt65k _ h14_lt
  have h15_val_lt : Main[15].val < 65536 := lt65k _ h15_lt
  have h16_val_lt : Main[16].val < 65536 := lt65k _ h16_lt
  have h17_val_lt : Main[17].val < 65536 := lt65k _ h17_lt
  have h_op_b_isU64 : Word.isU64_poly #v[Main[14], Main[15], Main[16], Main[17]] :=
    Word.isU64_of_cases_poly h14_val_lt h15_val_lt h16_val_lt h17_val_lt
  -- Recover the standard sign-extension equality for the 20-bit immediate.
  have h_imm := toBitVec64_eq_signExtend_sp1_op_b_poly Main h14_val_lt h15_val_lt h_div h_se
  -- Initial state: PC.
  simp [SP1ConstraintList.initialState_poly, constraints, SP1Constraint.toStateProp,
    AddOperation.constraints, CPUState.constraints,
    JTypeReader.constraints, h_is_real] at state_cstrs
  obtain ⟨read_pc, _⟩ := state_cstrs
  -- Unfold the spec and the SP1 implementation.
  simp [spec_lui, sp1_utype, execute_UTYPE, sp1_op_a]
  rw [run_readReg, read_pc]
  clear rest
  -- pc + 4 bridge.
  have h_pc3 : Main[3].val < 65536 := lt65k _ h3_lt
  have h_pc_step : Word.toBitVec64 (#v[Main[3], Main[4], Main[5], (0 : ZMod p)]) + 4#64 =
      Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0] := by
    have hp_lt : 131072 < p := by
      have := Fact.out (p := 2 ^ 17 < p)
      have h17 : (2 : ℕ) ^ 17 = 131072 := by decide
      omega
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
  -- The zero word's BitVec form is 0#64.
  have h_zero_word : Word.toBitVec64 (#v[(0 : ZMod p), 0, 0, 0]) = 0#64 := by
    simp [Word.toBitVec64, Word.toNat_poly_def, ZMod.val_zero]
  by_cases h_is_op_a_0 : Main[6] = 0
  · -- rd = x0: spec's wX_bits is a no-op; sp1's write_reg is a no-op when value = 0.
    have h13_one : Main[13] = 1 := h_a0_iff.mpr h_is_op_a_0
    obtain ⟨h25, h26, h27, h28⟩ := h_op_a_0_zero (by rw [h13_one]; exact one_ne_zero)
    have h_addr_zero : (BitVec.ofNat 5 Main[6].val) = 0#5 := by
      rw [h_is_op_a_0]; simp [ZMod.val_zero]
    simp [h_addr_zero, h_zero_word, h_pc_step, h25, h26, h27, h28]
  · -- rd ≠ x0: AddOp gives value = signExtend 64 (imm +++ 0#12).
    have h13_zero : Main[13] = 0 := by
      rcases _h13_bool with h | h
      · exact h
      · exact absurd (h_a0_iff.mp h) h_is_op_a_0
    rw [show (1 : ZMod p) - Main[13] = 1 by simp [h13_zero]] at add_op_cstrs
    have h_zero_isU64 : Word.isU64_poly (#v[(0 : ZMod p), 0, 0, 0]) := by
      apply Word.isU64_of_cases_poly <;> simp [ZMod.val_zero]
    have ⟨_, h_add⟩ := AddOperation.spec_poly h_zero_isU64 h_op_b_isU64 add_op_cstrs
    simp [h_zero_word, BitVec.zero_add] at h_add
    have h6_val : Main[6].val ≠ 0 := by
      intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
    have h6_lt' : Main[6].val < 32 := by
      have : Main[6].val < (32 : ZMod p).val := h6_lt; rwa [h32_val] at this
    have h_rd_ne : (BitVec.ofNat 5 Main[6].val) ≠ 0#5 := by
      simp [← BitVec.toNat_inj]; omega
    simp [h_pc_step, ← h_imm, ← h_add, if_neg h_rd_ne, bitVecToRegidxVal]

set_option maxHeartbeats 1600000 in
-- Same heartbeat justification as `correct_lui`; AUIPC's pc-addend path
-- doubles the BitVec arithmetic load.
theorem correct_auipc
    (cstrs : (constraints Main).allHold_poly)
    (h_is_real : Main[30] = 1)
    (h_is_auipc : Main[29] = 1)
    (state_cstrs : (constraints Main).initialState_poly s) :
    let rd := sp1_op_a Main
    (spec_auipc (sp1_op_b Main) (.Regidx rd)).run s = (sp1_utype Main).run s := by
  simp only []
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp [constraints] at cstrs
  obtain ⟨_, add_op_cstrs, reader_cstrs, rest⟩ := cstrs
  rw [JTypeReader.allHold_constraints_iff_is_real_poly h_is_real h_is_real] at reader_cstrs
  have h48_lt : (48 : ℕ) < p := by
    have h := Fact.out (p := 2 ^ 17 < p)
    have : (48 : ℕ) < 2 ^ 17 := by decide
    omega
  have h48_val : (48 : ZMod p).val = 48 := ZMod.val_natCast_of_lt h48_lt
  simp [h_is_auipc, h_is_real, show (Opcode.ofNat 48) = Opcode.AUIPC from rfl,
    Opcode.trusted_instr_poly, h48_val] at add_op_cstrs reader_cstrs
  -- AUIPC's addend is the pc word: from rest, Main[22..24] = pc[0..2].
  obtain ⟨h22, h23, h24⟩ : Main[22] = Main[3] ∧ Main[23] = Main[4] ∧ Main[24] = Main[5] := by
    obtain ⟨_, _, hr22, hr23, hr24, _⟩ := rest
    rw [h_is_auipc] at hr22 hr23 hr24
    refine ⟨?_, ?_, ?_⟩
    · linear_combination hr22
    · linear_combination hr23
    · linear_combination hr24
  rw [h22, h23, h24] at add_op_cstrs
  obtain ⟨⟨h_div, h_se⟩, h6_lt, h14_lt, h15_lt, h16_lt, h17_lt,
          _h18, _h19, _h20, _h21,
          _h13_bool, h_a0_iff,
          _hpc_mod, h3_lt, h4_lt, h5_lt,
          _h12, _hts, _h_prev_isU64, h_op_a_0_zero⟩ := reader_cstrs
  have h65k : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
  have lt65k : ∀ (x : ZMod p), x < (65536 : ZMod p) → x.val < 65536 :=
    fun x h => by have : x.val < (65536 : ZMod p).val := h; rwa [h65k] at this
  have h32_val : (32 : ZMod p).val = 32 := val_32_zmod_p
  have h3_val_lt : Main[3].val < 65536 := lt65k _ h3_lt
  have h4_val_lt : Main[4].val < 65536 := lt65k _ h4_lt
  have h5_val_lt : Main[5].val < 65536 := lt65k _ h5_lt
  have h14_val_lt : Main[14].val < 65536 := lt65k _ h14_lt
  have h15_val_lt : Main[15].val < 65536 := lt65k _ h15_lt
  have h16_val_lt : Main[16].val < 65536 := lt65k _ h16_lt
  have h17_val_lt : Main[17].val < 65536 := lt65k _ h17_lt
  have h_op_b_isU64 : Word.isU64_poly #v[Main[14], Main[15], Main[16], Main[17]] :=
    Word.isU64_of_cases_poly h14_val_lt h15_val_lt h16_val_lt h17_val_lt
  have h_pc_isU64 : Word.isU64_poly #v[Main[3], Main[4], Main[5], (0 : ZMod p)] :=
    Word.isU64_of_cases_poly h3_val_lt h4_val_lt h5_val_lt (by simp [ZMod.val_zero])
  have h_imm := toBitVec64_eq_signExtend_sp1_op_b_poly Main h14_val_lt h15_val_lt h_div h_se
  simp [SP1ConstraintList.initialState_poly, constraints, SP1Constraint.toStateProp,
    AddOperation.constraints, CPUState.constraints,
    JTypeReader.constraints, h_is_real] at state_cstrs
  obtain ⟨read_pc, _⟩ := state_cstrs
  simp [spec_auipc, sp1_utype, execute_UTYPE, sp1_op_a, get_arch_pc]
  rw [run_readReg, read_pc]
  simp only []
  -- The second `readReg PC` (in execute_UTYPE for AUIPC) on the post-writeReg state.
  rw [run_readReg_insert_of_ne _ (by decide : Register.nextPC ≠ Register.PC), read_pc]
  clear rest
  -- pc + 4 bridge.
  have h_pc_step : Word.toBitVec64 (#v[Main[3], Main[4], Main[5], (0 : ZMod p)]) + 4#64 =
      Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0] := by
    have hp_lt : 131072 < p := by
      have := Fact.out (p := 2 ^ 17 < p)
      have h17 : (2 : ℕ) ^ 17 = 131072 := by decide
      omega
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
  -- The zero word's BitVec form is 0#64 — needed for AUIPC's `if` reduction.
  have h_zero_word : Word.toBitVec64 (#v[(0 : ZMod p), 0, 0, 0]) = 0#64 := by
    simp [Word.toBitVec64, Word.toNat_poly_def, ZMod.val_zero]
  by_cases h_is_op_a_0 : Main[6] = 0
  · have h13_one : Main[13] = 1 := h_a0_iff.mpr h_is_op_a_0
    obtain ⟨h25, h26, h27, h28⟩ := h_op_a_0_zero (by rw [h13_one]; exact one_ne_zero)
    have h_addr_zero : (BitVec.ofNat 5 Main[6].val) = 0#5 := by
      rw [h_is_op_a_0]; simp [ZMod.val_zero]
    simp [h_addr_zero, h_pc_step, h_zero_word, h25, h26, h27, h28]
  · have h13_zero : Main[13] = 0 := by
      rcases _h13_bool with h | h
      · exact h
      · exact absurd (h_a0_iff.mp h) h_is_op_a_0
    rw [show (1 : ZMod p) - Main[13] = 1 by simp [h13_zero]] at add_op_cstrs
    have ⟨_, h_add⟩ := AddOperation.spec_poly h_pc_isU64 h_op_b_isU64 add_op_cstrs
    simp at h_add
    have h6_val : Main[6].val ≠ 0 := by
      intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
    have h6_lt' : Main[6].val < 32 := by
      have : Main[6].val < (32 : ZMod p).val := h6_lt; rwa [h32_val] at this
    have h_rd_ne : (BitVec.ofNat 5 Main[6].val) ≠ 0#5 := by
      simp [← BitVec.toNat_inj]; omega
    simp [h_pc_step, ← h_imm, ← h_add, if_neg h_rd_ne, bitVecToRegidxVal]

end UType
