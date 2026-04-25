import SP1Operations.Operation.AddOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.JTypeReader
import SP1Chips.UType.Constraints

open LeanRV64D.Functions BitVec Sail

namespace UType

variable (Main : Vector (Fin KB) 31) (s : SailState)

lemma op_a_lt32_of_constraints {Main : Vector (Fin KB) 31}
    (h_cstrs : (constraints Main).allHold) (h_is_real : Main[30] = 1) : Main[6].val < 32 := by
  simp [constraints] at h_cstrs
  obtain ⟨_, _, reader_cstrs, _⟩ := h_cstrs
  rw [JTypeReader.allHold_constraints_iff_is_real h_is_real] at reader_cstrs
  exact reader_cstrs.2.1

/-- The destination register `rd` extracted from the trace. -/
def sp1_op_a {Main : Vector (Fin KB) 31}
    (cstrs : (constraints Main).allHold) (h_is_real : Main[30] = 1) : BitVec 5 :=
  Main[6].val#'(op_a_lt32_of_constraints cstrs h_is_real)

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
def sp1_utype (cstrs : (constraints Main).allHold) (h_is_real : Main[30] = 1) :
    SailM ExecutionResult := do
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg (sp1_op_a cstrs h_is_real)
                 (Word.toBitVec64 #v[Main[25], Main[26], Main[27], Main[28]])
  return RETIRE_SUCCESS

/-- Internal helper: from the trusted-instr divisibility + sign-extension equality,
the `Word.toBitVec64` of `Main[14..17]` equals the Sail-style `signExtend 64 (imm +++ 0#12)`
where `imm` is the 20-bit immediate recovered by `sp1_op_b`. -/
private lemma toBitVec64_eq_signExtend_sp1_op_b
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

theorem correct_lui
    (Main : Vector (Fin KB) 31) (s : SailState)
    (cstrs : (constraints Main).allHold)
    (h_is_real : Main[30] = 1)
    (h_is_lui : Main[29] = 0)
    (state_cstrs : (constraints Main).initialState s) :
    let rd := sp1_op_a cstrs h_is_real
    (spec_lui (sp1_op_b Main) (.Regidx rd)).run s = (sp1_utype Main cstrs h_is_real).run s := by
  simp only []  -- expose the let-binding without extracting it
  -- Split the constraints into the four pieces.
  simp [constraints] at cstrs
  obtain ⟨_, add_op_cstrs, reader_cstrs, rest⟩ := cstrs
  rw [JTypeReader.allHold_constraints_iff_is_real h_is_real] at reader_cstrs
  -- Specialize the addend to LUI's 0 word and reduce the opcode to LUI.
  simp [h_is_lui, h_is_real, show (Opcode.ofNat 49) = Opcode.LUI from rfl,
    Opcode.trusted_instr] at add_op_cstrs reader_cstrs
  -- LUI's addend is the zero word: from rest, Main[22..24] = 0.
  obtain ⟨h22, h23, h24⟩ : Main[22] = 0 ∧ Main[23] = 0 ∧ Main[24] = 0 := by
    rcases rest with ⟨_, _, h22, h23, h24, _⟩
    refine ⟨?_, ?_, ?_⟩ <;> simp [h_is_lui] at h22 h23 h24 <;> assumption
  rw [h22, h23, h24] at add_op_cstrs
  -- Destructure the reader iff RHS into named facts.
  obtain ⟨⟨h_div, h_se⟩, h6_lt, h14_lt, h15_lt, h16_lt, h17_lt,
          _h18, _h19, _h20, _h21,
          _h13_bool, h_a0_iff,
          _hpc_mod, h3_lt, h4_lt, h5_lt,
          _h12, _hts, _h_prev_isU64, h_op_a_0_zero⟩ := reader_cstrs
  have h_op_b_isU64 : Word.isU64 #v[Main[14], Main[15], Main[16], Main[17]] :=
    Word.isU64_of_cases h14_lt h15_lt h16_lt h17_lt
  -- Recover the standard sign-extension equality for the 20-bit immediate.
  have h_imm := toBitVec64_eq_signExtend_sp1_op_b Main h14_lt h15_lt h_div h_se
  -- Initial state: PC.
  simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp,
    List.Forall, AddOperation.constraints, CPUState.constraints,
    JTypeReader.constraints, h_is_real] at state_cstrs
  obtain ⟨read_pc, _⟩ := state_cstrs
  -- The pc + 4 equality.
  have h_pc_step : Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] + 4#64 =
      Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0] := by
    simp [Word.toBitVec64, Word.toNat]
    exact Fin.BitVec_ofNat_add_eq_add_ofNat _ 4 (by decide) (by omega)
  -- The zero word's BitVec form is 0#64.
  have h_zero_word : Word.toBitVec64 (#v[0, 0, 0, 0] : Vector (Fin KB) 4) = 0#64 := by
    simp [Word.toBitVec64, Word.toNat]
  -- Unfold the spec and the SP1 implementation.
  simp [spec_lui, sp1_utype, execute_UTYPE, sp1_op_a]
  rw [run_readReg, read_pc]
  clear rest
  by_cases h_is_op_a_0 : Main[6] = 0
  · -- rd = x0: spec's wX_bits is a no-op; sp1's write_reg is a no-op when value = 0.
    have h13_one : Main[13] = 1 := h_a0_iff.mpr h_is_op_a_0
    obtain ⟨h25, h26, h27, h28⟩ := h_op_a_0_zero (by rw [h13_one]; decide)
    simp_all
  · -- rd ≠ x0: AddOp gives value = signExtend 64 (imm +++ 0#12).
    have h13_zero : Main[13] = 0 := by
      rcases _h13_bool with h | h
      · exact h
      · exact absurd (h_a0_iff.mp h) h_is_op_a_0
    rw [show (1 : Fin KB) - Main[13] = 1 by simp [h13_zero]] at add_op_cstrs
    have ⟨_, h_add⟩ := AddOperation.spec (a := #v[0, 0, 0, 0])
      (b := #v[Main[14], Main[15], Main[16], Main[17]])
      (cols := { value := #v[Main[25], Main[26], Main[27], Main[28]] })
      (by simp [Word.isU64_of_cases]) h_op_b_isU64 add_op_cstrs
    simp [h_zero_word, BitVec.zero_add] at h_add
    have h_rd_ne : ((Main[6].val : Nat)#'(by aesop) : BitVec 5) ≠ 0#5 := by
      simp [← BitVec.toNat_inj]; omega
    simp_all [bitVecToRegidxVal]

theorem correct_auipc
    (Main : Vector (Fin KB) 31) (s : SailState)
    (cstrs : (constraints Main).allHold)
    (h_is_real : Main[30] = 1)
    (h_is_auipc : Main[29] = 1)
    (state_cstrs : (constraints Main).initialState s) :
    let rd := sp1_op_a cstrs h_is_real
    (spec_auipc (sp1_op_b Main) (.Regidx rd)).run s = (sp1_utype Main cstrs h_is_real).run s := by
  simp only []
  -- Split the constraints into the four pieces.
  simp [constraints] at cstrs
  obtain ⟨_, add_op_cstrs, reader_cstrs, rest⟩ := cstrs
  rw [JTypeReader.allHold_constraints_iff_is_real h_is_real] at reader_cstrs
  simp [h_is_auipc, h_is_real, show (Opcode.ofNat 48) = Opcode.AUIPC from rfl,
    Opcode.trusted_instr] at add_op_cstrs reader_cstrs
  -- AUIPC's addend is the pc word: from rest, Main[22..24] = pc[0..2].
  obtain ⟨h22, h23, h24⟩ : Main[22] = Main[3] ∧ Main[23] = Main[4] ∧ Main[24] = Main[5] := by
    obtain ⟨_, _, hr22, hr23, hr24, _⟩ := rest
    rw [h_is_auipc] at hr22 hr23 hr24
    refine ⟨?_, ?_, ?_⟩
    · linear_combination hr22
    · linear_combination hr23
    · linear_combination hr24
  rw [h22, h23, h24] at add_op_cstrs
  -- Destructure the reader iff RHS into named facts.
  obtain ⟨⟨h_div, h_se⟩, h6_lt, h14_lt, h15_lt, h16_lt, h17_lt,
          _h18, _h19, _h20, _h21,
          _h13_bool, h_a0_iff,
          _hpc_mod, h3_lt, h4_lt, h5_lt,
          _h12, _hts, _h_prev_isU64, h_op_a_0_zero⟩ := reader_cstrs
  have h_op_b_isU64 : Word.isU64 #v[Main[14], Main[15], Main[16], Main[17]] :=
    Word.isU64_of_cases h14_lt h15_lt h16_lt h17_lt
  have h_pc_isU64 : Word.isU64 #v[Main[3], Main[4], Main[5], 0] :=
    Word.isU64_of_cases h3_lt h4_lt h5_lt (by simp)
  -- Recover the standard sign-extension equality for the 20-bit immediate.
  have h_imm := toBitVec64_eq_signExtend_sp1_op_b Main h14_lt h15_lt h_div h_se
  -- Initial state: PC.
  simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp,
    List.Forall, AddOperation.constraints, CPUState.constraints,
    JTypeReader.constraints, h_is_real] at state_cstrs
  obtain ⟨read_pc, _⟩ := state_cstrs
  -- The pc + 4 equality.
  have h_pc_step : Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] + 4#64 =
      Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0] := by
    simp [Word.toBitVec64, Word.toNat]
    exact Fin.BitVec_ofNat_add_eq_add_ofNat _ 4 (by decide) (by omega)
  -- The zero word's BitVec form is 0#64.
  have h_zero_word : Word.toBitVec64 (#v[0, 0, 0, 0] : Vector (Fin KB) 4) = 0#64 := by
    simp [Word.toBitVec64, Word.toNat]
  -- Unfold the spec and the SP1 implementation.
  simp [spec_auipc, sp1_utype, execute_UTYPE, sp1_op_a, get_arch_pc]
  rw [run_readReg, read_pc]
  simp only []
  -- The second `readReg PC` (in execute_UTYPE for AUIPC) on the post-writeReg state.
  rw [run_readReg_insert_of_ne _ (by decide : Register.nextPC ≠ Register.PC), read_pc]
  clear rest
  by_cases h_is_op_a_0 : Main[6] = 0
  · -- rd = x0: spec's wX_bits is a no-op; sp1's write_reg is a no-op when value = 0.
    have h13_one : Main[13] = 1 := h_a0_iff.mpr h_is_op_a_0
    obtain ⟨h25, h26, h27, h28⟩ := h_op_a_0_zero (by rw [h13_one]; decide)
    simp_all
  · -- rd ≠ x0: AddOp gives value = pc.toBitVec64 + signExtend 64 (imm +++ 0#12).
    have h13_zero : Main[13] = 0 := by
      rcases _h13_bool with h | h
      · exact h
      · exact absurd (h_a0_iff.mp h) h_is_op_a_0
    rw [show (1 : Fin KB) - Main[13] = 1 by simp [h13_zero]] at add_op_cstrs
    have ⟨_, h_add⟩ := AddOperation.spec (a := #v[Main[3], Main[4], Main[5], 0])
      (b := #v[Main[14], Main[15], Main[16], Main[17]])
      (cols := { value := #v[Main[25], Main[26], Main[27], Main[28]] })
      h_pc_isU64 h_op_b_isU64 add_op_cstrs
    simp at h_add
    have h_rd_ne : ((Main[6].val : Nat)#'(by aesop) : BitVec 5) ≠ 0#5 := by
      simp [← BitVec.toNat_inj]; omega
    simp_all [bitVecToRegidxVal]

end UType
