import SP1Operations.Operation.MulOperation
import SP1Operations.Operation.AddOperation
import SP1Operations.Compare.IsEqualWordOperation
import SP1Operations.Compare.IsZeroWordOperation
import SP1Operations.Compare.LtOperationUnsigned
import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.RTypeReader
import SP1Chips.DivRem.DivRem
import SP1Chips.DivRem.DivuRemu
import SP1Chips.DivRem.DivwRemw
import SP1Chips.DivRem.DivuwRemuw

open LeanRV64D.Functions
open BitVec

open DivRem

variable
  (Main : Vector (Fin KB) 246)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_real : is_real Main)


-- bundled prologue unfolds 247-column constraint list
set_option maxRecDepth 1000000 in
/-- Bundled prologue facts shared by every `correct_*` theorem: register bounds,
    U64 shapes of `op_b`/`op_c`, the `op_a = 0 → result = 0` implication, the
    eight mutually-exclusive `is_<op>` implications, and the four initial-state
    reads (PC and the three operand registers). The eight `sopᵢ` implications
    are returned as-is; callers collapse seven of them with `simp_all` against
    their specific `h_is_<op>` hypothesis. -/
lemma correct_prologue_facts
  (cstrs : (constraints Main).allHold)
  (h_is_real : is_real Main)
  (state_cstrs : (constraints Main).initialState s) :
  ∃ (ha : Main[6].val < 32) (hb : Main[14].val < 32) (hc : Main[21].val < 32),
    Main[3] < 65536 ∧
    Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] ∧
    Word.isU64 #v[Main[22], Main[23], Main[24], Main[25]] ∧
    (Main[6] = 0 → Main[28] = 0 ∧ Main[29] = 0 ∧ Main[30] = 0 ∧ Main[31] = 0) ∧
    (Main[201] = 1 → Main[202] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0) ∧
    (Main[202] = 1 → Main[201] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0) ∧
    (Main[203] = 1 → Main[201] = 0 ∧ Main[202] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0) ∧
    (Main[204] = 1 → Main[201] = 0 ∧ Main[202] = 0 ∧ Main[203] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0) ∧
    (Main[205] = 1 → Main[201] = 0 ∧ Main[202] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0) ∧
    (Main[206] = 1 → Main[201] = 0 ∧ Main[202] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0) ∧
    (Main[207] = 1 → Main[201] = 0 ∧ Main[202] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[208] = 0) ∧
    (Main[208] = 1 → Main[201] = 0 ∧ Main[202] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0) ∧
    s.regs.get? Register.PC = some (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0]) ∧
    s.get_reg? ((Main[6].val)#'ha) = some (Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]]) ∧
    s.get_reg? ((Main[14].val)#'hb) = some (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]) ∧
    s.get_reg? ((Main[21].val)#'hc) = some (Word.toBitVec64 #v[Main[22], Main[23], Main[24], Main[25]]) := by
  have ⟨ha, hb, hc, hpc⟩ := register_bounds Main cstrs h_is_real
  have ⟨is_U64_b, is_U64_c⟩ := ops_U64_b_c Main cstrs h_is_real
  have h_a0 := op_a_is_0 Main cstrs h_is_real
  have ⟨sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8⟩ := single_op Main cstrs
  simp at h_is_real
  simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp,
    List.Forall, CPUState.constraints, RTypeReader.constraints] at state_cstrs
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
  simp [h_is_real, ha, hb, hc] at read_pc read_op_a read_op_b read_op_c
  exact ⟨ha, hb, hc, hpc, is_U64_b, is_U64_c, h_a0,
    sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8,
    read_pc, read_op_a, read_op_b, read_op_c⟩

section poly_prologue

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 246)

/-- Polymorphic counterpart of `correct_prologue_facts` covering the
variant-INDEPENDENT facts available without the active variant flag in scope:
register bounds (`op_a < 32`, `op_b/op_c/pc[0] < 65536`), the U64 shapes for
`op_b`/`op_c`, the `op_a = 0 → result = 0` implication, and the eight
`sop_i` mutual-exclusion implications. The op_b/op_c bounds at `< 32` and
the four state-side reads remain variant-dependent and are derived per-arm
in each `correct_<v>_poly`. -/
lemma correct_prologue_facts_poly
  (cstrs : (constraints Main).allHold_poly)
  (h_is_real : is_real_poly Main) :
  Main[6].val < 32 ∧
  Main[14].val < 65536 ∧
  Main[21].val < 65536 ∧
  Main[3].val < 65536 ∧
  Word.isU64_poly #v[Main[15], Main[16], Main[17], Main[18]] ∧
  Word.isU64_poly #v[Main[22], Main[23], Main[24], Main[25]] ∧
  (Main[6] = 0 → Main[28] = 0 ∧ Main[29] = 0 ∧ Main[30] = 0 ∧ Main[31] = 0) ∧
  (Main[201] = 1 → Main[202] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0) ∧
  (Main[202] = 1 → Main[201] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0) ∧
  (Main[203] = 1 → Main[201] = 0 ∧ Main[202] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0) ∧
  (Main[204] = 1 → Main[201] = 0 ∧ Main[202] = 0 ∧ Main[203] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0) ∧
  (Main[205] = 1 → Main[201] = 0 ∧ Main[202] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0) ∧
  (Main[206] = 1 → Main[201] = 0 ∧ Main[202] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0) ∧
  (Main[207] = 1 → Main[201] = 0 ∧ Main[202] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[208] = 0) ∧
  (Main[208] = 1 → Main[201] = 0 ∧ Main[202] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0) := by
  obtain ⟨ha, hb, hc, hpc⟩ := register_bounds_poly Main cstrs h_is_real
  obtain ⟨is_U64_b, is_U64_c⟩ := ops_U64_b_c_poly Main cstrs h_is_real
  have h_a0 := op_a_is_0_poly Main cstrs h_is_real
  obtain ⟨sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8⟩ := single_op_poly Main cstrs
  exact ⟨ha, hb, hc, hpc, is_U64_b, is_U64_c, h_a0,
    sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8⟩

end poly_prologue

def sp1_op : SailM Unit := do
  let op_a := sp1_op_a Main cstrs h_is_real
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[28], Main[29], Main[30], Main[31]])

namespace Div

open DivRem

def spec_div (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_DIV rs2 rs1 rd false
  pure ()


-- whole-chip correctness across DIV/DIVU/DIVW/etc arms
set_option maxRecDepth 1000000 in
theorem correct_div
  (h_is_div : is_div Main)
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main cstrs h_is_real
  let op_b := sp1_op_b Main cstrs h_is_real
  let op_a := sp1_op_a Main cstrs h_is_real
  (spec_div (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op Main cstrs h_is_real).run s
  := by
    obtain ⟨ha, hb, hc, hpc, is_U64_b, is_U64_c, h_a0,
      sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8,
      read_pc, read_op_a, read_op_b, read_op_c⟩ :=
      correct_prologue_facts Main s cstrs h_is_real state_cstrs
    simp [spec_div, sp1_op, execute, execute_DIV']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    · simp [Word.toBitVec64, Word.toNat]
      exact Fin.BitVec_ofNat_add_eq_add_ofNat Main[3] 4 (by decide) (by omega)
    · rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [spec.div Main cstrs h_is_real h_is_div]
      simp [Word.toBitVec64, Word.toNat]
      rw [Fin.BitVec_ofNat_add_eq_add_ofNat Main[3] 4 (by decide) (by omega)]
      simp [bitVecToRegidxVal]

end Div

namespace Divu

open DivRem

def spec_divu (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_DIV rs2 rs1 rd true
  pure ()


-- whole-chip correctness across DIV/DIVU/DIVW/etc arms
set_option maxRecDepth 1000000 in
theorem correct_divu
  (h_is_divu : is_divu Main)
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main cstrs h_is_real
  let op_b := sp1_op_b Main cstrs h_is_real
  let op_a := sp1_op_a Main cstrs h_is_real
  (spec_divu (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op Main cstrs h_is_real).run s
  := by
    obtain ⟨ha, hb, hc, hpc, is_U64_b, is_U64_c, h_a0,
      sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8,
      read_pc, read_op_a, read_op_b, read_op_c⟩ :=
      correct_prologue_facts Main s cstrs h_is_real state_cstrs
    simp [spec_divu, sp1_op, execute, execute_DIV']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    · simp [Word.toBitVec64, Word.toNat]
      exact Fin.BitVec_ofNat_add_eq_add_ofNat Main[3] 4 (by decide) (by omega)
    · rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [spec.divu Main cstrs h_is_real h_is_divu]
      simp [Word.toBitVec64, Word.toNat]
      rw [Fin.BitVec_ofNat_add_eq_add_ofNat Main[3] 4 (by decide) (by omega)]
      simp [bitVecToRegidxVal]

end Divu

namespace Divw

open DivRem

def spec_divw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_DIVW rs2 rs1 rd false
  pure ()


-- whole-chip correctness across DIV/DIVU/DIVW/etc arms
set_option maxRecDepth 1000000 in
theorem correct_divw
  (h_is_divw : is_divw Main)
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main cstrs h_is_real
  let op_b := sp1_op_b Main cstrs h_is_real
  let op_a := sp1_op_a Main cstrs h_is_real
  (spec_divw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op Main cstrs h_is_real).run s
  := by
    obtain ⟨ha, hb, hc, hpc, is_U64_b, is_U64_c, h_a0,
      sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8,
      read_pc, read_op_a, read_op_b, read_op_c⟩ :=
      correct_prologue_facts Main s cstrs h_is_real state_cstrs
    simp [spec_divw, sp1_op, execute, execute_DIVW']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    · simp [Word.toBitVec64, Word.toNat]
      exact Fin.BitVec_ofNat_add_eq_add_ofNat Main[3] 4 (by decide) (by omega)
    · rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [spec.divw Main cstrs h_is_real h_is_divw]
      simp [Word.toBitVec64, Word.toNat]
      rw [Fin.BitVec_ofNat_add_eq_add_ofNat Main[3] 4 (by decide) (by omega)]
      simp [bitVecToRegidxVal]

end Divw

namespace Divuw

open DivRem

def spec_divuw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_DIVW rs2 rs1 rd true
  pure ()


-- whole-chip correctness across DIV/DIVU/DIVW/etc arms
set_option maxRecDepth 1000000 in
theorem correct_divuw
  (h_is_divuw : is_divuw Main)
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main cstrs h_is_real
  let op_b := sp1_op_b Main cstrs h_is_real
  let op_a := sp1_op_a Main cstrs h_is_real
  (spec_divuw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op Main cstrs h_is_real).run s
  := by
    obtain ⟨ha, hb, hc, hpc, is_U64_b, is_U64_c, h_a0,
      sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8,
      read_pc, read_op_a, read_op_b, read_op_c⟩ :=
      correct_prologue_facts Main s cstrs h_is_real state_cstrs
    simp [spec_divuw, sp1_op, execute, execute_DIVW']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    · simp [Word.toBitVec64, Word.toNat]
      exact Fin.BitVec_ofNat_add_eq_add_ofNat Main[3] 4 (by decide) (by omega)
    · rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [spec.divuw Main cstrs h_is_real h_is_divuw]
      simp [Word.toBitVec64, Word.toNat]
      rw [Fin.BitVec_ofNat_add_eq_add_ofNat Main[3] 4 (by decide) (by omega)]
      simp [bitVecToRegidxVal]

end Divuw

namespace Rem

open DivRem

def spec_rem (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_REM rs2 rs1 rd false
  pure ()


-- whole-chip correctness across DIV/DIVU/DIVW/etc arms
set_option maxRecDepth 1000000 in
theorem correct_rem
  (h_is_rem : is_rem Main)
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main cstrs h_is_real
  let op_b := sp1_op_b Main cstrs h_is_real
  let op_a := sp1_op_a Main cstrs h_is_real
  (spec_rem (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op Main cstrs h_is_real).run s
  := by
    obtain ⟨ha, hb, hc, hpc, is_U64_b, is_U64_c, h_a0,
      sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8,
      read_pc, read_op_a, read_op_b, read_op_c⟩ :=
      correct_prologue_facts Main s cstrs h_is_real state_cstrs
    simp [spec_rem, sp1_op, execute, execute_REM']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    · simp [Word.toBitVec64, Word.toNat]
      exact Fin.BitVec_ofNat_add_eq_add_ofNat Main[3] 4 (by decide) (by omega)
    · rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [spec.rem Main cstrs h_is_real h_is_rem]
      simp [Word.toBitVec64, Word.toNat]
      rw [Fin.BitVec_ofNat_add_eq_add_ofNat Main[3] 4 (by decide) (by omega)]
      simp [bitVecToRegidxVal]

end Rem

namespace Remu

open DivRem

def spec_remu (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_REM rs2 rs1 rd true
  pure ()


-- whole-chip correctness across DIV/DIVU/DIVW/etc arms
set_option maxRecDepth 1000000 in
theorem correct_remu
  (h_is_remu : is_remu Main)
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main cstrs h_is_real
  let op_b := sp1_op_b Main cstrs h_is_real
  let op_a := sp1_op_a Main cstrs h_is_real
  (spec_remu (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op Main cstrs h_is_real).run s
  := by
    obtain ⟨ha, hb, hc, hpc, is_U64_b, is_U64_c, h_a0,
      sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8,
      read_pc, read_op_a, read_op_b, read_op_c⟩ :=
      correct_prologue_facts Main s cstrs h_is_real state_cstrs
    simp [spec_remu, sp1_op, execute, execute_REM']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    · simp [Word.toBitVec64, Word.toNat]
      exact Fin.BitVec_ofNat_add_eq_add_ofNat Main[3] 4 (by decide) (by omega)
    · rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [spec.remu Main cstrs h_is_real h_is_remu]
      simp [Word.toBitVec64, Word.toNat]
      rw [Fin.BitVec_ofNat_add_eq_add_ofNat Main[3] 4 (by decide) (by omega)]
      simp [bitVecToRegidxVal]

end Remu

namespace Remw

open DivRem

def spec_remw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_REMW rs2 rs1 rd false
  pure ()


-- whole-chip correctness across DIV/DIVU/DIVW/etc arms
set_option maxRecDepth 1000000 in
theorem correct_remw
  (h_is_remw : is_remw Main)
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main cstrs h_is_real
  let op_b := sp1_op_b Main cstrs h_is_real
  let op_a := sp1_op_a Main cstrs h_is_real
  (spec_remw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op Main cstrs h_is_real).run s
  := by
    obtain ⟨ha, hb, hc, hpc, is_U64_b, is_U64_c, h_a0,
      sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8,
      read_pc, read_op_a, read_op_b, read_op_c⟩ :=
      correct_prologue_facts Main s cstrs h_is_real state_cstrs
    simp [spec_remw, sp1_op, execute, execute_REMW']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    · simp [Word.toBitVec64, Word.toNat]
      exact Fin.BitVec_ofNat_add_eq_add_ofNat Main[3] 4 (by decide) (by omega)
    · rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [spec.remw Main cstrs h_is_real h_is_remw]
      simp [Word.toBitVec64, Word.toNat]
      rw [Fin.BitVec_ofNat_add_eq_add_ofNat Main[3] 4 (by decide) (by omega)]
      simp [bitVecToRegidxVal]

end Remw

namespace Remuw

open DivRem

def spec_remuw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_REMW rs2 rs1 rd true
  pure ()


-- whole-chip correctness across DIV/DIVU/DIVW/etc arms
set_option maxRecDepth 1000000 in
theorem correct_remuw
  (h_is_remuw : is_remuw Main)
  (state_cstrs : (constraints Main).initialState s) :
  let op_c := sp1_op_c Main cstrs h_is_real
  let op_b := sp1_op_b Main cstrs h_is_real
  let op_a := sp1_op_a Main cstrs h_is_real
  (spec_remuw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op Main cstrs h_is_real).run s
  := by
    obtain ⟨ha, hb, hc, hpc, is_U64_b, is_U64_c, h_a0,
      sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8,
      read_pc, read_op_a, read_op_b, read_op_c⟩ :=
      correct_prologue_facts Main s cstrs h_is_real state_cstrs
    simp [spec_remuw, sp1_op, execute, execute_REMW']
    rw [Sail.run_readReg, read_pc]
    simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
    by_cases h_is_op_a_0 : Main[6] = 0 <;> simp_all
    · simp [Word.toBitVec64, Word.toNat]
      exact Fin.BitVec_ofNat_add_eq_add_ofNat Main[3] 4 (by decide) (by omega)
    · rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [spec.remuw Main cstrs h_is_real h_is_remuw]
      simp [Word.toBitVec64, Word.toNat]
      rw [Fin.BitVec_ofNat_add_eq_add_ofNat Main[3] 4 (by decide) (by omega)]
      simp [bitVecToRegidxVal]

end Remuw

-- ============================================================================
-- Polymorphic chip-level theorems.
-- ============================================================================
-- Each `correct_<variant>_poly` mirrors its Fin KB sibling and delegates the
-- variant-specific witness to the corresponding `spec.<variant>_poly` wrapper
-- in `SP1Chips/DivRem/{DivRem,DivuRemu,DivwRemw,DivuwRemuw}.lean`.
-- `correct_prologue_facts_poly` (variant-INDEPENDENT bundle, lines 78-101)
-- handles the prologue shared by all 8 variants.

namespace DivRem.Poly

open DivRem

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)]
  (Main : Vector (ZMod p) 246)
  (s : SailState)
  (h_is_real : is_real_poly Main)

def sp1_op_poly : SailM Unit := do
  let op_a := sp1_op_a_poly Main
  Sail.writeReg Register.nextPC (Word.toBitVec64_poly #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64_poly #v[Main[28], Main[29], Main[30], Main[31]])

open Sail

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 8000000 in
-- Heavy reader/state-cstrs destructure + spec.<v>_poly delegate exceeds the
-- default budget on every chip-level correct_<v>_poly variant.
set_option maxRecDepth 2000000 in
theorem correct_div_poly
    (cstrs : (constraints Main).allHold_poly)
    (h_is_real : is_real_poly Main)
    (h_is_div : is_div_poly Main)
    (state_cstrs : (constraints Main).initialState_poly s) :
    let op_c := sp1_op_c_poly Main
    let op_b := sp1_op_b_poly Main
    let op_a := sp1_op_a_poly Main
    (Div.spec_div (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op_poly Main).run s
  := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  have h17 : 2 ^ 17 < p := Fact.out
  obtain ⟨h6, h14, h21, is_U64_b, is_U64_c⟩ :=
    DivRem.div_chip_bounds_poly Main cstrs h_is_real h_is_div
  have h_a0 := DivRem.op_a_is_0_poly Main cstrs h_is_real
  obtain ⟨_, _, _, h_pc3, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    correct_prologue_facts_poly Main cstrs h_is_real
  simp only [DivRem.is_real_poly] at h_is_real
  simp only [SP1ConstraintList.initialState_poly, constraints,
    SP1Constraint.toStateProp_poly, List.Forall] at state_cstrs
  simp only [MulOperation.constraints, IsEqualWordOperation.constraints,
    IsZeroWordOperation.constraints, U16MSBOperation.constraints,
    AddOperation.constraints, LtOperationUnsigned.constraints,
    U16toU8OperationSafe.constraints, U16CompareOperation.constraints,
    IsZeroOperation.constraints,
    CPUState.constraints, RTypeReader.constraints,
    SP1Constraint.toStateProp_poly, List.Forall] at state_cstrs
  simp [h6, h14, h21, h_is_real] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
  simp only [BitVec.ofNatLT_eq_ofNat] at *
  simp [Div.spec_div, sp1_op_poly, execute_DIV']
  rw [Sail.run_readReg, read_pc]
  simp [sp1_op_a_poly, sp1_op_b_poly, sp1_op_c_poly, read_op_b, read_op_c]
  by_cases h_is_op_a_0 : Main[6] = 0
  · obtain ⟨ha28, ha29, ha30, ha31⟩ := h_a0 h_is_op_a_0
    rw [ha28, ha29, ha30, ha31]
    have h_zero : Word.toBitVec64_poly (#v[0, 0, 0, 0] : Word (ZMod p)) = 0#64 := by
      simp [Word.toBitVec64_poly, Word.toNat_poly, ZMod.val_zero]
    rw [if_pos h_zero]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    have h_bv_zero : BitVec.ofNat 5 Main[6].val = 0#5 := by
      rw [h_is_op_a_0, ZMod.val_zero]
    simp [h_bv_zero]
  · have h6_val : Main[6].val ≠ 0 := by
      intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
    have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
      intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
    rw [if_neg h_bv_neq, if_neg h_bv_neq]
    simp [DivRem.spec.div_poly Main cstrs h_is_real h_is_div]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    simp [bitVecToRegidxVal]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 8000000 in
-- Heavy reader/state-cstrs destructure + spec.<v>_poly delegate exceeds the
-- default budget on every chip-level correct_<v>_poly variant.
set_option maxRecDepth 2000000 in
theorem correct_divu_poly
    (cstrs : (constraints Main).allHold_poly)
    (h_is_real : is_real_poly Main)
    (h_is_divu : is_divu_poly Main)
    (state_cstrs : (constraints Main).initialState_poly s) :
    let op_c := sp1_op_c_poly Main
    let op_b := sp1_op_b_poly Main
    let op_a := sp1_op_a_poly Main
    (Divu.spec_divu (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op_poly Main).run s
  := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  -- Surface the prime-size bound as a Nat fact so omega can use it.
  have h17 : 2 ^ 17 < p := Fact.out
  -- Extract op_a/op_b/op_c < 32 bounds + U64 properties via the Common.lean helper.
  obtain ⟨h6, h14, h21, is_U64_b, is_U64_c⟩ :=
    DivRem.divu_chip_bounds_poly Main cstrs h_is_real h_is_divu
  -- op_a = 0 → writeback limbs all 0 (for the case-pos op-a-x0 collapse).
  have h_a0 := DivRem.op_a_is_0_poly Main cstrs h_is_real
  -- PC[0] < 65536 bound (needed by lowLimb_add_nat's carry-check side condition).
  obtain ⟨_, _, _, h_pc3, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    correct_prologue_facts_poly Main cstrs h_is_real
  -- Unfold h_is_real's type so simp can use it as a Main[244] = 1 rewrite.
  simp only [DivRem.is_real_poly] at h_is_real
  -- State extraction in multi-pass simp to keep stack usage bounded.
  simp only [SP1ConstraintList.initialState_poly, constraints,
    SP1Constraint.toStateProp_poly, List.Forall] at state_cstrs
  simp only [MulOperation.constraints, IsEqualWordOperation.constraints,
    IsZeroWordOperation.constraints, U16MSBOperation.constraints,
    AddOperation.constraints, LtOperationUnsigned.constraints,
    U16toU8OperationSafe.constraints, U16CompareOperation.constraints,
    IsZeroOperation.constraints,
    CPUState.constraints, RTypeReader.constraints,
    SP1Constraint.toStateProp_poly, List.Forall] at state_cstrs
  simp [h6, h14, h21, h_is_real] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
  -- Bridge BitVec↔Fin so read_op_b/c rewrites apply against the goal's BitVec form.
  simp only [BitVec.ofNatLT_eq_ofNat] at *
  simp [Divu.spec_divu, sp1_op_poly, execute_DIV']
  rw [Sail.run_readReg, read_pc]
  simp [sp1_op_a_poly, sp1_op_b_poly, sp1_op_c_poly, read_op_b, read_op_c]
  by_cases h_is_op_a_0 : Main[6] = 0
  · obtain ⟨ha28, ha29, ha30, ha31⟩ := h_a0 h_is_op_a_0
    rw [ha28, ha29, ha30, ha31]
    have h_zero : Word.toBitVec64_poly (#v[0, 0, 0, 0] : Word (ZMod p)) = 0#64 := by
      simp [Word.toBitVec64_poly, Word.toNat_poly, ZMod.val_zero]
    rw [if_pos h_zero]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    have h_bv_zero : BitVec.ofNat 5 Main[6].val = 0#5 := by
      rw [h_is_op_a_0, ZMod.val_zero]
    simp [h_bv_zero]
  · have h6_val : Main[6].val ≠ 0 := by
      intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
    have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
      intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
    rw [if_neg h_bv_neq, if_neg h_bv_neq]
    simp [DivRem.spec.divu_poly Main cstrs h_is_real h_is_divu]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    simp [bitVecToRegidxVal]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 8000000 in
-- Heavy reader/state-cstrs destructure + spec.<v>_poly delegate exceeds the
-- default budget on every chip-level correct_<v>_poly variant.
set_option maxRecDepth 2000000 in
theorem correct_divw_poly
    (cstrs : (constraints Main).allHold_poly)
    (h_is_real : is_real_poly Main)
    (h_is_divw : is_divw_poly Main)
    (state_cstrs : (constraints Main).initialState_poly s) :
    let op_c := sp1_op_c_poly Main
    let op_b := sp1_op_b_poly Main
    let op_a := sp1_op_a_poly Main
    (Divw.spec_divw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op_poly Main).run s
  := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  have h17 : 2 ^ 17 < p := Fact.out
  obtain ⟨h6, h14, h21, is_U64_b, is_U64_c⟩ :=
    DivRem.divw_chip_bounds_poly Main cstrs h_is_real h_is_divw
  have h_a0 := DivRem.op_a_is_0_poly Main cstrs h_is_real
  obtain ⟨_, _, _, h_pc3, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    correct_prologue_facts_poly Main cstrs h_is_real
  simp only [DivRem.is_real_poly] at h_is_real
  simp only [SP1ConstraintList.initialState_poly, constraints,
    SP1Constraint.toStateProp_poly, List.Forall] at state_cstrs
  simp only [MulOperation.constraints, IsEqualWordOperation.constraints,
    IsZeroWordOperation.constraints, U16MSBOperation.constraints,
    AddOperation.constraints, LtOperationUnsigned.constraints,
    U16toU8OperationSafe.constraints, U16CompareOperation.constraints,
    IsZeroOperation.constraints,
    CPUState.constraints, RTypeReader.constraints,
    SP1Constraint.toStateProp_poly, List.Forall] at state_cstrs
  simp [h6, h14, h21, h_is_real] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
  simp only [BitVec.ofNatLT_eq_ofNat] at *
  simp [Divw.spec_divw, sp1_op_poly, execute_DIVW']
  rw [Sail.run_readReg, read_pc]
  simp [sp1_op_a_poly, sp1_op_b_poly, sp1_op_c_poly, read_op_b, read_op_c]
  by_cases h_is_op_a_0 : Main[6] = 0
  · obtain ⟨ha28, ha29, ha30, ha31⟩ := h_a0 h_is_op_a_0
    rw [ha28, ha29, ha30, ha31]
    have h_zero : Word.toBitVec64_poly (#v[0, 0, 0, 0] : Word (ZMod p)) = 0#64 := by
      simp [Word.toBitVec64_poly, Word.toNat_poly, ZMod.val_zero]
    rw [if_pos h_zero]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    have h_bv_zero : BitVec.ofNat 5 Main[6].val = 0#5 := by
      rw [h_is_op_a_0, ZMod.val_zero]
    simp [h_bv_zero]
  · have h6_val : Main[6].val ≠ 0 := by
      intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
    have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
      intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
    rw [if_neg h_bv_neq, if_neg h_bv_neq]
    simp [DivRem.spec.divw_poly Main cstrs h_is_real h_is_divw]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    simp [bitVecToRegidxVal]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 8000000 in
-- Heavy reader/state-cstrs destructure + spec.<v>_poly delegate exceeds the
-- default budget on every chip-level correct_<v>_poly variant.
set_option maxRecDepth 2000000 in
theorem correct_divuw_poly
    (cstrs : (constraints Main).allHold_poly)
    (h_is_real : is_real_poly Main)
    (h_is_divuw : is_divuw_poly Main)
    (state_cstrs : (constraints Main).initialState_poly s) :
    let op_c := sp1_op_c_poly Main
    let op_b := sp1_op_b_poly Main
    let op_a := sp1_op_a_poly Main
    (Divuw.spec_divuw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op_poly Main).run s
  := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  have h17 : 2 ^ 17 < p := Fact.out
  obtain ⟨h6, h14, h21, is_U64_b, is_U64_c⟩ :=
    DivRem.divuw_chip_bounds_poly Main cstrs h_is_real h_is_divuw
  have h_a0 := DivRem.op_a_is_0_poly Main cstrs h_is_real
  obtain ⟨_, _, _, h_pc3, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    correct_prologue_facts_poly Main cstrs h_is_real
  simp only [DivRem.is_real_poly] at h_is_real
  simp only [SP1ConstraintList.initialState_poly, constraints,
    SP1Constraint.toStateProp_poly, List.Forall] at state_cstrs
  simp only [MulOperation.constraints, IsEqualWordOperation.constraints,
    IsZeroWordOperation.constraints, U16MSBOperation.constraints,
    AddOperation.constraints, LtOperationUnsigned.constraints,
    U16toU8OperationSafe.constraints, U16CompareOperation.constraints,
    IsZeroOperation.constraints,
    CPUState.constraints, RTypeReader.constraints,
    SP1Constraint.toStateProp_poly, List.Forall] at state_cstrs
  simp [h6, h14, h21, h_is_real] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
  simp only [BitVec.ofNatLT_eq_ofNat] at *
  simp [Divuw.spec_divuw, sp1_op_poly, execute_DIVW']
  rw [Sail.run_readReg, read_pc]
  simp [sp1_op_a_poly, sp1_op_b_poly, sp1_op_c_poly, read_op_b, read_op_c]
  by_cases h_is_op_a_0 : Main[6] = 0
  · obtain ⟨ha28, ha29, ha30, ha31⟩ := h_a0 h_is_op_a_0
    rw [ha28, ha29, ha30, ha31]
    have h_zero : Word.toBitVec64_poly (#v[0, 0, 0, 0] : Word (ZMod p)) = 0#64 := by
      simp [Word.toBitVec64_poly, Word.toNat_poly, ZMod.val_zero]
    rw [if_pos h_zero]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    have h_bv_zero : BitVec.ofNat 5 Main[6].val = 0#5 := by
      rw [h_is_op_a_0, ZMod.val_zero]
    simp [h_bv_zero]
  · have h6_val : Main[6].val ≠ 0 := by
      intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
    have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
      intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
    rw [if_neg h_bv_neq, if_neg h_bv_neq]
    simp [DivRem.spec.divuw_poly Main cstrs h_is_real h_is_divuw]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    simp [bitVecToRegidxVal]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 8000000 in
-- Heavy reader/state-cstrs destructure + spec.<v>_poly delegate exceeds the
-- default budget on every chip-level correct_<v>_poly variant.
set_option maxRecDepth 2000000 in
theorem correct_rem_poly
    (cstrs : (constraints Main).allHold_poly)
    (h_is_real : is_real_poly Main)
    (h_is_rem : is_rem_poly Main)
    (state_cstrs : (constraints Main).initialState_poly s) :
    let op_c := sp1_op_c_poly Main
    let op_b := sp1_op_b_poly Main
    let op_a := sp1_op_a_poly Main
    (Rem.spec_rem (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op_poly Main).run s
  := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  have h17 : 2 ^ 17 < p := Fact.out
  obtain ⟨h6, h14, h21, is_U64_b, is_U64_c⟩ :=
    DivRem.rem_chip_bounds_poly Main cstrs h_is_real h_is_rem
  have h_a0 := DivRem.op_a_is_0_poly Main cstrs h_is_real
  obtain ⟨_, _, _, h_pc3, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    correct_prologue_facts_poly Main cstrs h_is_real
  simp only [DivRem.is_real_poly] at h_is_real
  simp only [SP1ConstraintList.initialState_poly, constraints,
    SP1Constraint.toStateProp_poly, List.Forall] at state_cstrs
  simp only [MulOperation.constraints, IsEqualWordOperation.constraints,
    IsZeroWordOperation.constraints, U16MSBOperation.constraints,
    AddOperation.constraints, LtOperationUnsigned.constraints,
    U16toU8OperationSafe.constraints, U16CompareOperation.constraints,
    IsZeroOperation.constraints,
    CPUState.constraints, RTypeReader.constraints,
    SP1Constraint.toStateProp_poly, List.Forall] at state_cstrs
  simp [h6, h14, h21, h_is_real] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
  simp only [BitVec.ofNatLT_eq_ofNat] at *
  simp [Rem.spec_rem, sp1_op_poly, execute_REM']
  rw [Sail.run_readReg, read_pc]
  simp [sp1_op_a_poly, sp1_op_b_poly, sp1_op_c_poly, read_op_b, read_op_c]
  by_cases h_is_op_a_0 : Main[6] = 0
  · obtain ⟨ha28, ha29, ha30, ha31⟩ := h_a0 h_is_op_a_0
    rw [ha28, ha29, ha30, ha31]
    have h_zero : Word.toBitVec64_poly (#v[0, 0, 0, 0] : Word (ZMod p)) = 0#64 := by
      simp [Word.toBitVec64_poly, Word.toNat_poly, ZMod.val_zero]
    rw [if_pos h_zero]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    have h_bv_zero : BitVec.ofNat 5 Main[6].val = 0#5 := by
      rw [h_is_op_a_0, ZMod.val_zero]
    simp [h_bv_zero]
  · have h6_val : Main[6].val ≠ 0 := by
      intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
    have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
      intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
    rw [if_neg h_bv_neq, if_neg h_bv_neq]
    simp [DivRem.spec.rem_poly Main cstrs h_is_real h_is_rem]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    simp [bitVecToRegidxVal]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 8000000 in
-- Heavy reader/state-cstrs destructure + spec.<v>_poly delegate exceeds the
-- default budget on every chip-level correct_<v>_poly variant.
set_option maxRecDepth 2000000 in
theorem correct_remu_poly
    (cstrs : (constraints Main).allHold_poly)
    (h_is_real : is_real_poly Main)
    (h_is_remu : is_remu_poly Main)
    (state_cstrs : (constraints Main).initialState_poly s) :
    let op_c := sp1_op_c_poly Main
    let op_b := sp1_op_b_poly Main
    let op_a := sp1_op_a_poly Main
    (Remu.spec_remu (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op_poly Main).run s
  := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  have h17 : 2 ^ 17 < p := Fact.out
  obtain ⟨h6, h14, h21, is_U64_b, is_U64_c⟩ :=
    DivRem.remu_chip_bounds_poly Main cstrs h_is_real h_is_remu
  have h_a0 := DivRem.op_a_is_0_poly Main cstrs h_is_real
  obtain ⟨_, _, _, h_pc3, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    correct_prologue_facts_poly Main cstrs h_is_real
  simp only [DivRem.is_real_poly] at h_is_real
  simp only [SP1ConstraintList.initialState_poly, constraints,
    SP1Constraint.toStateProp_poly, List.Forall] at state_cstrs
  simp only [MulOperation.constraints, IsEqualWordOperation.constraints,
    IsZeroWordOperation.constraints, U16MSBOperation.constraints,
    AddOperation.constraints, LtOperationUnsigned.constraints,
    U16toU8OperationSafe.constraints, U16CompareOperation.constraints,
    IsZeroOperation.constraints,
    CPUState.constraints, RTypeReader.constraints,
    SP1Constraint.toStateProp_poly, List.Forall] at state_cstrs
  simp [h6, h14, h21, h_is_real] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
  simp only [BitVec.ofNatLT_eq_ofNat] at *
  simp [Remu.spec_remu, sp1_op_poly, execute_REM']
  rw [Sail.run_readReg, read_pc]
  simp [sp1_op_a_poly, sp1_op_b_poly, sp1_op_c_poly, read_op_b, read_op_c]
  by_cases h_is_op_a_0 : Main[6] = 0
  · obtain ⟨ha28, ha29, ha30, ha31⟩ := h_a0 h_is_op_a_0
    rw [ha28, ha29, ha30, ha31]
    have h_zero : Word.toBitVec64_poly (#v[0, 0, 0, 0] : Word (ZMod p)) = 0#64 := by
      simp [Word.toBitVec64_poly, Word.toNat_poly, ZMod.val_zero]
    rw [if_pos h_zero]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    have h_bv_zero : BitVec.ofNat 5 Main[6].val = 0#5 := by
      rw [h_is_op_a_0, ZMod.val_zero]
    simp [h_bv_zero]
  · have h6_val : Main[6].val ≠ 0 := by
      intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
    have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
      intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
    rw [if_neg h_bv_neq, if_neg h_bv_neq]
    simp [DivRem.spec.remu_poly Main cstrs h_is_real h_is_remu]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    simp [bitVecToRegidxVal]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 8000000 in
-- Heavy reader/state-cstrs destructure + spec.<v>_poly delegate exceeds the
-- default budget on every chip-level correct_<v>_poly variant.
set_option maxRecDepth 2000000 in
theorem correct_remw_poly
    (cstrs : (constraints Main).allHold_poly)
    (h_is_real : is_real_poly Main)
    (h_is_remw : is_remw_poly Main)
    (state_cstrs : (constraints Main).initialState_poly s) :
    let op_c := sp1_op_c_poly Main
    let op_b := sp1_op_b_poly Main
    let op_a := sp1_op_a_poly Main
    (Remw.spec_remw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op_poly Main).run s
  := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  have h17 : 2 ^ 17 < p := Fact.out
  obtain ⟨h6, h14, h21, is_U64_b, is_U64_c⟩ :=
    DivRem.remw_chip_bounds_poly Main cstrs h_is_real h_is_remw
  have h_a0 := DivRem.op_a_is_0_poly Main cstrs h_is_real
  obtain ⟨_, _, _, h_pc3, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    correct_prologue_facts_poly Main cstrs h_is_real
  simp only [DivRem.is_real_poly] at h_is_real
  simp only [SP1ConstraintList.initialState_poly, constraints,
    SP1Constraint.toStateProp_poly, List.Forall] at state_cstrs
  simp only [MulOperation.constraints, IsEqualWordOperation.constraints,
    IsZeroWordOperation.constraints, U16MSBOperation.constraints,
    AddOperation.constraints, LtOperationUnsigned.constraints,
    U16toU8OperationSafe.constraints, U16CompareOperation.constraints,
    IsZeroOperation.constraints,
    CPUState.constraints, RTypeReader.constraints,
    SP1Constraint.toStateProp_poly, List.Forall] at state_cstrs
  simp [h6, h14, h21, h_is_real] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
  simp only [BitVec.ofNatLT_eq_ofNat] at *
  simp [Remw.spec_remw, sp1_op_poly, execute_REMW']
  rw [Sail.run_readReg, read_pc]
  simp [sp1_op_a_poly, sp1_op_b_poly, sp1_op_c_poly, read_op_b, read_op_c]
  by_cases h_is_op_a_0 : Main[6] = 0
  · obtain ⟨ha28, ha29, ha30, ha31⟩ := h_a0 h_is_op_a_0
    rw [ha28, ha29, ha30, ha31]
    have h_zero : Word.toBitVec64_poly (#v[0, 0, 0, 0] : Word (ZMod p)) = 0#64 := by
      simp [Word.toBitVec64_poly, Word.toNat_poly, ZMod.val_zero]
    rw [if_pos h_zero]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    have h_bv_zero : BitVec.ofNat 5 Main[6].val = 0#5 := by
      rw [h_is_op_a_0, ZMod.val_zero]
    simp [h_bv_zero]
  · have h6_val : Main[6].val ≠ 0 := by
      intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
    have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
      intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
    rw [if_neg h_bv_neq, if_neg h_bv_neq]
    simp [DivRem.spec.remw_poly Main cstrs h_is_real h_is_remw]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    simp [bitVecToRegidxVal]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 8000000 in
-- Heavy reader/state-cstrs destructure + spec.<v>_poly delegate exceeds the
-- default budget on every chip-level correct_<v>_poly variant.
set_option maxRecDepth 2000000 in
theorem correct_remuw_poly
    (cstrs : (constraints Main).allHold_poly)
    (h_is_real : is_real_poly Main)
    (h_is_remuw : is_remuw_poly Main)
    (state_cstrs : (constraints Main).initialState_poly s) :
    let op_c := sp1_op_c_poly Main
    let op_b := sp1_op_b_poly Main
    let op_a := sp1_op_a_poly Main
    (Remuw.spec_remuw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op_poly Main).run s
  := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  have h17 : 2 ^ 17 < p := Fact.out
  obtain ⟨h6, h14, h21, is_U64_b, is_U64_c⟩ :=
    DivRem.remuw_chip_bounds_poly Main cstrs h_is_real h_is_remuw
  have h_a0 := DivRem.op_a_is_0_poly Main cstrs h_is_real
  obtain ⟨_, _, _, h_pc3, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    correct_prologue_facts_poly Main cstrs h_is_real
  simp only [DivRem.is_real_poly] at h_is_real
  simp only [SP1ConstraintList.initialState_poly, constraints,
    SP1Constraint.toStateProp_poly, List.Forall] at state_cstrs
  simp only [MulOperation.constraints, IsEqualWordOperation.constraints,
    IsZeroWordOperation.constraints, U16MSBOperation.constraints,
    AddOperation.constraints, LtOperationUnsigned.constraints,
    U16toU8OperationSafe.constraints, U16CompareOperation.constraints,
    IsZeroOperation.constraints,
    CPUState.constraints, RTypeReader.constraints,
    SP1Constraint.toStateProp_poly, List.Forall] at state_cstrs
  simp [h6, h14, h21, h_is_real] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
  simp only [BitVec.ofNatLT_eq_ofNat] at *
  simp [Remuw.spec_remuw, sp1_op_poly, execute_REMW']
  rw [Sail.run_readReg, read_pc]
  simp [sp1_op_a_poly, sp1_op_b_poly, sp1_op_c_poly, read_op_b, read_op_c]
  by_cases h_is_op_a_0 : Main[6] = 0
  · obtain ⟨ha28, ha29, ha30, ha31⟩ := h_a0 h_is_op_a_0
    rw [ha28, ha29, ha30, ha31]
    have h_zero : Word.toBitVec64_poly (#v[0, 0, 0, 0] : Word (ZMod p)) = 0#64 := by
      simp [Word.toBitVec64_poly, Word.toNat_poly, ZMod.val_zero]
    rw [if_pos h_zero]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    have h_bv_zero : BitVec.ofNat 5 Main[6].val = 0#5 := by
      rw [h_is_op_a_0, ZMod.val_zero]
    simp [h_bv_zero]
  · have h6_val : Main[6].val ≠ 0 := by
      intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
    have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
      intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
    rw [if_neg h_bv_neq, if_neg h_bv_neq]
    simp [DivRem.spec.remuw_poly Main cstrs h_is_real h_is_remuw]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    simp [bitVecToRegidxVal]

end DivRem.Poly
