import SP1Operations.Operation.MulOperation
import SP1Operations.Operation.AddOperation
import SP1Operations.Compare.IsEqualWordOperation
import SP1Operations.Compare.IsZeroWordOperation
import SP1Operations.Compare.LtOperationUnsigned
import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.RTypeReader
import SP1Chips.DivRem.Constraints

open LeanRV64D.Functions
open BitVec

set_option linter.style.setOption false
set_option maxHeartbeats 10000000

open DivRem

variable
  (Main : Vector (Fin KB) 247)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_real : is_real Main)

set_option maxHeartbeats 1000000 in

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
    (Main[6] = 0 → Main[29] = 0 ∧ Main[30] = 0 ∧ Main[31] = 0 ∧ Main[32] = 0) ∧
    (Main[202] = 1 → Main[203] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0 ∧ Main[209] = 0) ∧
    (Main[203] = 1 → Main[202] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0 ∧ Main[209] = 0) ∧
    (Main[204] = 1 → Main[202] = 0 ∧ Main[203] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0 ∧ Main[209] = 0) ∧
    (Main[205] = 1 → Main[202] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0 ∧ Main[209] = 0) ∧
    (Main[206] = 1 → Main[202] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0 ∧ Main[209] = 0) ∧
    (Main[207] = 1 → Main[202] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[208] = 0 ∧ Main[209] = 0) ∧
    (Main[208] = 1 → Main[202] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[209] = 0) ∧
    (Main[209] = 1 → Main[202] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0) ∧
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

def sp1_op : SailM Unit := do
  let op_a := sp1_op_a Main cstrs h_is_real
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[29], Main[30], Main[31], Main[32]])

namespace Div

open DivRem

def spec_div (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_DIV rs2 rs1 rd false
  pure ()

set_option maxHeartbeats 1000000 in

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
    . simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [spec.div Main cstrs h_is_real h_is_div]
      simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
      simp [bitVecToRegidxVal]

end Div

namespace Divu

open DivRem

def spec_divu (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_DIV rs2 rs1 rd true
  pure ()

set_option maxHeartbeats 1000000 in

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
    . simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [spec.divu Main cstrs h_is_real h_is_divu]
      simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
      simp [bitVecToRegidxVal]

end Divu

namespace Divw

open DivRem

def spec_divw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_DIVW rs2 rs1 rd false
  pure ()

set_option maxHeartbeats 1000000 in

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
    . simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [spec.divw Main cstrs h_is_real h_is_divw]
      simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
      simp [bitVecToRegidxVal]

end Divw

namespace Divuw

open DivRem

def spec_divuw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_DIVW rs2 rs1 rd true
  pure ()

set_option maxHeartbeats 1000000 in

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
    . simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [spec.divuw Main cstrs h_is_real h_is_divuw]
      simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
      simp [bitVecToRegidxVal]

end Divuw

namespace Rem

open DivRem

def spec_rem (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_REM rs2 rs1 rd false
  pure ()

set_option maxHeartbeats 1000000 in

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
    . simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [spec.rem Main cstrs h_is_real h_is_rem]
      simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
      simp [bitVecToRegidxVal]

end Rem

namespace Remu

open DivRem

def spec_remu (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_REM rs2 rs1 rd true
  pure ()

set_option maxHeartbeats 1000000 in

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
    . simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [spec.remu Main cstrs h_is_real h_is_remu]
      simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
      simp [bitVecToRegidxVal]

end Remu

namespace Remw

open DivRem

def spec_remw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_REMW rs2 rs1 rd false
  pure ()

set_option maxHeartbeats 1000000 in

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
    . simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [spec.remw Main cstrs h_is_real h_is_remw]
      simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
      simp [bitVecToRegidxVal]

end Remw

namespace Remuw

open DivRem

def spec_remuw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_REMW rs2 rs1 rd true
  pure ()

set_option maxHeartbeats 1000000 in

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
    . simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
    . rw [if_neg (by simpa [← BitVec.toNat_inj])]
      rw [if_neg (by simpa [← BitVec.toNat_inj])]
      simp [spec.remuw Main cstrs h_is_real h_is_remuw]
      simp [Word.toBitVec64, Word.toNat]
      rw [KoalaBear.add4_into_pc_ofNat (by omega)]
      simp [bitVecToRegidxVal]

end Remuw
