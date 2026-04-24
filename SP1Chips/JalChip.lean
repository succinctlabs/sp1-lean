import SP1Operations.Operation.AddOperation
import SP1Chips.Jal.Constraints

namespace Jal

open BitVec

open Sail SailState BitVec LeanRV64D.Functions

attribute [simp] assert PreSail.assert
  RETIRE_SUCCESS

variable (Main : Vector (Fin KB) 31) (s : SailState)

lemma op_a_lt32_of_constraints {Main : Vector (Fin KB) 31}
    (_ : (constraints Main).allHold) (_ : Main[30] = 1) : Main[6].val < 32 := by
  sorry

def sp1_op_a (cstrs : (constraints Main).allHold) (h_is_real : Main[30] = 1) : BitVec 5 :=
  Main[6].val#'(op_a_lt32_of_constraints cstrs h_is_real)

def sp1_op_b : BitVec 21 := BitVec.ofNat 21 (Main[14].val + Main[15].val * 65536)

def sp1_jal (Main : Vector (Fin KB) 31) : SailM Unit := do
  let op_a := regidx.Regidx (BitVec.ofNat 5 Main[6].val)
  set_next_pc (Word.toBitVec64 #v[Main[22], Main[23], Main[24], Main[25]])
  wX_bits op_a (Word.toBitVec64 #v[Main[26], Main[27], Main[28], Main[29]])

noncomputable def spec_jal (imm : BitVec 21) (rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  let _ ← execute_JAL imm rd

theorem SP1JAL_correct
    (cstrs : (constraints Main).allHold)
    (h_is_real : Main[30] = 1)
    (state_cstrs : (constraints Main).initialState s)
    (hs : SailState.isInitialized s) :
    let op_a := sp1_op_a Main cstrs h_is_real
    let op_b := sp1_op_b Main
    (spec_jal op_b (.Regidx op_a)).run s = (sp1_jal Main).run s := by
  sorry

end Jal
