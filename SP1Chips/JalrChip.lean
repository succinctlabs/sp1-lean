import SP1Operations.Operation.AddOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ITypeReader
import SP1Chips.Jalr.Constraints

namespace Jalr

open Sail SailState BitVec LeanRV64D.Functions

attribute [simp] ofBool
  update updateSubrange'
  assert PreSail.assert
  LeanRV64D.Functions.RETIRE_SUCCESS

variable (Main : Vector (Fin KB) 35) (s : SailState)

def sp1_op_a (Main : Vector (Fin KB) 35) : BitVec 5 := BitVec.ofNat 5 Main[6].val

def sp1_op_b (Main : Vector (Fin KB) 35) : BitVec 5 := BitVec.ofNat 5 Main[14].val

def sp1_op_c (Main : Vector (Fin KB) 35) : BitVec 12 := BitVec.ofNat 12 Main[21].val

def sp1_jalr (Main : Vector (Fin KB) 35) : SailM Unit := do
  let op_a := sp1_op_a Main
  writeReg Register.nextPC (Word.toBitVec64 #v[Main[26], Main[27], Main[28], Main[29]])
  wX_bits (.Regidx op_a) (Word.toBitVec64 #v[Main[30], Main[31], Main[32], Main[33]])

noncomputable def spec_jalr (imm : BitVec 12) (rs1 rd : regidx) : SailM Unit := do
  writeReg Register.nextPC ((← readReg Register.PC) + 4#64)
  _ ← execute_JALR imm rs1 rd

theorem JALR_correct
    (cstrs : (constraints Main).allHold)
    (h_is_real : Main[25] = 1)
    (hs : isInitialized s)
    (h_valid_pc : (Main[15].val + Main[21].val) % 4 = 0)
    (state_cstrs : (constraints Main).initialState s) :
    let op_b := sp1_op_b Main
    let op_a := sp1_op_a Main
    let op_c := sp1_op_c Main
    (spec_jalr op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_jalr Main).run s := by
  sorry

end Jalr
