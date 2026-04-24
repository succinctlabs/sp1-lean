import SP1Foundations
import SP1Chips.Load.LoadByte.Constraints
import SP1Operations.Operation.AddrAddOperation

open LeanRV64D.Functions Sail SailState

namespace Load

namespace LoadByte

def sp1_op_a (Main : Vector (Fin KB) 47) : BitVec 5 :=
  BitVec.ofNat 5 Main[6]

def sp1_ob_b (Main : Vector (Fin KB) 47) : BitVec 5 :=
  BitVec.ofNat 5 Main[14]

def sp1_imm_c (Main : Vector (Fin KB) 47) : BitVec 12 :=
  BitVec.ofNat 12 Main[21]

def sp1_load_byte (Main : Vector (Fin KB) 47) : SailM ExecutionResult := do
  let op_a := sp1_op_a Main
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] + 4)
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[44] + 65280 * Main[45],
    65535 * Main[45], 65535 * Main[45], 65535 * Main[45]])
  return RETIRE_SUCCESS

noncomputable def spec_lb (imm : BitVec 12) (rs1 rs2 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_LOAD imm rs1 rs2 (is_unsigned := false) (width := 1)

noncomputable def spec_lbu (imm : BitVec 12) (rs1 rs2 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_LOAD imm rs1 rs2 (is_unsigned := true) (width := 1)

set_option maxHeartbeats 2000000 in
-- correct_lb unfolds Load chip + Sail memory read spec
theorem correct_lb (Main : Vector (Fin KB) 47)
    (s : SailState) (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (LoadByte.constraints Main).allHold)
    (state_cstrs : (LoadByte.constraints Main).initialState s)
    (h_is_lb : Main[45] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (sp1_imm_c Main)).toNat
      reg_val + offset + 1 < 2 ^ 64)
    (h_below_clint :
      let reg_val := Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]
      let offset := BitVec.signExtend 64 (sp1_imm_c Main)
      BitVec.toNat (reg_val + offset) + 1 ≤ 33554432) :
    let op_a := sp1_op_a Main
    let op_b := sp1_ob_b Main
    let imm_c := sp1_imm_c Main
    (spec_lb imm_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_load_byte Main).run s := by
  sorry
set_option maxHeartbeats 2000000 in
-- correct_lbu unfolds Load chip + Sail memory read spec
theorem correct_lbu (Main : Vector (Fin KB) 47)
    (s : SailState) (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (LoadByte.constraints Main).allHold)
    (state_cstrs : (LoadByte.constraints Main).initialState s)
    (h_is_lbu : Main[46] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (sp1_imm_c Main)).toNat
      reg_val + offset + 1 < 2 ^ 64)
    (h_below_clint :
      let reg_val := Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]
      let offset := BitVec.signExtend 64 (sp1_imm_c Main)
      BitVec.toNat (reg_val + offset) + 1 ≤ 33554432) :
    let op_a := sp1_op_a Main
    let op_b := sp1_ob_b Main
    let imm_c := sp1_imm_c Main
    (spec_lbu imm_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_load_byte Main).run s := by
  sorry
end LoadByte

end Load
