import SP1Foundations
import SP1Chips.Store.StoreByte.Constraints
import SP1Operations.Operation.AddrAddOperation

open LeanRV64D.Functions Sail SailState

namespace Store

namespace StoreByte

noncomputable def spec_sb (imm : BitVec 12) (rs1 rs2 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_STORE imm rs1 rs2 (width := 1)

def sp1_op_a (Main : Vector (Fin KB) 50) : BitVec 5 :=
  BitVec.ofNat 5 Main[6]

def sp1_ob_b (Main : Vector (Fin KB) 50) : BitVec 5 :=
  BitVec.ofNat 5 Main[14]

def sp1_imm_c (Main : Vector (Fin KB) 50) : BitVec 12 :=
  BitVec.ofNat 12 (Word.toNat #v[Main[21], Main[22], Main[23], Main[24]])

def sp1_sb (Main : Vector (Fin KB) 50) : SailM ExecutionResult := do
  let op_a := sp1_op_a Main
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  let addr : BitVec 64 := Word.toBitVec64 #v[Main[26], Main[27], Main[28], 0]
  Sail.ConcurrencyInterfaceV1.write_ram 64 1 0#64 addr
    (Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]])
  return RETIRE_SUCCESS

theorem correct (Main : Vector (Fin KB) 50)
    (s : SailState) (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (StoreByte.constraints Main).allHold)
    (state_cstrs : (StoreByte.constraints Main).initialState s)
    (h_is_real : Main[49] = 1)
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
    (spec_sb imm_c (.Regidx op_a) (.Regidx op_b)).run s = (sp1_sb Main).run s := by
  sorry
end StoreByte

end Store
