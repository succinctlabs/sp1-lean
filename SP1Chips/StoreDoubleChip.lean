import SP1Foundations
import SP1Chips.Store.StoreDouble.Constraints
import SP1Operations.Operation.AddrAddOperation

open LeanRV64D.Functions Sail SailState

namespace Store

namespace StoreDouble

noncomputable def spec_sb (imm : BitVec 12) (rs1 rs2 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  let width : ℕ := 8 -- eight bytes
  execute_STORE imm rs1 rs2 width

def sp1_op_a (Main : Vector (Fin KB) 39) : BitVec 5 :=
  BitVec.ofNat 5 Main[6]

def sp1_ob_b (Main : Vector (Fin KB) 39) : BitVec 5 :=
  BitVec.ofNat 5 Main[14]

def sp1_imm_c (Main : Vector (Fin KB) 39) : BitVec 12 :=
  BitVec.ofNat 12 (Word.toNat #v[Main[21], Main[22], Main[23], Main[24]])

def sp1_sb (Main : Vector (Fin KB) 39) : SailM ExecutionResult := do
  let op_a := sp1_op_a Main
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  let addr : BitVec 64 := Word.toBitVec64 #v[Main[26], Main[27], Main[28], 0]
  Sail.ConcurrencyInterfaceV1.write_ram 64 8 0#64 addr
    (Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]])
  return RETIRE_SUCCESS

theorem correct (Main : Vector (Fin KB) 39)
    (s : SailState) (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (StoreDouble.constraints Main).allHold)
    (state_cstrs : (StoreDouble.constraints Main).initialState s)
    (h_is_real : Main[38] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (sp1_imm_c Main)).toNat
      reg_val + offset + 8 < 2 ^ 64)
    -- dt: This should eventually come from trusted instruction assumption
    -- should try to simplify it more first to minimize assumptions though
    (h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 (Word.toNat #v[Main[21], Main[22], Main[23], Main[24]])))) 8 = true)
    (h_below_clint :
      let reg_val := Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]
      let offset := BitVec.signExtend 64 (sp1_imm_c Main)
      BitVec.toNat (reg_val + offset) + 8 ≤ 33554432) :
    let op_a := sp1_op_a Main
    let op_b := sp1_ob_b Main
    let imm_c := sp1_imm_c Main
    (spec_sb imm_c (.Regidx op_a) (.Regidx op_b)).run s = (sp1_sb Main).run s := by
  sorry
end StoreDouble

end Store
