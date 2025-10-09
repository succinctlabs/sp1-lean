import SP1Foundations
import SP1Chips.Load.LoadWord.Constraints

open LeanRV64D.Functions Sail SailState

namespace Load

namespace LoadByte

def sp1_op_a (Main : Vector (Fin KB) 49) : BitVec 5 :=
  BitVec.ofNat 5 Main[6]

def sp1_ob_b (Main : Vector (Fin KB) 49) : BitVec 5 :=
  BitVec.ofNat 5 Main[14]

def sp1_imm_c (Main : Vector (Fin KB) 49) : BitVec 12 :=
  BitVec.ofNat 12 Main[21]

def sp1_load_byte (Main : Vector (Fin KB) 49) : SailM ExecutionResult := do
  let op_a := sp1_op_a Main
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] + 4)
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[44] + 65280 * Main[45],
    65535 * Main[45], 65535 * Main[45], 65535 * Main[45]])
  return RETIRE_SUCCESS

noncomputable def spec_lb (imm : BitVec 12) (rs1 rs2 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_LOAD imm rs1 rs2 (is_unsigned := false) (width := 4)

-- set_option debug.skipKernelTC true in
-- set_option maxHeartbeats 2000000 in
-- theorem correct_lb (Main : Vector (Fin KB) 49)
--     (s : SailState) (hs : SailState.isInitialized s)
--     (hs_config : SailState.isValidMemConfig s hs)
--     (h_cstrs : (LoadByte.constraints Main).allHold)
--     (state_cstrs : (LoadByte.constraints Main).initialState s)
--     (h_is_lb : Main[46] = 1)
--     (h_fits_in_mem :
--       let reg_val := (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat
--       let offset := (BitVec.signExtend 64 (sp1_imm_c Main)).toNat
--       reg_val + offset + 1 < 2^64) :
--     let op_a := sp1_op_a Main
--     let op_b := sp1_ob_b Main
--     let imm_c := sp1_imm_c Main
--     (spec_lb imm_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_load_byte Main).run s := by
--   extract_lets op_a op_b imm_c
