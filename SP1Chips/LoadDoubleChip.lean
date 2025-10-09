import SP1Foundations
import SP1Chips.Load.LoadDouble.Constraints

open LeanRV64D.Functions Sail SailState

namespace Load

namespace LoadDouble

def sp1_op_a (Main : Vector (Fin KB) 49) : BitVec 5 :=
  BitVec.ofNat 5 Main[6]

def sp1_ob_b (Main : Vector (Fin KB) 49) : BitVec 5 :=
  BitVec.ofNat 5 Main[14]

def sp1_imm_c (Main : Vector (Fin KB) 49) : BitVec 12 :=
  BitVec.ofNat 12 Main[21]

noncomputable def spec_ld (imm : BitVec 12) (rs1 rs2 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_LOAD imm rs1 rs2 (is_unsigned := true) (width := 8)
