import SP1Chips.UType.Constraints


namespace UTypeChip

open BitVec

open Sail SailState BitVec LeanRV64IM.Functions

variable (Main : Vector (Fin BB) 31) (s : SailState)

def spec_utype (imm : (BitVec 20)) (rd : regidx) (op : uop) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  let _ ← execute_UTYPE imm rd op

#check execute_UTYPE

end UTypeChip
