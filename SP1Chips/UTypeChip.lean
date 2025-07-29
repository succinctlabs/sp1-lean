import SP1Chips.UType.Constraints


namespace UType

open BitVec

open Sail SailState BitVec LeanRV64IM.Functions

variable (Main : Vector (Fin BB) 31) (s : SailState)

def spec_utype (imm : (BitVec 20)) (rd : regidx) (op : uop) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  let _ ← execute_UTYPE imm rd op

/-- The destination register for the operation-/
def sp1_op_a (Main : Vector (Fin BB) 31)
    (cstrs : (constraints Main).allHold)
    (h_is_real : Main[30] = 1) : BitVec 5 :=
  sorry

/-- The immediate used to determine the next program counter. -/
def sp1_op_b (Main : Vector (Fin BB) 31)
    (cstrs : (constraints Main).allHold)
    (h_is_real : Main[30] = 1) : BitVec 20 :=
  sorry

def sp1_op_c (Main : Vector (Fin BB) 31) : sorry := sorry

def sp1_utype (Main : Vector (Fin BB) 31)
    (cstrs : (constraints Main).allHold)
    (h_is_real : Main[30] = 1) : SailM Unit :=

  return ()


def utype_chip_correct (Main : Vector (Fin BB) 31)
    (cstrs : (constraints Main).allHold)
    (h_is_real : Main[30] = 1)
    (state_cstrs : (constraints Main).initialState s)
    (h_misa : Register.misa ∈ s.regs) :
    sp1_utype Main cstrs h_is_real = sorry := by
  simp [constraints, sub_eq_zero] at cstrs

  sorry

end UType
