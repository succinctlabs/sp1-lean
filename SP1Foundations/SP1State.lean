import SP1Foundations.Constraint

/-- State for arithmetic chip verification is a program counter and register assignment map. -/
abbrev SP1State := BitVec 32 × (regidx → BitVec 32)

/-- Add `4` to the current program counter state. -/
@[reducible] def incrementPC : StateM SP1State Unit :=
  do modify (.map (· + (BitVec.ofNat _ 4)) id)

@[reducible] def set_pc (new_pc : BitVec 32) : StateM SP1State Unit :=
  do modify (.map (fun _old_pc => new_pc) id)

/-- Modify the register map state -/
@[reducible] def update_reg (idx : regidx) (v : BitVec 32) : StateM SP1State Unit :=
  do modify (.map id (Function.update · idx v))

@[reducible] def get_reg (idx : regidx) : StateM SP1State (BitVec 32) :=
  do return (← get).2 idx
