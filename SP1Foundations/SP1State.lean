import Mathlib
import LeanRV32IM.Defs

import SP1Foundations.SailM

/-- State for arithmetic chip verification is a program counter and register assignment map. -/
abbrev SP1State := BitVec 32 × (regidx → BitVec 32)

/-- Add `4` to the current program counter state. -/
@[reducible] def incrementPC : StateM SP1State Unit :=
  do modify (.map (· + (BitVec.ofNat _ 4)) id)

@[reducible] def setPC (new_pc : BitVec 32) : StateM SP1State Unit :=
  do modify (.map (fun _old_pc => new_pc) id)

/-- Modify the register map state -/
@[reducible] def update_reg (idx : regidx) (v : BitVec 32) : StateM SP1State Unit :=
  do modify (.map id (Function.update · idx v))

@[reducible] def get_reg (idx : regidx) : StateM SP1State (BitVec 32) :=
  do return (← get).2 idx

-- dt: below isn't enough to handle read and write both
-- we could maybe make something like this work assuming unique state constraints

-- section ControlFlowState

-- structure SP1ControlFlowState where
--   pc : Fin BB
--   shard : Fin BB
--   clk : Fin BB

-- @[reducible] def increment_pc (c : Fin BB) : StateM SP1ControlFlowState Unit :=
--   do modify fun st => { pc := st.pc + c, __ := st }

-- @[reducible] def increment_shard (c : Fin BB) : StateM SP1ControlFlowState Unit :=
--   do modify fun st => { shard := st.shard + c, __ := st }

-- @[reducible] def increment_clk (c : Fin BB) : StateM SP1ControlFlowState Unit :=
--   do modify fun st => { clk := st.clk + c, __ := st }

-- @[reducible] def set_pc (new_pc : Fin BB) : StateM SP1ControlFlowState Unit :=
--   do modify fun st => { pc := new_pc, __ := st }

-- @[reducible] def set_shard (new_shard : Fin BB) : StateM SP1ControlFlowState Unit :=
--   do modify fun st => { shard := new_shard, __ := st }

-- @[reducible] def set_clk (new_clk : Fin BB) : StateM SP1ControlFlowState Unit :=
--   do modify fun st => { clk := new_clk, __ := st }

-- def SP1ConstraintList.toControlFlowM : SP1ConstraintList → StateM SP1ControlFlowState Unit
--   | .send _ mult :: cs => sorry
--   | .receive _ mult :: cs => sorry
--   | _ :: cs => toControlFlowM cs
--   | [] => return ()

-- end ControlFlowState
