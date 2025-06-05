import SP1Foundations
import SP1Operations

structure AddChip where
  state : CPUState
  adapter : RTypeReader U16
  add_operation : AddOperation
  is_real : U1

namespace AddChip

-- What we expect the generated constraint to look like:
def constraints 
  (chip : AddChip) : Prop :=
  let ⟨state, adapter, add_operation, is_real⟩ := chip
  state.spec (state.pc + 4) 4 is_real
  ∧ add_operation.spec adapter.b adapter.c is_real
  ∧ adapter.spec state.shard state.clk state.pc 0 /- Opcode::ADD -/ add_operation.value is_real

end AddChip
