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

/-

Asserting expr 3: `(is_real * (is_real - 1))`
Asserting expr 3: `(is_real * (is_real - 1))`
Asserting expr 15: `(is_real * (((((adapter.op_b_memory.prev_value[0] + adapter.op_c_memory.prev_value[0]) - add_operation.value[0]) + 0) * 2013235201) * (((((adapter.op_b_memory.prev_value[0] + adapter.op_c_memory.prev_value[0]) - add_operation.value[0]) + 0) * 2013235201) - 1)))`
Asserting expr 25: `(is_real * (((((adapter.op_b_memory.prev_value[1] + adapter.op_c_memory.prev_value[1]) - add_operation.value[1]) + ((((adapter.op_b_memory.prev_value[0] + adapter.op_c_memory.prev_value[0]) - add_operation.value[0]) + 0) * 2013235201)) * 2013235201) * (((((adapter.op_b_memory.prev_value[1] + adapter.op_c_memory.prev_value[1]) - add_operation.value[1]) + ((((adapter.op_b_memory.prev_value[0] + adapter.op_c_memory.prev_value[0]) - add_operation.value[0]) + 0) * 2013235201)) * 2013235201) - 1)))`
Asserting expr 3: `(is_real * (is_real - 1))`
Asserting expr 3: `(is_real * (is_real - 1))`
Asserting expr 46: `(adapter.op_a_0 * (add_operation.value[0] - 0))`
Asserting expr 48: `(adapter.op_a_0 * (add_operation.value[1] - 0))`
Asserting expr 3: `(is_real * (is_real - 1))`
Asserting expr 3: `(is_real * (is_real - 1))`
Asserting expr 3: `(is_real * (is_real - 1))`
Sends: AirInteraction { values: [6, add_operation.value[0], 16, 0], multiplicity: is_real, kind: Byte }
Sends: AirInteraction { values: [6, add_operation.value[1], 16, 0], multiplicity: is_real, kind: Byte }
Sends: AirInteraction { values: [state.shard, (((16384 * state.clk_high_limb) + state.clk_low_limb) + 4), (state.pc + 4)], multiplicity: is_real, kind: State }
Sends: AirInteraction { values: [6, state.clk_high_limb, 14, 0], multiplicity: is_real, kind: Byte }
Sends: AirInteraction { values: [6, state.clk_low_limb, 14, 0], multiplicity: is_real, kind: Byte }
Sends: AirInteraction { values: [state.pc, 0, adapter.op_a, (0 + adapter.op_b), 0, (0 + adapter.op_c), 0, adapter.op_a_0, 0, 0], multiplicity: is_real, kind: Program }
Sends: AirInteraction { values: [6, adapter.op_a_memory.access_timestamp.diff_low_limb, 14, 0], multiplicity: is_real, kind: Byte }
Sends: AirInteraction { values: [6, (((((((16384 * state.clk_high_limb) + state.clk_low_limb) + 3) - adapter.op_a_memory.access_timestamp.prev_clk) - 1) - adapter.op_a_memory.access_timestamp.diff_low_limb) * 2013143041), 14, 0], multiplicity: is_real, kind: Byte }
Sends: AirInteraction { values: [state.shard, adapter.op_a_memory.access_timestamp.prev_clk, adapter.op_a, adapter.op_a_memory.prev_value[0], adapter.op_a_memory.prev_value[1]], multiplicity: is_real, kind: Memory }
Sends: AirInteraction { values: [6, adapter.op_b_memory.access_timestamp.diff_low_limb, 14, 0], multiplicity: is_real, kind: Byte }
Sends: AirInteraction { values: [6, (((((((16384 * state.clk_high_limb) + state.clk_low_limb) + 2) - adapter.op_b_memory.access_timestamp.prev_clk) - 1) - adapter.op_b_memory.access_timestamp.diff_low_limb) * 2013143041), 14, 0], multiplicity: is_real, kind: Byte }
Sends: AirInteraction { values: [state.shard, adapter.op_b_memory.access_timestamp.prev_clk, adapter.op_b, adapter.op_b_memory.prev_value[0], adapter.op_b_memory.prev_value[1]], multiplicity: is_real, kind: Memory }
Sends: AirInteraction { values: [6, adapter.op_c_memory.access_timestamp.diff_low_limb, 14, 0], multiplicity: is_real, kind: Byte }
Sends: AirInteraction { values: [6, (((((((16384 * state.clk_high_limb) + state.clk_low_limb) + 1) - adapter.op_c_memory.access_timestamp.prev_clk) - 1) - adapter.op_c_memory.access_timestamp.diff_low_limb) * 2013143041), 14, 0], multiplicity: is_real, kind: Byte }
Sends: AirInteraction { values: [state.shard, adapter.op_c_memory.access_timestamp.prev_clk, adapter.op_c, adapter.op_c_memory.prev_value[0], adapter.op_c_memory.prev_value[1]], multiplicity: is_real, kind: Memory }
Receives: AirInteraction { values: [state.shard, ((16384 * state.clk_high_limb) + state.clk_low_limb), state.pc], multiplicity: is_real, kind: State }
Receives: AirInteraction { values: [state.shard, (((16384 * state.clk_high_limb) + state.clk_low_limb) + 3), adapter.op_a, add_operation.value[0], add_operation.value[1]], multiplicity: is_real, kind: Memory }
Receives: AirInteraction { values: [state.shard, (((16384 * state.clk_high_limb) + state.clk_low_limb) + 2), adapter.op_b, adapter.op_b_memory.prev_value[0], adapter.op_b_memory.prev_value[1]], multiplicity: is_real, kind: Memory }
Receives: AirInteraction { values: [state.shard, (((16384 * state.clk_high_limb) + state.clk_low_limb) + 1), adapter.op_c, adapter.op_c_memory.prev_value[0], adapter.op_c_memory.prev_value[1]], multiplicity: is_real, kind: Memory }


-/
