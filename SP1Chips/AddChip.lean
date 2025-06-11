import SP1Foundations
import SP1Operations.AddOperation
import LeanRV32D.RiscvInstsEnd
import LeanRV32D.RiscvRegs
import SP1Operations.CPUState
import SP1Operations.RTypeReader

open LeanRV32D.Functions
open Sail
open PreSail (SequentialState)

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
  ∧ constraintSet_toProp (add_operation.constraints adapter.b adapter.c is_real)
  ∧ adapter.spec state.shard state.clk state.pc 0 /- Opcode::ADD -/ add_operation.value is_real

/- def read  -/
/-   (chip : AddChip) -/
/-   (rs1 rs2 : regidx) : SailM (BitVec 32 × BitVec 32 × (rs1_val = chip.adapter.b.toBV32_U16 ∧ rs2_val = chip.adapter.c.toBV32_U16)) := do -/
/-     let rs1_val ← rx_bits rs1 -/
/-     let rs2_val ← rx_bits rs2 -/
/-     pure -/
/-       ⟨rs1_val, -/
/-         ⟨rs2_val, -/
/-         sorry -/
/-         ⟩ -/
/-       ⟩ -/

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

def sp1_add (chip : AddChip) (constraints : chip.constraints) (h_is_real : chip.is_real = U1.one) (rd rs1 rs2 : regidx) (read_b : chip.adapter.read_b_fun rs1) (read_c : chip.adapter.read_c_fun rs2) : SailM Unit := do
    -- Model YOUR implementation's behavior
    writeReg Register.nextPC (BitVec.addInt (← readReg Register.PC) 4)
    /- let ⟨rs1_val, ⟨rs2_val, matching⟩⟩ ← chip.read rs1 rs2 -/
    let rs1_val ← rX_bits rs1
    let rs2_val ← rX_bits rs2
    /- let ⟨rs1_val, mem_read_1⟩ ← read_b -/
    /- let ⟨rs2_val, mem_read_2⟩ ← read_c -/
    /- let ⟨_, ⟨h_constraints_2, _⟩⟩ := constraints -/
    by
      /- let h_add := (chip.add_operation.correct chip.adapter.b chip.adapter.c chip.is_real constraints.right.left) h_is_real -/
      /- rw [←mem_read_1, ←mem_read_2] at h_add -/
      /- let res := chip.add_operation.value.toBV32_U16 -/
      exact wX_bits rd chip.add_operation.value.toBV32_U16

/- noncomputable -/ def spec_add (rd rs1 rs2 : regidx) : SailM Unit := do
  writeReg Register.nextPC (BitVec.addInt (← readReg Register.PC) 4)
  /- let _ ← execute (.RTYPE ⟨rs2, rs1, rd, rop.ADD⟩) -/ -- `execute` is uncomputable...?
  let _ ← execute_RTYPE rs2 rs1 rd rop.ADD
  pure ()

theorem sp1_add_implies_spec_add (chip : AddChip) (constraints : chip.constraints) (h_is_real : chip.is_real = U1.one) (rd rs1 rs2 : regidx) (read_b : chip.adapter.read_b_fun rs1) (read_c : chip.adapter.read_c_fun rs2) (s : PreSail.SequentialState RegisterType trivialChoiceSource) :
  let res := (sp1_add chip constraints h_is_real rd rs1 rs2 read_b read_c).run s
  let res_spec := (spec_add rd rs1 rs2).run s
  res = res_spec :=
  by
    simp [EStateM.run]
    simp [sp1_add, spec_add, /- execute, -/ execute_RTYPE]
    let add_spec := (chip.add_operation.correct chip.adapter.b chip.adapter.c chip.is_real constraints.right.left) h_is_real
    simp [RTypeReader.read_b_fun] at read_b
    rw [read_b]
    simp [RTypeReader.read_c_fun] at read_c
    rw [read_c]
    rw [←add_spec]
    rw [pure_bind, pure_bind]
    rfl
