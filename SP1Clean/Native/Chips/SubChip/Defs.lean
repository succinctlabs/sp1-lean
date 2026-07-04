import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Proofs.Operations.SubOperation.Formal
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.RTypeReader
import SP1Clean.Native.Readers.RegisterWrite
import SP1Clean.Model.Channels
import SP1Clean.Extracted.SubChip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The Sub chip row as a `GeneralFormalCircuit`, output = the extracted column struct

Composes `Readers.CPUState.circuit`, `SubOperation.circuit`, and `Readers.RTypeReader.circuit` as Clean
subcircuits/assertions, gates `is_real`, and returns the extracted `SubCols` struct (emitting all four
buses). SUB is **not commutative**: operand order `op_b_val - op_c_val` (= `rX(rs1) - rX(rs2)`) must
match the Sail bridge's `execute_RTYPE rs2 rs1 rd .SUB`. Program-bus opcode `2`. -/

namespace SP1Clean.SubChip

open Circuit
open Extracted (SubCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Compose the `CPUState`/`SubOperation`/`RTypeReader` sub-circuits, witness the ALU result word via
`SubOperation.populate`, gate `is_real`, and assemble the extracted `SubCols` struct. `RTypeReader`
carries opcode `2` and the four `op_a_write_value` limbs. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var (SubCols) (ZMod p)) := do
  assertion Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  let value ← witnessVector 4 (fun env =>
    SubOperation.populate
      #v[env input.op_b_val[0], env input.op_b_val[1], env input.op_b_val[2], env input.op_b_val[3]]
      #v[env input.op_c_val[0], env input.op_c_val[1], env input.op_c_val[2], env input.op_c_val[3]])
  assertion SubOperation.circuit ⟨input.op_b_val, input.op_c_val, { value := value }, input.is_real⟩
  -- `RTypeReader` is now a `GeneralFormalCircuit` (SC Phase 2pre) — composed via the GFC `CoeFun`
  -- (`subcircuitWithAssertion`), discarding its `unit` output. Its `Spec` (Contracts) is unchanged.
  let _ ← Readers.RTypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 2,
     value[0], value[1], value[2], value[3]⟩
  -- Option B: the op_a (`rd`) write Memory **push** is composed here (factored OUT of the reader), *after*
  -- `SubOperation`, so `isU64 value` (the ALU result range-check) discharges its requirement — breaking the
  -- old reader-circularity. The write access clock is the recombined low clock `+ 4` (matching the old reader).
  assertion Readers.RegisterWrite.circuit
    ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
     input.adapter.op_a, value, input.is_real⟩
  -- Inline `assertZero` (not `=== 0`, the deep Equality subcircuit) so the `is_real` booleanity is visible
  -- to `ConstraintsHold.Shallow` — required for the chip to be a `VmTables` table (A2).
  assertZero (input.is_real * (input.is_real - 1))
  return ⟨input.state, input.adapter, ⟨value⟩, input.is_real⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs SubCols main where
  channelsLawful := by
    simp [circuit_norm, main, Readers.CPUState.circuit, Readers.RTypeReader.circuit,
      Readers.RegisterWrite.circuit, SubOperation.circuit]
  localLength _ := 4
  -- `programChannel` joins the byte guarantee propagated up from `RTypeReader`'s program **pull** (W11 flip);
  -- `memoryChannel` joins from `RTypeReader`'s memory read **pulls** (W11 memory flip). The `RegisterWrite`
  -- op_a write push owes a memory requirement (declared in `circuit.channelsWithRequirements`), not a guarantee.
  channelsWithGuarantees := [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]

end SP1Clean.SubChip
