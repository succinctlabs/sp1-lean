import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Proofs.Operations.AddwOperation.Formal
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.ALUTypeReader
import SP1Clean.Native.Readers.RegisterWrite
import SP1Clean.Model.Channels
import SP1Clean.Extracted.AddwChip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The ADDW chip row as a `GeneralFormalCircuit`, output = the extracted column struct

Composes `Readers.CPUState.circuit`, the witnessed `AddwOperation.circuit`, and
`Readers.ALUTypeReader.circuit` as Clean subcircuits/assertions, gates `is_real`, and returns the
extracted `AddwCols` struct (emitting all four buses: State, Byte, Memory, Program).

W-instruction: result is 2 limbs + sign bit (`addw_operation.value`/`addw_operation.msb.msb`); the
64-bit `op_a` write is the sign-extended word `[v0, v1, msb·65535, msb·65535]`. Adapter is the
immediate-capable `ALUTypeReader` (unlike SUBW's `RTypeReader`); Program-bus opcode is `19`. -/

namespace SP1Clean.AddwChip

open Circuit
open Extracted (AddwCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Compose the `CPUState`/`AddwOperation`/`ALUTypeReader` column blocks as Clean subcircuits/assertions
and assemble the extracted `AddwCols` struct. The chip witnesses the result low limbs + sign bit via the
operation's `populate` (`addwValueWitness`/`addwMsbWitness`), then composes the demoted `AddwOperation`
gadget as a Clean `assertion`. The `ALUTypeReader`'s four `op_a_write_value` limbs are the
**sign-extended** W result `[value[0], value[1], msb·65535, msb·65535]` (mirroring `Extracted/AddwChip.lean`'s
`ALUTypeReader.asserts … 19 #v[…value[0], …value[1], msb·65535, msb·65535] …`); the Program-bus opcode is
`19`. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var (AddwCols) (ZMod p)) := do
  assertion Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  let value ← witnessVector 2 (fun env =>
    AddwOperation.addwValueWitness
      #v[env input.op_b_val[0], env input.op_b_val[1], env input.op_b_val[2], env input.op_b_val[3]]
      #v[env input.op_c_val[0], env input.op_c_val[1], env input.op_c_val[2], env input.op_c_val[3]])
  let msb ← witnessVector 1 (fun env =>
    #v[AddwOperation.addwMsbWitness
      #v[env input.op_b_val[0], env input.op_b_val[1], env input.op_b_val[2], env input.op_b_val[3]]
      #v[env input.op_c_val[0], env input.op_c_val[1], env input.op_c_val[2], env input.op_c_val[3]]])
  assertion AddwOperation.circuit ⟨input.op_b_val, input.op_c_val, ⟨value, ⟨msb[0]⟩⟩, input.is_real⟩
  assertion Readers.ALUTypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 19,
     value[0], value[1], msb[0] * 65535, msb[0] * 65535⟩
  -- Option B: the op_a (`rd`) write Memory **push** is composed here (factored OUT of the reader), *after*
  -- `AddwOperation`, so `isU64 (resultWord)` (the sign-extended W result, range-checked by the operation)
  -- discharges its requirement. The written value is the sign-extended W word
  -- `#v[value[0], value[1], msb·65535, msb·65535]`; the write access clock is the recombined low clock `+ 4`.
  assertion Readers.RegisterWrite.circuit
    ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
     input.adapter.op_a, #v[value[0], value[1], msb[0] * 65535, msb[0] * 65535], input.is_real⟩
  -- Inline `assertZero` (not `=== 0`) so the `is_real` booleanity is visible to
  -- `ConstraintsHold.Shallow` — required for the chip to be a `VmTables` table (A2).
  assertZero (input.is_real * (input.is_real - 1))
  return ⟨input.state, input.adapter, ⟨value, ⟨msb[0]⟩⟩, input.is_real⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs AddwCols main where
  channelsLawful := by
    simp [circuit_norm, main, AddwOperation.circuit, Readers.ALUTypeReader.circuit,
      Readers.CPUState.circuit, Readers.RegisterWrite.circuit]
  -- 2 result limbs + 1 sign bit; readers are `assertion`s (`localLength 0`).
  localLength _ := 3
  -- `programChannel` joins the byte guarantee propagated up from `ALUTypeReader`'s program **pull** (W11 flip);
  -- `memoryChannel` joins from `ALUTypeReader`'s memory read **pulls** (W11 memory flip). The `RegisterWrite`
  -- op_a write push owes a memory requirement (declared in `circuit.channelsWithRequirements`), not a guarantee.
  channelsWithGuarantees := [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]

end SP1Clean.AddwChip
