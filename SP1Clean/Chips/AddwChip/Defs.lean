import SP1Clean.Specs.Chip
import SP1Clean.Operations.AddwOperation.Formal
import SP1Clean.Readers.CPUState
import SP1Clean.Readers.ALUTypeReader
import SP1Clean.Foundations.Channels
import SP1Clean.Extracted.AddwChip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The ADDW chip row as a `GeneralFormalCircuit`, output = the extracted column struct

Migrated onto the **reader/bus pattern** (direct mirror of `Chips/SubwChip.lean`): composes
`Readers.CPUState.circuit`, the witnessed `AddwOperation.circuit`, and `Readers.ALUTypeReader.circuit`
as Clean subcircuits/assertions, gates the row with `is_real`, and **returns the extracted
`Extracted.AddwCols` struct**. So an ADDW row now emits the same four buses (State, Byte, Memory,
Program) and slots into the heterogeneous trace alongside Add/Sub/Subw.

ADDW is a W-instruction: the gadget's result is a **2-limb value + a sign bit**
(`addw_operation.value`, `addw_operation.msb.msb`), and the 64-bit `op_a` write value the reader carries
is the sign-extended word `[v0, v1, msb·65535, msb·65535]` (= `AddwOperation.resultWord`). Unlike SUBW,
ADDW's adapter is the **immediate-capable `ALUTypeReader`** (SP1's `AddwCols.adapter : ALUTypeReader`); the
Program-bus opcode is `19`. ADDW operates on the low 32 bits of each operand and sign-extends. -/

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
  input.is_real * (input.is_real - 1) === 0
  return ⟨input.state, input.adapter, ⟨value, ⟨msb[0]⟩⟩, input.is_real⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs AddwCols main where
  channelsLawful := by simp [circuit_norm, main, AddwOperation.circuit, Readers.ALUTypeReader.circuit, Readers.CPUState.circuit]
  -- The chip witnesses only the 2 result limbs + 1 sign bit (via `populate`); `AddwOperation` is a
  -- `FormalAssertion` (its byte/U16MSB constraints are bus pulls). The two readers are `assertion`s
  -- (`localLength 0`), the binary gate adds 0. 2 + 1 = 3.
  localLength _ := 3
  channelsWithGuarantees := [byteChannel.toRawGated]
  channelsWithRequirements :=
    [byteChannel.toRawGated, stateChannel.toRawGated, memoryChannel.toRaw, programChannel.toRaw]

end SP1Clean.AddwChip
