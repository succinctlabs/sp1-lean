import SP1Clean.Specs.Chip
import SP1Clean.Operations.SubwOperation.Formal
import SP1Clean.Readers.CPUState
import SP1Clean.Readers.RTypeReader
import SP1Clean.Foundations.Channels
import SP1Clean.Extracted.SubwChip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The SUBW chip row as a `GeneralFormalCircuit`, output = the extracted column struct

Migrated onto the **reader/bus pattern** (direct mirror of `Chips/SubChip.lean`): composes
`Readers.CPUState.circuit`, the witnessed `SubwOperation.circuit`, and `Readers.RTypeReader.circuit` as
Clean subcircuits/assertions, gates the row with `is_real`, and **returns the extracted `Extracted.SubwCols`
struct**. So a SUBW row now emits the same four buses (State, Byte, Memory, Program) and slots into the
heterogeneous trace alongside Add/Sub.

SUBW is a W-instruction: the gadget's result is a **2-limb value + a sign bit** (`subw_operation.value`,
`subw_operation.msb.msb`), and the 64-bit `op_a` write value the reader carries is the sign-extended word
`[v0, v1, msb·65535, msb·65535]` (= `SubwOperation.resultWord`). SUBW's adapter is the register
`RTypeReader` (SP1's `SubwCols.adapter : RTypeReader`, unlike `AddwCols`'s `ALUTypeReader`); the Program-bus
opcode is `20`. SUBW is **not commutative**, so the order `op_b_val - op_c_val` (= `rX(rs1) - rX(rs2)`) is
load-bearing and must match the Sail bridge's `execute_RTYPEW rs2 rs1 rd .SUBW`. -/

namespace SP1Clean.SubwChip

open Circuit
open Extracted (SubwCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Compose the three column blocks as Clean subcircuits/assertions and assemble the extracted `SubwCols`
struct. The `RTypeReader`'s four `op_a_write_value` limbs are the **sign-extended** W result
`[value[0], value[1], msb·65535, msb·65535]` (mirroring `Extracted/SubwChip.lean`'s `RTypeReader.asserts …
20 #v[…value[0], …value[1], msb·65535, msb·65535] …`); the Program-bus opcode is `20`. Only the
`SubwOperation` gadget witnesses; the two readers are `assertion`s over the threaded `state`/`adapter`. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var (SubwCols) (ZMod p)) := do
  assertion Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  -- The chip witnesses the result low limbs + sign bit via the operation's `populate`, then composes the
  -- demoted `SubwOperation` gadget as a Clean `assertion`.
  let value ← witnessVector 2 (fun env =>
    SubwOperation.subwValueWitness
      #v[env input.op_b_val[0], env input.op_b_val[1], env input.op_b_val[2], env input.op_b_val[3]]
      #v[env input.op_c_val[0], env input.op_c_val[1], env input.op_c_val[2], env input.op_c_val[3]])
  let msb ← witnessVector 1 (fun env =>
    #v[SubwOperation.subwMsbWitness
      #v[env input.op_b_val[0], env input.op_b_val[1], env input.op_b_val[2], env input.op_b_val[3]]
      #v[env input.op_c_val[0], env input.op_c_val[1], env input.op_c_val[2], env input.op_c_val[3]]])
  assertion SubwOperation.circuit ⟨input.op_b_val, input.op_c_val, ⟨value, ⟨msb[0]⟩⟩, input.is_real⟩
  assertion Readers.RTypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 20,
     value[0], value[1], msb[0] * 65535, msb[0] * 65535⟩
  input.is_real * (input.is_real - 1) === 0
  return ⟨input.state, input.adapter, ⟨value, ⟨msb[0]⟩⟩, input.is_real⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs SubwCols main where
  channelsLawful := by simp [circuit_norm, main, Readers.CPUState.circuit, Readers.RTypeReader.circuit, SubwOperation.circuit]
  -- The chip witnesses only the 2 result limbs + 1 sign bit now (via `populate`); `SubwOperation` is a
  -- `FormalAssertion` (its U16MSB/byte constraints are bus pulls). The readers are `assertion`s
  -- (`localLength 0`), the binary gate adds 0.
  localLength _ := 3
  channelsWithGuarantees := [byteChannel.toRawGated]
  channelsWithRequirements :=
    [byteChannel.toRawGated, stateChannel.toRawGated, memoryChannel.toRaw, programChannel.toRaw]

end SP1Clean.SubwChip
