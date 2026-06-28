import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Proofs.Operations.SubwOperation.Formal
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.RTypeReader
import SP1Clean.Model.Channels
import SP1Clean.Extracted.SubwChip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The SUBW chip row as a `GeneralFormalCircuit`, output = the extracted column struct

Composes `Readers.CPUState.circuit`, the witnessed `SubwOperation.circuit`, and
`Readers.RTypeReader.circuit` as Clean subcircuits/assertions, gates `is_real`, and returns the
extracted `SubwCols` struct (emitting all four buses).

W-instruction: result is 2 limbs + sign bit (`subw_operation.value`/`subw_operation.msb.msb`); the
64-bit `op_a` write is the sign-extended word `[v0, v1, msb·65535, msb·65535]`. Adapter is the
`RTypeReader` (unlike ADDW's `ALUTypeReader`); Program-bus opcode `20`. SUBW is **not commutative**:
operand order `op_b_val - op_c_val` must match `execute_RTYPEW rs2 rs1 rd .SUBW`. -/

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
  -- Inline `assertZero` (not `=== 0`) so the `is_real` booleanity is visible to
  -- `ConstraintsHold.Shallow` — required for the chip to be a `VmTables` table (A2).
  assertZero (input.is_real * (input.is_real - 1))
  return ⟨input.state, input.adapter, ⟨value, ⟨msb[0]⟩⟩, input.is_real⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs SubwCols main where
  channelsLawful := by simp [circuit_norm, main, Readers.CPUState.circuit, Readers.RTypeReader.circuit, SubwOperation.circuit]
  -- 2 result limbs + 1 sign bit; readers are `assertion`s (`localLength 0`).
  localLength _ := 3
  -- `programChannel` joins the byte guarantee propagated up from `RTypeReader`'s program **pull** (W11 flip).
  channelsWithGuarantees := [byteChannel.toRaw, programChannel.toRaw]

end SP1Clean.SubwChip
