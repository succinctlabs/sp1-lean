import SP1Clean.Math.Word
import SP1Clean.Model.Channels
import SP1Clean.Model.ByteTable
import SP1Clean.FormalModel.Contracts.Operations
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # `BitwiseOperation` native circuit

The proof-oriented Clean implementation of the bytewise bitwise gadget. -/

namespace SP1Clean.BitwiseOperation

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let a := input.a
  let b := input.b
  let cols := input.cols
  let opcode := input.opcode
  let is_real := input.is_real
  byteChannel.pullIf is_real (⟨opcode, cols.result[0], a[0], b[0]⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf is_real (⟨opcode, cols.result[1], a[1], b[1]⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf is_real (⟨opcode, cols.result[2], a[2], b[2]⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf is_real (⟨opcode, cols.result[3], a[3], b[3]⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf is_real (⟨opcode, cols.result[4], a[4], b[4]⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf is_real (⟨opcode, cols.result[5], a[5], b[5]⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf is_real (⟨opcode, cols.result[6], a[6], b[6]⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf is_real (⟨opcode, cols.result[7], a[7], b[7]⟩ : ByteRow (Expression (ZMod p)))
  assertZero (is_real * (is_real - 1))

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main := by
  elaborate_circuit_with {
    channelsWithGuarantees := [byteChannel.toRaw]
  }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [byteChannel.toRaw] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

end SP1Clean.BitwiseOperation
