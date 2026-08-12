import SP1Clean.Math.Word
import SP1Clean.Model.Channels
import SP1Clean.Model.ByteTable
import SP1Clean.FormalModel.Contracts.Operations
import SP1Clean.Proofs.Operations.U16MSBOperation.Formal
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # `AddwOperation` native circuit

The proof-oriented Clean implementation, composed with the native MSB gadget. -/

namespace SP1Clean.AddwOperation

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let a := input.a
  let b := input.b
  let cols := input.cols
  let is_real := input.is_real
  let E0 := is_real - 1
  let E1 := is_real * E0
  let E2 := a[0] + b[0]
  let E3 := E2 - cols.value[0]
  let E4 := E3 + 0
  let E5 := E4 * ((65536 : ZMod p)⁻¹)
  let E6 := E5 - 1
  let E7 := E5 * E6
  let E8 := is_real * E7
  let E9 := a[1] + b[1]
  let E10 := E9 - cols.value[1]
  let E11 := E10 + E5
  let E12 := E11 * ((65536 : ZMod p)⁻¹)
  let E13 := E12 - 1
  let E14 := E12 * E13
  let E15 := is_real * E14
  assertion U16MSBOperation.circuit ⟨cols.value[1], { msb := cols.msb.msb }, is_real⟩
  byteChannel.pullIf is_real (⟨6, cols.value[0], Expression.const ((16 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf is_real (⟨6, cols.value[1], Expression.const ((16 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))
  assertZero E1
  E8 === 0
  E15 === 0

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

end SP1Clean.AddwOperation
