import SP1Clean.Math.Word
import SP1Clean.Model.Channels
import SP1Clean.Model.ByteTable
import SP1Clean.FormalModel.Contracts.Operations
import SP1Clean.Proofs.Operations.IsZeroOperation.Formal
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # `IsZeroWordOperation` native circuit

The proof-oriented Clean implementation, composed from the native field-zero gadget. -/

namespace SP1Clean.IsZeroWordOperation

open Circuit
open SP1Clean.Channels (byteChannel)
open SP1Clean.Extracted

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let a := input.a
  let cols := input.cols
  let is_real := input.is_real
  let E0 := is_real - 1
  let E1 := is_real * E0
  let E2 := cols.result - 1
  let E3 := cols.result * E2
  let E4 := cols.is_zero_limb_0.result * cols.is_zero_limb_1.result
  let E5 := cols.is_zero_first_half - E4
  let E6 := cols.is_zero_limb_2.result * cols.is_zero_limb_3.result
  let E7 := cols.is_zero_second_half - E6
  let E8 := cols.is_zero_first_half * cols.is_zero_second_half
  let E9 := cols.result - E8
  let E10 := is_real * E9
  assertion IsZeroOperation.circuit ⟨a[0], { inverse := cols.is_zero_limb_0.inverse, result := cols.is_zero_limb_0.result }, is_real⟩
  assertion IsZeroOperation.circuit ⟨a[1], { inverse := cols.is_zero_limb_1.inverse, result := cols.is_zero_limb_1.result }, is_real⟩
  assertion IsZeroOperation.circuit ⟨a[2], { inverse := cols.is_zero_limb_2.inverse, result := cols.is_zero_limb_2.result }, is_real⟩
  assertion IsZeroOperation.circuit ⟨a[3], { inverse := cols.is_zero_limb_3.inverse, result := cols.is_zero_limb_3.result }, is_real⟩
  E1 === 0
  E3 === 0
  E5 === 0
  E7 === 0
  E10 === 0

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main := by
  elaborate_circuit_with {
    channelsWithGuarantees := []
  }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

end SP1Clean.IsZeroWordOperation
