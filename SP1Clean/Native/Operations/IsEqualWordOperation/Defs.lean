import SP1Clean.Math.Word
import SP1Clean.Model.Channels
import SP1Clean.Model.ByteTable
import SP1Clean.FormalModel.Contracts.Operations
import SP1Clean.Proofs.Operations.IsZeroWordOperation.Formal
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # `IsEqualWordOperation` native circuit

The proof-oriented Clean implementation, composed from the native word-zero gadget. -/

namespace SP1Clean.IsEqualWordOperation

open Circuit
open SP1Clean.Channels (byteChannel)
open SP1Clean.Extracted

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let a := input.a
  let b := input.b
  let cols := input.cols
  let is_real := input.is_real
  let E0 := is_real - 1
  let E1 := is_real * E0
  let E2 := a[0] - b[0]
  let E3 := a[1] - b[1]
  let E4 := a[2] - b[2]
  let E5 := a[3] - b[3]
  assertion IsZeroWordOperation.circuit ⟨#v[E2, E3, E4, E5], { is_zero_limb_0 := { inverse := cols.is_diff_zero.is_zero_limb_0.inverse, result := cols.is_diff_zero.is_zero_limb_0.result }, is_zero_limb_1 := { inverse := cols.is_diff_zero.is_zero_limb_1.inverse, result := cols.is_diff_zero.is_zero_limb_1.result }, is_zero_limb_2 := { inverse := cols.is_diff_zero.is_zero_limb_2.inverse, result := cols.is_diff_zero.is_zero_limb_2.result }, is_zero_limb_3 := { inverse := cols.is_diff_zero.is_zero_limb_3.inverse, result := cols.is_diff_zero.is_zero_limb_3.result }, is_zero_first_half := cols.is_diff_zero.is_zero_first_half, is_zero_second_half := cols.is_diff_zero.is_zero_second_half, result := cols.is_diff_zero.result }, is_real⟩
  E1 === 0

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

end SP1Clean.IsEqualWordOperation
