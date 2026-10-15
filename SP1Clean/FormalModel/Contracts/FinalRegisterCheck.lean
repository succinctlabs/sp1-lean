import SP1Clean.FormalModel.Contracts.FinalMemoryChange
import SP1Clean.FormalModel.Contracts.FinalRegisterValue

/-! # A validated final register and its optional change contribution -/

namespace SP1Clean.FinalRegisterCheck

open Model.Core Channels

/-- Register checks need only the full record and its Boolean coverage selector. -/
abbrev Inputs := FinalMemoryChange.Inputs

/-- The complete target register value agrees, with a Boolean coverage contribution. -/
def Spec {p : ℕ} [Fact p.Prime] (target : MemorySnapshot) (input : Inputs (ZMod p)) : Prop :=
  FinalRegisterValue.Spec target input.record ∧ FinalMemoryChange.Spec input

end SP1Clean.FinalRegisterCheck
