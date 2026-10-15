import SP1Clean.FormalModel.Contracts.FinalMemoryChange
import SP1Clean.FormalModel.Contracts.FinalRamValue

/-! # A validated final RAM value and its optional change contribution -/

namespace SP1Clean.FinalRamCheck

open Circuit Model.Core

/-- The existing complete target read and its coverage selector. -/
structure Inputs (F : Type) where
  /-- Complete final RAM record, including its clock and value. -/
  record : Channels.MemoryMsg F
  /-- Boolean contribution to the complete change inventory. -/
  selected : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- The entire target RAM word agrees, with a Boolean coverage contribution. -/
def Spec {p : ℕ} [Fact p.Prime] (target : MemorySnapshot) (input : Inputs (ZMod p)) : Prop :=
  FinalRamValue.Spec target input.record ∧
    FinalMemoryChange.Spec ⟨input.record, input.selected⟩

end SP1Clean.FinalRamCheck
