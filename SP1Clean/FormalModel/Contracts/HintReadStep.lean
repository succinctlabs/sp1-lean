import SP1Clean.FormalModel.Contracts.HintWords

/-! # One successive padded hint word

The word index advances by exactly one without wrap. Nonfinal rows advance the address by
eight; the final row retains its last written address so a write may end at `2^48`. Word
authenticity and complete row coverage are derived from the enclosing ledgers.
-/

namespace SP1Clean.HintReadStep

structure Inputs (F : Type) where
  word : Model.Core.HintQueue.WordRecord F
  address : fields 3 F
  nextIndex : fields 3 F
  nextAddress : fields 3 F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

def Spec {p : ℕ} [Fact p.Prime] (last : Bool) (input : Inputs (ZMod p)) : Prop :=
  input.word.Valid ∧ input.word.isLast = (if last then 1 else 0) ∧
    Address.Bounded input.address ∧ Address.Bounded input.nextIndex ∧
    Address.toNat input.nextIndex = Address.toNat input.word.index + 1 ∧
    Address.Bounded input.nextAddress ∧
    Address.toNat input.nextAddress = Address.toNat input.address + (if last then 0 else 8)

end SP1Clean.HintReadStep
