import SP1Clean.Math.Address
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Inclusive order of bounded 48-bit addresses

Both addresses use three 16-bit limbs. Their range facts are explicit local assumptions, supplied
by a fixed interval lookup or a range-check circuit. The comparison itself has no channel inputs.
-/

namespace SP1Clean.AddressOrder

structure Inputs (F : Type) where
  lower : fields 3 F
  upper : fields 3 F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

variable {p : ℕ}

abbrev value (address : fields 3 (ZMod p)) : ℕ := Address.toNat address

abbrev Bounded (address : fields 3 (ZMod p)) : Prop := Address.Bounded address

def Assumptions (input : Inputs (ZMod p)) : Prop := Bounded input.lower ∧ Bounded input.upper

def Spec (input : Inputs (ZMod p)) : Prop := value input.lower ≤ value input.upper

end SP1Clean.AddressOrder
