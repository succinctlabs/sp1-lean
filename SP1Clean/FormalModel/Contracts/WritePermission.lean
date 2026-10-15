import SP1Clean.Model.Core.WritePermission
import Clean.Circuit.Channel

/-! # Byte-level write permission contract

The provider contract is a local property of the program's fixed ROM, independent of execution
or memory values. The channel is structural: global balance must match each active write's byte
requests with fixed-table providers. Instruction rows need no local permission premise.
-/

namespace SP1Clean.WritePermissionProvider

open SP1Clean.Model.Core

structure Inputs (F : Type) where
  address : fields 3 F
  interval : WritePermissionInterval F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

variable {p : ℕ}

def Permitted (image : ProgramImage) (address : fields 3 (ZMod p)) : Prop :=
  Address.Bounded address ∧ Address.toNat address < 2 ^ 48 ∧
    image.readOnly (Address.toNat address) = false

def Spec (image : ProgramImage) (input : Inputs (ZMod p)) : Prop :=
  Permitted image input.address

def channel : Channel (ZMod p) (fields 3) where
  name := "SP1WritePermission"
  Guarantees _ _ := True

end SP1Clean.WritePermissionProvider
