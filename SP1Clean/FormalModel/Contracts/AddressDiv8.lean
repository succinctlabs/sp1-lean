import SP1Clean.Math.Address
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Division into eight-byte words inside the native address domain

The semantic output is the quotient, remainder, and rounded-down byte length. Canonical input
and output bounds are conclusions of the circuit, so consumers can use ordinary natural-number
division without field aliases. The three partial quotients are computed constructor columns.
-/

namespace SP1Clean.AddressDiv8

structure Inputs (F : Type) where
  value : Word F
  quotients : fields 3 F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

structure Output (F : Type) where
  quotient : fields 3 F
  remainder : F
  rounded : Word F
deriving ProvableStruct
provable_struct_eval_lemmas Output

def Spec {p : ℕ} [Fact p.Prime] (input : Inputs (ZMod p)) (output : Output (ZMod p)) : Prop :=
  Word.isU64 input.value ∧ Word.toNat input.value < 2 ^ 48 ∧
    Address.Bounded output.quotient ∧ Address.toNat output.quotient = Word.toNat input.value / 8 ∧
    output.remainder.val = Word.toNat input.value % 8 ∧ Word.isU64 output.rounded ∧
    Word.toNat output.rounded = Word.toNat input.value / 8 * 8

end SP1Clean.AddressDiv8
