import SP1Clean.Math.Word
import SP1Clean.Circuits.Types.LtOperationUnsigned

/-! # A word below a fixed natural bound

The comparison columns are internal completeness data. The semantic boundary is a genuine
64-bit word whose natural value is strictly below the circuit's constant bound.
-/

namespace SP1Clean.BoundedWord

structure Inputs (F : Type) where
  value : Word F
  comparison : Circuits.Types.LtOperationUnsigned F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

def Spec {p : ℕ} [Fact p.Prime] (bound : ℕ) (input : Inputs (ZMod p)) : Prop :=
  Word.isU64 input.value ∧ Word.toNat input.value < bound

end SP1Clean.BoundedWord
