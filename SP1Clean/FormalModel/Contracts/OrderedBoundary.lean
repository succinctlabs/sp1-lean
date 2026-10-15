import SP1Clean.Math.Word
import SP1Clean.Circuits.Types.LtOperationUnsigned

/-! # Strictly ordered boundary keys

Boundary providers use a separate structural channel to connect their keys. The circuit proves
strict integer ordering; balance then forces an exhaustive chain with unique keys. Neither
reachability nor uniqueness is a channel guarantee.
-/

namespace SP1Clean.OrderedBoundary

structure Inputs (F : Type) where
  previous : Word F
  current : Word F
  comparison : Circuits.Types.LtOperationUnsigned F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- A terminal row supplies only the last key and its comparison witness. The final key is
a circuit parameter, never a witness column. -/
structure TerminalInputs (F : Type) where
  previous : Word F
  comparison : Circuits.Types.LtOperationUnsigned F
deriving ProvableStruct
provable_struct_eval_lemmas TerminalInputs

variable {p : ℕ} [Fact p.Prime]

def Spec (input : Inputs (ZMod p)) : Prop :=
  Word.isU64 input.previous ∧ Word.isU64 input.current ∧
    Word.toNat input.previous < Word.toNat input.current

def TerminalSpec (final : Word (ZMod p)) (input : TerminalInputs (ZMod p)) : Prop :=
  Word.isU64 input.previous ∧ Word.toNat input.previous < Word.toNat final

end SP1Clean.OrderedBoundary
