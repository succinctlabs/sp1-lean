import SP1Clean.Model.Semantics.MicroTime
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Strict order between two native event clocks

Both clocks use bounded 24-bit high and low limbs. This contract states natural time order,
without exposing the equality selector or subtraction used to constrain it.
-/

namespace SP1Clean.ClockOrder

structure Inputs (F : Type) where
  previousHigh : F
  previousLow : F
  currentHigh : F
  currentLow : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

def Spec {p : ℕ} (input : Inputs (ZMod p)) : Prop :=
  input.previousHigh.val < 2 ^ 24 ∧ input.previousLow.val < 2 ^ 24 ∧
    input.currentHigh.val < 2 ^ 24 ∧ input.currentLow.val < 2 ^ 24 ∧
    Semantics.clkNat input.previousHigh input.previousLow <
      Semantics.clkNat input.currentHigh input.currentLow

end SP1Clean.ClockOrder
