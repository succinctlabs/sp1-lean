import SP1Clean.Model.Core.Memory
import SP1Clean.Math.Word

/-! # Initial-memory byte-read contract

A bounded address determines one byte in the supplied sparse memory. Interval endpoints and
comparison columns belong to the circuit implementation, below this input/output contract.
-/

namespace SP1Clean.InitialMemoryLookup

open SP1Clean.Model.Core

variable {p : ℕ} [Fact p.Prime]

/-- The returned byte is exactly the memory value at the bounded address. -/
def Spec (memory : ByteMemory) (limit : ℕ) (address : Word (ZMod p)) (value : ZMod p) : Prop :=
  Word.isU64 address ∧ Word.toNat address < limit ∧
    value = (memory.read (Word.toNat address)).toNat

end SP1Clean.InitialMemoryLookup
