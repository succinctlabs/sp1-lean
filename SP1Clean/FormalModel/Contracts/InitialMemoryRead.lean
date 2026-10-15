import SP1Clean.Math.Word
import SP1Clean.Model.Core.MemoryWord
import SP1Clean.Model.Core.Boot

/-! # The native initial-memory word-read contract

The contract accepts one address and returns the little-endian memory word at that address.
The complete eight-byte footprint is bounded; byte-row witnesses belong to the circuit.
-/

namespace SP1Clean.InitialMemoryRead

open SP1Clean.Model.Core

variable {p : ℕ} [Fact p.Prime]

/-- A full in-bounds 64-bit read from the canonical initial image. -/
def Spec (memory : ByteMemory) (address : Word (ZMod p)) (output : Word (ZMod p)) : Prop :=
  Word.isU64 address ∧ Word.toNat address + 8 ≤ 2 ^ 48 ∧
    Word.isU64 output ∧
      Word.toBitVec64 output = memory.readWord (Word.toNat address)

/-- The native word-read contract reaches the actual initial Sail memory, without a provider premise. -/
theorem Spec.initialSailState (image : ProgramImage) (address : Word (ZMod p)) (output : Word (ZMod p))
    (spec : Spec image.initialMemory address output) :
    Semantics.ramWord64? image.initialSailState (Word.toBitVec64 address) =
      some (Word.toBitVec64 output) := by
  have footprint : (Word.toBitVec64 address).toNat + 8 ≤ 2 ^ 48 := by
    rw [Word.toBitVec64_toNat spec.1]
    exact spec.2.1
  rw [image.initialSailState_word _ footprint, Word.toBitVec64_toNat spec.1, spec.2.2.2]

end SP1Clean.InitialMemoryRead
