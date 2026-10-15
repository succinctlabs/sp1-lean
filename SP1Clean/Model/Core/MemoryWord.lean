import SP1Clean.Math.ByteWord
import SP1Clean.Model.Core.SailMemory
import SP1Clean.Model.Semantics.MicroTime

/-! # Sparse byte memory at the memory bus's word granularity

`readWord` is executable on sparse memory. Its value is exactly the existing Sail-side
`ramWord64?` interpretation whenever all eight bytes lie in the realized address window.
-/

namespace SP1Clean.Model.Core.ByteMemory

open SP1Clean.Soundness.Target

/-- The eight bytes starting at a natural address, with the sparse memory's zero defaults. -/
def wordBytes (memory : ByteMemory) (address : ℕ) : Vector (BitVec 8) 8 :=
  Vector.ofFn fun index => memory.read (address + index.val)

/-- The memory bus's little-endian 64-bit value, computed from sparse storage. -/
def readWord (memory : ByteMemory) (address : ℕ) : BitVec 64 :=
  Word.bytesValue (memory.wordBytes address)

/-- Each byte of a sparse word is the corresponding memory read. -/
theorem readWord_byte (memory : ByteMemory) (address : ℕ) (index : Fin 8) :
    (memory.readWord address).extractLsb' (8 * index.val) 8 = memory.read (address + index.val) := by
  simp only [readWord, Word.bytesValue_extract, wordBytes, Fin.getElem_fin, Vector.getElem_ofFn]

/-- Byte-wise memory agreement suffices for whole-word agreement with Sail. -/
theorem ramWord64?_of_bytes (memory : ByteMemory) (state : SailState) (address : BitVec 64)
    (bytes : ∀ index : Fin 8,
      state.mem.get? (address.toNat + index.val) = some (memory.read (address.toNat + index.val))) :
    Semantics.ramWord64? state address = some (memory.readWord address.toNat) := by
  have byte (index : ℕ) (bound : index < 8) := bytes ⟨index, bound⟩
  dsimp only at byte
  simp only [Semantics.ramWord64?, readWord, wordBytes, Word.bytesValue, Vector.getElem_ofFn,
    show state.mem.get? address.toNat = some (memory.read address.toNat) from by simpa using byte 0 (by decide),
    byte 1 (by decide), byte 2 (by decide), byte 3 (by decide), byte 4 (by decide),
    byte 5 (by decide), byte 6 (by decide), byte 7 (by decide), Nat.add_zero]
  rfl

end SP1Clean.Model.Core.ByteMemory
