import SP1Clean.Model.Core.HostExecutionLaws
import SP1Clean.Model.Core.MemorySpan
import SP1Clean.Math.ByteWord

/-! # Host byte reads from defined word observations

An observation gives all eight bytes of a word at an explicit natural address. It cannot be
satisfied by an absent optional read. Buffer consumers use this interface after Memory grounding
has authenticated their cells, without depending on the Sail memory implementation.
-/

namespace SP1Clean.Model.Core.HostReadContext

def ObservesWord (context : HostReadContext) (address : ℕ) (word : BitVec 64) : Prop :=
  ∀ index : Fin 8,
    context.byte (address + index.val) = some (word.extractLsb' (8 * index.val) 8)

/-- Decoding a defined word gives the exact eight bytes returned by the host read interface. -/
theorem readBytes_of_word (context : HostReadContext) (address : ℕ)
    (bytes : Vector (BitVec 8) 8) (observed : context.ObservesWord address (Word.bytesValue bytes)) :
    context.readBytes? address 8 = some bytes.toList := by
  rw [readBytes?_eq_some_iff]
  refine ⟨by simp, ?_⟩
  intro index bound
  have small : index < 8 := by simpa using bound
  have read := observed ⟨index, small⟩
  rw [Word.bytesValue_extract bytes ⟨index, small⟩] at read
  simpa only [Vector.getElem_toList, Fin.getElem_fin] using read

/-- A requested slice of an aligned word map; no byte outside the slice is returned. -/
def slice (words : ℕ → BitVec 64) (address length : ℕ) : Bytes :=
  (List.range length).map fun index =>
    (words ((address + index) / 8)).extractLsb' (8 * ((address + index) % 8)) 8

/-- Defined observations of the minimal cell cover authenticate an arbitrary byte slice. -/
theorem readBytes_of_cells (context : HostReadContext) (words : ℕ → BitVec 64)
    (address length : ℕ)
    (observed : ∀ cell ∈ (MemorySpan.mk address length).cells,
      context.ObservesWord (cell * 8) (words cell)) :
    context.readBytes? address length = some (slice words address length) := by
  rw [readBytes?_eq_some_iff]
  refine ⟨by simp [slice], ?_⟩
  intro index bound
  have small : index < length := by simpa [slice] using bound
  have member := (MemorySpan.mk address length).byte_cell_mem index small
  have read := observed _ member ⟨(address + index) % 8, Nat.mod_lt _ (by decide)⟩
  have position : (address + index) / 8 * 8 + (address + index) % 8 = address + index := by omega
  simpa only [slice, List.getElem_map, List.getElem_range, position] using read

/-- Guest-window bounds plus cell observations give the host interpreter's complete read. -/
theorem readGuest_of_cells (context : HostReadContext) (policy : HostMemoryPolicy)
    (words : ℕ → BitVec 64) (address length : ℕ)
    (lower : policy.lower ≤ address) (upper : address + length ≤ policy.upper)
    (observed : ∀ cell ∈ (MemorySpan.mk address length).cells,
      context.ObservesWord (cell * 8) (words cell)) :
    context.readGuest? policy address length = some (slice words address length) := by
  rw [readGuest?, if_pos (show policy.lower ≤ address ∧ address + length ≤ policy.upper from
    ⟨lower, upper⟩)]
  exact readBytes_of_cells context words address length observed

end SP1Clean.Model.Core.HostReadContext
