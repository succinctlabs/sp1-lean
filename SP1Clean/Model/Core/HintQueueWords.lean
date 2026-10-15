import SP1Clean.Model.Core.HintQueue
import SP1Clean.Model.Core.MemoryWord

/-! # Complete immutable hint contents at RAM-word granularity

Each node has exactly the words HINT_READ writes, including its mandatory final padding word.
The complete length and these words determine every byte, without a content hash. The word
positions are local to the immutable node and remain meaningful after any queue update.
-/

namespace SP1Clean.Model.Core.HintQueue

/-- Even an empty or word-aligned hint has a final padding word. -/
def wordCount (bytes : Bytes) : ℕ := bytes.length / 8 + 1

def wordBytes (bytes : Bytes) (index : ℕ) : Vector (BitVec 8) 8 :=
  Vector.ofFn fun slot => bytes[index * 8 + slot.val]?.getD 0

def wordValue (bytes : Bytes) (index : ℕ) : BitVec 64 := Word.bytesValue (wordBytes bytes index)

/-- The complete aligned word inventory of the semantic padded write, in address order. -/
def wordWrites (address : ℕ) (bytes : Bytes) : List (ℕ × BitVec 64) :=
  (List.range (wordCount bytes)).map fun index => (address + index * 8, wordValue bytes index)

theorem wordWrites_length (address : ℕ) (bytes : Bytes) :
    (wordWrites address bytes).length = wordCount bytes := by simp [wordWrites]

/-- Each destination cell occurs exactly once, regardless of repeated or zero word contents. -/
theorem wordWrites_addresses_nodup (address : ℕ) (bytes : Bytes) :
    ((wordWrites address bytes).map Prod.fst).Nodup := by
  simp only [wordWrites, List.map_map, Function.comp_def]
  apply List.Nodup.map _ List.nodup_range
  intro left right equal
  dsimp only at equal
  omega

theorem wordCount_pos (bytes : Bytes) : 0 < wordCount bytes := by
  unfold wordCount
  omega

theorem wordCount_length (bytes : Bytes) : (hintWriteBytes bytes).length = 8 * wordCount bytes :=
  hintWriteBytes_length bytes

/-- Permissions for every byte of every word cover the entire padded host request. -/
theorem permits_of_word_bytes (policy : HostMemoryPolicy) (address : ℕ) (bytes : Bytes)
    (permissions : ∀ index < wordCount bytes, ∀ slot : Fin 8,
      policy.permits (address + index * 8 + slot.val) 1 = true) :
    policy.permits address (hintWriteBytes bytes).length = true := by
  have first := (policy.permits_iff _ _).mp (permissions 0 (wordCount_pos bytes) 0)
  have last := (policy.permits_iff _ _).mp
    (permissions (wordCount bytes - 1) (by have := wordCount_pos bytes; omega) 7)
  apply (policy.permits_iff _ _).mpr
  rw [wordCount_length]
  refine ⟨by simpa using first.1, by have := wordCount_pos bytes; omega, ?_⟩
  intro offset bound
  have slot : offset % 8 < 8 := Nat.mod_lt _ (by decide)
  have permitted := (policy.permits_iff _ _).mp
    (permissions (offset / 8) (by omega) ⟨offset % 8, slot⟩)
  have excluded := permitted.2.2 0 (by decide)
  simpa only [Nat.add_zero, show address + offset / 8 * 8 + offset % 8 = address + offset by omega]
    using excluded

/-- A permitted write in the native address window supplies the complete word-position bound. -/
theorem wordCount_bound_of_permitted (bytes : Bytes) (policy : HostMemoryPolicy) (address : ℕ)
    (window : policy.upper ≤ 2 ^ 48)
    (permitted : policy.permits address (hintWriteBytes bytes).length = true) :
    wordCount bytes ≤ 2 ^ 45 := by
  have bound := ((policy.permits_iff _ _).mp permitted).2.1
  rw [wordCount_length] at bound
  omega

/-- There is neither an omitted partial word nor an extra word beyond the required padding. -/
theorem word_position_bound (bytes : Bytes) {index : ℕ} (bound : index < wordCount bytes)
    (slot : Fin 8) : index * 8 + slot.val < (hintWriteBytes bytes).length := by
  rw [wordCount_length]
  have := slot.isLt
  omega

/-- Each authenticated word includes the exact zero padding of the executable host semantics. -/
theorem wordValue_byte (bytes : Bytes) {index : ℕ} (bound : index < wordCount bytes) (slot : Fin 8) :
    (wordValue bytes index).extractLsb' (8 * slot.val) 8 =
      (hintWriteBytes bytes)[index * 8 + slot.val]'(word_position_bound bytes bound slot) := by
  rw [wordValue, Word.bytesValue_extract]
  simp only [wordBytes, Fin.getElem_fin, Vector.getElem_ofFn]
  by_cases inside : index * 8 + slot.val < bytes.length
  · simp [hintWriteBytes, inside]
  · rw [List.getElem?_eq_none (by omega), Option.getD_none]
    simp [hintWriteBytes, List.getElem_append, inside]

/-- Equal-length byte strings are equal exactly when all their padded word values agree. -/
theorem bytes_eq_of_words {left right : Bytes} (length : left.length = right.length)
    (words : ∀ index < wordCount left, wordValue left index = wordValue right index) : left = right := by
  apply List.ext_getElem length
  intro index leftBound rightBound
  have bound : index / 8 < wordCount left := by unfold wordCount; omega
  have value := congrArg (fun word : BitVec 64 => word.extractLsb' (8 * (index % 8)) 8) (words _ bound)
  have slot : index % 8 < 8 := Nat.mod_lt _ (by decide)
  have position : index / 8 * 8 + index % 8 = index := by omega
  simpa only [wordValue, Word.bytesValue_extract _ ⟨index % 8, slot⟩,
    wordBytes, Fin.getElem_fin, Vector.getElem_ofFn, position, List.getElem?_eq_getElem leftBound,
    List.getElem?_eq_getElem rightBound, Option.getD_some] using value

/-- Padded host writes realize exactly these node words in the destination RAM cells. -/
theorem readWord_writeHint (memory : ByteMemory) (address : ℕ) (bytes : Bytes)
    {index : ℕ} (bound : index < wordCount bytes) :
    (memory.writeBytes address (hintWriteBytes bytes)).readWord (address + index * 8) =
      wordValue bytes index := by
  apply congrArg Word.bytesValue
  apply Vector.ext
  intro slot small
  simp only [ByteMemory.wordBytes, wordBytes, Vector.getElem_ofFn]
  rw [Nat.add_assoc, ByteMemory.read_writeBytes_inside _ _ _ _
    (word_position_bound bytes bound ⟨slot, small⟩)]
  exact (wordValue_byte bytes bound ⟨slot, small⟩).symm.trans (by
    rw [wordValue, Word.bytesValue_extract]
    simp only [wordBytes, Fin.getElem_fin, Vector.getElem_ofFn])

/-- Every entry in the complete inventory agrees with the actual byte-memory update. -/
theorem wordWrites_readback (memory : ByteMemory) (address : ℕ) (bytes : Bytes)
    (entry : ℕ × BitVec 64) (member : entry ∈ wordWrites address bytes) :
    (memory.writeBytes address (hintWriteBytes bytes)).readWord entry.1 = entry.2 := by
  obtain ⟨index, bound, rfl⟩ := List.mem_map.mp member
  exact readWord_writeHint memory address bytes (List.mem_range.mp bound)

end SP1Clean.Model.Core.HintQueue
