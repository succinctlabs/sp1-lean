import SP1Clean.Model.Core.HintQueueRecords
import SP1Clean.Model.Core.HintQueueWords

/-! # Authenticating immutable hint words from finite source bytes

A word record identifies a node and a word position with canonical 48-bit keys. Its value is
the complete little-endian word, including required zero padding, and an authenticated final-word
marker. A bounded final word recovers the true node length without a caller-supplied length bound.
The source lookup is computed
from source hints and permits no witness-selected content. Positions beyond the key range are
omitted, never wrapped; completeness states the needed position bound explicitly.
-/

namespace SP1Clean.Model.Core.HintQueue

open SP1Clean.Soundness.Target

structure WordRecord (F : Type) where
  pointer : fields 3 F
  index : fields 3 F
  value : Word F
  isLast : F
deriving ProvableStruct, DecidableEq
provable_struct_eval_lemmas WordRecord

variable {p : ℕ} [Fact p.Prime]

def WordRecord.Valid (record : WordRecord (ZMod p)) : Prop :=
  Address.Bounded record.pointer ∧ 0 < Address.toNat record.pointer ∧
    Address.Bounded record.index ∧ Word.isU64 record.value ∧ (record.isLast = 0 ∨ record.isLast = 1)

def WordRecord.Binds (store : Store) (record : WordRecord (ZMod p)) : Prop :=
  ∃ node, node? store (Address.toNat record.pointer) = some node ∧
    Address.toNat record.index < wordCount node.bytes ∧
    Word.toBitVec64 record.value = wordValue node.bytes (Address.toNat record.index) ∧
    record.isLast = if Address.toNat record.index + 1 = wordCount node.bytes then 1 else 0

def WordRecord.encode (pointer : ℕ) (bytes : Bytes) (index : ℕ) : WordRecord (ZMod p) :=
  ⟨Address.ofNat pointer, Address.ofNat index, bitVecToWord (wordValue bytes index),
    if index + 1 = wordCount bytes then 1 else 0⟩

variable [Fact (2 ^ 17 < p)]

theorem WordRecord.encode_valid (pointer : ℕ) (bytes : Bytes) (index : ℕ)
    (positive : 0 < pointer) (bound : pointer < 2 ^ 48) :
    (encode (p := p) pointer bytes index).Valid := by
  refine ⟨Address.bounded_ofNat _, ?_, Address.bounded_ofNat _, isU64_bitVecToWord _, ?_⟩
  · simpa only [encode, Address.toNat_ofNat _ bound] using positive
  · simp only [encode]
    split_ifs <;> simp

theorem WordRecord.encode_binds {store : Store} {pointer : ℕ} {node : Node}
    (read : node? store pointer = some node) (bound : pointer < 2 ^ 48)
    (index : ℕ) (position : index < wordCount node.bytes) (fits : index < 2 ^ 48) :
    (encode (p := p) pointer node.bytes index).Binds store := by
  refine ⟨node, ?_, ?_, ?_, ?_⟩
  · simpa only [encode, Address.toNat_ofNat _ bound] using read
  · simpa only [encode, Address.toNat_ofNat _ fits] using position
  · simp only [encode, Address.toNat_ofNat _ fits, toBitVec64_bitVecToWord]
  · simp only [encode, Address.toNat_ofNat _ fits]

omit [Fact (2 ^ 17 < p)] in
/-- Word authentication survives every later immutable allocation, including after pops. -/
theorem WordRecord.Binds.extend {old new : Store} {record : WordRecord (ZMod p)}
    (extension : Extends old new) (binding : record.Binds old) : record.Binds new := by
  obtain ⟨node, read, position, value, last⟩ := binding
  exact ⟨node, extension _ _ read, position, value, last⟩

omit [Fact (2 ^ 17 < p)] in
/-- A persistent word belongs to the current store once its node is within the current frontier. -/
theorem WordRecord.Binds.restrict {old new : Store} {record : WordRecord (ZMod p)}
    (binding : record.Binds new) (extension : Extends old new)
    (bound : Address.toNat record.pointer ≤ old.size) : record.Binds old := by
  obtain ⟨node, read, position, value, last⟩ := binding
  exact ⟨node, extension.read_of_bound read bound, position, value, last⟩

omit [Fact (2 ^ 17 < p)] in
/-- The complete word value is fixed by its node and position, not by metadata length alone. -/
theorem WordRecord.Binds.value {store : Store} {record : WordRecord (ZMod p)}
    (binding : record.Binds store) {node : Node}
    (read : node? store (Address.toNat record.pointer) = some node) :
    Address.toNat record.index < wordCount node.bytes ∧
      Word.toBitVec64 record.value = wordValue node.bytes (Address.toNat record.index) := by
  obtain ⟨actual, found, position, value, _⟩ := binding
  have same : actual = node := Option.some.inj (found.symm.trans read)
  cases same
  exact ⟨position, value⟩

omit [Fact (2 ^ 17 < p)] in
/-- The marker identifies the actual final padding word, rather than an arbitrary requested prefix. -/
theorem WordRecord.Binds.isLast_iff {store : Store} {record : WordRecord (ZMod p)}
    (binding : record.Binds store) {node : Node}
    (read : node? store (Address.toNat record.pointer) = some node) :
    record.isLast = 1 ↔ Address.toNat record.index + 1 = wordCount node.bytes := by
  obtain ⟨actual, found, _, _, last⟩ := binding
  have same : actual = node := Option.some.inj (found.symm.trans read)
  cases same
  rw [last]
  by_cases ended : Address.toNat record.index + 1 = wordCount node.bytes <;> simp [ended]

omit [Fact (2 ^ 17 < p)] in
/-- An authenticated final word has a bounded true length, even when source hints are unrestricted. -/
theorem WordRecord.Binds.length_bound_of_last {store : Store} {record : WordRecord (ZMod p)}
    (binding : record.Binds store) (valid : record.Valid) {node : Node}
    (read : node? store (Address.toNat record.pointer) = some node) (last : record.isLast = 1) :
    node.bytes.length < 2 ^ 51 := by
  have ended := (binding.isLast_iff read).mp last
  have bound := Address.toNat_lt valid.2.2.1
  simp only [wordCount] at ended
  omega

omit [Fact (2 ^ 17 < p)] in
/-- Authenticated words give the exact RAM values after the semantic padded write. -/
theorem WordRecord.Binds.write_value {store : Store} {record : WordRecord (ZMod p)}
    (binding : record.Binds store) {node : Node}
    (read : node? store (Address.toNat record.pointer) = some node)
    (memory : ByteMemory) (address : ℕ) :
    (memory.writeBytes address (hintWriteBytes node.bytes)).readWord
      (address + Address.toNat record.index * 8) = Word.toBitVec64 record.value := by
  obtain ⟨position, value⟩ := binding.value read
  rw [readWord_writeHint memory address node.bytes position]
  exact value.symm

omit [Fact (2 ^ 17 < p)] in
/-- A length word determines the natural length only when the actual hint fits in 64 bits. -/
theorem NodeRecord.Binds.length_eq {store : Store} {record : NodeRecord (ZMod p)}
    (binding : record.Binds store) (valid : record.Valid) {node : Node}
    (read : node? store (Address.toNat record.pointer) = some node)
    (bound : node.bytes.length < 2 ^ 64) : Word.toNat record.length = node.bytes.length := by
  obtain ⟨actual, found, _, length⟩ := binding
  have same : actual = node := Option.some.inj (found.symm.trans read)
  cases same
  have natural := congrArg BitVec.toNat length
  simpa only [Word.toBitVec64_toNat valid.2.2.2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] using natural

omit [Fact (2 ^ 17 < p)] in
/-- Final-word authentication discharges the natural-length premise of the metadata bridge. -/
theorem NodeRecord.Binds.length_eq_of_last {store : Store} {record : NodeRecord (ZMod p)}
    (binding : record.Binds store) (valid : record.Valid) (word : WordRecord (ZMod p))
    (wordBinding : word.Binds store) (wordValid : word.Valid) (same : word.pointer = record.pointer)
    (last : word.isLast = 1) {node : Node}
    (read : node? store (Address.toNat record.pointer) = some node) :
    Word.toNat record.length = node.bytes.length := by
  have atWord : node? store (Address.toNat word.pointer) = some node := by rwa [same]
  apply binding.length_eq valid read
  have bound := wordBinding.length_bound_of_last wordValid atWord last
  omega

omit [Fact (2 ^ 17 < p)] in
/-- Complete word coverage and the separately authenticated length recover every hint byte. -/
theorem bytes_eq_of_word_records {store : Store} {pointer : ℕ} {node : Node}
    (read : node? store pointer = some node) (claimed : Bytes)
    (length : claimed.length = node.bytes.length)
    (words : ∀ index < wordCount claimed, ∃ record : WordRecord (ZMod p),
      record.Binds store ∧ Address.toNat record.pointer = pointer ∧
        Address.toNat record.index = index ∧ Word.toBitVec64 record.value = wordValue claimed index) :
    claimed = node.bytes := by
  apply bytes_eq_of_words length
  intro index bound
  obtain ⟨record, binding, pointerEq, indexEq, value⟩ := words index bound
  have atNode : node? store (Address.toNat record.pointer) = some node := by rwa [pointerEq]
  have actual := (binding.value atNode).2
  rw [indexEq, value] at actual
  exact actual

/-- Per-node generation retains only positions with exact field encodings. -/
def nodeWordRows (pointer : ℕ) (bytes : Bytes) : List (WordRecord (ZMod p)) :=
  List.ofFn fun index : Fin (min (wordCount bytes) (2 ^ 48)) =>
    WordRecord.encode pointer bytes index.val

omit [Fact (2 ^ 17 < p)] in
theorem nodeWordRows_length (pointer : ℕ) (bytes : Bytes) :
    (nodeWordRows (p := p) pointer bytes).length = min (wordCount bytes) (2 ^ 48) := by
  simp [nodeWordRows]

theorem nodeWordRows_binds {store : Store} {pointer : ℕ} {node : Node}
    (read : node? store pointer = some node) (bound : pointer < 2 ^ 48) :
    ∀ record ∈ nodeWordRows (p := p) pointer node.bytes, record.Binds store := by
  intro record member
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
  exact WordRecord.encode_binds read bound _ (lt_of_lt_of_le index.isLt (Nat.min_le_left _ _))
    (lt_of_lt_of_le index.isLt (Nat.min_le_right _ _))

omit [Fact (2 ^ 17 < p)] in
theorem nodeWordRows_complete (pointer : ℕ) (bytes : Bytes) (index : ℕ)
    (position : index < wordCount bytes) (bound : index < 2 ^ 48) :
    WordRecord.encode (p := p) pointer bytes index ∈ nodeWordRows pointer bytes :=
  List.mem_ofFn.mpr ⟨⟨index, lt_min position bound⟩, rfl⟩

def sourceWordRows (hints : List Bytes) : List (WordRecord (ZMod p)) :=
  if hints.length < 2 ^ 48 then
    (List.ofFn fun index : Fin (ofList hints).1.size =>
      nodeWordRows (index.val + 1) (ofList hints).1[index.val].bytes).flatten
  else []

@[irreducible] def sourceWordTable (hints : List Bytes) : StaticTable (ZMod p) WordRecord :=
  StaticTable.ofRows "sp1.native.hint_source_words" (sourceWordRows hints)

omit [Fact (2 ^ 17 < p)] in
theorem sourceWordTable_spec (hints : List Bytes) (record : WordRecord (ZMod p)) :
    (sourceWordTable hints).Spec record ↔ hints.length < 2 ^ 48 ∧
      ∃ node : Fin (ofList hints).1.size,
        ∃ index : Fin (min (wordCount (ofList hints).1[node.val].bytes) (2 ^ 48)),
          WordRecord.encode (node.val + 1) (ofList hints).1[node.val].bytes index.val = record := by
  simp [sourceWordTable, StaticTable.ofRows, sourceWordRows, nodeWordRows]

/-- Raw source membership authenticates the actual source word and all local bounds. -/
theorem sourceWordTable_sound (hints : List Bytes) (record : WordRecord (ZMod p))
    (member : (sourceWordTable hints).Spec record) : record.Valid ∧ record.Binds (ofList hints).1 := by
  obtain ⟨fits, node, index, rfl⟩ := (sourceWordTable_spec hints record).mp member
  have read : node? (ofList hints).1 (node.val + 1) = some (ofList hints).1[node.val] :=
    Array.getElem?_eq_getElem node.isLt
  have bound : node.val + 1 < 2 ^ 48 := by
    have := node.isLt
    have := ofList_size hints
    omega
  exact ⟨WordRecord.encode_valid _ _ _ (by omega) bound,
    WordRecord.encode_binds read bound _ (lt_of_lt_of_le index.isLt (Nat.min_le_left _ _))
      (lt_of_lt_of_le index.isLt (Nat.min_le_right _ _))⟩

omit [Fact (2 ^ 17 < p)] in
/-- Every bounded source word, including its final padding word, has a canonical lookup row. -/
theorem sourceWordTable_complete (hints : List Bytes) (fits : hints.length < 2 ^ 48)
    (node : Fin (ofList hints).1.size) (index : ℕ)
    (position : index < wordCount (ofList hints).1[node.val].bytes) (bound : index < 2 ^ 48) :
    (sourceWordTable (p := p) hints).Spec
      (WordRecord.encode (node.val + 1) (ofList hints).1[node.val].bytes index) :=
  (sourceWordTable_spec hints _).mpr ⟨fits, node, ⟨index, lt_min position bound⟩, rfl⟩

end SP1Clean.Model.Core.HintQueue
