import Mathlib.Data.BitVec

/-! # Sparse byte memory for executable Core inputs and host effects

The finite list is an update history, with the most recent binding first. Missing addresses read
as zero. Addresses are natural numbers so interval checks take place before narrowing to the
architectural address width. The execution profile supplies the address-window and ROM checks;
the memory operations themselves have no silent wraparound.
-/

namespace SP1Clean.Model.Core

/-- Finite byte memory with zero defaults and newest-write precedence. -/
structure ByteMemory where
  entries : List (ℕ × BitVec 8) := []
deriving DecidableEq, Repr, Inhabited

namespace ByteMemory

/-- Read a byte, using zero for addresses absent from the finite image. -/
def read (memory : ByteMemory) (address : ℕ) : BitVec 8 :=
  ((memory.entries.find? (fun entry => entry.1 == address)).map Prod.snd).getD 0

/-- Update one byte. Historical entries do not affect the value at the updated address. -/
def write (memory : ByteMemory) (address : ℕ) (value : BitVec 8) : ByteMemory :=
  ⟨(address, value) :: memory.entries⟩

/-- Read a consecutive byte interval. -/
def readBytes (memory : ByteMemory) (address length : ℕ) : List (BitVec 8) :=
  (List.range length).map (fun offset => memory.read (address + offset))

/-- Write a consecutive byte interval without address truncation. -/
def writeBytes (memory : ByteMemory) (address : ℕ) : List (BitVec 8) → ByteMemory
  | [] => memory
  | byte :: rest => (memory.write address byte).writeBytes (address + 1) rest

@[simp] theorem read_empty (address : ℕ) : (ByteMemory.mk []).read address = 0 := rfl

/-- A listed byte is the read value whenever all bindings at its address agree. This permits
compatible ROM/data overlap without requiring the update history itself to have unique keys. -/
theorem read_eq_of_mem (memory : ByteMemory) (address : ℕ) (value : BitVec 8)
    (present : (address, value) ∈ memory.entries)
    (agrees : ∀ entry ∈ memory.entries, entry.1 = address → entry.2 = value) :
    memory.read address = value := by
  cases found : memory.entries.find? (fun entry => entry.1 == address) with
  | none =>
      have := List.find?_eq_none.mp found (address, value) present
      simp at this
  | some entry =>
      have atAddress : entry.1 = address := by simpa using List.find?_some found
      simp [read, found, agrees entry (List.mem_of_find?_eq_some found) atAddress]

/-- An address absent from the sparse image has the canonical zero value. -/
theorem read_eq_zero_of_absent (memory : ByteMemory) (address : ℕ)
    (absent : ∀ entry ∈ memory.entries, entry.1 ≠ address) : memory.read address = 0 := by
  have found : memory.entries.find? (fun entry => entry.1 == address) = none := by
    apply List.find?_eq_none.mpr
    simpa using absent
  simp [read, found]

@[simp] theorem read_write (memory : ByteMemory) (address query : ℕ) (value : BitVec 8) :
    (memory.write address value).read query =
      if address = query then value else memory.read query := by
  by_cases h : address = query <;> simp [read, write, h]

@[simp] theorem readBytes_length (memory : ByteMemory) (address length : ℕ) :
    (memory.readBytes address length).length = length := by
  simp [readBytes]

/-- Bulk writes preserve every byte outside the written interval. -/
theorem read_writeBytes_of_outside (memory : ByteMemory) (address query : ℕ)
    (bytes : List (BitVec 8)) (outside : query < address ∨ address + bytes.length ≤ query) :
    (memory.writeBytes address bytes).read query = memory.read query := by
  induction bytes generalizing memory address with
  | nil => rfl
  | cons byte rest ih =>
      rw [writeBytes, ih]
      · rw [read_write, if_neg (by simp only [List.length_cons] at outside; omega)]
      · simp only [List.length_cons] at outside
        omega

/-- Bulk writes realize the supplied bytes exactly, including writes over older bindings. -/
theorem read_writeBytes_inside (memory : ByteMemory) (address : ℕ)
    (bytes : List (BitVec 8)) (offset : ℕ) (bound : offset < bytes.length) :
    (memory.writeBytes address bytes).read (address + offset) = bytes[offset] := by
  induction bytes generalizing memory address offset with
  | nil => simp at bound
  | cons byte rest ih =>
      cases offset with
      | zero =>
          simp only [writeBytes, Nat.add_zero, List.getElem_cons_zero]
          rw [read_writeBytes_of_outside _ _ _ _ (Or.inl (by omega)), read_write, if_pos rfl]
      | succ offset =>
          simp only [writeBytes, List.getElem_cons_succ]
          rw [show address + (offset + 1) = address + 1 + offset by omega]
          exact ih _ _ _ (by simpa using bound)

/-- Reading back a written interval returns the original byte sequence. -/
theorem readBytes_writeBytes (memory : ByteMemory) (address : ℕ) (bytes : List (BitVec 8)) :
    (memory.writeBytes address bytes).readBytes address bytes.length = bytes := by
  apply List.ext_getElem
  · simp
  · intro index leftBound rightBound
    simpa [readBytes] using read_writeBytes_inside memory address bytes index rightBound

/-- A write interval is disjoint from the designated read-only bytes. -/
def Avoids (readOnly : ℕ → Bool) (address length : ℕ) : Prop :=
  ∀ offset < length, readOnly (address + offset) = false

/-- Byte-precise write exclusion implies preservation of every read-only byte. -/
theorem read_writeBytes_of_readOnly (memory : ByteMemory) (readOnly : ℕ → Bool)
    (address : ℕ) (bytes : List (BitVec 8)) (allowed : Avoids readOnly address bytes.length)
    (query : ℕ) (isReadOnly : readOnly query = true) :
    (memory.writeBytes address bytes).read query = memory.read query := by
  apply read_writeBytes_of_outside
  by_contra h
  have index : query - address < bytes.length := by omega
  have excluded := allowed (query - address) index
  rw [show address + (query - address) = query by omega, isReadOnly] at excluded
  contradiction

end ByteMemory

end SP1Clean.Model.Core
