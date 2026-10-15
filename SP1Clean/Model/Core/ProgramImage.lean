import SP1Clean.Model.Machine.Boot
import SP1Clean.Model.Core.Memory
import SP1Clean.Model.Core.NativeLayout

/-! # Checked finite program images

The input format contains bytes and instruction words, with no Lean proof fields. The executable
checker constructs the existing `GuestProgram` and proves its loader-facing well-formedness.
This checks the finite image contract, not instruction support or ELF/digest authentication.
Instruction decoding remains a separate check before an image can instantiate the native ensemble.
-/

namespace SP1Clean.Model.Core

open SP1Clean.Soundness.Target

/-- Proof-free program input. Addresses retain all 64 bits until their bounds are checked. -/
structure ProgramImage where
  rom : List (BitVec 64 × BitVec 32)
  entry : BitVec 64
  image : List (BitVec 64 × BitVec 8)
deriving DecidableEq, Repr

namespace ProgramImage

/-- Finite loader checks, including matching bytes wherever code and data overlap. -/
def Valid (input : ProgramImage) : Prop :=
  (input.rom.map Prod.fst).Nodup ∧
  (∀ row ∈ input.rom, row.1.toNat % 4 = 0 ∧
    NativeLayout.guestMemory.ContainsSpan row.1.toNat 4 ∧
    row.2.extractLsb' 0 2 = 0b11#2) ∧
  (input.rom.any (fun row => row.1 == input.entry) = true) ∧
  (input.image.map Prod.fst).Nodup ∧
  (∀ byte ∈ input.image, NativeLayout.guestMemory.Contains byte.1.toNat) ∧
  (∀ row ∈ input.rom, ∀ byte ∈ input.image, ∀ index : Fin 4,
    byte.1.toNat = row.1.toNat + index → byte.2 = row.2.extractLsb' (8 * index) 8)

/-- Iterate over the supplied finite lists, never the entire bit-vector address space. -/
def checkFields (input : ProgramImage) : Bool :=
  decide (input.rom.map Prod.fst).Nodup &&
  input.rom.all (fun row => decide (row.1.toNat % 4 = 0 ∧
    NativeLayout.guestMemory.ContainsSpan row.1.toNat 4 ∧
    row.2.extractLsb' 0 2 = 0b11#2)) &&
  input.rom.any (fun row => row.1 == input.entry) &&
  decide (input.image.map Prod.fst).Nodup &&
  input.image.all (fun byte => decide (NativeLayout.guestMemory.Contains byte.1.toNat)) &&
  input.rom.all (fun row => input.image.all (fun byte =>
    (List.finRange 4).all (fun index => decide
      (byte.1.toNat = row.1.toNat + index → byte.2 = row.2.extractLsb' (8 * index) 8))))

theorem checkFields_eq_true_iff (input : ProgramImage) : input.checkFields = true ↔ input.Valid := by
  simp only [checkFields, Valid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_finRange, forall_const, and_assoc]

instance (input : ProgramImage) : Decidable input.Valid :=
  decidable_of_iff (input.checkFields = true) input.checkFields_eq_true_iff

/-- Convert checked bytes into the semantic program; no decoding result is invented. -/
def toGuestProgram (input : ProgramImage) (valid : input.Valid) : GuestProgram where
  rom := input.rom
  pc_start := input.entry
  memImage := input.image
  rom_nodup := valid.1
  rom_aligned := by
    intro address member
    obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp member
    exact (valid.2.1 row rowMember).1
  rom_in_window := by
    intro row member
    exact (valid.2.1 row member).2.1
  rom_full_width := by
    intro row member
    exact (valid.2.1 row member).2.2

/-- Every listed ROM entry is the semantic fetch result at its address. Uniqueness comes
from finite-image validation, rather than a separate program-provider premise. -/
theorem fetchWord_of_mem (input : ProgramImage) (valid : input.Valid)
    {entry : BitVec 64 × BitVec 32} (member : entry ∈ input.rom) :
    (input.toGuestProgram valid).fetchWord entry.1 = some entry.2 := by
  cases found : input.rom.find? (fun row => row.1 == entry.1) with
  | none => exact False.elim (List.find?_eq_none.mp found entry member (by simp))
  | some row =>
    have atAddress : row.1 = entry.1 := by simpa using List.find?_some found
    have same := List.inj_on_of_nodup_map valid.1 (List.mem_of_find?_eq_some found) member atAddress
    simp only [GuestProgram.fetchWord, toGuestProgram, found, Option.map_some, same]

/-- The executable finite checks establish the semantic loader contract. -/
theorem toGuestProgram_wellFormed (input : ProgramImage) (valid : input.Valid) :
    (input.toGuestProgram valid).WellFormed where
  entryPointPresent := by
    have present := valid.2.2.1
    simp only [List.any_eq_true] at present
    obtain ⟨row, member, atEntry⟩ := present
    cases found : input.rom.find? (fun row => row.1 == input.entry) with
    | none => exact False.elim (List.find?_eq_none.mp found row member atEntry)
    | some row => exact ⟨row.2, by simp [GuestProgram.fetchWord, toGuestProgram, found]⟩
  imageAddressesUnique := valid.2.2.2.1
  imageCompatibleWithROM := by
    intro address instruction fetched index byte member atAddress
    obtain ⟨row, found, wordEq⟩ := Option.map_eq_some_iff.mp fetched
    have inROM := List.mem_of_find?_eq_some found
    have pcEq := List.find?_some found
    simp only [beq_iff_eq] at pcEq
    have agrees := valid.2.2.2.2.2 row inROM byte member index
    rw [pcEq, wordEq] at agrees
    exact agrees atAddress

/-- Image validation returns its proof, or fails. The caller supplies only finite data. -/
def check (input : ProgramImage) : Option { input : ProgramImage // input.Valid } :=
  if valid : input.Valid then some ⟨input, valid⟩ else none

theorem check_isSome_iff (input : ProgramImage) : input.check.isSome = true ↔ input.Valid := by
  simp [check]

/-- Instruction bytes in address order within each ROM word. Global input order is immaterial
to reads because `Valid` checks unique aligned ROM words. -/
def romBytes (input : ProgramImage) : List (ℕ × BitVec 8) :=
  input.rom.flatMap (fun row =>
    (List.finRange 4).map (fun index => (row.1.toNat + index, row.2.extractLsb' (8 * index) 8)))

/-- Canonical initial contents: the ROM overlay, finite image, and zero everywhere else. -/
def initialMemory (input : ProgramImage) : ByteMemory :=
  ⟨input.romBytes ++ input.image.map (fun byte => (byte.1.toNat, byte.2))⟩

theorem mem_romBytes (input : ProgramImage) (byte : ℕ × BitVec 8) :
    byte ∈ input.romBytes ↔ ∃ row ∈ input.rom, ∃ index : Fin 4,
      (row.1.toNat + index, row.2.extractLsb' (8 * index) 8) = byte := by
  simp [romBytes]

private theorem aligned_bytes_eq (left right : ℕ) (i j : Fin 4)
    (leftAligned : left % 4 = 0) (rightAligned : right % 4 = 0)
    (atAddress : left + i = right + j) : left = right ∧ i = j := by
  have ilt := i.isLt
  have jlt := j.isLt
  have bases : left = right := by omega
  exact ⟨bases, Fin.ext (by omega)⟩

/-- Every ROM byte is realized by the canonical sparse image, even when the supplied data image
also names that address. Alignment and unique ROM addresses prevent conflicting code words. -/
theorem initialMemory_rom (input : ProgramImage) (valid : input.Valid)
    (row : BitVec 64 × BitVec 32) (member : row ∈ input.rom) (index : Fin 4) :
    input.initialMemory.read (row.1.toNat + index) = row.2.extractLsb' (8 * index) 8 := by
  apply ByteMemory.read_eq_of_mem
  · exact List.mem_append_left _ ((mem_romBytes input _).mpr ⟨row, member, index, rfl⟩)
  · intro byte byteMem atAddress
    rcases List.mem_append.mp byteMem with inROM | inImage
    · obtain ⟨other, otherMem, j, rfl⟩ := (mem_romBytes input byte).mp inROM
      obtain ⟨pcEq, indexEq⟩ := aligned_bytes_eq other.1.toNat row.1.toNat j index
        (valid.2.1 other otherMem).1 (valid.2.1 row member).1 atAddress
      have rowEq := List.inj_on_of_nodup_map valid.1 otherMem member (BitVec.eq_of_toNat_eq pcEq)
      rw [rowEq, indexEq]
    · obtain ⟨imageByte, imageMem, rfl⟩ := List.mem_map.mp inImage
      exact valid.2.2.2.2.2 row member imageByte imageMem index atAddress

/-- Every supplied data byte survives the ROM overlay: the input checker requires exact
agreement at overlaps, rather than silently replacing inconsistent data. -/
theorem initialMemory_image (input : ProgramImage) (valid : input.Valid)
    (byte : BitVec 64 × BitVec 8) (member : byte ∈ input.image) :
    input.initialMemory.read byte.1.toNat = byte.2 := by
  apply ByteMemory.read_eq_of_mem
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨byte, member, rfl⟩)
  · intro other otherMem atAddress
    rcases List.mem_append.mp otherMem with inROM | inImage
    · obtain ⟨row, rowMem, index, rfl⟩ := (mem_romBytes input other).mp inROM
      exact (valid.2.2.2.2.2 row rowMem byte member index atAddress.symm).symm
    · obtain ⟨imageByte, imageMem, rfl⟩ := List.mem_map.mp inImage
      have byteEq := List.inj_on_of_nodup_map valid.2.2.2.1 imageMem member
        (BitVec.eq_of_toNat_eq atAddress)
      exact congrArg Prod.snd byteEq

/-- The remaining addresses have zero initial content; no separate memory-provider truth
premise chooses their values. -/
theorem initialMemory_zero (input : ProgramImage) (address : ℕ)
    (outsideROM : ∀ row ∈ input.rom, ∀ index : Fin 4, row.1.toNat + index ≠ address)
    (outsideImage : ∀ byte ∈ input.image, byte.1.toNat ≠ address) :
    input.initialMemory.read address = 0 := by
  apply ByteMemory.read_eq_zero_of_absent
  intro byte member
  rcases List.mem_append.mp member with inROM | inImage
  · obtain ⟨row, rowMem, index, rfl⟩ := (mem_romBytes input byte).mp inROM
    exact outsideROM row rowMem index
  · obtain ⟨imageByte, imageMem, rfl⟩ := List.mem_map.mp inImage
    exact outsideImage imageByte imageMem

/-- Byte-level ROM protection shared by ordinary stores and host writes. -/
def readOnly (input : ProgramImage) (address : ℕ) : Bool :=
  input.rom.any (fun row => decide (row.1.toNat ≤ address ∧ address < row.1.toNat + 4))

theorem readOnly_iff (input : ProgramImage) (address : ℕ) :
    input.readOnly address = true ↔
      ∃ row ∈ input.rom, row.1.toNat ≤ address ∧ address < row.1.toNat + 4 := by
  simp [readOnly]

end ProgramImage

end SP1Clean.Model.Core
