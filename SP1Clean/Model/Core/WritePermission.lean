import SP1Clean.Model.Core.ProgramImage
import SP1Clean.Model.Core.MemoryIntervals
import SP1Clean.Math.Address
import ToClean.Circuit.StaticTable
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Finite write permissions derived from the committed ROM

Nonempty zero-valued intervals of the ROM mask cover exactly the writable 48-bit addresses.
Inclusive endpoints fit three limbs even at the last native byte. The concrete fixed table
contains these endpoints, so its interpretation cannot be chosen by a witness producer.
-/

namespace SP1Clean.Model.Core

namespace ProgramImage

/-- One at every code byte and zero elsewhere, independently of the byte's instruction value. -/
def protectionMask (image : ProgramImage) : ByteMemory :=
  ⟨image.romBytes.map (fun byte => (byte.1, 1))⟩

private theorem protectionMask_mem (image : ProgramImage) (byte : ℕ × BitVec 8) :
    byte ∈ image.protectionMask.entries ↔ byte.2 = 1 ∧ image.readOnly byte.1 = true := by
  constructor
  · intro member
    obtain ⟨source, sourceMem, rfl⟩ := List.mem_map.mp member
    obtain ⟨row, rowMem, index, rfl⟩ := (image.mem_romBytes source).mp sourceMem
    exact ⟨rfl, (image.readOnly_iff _).mpr ⟨row, rowMem, by omega, by have := index.isLt; omega⟩⟩
  · rintro ⟨value, readonly⟩
    obtain ⟨row, rowMem, lower, upper⟩ := (image.readOnly_iff _).mp readonly
    let index : Fin 4 := ⟨byte.1 - row.1.toNat, by omega⟩
    apply List.mem_map.mpr
    refine ⟨(byte.1, row.2.extractLsb' (8 * index) 8), ?_, ?_⟩
    · exact (image.mem_romBytes _).mpr ⟨row, rowMem, index,
        Prod.ext (by dsimp only [index]; omega) rfl⟩
    · exact Prod.ext rfl value.symm

/-- Sparse mask lookup agrees with the semantic byte-level protection predicate. -/
theorem protectionMask_read (image : ProgramImage) (address : ℕ) :
    image.protectionMask.read address = if image.readOnly address then 1 else 0 := by
  cases readonly : image.readOnly address with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply ByteMemory.read_eq_zero_of_absent
      intro entry member equal
      have atEntry := ((image.protectionMask_mem entry).mp member).2
      rw [equal, readonly] at atEntry
      contradiction
  | true =>
      simp only [↓reduceIte]
      apply ByteMemory.read_eq_of_mem
      · exact (image.protectionMask_mem _).mpr ⟨rfl, readonly⟩
      · intro entry member _
        exact ((image.protectionMask_mem entry).mp member).1

/-- A finite interval inventory; empty intervals are omitted before inclusive encoding. -/
def writableIntervals (image : ProgramImage) : List MemoryInterval :=
  (image.protectionMask.intervals (2 ^ 48)).filter
    (fun interval => decide (interval.value = 0 ∧ interval.lower < interval.upper))

theorem writableIntervals_sound (image : ProgramImage) (interval : MemoryInterval)
    (member : interval ∈ image.writableIntervals) :
    interval.lower < interval.upper ∧ interval.upper ≤ 2 ^ 48 ∧
      ∀ address, interval.Contains address → address < 2 ^ 48 ∧ image.readOnly address = false := by
  obtain ⟨inMask, properties⟩ := List.mem_filter.mp member
  obtain ⟨zero, nonempty⟩ := of_decide_eq_true properties
  refine ⟨nonempty, (image.protectionMask.intervals_bounds _ interval inMask).2, ?_⟩
  intro address contains
  obtain ⟨bounded, value⟩ := image.protectionMask.intervals_sound _ interval inMask address contains
  rw [image.protectionMask_read, zero] at value
  refine ⟨bounded, ?_⟩
  cases readonly : image.readOnly address
  · rfl
  · simp [readonly] at value

/-- No writable address is lost when the concrete table is constructed. -/
theorem writableIntervals_complete (image : ProgramImage) (address : ℕ)
    (bounded : address < 2 ^ 48) (writable : image.readOnly address = false) :
    ∃ interval ∈ image.writableIntervals, interval.Contains address := by
  obtain ⟨interval, member, contains⟩ := image.protectionMask.intervals_complete _ address bounded
  have value := (image.protectionMask.intervals_sound _ interval member address contains).2
  rw [image.protectionMask_read, writable] at value
  refine ⟨interval, List.mem_filter.mpr ⟨member, ?_⟩, contains⟩
  apply decide_eq_true
  exact ⟨by simpa using value.symm, by have := contains.1; have := contains.2; omega⟩

theorem writableIntervals_length_le (image : ProgramImage) :
    image.writableIntervals.length ≤ 2 * image.romBytes.length + 1 := by
  have bound := image.protectionMask.intervals_length_le (2 ^ 48)
  have filtered := List.length_filter_le
    (fun interval : MemoryInterval => decide (interval.value = 0 ∧ interval.lower < interval.upper))
    (image.protectionMask.intervals (2 ^ 48))
  change _ ≤ _ at filtered
  apply le_trans filtered
  have support := image.protectionMask.supportBelow_card_le (2 ^ 48)
  have rows : image.protectionMask.entries.length = image.romBytes.length := by
    simp only [protectionMask, List.length_map]
  rw [rows] at support
  omega

/-- Deterministic finite lookup for permission-row construction. -/
def writableIntervalAt? (image : ProgramImage) (address : ℕ) : Option MemoryInterval :=
  image.writableIntervals.find? (fun interval => decide (interval.Contains address))

theorem writableIntervalAt?_sound (image : ProgramImage) (address : ℕ) (interval : MemoryInterval)
    (found : image.writableIntervalAt? address = some interval) :
    interval ∈ image.writableIntervals ∧ interval.Contains address :=
  ⟨List.mem_of_find?_eq_some found, by simpa using List.find?_some found⟩

theorem writableIntervalAt?_isSome_iff (image : ProgramImage) (address : ℕ) :
    (image.writableIntervalAt? address).isSome = true ↔
      address < 2 ^ 48 ∧ image.readOnly address = false := by
  constructor
  · intro present
    obtain ⟨interval, found⟩ := Option.isSome_iff_exists.mp present
    obtain ⟨member, contains⟩ := image.writableIntervalAt?_sound address interval found
    exact (image.writableIntervals_sound interval member).2.2 address contains
  · rintro ⟨bounded, writable⟩
    obtain ⟨interval, member, contains⟩ := image.writableIntervals_complete address bounded writable
    cases found : image.writableIntervalAt? address with
    | none =>
        have := List.find?_eq_none.mp found interval member
        simp [contains] at this
    | some interval => rfl

end ProgramImage

/-- An inclusive writable interval, with no prover-selected value or protection flag. -/
structure WritePermissionInterval (F : Type) where
  lower : fields 3 F
  upper : fields 3 F
deriving ProvableStruct, DecidableEq
provable_struct_eval_lemmas WritePermissionInterval

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def WritePermissionInterval.encode (interval : MemoryInterval) : WritePermissionInterval (ZMod p) :=
  ⟨Address.ofNat interval.lower, Address.ofNat (interval.upper - 1)⟩

@[irreducible] def ProgramImage.writePermissionTable (image : ProgramImage) :
    StaticTable (ZMod p) WritePermissionInterval :=
  StaticTable.ofRows "sp1.native.write_permission"
    (image.writableIntervals.map WritePermissionInterval.encode)

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
theorem ProgramImage.writePermissionTable_spec (image : ProgramImage)
    (row : WritePermissionInterval (ZMod p)) :
    image.writePermissionTable.Spec row ↔
      ∃ interval ∈ image.writableIntervals, WritePermissionInterval.encode interval = row := by
  simpa only [writePermissionTable, StaticTable.ofRows] using
    (List.mem_map : row ∈ image.writableIntervals.map WritePermissionInterval.encode ↔ _)

/-- Fixed lookup authenticates endpoint bounds and permission for every included byte. -/
theorem ProgramImage.writePermissionTable_sound (image : ProgramImage)
    (row : WritePermissionInterval (ZMod p)) (member : image.writePermissionTable.Spec row) :
    Address.Bounded row.lower ∧ Address.Bounded row.upper ∧
      ∀ address, Address.toNat row.lower ≤ address → address ≤ Address.toNat row.upper →
        address < 2 ^ 48 ∧ image.readOnly address = false := by
  obtain ⟨interval, inTable, rfl⟩ := (image.writePermissionTable_spec row).mp member
  obtain ⟨nonempty, upperBound, sound⟩ := image.writableIntervals_sound interval inTable
  refine ⟨Address.bounded_ofNat _, Address.bounded_ofNat _, ?_⟩
  intro address lower upper
  change Address.toNat (Address.ofNat (p := p) interval.lower) ≤ address at lower
  change address ≤ Address.toNat (Address.ofNat (p := p) (interval.upper - 1)) at upper
  rw [Address.toNat_ofNat _ (by omega)] at lower upper
  exact sound address ⟨lower, by omega⟩

end SP1Clean.Model.Core
