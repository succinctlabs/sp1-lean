import SP1Clean.Model.Core.MemorySnapshot
import SP1Clean.Model.Core.ProgramTable

/-! # Finite validation of local source data

An arbitrary snapshot must agree with the committed instruction bytes, including code that the
shard does not touch. Data memory may have changed since boot. The check also validates the finite
program and every decoded instruction, and rules out a nonzero x0. It never enumerates the address
space or requires an execution witness. Full Sail/host endpoint representation is separate.
-/

namespace SP1Clean.Model.Core

/-- Program validity, supported decoding, architectural x0, and complete ROM-byte agreement. -/
def SourceValid (image : ProgramImage) (snapshot : MemorySnapshot) : Prop :=
  image.Valid ∧ image.Decodable ∧ snapshot.Valid ∧
    ∀ entry ∈ image.rom, ∀ index : Fin 4,
      snapshot.memory.read (entry.1.toNat + index) = entry.2.extractLsb' (8 * index) 8

/-- Executable instance validation over finite input lists, independent of the AIR field. -/
def checkSource (image : ProgramImage) (snapshot : MemorySnapshot) : Bool :=
  image.checkFields && decide image.Decodable && decide (snapshot.registers[0] = 0) &&
    image.rom.all (fun entry => (List.finRange 4).all (fun index =>
      snapshot.memory.read (entry.1.toNat + index) == entry.2.extractLsb' (8 * index) 8))

theorem checkSource_iff (image : ProgramImage) (snapshot : MemorySnapshot) :
    checkSource image snapshot = true ↔ SourceValid image snapshot := by
  simp only [checkSource, SourceValid, Bool.and_eq_true, ProgramImage.checkFields_eq_true_iff,
    decide_eq_true_eq, List.all_eq_true, List.mem_finRange, forall_const, beq_iff_eq,
    MemorySnapshot.Valid, and_assoc]

/-- Every checked, supported image has a valid boot source without an additional loader premise. -/
theorem SourceValid.boot (image : ProgramImage) (valid : image.Valid) (decoded : image.Decodable) :
    SourceValid image image.memorySnapshot :=
  ⟨valid, decoded, by simp [MemorySnapshot.Valid, ProgramImage.memorySnapshot],
    image.initialMemory_rom valid⟩

/-- The finite ROM check reaches Sail's actual instruction-memory predicate through snapshot
realization. It covers all committed instructions, independently of this shard's accesses. -/
theorem SourceValid.romLoaded {image : ProgramImage} {snapshot : MemorySnapshot}
    (valid : SourceValid image snapshot) {state : SailState} (realizes : snapshot.Realizes state) :
    SP1Clean.Soundness.Target.RomLoaded (image.toGuestProgram valid.1) state := by
  intro address word fetched index
  obtain ⟨entry, found, wordEq⟩ := Option.map_eq_some_iff.mp fetched
  have member : entry ∈ image.rom := List.mem_of_find?_eq_some found
  have atPC : entry.1 = address := by simpa using List.find?_some found
  have window : 2 ^ 16 ≤ entry.1.toNat ∧ entry.1.toNat + 4 ≤ 2 ^ 48 :=
    (valid.1.2.1 entry member).2.1
  rw [← atPC, ← wordEq]
  exact (realizes.2 _ (by have := index.isLt; omega)).trans
    (congrArg some (valid.2.2.2 entry member index))

end SP1Clean.Model.Core
