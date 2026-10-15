import SP1Clean.Model.Semantics.GuestProgram

/-! # Auditable SP1 boot contract

`GuestProgram` contains the invariants needed to fetch its ROM, but those invariants alone do not say
that the entry point exists or that the byte-granular ELF image is compatible with the instruction
bytes loaded into the same Sail memory.  Those omissions can make `IsInitialState` empty and turn a
universally quantified execution statement into a vacuous theorem.

This file records the missing, loader-facing conditions without pretending to implement an ELF
loader.  The concrete loader belongs at the Rust/ELF bridge; the native machine consumes its result
through `Machine.SP1MachineModel`. -/

namespace SP1Clean.Soundness.Target.GuestProgram

/-- The program's entry point names an actual instruction word. -/
def EntryPointPresent (program : GuestProgram) : Prop :=
  ∃ instruction, program.fetchWord program.pc_start = some instruction

/-- The byte image has at most one value for each address. -/
def ImageAddressesUnique (program : GuestProgram) : Prop :=
  (program.memImage.map Prod.fst).Nodup

/-- If an ELF data-image byte overlaps a ROM word, both loaders demand the same byte.  Without this
condition `RomLoaded` and `IsInitialState.imageLoaded` can contradict one another. -/
def ImageCompatibleWithROM (program : GuestProgram) : Prop :=
  ∀ address instruction, program.fetchWord address = some instruction →
    ∀ index : Fin 4, ∀ imageEntry ∈ program.memImage,
      imageEntry.1.toNat = address.toNat + index →
      imageEntry.2 = instruction.extractLsb' (8 * index) 8

/-- The program-level precondition expected of an ELF-to-`GuestProgram` bridge.  ROM uniqueness,
alignment, code-window bounds, and non-compressed width are already fields of `GuestProgram`; these
are the additional cross-field obligations. -/
structure WellFormed (program : GuestProgram) : Prop where
  entryPointPresent : EntryPointPresent program
  imageAddressesUnique : ImageAddressesUnique program
  imageCompatibleWithROM : ImageCompatibleWithROM program

/-- Semantic non-vacuity of the loader relation.  This is stronger than `WellFormed`: an actual ELF
bridge should construct the witness and thereby prove this predicate. -/
def HasInitialState (program : GuestProgram) : Prop :=
  ∃ initial, IsInitialState program initial

end SP1Clean.Soundness.Target.GuestProgram
