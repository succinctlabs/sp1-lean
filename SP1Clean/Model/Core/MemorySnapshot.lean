import SP1Clean.Model.Core.Boot
import SP1Clean.Model.Core.MemoryEquality

/-! # Finite register and RAM snapshots at a local execution boundary

A snapshot records every integer register and the complete zero-default byte memory, including
locations that a shard never touches. `Realizes` compares these observations with an actual Sail
state. It is a representation relation, not an AIR premise or equality of complete machine states:
PC, platform registers, Sail bookkeeping, host state, and clock are deliberately outside this type.
Those still belong to `ExecutionState` and must agree at a composed execution boundary.
-/

namespace SP1Clean.Model.Core

open SP1Clean.Semantics SP1Clean.Soundness.Target

structure MemorySnapshot where
  registers : Vector (BitVec 64) 32
  memory : ByteMemory
deriving DecidableEq, Repr

namespace MemorySnapshot

/-- The architectural x0 condition on finite input data. -/
def Valid (snapshot : MemorySnapshot) : Prop := snapshot.registers[0] = 0

/-- Executable content at the same register/aligned-word locations used by the Memory bus. -/
def read (snapshot : MemorySnapshot) : MemLoc → BitVec 64
  | .reg index => snapshot.registers[index.toNat]
  | .ram cell => snapshot.memory.readWord (cell.toNat * 8)

theorem read_of_ram_address (snapshot : MemorySnapshot) (location : MemLoc)
    (ram : 32 ≤ location.busAddress) :
    snapshot.read location = snapshot.memory.readWord location.busAddress := by
  cases location with
  | reg index => have := index.isLt; simp only [MemLoc.busAddress] at ram; omega
  | ram cell => rfl

/-- Agreement covers all registers and every supported byte, not just the touched inventory. -/
def Realizes (snapshot : MemorySnapshot) (state : SailState) : Prop :=
  (∀ index : BitVec 5, state.get_reg? index = some (snapshot.read (.reg index))) ∧
    ∀ address < 2 ^ 48, state.mem.get? address = some (snapshot.memory.read address)

theorem Realizes.valid {snapshot : MemorySnapshot} {state : SailState}
    (realizes : snapshot.Realizes state) : snapshot.Valid := by
  have zero := realizes.1 0
  simpa [SailState.get_reg?, read, Valid] using zero.symm

/-- Full byte agreement also covers RAM below the bus's register-reserved addresses. -/
theorem Realizes.locContent_of_address_lt {snapshot : MemorySnapshot} {state : SailState}
    (realizes : snapshot.Realizes state) (location : MemLoc)
    (bound : location.busAddress < 2 ^ 48) :
    locContent state location = some (snapshot.read location) := by
  cases location with
  | reg index => exact realizes.1 index
  | ram cell =>
      have upper : cell.toNat * 8 < 2 ^ 48 := bound
      have base : cell.baseAddr.toNat = cell.toNat * 8 := by
        exact (BitVec.toNat_ofNat _ _).trans (Nat.mod_eq_of_lt (by omega))
      change ramWord64? state cell.baseAddr = _
      rw [snapshot.memory.ramWord64?_of_bytes state cell.baseAddr (fun index => by
        rw [base]
        exact realizes.2 _ (by have := index.isLt; omega)), base]
      rfl

/-- Full byte agreement implies agreement at every canonically encoded bus location. -/
theorem Realizes.locContent {snapshot : MemorySnapshot} {state : SailState}
    (realizes : snapshot.Realizes state) (location : MemLoc)
    (canonical : location.CanonicalAddress) :
    locContent state location = some (snapshot.read location) :=
  realizes.locContent_of_address_lt location (MemLoc.busAddress_lt_two_pow_48 canonical)

/-- Extensional comparison ignores obsolete writes in the sparse update history. It still
checks every supported byte, so a mutation at an untouched location cannot disappear. -/
def Equivalent (left right : MemorySnapshot) : Prop :=
  left.registers = right.registers ∧
    ∀ address < 2 ^ 48, left.memory.read address = right.memory.read address

/-- Executable comparison includes every supported byte without enumerating the address space. -/
def equivalent (left right : MemorySnapshot) : Bool :=
  decide (left.registers = right.registers) && left.memory.agreesBelow right.memory (2 ^ 48)

theorem equivalent_iff (left right : MemorySnapshot) :
    left.equivalent right = true ↔ left.Equivalent right := by
  simp only [equivalent, Bool.and_eq_true, decide_eq_true_eq, ByteMemory.agreesBelow_iff, Equivalent]

theorem Realizes.equivalent {left right : MemorySnapshot} {state : SailState}
    (leftRealizes : left.Realizes state) (rightRealizes : right.Realizes state) :
    left.Equivalent right := by
  refine ⟨?_, fun address bound => Option.some.inj
    ((leftRealizes.2 address bound).symm.trans (rightRealizes.2 address bound))⟩
  apply Vector.ext
  intro index bound
  have agree := Option.some.inj
    ((leftRealizes.1 (BitVec.ofNat 5 index)).symm.trans (rightRealizes.1 (BitVec.ofNat 5 index)))
  simpa only [read, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] using agree

theorem Equivalent.realizes {left right : MemorySnapshot} {state : SailState}
    (equivalent : left.Equivalent right) (realizes : left.Realizes state) : right.Realizes state := by
  refine ⟨?_, fun address bound => (realizes.2 address bound).trans
    (congrArg some (equivalent.2 address bound))⟩
  intro index
  simpa only [read, equivalent.1] using realizes.1 index

end MemorySnapshot

/-- Boot is one finite memory snapshot, with its usual zeroed integer registers. -/
def ProgramImage.memorySnapshot (image : ProgramImage) : MemorySnapshot :=
  ⟨Vector.replicate 32 0, image.initialMemory⟩

theorem ProgramImage.memorySnapshot_realizes (image : ProgramImage) :
    image.memorySnapshot.Realizes image.initialSailState := by
  refine ⟨?_, image.initialSailState_memory⟩
  intro index
  simpa only [MemorySnapshot.read, memorySnapshot, Vector.getElem_replicate] using
    image.initialSailState_registersZero index

end SP1Clean.Model.Core
