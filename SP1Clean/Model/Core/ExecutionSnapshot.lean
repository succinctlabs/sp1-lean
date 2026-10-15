import SP1Clean.Model.Core.SailRegisterEquality
import SP1Clean.Model.Core.MemorySnapshot
import SP1Clean.Model.Core.ExecutionBoot

/-! # Complete finite snapshots of local execution states

Unlike a MemorySnapshot, this representation retains every Sail register (including absent keys),
the runtime cycle counter and output, the complete host state, and the execution clock. Sail's
choice state and tags are Unit. Only RAM changes representation: sparse zero-default bytes realize
the exact bounded Sail map, with every address outside the native window absent.

Executable equality compares the full state without enumerating the address space. Its theorem
is literal equality of realized execution states, so it can justify semantic path composition
without resetting bookkeeping or ignoring untouched memory. The AIR must still bind both complete
snapshots and prove its final state realizes the outgoing one; this module does not assume that
binding into an ensemble relation or claim certified AIR composition.
-/

namespace SP1Clean.Model.Core

open LeanRV64D.Defs SP1Clean.Soundness.Target

/-- All nontrivial fields of the official Sail state, with sparse native RAM. -/
structure SailSnapshot where
  registers : SailRegisterFile.Map
  memory : ByteMemory
  cycleCount : ℕ := 0
  output : Array String := #[]

namespace SailSnapshot

/-- The register/runtime carrier is executable without materializing the dense Sail memory. -/
def skeleton (snapshot : SailSnapshot) : SailState where
  regs := snapshot.registers
  choiceState := ()
  mem := ∅
  tags := ()
  cycleCount := snapshot.cycleCount
  sailOutput := snapshot.output

/-- Semantic realization; the compiler never evaluates the dense bounded memory map. -/
def realize (snapshot : SailSnapshot) : SailState :=
  { snapshot.skeleton with mem := snapshot.memory.toSailMemory (2 ^ 48) }

/-- Capture all runtime fields while using a supplied sparse memory representation. -/
def capture (state : SailState) (memory : ByteMemory) : SailSnapshot :=
  ⟨state.regs, memory, state.cycleCount, state.sailOutput⟩

theorem realize_capture (state : SailState) (memory : ByteMemory)
    (represents : memory.toSailMemory (2 ^ 48) = state.mem) :
    (capture state memory).realize = state := by
  cases state with
  | mk registers choice mem tags cycles output =>
      cases choice
      cases tags
      simp only [capture, realize, skeleton, represents]

/-- Equality checks every stored register and runtime field, as well as every supported byte. -/
def equivalent (left right : SailSnapshot) : Bool :=
  SailRegisterFile.equivalent left.registers right.registers &&
    left.memory.agreesBelow right.memory (2 ^ 48) &&
    decide (left.cycleCount = right.cycleCount) && decide (left.output = right.output)

theorem realize_eq_iff (left right : SailSnapshot) :
    left.realize = right.realize ↔
      left.registers = right.registers ∧
      (∀ address < 2 ^ 48, left.memory.read address = right.memory.read address) ∧
      left.cycleCount = right.cycleCount ∧ left.output = right.output := by
  constructor
  · intro equal
    exact ⟨congrArg (·.regs) equal,
      (ByteMemory.toSailMemory_eq_iff _ _ _).mp (congrArg (·.mem) equal),
      congrArg (·.cycleCount) equal, congrArg (·.sailOutput) equal⟩
  · rintro ⟨registers, memory, cycles, output⟩
    have mem := (ByteMemory.toSailMemory_eq_iff _ _ _).mpr memory
    simp only [realize, skeleton, registers, mem, cycles, output]

theorem equivalent_iff (left right : SailSnapshot) :
    left.equivalent right = true ↔ left.realize = right.realize := by
  simp only [equivalent, Bool.and_eq_true, SailRegisterFile.equivalent_iff,
    ByteMemory.agreesBelow_iff, decide_eq_true_eq, realize_eq_iff, and_assoc]

/-- The provider projection observes GPRs directly from the finite register map. Missing GPRs
default to zero here; the realization theorem explicitly requires their initialization. -/
def memorySnapshot (snapshot : SailSnapshot) : MemorySnapshot where
  registers := Vector.ofFn (fun index =>
    (snapshot.skeleton.get_reg? (BitVec.ofNat 5 index.val)).getD 0)
  memory := snapshot.memory

private theorem transported_getD {α β : Type} (equal : α = β) (value : α) (fallback : β) :
    (equal ▸ some value : Option β) = some ((equal ▸ some value : Option β).getD fallback) := by
  cases equal
  rfl

/-- Initialized full register files give the source providers precisely the realized Sail bytes
and GPRs; the default for an absent GPR cannot be used by this theorem. -/
theorem memorySnapshot_realizes (snapshot : SailSnapshot)
    (initialized : snapshot.skeleton.isInitialized) :
    snapshot.memorySnapshot.Realizes snapshot.realize := by
  refine ⟨?_, fun address bound =>
    (snapshot.memory.toSailMemory_get? (2 ^ 48) address).trans (if_pos bound)⟩
  intro index
  simp only [MemorySnapshot.read, memorySnapshot, Vector.getElem_ofFn]
  rw [show BitVec.ofNat 5 index.toNat = index by simp]
  have present (reg : Register) : snapshot.registers.get? reg =
      some (snapshot.registers.get reg (initialized reg)) :=
    Std.ExtDHashMap.get?_eq_some_get (initialized reg)
  simp only [SailState.get_reg?, realize, skeleton]
  split
  · rfl
  · rw [present]
    exact transported_getD _ _ _

/-- All source-provider representations satisfy the architectural x0 convention. -/
theorem memorySnapshot_valid (snapshot : SailSnapshot) : snapshot.memorySnapshot.Valid := by
  simp [MemorySnapshot.Valid, memorySnapshot, SailState.get_reg?]

end SailSnapshot

/-- Complete input/output data for a local segment, including continuing or terminal host state. -/
structure ExecutionSnapshot where
  sail : SailSnapshot
  host : HostState
  clock : ℕ

namespace ExecutionSnapshot

def realize (snapshot : ExecutionSnapshot) : ExecutionState :=
  ⟨snapshot.sail.realize, snapshot.host, snapshot.clock⟩

def capture (state : ExecutionState) (memory : ByteMemory) : ExecutionSnapshot :=
  ⟨SailSnapshot.capture state.sail memory, state.host, state.clock⟩

theorem realize_capture (state : ExecutionState) (memory : ByteMemory)
    (represents : memory.toSailMemory (2 ^ 48) = state.sail.mem) :
    (capture state memory).realize = state := by
  have sail := SailSnapshot.realize_capture state.sail memory represents
  cases state
  simp only [capture, realize, sail]

/-- Capturing a represented state and comparing it does not lose any runtime or host field. -/
theorem capture_realize (snapshot : ExecutionSnapshot) :
    capture snapshot.realize snapshot.sail.memory = snapshot := by
  cases snapshot with
  | mk sail host clock => cases sail; rfl

def equivalent (left right : ExecutionSnapshot) : Bool :=
  left.sail.equivalent right.sail && decide (left.host = right.host) && decide (left.clock = right.clock)

theorem equivalent_iff (left right : ExecutionSnapshot) :
    left.equivalent right = true ↔ left.realize = right.realize := by
  simp only [equivalent, Bool.and_eq_true, SailSnapshot.equivalent_iff, decide_eq_true_eq,
    realize, ExecutionState.mk.injEq, and_assoc]

/-- Even an empty segment must preserve the complete finite boundary, extensionally. -/
theorem zero_iff (policy : HostPolicy) (program : GuestProgram) (source target : ExecutionSnapshot) :
    ExecutionSegment policy program source.realize 0 target.realize ↔
      source.equivalent target = true := by
  rw [ExecutionSegment.zero_iff, equivalent_iff, eq_comm]

/-- A successful finite comparison suffices to join semantic segments at the exact full state.
The segments' AIR certification and resource bounds belong to the enclosing core theorem. -/
theorem compose {policy : HostPolicy} {program : GuestProgram}
    {source left right target : ExecutionSnapshot} {m n : ℕ}
    (first : ExecutionSegment policy program source.realize m left.realize)
    (second : ExecutionSegment policy program right.realize n target.realize)
    (same : left.equivalent right = true) :
    ExecutionSegment policy program source.realize (m + n) target.realize := by
  rw [← (equivalent_iff left right).mp same] at second
  exact first.append second

end ExecutionSnapshot

/-- Boot supplies one complete finite boundary; continuing shards need not use this constructor. -/
noncomputable def ProgramImage.executionBootSnapshot (image : ProgramImage) (input : HostInputs) :
    ExecutionSnapshot := ExecutionSnapshot.capture (image.executionBoot input) image.initialMemory

theorem ProgramImage.executionBootSnapshot_realize (image : ProgramImage) (input : HostInputs) :
    (image.executionBootSnapshot input).realize = image.executionBoot input :=
  ExecutionSnapshot.realize_capture _ _ rfl

end SP1Clean.Model.Core
