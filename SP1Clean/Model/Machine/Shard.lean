import SP1Clean.Model.Machine.EventExecution
import SP1Clean.Model.Semantics.MicroTime

/-! # Canonical proof-free Core shard data

Soundness and completeness use the same shard witness in this module.  The witness stores the
program, the finite Memory boundary, private initial state, and event transcript; it does not store
a second copy of the intermediate Sail states. A `CoreShardModel` supplies the statement projection
and executable syscall semantics. `CoreShardSemanticWitness.trace?`
then reconstructs the one `EventExecutionTrace` checked by the semantic relation.

This is deliberately below every AIR representation.  Native Clean tables and extracted Rust rows
are two compilers for this data, not fields of its validity predicate. -/

open LeanRV64D.Defs

namespace SP1Clean.Machine

open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.Soundness.Target
open SP1Clean.Semantics

/-- Public execution coordinates shared by the native and exact Core statements.  `exit` is the
committed exit-code cell decoded to the Sail width; it becomes meaningful on halting shards
(the halt row binds the cell to the reduced `a0` word). -/
structure CoreShardBoundary where
  isExecution : Bool
  initialClock : ℕ
  initialPc : BitVec 64
  finalClock : ℕ
  finalPc : BitVec 64
  exit : BitVec 64
deriving DecidableEq, Repr

/-- One finite Memory-bus location at the beginning and end of a shard. -/
structure CoreMemoryBoundaryCell where
  loc : MemLoc
  initialValue : BitVec 64
  finalValue : BitVec 64
  finalClock : ℕ
deriving DecidableEq

/-- Proof-free finite Memory boundary.  Ordering, uniqueness, address canonicity, and agreement with
the reconstructed execution are properties of the semantic relation rather than proof fields. -/
structure CoreMemoryBoundary where
  cells : List CoreMemoryBoundaryCell
deriving DecidableEq

namespace CoreMemoryBoundary

/-- Locations are represented once in a shard boundary. -/
def LocationsNodup (boundary : CoreMemoryBoundary) : Prop :=
  (boundary.cells.map CoreMemoryBoundaryCell.loc).Nodup

/-- Representation-level validity shared by both AIR directions.  The timestamp on a final record
cannot escape the shard and every location has the one canonical 48-bit Memory-bus encoding. -/
def WellFormed (boundary : CoreMemoryBoundary) (finalClock : ℕ) : Prop :=
  boundary.LocationsNodup ∧
    ∀ cell ∈ boundary.cells,
      cell.loc.CanonicalAddress ∧ cell.finalClock ≤ finalClock

/-- Representation validity is monotone in the clock ceiling. -/
theorem WellFormed.mono {boundary : CoreMemoryBoundary} {t t' : ℕ}
    (wf : boundary.WellFormed t) (le : t ≤ t') : boundary.WellFormed t' :=
  ⟨wf.1, fun cell cellMem => ⟨(wf.2 cell cellMem).1, le_trans (wf.2 cell cellMem).2 le⟩⟩

/-- The finite boundary agrees with the semantic states at both ends of the shard. -/
def AgreesWith (boundary : CoreMemoryBoundary) (initial final : SailState) : Prop :=
  ∀ cell ∈ boundary.cells,
    locContent initial cell.loc = some cell.initialValue ∧
      locContent final cell.loc = some cell.finalValue

end CoreMemoryBoundary

/-- Executable host semantics.  Its graph is the `SyscallHandler` used by `EventStep`; a concrete
integration therefore cannot choose one syscall target in the witness and prove a different target
through an unrelated relational handler. -/
structure ExecutableSyscallHandler where
  run : GuestProgram → CoreSyscallEvent → SailState → Option SailState

namespace ExecutableSyscallHandler

/-- Relational view consumed by the existing event semantics. -/
def relation (handler : ExecutableSyscallHandler) : SyscallHandler :=
  fun program event source target => handler.run program event source = some target

/-- The syscall-free machine used by the ordinary native restriction. -/
def none : ExecutableSyscallHandler where
  run := fun _ _ _ => Option.none

/-- **The canonical HALT arm of SP1's host semantics**, and nothing else: on the exact Rust
`SyscallCode::HALT` code (`rawCode = 0`) the terminal transition parks the machine at the
executor's `haltPc` and leaves every other register and all of memory untouched — matching
`CoreSyscallEvent.PcLaw`/`MatchesStates` (the target's pc is `nextPc = haltPc`, `x5` keeps the
zero result).  Every non-halt syscall evaluates to `Option.none`: outside the supported
profile. -/
def haltOnly : ExecutableSyscallHandler where
  run := fun _ event source =>
    if event.rawCode = 0 then
      some { source with regs := source.regs.insert Register.PC haltPc }
    else
      Option.none

end ExecutableSyscallHandler

/-- Statement-dependent data needed to interpret the common shard witness.  Exact preprocessing
authentication extends this structure at the FormalModel boundary; it is not baked into the
machine-level execution carrier. -/
structure CoreShardModel (Statement : Type) where
  boundary : Statement → CoreShardBoundary
  programBound : Statement → GuestProgram → Prop
  syscalls : ExecutableSyscallHandler

/-- The single proof-free semantic witness shared by native and exact soundness/completeness.
`none` denotes a boundary-only shard; an execution shard stores an initial state and its stable
event transcript, never a redundant list of target states.  The initial state is private semantic
data: public PC/clock values and a finite touched-location boundary do not determine every Sail
register, so pretending it could always be reconstructed from the statement would narrow the
language. -/
structure CoreShardSemanticWitness where
  program : GuestProgram
  memoryBoundary : CoreMemoryBoundary
  initialState : SailState
  events : Option (List ExecutionEvent)

/-- Syscall transcript exposed by the common witness; boundary-only shards expose the empty list. -/
def CoreShardSemanticWitness.syscallEvents
    (witness : CoreShardSemanticWitness) : List CoreSyscallEvent :=
  witness.events.getD [] |>.filterMap fun
    | .ordinary => none
    | .syscall event => some event

/-- Execute one transcript event.  Ordinary events use the complete official Sail `try_step` entry
point; syscall events use the executable handler supplied by the model. -/
noncomputable def executeEvent? (handler : ExecutableSyscallHandler) (program : GuestProgram)
    (source : SailState) : ExecutionEvent → Option SailState
  | .ordinary =>
      match (try_step 0 false).run source with
      | .ok _ target => some target
      | .error _ _ => none
  | .syscall event => handler.run program event source

/-- Execute a transcript while retaining the target of every transition. -/
noncomputable def executeEvents? (handler : ExecutableSyscallHandler) (program : GuestProgram) :
    SailState → List ExecutionEvent → Option (List EventTransition)
  | _, [] => some []
  | source, event :: rest => do
      let target ← executeEvent? handler program source event
      let tail ← executeEvents? handler program target rest
      pure (⟨event, target⟩ :: tail)

/-- Deterministically reconstruct the official-Sail trace represented by an execution transcript. -/
noncomputable def traceOfEvents? (handler : ExecutableSyscallHandler) (program : GuestProgram)
    (initial : SailState) (events : List ExecutionEvent) : Option EventExecutionTrace := do
  let transitions ← executeEvents? handler program initial events
  pure ⟨initial, transitions⟩

/-- Re-evaluating the event projection of a valid ordinary transition list recovers its exact
proof-free targets.  This is the representation bridge used by native soundness and completeness;
it follows from determinism of the official `try_step` entry point, not from proof irrelevance. -/
theorem executeEvents?_of_valid_allOrdinary (handler : ExecutableSyscallHandler)
    (program : GuestProgram) {source : SailState} {transitions : List EventTransition}
    (valid : EventTransitionsValid handler.relation program source transitions)
    (ordinary : ∀ transition ∈ transitions, transition.event = .ordinary) :
    executeEvents? handler program source
      (transitions.map EventTransition.event) = some transitions := by
  induction valid with
  | nil => rfl
  | @cons source transition rest step tail ih =>
      have headOrdinary : transition.event = .ordinary := ordinary transition (by simp)
      have restOrdinary : ∀ item ∈ rest, item.event = .ordinary :=
        fun item itemMem => ordinary item (by simp [itemMem])
      rcases transition with ⟨event, target⟩
      simp only at headOrdinary
      subst event
      cases step with
      | ordinary _ sailStep =>
          obtain ⟨result, evaluated⟩ := sailStep
          simp [executeEvents?, executeEvent?, evaluated, ih restOrdinary]

/-- Re-evaluating the event projection of **any** valid transition list recovers its exact
proof-free targets: ordinary steps by determinism of `try_step`, syscall steps by the executable
handler's own graph (`ExecutableSyscallHandler.relation` is definitionally `run = some`). -/
theorem executeEvents?_of_valid (handler : ExecutableSyscallHandler)
    (program : GuestProgram) {source : SailState} {transitions : List EventTransition}
    (valid : EventTransitionsValid handler.relation program source transitions) :
    executeEvents? handler program source
      (transitions.map EventTransition.event) = some transitions := by
  induction valid with
  | nil => rfl
  | @cons source transition rest step tail ih =>
      rcases transition with ⟨event, target⟩
      cases step with
      | ordinary _ sailStep =>
          obtain ⟨result, evaluated⟩ := sailStep
          simp [executeEvents?, executeEvent?, evaluated, ih]
      | syscall _ syscallStep =>
          have run : handler.run program _ source = some target := syscallStep.2.2
          simp [executeEvents?, executeEvent?, run, ih]

/-- Any valid trace is the unique trace reconstructed from its stable event transcript. -/
theorem traceOfEvents?_of_valid (handler : ExecutableSyscallHandler)
    (program : GuestProgram) (execution : EventExecutionTrace)
    (valid : execution.Valid handler.relation program) :
    traceOfEvents? handler program execution.initialState execution.events = some execution := by
  simp only [traceOfEvents?, EventExecutionTrace.events]
  rw [executeEvents?_of_valid handler program valid]
  rfl

/-- A valid ordinary trace is the unique trace reconstructed from its stable event transcript. -/
theorem traceOfEvents?_of_valid_allOrdinary (handler : ExecutableSyscallHandler)
    (program : GuestProgram) (execution : EventExecutionTrace)
    (valid : execution.Valid handler.relation program)
    (ordinary : execution.AllOrdinary) :
    traceOfEvents? handler program execution.initialState execution.events = some execution := by
  simp only [traceOfEvents?, EventExecutionTrace.events]
  rw [executeEvents?_of_valid_allOrdinary handler program valid ordinary]
  rfl

/-- Embed an existing ordinary official-Sail trace into the common proof-free shard carrier. -/
def CoreShardSemanticWitness.ofOrdinaryTrace (program : GuestProgram)
    (memoryBoundary : CoreMemoryBoundary) (execution : EventExecutionTrace) :
    CoreShardSemanticWitness where
  program := program
  memoryBoundary := memoryBoundary
  initialState := execution.initialState
  events := some execution.events

/-- Reconstruct the optional execution carried by a canonical shard witness. -/
noncomputable def CoreShardSemanticWitness.trace? {Statement : Type}
    (model : CoreShardModel Statement)
    (witness : CoreShardSemanticWitness) : Option EventExecutionTrace :=
  witness.events.bind fun events =>
    traceOfEvents? model.syscalls witness.program witness.initialState events

/-- The common carrier's evaluator is a left inverse of `ofOrdinaryTrace` on valid ordinary
traces. -/
theorem CoreShardSemanticWitness.trace?_ofOrdinaryTrace {Statement : Type}
    (model : CoreShardModel Statement) (program : GuestProgram)
    (memoryBoundary : CoreMemoryBoundary) (execution : EventExecutionTrace)
    (valid : execution.Valid model.syscalls.relation program)
    (ordinary : execution.AllOrdinary) :
    (CoreShardSemanticWitness.ofOrdinaryTrace program memoryBoundary execution).trace? model =
      some execution := by
  exact traceOfEvents?_of_valid_allOrdinary model.syscalls program execution valid ordinary

/-- Total trace projection used by witness compilers.  Malformed transcripts map to the empty
trace at the supplied initial state; relation validity proves that branch unreachable before any
property of the compiled trace is used. -/
noncomputable def CoreShardSemanticWitness.evaluatedTrace {Statement : Type}
    (model : CoreShardModel Statement) (witness : CoreShardSemanticWitness) :
    EventExecutionTrace :=
  (witness.trace? model).getD ⟨witness.initialState, []⟩

/-- The common carrier's evaluator is a left inverse of the trace embedding on **any** valid
trace — the halting-shard companion of `trace?_ofOrdinaryTrace`. -/
theorem CoreShardSemanticWitness.trace?_ofTrace {Statement : Type}
    (model : CoreShardModel Statement) (program : GuestProgram)
    (memoryBoundary : CoreMemoryBoundary) (execution : EventExecutionTrace)
    (valid : execution.Valid model.syscalls.relation program) :
    (CoreShardSemanticWitness.ofOrdinaryTrace program memoryBoundary execution).trace? model =
      some execution := by
  simp only [CoreShardSemanticWitness.trace?, CoreShardSemanticWitness.ofOrdinaryTrace,
    Option.bind_some]
  exact traceOfEvents?_of_valid model.syscalls program execution valid

theorem CoreShardSemanticWitness.evaluatedTrace_eq_of_trace? {Statement : Type}
    {model : CoreShardModel Statement} {witness : CoreShardSemanticWitness}
    {trace : EventExecutionTrace} (evaluated : witness.trace? model = some trace) :
    witness.evaluatedTrace model = trace := by
  simp [CoreShardSemanticWitness.evaluatedTrace, evaluated]

/-- Evaluation never changes the private initial state, including on the total fallback branch. -/
@[simp] theorem CoreShardSemanticWitness.evaluatedTrace_initialState {Statement : Type}
    (model : CoreShardModel Statement) (witness : CoreShardSemanticWitness) :
    (witness.evaluatedTrace model).initialState = witness.initialState := by
  unfold CoreShardSemanticWitness.evaluatedTrace CoreShardSemanticWitness.trace?
  cases events : witness.events with
  | none => simp
  | some transcript =>
      simp only [Option.bind_some, traceOfEvents?]
      cases evaluated : executeEvents? model.syscalls witness.program witness.initialState transcript <;>
        simp

/-- Semantic event counts, independent of a field or either AIR representation. -/
structure CoreTraceResources where
  ordinaryEvents : ℕ
  syscallEvents : ℕ
  memoryBoundaryCells : ℕ
  ticks : ℕ
deriving DecidableEq, Repr

/-- Resource accounting for the common shard representation. -/
def CoreShardSemanticWitness.resources (witness : CoreShardSemanticWitness) : CoreTraceResources :=
  let events := witness.events.getD []
  { ordinaryEvents := events.countP (· = .ordinary)
    syscallEvents := events.countP fun event => match event with
      | .ordinary => false
      | .syscall _ => true
    memoryBoundaryCells := witness.memoryBoundary.cells.length
    ticks := events.foldl (fun total event => total + event.duration) 0 }

/-- Representation-independent shard capacity.  Exact per-table trace heights refine this coarse
profile in the Core AIR context, while the native compiler proves its physical footprint from it. -/
structure CoreTraceBudget where
  maxOrdinaryEvents : ℕ
  maxSyscallEvents : ℕ
  maxMemoryBoundaryCells : ℕ
  maxTicks : ℕ
deriving DecidableEq, Repr

/-- A semantic shard fits a declared resource budget. -/
def CoreTraceBudget.Fits (budget : CoreTraceBudget) (resources : CoreTraceResources) : Prop :=
  resources.ordinaryEvents ≤ budget.maxOrdinaryEvents ∧
    resources.syscallEvents ≤ budget.maxSyscallEvents ∧
    resources.memoryBoundaryCells ≤ budget.maxMemoryBoundaryCells ∧
    resources.ticks ≤ budget.maxTicks

end SP1Clean.Machine
