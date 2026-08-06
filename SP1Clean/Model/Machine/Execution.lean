import SP1Clean.Model.Machine.Schedule
import SP1Clean.Model.Machine.Boot
import PolyFun.PFunctor.Dynamical.Basic
import PolyFun.PFunctor.Dynamical.Run

/-! # The Lean-native SP1 execution machine

The official Sail `try_step` function remains the instruction semantics.  This file packages its
deterministic trajectory as a small PolyFun dynamical system: the exposed observation is the current
`Option SailState`, and the sole direction is `PUnit`.  Failure is represented by `none`, which then
stutters, making the transition total without treating an interpreter error as a successful halt.

PolyFun is used only for this semantic transition/run interface.  Circuit construction and Clean's
interaction machinery remain independent of it. -/

open LeanRV64D.Defs

namespace SP1Clean.Machine

open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.Soundness.Target

/-- SP1 starts execution with a zeroed integer register file. -/
def RegistersZero (state : SailState) : Prop :=
  ∀ index : BitVec 5, state.get_reg? index = some 0

/-- The two pieces of platform policy that must be fixed independently of a proof witness:

* the ELF/program loader selects an initial Sail state for every well-formed program; and
* the timing policy assigns the upstream interaction window of the instruction in a pre-state.

Keeping this record outside `ExecutionWitness` prevents a malicious witness from choosing a convenient
initial CSR state or a convenient clock schedule.  A concrete SP1 integration must provide one audited
value of this type. -/
structure SP1MachineModel where
  boot : (program : GuestProgram) → program.WellFormed → SailState
  boot_loaded : ∀ (program : GuestProgram) (wellFormed : program.WellFormed),
    IsInitialState program (boot program wellFormed)
  boot_registers_zero : ∀ (program : GuestProgram) (wellFormed : program.WellFormed),
    RegistersZero (boot program wellFormed)
  schedule : GuestProgram → SailState → StepSchedule

/-- The timing policy for the presently supported 25-chip slice.  Those chips are all ordinary
eight-tick instruction rows; syscall- and precompile-aware models intentionally do not satisfy this
predicate globally and belong to the full-machine schedule bridge. -/
def SP1MachineModel.UsesOrdinarySchedule (model : SP1MachineModel) : Prop :=
  ∀ program state, model.schedule program state = ordinarySchedule

/-- Everything fixed before an execution begins.  Public-value and verifying-key bindings are kept
at the AIR relation boundary rather than hidden in the transition system. -/
structure ExecutionCtx (model : SP1MachineModel) where
  program : GuestProgram
  wellFormed : program.WellFormed

/-- The unique boot state selected by the model for this execution context.  Proof irrelevance makes
the result independent of the particular proof term stored in `wellFormed`. -/
def ExecutionCtx.initial {model : SP1MachineModel} (ctx : ExecutionCtx model) : SailState :=
  model.boot ctx.program ctx.wellFormed

theorem ExecutionCtx.loaded {model : SP1MachineModel} (ctx : ExecutionCtx model) :
    IsInitialState ctx.program ctx.initial :=
  model.boot_loaded ctx.program ctx.wellFormed

theorem ExecutionCtx.registersZero {model : SP1MachineModel} (ctx : ExecutionCtx model) :
    RegistersZero ctx.initial :=
  model.boot_registers_zero ctx.program ctx.wellFormed

/-- One deterministic Sail step, totalized with `Option`. -/
noncomputable def stepOnce (state : SailState) : Option SailState :=
  match (try_step 0 false).run state with
  | .ok _ next => some next
  | .error _ _ => none

/-- The canonical total trajectory.  Once `try_step` fails, all later states remain `none`. -/
noncomputable def trajectory (initial : SailState) : ℕ → Option SailState
  | 0 => some initial
  | n + 1 => (trajectory initial n).bind stepOnce

/-- Running the deterministic trajectory for `m + n` steps is the same as running `m` steps and,
if that succeeds, restarting the machine from the intermediate state for `n` more steps.  This is
the composition lemma used to anchor a locally proved AIR shard in the canonical boot run. -/
theorem trajectory_add (initial : SailState) (m n : ℕ) :
    trajectory initial (m + n) = (trajectory initial m).bind fun state => trajectory state n := by
  induction n with
  | zero => simp [trajectory]
  | succ n ih =>
      rw [Nat.add_succ, trajectory, ih]
      simp only [trajectory, Option.bind_assoc]

/-- The deterministic interface exposed by the SP1 semantic machine.  Both universes are pinned:
`linear`'s direction universe is otherwise unconstrained by its `PUnit` direction family, which can
leave bundled-run fields with an ambiguous universe. -/
abbrev SailInterface : PFunctor.{0, 0} := PFunctor.linear (Option SailState)

/-- `try_step` as PolyFun's extensible bundled-machine substrate.  Halting is deliberately a separate
semantic predicate (`SP1Halted`), not failure of the interpreter. -/
noncomputable def sailMachine : PFunctor.DynSystem.Machine SailInterface where
  State := Option SailState
  toDynSystem := PFunctor.DynSystem.mk' id fun state _ => state.bind stepOnce

/-- The unique run selected by the unit direction at every step. -/
noncomputable def sailRun {model : SP1MachineModel} (ctx : ExecutionCtx model) :
    PFunctor.DynSystem.Run sailMachine.toDynSystem where
  state := trajectory ctx.initial
  dir _ := PUnit.unit
  next_state _ := rfl

@[simp] theorem sailRun_state {model : SP1MachineModel} (ctx : ExecutionCtx model) (n : ℕ) :
    (sailRun ctx).state n = trajectory ctx.initial n := rfl

@[simp] theorem sailRun_initial {model : SP1MachineModel} (ctx : ExecutionCtx model) :
    (sailRun ctx).initial = some ctx.initial := rfl

/-- The schedule fixed by the machine model at step `n`.  The ordinary schedule is used only to
totalize the definition after an interpreter failure; a valid execution witness reaches `some` at
its endpoint, hence never observes that fallback before the endpoint. -/
noncomputable def scheduleAt {model : SP1MachineModel} (ctx : ExecutionCtx model) (n : ℕ) :
    StepSchedule :=
  match trajectory ctx.initial n with
  | some state => model.schedule ctx.program state
  | none => ordinarySchedule

/-- Absolute interaction clock at the start of a semantic step.  Unlike the legacy `/ 8` model this
supports opcode- and syscall-dependent windows. -/
noncomputable def executionClock {model : SP1MachineModel} (ctx : ExecutionCtx model)
    (initialClock step : ℕ) : ℕ :=
  clockAt initialClock (scheduleAt ctx) step

/-- The semantic context of one AIR shard.  Unlike `ExecutionCtx`, its initial state is the public
start of this shard rather than the model-selected boot state.  The context carries only invariants
that a local step proof needs; reachability from boot is deliberately a separate composition fact. -/
structure LocalExecutionCtx (model : SP1MachineModel) where
  program : GuestProgram
  wellFormed : program.WellFormed
  initial : SailState
  romLoaded : RomLoaded program initial
  configured : SailConfigured initial

/-- The schedule selected from a shard-local initial state. -/
noncomputable def localScheduleAt {model : SP1MachineModel} (ctx : LocalExecutionCtx model) (n : ℕ) :
    StepSchedule :=
  match trajectory ctx.initial n with
  | some state => model.schedule ctx.program state
  | none => ordinarySchedule

/-- Absolute interaction clock inside a shard-local execution. -/
noncomputable def localExecutionClock {model : SP1MachineModel} (ctx : LocalExecutionCtx model)
    (initialClock step : ℕ) : ℕ :=
  clockAt initialClock (localScheduleAt ctx) step

/-- On the currently supported ordinary-instruction slice, the model schedule reduces the local
clock to the familiar eight-tick formula.  This is a theorem about a selected machine model, not a
definition baked into Sail execution. -/
theorem localExecutionClock_eq_ordinary {model : SP1MachineModel}
    (ordinary : model.UsesOrdinarySchedule) (ctx : LocalExecutionCtx model)
    (initialClock step : ℕ) :
    localExecutionClock ctx initialClock step = initialClock + 8 * step := by
  unfold localExecutionClock
  have schedules : localScheduleAt ctx = fun _ => ordinarySchedule := by
    funext n
    unfold localScheduleAt
    split
    exacts [ordinary ctx.program _, rfl]
  rw [schedules, clockAt_ordinary]

/-- Once a shard-local initial state is located in a canonical trajectory, every later local state is
the corresponding canonical state. -/
theorem trajectory_from_reached {model : SP1MachineModel} {global : ExecutionCtx model}
    {shard : LocalExecutionCtx model} {startStep : ℕ}
    (initialReached : trajectory global.initial startStep = some shard.initial) (n : ℕ) :
    trajectory global.initial (startStep + n) = trajectory shard.initial n := by
  rw [trajectory_add, initialReached]; rfl

/-- The local and canonical schedule views agree after anchoring the local initial state. -/
theorem localScheduleAt_eq_scheduleAt {model : SP1MachineModel} {global : ExecutionCtx model}
    {shard : LocalExecutionCtx model} {startStep : ℕ}
    (program_eq : shard.program = global.program)
    (initialReached : trajectory global.initial startStep = some shard.initial) (n : ℕ) :
    localScheduleAt shard n = scheduleAt global (startStep + n) := by
  unfold localScheduleAt scheduleAt
  rw [trajectory_from_reached initialReached]
  split <;> simp_all

/-- A successful local Sail segment beginning at the state committed by a shard's initial boundary. -/
structure LocalExecutionSegmentWitness {model : SP1MachineModel} (ctx : LocalExecutionCtx model) where
  steps : ℕ
  finalState : SailState
  reached : trajectory ctx.initial steps = some finalState

/-- Clock at an offset inside a local segment. -/
noncomputable def LocalExecutionSegmentWitness.clockAt {model : SP1MachineModel}
    {ctx : LocalExecutionCtx model} (_execution : LocalExecutionSegmentWitness ctx)
    (initialClock offset : ℕ) : ℕ :=
  localExecutionClock ctx initialClock offset

/-- A finite, successful prefix of the official Sail execution.  This is the semantic target of a
whole execution before the terminal condition is imposed. -/
structure PrefixExecutionWitness {model : SP1MachineModel} (ctx : ExecutionCtx model) where
  steps : ℕ
  finalState : SailState
  reached : (sailRun ctx).state steps = some finalState

/-- A finite segment of the canonical execution.  AIR shards and the current supported-core ensemble
commit two State endpoints that need not include boot or halt, so their honest target is an interval
of the one global Sail run rather than a fresh run beginning at `pc_start`. -/
structure ExecutionSegmentWitness {model : SP1MachineModel} (ctx : ExecutionCtx model) where
  startStep : ℕ
  steps : ℕ
  initialState : SailState
  finalState : SailState
  initialReached : (sailRun ctx).state startStep = some initialState
  finalReached : (sailRun ctx).state (startStep + steps) = some finalState

/-- Clock at an offset inside an execution segment, using the segment's public initial clock. -/
noncomputable def ExecutionSegmentWitness.clockAt {model : SP1MachineModel}
    {ctx : ExecutionCtx model} (execution : ExecutionSegmentWitness ctx)
    (initialClock offset : ℕ) : ℕ :=
  SP1Clean.Machine.clockAt initialClock
    (fun n => scheduleAt ctx (execution.startStep + n)) offset

/-- Anchor a local AIR segment in the canonical boot run once the shard's initial state is known to
occur there.  The program equality is explicit so the result cannot splice trajectories belonging to
different committed programs. -/
def LocalExecutionSegmentWitness.anchor {model : SP1MachineModel}
    {global : ExecutionCtx model} {shard : LocalExecutionCtx model}
    (execution : LocalExecutionSegmentWitness shard) (startStep : ℕ)
    (_program_eq : shard.program = global.program)
    (initialReached : trajectory global.initial startStep = some shard.initial) :
    ExecutionSegmentWitness global where
  startStep := startStep
  steps := execution.steps
  initialState := shard.initial
  finalState := execution.finalState
  initialReached := initialReached
  finalReached := by
    change trajectory global.initial (startStep + execution.steps) = some execution.finalState
    rw [trajectory_add, initialReached]; exact execution.reached

/-- Anchoring preserves the shard's schedule-derived clock. -/
theorem LocalExecutionSegmentWitness.clockAt_anchor {model : SP1MachineModel}
    {global : ExecutionCtx model} {shard : LocalExecutionCtx model}
    (execution : LocalExecutionSegmentWitness shard) (startStep : ℕ)
    (program_eq : shard.program = global.program)
    (initialReached : trajectory global.initial startStep = some shard.initial)
    (initialClock offset : ℕ) :
    (execution.anchor startStep program_eq initialReached).clockAt initialClock offset =
      execution.clockAt initialClock offset := by
  unfold ExecutionSegmentWitness.clockAt LocalExecutionSegmentWitness.clockAt localExecutionClock
  congr 1
  funext n
  exact (localScheduleAt_eq_scheduleAt program_eq initialReached n).symm

/-- A finite execution prefix whose endpoint is SP1's halting ECALL with the claimed exit code.  This
belongs at the composed-execution boundary, not at every shard or partial-chip AIR boundary. -/
structure HaltedExecutionWitness {model : SP1MachineModel} (ctx : ExecutionCtx model)
    (exitCode : ℕ) extends PrefixExecutionWitness ctx where
  halted : SP1Halted ctx.program exitCode finalState

/-- Closed carrier for a finite successful prefix. -/
structure ClosedPrefixExecutionWitness (model : SP1MachineModel) where
  context : ExecutionCtx model
  execution : PrefixExecutionWitness context

/-- Closed carrier for one finite segment of the canonical execution. -/
structure ClosedExecutionSegmentWitness (model : SP1MachineModel) where
  context : ExecutionCtx model
  execution : ExecutionSegmentWitness context

/-- Closed carrier for a shard-local execution segment. -/
structure ClosedLocalExecutionSegmentWitness (model : SP1MachineModel) where
  context : LocalExecutionCtx model
  execution : LocalExecutionSegmentWitness context

/-- Closed carrier for a complete execution ending at the halting ECALL. -/
structure ClosedHaltedExecutionWitness (model : SP1MachineModel) where
  context : ExecutionCtx model
  exitCode : ℕ
  execution : HaltedExecutionWitness context exitCode

end SP1Clean.Machine
