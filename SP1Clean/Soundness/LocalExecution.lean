import SP1Clean.Soundness.ChipRegistry
import SP1Clean.FormalModel.SupportedShard
import SP1Clean.Model.Semantics.MicroTime
import SP1Clean.Model.Semantics.GenericTruth
import SP1Clean.Soundness.Walk

/-! # Ordered grounded rows produce a local Sail execution

This is the semantic engine above channel/timing grounding and below the AIR capstone.  Its premises
contain row-local facts—registered chip, `Spec`, committed decode, current operands, and
`advanceReady`—but no next state or execution witness.  Each next state is constructed by the chip's
verified `advance` theorem.
-/

open LeanRV64D.Defs

namespace SP1Clean.Soundness

open Sail LeanRV64D
open SP1Clean.Execution
open SP1Clean.Soundness.Target

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

universe u

/-- The pc projection of an ordered State-bus trail.  `Row` deliberately remains generic: the
production path retains each `DecodedInstructionRow` (and therefore its physical circuit row) until
local soundness has fired, while this engine observes only its semantic `ChipRow` projection. -/
def PcWalk {Row : Type u} (rowOf : Row → ChipRow p) : BitVec 64 → BitVec 64 → List Row → Prop
  | initial, final, [] => initial = final
  | initial, final, row :: rest =>
      rcvPcOf (stateAccess (rowOf row).view) = initial ∧
        PcWalk rowOf (sndPcOf (stateAccess (rowOf row).view)) final rest

/-- The pc edge of one row: what the State bus says it receives, and what it sends. -/
def pcEdgeOf {Row : Type u} (rowOf : Row → ChipRow p) (row : Row) : BitVec 64 × BitVec 64 :=
  (rcvPcOf (stateAccess (rowOf row).view), sndPcOf (stateAccess (rowOf row).view))

/-- `PcWalk` **is** the generic `Walk.IsWalk` at the pc edge — the two have the same nil (`a = b`)
and cons (`(edge x).1 = a ∧ …`) shapes, so this holds by `Iff.rfl` at every position.

Stating the identity is worth a lemma for two reasons.  It makes `Walk.isWalk_append`,
`isWalk_map` and `isWalk_forall₂` available to the pc walk — the halt branch is literally a
`prefix ++ [one row]` walk, which is `isWalk_append`.  And it is the generalization a syscall row
needs: a row with no `ChipRow` still has a pc edge, so the mixed engine walks `Walk.IsWalk` at an
edge built from `RowFacts` (`statePullMessage_pcBits`/`statePushMessage_pcBits`) while every
existing consumer keeps its `PcWalk rowOf` spelling unchanged. -/
theorem pcWalk_iff_isWalk {Row : Type u} (rowOf : Row → ChipRow p)
    (initial final : BitVec 64) (rows : List Row) :
    PcWalk rowOf initial final rows ↔ Walk.IsWalk (pcEdgeOf rowOf) initial final rows := by
  induction rows generalizing initial with
  | nil => exact Iff.rfl
  | cons row rest ih => exact and_congr Iff.rfl (ih _)

/-- State-independent facts about one active decoded row.  These come from deterministic witness
decoding, the chip registry, and Program-channel grounding; they do not belong to the evolving-state
induction. -/
structure StaticGroundedRow (program : GuestProgram) (row : ChipRow p) : Prop where
  real : row.is_real = 1
  registered : row.kind ∈ allChipKinds (p := p)
  decoded : decodedInROM program (programAccess row.view).toRow

/-- Facts about one row that depend on the current official-Sail state.  In particular, the proof of
the row's `chipSpec` is dynamic even though the proposition itself does not mention `state`: many chip
soundness assumptions are discharged from register/Memory values that are current only at this
execution position.  The timed Memory engine and per-chip readiness contracts supply these facts. -/
structure DynamicGroundedRow (data : ProverData (ZMod p)) (program : GuestProgram)
    (row : ChipRow p) (state : SailState) : Prop where
  spec : row.chipSpec data
  ready : row.kind.advanceReady row.inputs row.cols program state
  operands : ValueOperandsBound row.view state

/-- Everything needed to fire one registered chip row in the current semantic state. -/
structure GroundedRow (data : ProverData (ZMod p)) (program : GuestProgram)
    (row : ChipRow p) (state : SailState) extends
    StaticGroundedRow program row, DynamicGroundedRow data program row state

/-- Position-indexed grounding for an ordered list of row labels.  The labels stay generic so a
caller can retain a physical decoded circuit row while this semantic engine reads only `rowOf`.
Static facts are stated once per member; only operand currency and readiness are indexed by
execution position.

The position index is a **trajectory**, not a `SailChain`.  `DynamicGroundedRow` never mentions a
chain — only the quantifier in front of it did — and `sailTrajectory_eq_some_iff` is already proved
in both directions, so `SailChain done.length initial state` is recovered verbatim at
`Semantics.sailTrajectory initial` and no consumer changes.  What the generalization buys is a
position index a 264-tick syscall row can also occupy: `eventTrajectory` counts *steps*, so a row's
duration never enters here (it enters the clock, which is a separate axis). -/
structure RowsGrounded {Row : Type u} (rowOf : Row → ChipRow p)
    (data : ProverData (ZMod p)) (program : GuestProgram)
    (traj : Semantics.Trajectory) (rows : List Row) : Prop where
  static : ∀ row ∈ rows, StaticGroundedRow program (rowOf row)
  dynamic : ∀ done row suffix, rows = done ++ row :: suffix →
    ∀ state, traj done.length = some state → DynamicGroundedRow data program (rowOf row) state

/-- Recombine the static and position-dependent layers at one execution position. -/
theorem RowsGrounded.at {Row : Type u} {rowOf : Row → ChipRow p}
    {data : ProverData (ZMod p)} {program : GuestProgram}
    {traj : Semantics.Trajectory} {rows : List Row}
    (grounded : RowsGrounded rowOf data program traj rows)
    (done : List Row) (row : Row) (suffix : List Row)
    (rowsEq : rows = done ++ row :: suffix) (state : SailState)
    (position : traj done.length = some state) :
    GroundedRow data program (rowOf row) state := by
  refine { toStaticGroundedRow := grounded.static row ?_
           toDynamicGroundedRow := grounded.dynamic done row suffix rowsEq state position }
  rw [rowsEq]
  simp

/-- Fire one grounded row through its registered `ChipKind.advance`. -/
theorem GroundedRow.advance {data : ProverData (ZMod p)} {program : GuestProgram}
    {row : ChipRow p} {state : SailState} (grounded : GroundedRow data program row state)
    (configured : SailConfigured state) (romLoaded : RomLoaded program state)
    (pc : state.regs.get? Register.PC = some (rcvPcOf (stateAccess row.view))) :
    ∃ next, SailStep state next ∧ RowEffect program row.view state next := by
  have migrated : row.kind.advance.isSome = true :=
    allChipKinds_migrated row.kind grounded.registered
  obtain ⟨advance, -⟩ := Option.isSome_iff_exists.mp migrated
  exact advance.down row.inputs row.cols data program state grounded.real grounded.spec
    configured romLoaded pc grounded.operands grounded.decoded grounded.ready

/-- A grounded row exposes the one shared SP1 transition view required by the ordinary-shard
relation. The Program and State pc keys are definitionally the same three row limbs; guarded
Program grounding proves the decoder-image check, and the access-plan attempt is retained exactly
without being assumed successful. -/
theorem GroundedRow.supportedSP1Transition
    {data : ProverData (ZMod p)} {program : GuestProgram}
    {row : ChipRow p} {state next : SailState}
    (grounded : GroundedRow data program row state)
    (normal : SailRetiresNormally state next)
    (configured : SailConfigured state)
    (pc : state.regs.get? Register.PC = some (rcvPcOf (stateAccess row.view))) :
    SupportedSP1Transition program
      ⟨state, ⟨Machine.ExecutionEvent.ordinary, next⟩⟩ := by
  obtain ⟨word, instruction, fetch, decoded, projection⟩ := grounded.decoded
  have image := instructionImageOK_of_instrToProgramRow'_some projection
  obtain ⟨key, chipId, keyEq, routeEq⟩ := instrToProgramRow'_route_exists projection
  let view : SP1Clean.Semantics.SP1TransitionView :=
    { pc := rcvPcOf (stateAccess row.view)
      word := word
      decoded := instruction
      routeKey := key
      chipId := chipId
      accessPlan? := SP1Clean.Semantics.instructionAccessPlan? instruction state next }
  have decodeEq : SP1Clean.Semantics.decodeLocated? program
      ⟨state, ⟨Machine.ExecutionEvent.ordinary, next⟩⟩ = some instruction :=
    SP1Clean.Semantics.decodeLocated?_eq_some_of pc fetch (decoded state configured)
  have fetch' : program.fetchWord (rcvPcOf (stateAccess row.view)) = some word := fetch
  have projected : SP1Clean.Semantics.projectSP1Transition? program
      ⟨state, ⟨Machine.ExecutionEvent.ordinary, next⟩⟩ = some view := by
    simp [SP1Clean.Semantics.projectSP1Transition?, view, pc, fetch', decodeEq, image, keyEq,
      routeEq]
  exact ⟨rfl, normal, configured, view, projected, decoded⟩

/-- Ordinary events impose no carried timestamp, so an all-ordinary proof-free transition list is
clocked from every initial clock. -/
private theorem ordinaryTransitions_clocked :
    ∀ (transitions : List Machine.EventTransition) (clock : ℕ),
      (∀ transition ∈ transitions, transition.event = .ordinary) →
      Machine.EventTransitionsClocked clock transitions := by
  intro transitions clock ordinary
  induction transitions generalizing clock with
  | nil => trivial
  | cons transition rest ih =>
      have head : transition.event = .ordinary := ordinary transition (by simp)
      have tail : ∀ item ∈ rest, item.event = .ordinary :=
        fun item itemMem => ordinary item (by simp [itemMem])
      rcases transition with ⟨event, target⟩
      simp only at head
      subst event
      exact ⟨trivial, ih _ tail⟩

/-- The event clock after a transition list is the prefix sum of that list's own event durations.

No ordinary hypothesis: this is plain `clockAfterEvents` telescoping, and it is the form a mixed
timeline needs, where an ordinary row spends 8 ticks and a syscall row 264.  The eight-tick
`ordinaryTransitions_finalClock` below is this theorem composed with
`ordinaryTransitions_durationSum`. -/
theorem transitions_finalClock :
    ∀ (transitions : List Machine.EventTransition) (clock : ℕ),
      Machine.clockAfterEvents clock (transitions.map Machine.EventTransition.event) =
        clock + (transitions.map fun transition => transition.event.duration).sum := by
  intro transitions
  induction transitions with
  | nil => intro clock; simp [Machine.clockAfterEvents]
  | cons transition rest ih =>
      intro clock
      simp only [List.map_cons, Machine.clockAfterEvents, List.foldl_cons, List.sum_cons]
      change Machine.clockAfterEvents (clock + transition.event.duration)
          (rest.map Machine.EventTransition.event) =
        clock + (transition.event.duration +
          (rest.map fun item => item.event.duration).sum)
      rw [ih _]
      omega

/-- An all-ordinary transition list's durations sum to the eight-tick step count. -/
private theorem ordinaryTransitions_durationSum :
    ∀ (transitions : List Machine.EventTransition),
      (∀ transition ∈ transitions, transition.event = .ordinary) →
      (transitions.map fun transition => transition.event.duration).sum =
        8 * transitions.length := by
  intro transitions
  induction transitions with
  | nil => intro _; simp
  | cons transition rest ih =>
      intro ordinary
      have head : transition.event = .ordinary := ordinary transition (by simp)
      have tail : ∀ item ∈ rest, item.event = .ordinary :=
        fun item itemMem => ordinary item (by simp [itemMem])
      simp only [List.map_cons, List.sum_cons, List.length_cons, head,
        Machine.ExecutionEvent.duration_ordinary]
      rw [ih tail]
      omega

/-- The ordinary eight-tick schedule makes the final event clock a simple step count. -/
private theorem ordinaryTransitions_finalClock :
    ∀ (transitions : List Machine.EventTransition) (clock : ℕ),
      (∀ transition ∈ transitions, transition.event = .ordinary) →
      Machine.clockAfterEvents clock (transitions.map Machine.EventTransition.event) =
        clock + 8 * transitions.length := by
  intro transitions clock ordinary
  rw [transitions_finalClock, ordinaryTransitions_durationSum transitions ordinary]

/-- Execute the unprocessed suffix of a pc walk, retaining the already-executed prefix only as an
index into `RowsGrounded`. -/
private theorem executePcWalkAux {Row : Type u}
    (rowOf : Row → ChipRow p)
    (data : ProverData (ZMod p)) (program : GuestProgram) (initial : SailState)
    (rows : List Row) (grounded : RowsGrounded rowOf data program (Semantics.sailTrajectory initial) rows)
    (codeMemoryCompatible : SailCodeMemoryCompatible program initial) :
    ∀ (done suffix : List Row) (current final : BitVec 64) (state : SailState),
      rows = done ++ suffix →
      PcWalk rowOf current final suffix →
      SailRetireChain done.length initial state →
      state.regs.get? Register.PC = some current →
      RomLoaded program state → SailConfigured state →
      ∃ finalState,
        SailRetireChain rows.length initial finalState ∧
        finalState.regs.get? Register.PC = some final := by
  intro done suffix
  induction suffix generalizing done with
  | nil =>
      intro current final state rows_eq walk chain pc _ _
      have current_eq : current = final := walk
      refine ⟨state, ?_, by simpa [current_eq] using pc⟩
      simpa [rows_eq] using chain
  | cons row suffix ih =>
      intro current final state rows_eq walk chain pc rom cfg
      obtain ⟨rowSource, tailWalk⟩ := walk
      have pcRow : state.regs.get? Register.PC =
          some (rcvPcOf (stateAccess (rowOf row).view)) := by
        rw [rowSource]
        exact pc
      have rowGrounded := grounded.at done row suffix rows_eq state
        (Semantics.sailTrajectory_eq_some_iff.mpr chain.toSailChain)
      obtain ⟨next, step, effect⟩ := rowGrounded.advance cfg rom pcRow
      have rows_eq' : rows = (done ++ [row]) ++ suffix := by
        simpa [List.append_assoc] using rows_eq
      have chain' : SailRetireChain (done ++ [row]).length initial next := by
        simpa using chain.snoc effect.normal
      have nextRom : RomLoaded program next :=
        codeMemoryCompatible chain.toSailChain step rom
      exact ih (done ++ [row]) (sndPcOf (stateAccess (rowOf row).view)) final next rows_eq'
        tailWalk chain' effect.pc nextRom (effect.cfg cfg)

/-- A fully grounded, ordered row list constructs a genuine local official-Sail chain in which
every step retires normally.  Downgrade with `SailRetireChain.toSailChain` where only step
completion is needed. -/
theorem sailRetireChain_of_groundedRows {Row : Type u} (rowOf : Row → ChipRow p)
    (data : ProverData (ZMod p)) (program : GuestProgram) (initial : SailState)
    (rows : List Row) (initialPc finalPc : BitVec 64)
    (walk : PcWalk rowOf initialPc finalPc rows)
    (grounded : RowsGrounded rowOf data program (Semantics.sailTrajectory initial) rows)
    (codeMemoryCompatible : SailCodeMemoryCompatible program initial)
    (pc : initial.regs.get? Register.PC = some initialPc)
    (rom : RomLoaded program initial) (cfg : SailConfigured initial) :
    ∃ finalState,
      SailRetireChain rows.length initial finalState ∧
      finalState.regs.get? Register.PC = some finalPc := by
  simpa using executePcWalkAux rowOf data program initial rows grounded codeMemoryCompatible
    [] rows initialPc finalPc initial (by simp) walk (.refl initial) pc rom cfg

/-! ## The row-generic execution engine

The eight-tick engine below *constructs* its own position index (`chain.snoc`).  A mixed walk cannot
do that: a syscall step is not a `SailStep`, so nothing lets the engine extend the trajectory itself.
The generic engine therefore **consumes** its index — each row's own advance obligation hands back
`traj (k + 1)` — and stays generic in the row type, because this file sits below the entire syscall
campaign in the import order and so cannot mention a mixed row type. -/

/-- What each row of a walk owes the engine at its own position.

Everything the engine cannot derive from a bare row type lives here: the row's own semantic step,
the trajectory's next value, the outgoing pc / ROM / configuration facts, and — on the ordinary arm
only — the instruction-routing obligation.  A caller discharges this per arm: `GroundedRow.advance`
for an ordinary row, the syscall row's own payload for a `.syscall` one.  The routing obligation is
guarded because `SupportedSP1Transition` *begins* with `event = .ordinary`; a syscall transition's
meaning travels in `Machine.EventStep.syscall` instead. -/
def WalkAdvancesAt {Row : Type u} (handler : Machine.SyscallHandler) (program : GuestProgram)
    (eventOf : Row → Machine.ExecutionEvent) (edge : Row → BitVec 64 × BitVec 64)
    (traj : Semantics.Trajectory) (rows : List Row) : Prop :=
  ∀ done row suffix, rows = done ++ row :: suffix →
    ∀ state, traj done.length = some state →
      state.regs.get? Register.PC = some (edge row).1 →
      RomLoaded program state → SailConfigured state →
      ∃ next : SailState,
        traj (done.length + 1) = some next ∧
        Machine.EventStep handler program state (eventOf row) next ∧
        next.regs.get? Register.PC = some (edge row).2 ∧
        RomLoaded program next ∧ SailConfigured next ∧
        (eventOf row = .ordinary →
          SupportedSP1Transition program ⟨state, ⟨eventOf row, next⟩⟩)

/-- Execute the unprocessed suffix of a walk into the proof-free event-trace carrier.

The event list is reported as `suffix.map eventOf` rather than as a step count.  That single
equation carries the length, the per-row durations — so the clock is a prefix sum — and, when every
row is ordinary, `AllOrdinary` too; the eight-tick engine had to state all three separately. -/
private theorem executeWalkEventsAux {Row : Type u}
    (handler : Machine.SyscallHandler) (program : GuestProgram)
    (eventOf : Row → Machine.ExecutionEvent) (edge : Row → BitVec 64 × BitVec 64)
    (traj : Semantics.Trajectory) (rows : List Row)
    (advances : WalkAdvancesAt handler program eventOf edge traj rows) :
    ∀ (done suffix : List Row) (current final : BitVec 64) (state : SailState),
      rows = done ++ suffix →
      Walk.IsWalk edge current final suffix →
      traj done.length = some state →
      state.regs.get? Register.PC = some current →
      RomLoaded program state → SailConfigured state →
      ∃ execution : Machine.EventExecutionTrace,
        execution.initialState = state ∧
        execution.events = suffix.map eventOf ∧
        execution.finalState.regs.get? Register.PC = some final ∧
        execution.Valid handler program ∧
        AllTransitionsSupported program execution := by
  intro done suffix
  induction suffix generalizing done with
  | nil =>
      intro current final state rowsEq walk position pc rom cfg
      have currentEq : current = final := walk
      refine ⟨⟨state, []⟩, rfl, rfl, ?_, ?_, ?_⟩
      · simpa [Machine.EventExecutionTrace.finalState, Machine.stateAfterTransitions, currentEq]
          using pc
      · exact .nil state
      · intro located locatedMem
        simp [Machine.EventExecutionTrace.locatedTransitions, Machine.locateTransitions]
          at locatedMem
  | cons row suffix ih =>
      intro current final state rowsEq walk position pc rom cfg
      obtain ⟨rowSource, tailWalk⟩ := walk
      have pcRow : state.regs.get? Register.PC = some (edge row).1 := by
        rw [rowSource]
        exact pc
      obtain ⟨next, nextPosition, step, nextPc, nextRom, nextCfg, headSupported⟩ :=
        advances done row suffix rowsEq state position pcRow rom cfg
      have rowsEq' : rows = (done ++ [row]) ++ suffix := by
        simpa [List.append_assoc] using rowsEq
      have nextPosition' : traj (done ++ [row]).length = some next := by
        simpa using nextPosition
      obtain ⟨tailExecution, tailInitial, tailEvents, tailFinal, tailValid, tailSupported⟩ :=
        ih (done ++ [row]) (edge row).2 final next rowsEq' tailWalk nextPosition' nextPc
          nextRom nextCfg
      let head : Machine.EventTransition := ⟨eventOf row, next⟩
      let execution : Machine.EventExecutionTrace :=
        ⟨state, head :: tailExecution.transitions⟩
      refine ⟨execution, rfl, ?_, ?_, ?_, ?_⟩
      · have tailMap : tailExecution.transitions.map Machine.EventTransition.event =
            suffix.map eventOf := tailEvents
        simp only [execution, head, Machine.EventExecutionTrace.events, List.map_cons, tailMap]
      · simpa [execution, Machine.EventExecutionTrace.finalState,
          Machine.stateAfterTransitions, tailInitial] using tailFinal
      · refine .cons head step ?_
        change Machine.EventTransitionsValid handler program next tailExecution.transitions
        rw [← tailInitial]
        exact tailValid
      · intro located locatedMem
        simp only [execution, Machine.EventExecutionTrace.locatedTransitions,
          Machine.locateTransitions, List.mem_cons] at locatedMem
        rcases locatedMem with rfl | locatedMem
        · exact headSupported
        · intro rowOrdinary
          refine tailSupported _ ?_ rowOrdinary
          simpa [Machine.EventExecutionTrace.locatedTransitions, tailInitial] using locatedMem

/-- A walk whose every row can advance produces that walk's own proof-free event trace.

The public entry point to the engine: `executeWalkEventsAux` specialized from its suffix-indexed
form to the whole row list. -/
theorem walkExecution_of_advances {Row : Type u}
    (handler : Machine.SyscallHandler) (program : GuestProgram)
    (eventOf : Row → Machine.ExecutionEvent) (edge : Row → BitVec 64 × BitVec 64)
    (traj : Semantics.Trajectory) (rows : List Row) (initial : SailState)
    (initialPc finalPc : BitVec 64)
    (advances : WalkAdvancesAt handler program eventOf edge traj rows)
    (walk : Walk.IsWalk edge initialPc finalPc rows)
    (genesis : traj 0 = some initial)
    (pc : initial.regs.get? Register.PC = some initialPc)
    (rom : RomLoaded program initial) (cfg : SailConfigured initial) :
    ∃ execution : Machine.EventExecutionTrace,
      execution.initialState = initial ∧
      execution.events = rows.map eventOf ∧
      execution.finalState.regs.get? Register.PC = some finalPc ∧
      execution.Valid handler program ∧
      AllTransitionsSupported program execution :=
  executeWalkEventsAux handler program eventOf edge traj rows advances [] rows initialPc finalPc
    initial (by simp) walk (by simpa using genesis) pc rom cfg

/-- A fully grounded ordered row list constructs one exact proof-free ordinary event trace.  Its
validity is the official event-step relation, its transition order is the row order, every decode
retains a canonical instruction-chip route, and the ordinary schedule gives the exact eight-tick
clock count. -/
theorem eventExecution_of_groundedRows {Row : Type u}
    (handler : Machine.SyscallHandler) (rowOf : Row → ChipRow p)
    (data : ProverData (ZMod p)) (program : GuestProgram) (initial : SailState)
    (rows : List Row) (initialPc finalPc : BitVec 64)
    (walk : PcWalk rowOf initialPc finalPc rows)
    (grounded : RowsGrounded rowOf data program (Semantics.sailTrajectory initial) rows)
    (codeMemoryCompatible : SailCodeMemoryCompatible program initial)
    (pc : initial.regs.get? Register.PC = some initialPc)
    (rom : RomLoaded program initial) (cfg : SailConfigured initial) (initialClock : ℕ) :
    ∃ execution : Machine.EventExecutionTrace,
      execution.initialState = initial ∧
      execution.steps = rows.length ∧
      execution.finalState.regs.get? Register.PC = some finalPc ∧
      execution.Valid handler program ∧
      execution.Clocked initialClock ∧
      execution.finalClock initialClock = initialClock + 8 * rows.length ∧
      execution.AllOrdinary ∧
      AllTransitionsSupported program execution := by
  -- The ordinary arm of the generic engine: every row is `.ordinary`, the position index is the
  -- Sail trajectory, and the pc edge is the row's own `ChipRow` projection.
  have advances : WalkAdvancesAt handler program (fun _ => Machine.ExecutionEvent.ordinary)
      (pcEdgeOf rowOf) (Semantics.sailTrajectory initial) rows := by
    intro done row suffix rowsEq state position pcRow romState cfgState
    simp only [pcEdgeOf] at pcRow
    have chain := Semantics.sailTrajectory_eq_some_iff.mp position
    have rowGrounded := grounded.at done row suffix rowsEq state position
    obtain ⟨next, step, effect⟩ := rowGrounded.advance cfgState romState pcRow
    have headSupported := rowGrounded.supportedSP1Transition effect.normal cfgState pcRow
    exact ⟨next, Semantics.sailTrajectory_eq_some_iff.mpr (chain.snoc step),
      .ordinary headSupported.notAboutToExecuteEcall step, effect.pc,
      codeMemoryCompatible chain step romState, effect.cfg cfgState, fun _ => headSupported⟩
  obtain ⟨execution, initialEq, events, finalEq, valid, supported⟩ :=
    walkExecution_of_advances handler program (fun _ => Machine.ExecutionEvent.ordinary)
      (pcEdgeOf rowOf) (Semantics.sailTrajectory initial) rows initial initialPc finalPc advances
      ((pcWalk_iff_isWalk rowOf initialPc finalPc rows).mp walk)
      (Semantics.sailTrajectory_eq_some_iff.mpr (by simpa using Target.SailChain.refl initial))
      pc rom cfg
  -- The single event equation recovers all three facts the eight-tick engine stated separately.
  have ordinary : execution.AllOrdinary := by
    intro transition transitionMem
    have member : transition.event ∈ execution.events := List.mem_map_of_mem transitionMem
    rw [events] at member
    obtain ⟨_, -, headEq⟩ := List.mem_map.mp member
    exact headEq.symm
  have stepsEq : execution.steps = rows.length := by
    simpa [Machine.EventExecutionTrace.events, Machine.EventExecutionTrace.steps] using
      congrArg List.length events
  refine ⟨execution, initialEq, stepsEq, finalEq, valid,
    ordinaryTransitions_clocked execution.transitions initialClock ordinary, ?_, ordinary, supported⟩
  change Machine.clockAfterEvents initialClock
      (execution.transitions.map Machine.EventTransition.event) = initialClock + 8 * rows.length
  rw [ordinaryTransitions_finalClock execution.transitions initialClock ordinary]
  change execution.transitions.length = rows.length at stepsEq
  rw [stepsEq]

/-- Package the grounded-row engine as the plain-Sail relation: no machine-model parameter, and
the clock claim is the literal eight-tick count the 25-chip slice implements.  The caller
supplies the populated Memory boundary and its two validity facts; agreement with the final
state is taken conditionally on the constructed chain endpoint, which this theorem produces. -/
theorem groundedRows_sailRelation {Row : Type u}
    (statement : ProgramStatement (SupportedCorePrefixPublicValues (ZMod p)))
    (data : ProverData (ZMod p)) (initial : SailState)
    (rowOf : Row → ChipRow p) (rows : List Row)
    (memory : Machine.CoreMemoryBoundary)
    (wellFormed : statement.program.WellFormed)
    (pc : initial.regs.get? Register.PC = some statement.initPcBits)
    (rom : RomLoaded statement.program initial) (cfg : SailConfigured initial)
    (codeMemoryCompatible : SailCodeMemoryCompatible statement.program initial)
    (walk : PcWalk rowOf statement.initPcBits statement.finalPcBits rows)
    (grounded : RowsGrounded rowOf data statement.program (Semantics.sailTrajectory initial) rows)
    (clockCount : statement.initClkNat + 8 * rows.length = statement.finalClkNat)
    (exitZero : statement.publicValues.exit_code = 0)
    (memoryWellFormed : memory.WellFormed statement.finalClkNat)
    (memoryAgrees : ∀ final, Semantics.chainState initial rows.length = some final →
      memory.AgreesWith initial final) :
    ∃ w, SupportedCoreSailRelation statement w ∧
      SailSegmentWitness.OrdinaryRun statement w := by
  obtain ⟨finalState, chain, finalPc⟩ :=
    sailRetireChain_of_groundedRows rowOf data statement.program initial rows _ _ walk grounded
      codeMemoryCompatible pc rom cfg
  exact ⟨⟨initial, rows.length, finalState, memory⟩,
    ⟨wellFormed, ⟨pc, rom, cfg⟩, memoryWellFormed,
      memoryAgrees finalState (Semantics.chainState_of_sailChain chain.toSailChain),
      Or.inl ⟨chain, finalPc, clockCount.symm, exitZero⟩⟩,
    chain, finalPc, clockCount.symm, exitZero⟩

end SP1Clean.Soundness
