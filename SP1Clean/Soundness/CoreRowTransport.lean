import SP1Clean.Soundness.CoreTouches
import SP1Clean.Soundness.MixedRowTransport
import SP1Clean.Soundness.WalkTimeline

/-! # Shared semantic transport through alignment and refresh rewriting

The transformation preserves each event's fetch and semantic State endpoints, and matches its
reads inside their pre-effect windows. Only equal-value prior records at the same location and an
earlier time may replace the original pulls. These lemmas carry arbitrary trajectory step/frame
facts through the structural transformation; they do not assert host execution.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance coreRowTransportField24 : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance coreRowTransportField17 : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

private theorem syscall_readsInWindow (row : SyscallInstrsChip.Inputs (ZMod p))
    (opB : row.op_b = 10) (opC : row.op_c = 11) : ReadsInWindow (syscallRowFacts row) := by
  have bLoc := (syscallRow_locOf_reg row (i := 10#5)
    (by norm_num; exact opB.symm) row.op_b_memory row.op_b_memory.prev_value 3).1
  have cLoc := (syscallRow_locOf_reg row (i := 11#5)
    (by norm_num; exact opC.symm) row.op_c_memory row.op_c_memory.prev_value 2).1
  intro pull member
  simp only [syscallRowFacts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ⟨le_rfl, Nat.le_add_right _ _⟩
  · simpa only [syscallRowFacts, bLoc, readWindow_reg] using
      (show _ ≤ _ + 3 ∧ _ + 3 ≤ _ + 3 from ⟨Nat.le_add_right _ _, le_rfl⟩)
  · simp only [syscallRowFacts, cLoc, readWindow_reg]
    omega

theorem syscall_readsInWindow_of_committed (row : SyscallInstrsChip.Inputs (ZMod p))
    (program : Target.GuestProgram)
    (committed : Target.committedInROM program (rowOfMsg (SyscallInstrsChip.programMessage row))) :
    ReadsInWindow (syscallRowFacts row) := by
  have shape := (committed.ecall_of_opcode rfl).2
  exact syscall_readsInWindow row
    (congrArg (fun r : ProgramChip.ProgramRow (ZMod p) => r.op_b[0]) shape)
    (congrArg (fun r : ProgramChip.ProgramRow (ZMod p) => r.op_c[0]) shape)

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
/-- Local alignment becomes semantic transport once the original reads' windows and prior
low-clock bounds are known. No global Memory truth is required. -/
theorem AlignedFacts.windowAligned {aligned original : RowFacts p}
    (facts : AlignedFacts aligned original) (reads : ReadsInWindow original)
    (prior : ∀ pull ∈ original.memPulls, MemoryMsg.ClkBound pull.1) :
    WindowAligned aligned original where
  pullTime := congrArg StateMsg.timeNat facts.statePull
  pullPc := congrArg StateMsg.pcBits facts.statePull
  pushTime := congrArg StateMsg.timeNat facts.statePush
  pushPc := congrArg StateMsg.pcBits facts.statePush
  fetch := facts.fetch
  pushes := facts.memory.pushes
  pullClk := prior
  originalReads := reads
  match_ := by
    intro pull member
    have mapped := facts.memory.pulls.mem_iff.mpr (List.mem_map_of_mem member)
    obtain ⟨matched, matchedMem, same⟩ := List.mem_map.mp mapped
    obtain ⟨_, _, touch⟩ := forall₂_exists_right facts.touches matched matchedMem
    exact ⟨matched, matchedMem, congrArg MemoryMsg.locOf same, congrArg (·.value) same,
      touch.read_lo, by rw [← same]; exact touch.read_hi⟩

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
theorem rewritten_core {initialClock : ℕ} {row : RowFacts p} {touches : List (Touch p)}
    (ok : RowOKCore initialClock row)
    (prior : ∀ pull ∈ row.memPulls, MemoryMsg.ClkBound pull.1)
    (rewrite : List.Forall₂ PullRewrite (rowTouches row) touches) :
    RowOKCore initialClock (alignedOf row touches) := by
  refine rowOKCore_alignedOf_pullRewrite initialClock row (rowTouches row) touches rewrite
    ok.timeGap ok.align8 ?_ ok.chain_mono ?_ ?_
  · exact fun touch member => (List.forall₂_iff_zip.mp ok.touches).2 member
  · exact fun touch member => ok.pushClkBound _ (List.of_mem_zip member).2
  · exact fun touch member => ok.slotOfClkBound touch member (prior _ (List.of_mem_zip member).1)

/-- Canonical State messages on a row, independent of its Memory touch representation. -/
noncomputable def canonicalRow (row : RowFacts p) : RowFacts p :=
  stateRespell row (canonState row.statePull) (canonState row.statePush)

/-- Apply each chosen refresh rewrite and normalize the State endpoints, retaining list order. -/
noncomputable def rewrittenRows (rows : List (RowFacts p)) (touches : List (List (Touch p))) :
    List (RowFacts p) :=
  (rows.zip touches).map (fun pair => canonicalRow (alignedOf pair.1 pair.2))

omit [Fact (2 ^ 25 < p)] in
theorem rewriteRows_forall₂ {R : RowFacts p → RowFacts p → Prop}
    {rows originals : List (RowFacts p)} (alignment : List.Forall₂ AlignedFacts rows originals)
    {touches : List (List (Touch p))}
    (rewrite : List.Forall₂ (List.Forall₂ PullRewrite) (rows.map rowTouches) touches)
    (each : ∀ row ∈ rows, ∀ original ∈ originals, ∀ ts,
      AlignedFacts row original → List.Forall₂ PullRewrite (rowTouches row) ts →
        R (canonicalRow (alignedOf row ts)) original) :
    List.Forall₂ R (rewrittenRows rows touches) originals := by
  induction alignment generalizing touches with
  | nil => cases rewrite; exact .nil
  | @cons row original rows originals aligned rest ih =>
    cases rewrite with
    | cons head tail =>
      exact .cons (each row List.mem_cons_self original List.mem_cons_self _ aligned head)
        (ih tail (fun r rMem o oMem ts => each r (List.mem_cons_of_mem _ rMem)
          o (List.mem_cons_of_mem _ oMem) ts))

omit [Fact (2 ^ 25 < p)] in
theorem rewritten_memory (rows : List (RowFacts p)) (touches : List (List (Touch p))) (loc : MemLoc) :
    pushesAt (rewrittenRows rows touches) loc =
      pushesAt ((rows.zip touches).map (fun pair => alignedOf pair.1 pair.2)) loc ∧
    pullsAt (rewrittenRows rows touches) loc =
      pullsAt ((rows.zip touches).map (fun pair => alignedOf pair.1 pair.2)) loc := by
  simp only [rewrittenRows, pushesAt, pullsAt, List.map_map, Function.comp_def, rowPushesAt, rowPullsAt,
    canonicalRow, stateRespell_memPushes, stateRespell_memPulls, and_self]

/-- Canonical edges can be read from the semantic facts without unfolding a physical decoder. -/
theorem ExecutionRow.canonEdge_facts (data : ProverData (ZMod p)) :
    (fun event : ExecutionRow p =>
      (canonState (event.facts data).statePull, canonState (event.facts data).statePush)) =
      ExecutionRow.canonEdge data := by
  funext event
  rw [ExecutionRow.canonEdge, ExecutionRow.edge_eq_facts]

/-- A structural grounding carrier over opaque event and boundary values. Keeping the concrete
ensemble out of the carrier type avoids normalizing the complete source during structure elaboration.
The event facts explicitly include the complete instruction and host Memory footprint. -/
structure ExecutionCarrier (facts : ExecutionRow p → RowFacts p) (events : List (ExecutionRow p))
    (incoming outgoing : StateMsg (ZMod p))
    (initialFrontier physicalFinal : MemLoc → Option (MemoryMsg (ZMod p))) where
  ordered : List (ExecutionRow p)
  rows : List (RowFacts p)
  final : MemLoc → Option (MemoryMsg (ZMod p))
  exhaustive : ordered.Perm events
  aligned : List.Forall₂ WindowAligned rows (ordered.map facts)
  rowOK : ∀ row ∈ rows, RowOKCore (StateMsg.timeNat incoming) row
  stateWalk : Walk.IsWalk (fun row : RowFacts p => (row.statePull, row.statePush))
    incoming outgoing rows
  eventWalk : Walk.IsWalk (fun event =>
    (canonState (facts event).statePull, canonState (facts event).statePush)) incoming outgoing ordered
  memoryBalance : ∀ loc, optMS (initialFrontier loc) + pushesAt rows loc =
    optMS (final loc) + pullsAt rows loc
  finalRewrite : ∀ loc message, physicalFinal loc = some message →
    ∃ earlier, final loc = some earlier ∧ MemoryMsg.locOf earlier = MemoryMsg.locOf message ∧
      earlier.value = message.value ∧ MemoryMsg.timeNat earlier ≤ MemoryMsg.timeNat message

variable {facts : ExecutionRow p → RowFacts p} {events : List (ExecutionRow p)}
  {incoming outgoing : StateMsg (ZMod p)}
  {initialFrontier physicalFinal : MemLoc → Option (MemoryMsg (ZMod p))}

/-- The complete event footprints determine the timeline through their preserved State edges. -/
noncomputable def ExecutionCarrier.timeline
    (carrier : ExecutionCarrier facts events incoming outgoing initialFrontier physicalFinal) : Timeline :=
  rowTimeline (StateMsg.timeNat incoming) carrier.rows (fun row member => (carrier.rowOK row member).timeGap)

theorem ExecutionCarrier.timeline_start
    (carrier : ExecutionCarrier facts events incoming outgoing initialFrontier physicalFinal) :
    carrier.timeline.start 0 = StateMsg.timeNat incoming := rowTimeline_start _ _ _

theorem ExecutionCarrier.timeStep
    (carrier : ExecutionCarrier facts events incoming outgoing initialFrontier physicalFinal) :
    ∀ row ∈ carrier.rows, ∀ n, StateMsg.timeNat row.statePull = carrier.timeline.start n →
      StateMsg.timeNat row.statePush = carrier.timeline.start (n + 1) :=
  rowTimeline_step_of_walk carrier.stateWalk _

theorem ExecutionCarrier.finalClock
    (carrier : ExecutionCarrier facts events incoming outgoing initialFrontier physicalFinal) :
    carrier.timeline.start carrier.rows.length = StateMsg.timeNat outgoing :=
  rowTimeline_end_of_walk carrier.stateWalk _

theorem ExecutionCarrier.stateBalance
    (carrier : ExecutionCarrier facts events incoming outgoing initialFrontier physicalFinal) :
    incoming ::ₘ (↑(carrier.rows.map (·.statePush)) : Multiset (StateMsg (ZMod p))) =
      outgoing ::ₘ ↑(carrier.rows.map (·.statePull)) := endpointBalance_of_stateWalk _ carrier.stateWalk

/-- Step/frame facts for the complete physical event footprint survive every carrier rewrite. -/
theorem ExecutionCarrier.engineFacts
    (carrier : ExecutionCarrier facts events incoming outgoing initialFrontier physicalFinal)
    (program : Target.GuestProgram) (trajectory : Trajectory) (initial : SailState) (timeline : Timeline)
    (steps : ∀ event ∈ events,
      LocalStepFactG program trajectory initial timeline (facts event) ∧
      FrameFactG program trajectory initial timeline (facts event)) :
    ∀ row ∈ carrier.rows, LocalStepFactG program trajectory initial timeline row ∧
      FrameFactG program trajectory initial timeline row := by
  intro row member
  obtain ⟨original, originalMem, aligned⟩ := forall₂_exists_right carrier.aligned row member
  obtain ⟨event, eventMem, rfl⟩ := List.mem_map.mp originalMem
  have semantic := steps event (carrier.exhaustive.mem_iff.mp eventMem)
  exact ⟨aligned.stepFact semantic.1, aligned.frameFact semantic.2⟩

/-- Grounding the rewritten carrier authenticates every original event's operands at their
actual read times. This does not assert truth at the original prior record's historical timestamp. -/
theorem ExecutionCarrier.originalCurrency
    (carrier : ExecutionCarrier facts events incoming outgoing initialFrontier physicalFinal)
    {program : Target.GuestProgram} {trajectory : Trajectory} {initial : SailState}
    (grounded : ∀ row ∈ carrier.rows, GroundedG program trajectory initial carrier.timeline row) :
    ∀ event ∈ events, LocalStateTruthG program trajectory carrier.timeline (facts event).statePull ∧
      ∀ pull ∈ (facts event).memPulls, MemoryMsg.isU64 pull.1 ∧ MemoryMsg.ClkBound pull.1 ∧
        LocalValueAtG trajectory initial carrier.timeline (MemoryMsg.locOf pull.1) pull.2 pull.1.value := by
  intro event member
  have originalMem := List.mem_map_of_mem (f := facts) (carrier.exhaustive.mem_iff.mpr member)
  obtain ⟨row, rowMem, aligned⟩ := forall₂_exists_right carrier.aligned.flip _ originalMem
  have current := grounded row rowMem
  exact ⟨localStateTruthG_congr aligned.pullTime.symm aligned.pullPc.symm current.1,
    aligned.pullCurrency current.1 (fun pull member =>
      ⟨(current.2 pull member).1.1, (current.2 pull member).1.2.1, (current.2 pull member).2⟩)⟩

/-- Ground the carrier from authentic genesis and complete per-event step/frame facts.
The final value assertion concerns the original physical frontier at the outgoing State time. -/
theorem ExecutionCarrier.ground
    (carrier : ExecutionCarrier facts events incoming outgoing initialFrontier physicalFinal)
    (program : Target.GuestProgram) (trajectory : Trajectory) (initial : SailState)
    (initialState : LocalStateTruthG program trajectory carrier.timeline incoming)
    (initialMemory : LiveOKG trajectory initial carrier.timeline (StateMsg.timeNat incoming) initialFrontier)
    (steps : ∀ event ∈ events,
      LocalStepFactG program trajectory initial carrier.timeline (facts event) ∧
      FrameFactG program trajectory initial carrier.timeline (facts event)) :
    (∀ row ∈ carrier.rows, GroundedG program trajectory initial carrier.timeline row) ∧
      LocalStateTruthG program trajectory carrier.timeline outgoing ∧
      (∀ loc message, physicalFinal loc = some message →
        LocalValueAtG trajectory initial carrier.timeline loc (StateMsg.timeNat outgoing) message.value) := by
  have semantic := carrier.engineFacts program trajectory initial carrier.timeline steps
  have grounded := walkG program trajectory initial carrier.timeline (StateMsg.timeNat incoming)
    outgoing carrier.final carrier.rows.length carrier.rows incoming initialFrontier rfl
    (fun row member => (semantic row member).1) (fun row member => (semantic row member).2)
    carrier.rowOK carrier.timeStep initialState initialMemory carrier.stateBalance carrier.memoryBalance
  refine ⟨grounded.1, grounded.2.1, ?_⟩
  intro loc message present
  obtain ⟨earlier, earlierPresent, _, value, _⟩ := carrier.finalRewrite loc message present
  have current := (grounded.2.2 loc earlier earlierPresent).2.2.1
  rwa [value] at current

end SP1Clean.Soundness.NativeCore
