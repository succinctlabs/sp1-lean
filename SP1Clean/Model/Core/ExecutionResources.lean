import SP1Clean.Model.Core.ResourceUsage
import SP1Clean.Model.Core.HostSnapshot
import SP1Clean.Model.Core.ExecutionReplay
import SP1Clean.Model.Core.MemorySupport

/-! # Resource observation of the complete execution replay

This observer calls the existing replay step. It adds no transition relation and makes no
choices of intermediate states. Failed tapes have a total observation, but are excluded by
`ExecutionPath`; all composition and event-cost conclusions below use that existing relation.
-/

namespace SP1Clean.Model.Core
open Machine Soundness.Target

/-- Every real event consumes at least one ordinary eight-tick window. -/
theorem event_count_le_ticks (events : List ExecutionEvent) :
    8 * events.length ≤ (events.map ExecutionEvent.duration).sum := by
  induction events with
  | nil => simp
  | cons event rest ih =>
    cases event <;> simp only [List.length_cons, List.map_cons, List.sum_cons,
      ExecutionEvent.duration_ordinary, ExecutionEvent.duration_syscall] <;> omega

/-- Length-prefixed byte payload cost; empty buffers still occupy one length word. -/
def bytePayloadCost (bytes : Bytes) : ℕ := 8 + bytes.length

/-- An ordered list includes its length and every individual buffer length. -/
def hintPayloadCost (hints : List Bytes) : ℕ := 8 + (hints.map bytePayloadCost).sum

/-- Request-bound replies retain their descriptor, request bytes and ordered fresh hints. -/
def HookReply.payloadCost (reply : HookReply) : ℕ :=
  4 + bytePayloadCost reply.request.input + hintPayloadCost reply.hints

/-- Request tags and logical buffers are counted even when guest addresses overlap. -/
def HostRequest.payloadCost : HostRequest → ℕ
  | .hook request => 1 + 4 + bytePayloadCost request.input
  | .proof request => 1 + bytePayloadCost request.verificationKey + bytePayloadCost request.publicValues

/-- Host boundary payload, including pending replies, recorded requests, banks and exit status. -/
def HostState.payloadCost (host : HostState) : ℕ :=
  hintPayloadCost host.io.hints + bytePayloadCost host.io.publicOutput +
    8 + (host.replies.map HookReply.payloadCost).sum +
    64 + 8 + (host.requests.map HostRequest.payloadCost).sum +
    bytePayloadCost host.stdout + bytePayloadCost host.stderr + 5

/-- Canonical live nonzero RAM addresses in the represented Sail domain. -/
noncomputable def ExecutionState.memorySupport (state : ExecutionState) : Finset ℕ := by
  classical
  exact (Finset.range NativeLayout.sailMemory.upper).filter
    (fun address => (state.sail.mem.get? address).any (· != 0))

/-- Variable byte payload at a boundary: live RAM, complete host data and Sail output strings.
Fixed register/platform data is public boundary data, not a serialization claim of this measure. -/
noncomputable def ExecutionState.boundaryPayload (state : ExecutionState) : ℕ :=
  state.memorySupport.card + state.host.payloadCost +
    8 + (state.sail.sailOutput.toList.map (fun line => 8 + line.utf8ByteSize)).sum

/-- Peak quantities observe the complete current state, including the incoming host inventory. -/
noncomputable def ExecutionState.resources (state : ExecutionState) : ResourceUsage
  | .liveHints => state.host.io.hints.length
  | .liveHintBytes => (state.host.io.hints.map List.length).sum
  | .requests => state.host.requests.length
  | .outputBytes => state.host.io.publicOutput.length + state.host.stdout.length + state.host.stderr.length
  | .boundaryBytes => state.boundaryPayload
  | _ => 0

/-- Work of one event. Host demand is obtained from the existing concrete interpreter and footprint. -/
def HostState.eventResources (host : HostState) (policy : HostPolicy) (context : HostReadContext)
    (event : ExecutionEvent) : ResourceUsage :=
  fun kind => match kind with
    | .events => 1
    | .ticks => event.duration
    | _ => match event with
      | .ordinary => 0
      | .syscall _ => match host.run policy context with
        | none => 0
        | some execution => host.executionResources context execution kind

/-- One event observed directly on the complete Sail state. -/
def ExecutionState.eventResources (policy : HostPolicy) (source : ExecutionState)
    (event : ExecutionEvent) : ResourceUsage :=
  source.host.eventResources policy (.ofSail source.sail) event

/-- The finite host read interface computes exactly the same event cost. -/
theorem ExecutionSnapshot.eventResources_realize (snapshot : ExecutionSnapshot) (policy : HostPolicy)
    (event : ExecutionEvent) : snapshot.realize.eventResources policy event =
      snapshot.host.eventResources policy snapshot.sail.readContext event := by
  rw [snapshot.sail.readContext_eq]
  rfl

/-- Measure one tape by observing the existing replay; endpoint occupancy belongs to each real step. -/
noncomputable def executionResources (policy : HostPolicy) (program : GuestProgram) :
    ExecutionState → List ExecutionEvent → ResourceUsage
  | _, [] => ResourceUsage.zero
  | source, event :: rest =>
      (source.resources.combine (source.eventResources policy event)).combine
        (match replayStep? policy program source event with
          | none => ResourceUsage.zero
          | some next => next.resources.combine (executionResources policy program next rest))

@[simp] theorem executionResources_nil (policy : HostPolicy) (program : GuestProgram)
    (source : ExecutionState) : executionResources policy program source [] = ResourceUsage.zero := rfl

/-- Along an actual path, the observer uses the actual next state with no default branch. -/
theorem executionResources_cons {policy : HostPolicy} {program : GuestProgram}
    {source middle : ExecutionState} {event : ExecutionEvent}
    (step : ExecutionStep policy program source event middle) (events : List ExecutionEvent) :
    executionResources policy program source (event :: events) =
      (source.resources.combine (source.eventResources policy event)).combine
        (middle.resources.combine (executionResources policy program middle events)) := by
  simp only [executionResources, step.replay]

/-- Boundary occupancy is invariant under executable complete-snapshot equality. -/
theorem ExecutionSnapshot.resources_congr {left right : ExecutionSnapshot}
    (same : left.equivalent right = true) : left.realize.resources = right.realize.resources :=
  congrArg ExecutionState.resources ((ExecutionSnapshot.equivalent_iff _ _).mp same)

/-- Tape usage is invariant under complete source equality, including all host inputs. -/
theorem ExecutionSnapshot.executionResources_congr (policy : HostPolicy) (program : GuestProgram)
    {left right : ExecutionSnapshot} (same : left.equivalent right = true)
    (events : List ExecutionEvent) :
    executionResources policy program left.realize events =
      executionResources policy program right.realize events := by
  rw [(ExecutionSnapshot.equivalent_iff _ _).mp same]

/-- Canonical sparse support computes the semantic measure without enumerating dense Sail memory. -/
theorem ExecutionSnapshot.memorySupport_eq (snapshot : ExecutionSnapshot) :
    snapshot.realize.memorySupport = snapshot.sail.memory.supportBelow NativeLayout.sailMemory.upper := by
  classical
  apply Finset.ext
  intro address
  simp only [ExecutionState.memorySupport, Finset.mem_filter, Finset.mem_range, ByteMemory.mem_supportBelow]
  by_cases bound : address < NativeLayout.sailMemory.upper
  · have read : snapshot.realize.sail.mem.get? address = some (snapshot.sail.memory.read address) :=
      (snapshot.sail.memory.toSailMemory_get? _ _).trans (if_pos bound)
    simp only [bound, true_and]
    change (snapshot.realize.sail.mem.get? address).any (· != 0) = true ↔ _
    rw [read]
    simp
  · simp [bound]

/-- Executable occupancy measurement of the finite boundary; no dense memory is materialized. -/
def ExecutionSnapshot.resources (snapshot : ExecutionSnapshot) : ResourceUsage
  | .liveHints => snapshot.host.io.hints.length
  | .liveHintBytes => (snapshot.host.io.hints.map List.length).sum
  | .requests => snapshot.host.requests.length
  | .outputBytes => snapshot.host.io.publicOutput.length + snapshot.host.stdout.length + snapshot.host.stderr.length
  | .boundaryBytes => (snapshot.sail.memory.supportBelow NativeLayout.sailMemory.upper).card +
      snapshot.host.payloadCost + 8 + (snapshot.sail.output.toList.map (fun line => 8 + line.utf8ByteSize)).sum
  | _ => 0

/-- The executable finite measurement is exactly the complete semantic state's occupancy. -/
theorem ExecutionSnapshot.resources_realize (snapshot : ExecutionSnapshot) :
    snapshot.realize.resources = snapshot.resources := by
  funext kind
  cases kind <;> simp only [ExecutionState.resources, ExecutionSnapshot.resources,
    ExecutionState.boundaryPayload, ExecutionSnapshot.memorySupport_eq] <;> rfl

/-- Segment composition adds cumulative work and takes maxima of actual live inventories. -/
theorem ExecutionPath.resources_append {policy : HostPolicy} {program : GuestProgram}
    {source middle : ExecutionState} {first : List ExecutionEvent}
    (path : ExecutionPath policy program source first middle) (second : List ExecutionEvent) :
    executionResources policy program source (first ++ second) =
      (executionResources policy program source first).combine
        (executionResources policy program middle second) := by
  induction path with
  | nil => simp only [List.nil_append, executionResources_nil, ResourceUsage.zero_combine]
  | cons step _ ih =>
      simp only [List.cons_append, executionResources_cons step, ih, ResourceUsage.combine_assoc]

/-- Work counts real events, not rows or padded trace height. -/
theorem ExecutionPath.resources_events {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {events : List ExecutionEvent}
    (path : ExecutionPath policy program source events target) :
    executionResources policy program source events .events = events.length := by
  induction path with
  | nil => rfl
  | cons step _ ih =>
      rw [executionResources_cons step]
      simp only [ResourceUsage.combine, ResourceKind.cumulative, ↓reduceIte,
        ExecutionState.resources, ExecutionState.eventResources, HostState.eventResources, Nat.zero_add, ih, List.length_cons]
      omega

/-- Work uses the actual ordinary/host schedule rather than an eight-tick approximation. -/
theorem ExecutionPath.resources_ticks {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {events : List ExecutionEvent}
    (path : ExecutionPath policy program source events target) :
    executionResources policy program source events .ticks = (events.map ExecutionEvent.duration).sum := by
  induction path with
  | nil => rfl
  | cons step _ ih =>
      rw [executionResources_cons step]
      simp only [ResourceUsage.combine, ResourceKind.cumulative, ↓reduceIte,
        ExecutionState.resources, ExecutionState.eventResources, HostState.eventResources, Nat.zero_add, ih, List.map_cons, List.sum_cons]

/-- Every cut of a bounded path fits the same ceilings on both pieces, without resetting host state. -/
theorem ExecutionPath.resources_split {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {events : List ExecutionEvent} {limits : ResourceLimits}
    (path : ExecutionPath policy program source events target)
    (fits : (executionResources policy program source events).Fits limits) (cut : ℕ) :
    ∃ middle, ExecutionPath policy program source (events.take cut) middle ∧
      ExecutionPath policy program middle (events.drop cut) target ∧
      (executionResources policy program source (events.take cut)).Fits limits ∧
      (executionResources policy program middle (events.drop cut)).Fits limits := by
  obtain ⟨middle, left, right⟩ := path.split cut
  have combined := left.resources_append (events.drop cut)
  rw [List.take_append_drop] at combined
  rw [combined] at fits
  exact ⟨middle, left, right, fits.left, fits.right⟩

end SP1Clean.Model.Core
