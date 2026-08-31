import SP1Clean.Proofs.Completeness.EventBuckets
import SP1Clean.Proofs.Completeness.ChipLedger
import SP1Clean.Soundness.StateCanon

/-!
# Canonical State-boundary histories

Instruction occurrences are compiled chronologically but stored physically in twenty-five
chip-indexed tables.  State refreshes are stored in one further table.  This module keeps those
orders separate:

* `RoutedEvent.pullState` and `RoutedEvent.rawPushState` are the field-free State records emitted
  by one instruction occurrence;
* `stateBumpEvents` inserts a real `StateBump` exactly when the raw pushed limbs are not already
  canonical;
* `chronologicalStateLinks` interleaves every refresh immediately after the instruction which
  requires it; and
* `physicalStateLinks_perm_chronological` proves that the chip-bucketed instruction links followed
  by the separate bump-table links are a permutation of that chronological stream.

No channel balance or AIR witness is used in the construction.  The final adapter to
`SupportedCoreTraceWitness` names the remaining representation theorem explicitly as
`StateTraceAgreement`: it says that rows built by the registry-indexed table builders expose the
same links as these field-free event projections.  Once that theorem is supplied by trace
assembly, both the regrouping and hand-off premises of
`stateLedger_perm_handoff_chronological` are immediate.
-/

namespace SP1Clean.TraceGen

open SP1Clean.Channels
open SP1Clean.LookupAccessList

/-! ## Field-free State records -/

/-- The five naturals carried by one State-bus message, before embedding in a prime field. -/
structure StateRecord where
  clkHigh : ℕ
  clkLow : ℕ
  pc0 : ℕ
  pc1 : ℕ
  pc2 : ℕ
deriving DecidableEq, Repr

namespace StateRecord

/-- Canonical limb split of a semantic clock and program counter. -/
def canonical (clock pc : ℕ) : StateRecord where
  clkHigh := clock / 2 ^ 24
  clkLow := clock % 2 ^ 24
  pc0 := pc % 2 ^ 16
  pc1 := pc / 2 ^ 16 % 2 ^ 16
  pc2 := pc / 2 ^ 32 % 2 ^ 16

/-- The `StateBump` input which pulls this possibly drifted record. -/
def toBumpEvent (record : StateRecord) : StateBumpEvent where
  clkHigh := record.clkHigh
  clkLow := record.clkLow
  pc0 := record.pc0
  pc1 := record.pc1
  pc2 := record.pc2

/-- The canonical record obtained by running the `StateBump` carry cascade. -/
def normalize (record : StateRecord) : StateRecord where
  clkHigh := record.toBumpEvent.nextClkHigh
  clkLow := record.toBumpEvent.nextClkLow
  pc0 := record.toBumpEvent.nextPc0
  pc1 := record.toBumpEvent.nextPc1
  pc2 := record.toBumpEvent.nextPc2

/-- A field embedding used only at the interaction-ledger boundary. -/
def toMessage {p : ℕ} [NeZero p] (record : StateRecord) : StateMsg (ZMod p) :=
  ⟨record.clkHigh, record.clkLow, record.pc0, record.pc1, record.pc2⟩

/-- The exact Clean lookup key of the embedded State record. -/
def key {p : ℕ} [NeZero p] (record : StateRecord) : LookupKey :=
  msgToken Channels.stateChannel (record.toMessage (p := p))

end StateRecord

/-- Canonical public State endpoints, in the same five-limb representation used by the boundary
verifier row. -/
structure StateBoundary where
  initial : StateRecord
  final : StateRecord

namespace StateBoundary

/-- Construct both public endpoints from semantic clocks and program counters. -/
def canonical (initialClock initialPc finalClock finalPc : ℕ) : StateBoundary where
  initial := StateRecord.canonical initialClock initialPc
  final := StateRecord.canonical finalClock finalPc

end StateBoundary

namespace StateRecord

variable {p : ℕ} [Fact p.Prime]

/-- The generated StateBump row pulls exactly the raw field-free record. -/
@[simp] theorem pulledMessage_stateBumpCols (record : StateRecord) :
    Soundness.StateBumpChip.pulledMessage
        (stateBumpCols (p := p) record.toBumpEvent) = record.toMessage (p := p) := rfl

/-- The generated StateBump row pushes exactly the normalized field-free record. -/
@[simp] theorem pushedMessage_stateBumpCols (record : StateRecord) :
    Soundness.StateBumpChip.pushedMessage
        (stateBumpCols (p := p) record.toBumpEvent) = record.normalize.toMessage (p := p) := by
  unfold Soundness.StateBumpChip.pushedMessage stateBumpCols normalize toMessage
  congr 1
  · change
      ((record.toBumpEvent.nextClkHigh % 256 : ℕ) : ZMod p) +
          ((record.toBumpEvent.nextClkHigh / 256 : ℕ) : ZMod p) * 256 =
        ((record.toBumpEvent.nextClkHigh : ℕ) : ZMod p)
    simpa using congrArg (fun n : ℕ => (n : ZMod p))
      (Nat.mod_add_div' record.toBumpEvent.nextClkHigh 256)
  · change
      ((record.toBumpEvent.nextClkLow % 65536 : ℕ) : ZMod p) +
          ((record.toBumpEvent.nextClkLow / 65536 : ℕ) : ZMod p) * 65536 =
        ((record.toBumpEvent.nextClkLow : ℕ) : ZMod p)
    simpa using congrArg (fun n : ℕ => (n : ZMod p))
      (Nat.mod_add_div' record.toBumpEvent.nextClkLow 65536)

end StateRecord

/-! ## One instruction's State edge -/

namespace RoutedEvent

/-- Clock carried by the common CPU-state input of a routed event. -/
def clock : RoutedEvent → ℕ
  | ⟨.add, event⟩ => event.clk
  | ⟨.addi, event⟩ => event.clk
  | ⟨.addw, event⟩ => event.clk
  | ⟨.sub, event⟩ => event.clk
  | ⟨.subw, event⟩ => event.clk
  | ⟨.bitwise, event⟩ => event.clk
  | ⟨.lt, event⟩ => event.clk
  | ⟨.shiftLeft, event⟩ => event.clk
  | ⟨.shiftRight, event⟩ => event.clk
  | ⟨.jal, event⟩ => event.clk
  | ⟨.jalr, event⟩ => event.clk
  | ⟨.branch, event⟩ => event.clk
  | ⟨.uType, event⟩ => event.clk
  | ⟨.loadByte, event⟩ => event.clk
  | ⟨.loadHalf, event⟩ => event.clk
  | ⟨.loadWord, event⟩ => event.clk
  | ⟨.loadDouble, event⟩ => event.clk
  | ⟨.loadX0, event⟩ => event.clk
  | ⟨.storeByte, event⟩ => event.clk
  | ⟨.storeHalf, event⟩ => event.clk
  | ⟨.storeWord, event⟩ => event.clk
  | ⟨.storeDouble, event⟩ => event.clk
  | ⟨.mul, event⟩ => event.clk
  | ⟨.divRem, event⟩ => event.clk
  | ⟨.aluX0, event⟩ => event.clk

/-- Program counter carried by the common CPU-state input of a routed event. -/
def pc : RoutedEvent → ℕ
  | ⟨.add, event⟩ => event.pc
  | ⟨.addi, event⟩ => event.pc
  | ⟨.addw, event⟩ => event.pc
  | ⟨.sub, event⟩ => event.pc
  | ⟨.subw, event⟩ => event.pc
  | ⟨.bitwise, event⟩ => event.pc
  | ⟨.lt, event⟩ => event.pc
  | ⟨.shiftLeft, event⟩ => event.pc
  | ⟨.shiftRight, event⟩ => event.pc
  | ⟨.jal, event⟩ => event.pc
  | ⟨.jalr, event⟩ => event.pc
  | ⟨.branch, event⟩ => event.pc
  | ⟨.uType, event⟩ => event.pc
  | ⟨.loadByte, event⟩ => event.pc
  | ⟨.loadHalf, event⟩ => event.pc
  | ⟨.loadWord, event⟩ => event.pc
  | ⟨.loadDouble, event⟩ => event.pc
  | ⟨.loadX0, event⟩ => event.pc
  | ⟨.storeByte, event⟩ => event.pc
  | ⟨.storeHalf, event⟩ => event.pc
  | ⟨.storeWord, event⟩ => event.pc
  | ⟨.storeDouble, event⟩ => event.pc
  | ⟨.mul, event⟩ => event.pc
  | ⟨.divRem, event⟩ => event.pc
  | ⟨.aluX0, event⟩ => event.pc

/-- The canonical State record consumed by this instruction occurrence. -/
def pullState (routed : RoutedEvent) : StateRecord :=
  StateRecord.canonical routed.clock routed.pc

private def straightRawPush (clock pc : ℕ) : StateRecord :=
  { clkHigh := clock / 2 ^ 24
    clkLow := clock % 2 ^ 24 + 8
    pc0 := pc % 2 ^ 16 + 4
    pc1 := pc / 2 ^ 16 % 2 ^ 16
    pc2 := pc / 2 ^ 32 % 2 ^ 16 }

private def controlRawPush (clock target : ℕ) : StateRecord :=
  { clkHigh := clock / 2 ^ 24
    clkLow := clock % 2 ^ 24 + 8
    pc0 := target % 2 ^ 16
    pc1 := target / 2 ^ 16 % 2 ^ 16
    pc2 := target / 2 ^ 32 % 2 ^ 16 }

/-- The *uncanonicalized* State record emitted by the instruction row.

Straight-line chips add four only to `pc0`; the three control-flow chips emit their already-limbed
computed target.  Every chip adds eight to the low 24-bit clock without carrying. -/
def rawPushState : RoutedEvent → StateRecord
  | ⟨.jal, event⟩ => controlRawPush event.clk event.jalTarget
  | ⟨.jalr, event⟩ =>
      controlRawPush event.clk (event.jalrTarget - event.jalrTarget % 2)
  | ⟨.branch, event⟩ => controlRawPush event.clk event.branchNextPc
  | ⟨.add, event⟩ => straightRawPush event.clk event.pc
  | ⟨.addi, event⟩ => straightRawPush event.clk event.pc
  | ⟨.addw, event⟩ => straightRawPush event.clk event.pc
  | ⟨.sub, event⟩ => straightRawPush event.clk event.pc
  | ⟨.subw, event⟩ => straightRawPush event.clk event.pc
  | ⟨.bitwise, event⟩ => straightRawPush event.clk event.pc
  | ⟨.lt, event⟩ => straightRawPush event.clk event.pc
  | ⟨.shiftLeft, event⟩ => straightRawPush event.clk event.pc
  | ⟨.shiftRight, event⟩ => straightRawPush event.clk event.pc
  | ⟨.uType, event⟩ => straightRawPush event.clk event.pc
  | ⟨.loadByte, event⟩ => straightRawPush event.clk event.pc
  | ⟨.loadHalf, event⟩ => straightRawPush event.clk event.pc
  | ⟨.loadWord, event⟩ => straightRawPush event.clk event.pc
  | ⟨.loadDouble, event⟩ => straightRawPush event.clk event.pc
  | ⟨.loadX0, event⟩ => straightRawPush event.clk event.pc
  | ⟨.storeByte, event⟩ => straightRawPush event.clk event.pc
  | ⟨.storeHalf, event⟩ => straightRawPush event.clk event.pc
  | ⟨.storeWord, event⟩ => straightRawPush event.clk event.pc
  | ⟨.storeDouble, event⟩ => straightRawPush event.clk event.pc
  | ⟨.mul, event⟩ => straightRawPush event.clk event.pc
  | ⟨.divRem, event⟩ => straightRawPush event.clk event.pc
  | ⟨.aluX0, event⟩ => straightRawPush event.clk event.pc

/-- Canonical successor after the optional State refresh. -/
def nextState (routed : RoutedEvent) : StateRecord := routed.rawPushState.normalize

/-- Exactly one refresh when the instruction's raw push is not already canonical. -/
def stateBumpEvents (routed : RoutedEvent) : List StateBumpEvent :=
  if routed.rawPushState = routed.nextState then [] else [routed.rawPushState.toBumpEvent]

end RoutedEvent

/-- All canonical State refresh rows, in chronological instruction order. -/
def stateBumpEvents (events : List RoutedEvent) : List StateBumpEvent :=
  events.flatMap RoutedEvent.stateBumpEvents

@[simp] theorem RoutedEvent.stateBumpEvents_eq_nil_iff (routed : RoutedEvent) :
    routed.stateBumpEvents = [] ↔ routed.rawPushState = routed.nextState := by
  by_cases canonical : routed.rawPushState = routed.nextState <;>
    simp [RoutedEvent.stateBumpEvents, canonical]

@[simp] theorem RoutedEvent.stateBumpEvents_length_le_one (routed : RoutedEvent) :
    routed.stateBumpEvents.length ≤ 1 := by
  by_cases canonical : routed.rawPushState = routed.nextState <;>
    simp [RoutedEvent.stateBumpEvents, canonical]

/-- The exact semantic range assumptions needed by the StateBump table.  In particular this makes
the top-clock and top-pc no-overflow obligations visible rather than hiding them in trace assembly. -/
def StateBumpReady (events : List RoutedEvent) : Prop :=
  ∀ routed ∈ events, routed.rawPushState ≠ routed.nextState →
    routed.rawPushState.toBumpEvent.WellFormed

/-- Every event emitted by the deterministic State refresh compiler meets the provider registry's
row contract. -/
theorem stateBumpEvents_wellFormed {events : List RoutedEvent}
    (ready : StateBumpReady events) :
    ∀ event ∈ stateBumpEvents events, event.WellFormed := by
  intro event member
  rcases List.mem_flatMap.mp member with ⟨routed, routedMem, eventMem⟩
  by_cases canonical : routed.rawPushState = routed.nextState
  · simp [RoutedEvent.stateBumpEvents, canonical] at eventMem
  · simp [RoutedEvent.stateBumpEvents, canonical] at eventMem
    subst event
    exact ready routed routedMem canonical

/-! ## Chronological record and key links -/

/-- The instruction link followed immediately by its optional canonicalizing refresh. -/
def routedStateRecordLinks (routed : RoutedEvent) : List (StateRecord × StateRecord) :=
  [(routed.pullState, routed.rawPushState)] ++
    if routed.rawPushState = routed.nextState then []
    else [(routed.rawPushState, routed.nextState)]

/-- The one semantic execution order. -/
def chronologicalStateRecordLinks (events : List RoutedEvent) :
    List (StateRecord × StateRecord) :=
  events.flatMap routedStateRecordLinks

/-- Field-free adjacency and endpoint condition for the generated State stream. -/
def StateChronology : StateRecord → List RoutedEvent → StateRecord → Prop
  | held, [], final => held = final
  | held, routed :: rest, final =>
      routed.pullState = held ∧ StateChronology routed.nextState rest final

/-- Embed the chronological links into the exact Clean lookup-key representation. -/
def chronologicalStateLinks {p : ℕ} [NeZero p] (events : List RoutedEvent) :
    List (LookupKey × LookupKey) :=
  (chronologicalStateRecordLinks events).map fun link =>
    (link.1.key (p := p), link.2.key (p := p))

@[simp] theorem chronologicalStateLinks_cons {p : ℕ} [NeZero p]
    (routed : RoutedEvent) (rest : List RoutedEvent) :
    chronologicalStateLinks (p := p) (routed :: rest) =
      (routedStateRecordLinks routed).map (fun link =>
        (link.1.key (p := p), link.2.key (p := p))) ++
        chronologicalStateLinks (p := p) rest := by
  simp [chronologicalStateLinks, chronologicalStateRecordLinks]

/-- Field-free chronology implies the generic State-bus hand-off chain after field embedding. -/
theorem chronologicalStateLinks_isHandoffChain {p : ℕ} [NeZero p]
    {initial final : StateRecord} {events : List RoutedEvent}
    (chronology : StateChronology initial events final) :
    IsHandoffChain (initial.key (p := p)) (chronologicalStateLinks (p := p) events)
      (final.key (p := p)) := by
  induction events generalizing initial with
  | nil =>
      change initial.key (p := p) = final.key (p := p)
      exact congrArg (StateRecord.key (p := p)) chronology
  | cons routed rest ih =>
      obtain ⟨pullEq, tail⟩ := chronology
      rw [chronologicalStateLinks_cons]
      by_cases canonical : routed.rawPushState = routed.nextState
      · simp only [routedStateRecordLinks, canonical, if_pos, List.append_nil,
          List.map_cons, List.map_nil]
        exact ⟨congrArg (StateRecord.key (p := p)) pullEq,
          by simpa [canonical] using ih tail⟩
      · simp only [routedStateRecordLinks, canonical, List.map_append,
          List.map_cons, List.map_nil]
        exact ⟨congrArg (StateRecord.key (p := p)) pullEq, rfl, ih tail⟩

/-! ## Physical table order versus chronological order -/

private def instructionStateLink {p : ℕ} [NeZero p] (routed : RoutedEvent) :
    LookupKey × LookupKey :=
  (routed.pullState.key (p := p), routed.rawPushState.key (p := p))

/-- Instruction links in physical chip-table order. -/
private def bucketInstructionStateLinks {p : ℕ} [NeZero p] :
    List InstructionChipId → List RoutedEvent → List (LookupKey × LookupKey)
  | [], _ => []
  | id :: ids, events =>
      (events.filter fun routed => routed.id = id).map (instructionStateLink (p := p)) ++
          bucketInstructionStateLinks (p := p) ids events

def physicalInstructionStateLinks {p : ℕ} [NeZero p] (events : List RoutedEvent) :
    List (LookupKey × LookupKey) :=
  bucketInstructionStateLinks (p := p) InstructionChipId.all events

/-- Refresh links in their separate physical table order. -/
def physicalStateBumpLinks {p : ℕ} [NeZero p] (events : List RoutedEvent) :
    List (LookupKey × LookupKey) :=
  events.flatMap fun routed =>
    if routed.rawPushState = routed.nextState then []
    else [(routed.rawPushState.key (p := p), routed.nextState.key (p := p))]

private theorem bucketInstructionStateLinks_cons_of_not_mem {p : ℕ} [NeZero p]
    (ids : List InstructionChipId) (routed : RoutedEvent) (rest : List RoutedEvent)
    (notMem : routed.id ∉ ids) :
    bucketInstructionStateLinks (p := p) ids (routed :: rest) =
      bucketInstructionStateLinks (p := p) ids rest := by
  induction ids with
  | nil => rfl
  | cons id ids ih =>
      have ne : routed.id ≠ id := fun eq => notMem (by simp [eq])
      have notTail : routed.id ∉ ids := fun mem => notMem (by simp [mem])
      simp [bucketInstructionStateLinks, ne, ih notTail]

/-- Adding one event to a complete, duplicate-free bucket inventory inserts its instruction link
at exactly one bucket; moving that link to the front is a permutation. -/
private theorem bucketInstructionStateLinks_cons_perm {p : ℕ} [NeZero p]
    (ids : List InstructionChipId) (routed : RoutedEvent) (rest : List RoutedEvent)
    (nodup : ids.Nodup) (member : routed.id ∈ ids) :
    (bucketInstructionStateLinks (p := p) ids (routed :: rest)).Perm
      (instructionStateLink (p := p) routed ::
        bucketInstructionStateLinks (p := p) ids rest) := by
  induction ids with
  | nil => simp at member
  | cons id ids ih =>
      have idNotMem : id ∉ ids := (List.nodup_cons.mp nodup).1
      have tailNodup : ids.Nodup := (List.nodup_cons.mp nodup).2
      by_cases routeEq : routed.id = id
      · have routeNotTail : routed.id ∉ ids := by simpa [routeEq] using idNotMem
        simp [bucketInstructionStateLinks, routeEq,
          bucketInstructionStateLinks_cons_of_not_mem ids routed rest routeNotTail,
          instructionStateLink]
      · have routeMem : routed.id ∈ ids := (List.mem_cons.mp member).resolve_left routeEq
        have tailPerm := ih tailNodup routeMem
        have moved := tailPerm.append_left
          ((rest.filter fun item => item.id = id).map (instructionStateLink (p := p)))
        have result := moved.trans
          (List.perm_middle
            (l₁ := (rest.filter fun item => item.id = id).map
              (instructionStateLink (p := p)))
            (l₂ := bucketInstructionStateLinks (p := p) ids rest)
            (a := instructionStateLink (p := p) routed))
        simpa [bucketInstructionStateLinks, instructionStateLink, routeEq] using result

/-- Stable registry bucketing is a permutation, not an execution ordering. -/
theorem physicalInstructionStateLinks_perm {p : ℕ} [NeZero p]
    (events : List RoutedEvent) :
    (physicalInstructionStateLinks (p := p) events).Perm
      (events.map fun routed =>
        (routed.pullState.key (p := p), routed.rawPushState.key (p := p))) := by
  induction events with
  | nil => simp [physicalInstructionStateLinks, InstructionChipId.all,
      bucketInstructionStateLinks]
  | cons routed rest ih =>
      exact (bucketInstructionStateLinks_cons_perm InstructionChipId.all routed rest
          InstructionChipId.all_nodup (InstructionChipId.mem_all routed.id)).trans
        (List.Perm.cons (instructionStateLink (p := p) routed) ih)

/-- The generic shuffle which moves each row's bump links out of the separate tail and places them
immediately after that row's instruction link. -/
private theorem separatedStateLinks_perm_chronological {p : ℕ} [NeZero p]
    (events : List RoutedEvent) :
    (events.map (instructionStateLink (p := p)) ++
        physicalStateBumpLinks (p := p) events).Perm
      (chronologicalStateLinks (p := p) events) := by
  induction events with
  | nil => simp [physicalStateBumpLinks, chronologicalStateLinks,
      chronologicalStateRecordLinks]
  | cons routed rest ih =>
      let bump : List (LookupKey × LookupKey) :=
        if routed.rawPushState = routed.nextState then []
        else [(routed.rawPushState.key (p := p), routed.nextState.key (p := p))]
      have moveBump :
          (rest.map (instructionStateLink (p := p)) ++ bump ++
              physicalStateBumpLinks (p := p) rest).Perm
            (bump ++ rest.map (instructionStateLink (p := p)) ++
              physicalStateBumpLinks (p := p) rest) :=
        (List.perm_append_comm (l₁ := rest.map (instructionStateLink (p := p)))
          (l₂ := bump)).append_right _
      have tailShuffled :
          (bump ++ rest.map (instructionStateLink (p := p)) ++
              physicalStateBumpLinks (p := p) rest).Perm
            (bump ++ chronologicalStateLinks (p := p) rest) := by
        simpa only [List.append_assoc] using ih.append_left bump
      have shuffled := (List.Perm.cons (instructionStateLink (p := p) routed) moveBump).trans
        (List.Perm.cons (instructionStateLink (p := p) routed) tailShuffled)
      change
        (instructionStateLink (p := p) routed ::
          rest.map (instructionStateLink (p := p)) ++ bump ++
            physicalStateBumpLinks (p := p) rest).Perm _ at shuffled
      by_cases canonical : routed.rawPushState = routed.nextState
      · simpa [physicalStateBumpLinks, chronologicalStateLinks_cons,
          routedStateRecordLinks, instructionStateLink, bump, canonical] using shuffled
      · simpa [physicalStateBumpLinks, chronologicalStateLinks_cons,
          routedStateRecordLinks, instructionStateLink, bump, canonical] using shuffled

/-- Separating all instruction rows from the bump table preserves the interleaved semantic order. -/
theorem physicalStateLinks_perm_chronological {p : ℕ} [NeZero p]
    (events : List RoutedEvent) :
    (physicalInstructionStateLinks (p := p) events ++
        physicalStateBumpLinks (p := p) events).Perm
      (chronologicalStateLinks (p := p) events) := by
  refine ((physicalInstructionStateLinks_perm (p := p) events).append_right _).trans ?_
  exact separatedStateLinks_perm_chronological (p := p) events

/-! ## Exact adapter to the built trace -/

end SP1Clean.TraceGen

namespace SP1Clean.Soundness

open SP1Clean.LookupAccessList
open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance stateHistoryFieldBound : Fact (2 ^ 24 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- The sole remaining representation bridge for State completeness.

The first two fields identify the actual links decoded from the built instruction/StateBump tables
with the compiler's field-free projections.  The last two identify the verifier boundary row with
the compiler's semantic endpoints.  No balance or chain property is hidden here. -/
structure StateTraceAgreement (trace : SupportedCoreTraceWitness p)
    (events : List RoutedEvent) (initial final : StateRecord) : Prop where
  instruction : stateInstrLinks trace = physicalInstructionStateLinks (p := p) events
  bumps : stateBumpLinks trace = physicalStateBumpLinks (p := p) events
  initial : stateInitToken trace = initial.key (p := p)
  final : stateFinalToken trace = final.key (p := p)

/-- Agreement gives the explicit physical-to-chronological regrouping required by State balance. -/
theorem StateTraceAgreement.links_perm_chronological
    {trace : SupportedCoreTraceWitness p} {events : List RoutedEvent}
    {initial final : StateRecord} (agreement : StateTraceAgreement trace events initial final) :
    (stateInstrLinks trace ++ stateBumpLinks trace).Perm
      (chronologicalStateLinks (p := p) events) := by
  rw [agreement.instruction, agreement.bumps]
  exact physicalStateLinks_perm_chronological events

/-- Agreement plus field-free chronology closes the semantic State hand-off. -/
theorem StateTraceAgreement.isHandoffChain
    {trace : SupportedCoreTraceWitness p} {events : List RoutedEvent}
    {initial final : StateRecord} (agreement : StateTraceAgreement trace events initial final)
    (chronology : StateChronology initial events final) :
    IsHandoffChain (stateInitToken trace) (chronologicalStateLinks (p := p) events)
      (stateFinalToken trace) := by
  rw [agreement.initial, agreement.final]
  exact chronologicalStateLinks_isHandoffChain chronology

/-- The complete State-ledger hand-off theorem for a compiled chronological history.  Its
`hbinary`/`hbump` premises are the ordinary selector facts produced by table constraints; all
ordering content comes from the compiler agreement and field-free chronology above. -/
theorem StateTraceAgreement.ledger_perm_handoff
    {trace : SupportedCoreTraceWitness p} {events : List RoutedEvent}
    {initial final : StateRecord} (agreement : StateTraceAgreement trace events initial final)
    (hbinary : ∀ decoded ∈ decodedInstructionRows (p := p) trace.witness.tables,
      (decoded.toChipRow trace.witness.data).is_real = 0 ∨
        (decoded.toChipRow trace.witness.data).is_real = 1)
    (hbump : ∀ row ∈ (stateBumpTable trace.witness).table,
      (stateBumpRow (stateBumpTable trace.witness) row).is_real = 0 ∨
        (stateBumpRow (stateBumpTable trace.witness) row).is_real = 1)
    (hhalt : ∀ row ∈ (haltTable trace.witness).table,
      (haltRow (haltTable trace.witness) row).is_real = 0)
    (chronology : StateChronology initial events final) :
    (active trace.stateLedger).Perm
      (handoff (chainTokens (stateInitToken trace,
        chronologicalStateLinks (p := p) events, stateFinalToken trace))) :=
  stateLedger_perm_handoff_chronological trace hbinary hbump hhalt _
    agreement.links_perm_chronological (agreement.isHandoffChain chronology)

end SP1Clean.Soundness
