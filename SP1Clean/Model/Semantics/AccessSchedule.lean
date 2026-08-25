import SP1Clean.Model.Semantics.AccessPlan

/-!
# Canonical scheduling for an instruction access plan

An `InstructionAccessPlan` says which offline-memory locations an ordinary instruction touches,
but deliberately carries no previous timestamps.  This module supplies those timestamps from an
`AccessFrontier` and inserts the register refreshes needed when a record was last used in another
24-bit timestamp window.

The scheduler is a total, proof-independent function.  A refresh is always posted at `base + 1`,
before the instruction's register positions C/B/A; RAM is never refreshed.  Each scheduled entry
retains its optional refresh beside its stamped touch, so filtering the refreshes cannot obscure
their plan order.  Refreshes do not affect the outgoing frontier: the immediately following
instruction touch overwrites the same location with its position timestamp.

`MemoryBumpEvent` is field-free executor data, so its carrier and semantic well-formedness live at
this substrate layer.  `FormalModel/TraceGen/Bump.lean` remains responsible for turning it into a
physical MemoryBump row and proving the row contract.
-/

namespace SP1Clean.TraceGen

/-- One register-record timestamp refresh.  The value is unchanged; only its timestamp advances. -/
structure MemoryBumpEvent where
  addr : ℕ
  value : ℕ
  prevTs : ℕ
  currTs : ℕ
deriving DecidableEq

/-- The field-free conditions under which a refresh is representable by a MemoryBump row. -/
structure MemoryBumpEvent.WellFormed (event : MemoryBumpEvent) : Prop where
  addr : event.addr < 32
  increases : event.prevTs < event.currTs
  currLt : event.currTs < 2 ^ 48

end SP1Clean.TraceGen

namespace SP1Clean.Semantics

open SP1Clean.TraceGen

/-! ## Window and refresh readiness -/

/-- The high part selected by SP1's 24-bit timestamp comparison. -/
def timestampWindow (timestamp : ℕ) : ℕ :=
  timestamp / 2 ^ 24

/-- Either a frontier timestamp precedes the refresh position or it is already in this row's
timestamp window.  This invariant admits timestamps posted by an earlier aliased role in the same
row while still proving that every generated refresh moves forward. -/
def AccessFrontier.RefreshReadyAt (frontier : AccessFrontier) (base : ℕ) : Prop :=
  ∀ loc, frontier loc < base + 1 ∨
    timestampWindow (frontier loc) = timestampWindow (base + 1)

/-- A frontier that predates the row is refresh-ready. -/
theorem AccessFrontier.BoundedAt.refreshReadyAt {frontier : AccessFrontier} {base : ℕ}
    (bounded : frontier.BoundedAt base) : frontier.RefreshReadyAt base := by
  intro loc
  exact Or.inl (bounded loc)

/-- Executor alignment leaves enough room for all four ordinary record positions in one 24-bit
window. -/
theorem ordinaryBase_remainder_lt {base : ℕ} (aligned : base % ordinaryClkInc = 1) :
    base % 2 ^ 24 + 4 < 2 ^ 24 := by
  have remainderMod : base % 2 ^ 24 % ordinaryClkInc = 1 := by
    rw [Nat.mod_mod_of_dvd base (by norm_num : ordinaryClkInc ∣ 2 ^ 24)]
    exact aligned
  have remainderLt : base % 2 ^ 24 < 2 ^ 24 := Nat.mod_lt _ (by norm_num)
  unfold ordinaryClkInc at remainderMod
  omega

/-- Every planned record position lies in the same timestamp window as the refresh position
`base + 1` when `base` has the ordinary executor alignment. -/
theorem PlannedTouch.recordTime_sameWindow {base : ℕ} (touch : PlannedTouch)
    (aligned : base % ordinaryClkInc = 1) :
    timestampWindow (touch.recordTime base) = timestampWindow (base + 1) := by
  have remainderBound := ordinaryBase_remainder_lt aligned
  have offsetLe : touch.slot.recordOffset ≤ 4 := touch.slot.recordOffset_le_four
  have offsetLt : touch.slot.recordOffset < 2 ^ 24 := by
    omega
  have oneLt : 1 < 2 ^ 24 := by norm_num
  have recordNoCarry : base % 2 ^ 24 + touch.slot.recordOffset % 2 ^ 24 < 2 ^ 24 := by
    rw [Nat.mod_eq_of_lt offsetLt]
    omega
  have refreshNoCarry : base % 2 ^ 24 + 1 % 2 ^ 24 < 2 ^ 24 := by
    rw [Nat.mod_eq_of_lt oneLt]
    omega
  unfold timestampWindow PlannedTouch.recordTime
  rw [Nat.add_div_eq_of_add_mod_lt recordNoCarry,
    Nat.div_eq_of_lt offsetLt, Nat.add_zero,
    Nat.add_div_eq_of_add_mod_lt refreshNoCarry,
    Nat.div_eq_of_lt oneLt, Nat.add_zero]

/-- Posting one touch preserves refresh readiness for the remaining roles in an aligned row. -/
theorem AccessFrontier.RefreshReadyAt.advanceFrontier {frontier : AccessFrontier} {base : ℕ}
    (ready : frontier.RefreshReadyAt base) (touch : PlannedTouch)
    (aligned : base % ordinaryClkInc = 1) :
    (advanceFrontier frontier base touch).RefreshReadyAt base := by
  intro loc
  by_cases sameLoc : loc = touch.loc
  · subst loc
    rw [advanceFrontier_same]
    exact Or.inr (touch.recordTime_sameWindow aligned)
  · rw [advanceFrontier_of_ne frontier base touch sameLoc]
    exact ready loc

/-! ## The total scheduler -/

/-- The optional refresh immediately preceding one planned touch.  Only a structurally register
slot paired with a register location can emit an event. -/
def memoryBumpEvent? (frontier : AccessFrontier) (base : ℕ)
    (touch : PlannedTouch) : Option MemoryBumpEvent :=
  match touch.loc, touch.slot with
  | .reg index, .opC =>
      if timestampWindow (frontier touch.loc) = timestampWindow (base + 1) then
        none
      else
        some
          { addr := index.toNat
            value := touch.pulled.toNat
            prevTs := frontier touch.loc
            currTs := base + 1 }
  | .reg index, .opB =>
      if timestampWindow (frontier touch.loc) = timestampWindow (base + 1) then
        none
      else
        some
          { addr := index.toNat
            value := touch.pulled.toNat
            prevTs := frontier touch.loc
            currTs := base + 1 }
  | .reg index, .opA =>
      if timestampWindow (frontier touch.loc) = timestampWindow (base + 1) then
        none
      else
        some
          { addr := index.toNat
            value := touch.pulled.toNat
            prevTs := frontier touch.loc
            currTs := base + 1 }
  | _, _ => none

/-- The timestamp the instruction row should put in its `prevTs` column. -/
def scheduledPrevious (frontier : AccessFrontier) (base : ℕ)
    (touch : PlannedTouch) : ℕ :=
  match memoryBumpEvent? frontier base touch with
  | some event => event.currTs
  | none => frontier touch.loc

/-- One plan entry with its optional preceding refresh kept beside it. -/
structure ScheduledAccess where
  stamped : StampedTouch
  memoryBump? : Option MemoryBumpEvent
deriving DecidableEq

/-- Schedule one access without consulting or constructing a proof. -/
def scheduleAccess (frontier : AccessFrontier) (base : ℕ)
    (touch : PlannedTouch) : ScheduledAccess :=
  { stamped := ⟨touch, scheduledPrevious frontier base touch⟩
    memoryBump? := memoryBumpEvent? frontier base touch }

/-- A role-ordered scheduled plan and the frontier after all of its instruction touches. -/
structure AccessSchedule where
  accesses : List ScheduledAccess
  outgoing : AccessFrontier

namespace AccessSchedule

/-- The stamped instruction touches, in plan order. -/
def stampedTouches (schedule : AccessSchedule) : List StampedTouch :=
  schedule.accesses.map ScheduledAccess.stamped

/-- The refresh events, filtered from the same role-ordered carrier. -/
def memoryBumps (schedule : AccessSchedule) : List MemoryBumpEvent :=
  schedule.accesses.filterMap ScheduledAccess.memoryBump?

end AccessSchedule

/-- Canonically schedule every role from left to right.  A refresh is overwritten at the same
location by its following instruction access, so recursive frontier advancement is exactly
`advancePlan`. -/
def scheduleAccessPlan (frontier : AccessFrontier) (base : ℕ) :
    InstructionAccessPlan → AccessSchedule
  | [] => ⟨[], frontier⟩
  | touch :: rest =>
      let tail := scheduleAccessPlan (advanceFrontier frontier base touch) base rest
      ⟨scheduleAccess frontier base touch :: tail.accesses, tail.outgoing⟩

@[simp] theorem scheduleAccessPlan_nil (frontier : AccessFrontier) (base : ℕ) :
    scheduleAccessPlan frontier base [] = ⟨[], frontier⟩ := rfl

@[simp] theorem scheduleAccessPlan_cons (frontier : AccessFrontier) (base : ℕ)
    (touch : PlannedTouch) (rest : InstructionAccessPlan) :
    scheduleAccessPlan frontier base (touch :: rest) =
      let tail := scheduleAccessPlan (advanceFrontier frontier base touch) base rest
      ⟨scheduleAccess frontier base touch :: tail.accesses, tail.outgoing⟩ := rfl

@[simp] theorem scheduleAccess_stamped_touch (frontier : AccessFrontier) (base : ℕ)
    (touch : PlannedTouch) :
    (scheduleAccess frontier base touch).stamped.touch = touch := rfl

@[simp] theorem scheduleAccess_memoryBump? (frontier : AccessFrontier) (base : ℕ)
    (touch : PlannedTouch) :
    (scheduleAccess frontier base touch).memoryBump? = memoryBumpEvent? frontier base touch := rfl

/-- Scheduling erases exactly to the input plan, with no reordering or invented instruction role. -/
@[simp] theorem scheduleAccessPlan_erase (frontier : AccessFrontier) (base : ℕ)
    (plan : InstructionAccessPlan) :
    (scheduleAccessPlan frontier base plan).stampedTouches.map StampedTouch.touch = plan := by
  induction plan generalizing frontier with
  | nil => rfl
  | cons touch rest ih =>
      simp only [scheduleAccessPlan, AccessSchedule.stampedTouches, List.map_cons,
        scheduleAccess_stamped_touch]
      have tail := ih (advanceFrontier frontier base touch)
      change List.map StampedTouch.touch
          (List.map ScheduledAccess.stamped
            (scheduleAccessPlan (advanceFrontier frontier base touch) base rest).accesses) = rest
        at tail
      rw [tail]

/-- Scheduling emits exactly one stamped instruction touch per planned role. -/
@[simp] theorem scheduleAccessPlan_stamped_length (frontier : AccessFrontier) (base : ℕ)
    (plan : InstructionAccessPlan) :
    (scheduleAccessPlan frontier base plan).stampedTouches.length = plan.length := by
  induction plan generalizing frontier with
  | nil => rfl
  | cons touch rest ih =>
      simp only [scheduleAccessPlan, AccessSchedule.stampedTouches, List.map_cons,
        List.length_cons]
      have tail := ih (advanceFrontier frontier base touch)
      change (List.map ScheduledAccess.stamped
        (scheduleAccessPlan (advanceFrontier frontier base touch) base rest).accesses).length =
          rest.length at tail
      omega

/-- Refresh insertion does not alter the final access frontier. -/
theorem scheduleAccessPlan_outgoing (frontier : AccessFrontier) (base : ℕ)
    (plan : InstructionAccessPlan) :
    (scheduleAccessPlan frontier base plan).outgoing = advancePlan frontier base plan := by
  induction plan generalizing frontier with
  | nil => rfl
  | cons touch rest ih => simp [scheduleAccessPlan, advancePlan, ih]

/-- Hence the scheduler's frontier is valid at the next ordinary row. -/
theorem scheduleAccessPlan_outgoing_bounded_next {frontier : AccessFrontier} {base : ℕ}
    (plan : InstructionAccessPlan) (bounded : frontier.BoundedAt base) :
    (scheduleAccessPlan frontier base plan).outgoing.BoundedAt (base + ordinaryClkInc) := by
  rw [scheduleAccessPlan_outgoing]
  exact advancePlan_bounded_next plan (bounded.mono (by omega))

@[simp] theorem memoryBumpEvent?_ram (frontier : AccessFrontier) (base : ℕ)
    (slot : AccessSlot) (cell : RamCell) (pulled pushed : BitVec 64) :
    memoryBumpEvent? frontier base ⟨slot, .ram cell, pulled, pushed⟩ = none := by
  cases slot <;> rfl

@[simp] theorem memoryBumpEvent?_ramSlot (frontier : AccessFrontier) (base : ℕ)
    (index : BitVec 5) (pulled pushed : BitVec 64) :
    memoryBumpEvent? frontier base ⟨.ram, .reg index, pulled, pushed⟩ = none := rfl

/-! ## Scheduler correctness -/

/-- The shape of every emitted refresh: a register role, unchanged value, and timestamp `base + 1`.
This is also the precise statement that the scheduler never emits a RAM refresh. -/
theorem memoryBumpEvent?_shape {frontier : AccessFrontier} {base : ℕ}
    {touch : PlannedTouch} {event : MemoryBumpEvent}
    (emitted : memoryBumpEvent? frontier base touch = some event) :
    ∃ index : BitVec 5,
      touch.loc = .reg index ∧ touch.slot ≠ .ram ∧
      event =
        { addr := index.toNat
          value := touch.pulled.toNat
          prevTs := frontier touch.loc
          currTs := base + 1 } := by
  rcases touch with ⟨slot, loc, pulled, pushed⟩
  cases loc with
  | ram cell => cases slot <;> simp [memoryBumpEvent?] at emitted
  | reg index =>
      cases slot
      · simp [memoryBumpEvent?] at emitted
      all_goals
        simp only [memoryBumpEvent?] at emitted
        split at emitted
        · contradiction
        · simp only [Option.some.injEq] at emitted
          subst event
          refine ⟨index, rfl, ?_, rfl⟩
          simp

/-- A generated head refresh is well-formed whenever the frontier is refresh-ready and the row's
refresh position is within the 48-bit clock. -/
theorem memoryBumpEvent?_wellFormed {frontier : AccessFrontier} {base : ℕ}
    {touch : PlannedTouch} {event : MemoryBumpEvent}
    (ready : frontier.RefreshReadyAt base) (currLt : base + 1 < 2 ^ 48)
    (emitted : memoryBumpEvent? frontier base touch = some event) :
    event.WellFormed := by
  rcases touch with ⟨slot, loc, pulled, pushed⟩
  cases loc with
  | ram cell => cases slot <;> simp [memoryBumpEvent?] at emitted
  | reg index =>
      cases slot
      · simp [memoryBumpEvent?] at emitted
      all_goals
        simp only [memoryBumpEvent?] at emitted
        split at emitted
        · contradiction
        · rename_i different
          simp only [Option.some.injEq] at emitted
          subst event
          refine ⟨index.isLt, ?_, currLt⟩
          rcases ready (.reg index) with before | sameWindow
          · exact before
          · exact False.elim (different sameWindow)

/-- Refresh readiness is the induction invariant for the role-ordered schedule. -/
private theorem scheduledAccesses_bumps_wellFormed_of_ready
    {frontier : AccessFrontier} {base : ℕ} {plan : InstructionAccessPlan}
    (wellFormed : plan.WellFormed) (ready : frontier.RefreshReadyAt base)
    (aligned : base % ordinaryClkInc = 1) (currLt : base + 1 < 2 ^ 48) :
    ∀ access ∈ (scheduleAccessPlan frontier base plan).accesses,
      ∀ event, access.memoryBump? = some event → event.WellFormed := by
  induction plan generalizing frontier with
  | nil => simp [scheduleAccessPlan]
  | cons touch rest ih =>
      intro access member event emitted
      simp only [scheduleAccessPlan, List.mem_cons] at member
      rcases member with rfl | member
      · exact memoryBumpEvent?_wellFormed ready currLt emitted
      · exact ih wellFormed.tail (ready.advanceFrontier touch aligned)
          access member event emitted

/-- Every refresh filtered from a well-formed aligned plan satisfies the MemoryBump event contract.
The hypotheses are exactly the semantic scheduler boundary: a bounded incoming frontier and a
48-bit ordinary base clock. -/
theorem scheduleAccessPlan_memoryBumps_wellFormed
    {frontier : AccessFrontier} {base : ℕ} {plan : InstructionAccessPlan}
    (wellFormed : plan.WellFormed) (bounded : frontier.BoundedAt base)
    (aligned : base % ordinaryClkInc = 1) (currLt : base + 1 < 2 ^ 48) :
    ∀ event ∈ (scheduleAccessPlan frontier base plan).memoryBumps,
      event.WellFormed := by
  intro event member
  rw [AccessSchedule.memoryBumps] at member
  rcases List.mem_filterMap.mp member with ⟨access, accessMem, emitted⟩
  exact scheduledAccesses_bumps_wellFormed_of_ready wellFormed bounded.refreshReadyAt
    aligned currLt access accessMem event emitted

/-- Every filtered refresh uses the canonical pre-instruction timestamp. -/
theorem scheduleAccessPlan_memoryBump_currTs
    {frontier : AccessFrontier} {base : ℕ} {plan : InstructionAccessPlan}
    {event : MemoryBumpEvent}
    (member : event ∈ (scheduleAccessPlan frontier base plan).memoryBumps) :
    event.currTs = base + 1 := by
  rw [AccessSchedule.memoryBumps] at member
  rcases List.mem_filterMap.mp member with ⟨access, accessMem, emitted⟩
  have entriesShape :
      ∀ {frontier : AccessFrontier} {plan : InstructionAccessPlan}
        (access : ScheduledAccess),
        access ∈ (scheduleAccessPlan frontier base plan).accesses →
        ∀ {event : MemoryBumpEvent}, access.memoryBump? = some event →
          event.currTs = base + 1 := by
    intro nextFrontier nextPlan
    induction nextPlan generalizing nextFrontier with
    | nil => simp [scheduleAccessPlan]
    | cons touch rest ih =>
        intro nextAccess nextMember nextEvent nextEmitted
        simp only [scheduleAccessPlan, List.mem_cons] at nextMember
        rcases nextMember with rfl | nextMember
        · obtain ⟨_, _, _, eventEq⟩ := memoryBumpEvent?_shape nextEmitted
          rw [eventEq]
        · exact ih nextAccess nextMember nextEmitted
  exact entriesShape access accessMem emitted

/-- One scheduled touch's previous timestamp is sound whenever the incoming frontier predates that
touch. -/
private theorem scheduleAccess_previous_lt {frontier : AccessFrontier} {base : ℕ}
    (touch : PlannedTouch) (before : frontier touch.loc < touch.recordTime base) :
    (scheduleAccess frontier base touch).stamped.previous <
      (scheduleAccess frontier base touch).stamped.current base := by
  cases emitted : memoryBumpEvent? frontier base touch with
  | none =>
      simpa [scheduleAccess, scheduledPrevious, emitted, StampedTouch.current] using before
  | some event =>
      obtain ⟨_, _, notRam, eventEq⟩ := memoryBumpEvent?_shape emitted
      subst event
      rcases touch with ⟨slot, loc, pulled, pushed⟩
      simp only [scheduleAccess, scheduledPrevious, emitted, StampedTouch.current,
        PlannedTouch.recordTime]
      cases slot
      · contradiction
      all_goals (simp only [AccessSlot.recordOffset_opC, AccessSlot.recordOffset_opB,
        AccessSlot.recordOffset_opA]; omega)

private theorem scheduleAccessPlan_previous_lt_of_before
    {frontier : AccessFrontier} {base : ℕ} {plan : InstructionAccessPlan}
    (wellFormed : plan.WellFormed) (before : frontier.BeforePlan base plan) :
    ∀ stamped ∈ (scheduleAccessPlan frontier base plan).stampedTouches,
      stamped.previous < stamped.current base := by
  induction plan generalizing frontier with
  | nil => simp [scheduleAccessPlan, AccessSchedule.stampedTouches]
  | cons touch rest ih =>
      intro stamped member
      simp only [scheduleAccessPlan, AccessSchedule.stampedTouches, List.map_cons,
        List.mem_cons] at member
      rcases member with rfl | member
      · exact scheduleAccess_previous_lt touch (before touch List.mem_cons_self)
      · exact ih wellFormed.tail (beforePlan_advance before wellFormed.ordered) stamped member

/-- Every timestamp handed to an instruction event strictly predates that role's current access.
This covers both the direct-frontier case and the `base + 1` timestamp supplied after a refresh. -/
theorem scheduleAccessPlan_previous_lt
    {frontier : AccessFrontier} {base : ℕ} {plan : InstructionAccessPlan}
    (wellFormed : plan.WellFormed) (bounded : frontier.BoundedAt base) :
    ∀ stamped ∈ (scheduleAccessPlan frontier base plan).stampedTouches,
      stamped.previous < stamped.current base :=
  scheduleAccessPlan_previous_lt_of_before wellFormed bounded.beforePlan

end SP1Clean.Semantics
