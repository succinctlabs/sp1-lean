import SP1Clean.Model.Semantics.MicroTime

/-!
# Field-free instruction access plans

An ordinary SP1 instruction touches at most four offline-memory roles, in the fixed order
`RAM`, `op_c`, `op_b`, `op_a`.  This module records that common semantic spine without importing a
chip, a Clean circuit, or a physical row:

* a `PlannedTouch` names the semantic location and the 64-bit value claimed and reposted there;
* `InstructionAccessPlan.WellFormed` records the role order, register/RAM location kind, and the
  two unconditional read-back roles;
* `InstructionAccessPlan.RunsFrom` is the sequential value interpretation, so aliases observe the
  value posted by the preceding role; and
* `stampPlan` threads the trace generator's previous-access frontier through the same ordered list.

The plan deliberately carries no clock, previous timestamp, opcode, chip identity, PC, architectural
write flag, field limb, or Sail state.  Those remain owned by the semantic transition and physical
row on the two sides of this shared projection.
-/

namespace SP1Clean.Semantics

/-! ## The four ordinary-memory roles -/

/-- The executor's four ordinary offline-memory positions, in increasing record-time order. -/
inductive AccessSlot
  | ram
  | opC
  | opB
  | opA
deriving DecidableEq, Repr

namespace AccessSlot

/-- The micro-time at which grounding observes the pulled value.

The RAM and `op_a` priors describe the value before their effect, so they are observed at the row
start.  The two source-register read-backs are observed at their own access positions. -/
def observeOffset : AccessSlot → ℕ
  | .ram => 0
  | .opC => regCOffset
  | .opB => regBOffset
  | .opA => 0

/-- The micro-time at which the row posts the new/read-back offline-memory record. -/
def recordOffset : AccessSlot → ℕ
  | .ram => ramEffectOffset
  | .opC => regCOffset
  | .opB => regBOffset
  | .opA => regEffectOffset

/-- Whether a slot has the expected kind of semantic location. -/
def Accepts : AccessSlot → MemLoc → Prop
  | .ram, .ram _ => True
  | .opC, .reg _ => True
  | .opB, .reg _ => True
  | .opA, .reg _ => True
  | _, _ => False

@[simp] theorem observeOffset_ram : observeOffset .ram = 0 := rfl

@[simp] theorem observeOffset_opC : observeOffset .opC = 2 := rfl

@[simp] theorem observeOffset_opB : observeOffset .opB = 3 := rfl

@[simp] theorem observeOffset_opA : observeOffset .opA = 0 := rfl

@[simp] theorem recordOffset_ram : recordOffset .ram = 1 := rfl

@[simp] theorem recordOffset_opC : recordOffset .opC = 2 := rfl

@[simp] theorem recordOffset_opB : recordOffset .opB = 3 := rfl

@[simp] theorem recordOffset_opA : recordOffset .opA = 4 := rfl

/-- Every posted record lies strictly after the row's base clock. -/
theorem recordOffset_pos (slot : AccessSlot) : 0 < slot.recordOffset := by
  cases slot <;> norm_num

/-- Every posted record lies by the ordinary row's last memory position. -/
theorem recordOffset_le_four (slot : AccessSlot) : slot.recordOffset ≤ 4 := by
  cases slot <;> norm_num

/-- The semantic observation never follows the record it justifies. -/
theorem observeOffset_le_recordOffset (slot : AccessSlot) :
    slot.observeOffset ≤ slot.recordOffset := by
  cases slot <;> norm_num

end AccessSlot

/-! ## Plans and their sequential value meaning -/

/-- One field-free offline-memory touch of an ordinary instruction. -/
structure PlannedTouch where
  slot : AccessSlot
  loc : MemLoc
  pulled : BitVec 64
  pushed : BitVec 64
deriving DecidableEq

namespace PlannedTouch

/-- Absolute time of the value observation in a row beginning at `base`. -/
def observeTime (touch : PlannedTouch) (base : ℕ) : ℕ :=
  base + touch.slot.observeOffset

/-- Absolute time of the record posted by this touch in a row beginning at `base`. -/
def recordTime (touch : PlannedTouch) (base : ℕ) : ℕ :=
  base + touch.slot.recordOffset

end PlannedTouch

/-- The ordered, field-free memory-access spine of one ordinary instruction. -/
abbrev InstructionAccessPlan := List PlannedTouch

/-- A partial value image for SP1 Memory-bus locations.  Missing values make `run?` fail closed. -/
abbrev LocationValues := MemLoc → Option (BitVec 64)

namespace InstructionAccessPlan

/-- Structural validity of an ordinary access plan.

Strictly increasing record offsets imply that every role occurs at most once and that any
same-location aliases are processed in SP1's `RAM`, C, B, A order. -/
structure WellFormed (plan : InstructionAccessPlan) : Prop where
  ordered : plan.Pairwise fun left right =>
    left.slot.recordOffset < right.slot.recordOffset
  locKind : ∀ touch ∈ plan, touch.slot.Accepts touch.loc
  readback : ∀ touch ∈ plan,
    touch.slot = .opC ∨ touch.slot = .opB → touch.pushed = touch.pulled

/-- The empty access plan is structurally valid. -/
theorem wellFormed_nil : WellFormed [] :=
  ⟨List.Pairwise.nil, by simp, by simp⟩

/-- Structural validity is inherited by a plan tail. -/
theorem WellFormed.tail {touch : PlannedTouch} {rest : InstructionAccessPlan}
    (wellFormed : WellFormed (touch :: rest)) : WellFormed rest where
  ordered := (List.pairwise_cons.mp wellFormed.ordered).2
  locKind item member := wellFormed.locKind item (List.mem_cons_of_mem touch member)
  readback item member := wellFormed.readback item (List.mem_cons_of_mem touch member)

/-- Apply one planned value transition, failing when the claimed pulled value is not current. -/
def applyTouch? (values : LocationValues) (touch : PlannedTouch) : Option LocationValues :=
  if values touch.loc = some touch.pulled then
    some (Function.update values touch.loc (some touch.pushed))
  else
    none

/-- Execute a plan from left to right on a partial location-value image. -/
def run? : InstructionAccessPlan → LocationValues → Option LocationValues
  | [], values => some values
  | touch :: rest, values =>
      (applyTouch? values touch).bind (run? rest)

/-- A plan sequentially transforms `initial` into `final`. -/
def RunsFrom (plan : InstructionAccessPlan) (initial final : LocationValues) : Prop :=
  plan.run? initial = some final

@[simp] theorem run_nil (values : LocationValues) :
    run? [] values = some values := rfl

@[simp] theorem run_cons (touch : PlannedTouch) (rest : InstructionAccessPlan)
    (values : LocationValues) :
    run? (touch :: rest) values =
      (applyTouch? values touch).bind (run? rest) := rfl

/-- Constructor form of one sequential plan step. -/
theorem runsFrom_cons_iff {touch : PlannedTouch} {rest : InstructionAccessPlan}
    {initial final : LocationValues} :
    RunsFrom (touch :: rest) initial final ↔
      initial touch.loc = some touch.pulled ∧
        RunsFrom rest (Function.update initial touch.loc (some touch.pushed)) final := by
  by_cases current : initial touch.loc = some touch.pulled <;>
    simp [RunsFrom, run?, applyTouch?, current]

/-- The empty plan leaves the value image unchanged. -/
theorem runsFrom_nil_iff {initial final : LocationValues} :
    RunsFrom [] initial final ↔ final = initial := by
  simp [RunsFrom, eq_comm]

/-- Sequential execution has at most one result. -/
theorem RunsFrom.deterministic {plan : InstructionAccessPlan}
    {initial final₁ final₂ : LocationValues}
    (left : RunsFrom plan initial final₁) (right : RunsFrom plan initial final₂) :
    final₁ = final₂ := by
  rw [RunsFrom, left] at right
  exact Option.some.inj right

/-- Adjacent aliases are value-safe: the later touch claims exactly what the earlier one posted. -/
theorem RunsFrom.adjacent_alias {first second : PlannedTouch}
    {rest : InstructionAccessPlan} {initial final : LocationValues}
    (runs : RunsFrom (first :: second :: rest) initial final)
    (sameLoc : second.loc = first.loc) : second.pulled = first.pushed := by
  have afterFirst := (runsFrom_cons_iff.mp runs).2
  have secondPull := (runsFrom_cons_iff.mp afterFirst).1
  rw [sameLoc] at secondPull
  have valuesEq : some first.pushed = some second.pulled := by
    simpa using secondPull
  exact (Option.some.inj valuesEq).symm

end InstructionAccessPlan

/-! ## Previous-timestamp frontier stamping -/

/-- The most recently posted timestamp at every SP1 Memory-bus location. -/
abbrev AccessFrontier := MemLoc → ℕ

namespace AccessFrontier

/-- Genesis frontier: no location has been accessed after timestamp zero. -/
def initial : AccessFrontier := fun _ => 0

/-- Every timestamp in the frontier predates the earliest ordinary access at `base + 1`. -/
def BoundedAt (frontier : AccessFrontier) (base : ℕ) : Prop :=
  ∀ loc, frontier loc < base + 1

/-- A frontier bound remains true when the base clock is increased. -/
theorem BoundedAt.mono {frontier : AccessFrontier} {base next : ℕ}
    (bounded : frontier.BoundedAt base) (le : base ≤ next) : frontier.BoundedAt next := by
  intro loc
  exact lt_of_lt_of_le (bounded loc) (by omega)

/-- The genesis frontier is valid at the executor's initial clock one. -/
theorem initial_boundedAt_one : initial.BoundedAt 1 := by
  intro loc
  simp [initial]

end AccessFrontier

/-- One planned touch annotated with the previous timestamp displaced at its location. -/
structure StampedTouch where
  touch : PlannedTouch
  previous : ℕ
deriving DecidableEq

namespace StampedTouch

/-- The current record time of a stamped touch. -/
def current (stamped : StampedTouch) (base : ℕ) : ℕ :=
  stamped.touch.recordTime base

end StampedTouch

/-- Update one location's timestamp to this touch's record time. -/
def advanceFrontier (frontier : AccessFrontier) (base : ℕ)
    (touch : PlannedTouch) : AccessFrontier :=
  Function.update frontier touch.loc (touch.recordTime base)

@[simp] theorem advanceFrontier_same (frontier : AccessFrontier) (base : ℕ)
    (touch : PlannedTouch) :
    advanceFrontier frontier base touch touch.loc = touch.recordTime base := by
  simp [advanceFrontier]

theorem advanceFrontier_of_ne (frontier : AccessFrontier) (base : ℕ)
    (touch : PlannedTouch) {loc : MemLoc} (ne : loc ≠ touch.loc) :
    advanceFrontier frontier base touch loc = frontier loc := by
  simp [advanceFrontier, Function.update_of_ne ne]

/-- Update a frontier with every touch in plan order. -/
def advancePlan (frontier : AccessFrontier) (base : ℕ) :
    InstructionAccessPlan → AccessFrontier
  | [] => frontier
  | touch :: rest => advancePlan (advanceFrontier frontier base touch) base rest

/-- Annotate every touch with its displaced timestamp and return the final frontier. -/
def stampPlan (frontier : AccessFrontier) (base : ℕ) :
    InstructionAccessPlan → List StampedTouch × AccessFrontier
  | [] => ([], frontier)
  | touch :: rest =>
      let next := advanceFrontier frontier base touch
      let stampedRest := stampPlan next base rest
      (⟨touch, frontier touch.loc⟩ :: stampedRest.1, stampedRest.2)

@[simp] theorem stampPlan_nil (frontier : AccessFrontier) (base : ℕ) :
    stampPlan frontier base [] = ([], frontier) := rfl

@[simp] theorem stampPlan_cons (frontier : AccessFrontier) (base : ℕ)
    (touch : PlannedTouch) (rest : InstructionAccessPlan) :
    stampPlan frontier base (touch :: rest) =
      let next := advanceFrontier frontier base touch
      let stampedRest := stampPlan next base rest
      (⟨touch, frontier touch.loc⟩ :: stampedRest.1, stampedRest.2) := rfl

/-- Stamping preserves the plan's touch data and order. -/
@[simp] theorem stampPlan_touches (frontier : AccessFrontier) (base : ℕ)
    (plan : InstructionAccessPlan) :
    (stampPlan frontier base plan).1.map StampedTouch.touch = plan := by
  induction plan generalizing frontier with
  | nil => rfl
  | cons touch rest ih => simp [stampPlan, ih]

/-- Stamping emits exactly one annotation per planned touch. -/
@[simp] theorem stampPlan_length (frontier : AccessFrontier) (base : ℕ)
    (plan : InstructionAccessPlan) :
    (stampPlan frontier base plan).1.length = plan.length := by
  induction plan generalizing frontier with
  | nil => rfl
  | cons touch rest ih => simp [stampPlan, ih]

/-- Stamping returns exactly the generic fold-update frontier. -/
theorem stampPlan_frontier (frontier : AccessFrontier) (base : ℕ)
    (plan : InstructionAccessPlan) :
    (stampPlan frontier base plan).2 = advancePlan frontier base plan := by
  induction plan generalizing frontier with
  | nil => rfl
  | cons touch rest ih => simp [stampPlan, advancePlan, ih]

/-- A location absent from a plan retains its incoming timestamp. -/
theorem advancePlan_of_not_touched {frontier : AccessFrontier} {base : ℕ}
    {plan : InstructionAccessPlan} {loc : MemLoc}
    (notTouched : ∀ touch ∈ plan, touch.loc ≠ loc) :
    advancePlan frontier base plan loc = frontier loc := by
  induction plan generalizing frontier with
  | nil => rfl
  | cons touch rest ih =>
      have headNe : loc ≠ touch.loc := (notTouched touch (by simp)).symm
      have tailNe : ∀ item ∈ rest, item.loc ≠ loc :=
        fun item member => notTouched item (List.mem_cons_of_mem touch member)
      rw [advancePlan, ih tailNe, advanceFrontier_of_ne frontier base touch headNe]

/-- The stamped frontier also leaves every untouched location unchanged. -/
theorem stampPlan_frontier_of_not_touched {frontier : AccessFrontier} {base : ℕ}
    {plan : InstructionAccessPlan} {loc : MemLoc}
    (notTouched : ∀ touch ∈ plan, touch.loc ≠ loc) :
    (stampPlan frontier base plan).2 loc = frontier loc := by
  rw [stampPlan_frontier, advancePlan_of_not_touched notTouched]

/-- The second adjacent stamp sees the first stamp when their locations alias. -/
theorem stampPlan_adjacent_alias (frontier : AccessFrontier) (base : ℕ)
    (first second : PlannedTouch) (rest : InstructionAccessPlan)
    (sameLoc : second.loc = first.loc) :
    (stampPlan frontier base (first :: second :: rest)).1.take 2 =
      [⟨first, frontier first.loc⟩, ⟨second, first.recordTime base⟩] := by
  simp [stampPlan, sameLoc, advanceFrontier]

namespace AccessFrontier

/-- The incoming frontier is earlier than every access still present in a plan. -/
def BeforePlan (frontier : AccessFrontier) (base : ℕ)
    (plan : InstructionAccessPlan) : Prop :=
  ∀ touch ∈ plan, frontier touch.loc < touch.recordTime base

/-- The simple base-clock bound implies the plan-relative bound. -/
theorem BoundedAt.beforePlan {frontier : AccessFrontier} {base : ℕ}
    {plan : InstructionAccessPlan} (bounded : frontier.BoundedAt base) :
    frontier.BeforePlan base plan := by
  intro touch _
  have positive := touch.slot.recordOffset_pos
  have := bounded touch.loc
  unfold PlannedTouch.recordTime
  omega

end AccessFrontier

/-- Advancing by the head of an ordered plan preserves the relative bound for its tail. -/
theorem beforePlan_advance {frontier : AccessFrontier} {base : ℕ}
    {touch : PlannedTouch} {rest : InstructionAccessPlan}
    (before : frontier.BeforePlan base (touch :: rest))
    (ordered : (touch :: rest).Pairwise fun left right =>
      left.slot.recordOffset < right.slot.recordOffset) :
    (advanceFrontier frontier base touch).BeforePlan base rest := by
  intro later member
  have laterBefore := before later (List.mem_cons_of_mem touch member)
  have offsetLt := (List.pairwise_cons.mp ordered).1 later member
  by_cases sameLoc : later.loc = touch.loc
  · rw [sameLoc, advanceFrontier_same]
    unfold PlannedTouch.recordTime
    omega
  · rw [advanceFrontier_of_ne frontier base touch sameLoc]
    exact laterBefore

/-- Every previous timestamp returned by stamping predates that touch's current record time. -/
theorem stampPlan_previous_lt_of_before {frontier : AccessFrontier} {base : ℕ}
    {plan : InstructionAccessPlan}
    (before : frontier.BeforePlan base plan)
    (ordered : plan.Pairwise fun left right =>
      left.slot.recordOffset < right.slot.recordOffset) :
    ∀ stamped ∈ (stampPlan frontier base plan).1,
      stamped.previous < stamped.current base := by
  induction plan generalizing frontier with
  | nil => simp [stampPlan]
  | cons touch rest ih =>
      intro stamped member
      simp only [stampPlan, List.mem_cons] at member
      rcases member with rfl | member
      · exact before touch List.mem_cons_self
      · exact ih (beforePlan_advance before ordered)
          (List.pairwise_cons.mp ordered).2 stamped member

/-- Base-clock boundedness is the public precondition for safe plan stamping. -/
theorem stampPlan_previous_lt {frontier : AccessFrontier} {base : ℕ}
    {plan : InstructionAccessPlan} (wellFormed : plan.WellFormed)
    (bounded : frontier.BoundedAt base) :
    ∀ stamped ∈ (stampPlan frontier base plan).1,
      stamped.previous < stamped.current base :=
  stampPlan_previous_lt_of_before bounded.beforePlan wellFormed.ordered

/-- The stamped touches remain strictly ordered by their current record times. -/
theorem stampPlan_current_pairwise (frontier : AccessFrontier) (base : ℕ)
    {plan : InstructionAccessPlan} (wellFormed : plan.WellFormed) :
    (stampPlan frontier base plan).1.Pairwise fun left right =>
      left.current base < right.current base := by
  induction plan generalizing frontier with
  | nil => exact List.Pairwise.nil
  | cons touch rest ih =>
      simp only [stampPlan]
      refine List.Pairwise.cons ?_
        (ih (advanceFrontier frontier base touch) wellFormed.tail)
      intro stamped member
      have touchMember : stamped.touch ∈ rest := by
        have mappedMember : stamped.touch ∈
            (stampPlan (advanceFrontier frontier base touch) base rest).1.map
              StampedTouch.touch :=
          List.mem_map_of_mem member
        rwa [stampPlan_touches] at mappedMember
      have offsetLt := (List.pairwise_cons.mp wellFormed.ordered).1 stamped.touch touchMember
      change base + touch.slot.recordOffset < base + stamped.touch.slot.recordOffset
      omega

/-- Updating within an ordinary row preserves a bound at the next eight-tick row. -/
theorem advanceFrontier_bounded_next {frontier : AccessFrontier} {base : ℕ}
    (touch : PlannedTouch) (bounded : frontier.BoundedAt (base + ordinaryClkInc)) :
    (advanceFrontier frontier base touch).BoundedAt (base + ordinaryClkInc) := by
  intro loc
  by_cases sameLoc : loc = touch.loc
  · subst loc
    rw [advanceFrontier_same]
    have offsetLe := touch.slot.recordOffset_le_four
    unfold PlannedTouch.recordTime ordinaryClkInc
    omega
  · rw [advanceFrontier_of_ne frontier base touch sameLoc]
    exact bounded loc

/-- A whole plan preserves the next-row frontier bound. -/
theorem advancePlan_bounded_next {frontier : AccessFrontier} {base : ℕ}
    (plan : InstructionAccessPlan) (bounded : frontier.BoundedAt (base + ordinaryClkInc)) :
    (advancePlan frontier base plan).BoundedAt (base + ordinaryClkInc) := by
  induction plan generalizing frontier with
  | nil => exact bounded
  | cons touch rest ih =>
      exact ih (advanceFrontier_bounded_next touch bounded)

/-- A frontier valid at this row's base is valid after stamping at the next row's base. -/
theorem stampPlan_frontier_bounded_next {frontier : AccessFrontier} {base : ℕ}
    (plan : InstructionAccessPlan) (bounded : frontier.BoundedAt base) :
    (stampPlan frontier base plan).2.BoundedAt (base + ordinaryClkInc) := by
  rw [stampPlan_frontier]
  exact advancePlan_bounded_next plan (bounded.mono (by omega))

end SP1Clean.Semantics
