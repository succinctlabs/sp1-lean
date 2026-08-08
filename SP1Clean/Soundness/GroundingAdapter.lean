import SP1Clean.Soundness.RowSoundness
import SP1Clean.Soundness.TypedTimeContracts
import SP1Clean.Soundness.AlignedCarrier
import SP1Clean.Proofs.Chips.AddChip.Contracts

/-! # The grounding adapter — `ChipKind.advance` → the timed-engine per-row records

The generic bridge from a migrated chip's `ChipKind.advance` payload to the two per-row inputs the
timed grounding engine (`Soundness/TimedGrounding.lean`) consumes: the row's `LocalStepFact` (pulled
state truth + pull currency ⟹ pushed state truth + pushed Memory truths) and its `FrameFact`
(value persistence across the row's window at every location the row does not change).

The statement-level design (validated by the SP-2 spike): the adapter needs one per-row `RowWiring`
bundle — the message ↔ `RowView` correspondences between the row's semantic bus records
(`Semantics.RowFacts`) and the view its `advance` speaks about.  Most fields are `rfl`/bound
extractions; the one genuinely load-bearing discovery is `write_push` — *the op_a write push must be
present in the row's push multiset* — a completeness-of-emission fact channel balance alone does not
force, consumed by `FrameFact`'s written-register case.

Wiring is per-reader-shape, not per-chip: `rowWiring_rtype` below discharges the whole bundle for
any R-type-adapter row from a handful of in-circuit numeric facts (the CPUState clock byte bounds,
the reader's `op_a < 32` decode bound, the write value's range check, and the chip's exact
consumed/produced Memory lists).  Add is the concrete anchor: its exact Memory emissions are
evaluated from `AddChip.exposedMemoryInteractions`, and `addRow_engineFacts` runs a genuine decoded
Add row end-to-end through the adapter. -/

open LeanRV64D.Defs

namespace SP1Clean.Soundness

open Sail LeanRV64D LeanRV64D.Functions
open Air.Flat Circuit
open SP1Clean.Soundness.Target
open SP1Clean.Soundness.TimedGrounding
open SP1Clean.Semantics
open SP1Clean.Channels (StateMsg MemoryMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## View-level State message projections -/

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- The pull message denoted by a view recombines to the view's receive-side 64-bit pc. -/
theorem pcBits_statePullOfView (view : Trace.RowView (ZMod p)) :
    StateMsg.pcBits (statePullOfView view) = rcvPcOf (stateAccess view) := by
  simp [StateMsg.pcBits, Semantics.pcBits, statePullOfView, rcvPcOf, pcBitsOfVals, stateAccess]

omit [Fact (2 ^ 17 < p)] in
/-- The push message denoted by a view recombines to the view's send-side 64-bit pc. -/
theorem pcBits_statePushOfView (view : Trace.RowView (ZMod p)) :
    StateMsg.pcBits (statePushOfView view) = sndPcOf (stateAccess view) := by
  simp [StateMsg.pcBits, Semantics.pcBits, statePushOfView, sndPcOf, pcBitsOfVals, stateAccess]

/-! ## The advance payload, named -/

/-- The proposition carried by a migrated `ChipKind.advance` field (definitionally the `PLift`
content).  Naming it lets the adapter theorems take the payload as an ordinary hypothesis. -/
def ChipKind.AdvancePayload (kind : ChipKind p) : Prop :=
  ∀ (inp : kind.Inputs (ZMod p)) (cols : kind.Cols (ZMod p)) (data : ProverData (ZMod p))
      (prog : Target.GuestProgram) (s : SailState),
    (kind.view inp cols).is_real = 1 →
    kind.chipSpec inp cols data →
    Target.SailConfigured s → Target.RomLoaded prog s →
    s.regs.get? Register.PC = some (Target.rcvPcOf (stateAccess (kind.view inp cols))) →
    Target.ValueOperandsBound (kind.view inp cols) s →
    Target.decodedInROM prog (programAccess (kind.view inp cols)).toRow →
    kind.advanceReady inp cols prog s →
    ∃ s', Target.SailStep s s' ∧ Target.RowEffect prog (kind.view inp cols) s s'

/-- Extract the named payload from a migrated registry entry. -/
theorem ChipKind.advancePayload_of_migrated {kind : ChipKind p}
    (migrated : kind.advance.isSome = true) : kind.AdvancePayload := by
  obtain ⟨payload, -⟩ := Option.isSome_iff_exists.mp migrated
  exact payload.down

/-! ## The per-row wiring bundle -/

/-- Every ordinary Memory pull carried by a row agrees with the corresponding location in the
live Sail state at the beginning of that row.  Unlike `ValueOperandsBound` and
`SourceAValueBound`, this predicate is location-generic: load/store readiness and RAM-cell update
proofs consume its RAM cases, while register-only chips may ignore it.

This is not a new assumption.  `advance_at` and `memoryPullsBound_of_grounded` derive it from the
timed grounding currency together with `RowWiring.readTime`. -/
def MemoryPullsBound (rf : Semantics.RowFacts p) (state : SailState) : Prop :=
  ∀ mp ∈ rf.memPulls,
    locContent state (MemoryMsg.locOf mp.1) = some (Word.toBitVec64 mp.1.value)

/-- The physical high timestamp component of every pulled Memory record is a genuine 24-bit
integer. SP1's generic RAM `MemoryAccess` underflow argument needs this range premise when
`compare_low = 0` (the high-limb comparison branch; the `compare_low = 1` branch consumes the
bus guarantee `MemoryMsg.ClkBound` instead); its local AIR range-checks the difference limbs but
does not independently range-check both compared high components.

This predicate is deliberately separate from semantic pull currency and from `MemoryMsg.ClkBound`
(which bounds the low component). The current native capstone receives it through an explicit
witness-wide companion relation; a future exact extracted-AIR proof may discharge that relation
from the public timestamp range checks and Memory permutation. -/
def MemoryPullTimestampHighBound (rf : Semantics.RowFacts p) : Prop :=
  ∀ mp ∈ rf.memPulls, mp.1.clk_high.val < 2 ^ 24

/-- **The per-row message ↔ view correspondence** consumed by the adapter.  `view` is the row view
the chip's `advance` payload speaks about; `rf` is the row's semantic bus record.  All time facts
are already ℕ-decoded (the field → ℕ step is the wiring producer's obligation, from the CPUState
byte bounds).  `push_classified` sorts every Memory push into a safe pre-effect read-back, one of
the register-axis roles, or a genuine RAM-cell write at `+1`; `write_push` additionally asserts the
register write push is *present* whenever the row commits a register write — the one
completeness-of-emission fact balance does not force.  `ram_frame` is the orthogonal semantic
obligation that a row preserves a RAM cell whenever all of that cell's pushes agree with its
incoming value. -/
structure RowWiring (view : Trace.RowView (ZMod p)) (rf : Semantics.RowFacts p) : Prop where
  /-- The record's state pull is the view's canonical pull message. -/
  statePull_eq : rf.statePull = statePullOfView view
  /-- The record's state push is the view's canonical push message. -/
  statePush_eq : rf.statePush = statePushOfView view
  /-- The ℕ-decoded eight-tick clock step. -/
  time8 : StateMsg.timeNat rf.statePush = StateMsg.timeNat rf.statePull + 8
  /-- Every pull is read at the row's window start (the ordinary currency point). -/
  readTime : ∀ mp ∈ rf.memPulls, mp.2 = StateMsg.timeNat rf.statePull
  /-- The adapter's `op_a` prior value is carried by an exact register pull.  Register-writing
  chips use it only to maintain the Memory permutation; Branch, Store, and `rd = x0` rows consume
  it as a genuine source operand. -/
  opA_pull : ∀ index : BitVec 5, (index.toNat : ZMod p) = view.adapter.op_a →
    ∃ mp ∈ rf.memPulls, MemoryMsg.locOf mp.1 = MemLoc.reg index ∧
      mp.1.value = view.adapter.op_a_memory.prev_value
  /-- A register `op_b` source operand is carried by one of the row's pulls. -/
  opB_pull : ∀ index : BitVec 5, view.adapter.imm_b = 0 →
    (index.toNat : ZMod p) = view.adapter.op_b[0] →
    ∃ mp ∈ rf.memPulls, MemoryMsg.locOf mp.1 = MemLoc.reg index ∧
      mp.1.value = view.adapter.op_b_memory.prev_value
  /-- A register `op_c` source operand is carried by one of the row's pulls. -/
  opC_pull : ∀ index : BitVec 5, view.adapter.imm_c = 0 →
    (index.toNat : ZMod p) = view.adapter.op_c[0] →
    ∃ mp ∈ rf.memPulls, MemoryMsg.locOf mp.1 = MemLoc.reg index ∧
      mp.1.value = view.adapter.op_c_memory.prev_value
  /-- On a register-writing row, the `op_a` write push is present in the push list. -/
  write_push : view.commit.writesReg = true →
    ∀ index : BitVec 5, (index.toNat : ZMod p) = view.adapter.op_a →
    ∃ m ∈ rf.memPushes, MemoryMsg.locOf m = MemLoc.reg index ∧ m.value = view.rdWrite
  /-- Every push is one of five shapes: a pre-effect read-back of one of the row's own pulls; the
  committed `op_a` register write at the `+ 4` effect slot (with its in-circuit range check); or —
  on a **non-writing** row — either an `op_a` read-back or the canonical zero-register value sitting
  at exactly the `+ 4` slot; or a genuine aligned RAM-cell write at `+1`.

  The third arm is not redundant.  Branch, AluX0, LoadX0 and the four stores read `op_a` as a
  *source* and re-post it unchanged at the write slot, so their pushes land at `+ 4` with
  `writesReg = false`: the first arm's strict `< t + 4` excludes them and the second arm's
  `writesReg = true` does too.  JAL/U-type rows with `rd = x0` are subtly different: their factored
  `RegisterWrite` push carries the locally zeroed result rather than the prior-read column, so the
  fourth arm records the architectural `x0 = 0` fact directly.  Both non-writing arms are justified
  by `RowEffect.regs`' pure-frame branch, not by an intra-epoch shift.

  A first-arm RAM read-back must additionally prove that the row has no RAM write; otherwise a
  store could falsely re-post its old cell value after the `+1` effect.  The fifth arm instead
  carries the chip-level read-modify-write theorem connecting the pushed full cell to the
  byte-addressed `RowEffect`. -/
  push_classified : ∀ m ∈ rf.memPushes,
    (∃ mp ∈ rf.memPulls, MemoryMsg.locOf m = MemoryMsg.locOf mp.1 ∧ m.value = mp.1.value ∧
      StateMsg.timeNat rf.statePull ≤ MemoryMsg.timeNat m ∧
      MemoryMsg.timeNat m < StateMsg.timeNat rf.statePull + 4 ∧
      (∀ cell : RamCell, MemoryMsg.locOf m = MemLoc.ram cell →
        view.commit.memWrite = none)) ∨
    (view.commit.writesReg = true ∧ MemoryMsg.isU64 m ∧
      (∃ index : BitVec 5, MemoryMsg.locOf m = MemLoc.reg index ∧
        (index.toNat : ZMod p) = view.adapter.op_a) ∧
      m.value = view.rdWrite ∧
      MemoryMsg.timeNat m = StateMsg.timeNat rf.statePull + 4) ∨
    (view.commit.writesReg = false ∧
      ∃ mp ∈ rf.memPulls, (∃ index : BitVec 5, MemoryMsg.locOf m = MemLoc.reg index) ∧
        MemoryMsg.locOf m = MemoryMsg.locOf mp.1 ∧ m.value = mp.1.value ∧
        MemoryMsg.timeNat m = StateMsg.timeNat rf.statePull + 4) ∨
    (view.commit.writesReg = false ∧ MemoryMsg.isU64 m ∧
      MemoryMsg.locOf m = MemLoc.reg 0#5 ∧ Word.toBitVec64 m.value = 0 ∧
      MemoryMsg.timeNat m = StateMsg.timeNat rf.statePull + 4) ∨
    (∃ cell : RamCell, MemoryMsg.isU64 m ∧ MemoryMsg.locOf m = MemLoc.ram cell ∧
      MemoryMsg.timeNat m = StateMsg.timeNat rf.statePull + 1 ∧
      ∀ {program : GuestProgram} {s s' : SailState},
        RowEffect program view s s' → MemoryPullsBound rf s →
          locContent s' (MemLoc.ram cell) = some (Word.toBitVec64 m.value))
  /-- Every push carries a well-formed 24-bit access timestamp — the `MemoryMsg.ClkBound` half of
  the memory channel's `Guarantees`, and the timestamp conjunct of the pushed record's
  `LocalMemTruth`.  Its producer reads it off the row's own `CPUState` clock byte bounds: every push
  sits at `clk_low + δ` with `δ ≤ 4`, so `Channels.MemoryMsg.clkBound_of_cpuState_bounds` applies.
  It is *not* derivable from `push_classified`: that arm only relates a push's decoded ℕ time to the
  window start, which says nothing about the raw field limb the channel constrains. -/
  push_clkBound : ∀ m ∈ rf.memPushes, Channels.MemoryMsg.ClkBound m
  /-- The row preserves the value of a RAM cell whenever every push to that cell agrees with the
  incoming value.  For a non-store this follows from `RowEffect.mem`'s frame branch.  For a store,
  the written cell is discharged by its fifth-arm full-cell update theorem and every other
  canonical cell by disjointness of aligned 8-byte cells. -/
  ram_frame : ∀ {program : GuestProgram} {s s' : SailState},
    RowEffect program view s s' → MemoryPullsBound rf s →
      ∀ (cell : RamCell) (v : Word (ZMod p)),
        (∀ m ∈ rf.memPushes, MemoryMsg.locOf m = MemLoc.ram cell → m.value = v) →
        locContent s (MemLoc.ram cell) = some (Word.toBitVec64 v) →
        locContent s' (MemLoc.ram cell) = some (Word.toBitVec64 v)

/-! ## Firing the payload at the pulled state -/

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- RAM words are untouched by a pointwise memory frame. -/
theorem locContent_ram_congr {s s' : SailState}
    (frame : ∀ a : ℕ, s'.mem.get? a = s.mem.get? a) (cell : RamCell) :
    locContent s' (MemLoc.ram cell) = locContent s (MemLoc.ram cell) := by
  simp only [locContent, ramWord64?, frame]

/-- Fire a chip's advance payload at the exact chain state selected by the row's pulled State
record: the pull truth supplies platform configuration, ROM presence, and the committed pc; pull
currency at the window start supplies `ValueOperandsBound` through `localValueAt_stepStart_iff`. -/
theorem RowWiring.advance_at {kind : ChipKind p}
    {inp : kind.Inputs (ZMod p)} {cols : kind.Cols (ZMod p)} {rf : Semantics.RowFacts p}
    (wiring : RowWiring (kind.view inp cols) rf) (advance : kind.AdvancePayload)
    {data : ProverData (ZMod p)} {program : GuestProgram}
    (real : (kind.view inp cols).is_real = 1)
    (spec : kind.chipSpec inp cols data)
    (decode : Target.decodedInROM program (programAccess (kind.view inp cols)).toRow)
    (ready : ∀ s : SailState, ValueOperandsBound (kind.view inp cols) s →
      SourceAValueBound (kind.view inp cols) s → MemoryPullsBound rf s →
        kind.advanceReady inp cols program s)
    {initial state : SailState} {initialClock n : ℕ}
    (chain : SailChain n initial state)
    (htime : StateMsg.timeNat rf.statePull = initialClock + 8 * n)
    (hpc : state.regs.get? Register.PC = some (StateMsg.pcBits rf.statePull))
    (hrom : RomLoaded program state) (hcfg : SailConfigured state)
    (curr : ∀ mp ∈ rf.memPulls, MemoryMsg.isU64 mp.1 ∧
      LocalValueAt initial initialClock (MemoryMsg.locOf mp.1) mp.2 mp.1.value) :
    ∃ s', SailStep state s' ∧ RowEffect program (kind.view inp cols) state s' := by
  have operands : ValueOperandsBound (kind.view inp cols) state := by
    constructor
    · intro index himm hidx
      obtain ⟨mp, hmp, hloc, hval⟩ := wiring.opB_pull index himm hidx
      have hc := (curr mp hmp).2
      rw [hloc, wiring.readTime mp hmp, htime, hval] at hc
      exact (localValueAt_stepStart_iff chain).mp hc
    · intro index himm hidx
      obtain ⟨mp, hmp, hloc, hval⟩ := wiring.opC_pull index himm hidx
      have hc := (curr mp hmp).2
      rw [hloc, wiring.readTime mp hmp, htime, hval] at hc
      exact (localValueAt_stepStart_iff chain).mp hc
  have sourceA : SourceAValueBound (kind.view inp cols) state := by
    intro index hidx
    obtain ⟨mp, hmp, hloc, hval⟩ := wiring.opA_pull index hidx
    have hc := (curr mp hmp).2
    rw [hloc, wiring.readTime mp hmp, htime, hval] at hc
    exact (localValueAt_stepStart_iff chain).mp hc
  have pulls : MemoryPullsBound rf state := by
    intro mp hmp
    have hc := (curr mp hmp).2
    rw [wiring.readTime mp hmp, htime] at hc
    exact (localValueAt_stepStart_iff chain).mp hc
  rw [wiring.statePull_eq, pcBits_statePullOfView] at hpc
  exact advance inp cols data program state real spec hcfg hrom hpc operands decode
    (ready state operands sourceA pulls)

/-- A grounded row's exact B/C pulls bind the adapter operands to the live Sail state selected by
the row's execution position.  This is the post-walk counterpart of the currency argument internal
to `advance_at`; keeping it on `RowWiring` avoids a second per-chip operand-interaction interface. -/
theorem RowWiring.valueOperandsBound_of_grounded
    {view : Trace.RowView (ZMod p)} {rf : Semantics.RowFacts p}
    (wiring : RowWiring view rf) {program : GuestProgram} {initial state : SailState}
    {initialClock steps : ℕ}
    (grounded : TimedGrounding.Grounded program initial initialClock rf)
    (chain : SailChain steps initial state)
    (rowTime : StateMsg.timeNat rf.statePull = initialClock + 8 * steps) :
    ValueOperandsBound view state := by
  constructor
  · intro index immediate indexEq
    obtain ⟨mp, hmp, location, value⟩ := wiring.opB_pull index immediate indexEq
    have current := (grounded.2 mp hmp).2
    rw [location, value, wiring.readTime mp hmp, rowTime] at current
    exact (localValueAt_stepStart_iff chain).mp current
  · intro index immediate indexEq
    obtain ⟨mp, hmp, location, value⟩ := wiring.opC_pull index immediate indexEq
    have current := (grounded.2 mp hmp).2
    rw [location, value, wiring.readTime mp hmp, rowTime] at current
    exact (localValueAt_stepStart_iff chain).mp current

/-- The same grounded-row argument binds the adapter's source-A prior value. -/
theorem RowWiring.sourceAValueBound_of_grounded
    {view : Trace.RowView (ZMod p)} {rf : Semantics.RowFacts p}
    (wiring : RowWiring view rf) {program : GuestProgram} {initial state : SailState}
    {initialClock steps : ℕ}
    (grounded : TimedGrounding.Grounded program initial initialClock rf)
    (chain : SailChain steps initial state)
    (rowTime : StateMsg.timeNat rf.statePull = initialClock + 8 * steps) :
    SourceAValueBound view state := by
  intro index indexEq
  obtain ⟨mp, hmp, location, value⟩ := wiring.opA_pull index indexEq
  have current := (grounded.2 mp hmp).2
  rw [location, value, wiring.readTime mp hmp, rowTime] at current
  exact (localValueAt_stepStart_iff chain).mp current

/-- A grounded row binds every one of its ordinary pulls — register or RAM — to the live Sail
state selected by its execution position. -/
theorem RowWiring.memoryPullsBound_of_grounded
    {view : Trace.RowView (ZMod p)} {rf : Semantics.RowFacts p}
    (wiring : RowWiring view rf) {program : GuestProgram} {initial state : SailState}
    {initialClock steps : ℕ}
    (grounded : TimedGrounding.Grounded program initial initialClock rf)
    (chain : SailChain steps initial state)
    (rowTime : StateMsg.timeNat rf.statePull = initialClock + 8 * steps) :
    MemoryPullsBound rf state := by
  intro mp hmp
  have current := (grounded.2 mp hmp).2
  rw [wiring.readTime mp hmp, rowTime] at current
  exact (localValueAt_stepStart_iff chain).mp current

/-! ## The step fact -/

/-- **The generic step fact** (SP-2's `stepFact_of_advance`): a migrated chip's `advance` payload
plus its row wiring and the row's static facts produce the timed engine's `LocalStepFact`.  The
seven register-axis crux steps: the pulled state truth selects the chain state; pull currency at the
window start gives `ValueOperandsBound`; the payload fires one real Sail step with the committed
`RowEffect`; the chain extends; the pushed state truth re-assembles at `n + 1`; read-back pushes
shift inside the pre-effect epoch; and the `op_a` write push lands at the `+ 4` effect slot of the
extended trajectory. -/
theorem stepFact_of_advance {kind : ChipKind p}
    {inp : kind.Inputs (ZMod p)} {cols : kind.Cols (ZMod p)} {rf : Semantics.RowFacts p}
    (wiring : RowWiring (kind.view inp cols) rf) (advance : kind.AdvancePayload)
    {data : ProverData (ZMod p)} {program : GuestProgram}
    (real : (kind.view inp cols).is_real = 1)
    (spec : kind.chipSpec inp cols data)
    (decode : Target.decodedInROM program (programAccess (kind.view inp cols)).toRow)
    (ready : ∀ s : SailState, ValueOperandsBound (kind.view inp cols) s →
      SourceAValueBound (kind.view inp cols) s → MemoryPullsBound rf s →
        kind.advanceReady inp cols program s)
    (initial : SailState) (initialClock : ℕ)
    (codeMemoryCompatible : SailCodeMemoryCompatible program initial)
    (hpull : LocalStateTruth program initial initialClock rf.statePull)
    (hcurr : ∀ mp ∈ rf.memPulls, SP1Clean.Channels.MemoryMsg.isU64 mp.1 ∧
      LocalValueAt initial initialClock (MemoryMsg.locOf mp.1) mp.2 mp.1.value) :
    LocalStateTruth program initial initialClock rf.statePush ∧
      (∀ message ∈ rf.memPushes, LocalMemTruth initial initialClock message) := by
  obtain ⟨n, state, chain, htime, hpc, hrom, hcfg⟩ := hpull
  have hpull' : LocalStateTruth program initial initialClock rf.statePull :=
    ⟨n, state, chain, htime, hpc, hrom, hcfg⟩
  obtain ⟨s', hstep, heff⟩ :=
    wiring.advance_at advance real spec decode ready chain htime hpc hrom hcfg hcurr
  have chain' : SailChain (n + 1) initial s' := chain.snoc hstep
  have hcs : chainState initial n = some state := chainState_of_sailChain chain
  have hcs' : chainState initial (n + 1) = some s' :=
    chainState_succ_of hcs (stepOnce_of_sailStep hstep)
  have hpulls : MemoryPullsBound rf state := by
    intro mp hmp
    have hc := (hcurr mp hmp).2
    rw [wiring.readTime mp hmp, htime] at hc
    exact (localValueAt_stepStart_iff chain).mp hc
  refine ⟨?_, ?_⟩
  · -- the pushed state truth, one window later
    refine localStateTruth_of_sailChain chain' ?_ ?_
      (codeMemoryCompatible chain hstep hrom) (heff.cfg hcfg)
    · rw [wiring.time8, htime]
      omega
    · rw [wiring.statePush_eq, pcBits_statePushOfView]
      exact heff.pc
  · -- every pushed Memory record is true
    intro m hm
    rcases wiring.push_classified m hm with
      ⟨mp, hmp, hloc, hval, hlo, hhi, hramSafe⟩ |
      ⟨hw, hu64, ⟨idx, hlocw, hidx⟩, hvalw, htw⟩ |
      ⟨hnw, mp, hmp, ⟨idx, hlocr⟩, hloc, hval, htr⟩ |
      ⟨_hnw, hu64, hloc, hzero, htimeZero⟩ |
      ⟨cell, hu64, hloc, htimeRam, hpost⟩
    · -- read-back: the pull's currency, shifted inside the pre-effect epoch
      have hc := (hcurr mp hmp).2
      rw [wiring.readTime mp hmp] at hc
      have hu : MemoryMsg.isU64 m := by
        show Word.isU64 m.value
        rw [hval]
        exact (hcurr mp hmp).1
      refine ⟨hu, wiring.push_clkBound m hm, ?_⟩
      rw [hloc, hval]
      cases hlocmp : MemoryMsg.locOf mp.1 with
      | reg i =>
        rw [hlocmp] at hc
        exact localValueAt_shift hpull' (Or.inl ⟨le_refl _, by omega, hlo, hhi⟩) hc
      | ram a =>
        rw [hlocmp] at hc
        by_cases heq : MemoryMsg.timeNat m = StateMsg.timeNat rf.statePull
        · rw [heq]
          exact hc
        · unfold LocalValueAt at hc ⊢
          rw [microValue_ram] at hc ⊢
          rw [htime] at hc
          rw [ramEpoch_eq_of (n := n) (by omega) (by omega), hcs] at hc
          rw [ramEpoch_eq_succ_of (n := n) (by omega) (by omega), hcs']
          show locContent s' (MemLoc.ram a) = some (Word.toBitVec64 mp.1.value)
          rw [locContent_ram_congr (heff.mem.1 (hramSafe a (hloc.trans hlocmp))) a]
          exact hc
    · -- the op_a write: the new register value at the `+ 4` effect slot
      refine ⟨hu64, wiring.push_clkBound m hm, ?_⟩
      rw [hlocw, hvalw, htw, htime]
      unfold LocalValueAt
      rw [microValue_reg, regEpoch_eq_succ_of (n := n) (by omega) (by omega), hcs']
      show locContent s' (MemLoc.reg idx) = some (Word.toBitVec64 (kind.view inp cols).rdWrite)
      have hregs := heff.regs
      rw [if_pos hw] at hregs
      exact hregs.1 idx hidx
    · -- a non-writing row's `op_a` read-back at the `+ 4` slot: the row changes no register, so the
      -- post-state content is still the pulled prior value.
      have hlocmp : MemoryMsg.locOf mp.1 = MemLoc.reg idx := hloc.symm.trans hlocr
      have hc := (hcurr mp hmp).2
      rw [wiring.readTime mp hmp, hlocmp] at hc
      have hu : MemoryMsg.isU64 m := by
        show Word.isU64 m.value
        rw [hval]
        exact (hcurr mp hmp).1
      refine ⟨hu, wiring.push_clkBound m hm, ?_⟩
      rw [hlocr, hval, htr, htime]
      unfold LocalValueAt
      rw [microValue_reg, regEpoch_eq_succ_of (n := n) (by omega) (by omega), hcs']
      show locContent s' (MemLoc.reg idx) = some (Word.toBitVec64 mp.1.value)
      have hregs := heff.regs
      rw [if_neg (by simp [hnw])] at hregs
      have hframe : locContent s' (MemLoc.reg idx) = locContent state (MemLoc.reg idx) :=
        hregs idx
      rw [hframe]
      unfold LocalValueAt at hc
      rw [microValue_reg, htime, regEpoch_eq_of (n := n) (by omega) (by omega), hcs] at hc
      exact hc
    · -- A factored destination push on an `rd = x0` row carries the locally zeroed result rather
      -- than the prior-read column.  The architectural register view defines x0 to be zero in every
      -- state, so this is true at the post-effect slot independently of the backing Sail map.
      refine ⟨hu64, wiring.push_clkBound m hm, ?_⟩
      rw [hloc, htimeZero, htime]
      unfold LocalValueAt
      rw [microValue_reg, regEpoch_eq_succ_of (n := n) (by omega) (by omega), hcs']
      simp [locContent, SailState.get_reg?, hzero]
    · -- A genuine RAM write: the fifth-arm chip theorem identifies the full pushed cell with the
      -- byte-addressed post-state at SP1's `+1` RAM effect slot.
      refine ⟨hu64, wiring.push_clkBound m hm, ?_⟩
      rw [hloc, htimeRam, htime]
      unfold LocalValueAt
      rw [microValue_ram, ramEpoch_eq_succ_of (n := n) (by omega) (by omega), hcs']
      exact hpost heff hpulls

/-! ## The frame fact -/

/-- **The generic frame fact** (SP-2's `frameFact_of_advance`): under the same hypotheses, the
`RowEffect`'s frame halves advance any untouched location's value across the row's window — both
`writesReg` cases on the register axis, and the pointwise memory frame on the RAM axis. -/
theorem frameFact_of_advance {kind : ChipKind p}
    {inp : kind.Inputs (ZMod p)} {cols : kind.Cols (ZMod p)} {rf : Semantics.RowFacts p}
    (wiring : RowWiring (kind.view inp cols) rf) (advance : kind.AdvancePayload)
    {data : ProverData (ZMod p)} {program : GuestProgram}
    (real : (kind.view inp cols).is_real = 1)
    (spec : kind.chipSpec inp cols data)
    (decode : Target.decodedInROM program (programAccess (kind.view inp cols)).toRow)
    (ready : ∀ s : SailState, ValueOperandsBound (kind.view inp cols) s →
      SourceAValueBound (kind.view inp cols) s → MemoryPullsBound rf s →
        kind.advanceReady inp cols program s)
    (initial : SailState) (initialClock : ℕ)
    (hpull : LocalStateTruth program initial initialClock rf.statePull)
    (hcurr : ∀ mp ∈ rf.memPulls, SP1Clean.Channels.MemoryMsg.isU64 mp.1 ∧
      LocalValueAt initial initialClock (MemoryMsg.locOf mp.1) mp.2 mp.1.value)
    (loc : MemLoc) (v : Word (ZMod p))
    (hpush : ∀ m ∈ rf.memPushes, MemoryMsg.locOf m = loc → m.value = v)
    (hval : LocalValueAt initial initialClock loc (StateMsg.timeNat rf.statePull) v) :
    LocalValueAt initial initialClock loc (StateMsg.timeNat rf.statePush) v := by
  obtain ⟨n, state, chain, htime, hpc, hrom, hcfg⟩ := hpull
  obtain ⟨s', hstep, heff⟩ :=
    wiring.advance_at advance real spec decode ready chain htime hpc hrom hcfg hcurr
  have chain' : SailChain (n + 1) initial s' := chain.snoc hstep
  rw [htime] at hval
  have hcontent : locContent state loc = some (Word.toBitVec64 v) :=
    (localValueAt_stepStart_iff chain).mp hval
  have hpulls : MemoryPullsBound rf state := by
    intro mp hmp
    have hc := (hcurr mp hmp).2
    rw [wiring.readTime mp hmp, htime] at hc
    exact (localValueAt_stepStart_iff chain).mp hc
  have hpushTime : StateMsg.timeNat rf.statePush = initialClock + 8 * (n + 1) := by
    rw [wiring.time8, htime]
    omega
  rw [hpushTime]
  apply (localValueAt_stepStart_iff chain').mpr
  cases loc with
  | ram cell =>
    exact wiring.ram_frame heff hpulls cell v hpush hcontent
  | reg i =>
    show s'.get_reg? i = some (Word.toBitVec64 v)
    have hregs := heff.regs
    by_cases hw : (kind.view inp cols).commit.writesReg = true
    · rw [if_pos hw] at hregs
      by_cases hop : (i.toNat : ZMod p) = (kind.view inp cols).adapter.op_a
      · -- the written register: the pushed write value is pinned to `v` by `hpush`
        obtain ⟨m, hm, hlocm, hvalm⟩ := wiring.write_push hw i hop
        have hveq : m.value = v := hpush m hm hlocm
        rw [hregs.1 i hop, ← hvalm, hveq]
      · rw [hregs.2 i hop]
        exact hcontent
    · rw [if_neg hw] at hregs
      rw [hregs i]
      exact hcontent

/-! ## The dispatcher over the heterogeneous row -/

/-- **The dispatcher-shaped composite** (SP-2's `engineFacts_of_kind`): any migrated registry row
with its wiring and static facts yields both engine records at once. -/
theorem engineFacts_of_kind {row : ChipRow p} {rf : Semantics.RowFacts p}
    (migrated : row.kind.advance.isSome = true)
    {data : ProverData (ZMod p)} {program : GuestProgram}
    (real : row.is_real = 1)
    (decode : Target.decodedInROM program (programAccess row.view).toRow)
    (initial : SailState) (initialClock : ℕ)
    (wiringOf : (∀ mp ∈ rf.memPulls, SP1Clean.Channels.MemoryMsg.isU64 mp.1 ∧
        SP1Clean.Channels.MemoryMsg.ClkBound mp.1 ∧
        LocalValueAt initial initialClock (MemoryMsg.locOf mp.1) mp.2 mp.1.value) →
      RowWiring row.view rf)
    (specOf : (∀ mp ∈ rf.memPulls, SP1Clean.Channels.MemoryMsg.isU64 mp.1 ∧
        SP1Clean.Channels.MemoryMsg.ClkBound mp.1 ∧
        LocalValueAt initial initialClock (MemoryMsg.locOf mp.1) mp.2 mp.1.value) →
      row.chipSpec data)
    (readyOf : ∀ _hcurr : (∀ mp ∈ rf.memPulls,
        SP1Clean.Channels.MemoryMsg.isU64 mp.1 ∧
          SP1Clean.Channels.MemoryMsg.ClkBound mp.1 ∧
          LocalValueAt initial initialClock (MemoryMsg.locOf mp.1) mp.2 mp.1.value),
      ∀ s : SailState, ValueOperandsBound row.view s → SourceAValueBound row.view s →
        MemoryPullsBound rf s → row.kind.advanceReady row.inputs row.cols program s)
    (codeMemoryCompatible : SailCodeMemoryCompatible program initial) :
    LocalStepFact program initial initialClock rf ∧
      FrameFact program initial initialClock rf := by
  have advance := ChipKind.advancePayload_of_migrated migrated
  refine ⟨?_, ?_⟩
  · intro hpull hcurr
    exact stepFact_of_advance (wiringOf hcurr) advance real (specOf hcurr) decode
      (readyOf hcurr) initial initialClock codeMemoryCompatible hpull
      (fun mp hmp => ⟨(hcurr mp hmp).1, (hcurr mp hmp).2.2⟩)
  · intro hpull hcurr loc v hpush hval
    exact frameFact_of_advance (wiringOf hcurr) advance real (specOf hcurr) decode
      (readyOf hcurr) initial
      initialClock hpull (fun mp hmp => ⟨(hcurr mp hmp).1, (hcurr mp hmp).2.2⟩) loc v hpush hval

/-! ## The R-type reader-shape wiring

Everything below is the first reader-shape batch: the field → ℕ decoding of the intra-row effect
slots (`+ 2` / `+ 3` / `+ 4` / `+ 8`, from the CPUState clock byte bounds), the canonical R-type
Memory message shapes, and `rowWiring_rtype` — the whole `RowWiring` bundle from those numeric
facts.  The i-type/load/store shapes are later batches. -/

section RType

variable [Fact (2 ^ 25 < p)]

omit [Fact (2 ^ 17 < p)] in
/-- The two CPUState byte bounds decode any small field clock increment as an exact ℕ increment —
the `+ 2`/`+ 3`/`+ 4` effect-slot generalization of
`TimeExtraction.clkNat_add_eight_of_cpuState_bounds`. -/
theorem clkNat_add_delta_of_cpuState_bounds (clkHigh clk0 clk1 delta : ZMod p) (k : ℕ)
    (hdelta : delta.val = k) (hk : k ≤ 8)
    (clk0Bound : ((clk0 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13)
    (clk1Bound : clk1.val < 2 ^ 8) :
    clkNat clkHigh (clk0 + clk1 * 65536 + delta) =
      clkNat clkHigh (clk0 + clk1 * 65536) + k := by
  let scaled := (clk0 - 1) * (8 : ZMod p)⁻¹
  have eightNe : (8 : ZMod p) ≠ 0 := val_8_ne_zero
  have scaledBound : scaled.val < 2 ^ 13 := clk0Bound
  have reconstruct : scaled * 8 + 1 = clk0 := by
    dsimp only [scaled]
    rw [mul_assoc, inv_mul_cancel₀ eightNe, mul_one]
    ring_nf
  have scaledMulLt : scaled.val * (8 : ZMod p).val < p := by
    rw [val_8_zmod_p]
    have := Fact.out (p := 2 ^ 25 < p)
    omega
  have scaledMulVal : (scaled * 8).val = scaled.val * 8 := by
    rw [ZMod.val_mul_of_lt scaledMulLt, val_8_zmod_p]
  have clk0AddLt : (scaled * 8).val + (1 : ZMod p).val < p := by
    rw [scaledMulVal, ZMod.val_one]
    have := Fact.out (p := 2 ^ 25 < p)
    omega
  have clk0Val : clk0.val = scaled.val * 8 + 1 := by
    calc
      clk0.val = (scaled * 8 + 1).val := congrArg ZMod.val reconstruct.symm
      _ = (scaled * 8).val + (1 : ZMod p).val := ZMod.val_add_of_lt clk0AddLt
      _ = scaled.val * 8 + 1 := by rw [scaledMulVal, ZMod.val_one]
  have highLimbMulLt : clk1.val * (65536 : ZMod p).val < p := by
    rw [val_65536_zmod_p]
    have := Fact.out (p := 2 ^ 25 < p)
    omega
  have highLimbVal : (clk1 * 65536).val = clk1.val * 65536 := by
    rw [ZMod.val_mul_of_lt highLimbMulLt, val_65536_zmod_p]
  have lowAddLt : clk0.val + (clk1 * 65536).val < p := by
    rw [clk0Val, highLimbVal]
    have := Fact.out (p := 2 ^ 25 < p)
    omega
  have lowVal : (clk0 + clk1 * 65536).val = clk0.val + clk1.val * 65536 := by
    rw [ZMod.val_add_of_lt lowAddLt, highLimbVal]
  have incrementAddLt : (clk0 + clk1 * 65536).val + delta.val < p := by
    rw [lowVal, clk0Val, hdelta]
    have := Fact.out (p := 2 ^ 25 < p)
    omega
  have incrementedVal : (clk0 + clk1 * 65536 + delta).val =
      (clk0 + clk1 * 65536).val + k := by
    rw [ZMod.val_add_of_lt incrementAddLt, hdelta]
  simp only [clkNat, incrementedVal]
  omega

/-- The two CPUState clock byte bounds, bound to a row view's committed state block. -/
structure ViewClockBounds (view : Trace.RowView (ZMod p)) : Prop where
  clk0 : ((view.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13
  clk1 : view.state.clk_16_24.val < 2 ^ 8

/-- A retained `CPUState` reader plus the finished Byte guarantees bound the completed chip's view
clock limbs — the raw-bounds companion of `circuitStateTimeStep_of_cpuStateContract`, feeding the
`+ 2`/`+ 3`/`+ 4` effect-slot decodes that the eight-tick theorem does not expose. -/
theorem viewClockBounds_of_cpuStateContract {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p))
    (contract : CircuitCPUStateTimeContract circuit view)
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (guarantees : (⟨circuit⟩ : Component (ZMod p)).operations.ChannelGuarantees
      Channels.byteChannel.toRaw (Environment.fromArray physical data))
    (real : (view ((⟨circuit⟩ : Component (ZMod p)).rowInput (Environment.fromArray physical data))
      ((⟨circuit⟩ : Component (ZMod p)).rowOutput (Environment.fromArray physical data))).is_real
        = 1) :
    ViewClockBounds (view
      ((⟨circuit⟩ : Component (ZMod p)).rowInput (Environment.fromArray physical data))
      ((⟨circuit⟩ : Component (ZMod p)).rowOutput (Environment.fromArray physical data))) := by
  unfold CircuitCPUStateTimeContract at contract
  dsimp only at contract
  obtain ⟨cpuOffset, cpuInput, cpuMem, binding⟩ := contract
  set component : Component (ZMod p) := ⟨circuit⟩ with hcomponent
  set env := Environment.fromArray physical data with henv
  have rowGuarantees : component.rowOperations.ChannelGuarantees Channels.byteChannel.toRaw env :=
    (Component.channelGuarantees_iff env Channels.byteChannel.toRaw).mp guarantees
  have cpuGuarantees := channelGuarantees_subcircuit_of_mem Channels.byteChannel.toRaw env
    component.rowOperations
    ((Readers.CPUState.circuit (p := p)).toSubcircuit cpuOffset cpuInput) cpuMem rowGuarantees
  have inputEq : Eval.eval env (varFromOffset Input 0) = component.rowInput env :=
    eval_varFromOffset_valueFromOffset Input 0 env
  have outputEq : Eval.eval env (circuit.output (varFromOffset Input 0) (size Input)) =
      component.rowOutput env := by
    simp only [component, Component.rowOutput, circuit_norm]
  have bound := binding env
  rw [inputEq, outputEq] at bound
  have cpuReal : Expression.eval env cpuInput.is_real = 1 := bound.real_eq.trans real
  obtain ⟨clk0Bound, clk1Bound⟩ :=
    Readers.CPUState.bounds_of_byteGuarantees cpuInput cpuOffset env cpuGuarantees cpuReal
  constructor
  · rw [← bound.clk0_eq]
    exact clk0Bound
  · rw [← bound.clk1_eq]
    exact clk1Bound

/-! ### The canonical R-type Memory message shapes -/

omit [Fact (2 ^ 17 < p)] in
/-- `(3 : ZMod p)` decodes as the natural number 3 (the op_b read-back effect slot). -/
lemma val_3_zmod_p : (3 : ZMod p).val = 3 := by
  have : (2 ^ 25 : ℕ) < p := Fact.out
  exact ZMod.val_natCast_of_lt (show (3 : ℕ) < p by omega)

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
/-- The read-prior pull message an R-type register slot consumes. -/
def rtypePriorMessage (view : Trace.RowView (ZMod p)) (index : ZMod p)
    (access : Extracted.RegisterAccessCols (ZMod p)) : MemoryMsg (ZMod p) :=
  ⟨view.state.clk_high, access.access_timestamp.prev_low, index, 0, 0, access.prev_value⟩

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
/-- The read-back push message an R-type register slot produces at effect offset `delta`. -/
def rtypeReadBackMessage (view : Trace.RowView (ZMod p)) (index : ZMod p)
    (access : Extracted.RegisterAccessCols (ZMod p)) (delta : ZMod p) : MemoryMsg (ZMod p) :=
  ⟨view.state.clk_high, view.state.clk_0_16 + view.state.clk_16_24 * 65536 + delta,
   index, 0, 0, access.prev_value⟩

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
/-- The committed `op_a` register-write push message at the `+ 4` effect slot. -/
def rtypeWriteMessage (view : Trace.RowView (ZMod p)) : MemoryMsg (ZMod p) :=
  ⟨view.state.clk_high, view.state.clk_0_16 + view.state.clk_16_24 * 65536 + 4,
   view.adapter.op_a, 0, 0, view.rdWrite⟩

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
/-- A read-prior pull's low clock is the pulled record's timestamp `prev_low` — a `rfl` unfolding of
the message projection, so a decoded-row goal can be rewritten to the symbolic operand spelling before
crossing to the reader `Spec` (avoiding the `.clk_low`-of-message whnf blowup on the decoded view). -/
theorem clk_low_rtypePriorMessage (view : Trace.RowView (ZMod p)) (index : ZMod p)
    (access : Extracted.RegisterAccessCols (ZMod p)) :
    (rtypePriorMessage view index access).clk_low = access.access_timestamp.prev_low := rfl

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
/-- A read-back push's low clock is the window start plus its effect offset — the symbolic spelling. -/
theorem clk_low_rtypeReadBackMessage (view : Trace.RowView (ZMod p)) (index : ZMod p)
    (access : Extracted.RegisterAccessCols (ZMod p)) (delta : ZMod p) :
    (rtypeReadBackMessage view index access delta).clk_low
      = view.state.clk_0_16 + view.state.clk_16_24 * 65536 + delta := rfl

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
/-- The op_a write push's low clock is the window start plus four — the symbolic spelling. -/
theorem clk_low_rtypeWriteMessage (view : Trace.RowView (ZMod p)) :
    (rtypeWriteMessage view).clk_low
      = view.state.clk_0_16 + view.state.clk_16_24 * 65536 + 4 := rfl

omit [Fact (2 ^ 17 < p)] in
/-- A read-back push's decoded time is the window start plus its effect offset. -/
theorem timeNat_rtypeReadBackMessage {view : Trace.RowView (ZMod p)}
    (bounds : ViewClockBounds view) (index : ZMod p)
    (access : Extracted.RegisterAccessCols (ZMod p)) {delta : ZMod p} {k : ℕ}
    (hdelta : delta.val = k) (hk : k ≤ 8) :
    MemoryMsg.timeNat (rtypeReadBackMessage view index access delta) =
      StateMsg.timeNat (statePullOfView view) + k :=
  clkNat_add_delta_of_cpuState_bounds _ _ _ _ k hdelta hk bounds.clk0 bounds.clk1

omit [Fact (2 ^ 17 < p)] in
/-- The `op_a` write push's decoded time is the window start plus four. -/
theorem timeNat_rtypeWriteMessage {view : Trace.RowView (ZMod p)}
    (bounds : ViewClockBounds view) :
    MemoryMsg.timeNat (rtypeWriteMessage view) =
      StateMsg.timeNat (statePullOfView view) + 4 :=
  clkNat_add_delta_of_cpuState_bounds _ _ _ _ 4 val_4_zmod_p (by omega) bounds.clk0 bounds.clk1

omit [Fact (2 ^ 17 < p)] in
/-- The view's state push decodes exactly eight ticks after its state pull. -/
theorem timeNat_statePushOfView_eight {view : Trace.RowView (ZMod p)}
    (bounds : ViewClockBounds view) :
    StateMsg.timeNat (statePushOfView view) = StateMsg.timeNat (statePullOfView view) + 8 :=
  clkNat_add_delta_of_cpuState_bounds _ _ _ _ 8 val_8_zmod_p (le_refl 8) bounds.clk0 bounds.clk1

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
/-- A register index below 32 round-trips through its canonical five-bit encoding. -/
private theorem registerIndexCast (x : ZMod p) (bound : x.val < 32) :
    ((BitVec.ofNat 5 x.val).toNat : ZMod p) = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show x.val < 2 ^ 5 by omega)]
  exact ZMod.natCast_zmod_val _

omit [Fact (2 ^ 25 < p)] in
/-- The Memory key of a read-prior pull is the canonical register location of its index. -/
private theorem locOf_rtypePriorMessage (view : Trace.RowView (ZMod p)) (x : ZMod p)
    (access : Extracted.RegisterAccessCols (ZMod p)) (bound : x.val < 32) :
    MemoryMsg.locOf (rtypePriorMessage view x access) = MemLoc.reg (BitVec.ofNat 5 x.val) :=
  MemoryMsg.locOf_register _ _ (registerIndexCast x bound) rfl rfl

omit [Fact (2 ^ 25 < p)] in
/-- The Memory key of a read-back push, at any effect offset. -/
private theorem locOf_rtypeReadBackMessage (view : Trace.RowView (ZMod p)) (x : ZMod p)
    (access : Extracted.RegisterAccessCols (ZMod p)) (delta : ZMod p) (bound : x.val < 32) :
    MemoryMsg.locOf (rtypeReadBackMessage view x access delta) =
      MemLoc.reg (BitVec.ofNat 5 x.val) :=
  MemoryMsg.locOf_register _ _ (registerIndexCast x bound) rfl rfl

omit [Fact (2 ^ 25 < p)] in
/-- The Memory key of the committed `op_a` write push. -/
private theorem locOf_rtypeWriteMessage (view : Trace.RowView (ZMod p))
    (bound : view.adapter.op_a.val < 32) :
    MemoryMsg.locOf (rtypeWriteMessage view) =
      MemLoc.reg (BitVec.ofNat 5 view.adapter.op_a.val) :=
  MemoryMsg.locOf_register _ _ (registerIndexCast _ bound) rfl rfl

/-- Split a membership hypothesis against one of the exact three-element `memPulls`/`memPushes`
lists below.  The `rfl` patterns are built with `mkIdent`: a quotation-local `rfl` is renamed by
hygiene and would then bind a *name* instead of substituting. -/
local macro "threeElementCases " h:ident ", " listEq:term : tactic => do
  let rfl' := Lean.mkIdent `rfl
  `(tactic| (
    rw [$listEq:term] at $h:ident
    simp only [List.mem_cons, List.not_mem_nil, or_false] at $h:ident
    rcases $h:ident with $rfl':ident | $rfl':ident | $rfl':ident))

/-! ### The R-type wiring bundle -/

/-- **The R-type reader-shape wiring** (SP-2's `rowWiring_rtype`): for any row whose semantic bus
record has the canonical R-type shape — three read-prior pulls at the window start, two read-backs
at `+ 3`/`+ 2`, and the `op_a` write at `+ 4` — the whole `RowWiring` bundle follows from the
CPUState clock byte bounds, the reader's `op_a < 32` decode bound, and the write value's range
check.  No `op_b`/`op_c` register-index bound is needed: a read-back push re-asserts its own pull's
location and value, and the adapter's step fact handles both location kinds. -/
theorem rowWiring_rtype {view : Trace.RowView (ZMod p)} {rf : Semantics.RowFacts p}
    (bounds : ViewClockBounds view)
    (commit_eq : view.commit = Trace.CommitEffect.regWrite)
    (opa_lt : view.adapter.op_a.val < 32)
    (write_isU64 : Word.isU64 view.rdWrite)
    (statePull_eq : rf.statePull = statePullOfView view)
    (statePush_eq : rf.statePush = statePushOfView view)
    (pulls_eq : rf.memPulls =
      [(rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
          StateMsg.timeNat rf.statePull),
       (rtypePriorMessage view (view.adapter.op_b[0]) view.adapter.op_b_memory,
          StateMsg.timeNat rf.statePull),
       (rtypePriorMessage view (view.adapter.op_c[0]) view.adapter.op_c_memory,
          StateMsg.timeNat rf.statePull)])
    (pushes_eq : rf.memPushes =
      [rtypeReadBackMessage view (view.adapter.op_b[0]) view.adapter.op_b_memory 3,
       rtypeReadBackMessage view (view.adapter.op_c[0]) view.adapter.op_c_memory 2,
       rtypeWriteMessage view]) :
    RowWiring view rf where
  statePull_eq := statePull_eq
  statePush_eq := statePush_eq
  time8 := by
    rw [statePull_eq, statePush_eq]
    exact timeNat_statePushOfView_eight bounds
  readTime := by
    intro mp hmp
    threeElementCases hmp, pulls_eq <;> rfl
  opA_pull := by
    intro index hidx
    refine ⟨(rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
      StateMsg.timeNat rf.statePull), ?_, ?_, rfl⟩
    · rw [pulls_eq]
      exact List.mem_cons_self
    · exact MemoryMsg.locOf_register _ index hidx rfl rfl
  opB_pull := by
    intro index himm hidx
    refine ⟨(rtypePriorMessage view (view.adapter.op_b[0]) view.adapter.op_b_memory,
      StateMsg.timeNat rf.statePull), ?_, ?_, rfl⟩
    · rw [pulls_eq]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact MemoryMsg.locOf_register _ index hidx rfl rfl
  opC_pull := by
    intro index himm hidx
    refine ⟨(rtypePriorMessage view (view.adapter.op_c[0]) view.adapter.op_c_memory,
      StateMsg.timeNat rf.statePull), ?_, ?_, rfl⟩
    · rw [pulls_eq]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact MemoryMsg.locOf_register _ index hidx rfl rfl
  write_push := by
    intro _ index hidx
    refine ⟨rtypeWriteMessage view, ?_, ?_, rfl⟩
    · rw [pushes_eq]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact MemoryMsg.locOf_register _ index hidx rfl rfl
  push_classified := by
    intro m hm
    threeElementCases hm, pushes_eq
    · -- the op_b read-back at `+ 3`
      left
      refine ⟨(rtypePriorMessage view (view.adapter.op_b[0]) view.adapter.op_b_memory,
        StateMsg.timeNat rf.statePull), ?_, rfl, rfl, ?_, ?_, ?_⟩
      · rw [pulls_eq]
        exact List.mem_cons_of_mem _ List.mem_cons_self
      · rw [timeNat_rtypeReadBackMessage bounds _ _ val_3_zmod_p (by omega), ← statePull_eq]
        omega
      · rw [timeNat_rtypeReadBackMessage bounds _ _ val_3_zmod_p (by omega), ← statePull_eq]
        omega
      · intro _ _
        rw [commit_eq]
        rfl
    · -- the op_c read-back at `+ 2`
      left
      refine ⟨(rtypePriorMessage view (view.adapter.op_c[0]) view.adapter.op_c_memory,
        StateMsg.timeNat rf.statePull), ?_, rfl, rfl, ?_, ?_, ?_⟩
      · rw [pulls_eq]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
      · rw [timeNat_rtypeReadBackMessage bounds _ _ val_2_zmod_p (by omega), ← statePull_eq]
        omega
      · rw [timeNat_rtypeReadBackMessage bounds _ _ val_2_zmod_p (by omega), ← statePull_eq]
        omega
      · intro _ _
        rw [commit_eq]
        rfl
    · -- the op_a write at `+ 4` (the middle arm: this is a register-writing R-type row)
      refine Or.inr (Or.inl ?_)
      have hidx := registerIndexCast _ opa_lt
      refine ⟨by rw [commit_eq]; rfl, write_isU64, ?_, rfl, ?_⟩
      · exact ⟨BitVec.ofNat 5 view.adapter.op_a.val, locOf_rtypeWriteMessage view opa_lt, hidx⟩
      · rw [timeNat_rtypeWriteMessage bounds, ← statePull_eq]
  push_clkBound := by
    intro m hm
    -- each push sits at `clk_0_16 + clk_16_24 * 65536 + δ` with `δ ∈ {3, 2, 4}`
    threeElementCases hm, pushes_eq
    · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 3 val_3_zmod_p (by omega)
        bounds.clk0 bounds.clk1
    · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 2 val_2_zmod_p (by omega)
        bounds.clk0 bounds.clk1
    · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 4 val_4_zmod_p (by omega)
        bounds.clk0 bounds.clk1
  ram_frame := by
    intro program s s' heff _ cell v _ hcontent
    rw [locContent_ram_congr (heff.mem.1 (by rw [commit_eq]; rfl)) cell]
    exact hcontent

/-! ### The immutable R-type wiring bundle -/

/-- The no-write R-type sibling of `rowWiring_rtype`. All three register slots are sources and are
read back unchanged at `+4`, `+3`, and `+2`; in particular, the `op_a` message at the architectural
write slot is a genuine read-back rather than a destination write. -/
theorem rowWiring_immutableRtype {view : Trace.RowView (ZMod p)}
    {rf : Semantics.RowFacts p}
    (bounds : ViewClockBounds view)
    (commit_eq : view.commit = Trace.CommitEffect.noWrite)
    (opa_lt : view.adapter.op_a.val < 32)
    (statePull_eq : rf.statePull = statePullOfView view)
    (statePush_eq : rf.statePush = statePushOfView view)
    (pulls_eq : rf.memPulls =
      [(rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
          StateMsg.timeNat rf.statePull),
       (rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory,
          StateMsg.timeNat rf.statePull),
       (rtypePriorMessage view view.adapter.op_c[0] view.adapter.op_c_memory,
          StateMsg.timeNat rf.statePull)])
    (pushes_eq : rf.memPushes =
      [rtypeReadBackMessage view view.adapter.op_a view.adapter.op_a_memory 4,
       rtypeReadBackMessage view view.adapter.op_b[0] view.adapter.op_b_memory 3,
       rtypeReadBackMessage view view.adapter.op_c[0] view.adapter.op_c_memory 2]) :
    RowWiring view rf where
  statePull_eq := statePull_eq
  statePush_eq := statePush_eq
  time8 := by
    rw [statePull_eq, statePush_eq]
    exact timeNat_statePushOfView_eight bounds
  readTime := by
    intro mp hmp
    threeElementCases hmp, pulls_eq <;> rfl
  opA_pull := by
    intro index indexEq
    refine ⟨(rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
      StateMsg.timeNat rf.statePull), ?_, ?_, rfl⟩
    · rw [pulls_eq]
      exact List.mem_cons_self
    · exact MemoryMsg.locOf_register _ index indexEq rfl rfl
  opB_pull := by
    intro index _immediate indexEq
    refine ⟨(rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory,
      StateMsg.timeNat rf.statePull), ?_, ?_, rfl⟩
    · rw [pulls_eq]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact MemoryMsg.locOf_register _ index indexEq rfl rfl
  opC_pull := by
    intro index _immediate indexEq
    refine ⟨(rtypePriorMessage view view.adapter.op_c[0] view.adapter.op_c_memory,
      StateMsg.timeNat rf.statePull), ?_, ?_, rfl⟩
    · rw [pulls_eq]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact MemoryMsg.locOf_register _ index indexEq rfl rfl
  write_push := by
    intro writes
    rw [commit_eq] at writes
    exact Bool.noConfusion writes
  push_classified := by
    intro message messageMem
    threeElementCases messageMem, pushes_eq
    · refine Or.inr (Or.inr (Or.inl ?_))
      refine ⟨by rw [commit_eq]; rfl,
        (rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
          StateMsg.timeNat rf.statePull), ?_, ?_, rfl, rfl, ?_⟩
      · rw [pulls_eq]
        exact List.mem_cons_self
      · exact ⟨BitVec.ofNat 5 view.adapter.op_a.val,
          locOf_rtypeReadBackMessage view _ view.adapter.op_a_memory 4 opa_lt⟩
      · rw [timeNat_rtypeReadBackMessage bounds _ _ val_4_zmod_p (by omega),
          ← statePull_eq]
    · left
      refine ⟨(rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory,
        StateMsg.timeNat rf.statePull), ?_, rfl, rfl, ?_, ?_, ?_⟩
      · rw [pulls_eq]
        exact List.mem_cons_of_mem _ List.mem_cons_self
      · rw [timeNat_rtypeReadBackMessage bounds _ _ val_3_zmod_p (by omega),
          ← statePull_eq]
        omega
      · rw [timeNat_rtypeReadBackMessage bounds _ _ val_3_zmod_p (by omega),
          ← statePull_eq]
        omega
      · intro _ _
        rw [commit_eq]
        rfl
    · left
      refine ⟨(rtypePriorMessage view view.adapter.op_c[0] view.adapter.op_c_memory,
        StateMsg.timeNat rf.statePull), ?_, rfl, rfl, ?_, ?_, ?_⟩
      · rw [pulls_eq]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
      · rw [timeNat_rtypeReadBackMessage bounds _ _ val_2_zmod_p (by omega),
          ← statePull_eq]
        omega
      · rw [timeNat_rtypeReadBackMessage bounds _ _ val_2_zmod_p (by omega),
          ← statePull_eq]
        omega
      · intro _ _
        rw [commit_eq]
        rfl
  push_clkBound := by
    intro message messageMem
    threeElementCases messageMem, pushes_eq
    · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 4 val_4_zmod_p
        (by omega) bounds.clk0 bounds.clk1
    · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 3 val_3_zmod_p
        (by omega) bounds.clk0 bounds.clk1
    · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 2 val_2_zmod_p
        (by omega) bounds.clk0 bounds.clk1
  ram_frame := by
    intro program s s' heff _ cell v _ hcontent
    rw [locContent_ram_congr (heff.mem.1 (by rw [commit_eq]; rfl)) cell]
    exact hcontent

/-! ### The aligned R-type touch carrier (Phase B1) -/

/-- **The aligned R-type touch list** (the `AlignedCarrier` sibling of `rowWiring_rtype`'s wiring):
the three produced pushes — op_c's read-back at `+ 2`, op_b's at `+ 3`, and the op_a write at `+ 4`
— each paired *positionally* with the same-location prior read at that push's own micro-time.  The
touches are listed in strictly ascending push-time order (`+ 2 < + 3 < + 4`), so every per-key filter
sublist is push-time sorted even when op_b/op_c alias the same register (`add x3, x1, x1`) — no
register-index distinctness is needed.  Feeding this to `alignedOf` re-pairs the ordinary carrier's
window-start pulls with the produced pushes, exactly the positional `RowOK` shape the timed grounding
walk consumes. -/
def rtypeTouches (view : Trace.RowView (ZMod p)) (rf : Semantics.RowFacts p) : List (Touch p) :=
  [((rtypePriorMessage view (view.adapter.op_c[0]) view.adapter.op_c_memory,
       StateMsg.timeNat rf.statePull + 2),
     rtypeReadBackMessage view (view.adapter.op_c[0]) view.adapter.op_c_memory 2),
   ((rtypePriorMessage view (view.adapter.op_b[0]) view.adapter.op_b_memory,
       StateMsg.timeNat rf.statePull + 3),
     rtypeReadBackMessage view (view.adapter.op_b[0]) view.adapter.op_b_memory 3),
   ((rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
       StateMsg.timeNat rf.statePull),
     rtypeWriteMessage view)]

/-- Immutable R-type touches, in ascending push-time order. -/
def immutableRtypeTouches (view : Trace.RowView (ZMod p))
    (rf : Semantics.RowFacts p) : List (Touch p) :=
  [((rtypePriorMessage view view.adapter.op_c[0] view.adapter.op_c_memory,
       StateMsg.timeNat rf.statePull + 2),
     rtypeReadBackMessage view view.adapter.op_c[0] view.adapter.op_c_memory 2),
   ((rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory,
       StateMsg.timeNat rf.statePull + 3),
     rtypeReadBackMessage view view.adapter.op_b[0] view.adapter.op_b_memory 3),
   ((rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
       StateMsg.timeNat rf.statePull),
     rtypeReadBackMessage view view.adapter.op_a view.adapter.op_a_memory 4)]

/-- **The R-type reader-shape aligned carrier** (SP-2's `rowAligned_rtype`, the `AlignedCarrier`
sibling of `rowWiring_rtype`): from the same in-circuit numeric facts plus the reader's per-operand
timestamp `Spec`s and clock bounds, produce the two non-assembly inputs `rowOK_alignedOf` consumes —
`AlignsWith (alignedOf rf (rtypeTouches …)) rf`, the per-slot `TouchOK`, and the per-key push-time
`IsChain` — so a caller need only supply the `+ 8` step and mod-8 alignment (both `initialClock`-level)
to obtain the walk's `RowOK`.

Unlike `rowWiring_rtype` this needs the two source operands' index bounds (`opb_lt`/`opc_lt`) and the
per-operand register-access `RegisterAccessTimestamp.Spec`s at the pushes' access clocks and their
prior records' 24-bit `ClkBound`s (all supplied by `RTypeReader.Spec` — the `+ 4`/`+ 3`/`+ 2` slots and
the Phase-G tail).  It does **not** need register-index distinctness: because `rtypeTouches` lists the
pushes in ascending push-time order, the per-key `IsChain` holds even for the SP-6 register-alias rows
(`add x3, x1, x1`, whose op_b/op_c read-backs share a key). -/
theorem rowAligned_rtype {view : Trace.RowView (ZMod p)} {rf : Semantics.RowFacts p}
    (bounds : ViewClockBounds view)
    (_real : view.is_real = 1)
    (opa_lt : view.adapter.op_a.val < 32)
    (opb_lt : (view.adapter.op_b[0]).val < 32)
    (opc_lt : (view.adapter.op_c[0]).val < 32)
    (statePull_eq : rf.statePull = statePullOfView view)
    (pulls_eq : rf.memPulls =
      [(rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
          StateMsg.timeNat rf.statePull),
       (rtypePriorMessage view (view.adapter.op_b[0]) view.adapter.op_b_memory,
          StateMsg.timeNat rf.statePull),
       (rtypePriorMessage view (view.adapter.op_c[0]) view.adapter.op_c_memory,
          StateMsg.timeNat rf.statePull)])
    (pushes_eq : rf.memPushes =
      [rtypeReadBackMessage view (view.adapter.op_b[0]) view.adapter.op_b_memory 3,
       rtypeReadBackMessage view (view.adapter.op_c[0]) view.adapter.op_c_memory 2,
       rtypeWriteMessage view])
    (hslots : ∀ tc ∈ rtypeTouches view rf, SP1Clean.Channels.MemoryMsg.ClkBound (tc : Touch p).1.1 →
      MemoryMsg.timeNat (tc : Touch p).1.1 < MemoryMsg.timeNat tc.2) :
    AlignsWith (alignedOf rf (rtypeTouches view rf)) rf ∧
      (∀ tc ∈ rtypeTouches view rf,
        TouchOK (StateMsg.timeNat rf.statePull) tc.1 tc.2) ∧
      (∀ loc : MemLoc, List.IsChain
        (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2)
        ((rtypeTouches view rf).filter (fun pq => MemoryMsg.locOf pq.2 = loc))) ∧
      (∀ tc ∈ rtypeTouches view rf, SP1Clean.Channels.MemoryMsg.ClkBound tc.2) ∧
      (∀ tc ∈ rtypeTouches view rf, SP1Clean.Channels.MemoryMsg.ClkBound (tc : Touch p).1.1 →
        MemoryMsg.timeNat (tc : Touch p).1.1 < MemoryMsg.timeNat tc.2) := by
  -- Register-index → location facts (used everywhere).
  have hlocPriorA := locOf_rtypePriorMessage view _ view.adapter.op_a_memory opa_lt
  have hlocPriorB := locOf_rtypePriorMessage view _ view.adapter.op_b_memory opb_lt
  have hlocPriorC := locOf_rtypePriorMessage view _ view.adapter.op_c_memory opc_lt
  have hlocReadB := locOf_rtypeReadBackMessage view _ view.adapter.op_b_memory 3 opb_lt
  have hlocReadC := locOf_rtypeReadBackMessage view _ view.adapter.op_c_memory 2 opc_lt
  have hlocWrite := locOf_rtypeWriteMessage view opa_lt
  -- Read-back / write time equalities.
  have tb : MemoryMsg.timeNat
      (rtypeReadBackMessage view (view.adapter.op_b[0]) view.adapter.op_b_memory 3)
      = StateMsg.timeNat rf.statePull + 3 := by
    rw [statePull_eq]
    exact timeNat_rtypeReadBackMessage bounds _ _ val_3_zmod_p (by omega)
  have tc2 : MemoryMsg.timeNat
      (rtypeReadBackMessage view (view.adapter.op_c[0]) view.adapter.op_c_memory 2)
      = StateMsg.timeNat rf.statePull + 2 := by
    rw [statePull_eq]
    exact timeNat_rtypeReadBackMessage bounds _ _ val_2_zmod_p (by omega)
  have tw : MemoryMsg.timeNat (rtypeWriteMessage view) = StateMsg.timeNat rf.statePull + 4 := by
    rw [statePull_eq]
    exact timeNat_rtypeWriteMessage bounds
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- AlignsWith via the generic constructor
    refine alignsWith_alignedOf rf (rtypeTouches view rf) ?_ ?_ ?_ ?_ ?_
    · -- hpush: the aligned pushes permute the ordinary produced list (op_c/op_b read-backs swap)
      rw [pushes_eq]
      simp only [rtypeTouches, List.map_cons, List.map_nil]
      exact List.Perm.swap _ _ _
    · -- hpull: the aligned pull messages permute the ordinary ones (reversal of the three priors)
      rw [pulls_eq]
      simp only [rtypeTouches, List.map_cons, List.map_nil]
      refine (List.Perm.swap _ _ _).trans ((List.Perm.cons _ (List.Perm.swap _ _ _)).trans
        (List.Perm.swap _ _ _))
    · intro mp hmp
      threeElementCases hmp, pulls_eq
      · exact ⟨_, hlocPriorA⟩
      · exact ⟨_, hlocPriorB⟩
      · exact ⟨_, hlocPriorC⟩
    · intro mp hmp
      threeElementCases hmp, pulls_eq <;> rfl
    · intro mp hmp
      threeElementCases hmp, pulls_eq
      · -- op_a prior ↦ the write touch (still 3rd)
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
          rfl, by dsimp only; omega, by dsimp only; omega⟩
      · -- op_b prior ↦ op_b read-back (now 2nd)
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, rfl,
          by dsimp only; omega, by dsimp only; omega⟩
      · -- op_c prior ↦ op_c read-back (now 1st)
        exact ⟨_, List.mem_cons_self, rfl, by dsimp only; omega, by dsimp only; omega⟩
  · -- the per-slot `TouchOK`
    intro tc htc
    simp only [rtypeTouches, List.mem_cons, List.not_mem_nil, or_false] at htc
    rcases htc with rfl | rfl | rfl
    · -- op_c read-back at + 2
      refine ⟨?_, ?_, ?_, Or.inl ⟨rfl, tc2⟩⟩
      · dsimp only; rw [hlocReadC, hlocPriorC]
      · dsimp only; omega
      · dsimp only; simp only [hlocPriorC, readWindow_reg]; omega
    · -- op_b read-back at + 3
      refine ⟨?_, ?_, ?_, Or.inl ⟨rfl, tb⟩⟩
      · dsimp only; rw [hlocReadB, hlocPriorB]
      · dsimp only; omega
      · dsimp only; simp only [hlocPriorB, readWindow_reg]; omega
    · -- op_a write at + 4
      refine ⟨?_, ?_, ?_, Or.inr ?_⟩
      · dsimp only; rw [hlocWrite, hlocPriorA]
      · dsimp only; omega
      · dsimp only; simp only [hlocPriorA, readWindow_reg]; omega
      · dsimp only; rw [hlocWrite, writeOffset_reg]; exact tw
  · -- per-key push-time `IsChain` (distinctness-free: the full touch list is strictly push-time
    -- sorted, so every per-key filter sublist is sorted, hence a chain — this admits alias rows)
    have hpair : List.Pairwise
        (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2)
        (rtypeTouches view rf) := by
      simp only [rtypeTouches]
      refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil))
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · dsimp only; rw [tc2, tb]; omega
        · dsimp only; rw [tc2, tw]; omega
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl
        dsimp only; rw [tb, tw]; omega
      · intro x hx
        simp only [List.not_mem_nil] at hx
    intro loc
    exact (List.Pairwise.sublist List.filter_sublist hpair).isChain
  · -- the per-push `ClkBound` (`hpushClk` for `rowOK_alignedOf`): each push sits at
    -- `clk_0_16 + clk_16_24 * 65536 + δ` with `δ ∈ {2, 3, 4}` (the rtypeTouches order:
    -- op_c read-back @ +2, op_b read-back @ +3, op_a write @ +4), constraint-only from `bounds`.
    intro tc htc
    simp only [rtypeTouches, List.mem_cons, List.not_mem_nil, or_false] at htc
    rcases htc with rfl | rfl | rfl
    · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 2 val_2_zmod_p (by omega)
        bounds.clk0 bounds.clk1
    · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 3 val_3_zmod_p (by omega)
        bounds.clk0 bounds.clk1
    · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 4 val_4_zmod_p (by omega)
        bounds.clk0 bounds.clk1
  · -- the currency-free **conditional** `slot` (`prev_clk < access_clk` given the pulled record's
    -- received `ClkBound`) is supplied by the six-pack caller from the retained reader's finished
    -- Byte guarantees; no nested chip `Spec` is unfolded here.
    exact hslots

/-- Aligned carrier for an immutable three-register row. It differs from `rowAligned_rtype` only
at the final `+4` effect: source A is read back unchanged instead of receiving a computed value. -/
theorem rowAligned_immutableRtype {view : Trace.RowView (ZMod p)}
    {rf : Semantics.RowFacts p}
    (bounds : ViewClockBounds view)
    (_real : view.is_real = 1)
    (opa_lt : view.adapter.op_a.val < 32)
    (opb_lt : view.adapter.op_b[0].val < 32)
    (opc_lt : view.adapter.op_c[0].val < 32)
    (statePull_eq : rf.statePull = statePullOfView view)
    (pulls_eq : rf.memPulls =
      [(rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
          StateMsg.timeNat rf.statePull),
       (rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory,
          StateMsg.timeNat rf.statePull),
       (rtypePriorMessage view view.adapter.op_c[0] view.adapter.op_c_memory,
          StateMsg.timeNat rf.statePull)])
    (pushes_eq : rf.memPushes =
      [rtypeReadBackMessage view view.adapter.op_a view.adapter.op_a_memory 4,
       rtypeReadBackMessage view view.adapter.op_b[0] view.adapter.op_b_memory 3,
       rtypeReadBackMessage view view.adapter.op_c[0] view.adapter.op_c_memory 2])
    (hslots : ∀ tc ∈ immutableRtypeTouches view rf,
      SP1Clean.Channels.MemoryMsg.ClkBound (tc : Touch p).1.1 →
        MemoryMsg.timeNat (tc : Touch p).1.1 < MemoryMsg.timeNat tc.2) :
    AlignsWith (alignedOf rf (immutableRtypeTouches view rf)) rf ∧
      (∀ tc ∈ immutableRtypeTouches view rf,
        TouchOK (StateMsg.timeNat rf.statePull) tc.1 tc.2) ∧
      (∀ loc : MemLoc, List.IsChain
        (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2)
        ((immutableRtypeTouches view rf).filter
          (fun pq => MemoryMsg.locOf pq.2 = loc))) ∧
      (∀ tc ∈ immutableRtypeTouches view rf,
        SP1Clean.Channels.MemoryMsg.ClkBound tc.2) ∧
      (∀ tc ∈ immutableRtypeTouches view rf,
        SP1Clean.Channels.MemoryMsg.ClkBound (tc : Touch p).1.1 →
          MemoryMsg.timeNat (tc : Touch p).1.1 < MemoryMsg.timeNat tc.2) := by
  have hlocPriorA := locOf_rtypePriorMessage view _ view.adapter.op_a_memory opa_lt
  have hlocPriorB := locOf_rtypePriorMessage view _ view.adapter.op_b_memory opb_lt
  have hlocPriorC := locOf_rtypePriorMessage view _ view.adapter.op_c_memory opc_lt
  have hlocReadA := locOf_rtypeReadBackMessage view _ view.adapter.op_a_memory 4 opa_lt
  have hlocReadB := locOf_rtypeReadBackMessage view _ view.adapter.op_b_memory 3 opb_lt
  have hlocReadC := locOf_rtypeReadBackMessage view _ view.adapter.op_c_memory 2 opc_lt
  have tc2 : MemoryMsg.timeNat
      (rtypeReadBackMessage view view.adapter.op_c[0] view.adapter.op_c_memory 2) =
      StateMsg.timeNat rf.statePull + 2 := by
    rw [statePull_eq]
    exact timeNat_rtypeReadBackMessage bounds _ _ val_2_zmod_p (by omega)
  have tb : MemoryMsg.timeNat
      (rtypeReadBackMessage view view.adapter.op_b[0] view.adapter.op_b_memory 3) =
      StateMsg.timeNat rf.statePull + 3 := by
    rw [statePull_eq]
    exact timeNat_rtypeReadBackMessage bounds _ _ val_3_zmod_p (by omega)
  have ta : MemoryMsg.timeNat
      (rtypeReadBackMessage view view.adapter.op_a view.adapter.op_a_memory 4) =
      StateMsg.timeNat rf.statePull + 4 := by
    rw [statePull_eq]
    exact timeNat_rtypeReadBackMessage bounds _ _ val_4_zmod_p (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine alignsWith_alignedOf rf (immutableRtypeTouches view rf) ?_ ?_ ?_ ?_ ?_
    · rw [pushes_eq]
      simp only [immutableRtypeTouches, List.map_cons, List.map_nil]
      refine (List.Perm.swap _ _ _).trans
        ((List.Perm.cons _ (List.Perm.swap _ _ _)).trans (List.Perm.swap _ _ _))
    · rw [pulls_eq]
      simp only [immutableRtypeTouches, List.map_cons, List.map_nil]
      refine (List.Perm.swap _ _ _).trans
        ((List.Perm.cons _ (List.Perm.swap _ _ _)).trans (List.Perm.swap _ _ _))
    · intro mp hmp
      threeElementCases hmp, pulls_eq
      · exact ⟨_, hlocPriorA⟩
      · exact ⟨_, hlocPriorB⟩
      · exact ⟨_, hlocPriorC⟩
    · intro mp hmp
      threeElementCases hmp, pulls_eq <;> rfl
    · intro mp hmp
      threeElementCases hmp, pulls_eq
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
          rfl, by dsimp only; omega, by dsimp only; omega⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, rfl,
          by dsimp only; omega, by dsimp only; omega⟩
      · exact ⟨_, List.mem_cons_self, rfl,
          by dsimp only; omega, by dsimp only; omega⟩
  · intro tc htc
    simp only [immutableRtypeTouches, List.mem_cons, List.not_mem_nil, or_false] at htc
    rcases htc with rfl | rfl | rfl
    · refine ⟨?_, ?_, ?_, Or.inl ⟨rfl, tc2⟩⟩
      · dsimp only; rw [hlocReadC, hlocPriorC]
      · dsimp only; omega
      · dsimp only; simp only [hlocPriorC, readWindow_reg]; omega
    · refine ⟨?_, ?_, ?_, Or.inl ⟨rfl, tb⟩⟩
      · dsimp only; rw [hlocReadB, hlocPriorB]
      · dsimp only; omega
      · dsimp only; simp only [hlocPriorB, readWindow_reg]; omega
    · refine ⟨?_, ?_, ?_, Or.inr ?_⟩
      · dsimp only; rw [hlocReadA, hlocPriorA]
      · dsimp only; omega
      · dsimp only; simp only [hlocPriorA, readWindow_reg]; omega
      · dsimp only; rw [hlocReadA, writeOffset_reg]; exact ta
  · have hpair : List.Pairwise
        (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2)
        (immutableRtypeTouches view rf) := by
      simp only [immutableRtypeTouches]
      refine List.Pairwise.cons ?_
        (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil))
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · dsimp only; rw [tc2, tb]; omega
        · dsimp only; rw [tc2, ta]; omega
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl
        dsimp only; rw [tb, ta]; omega
      · intro x hx
        simp only [List.not_mem_nil] at hx
    intro loc
    exact (List.Pairwise.sublist List.filter_sublist hpair).isChain
  · intro tc htc
    simp only [immutableRtypeTouches, List.mem_cons, List.not_mem_nil, or_false] at htc
    rcases htc with rfl | rfl | rfl
    · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 2 val_2_zmod_p
        (by omega) bounds.clk0 bounds.clk1
    · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 3 val_3_zmod_p
        (by omega) bounds.clk0 bounds.clk1
    · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 4 val_4_zmod_p
        (by omega) bounds.clk0 bounds.clk1
  · exact hslots

end RType

/-! ## Canonical R-type interaction contract

The register-register chips all expose the same six Memory interactions.  Naming that evaluated
shape once lets wiring, aligned-carrier construction, and operand binding share one structural
anchor instead of maintaining three parallel per-chip projections. -/

open SP1Clean.Channels (memoryChannel byteChannel)

section RTypeInteractionShape

variable [Fact (2 ^ 25 < p)]

/-- The canonical typed six-pack emitted by an active-or-padding R-type row. -/
noncomputable def rtypeMemoryInteractions (view : Trace.RowView (ZMod p)) :
    List (TypedInteraction (memoryChannel (p := p))) :=
  [TypedInteraction.pulledIfValue memoryChannel view.is_real
      (rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory),
   TypedInteraction.pulledIfValue memoryChannel view.is_real
      (rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory),
   TypedInteraction.pushedIfValue memoryChannel view.is_real
      (rtypeReadBackMessage view view.adapter.op_b[0] view.adapter.op_b_memory 3),
   TypedInteraction.pulledIfValue memoryChannel view.is_real
      (rtypePriorMessage view view.adapter.op_c[0] view.adapter.op_c_memory),
   TypedInteraction.pushedIfValue memoryChannel view.is_real
      (rtypeReadBackMessage view view.adapter.op_c[0] view.adapter.op_c_memory 2),
   TypedInteraction.pushedIfValue memoryChannel view.is_real (rtypeWriteMessage view)]

/-- Descriptor-level structural contract for the canonical R-type Memory six-pack. -/
def RTypeMemoryInteractionShape (chip : SupportedChip p) : Prop :=
  ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
      decoded.interactionsWith data memoryChannel =
        rtypeMemoryInteractions (decoded.toChipRow data).view

/-- The two source words of an active canonical R-type row inherit `isU64` from the exact prior
record pulls and the finished Memory channel.  This is structural bus currency, independent of the
chip's arithmetic `Spec`; chips such as DivRem use it to discharge their soundness assumptions. -/
theorem rtypeOperandWords_isU64_of_shape {chip : SupportedChip p}
    (shape : RTypeMemoryInteractionShape chip) (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1)
    (guarantees : decoded.chip.table.operations.ChannelGuarantees memoryChannel.toRaw
      (decoded.environment data)) :
    Word.isU64 (decoded.toChipRow data).view.adapter.op_b_memory.prev_value ∧
      Word.isU64 (decoded.toChipRow data).view.adapter.op_c_memory.prev_value := by
  let view := (decoded.toChipRow data).view
  let pullB := TypedInteraction.pulledIfValue memoryChannel view.is_real
    (rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory)
  let pullC := TypedInteraction.pulledIfValue memoryChannel view.is_real
    (rtypePriorMessage view view.adapter.op_c[0] view.adapter.op_c_memory)
  have pullBMem : pullB ∈ decoded.interactionsWith data memoryChannel := by
    rw [shape decoded data hchip]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have pullCMem : pullC ∈ decoded.interactionsWith data memoryChannel := by
    rw [shape decoded data hchip]
    exact List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have pullBNegative : pullB.mult = -1 := by
    simp only [pullB, TypedInteraction.pulledIfValue_mult, view, real]
  have pullCNegative : pullC.mult = -1 := by
    simp only [pullC, TypedInteraction.pulledIfValue_mult, view, real]
  have bGuarantee := TypedInteraction.guarantee_of_channelGuarantees
    decoded.chip.table.operations memoryChannel (decoded.environment data) pullB pullBMem
    guarantees (by rfl) pullBNegative
  have cGuarantee := TypedInteraction.guarantee_of_channelGuarantees
    decoded.chip.table.operations memoryChannel (decoded.environment data) pullC pullCMem
    guarantees (by rfl) pullCNegative
  constructor
  · simpa only [Channels.memoryChannel, pullB, TypedInteraction.pulledIfValue_message,
      MemoryMsg.isU64, rtypePriorMessage] using bGuarantee.1
  · simpa only [Channels.memoryChannel, pullC, TypedInteraction.pulledIfValue_message,
      MemoryMsg.isU64, rtypePriorMessage] using cGuarantee.1

/-- The three active register timestamp facts carried by an R-type semantic row. -/
def RTypeTimestampBounds (view : Trace.RowView (ZMod p)) : Prop :=
  ActiveTimestampBounds view.adapter.op_a_memory.access_timestamp.prev_low
      view.adapter.op_a_memory.access_timestamp.diff_low_limb
      (view.state.clk_0_16 + view.state.clk_16_24 * 65536 + 4) ∧
    ActiveTimestampBounds view.adapter.op_b_memory.access_timestamp.prev_low
        view.adapter.op_b_memory.access_timestamp.diff_low_limb
        (view.state.clk_0_16 + view.state.clk_16_24 * 65536 + 3) ∧
      ActiveTimestampBounds view.adapter.op_c_memory.access_timestamp.prev_low
        view.adapter.op_c_memory.access_timestamp.diff_low_limb
        (view.state.clk_0_16 + view.state.clk_16_24 * 65536 + 2)

/-- Scalar binding between one retained `RTypeReader` and the public semantic row view.  Keeping
the contract scalar prevents a consumer from normalizing either evaluated nested structure. -/
structure RTypeTimestampBinding
    (readerReal aPrev aDiff bPrev bDiff cPrev cDiff targetA targetB targetC : ZMod p)
    (view : Trace.RowView (ZMod p)) : Prop where
  real_eq : readerReal = view.is_real
  aPrev_eq : aPrev = view.adapter.op_a_memory.access_timestamp.prev_low
  aDiff_eq : aDiff = view.adapter.op_a_memory.access_timestamp.diff_low_limb
  bPrev_eq : bPrev = view.adapter.op_b_memory.access_timestamp.prev_low
  bDiff_eq : bDiff = view.adapter.op_b_memory.access_timestamp.diff_low_limb
  cPrev_eq : cPrev = view.adapter.op_c_memory.access_timestamp.prev_low
  cDiff_eq : cDiff = view.adapter.op_c_memory.access_timestamp.diff_low_limb
  targetA_eq : targetA = view.state.clk_0_16 + view.state.clk_16_24 * 65536 + 4
  targetB_eq : targetB = view.state.clk_0_16 + view.state.clk_16_24 * 65536 + 3
  targetC_eq : targetC = view.state.clk_0_16 + view.state.clk_16_24 * 65536 + 2

/-- Chip-local contract locating the retained `RTypeReader` and binding precisely the timestamp
scalars used by the aligned carrier.  This is a named `Prop` inductive rather than a reducible
existential: completed chips may have hundreds of output columns, and unfolding the contract merely
to recognize its result sort would otherwise force `whnf` through the concrete circuit record. -/
inductive CircuitRTypeTimestampContract {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p)) : Prop where
  | intro (readerOffset : ℕ) (readerInput : Var Readers.RTypeReader.Inputs (ZMod p))
      (reader_mem :
        ⟨readerOffset,
          (Readers.RTypeReader.circuit (p := p)).toSubcircuit readerOffset readerInput⟩ ∈
          ((circuit.main (varFromOffset (F := ZMod p) Input 0)).operations
            (size Input)).subcircuits)
      (binding : ∀ env : Environment (ZMod p),
        RTypeTimestampBinding
          (Expression.eval env readerInput.is_real)
          (Expression.eval env readerInput.cols.op_a_memory.access_timestamp.prev_low)
          (Expression.eval env readerInput.cols.op_a_memory.access_timestamp.diff_low_limb)
          (Expression.eval env readerInput.cols.op_b_memory.access_timestamp.prev_low)
          (Expression.eval env readerInput.cols.op_b_memory.access_timestamp.diff_low_limb)
          (Expression.eval env readerInput.cols.op_c_memory.access_timestamp.prev_low)
          (Expression.eval env readerInput.cols.op_c_memory.access_timestamp.diff_low_limb)
          (Expression.eval env (readerInput.clk_low + 4))
          (Expression.eval env (readerInput.clk_low + 3))
          (Expression.eval env (readerInput.clk_low + 2))
          (view (Eval.eval env (varFromOffset (F := ZMod p) Input 0))
            (Eval.eval env
              (circuit.output (varFromOffset (F := ZMod p) Input 0) (size Input))))) :
      CircuitRTypeTimestampContract circuit view

/-- Finished Byte guarantees specialize any retained R-type timestamp contract to the semantic row. -/
theorem rtypeTimestampBounds_of_contract {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p))
    (contract : CircuitRTypeTimestampContract circuit view)
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (guarantees : (⟨circuit⟩ : Component (ZMod p)).operations.ChannelGuarantees
      byteChannel.toRaw (Environment.fromArray physical data))
    (real : (view ((⟨circuit⟩ : Component (ZMod p)).rowInput
      (Environment.fromArray physical data)) ((⟨circuit⟩ : Component (ZMod p)).rowOutput
        (Environment.fromArray physical data))).is_real = 1) :
    RTypeTimestampBounds (view ((⟨circuit⟩ : Component (ZMod p)).rowInput
      (Environment.fromArray physical data)) ((⟨circuit⟩ : Component (ZMod p)).rowOutput
        (Environment.fromArray physical data))) := by
  obtain ⟨readerOffset, readerInput, readerMem, binding⟩ := contract
  let component : Component (ZMod p) := ⟨circuit⟩
  let env := Environment.fromArray physical data
  have rowGuarantees : component.rowOperations.ChannelGuarantees byteChannel.toRaw env :=
    (Component.channelGuarantees_iff env byteChannel.toRaw).mp guarantees
  have readerGuarantees := channelGuarantees_subcircuit_of_mem byteChannel.toRaw env
    component.rowOperations
    ((Readers.RTypeReader.circuit (p := p)).toSubcircuit readerOffset readerInput)
    readerMem rowGuarantees
  have inputEq : Eval.eval env (varFromOffset Input 0) = component.rowInput env :=
    eval_varFromOffset_valueFromOffset Input 0 env
  have outputEq : Eval.eval env
      (circuit.output (varFromOffset Input 0) (size Input)) = component.rowOutput env := by
    simp only [component, Component.rowOutput, circuit_norm]
  have bound := binding env
  rw [inputEq, outputEq] at bound
  have readerReal : Expression.eval env readerInput.is_real = 1 := bound.real_eq.trans real
  have timestampBounds := Readers.RTypeReader.timestampSpecs_of_byteGuarantees readerInput
    readerOffset env readerGuarantees readerReal
  unfold RTypeTimestampBounds
  rwa [bound.aPrev_eq, bound.aDiff_eq, bound.bPrev_eq, bound.bDiff_eq, bound.cPrev_eq,
    bound.cDiff_eq, bound.targetA_eq, bound.targetB_eq, bound.targetC_eq] at timestampBounds

end RTypeInteractionShape

/-! ## The Add anchor

Add validates the whole pipeline: its exact Memory emissions are evaluated once from the circuit's
public exposed list (`AddChip.exposedMemoryInteractions`), the numeric wiring inputs are extracted
from the finished Byte channel, the chip `Spec`, and the row's own push `Requirements`, and
`addRow_engineFacts` produces both engine records for a genuine decoded Add row. -/

section AddAnchor

variable [Fact (2 ^ 25 < p)]

omit [Fact (2 ^ 25 < p)] in
/-- The Add instruction descriptor (entry 0 of `supportedChips`). -/
def addChipDescriptor : SupportedChip p :=
  ⟨AddChip.kind, AddChip.circuit, rfl, [.ADD], .nonX0⟩

omit [Fact (2 ^ 25 < p)] in
/-- The Add row view denoted by one physical environment. -/
noncomputable def addViewOf (env : Environment (ZMod p)) : Trace.RowView (ZMod p) :=
  AddChip.rowView ((⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
    ((⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env)

omit [Fact (2 ^ 25 < p)] in
/-- The Add row view's selector is the component input selector.  This tiny evaluator boundary keeps
clients from asking unification to normalize the complete concrete Add circuit just to project it. -/
theorem addViewOf_isReal (env : Environment (ZMod p)) :
    (addViewOf env).is_real =
      ((⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).is_real := by
  simp only [addViewOf, AddChip.rowView]

/-- The typed decoder's Add view is `addViewOf` at the row's physical environment — the descriptor's
retained circuit and its flat component agree by structure-literal projection. -/
theorem addViewOf_decodeRow (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    ((addChipDescriptor (p := p)).decodeRow data physical).view =
      addViewOf (Environment.fromArray physical data) := rfl

/-- The descriptor's flat table is the bare Add component — again structure-literal projection. -/
theorem addChipDescriptor_table :
    (addChipDescriptor (p := p)).table = (⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)) := rfl

omit [Fact (2 ^ 25 < p)] in
/-- The Add descriptor's heterogeneous view is the native Add row view.  Keeping this projection
explicit lets decoder consumers cross the dependent descriptor boundary by rewriting rather than
normalizing the retained circuit. -/
theorem addChipDescriptor_view (inp : AddChip.Inputs (ZMod p))
    (cols : AddChip.Columns (ZMod p)) :
    (addChipDescriptor (p := p)).kind.view inp cols = AddChip.rowView inp cols := rfl

omit [Fact (2 ^ 25 < p)] in
/-- Add's circuit output as its explicit (structural) row — a `rfl` reduction of `circuit.output` over an
**opaque** `input`.  Applying it at a concrete decoded row is a symbolic rewrite, so the memory closed-form
below closes via `simp only [circuit_norm, …]` **without** unfolding the composed `main`/`circuit` at the
concrete row (the `whnf`-into-concrete blowup that used to force a raised ceiling — see
`../clean/doc/performance-problems.md` §"Keep hypothesis types folded"). -/
theorem addChip_circuit_output_eq (input : Var AddChip.Inputs (ZMod p)) (offset : ℕ) :
    (AddChip.circuit (p := p)).output input offset =
      (⟨input.is_real, input.state, input.adapter,
         ⟨Vector.mapRange 4 fun i => var { index := offset + i }⟩⟩ :
        Var AddChip.Columns (ZMod p)) := rfl

omit [Fact (2 ^ 25 < p)] in
/-- **Add's evaluated Memory interaction list**, in the canonical R-type message shapes over the
row view: the three read-prior pulls and the two read-backs + `op_a` write pushes, all gated by the
view's selector.  Evaluated once from the circuit's public exposed list. -/
theorem addChip_memoryInteractionValues_eq (env : Environment (ZMod p)) :
    (⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).operations.interactionValuesWith
        (memoryChannel (p := p)).toRaw env =
      [memoryChannel.pulledIfValue (addViewOf env).is_real
         (rtypePriorMessage (addViewOf env) (addViewOf env).adapter.op_a
           (addViewOf env).adapter.op_a_memory),
       memoryChannel.pulledIfValue (addViewOf env).is_real
         (rtypePriorMessage (addViewOf env) ((addViewOf env).adapter.op_b[0])
           (addViewOf env).adapter.op_b_memory),
       memoryChannel.pushedIfValue (addViewOf env).is_real
         (rtypeReadBackMessage (addViewOf env) ((addViewOf env).adapter.op_b[0])
           (addViewOf env).adapter.op_b_memory 3),
       memoryChannel.pulledIfValue (addViewOf env).is_real
         (rtypePriorMessage (addViewOf env) ((addViewOf env).adapter.op_c[0])
           (addViewOf env).adapter.op_c_memory),
       memoryChannel.pushedIfValue (addViewOf env).is_real
         (rtypeReadBackMessage (addViewOf env) ((addViewOf env).adapter.op_c[0])
           (addViewOf env).adapter.op_c_memory 2),
       memoryChannel.pushedIfValue (addViewOf env).is_real
         (rtypeWriteMessage (addViewOf env))] := by
  rw [Operations.interactionValuesWith_eq_map, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval env)
      (((AddChip.main (varFromOffset AddChip.Inputs 0)).operations
        (size AddChip.Inputs)).interactionsWith (memoryChannel (p := p)).toRaw) = _
  rw [AddChip.interactionsWith_memory_eq]
  have inputEq : Eval.eval env (varFromOffset AddChip.Inputs 0) =
      (⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset AddChip.Inputs 0 env
  have outputEq : Eval.eval env
      ((AddChip.circuit (p := p)).output (varFromOffset AddChip.Inputs 0)
        (size AddChip.Inputs)) =
      (⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env := by
    simp only [Component.rowOutput, circuit_norm]
  simp only [AddChip.exposedMemoryInteractions, List.map_cons, List.map_nil,
    Channel.eval_pulledIf, Channel.eval_pushedIf, eval_registerMemoryMessage]
  simp only [addViewOf, ← inputEq, ← outputEq, rtypePriorMessage, rtypeReadBackMessage,
    rtypeWriteMessage, AddChip.rowView, Extracted.RTypeReader.toAdapterView]
  simp only [circuit_norm, addChip_circuit_output_eq]

/-- Lift the raw evaluation to the proof-carrying typed decoder for any retained Add row. -/
theorem addChip_typedMemoryInteractions_eq (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = addChipDescriptor (p := p)) :
    decoded.interactionsWith data (memoryChannel (p := p)) =
      [TypedInteraction.pulledIfValue memoryChannel (decoded.toChipRow data).view.is_real
         (rtypePriorMessage (decoded.toChipRow data).view
           (decoded.toChipRow data).view.adapter.op_a
           (decoded.toChipRow data).view.adapter.op_a_memory),
       TypedInteraction.pulledIfValue memoryChannel (decoded.toChipRow data).view.is_real
         (rtypePriorMessage (decoded.toChipRow data).view
           ((decoded.toChipRow data).view.adapter.op_b[0])
           (decoded.toChipRow data).view.adapter.op_b_memory),
       TypedInteraction.pushedIfValue memoryChannel (decoded.toChipRow data).view.is_real
         (rtypeReadBackMessage (decoded.toChipRow data).view
           ((decoded.toChipRow data).view.adapter.op_b[0])
           (decoded.toChipRow data).view.adapter.op_b_memory 3),
       TypedInteraction.pulledIfValue memoryChannel (decoded.toChipRow data).view.is_real
         (rtypePriorMessage (decoded.toChipRow data).view
           ((decoded.toChipRow data).view.adapter.op_c[0])
           (decoded.toChipRow data).view.adapter.op_c_memory),
       TypedInteraction.pushedIfValue memoryChannel (decoded.toChipRow data).view.is_real
         (rtypeReadBackMessage (decoded.toChipRow data).view
           ((decoded.toChipRow data).view.adapter.op_c[0])
           (decoded.toChipRow data).view.adapter.op_c_memory 2),
       TypedInteraction.pushedIfValue memoryChannel (decoded.toChipRow data).view.is_real
         (rtypeWriteMessage (decoded.toChipRow data).view)] := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = addChipDescriptor (p := p) := hchip
  subst hchip'
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [DecodedInstructionRow.interactionsWith_raw]
  simpa only [List.map_cons, List.map_nil, TypedInteraction.pulledIfValue_raw,
    TypedInteraction.pushedIfValue_raw, DecodedInstructionRow.environment,
    DecodedInstructionRow.toChipRow, addViewOf_decodeRow, addChipDescriptor_table] using
    addChip_memoryInteractionValues_eq (Environment.fromArray physical data)

/-- Add instantiates the shared R-type six-pack contract. -/
theorem addChip_rtypeMemoryInteractionShape :
    RTypeMemoryInteractionShape (addChipDescriptor (p := p)) := by
  intro decoded data hchip
  simpa only [rtypeMemoryInteractions] using
    addChip_typedMemoryInteractions_eq decoded data hchip

/-! ### Consumed/produced lists at an active selector -/

omit [Fact (2 ^ 25 < p)] in
private theorem memPull_one_signed (msg : MemoryMsg (ZMod p)) :
    signedVal (TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 msg).mult = -1 := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  calc
    _ = signedVal (-(1 : ZMod p)) := rfl
    _ = -((1 : ZMod p).val : ℤ) := signedVal_neg_is_real hp (Or.inr rfl)
    _ = -1 := by
      rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
      norm_num

omit [Fact (2 ^ 25 < p)] in
private theorem memPush_one_signed (msg : MemoryMsg (ZMod p)) :
    signedVal (TypedInteraction.pushedIfValue (memoryChannel (p := p)) 1 msg).mult = 1 := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  calc
    _ = signedVal (1 : ZMod p) := rfl
    _ = ((1 : ZMod p).val : ℤ) := signedVal_is_real hp (Or.inr rfl)
    _ = 1 := by
      rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
      norm_num

omit [Fact (2 ^ 25 < p)] in
/-- An active R-type six-pack consumes exactly its three read-prior messages. -/
private theorem consumedMessages_rtypeSix (m1 m2 b1 m3 b2 w : MemoryMsg (ZMod p)) :
    consumedMessages
      [TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 m1,
       TypedInteraction.pulledIfValue memoryChannel 1 m2,
       TypedInteraction.pushedIfValue memoryChannel 1 b1,
       TypedInteraction.pulledIfValue memoryChannel 1 m3,
       TypedInteraction.pushedIfValue memoryChannel 1 b2,
       TypedInteraction.pushedIfValue memoryChannel 1 w] = [m1, m2, m3] := by
  have filtered : List.filter (fun i => signedVal i.mult = -1)
      [TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 m1,
       TypedInteraction.pulledIfValue memoryChannel 1 m2,
       TypedInteraction.pushedIfValue memoryChannel 1 b1,
       TypedInteraction.pulledIfValue memoryChannel 1 m3,
       TypedInteraction.pushedIfValue memoryChannel 1 b2,
       TypedInteraction.pushedIfValue memoryChannel 1 w] =
      [TypedInteraction.pulledIfValue memoryChannel 1 m1,
       TypedInteraction.pulledIfValue memoryChannel 1 m2,
       TypedInteraction.pulledIfValue memoryChannel 1 m3] := by
    simp only [List.filter_cons, List.filter_nil, memPull_one_signed, memPush_one_signed]
    norm_num
  rw [consumedMessages, filtered]
  simp only [List.map_cons, List.map_nil, TypedInteraction.pulledIfValue_message]

omit [Fact (2 ^ 25 < p)] in
/-- An active R-type six-pack produces exactly its two read-backs and its write. -/
private theorem producedMessages_rtypeSix (m1 m2 b1 m3 b2 w : MemoryMsg (ZMod p)) :
    producedMessages
      [TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 m1,
       TypedInteraction.pulledIfValue memoryChannel 1 m2,
       TypedInteraction.pushedIfValue memoryChannel 1 b1,
       TypedInteraction.pulledIfValue memoryChannel 1 m3,
       TypedInteraction.pushedIfValue memoryChannel 1 b2,
       TypedInteraction.pushedIfValue memoryChannel 1 w] = [b1, b2, w] := by
  have filtered : List.filter (fun i => signedVal i.mult = 1)
      [TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 m1,
       TypedInteraction.pulledIfValue memoryChannel 1 m2,
       TypedInteraction.pushedIfValue memoryChannel 1 b1,
       TypedInteraction.pulledIfValue memoryChannel 1 m3,
       TypedInteraction.pushedIfValue memoryChannel 1 b2,
       TypedInteraction.pushedIfValue memoryChannel 1 w] =
      [TypedInteraction.pushedIfValue memoryChannel 1 b1,
       TypedInteraction.pushedIfValue memoryChannel 1 b2,
       TypedInteraction.pushedIfValue memoryChannel 1 w] := by
    simp only [List.filter_cons, List.filter_nil, memPull_one_signed, memPush_one_signed]
    norm_num
  rw [producedMessages, filtered]
  simp only [List.map_cons, List.map_nil, TypedInteraction.pushedIfValue_message]

/-- A canonical active R-type six-pack consumes exactly its three prior register records. -/
theorem consumedMemoryMessages_eq_of_rtypeShape {chip : SupportedChip p}
    (shape : RTypeMemoryInteractionShape chip) (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1) :
    decoded.consumedMemoryMessages data =
      [rtypePriorMessage (decoded.toChipRow data).view
         (decoded.toChipRow data).view.adapter.op_a
         (decoded.toChipRow data).view.adapter.op_a_memory,
       rtypePriorMessage (decoded.toChipRow data).view
         (decoded.toChipRow data).view.adapter.op_b[0]
         (decoded.toChipRow data).view.adapter.op_b_memory,
       rtypePriorMessage (decoded.toChipRow data).view
         (decoded.toChipRow data).view.adapter.op_c[0]
         (decoded.toChipRow data).view.adapter.op_c_memory] := by
  unfold DecodedInstructionRow.consumedMemoryMessages
  rw [shape decoded data hchip]
  unfold rtypeMemoryInteractions
  rw [real]
  exact consumedMessages_rtypeSix _ _ _ _ _ _

/-- A canonical active R-type six-pack produces its two source read-backs and destination write. -/
theorem producedMemoryMessages_eq_of_rtypeShape {chip : SupportedChip p}
    (shape : RTypeMemoryInteractionShape chip) (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1) :
    decoded.producedMemoryMessages data =
      [rtypeReadBackMessage (decoded.toChipRow data).view
         (decoded.toChipRow data).view.adapter.op_b[0]
         (decoded.toChipRow data).view.adapter.op_b_memory 3,
       rtypeReadBackMessage (decoded.toChipRow data).view
         (decoded.toChipRow data).view.adapter.op_c[0]
         (decoded.toChipRow data).view.adapter.op_c_memory 2,
       rtypeWriteMessage (decoded.toChipRow data).view] := by
  unfold DecodedInstructionRow.producedMemoryMessages
  rw [shape decoded data hchip]
  unfold rtypeMemoryInteractions
  rw [real]
  exact producedMessages_rtypeSix _ _ _ _ _ _

/-- The six-pack itself supplies both exact register-source pull witnesses. -/
theorem registerOperandPullShape_of_rtypeShape {chip : SupportedChip p}
    (shape : RTypeMemoryInteractionShape chip) :
    DecodedInstructionRow.RegisterOperandPullShape chip := by
  constructor
  · intro data physical program state
    dsimp only
    intro ready _constraints real index immediate indexEq
    let decoded : DecodedInstructionRow p := ⟨chip, physical⟩
    let view := (decoded.toChipRow data).view
    have consumed := consumedMemoryMessages_eq_of_rtypeShape shape decoded data rfl real
    let message := rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory
    refine ⟨message, ?_, ?_, rfl⟩
    · change message ∈ decoded.consumedMemoryMessages data
      rw [consumed]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact Semantics.MemoryMsg.locOf_register message index indexEq rfl rfl
  · intro data physical program state
    dsimp only
    intro ready _constraints real index immediate indexEq
    let decoded : DecodedInstructionRow p := ⟨chip, physical⟩
    let view := (decoded.toChipRow data).view
    have consumed := consumedMemoryMessages_eq_of_rtypeShape shape decoded data rfl real
    let message := rtypePriorMessage view view.adapter.op_c[0] view.adapter.op_c_memory
    refine ⟨message, ?_, ?_, rfl⟩
    · change message ∈ decoded.consumedMemoryMessages data
      rw [consumed]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact Semantics.MemoryMsg.locOf_register message index indexEq rfl rfl

/-- An active decoded Add row's consumed Memory messages, in view form. -/
theorem addChip_consumedMemoryMessages_eq (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = addChipDescriptor (p := p))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    decoded.consumedMemoryMessages data =
      [rtypePriorMessage (decoded.toChipRow data).view
         (decoded.toChipRow data).view.adapter.op_a
         (decoded.toChipRow data).view.adapter.op_a_memory,
       rtypePriorMessage (decoded.toChipRow data).view
         ((decoded.toChipRow data).view.adapter.op_b[0])
         (decoded.toChipRow data).view.adapter.op_b_memory,
       rtypePriorMessage (decoded.toChipRow data).view
         ((decoded.toChipRow data).view.adapter.op_c[0])
         (decoded.toChipRow data).view.adapter.op_c_memory] := by
  unfold DecodedInstructionRow.consumedMemoryMessages
  rw [addChip_typedMemoryInteractions_eq decoded data hchip, real]
  exact consumedMessages_rtypeSix _ _ _ _ _ _

/-- An active decoded Add row's produced Memory messages, in view form. -/
theorem addChip_producedMemoryMessages_eq (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = addChipDescriptor (p := p))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    decoded.producedMemoryMessages data =
      [rtypeReadBackMessage (decoded.toChipRow data).view
         ((decoded.toChipRow data).view.adapter.op_b[0])
         (decoded.toChipRow data).view.adapter.op_b_memory 3,
       rtypeReadBackMessage (decoded.toChipRow data).view
         ((decoded.toChipRow data).view.adapter.op_c[0])
         (decoded.toChipRow data).view.adapter.op_c_memory 2,
       rtypeWriteMessage (decoded.toChipRow data).view] := by
  unfold DecodedInstructionRow.producedMemoryMessages
  rw [addChip_typedMemoryInteractions_eq decoded data hchip, real]
  exact producedMessages_rtypeSix _ _ _ _ _ _

/-! ### The remaining wiring inputs from the audited surfaces -/

/-- The clock byte bounds of an Add row's view, from the finished Byte channel and the retained
CPU-reader contract. -/
theorem addChip_viewClockBounds (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = addChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ViewClockBounds (decoded.toChipRow data).view := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = addChipDescriptor (p := p) := hchip
  subst hchip'
  exact viewClockBounds_of_cpuStateContract (AddChip.circuit (p := p)) AddChip.rowView
    AddChip.cpuStateTimeContract data physical guarantees real

/-- The exact R-type reader input retained by `AddChip.main`.  Keeping this construction opaque and
crossing its scalar spellings with the `rfl` lemmas below prevents the elaborator from normalizing a
large nested `Var RTypeReader.Inputs` merely to read one field. -/
def addChipRTypeInput (input : Var AddChip.Inputs (ZMod p)) (offset : ℕ) :
    Var Readers.RTypeReader.Inputs (ZMod p) :=
  let value : Word (Expression (ZMod p)) :=
    Vector.mapRange 4 fun i => var { index := offset + i }
  ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 0,
    value[0], value[1], value[2], value[3]⟩

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
@[circuit_norm] theorem addChipRTypeInput_isReal
    (input : Var AddChip.Inputs (ZMod p)) (offset : ℕ) :
    (addChipRTypeInput input offset).is_real = input.is_real := rfl

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
@[circuit_norm] theorem addChipRTypeInput_adapter
    (input : Var AddChip.Inputs (ZMod p)) (offset : ℕ) :
    (addChipRTypeInput input offset).cols = input.adapter := rfl

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
@[circuit_norm] theorem addChipRTypeInput_clkLow
    (input : Var AddChip.Inputs (ZMod p)) (offset : ℕ) :
    (addChipRTypeInput input offset).clk_low =
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 := rfl

omit [Fact (2 ^ 25 < p)] in
/-- Add's retained R-type reader, expressed through the family-level scalar timestamp contract. -/
theorem AddChip.rtypeTimestampContract :
    CircuitRTypeTimestampContract (p := p) (AddChip.circuit (p := p)) AddChip.rowView := by
  let input : Var AddChip.Inputs (ZMod p) := varFromOffset AddChip.Inputs 0
  let offset := size AddChip.Inputs
  let readerInput : Var Readers.RTypeReader.Inputs (ZMod p) := addChipRTypeInput input offset
  refine ⟨offset + 4, readerInput, ?_, ?_⟩
  · simp only [input, offset, readerInput, addChipRTypeInput, AddChip.circuit, AddChip.main,
      Readers.RTypeReader.circuit, circuit_norm]
  · intro env
    constructor <;>
      simp only [input, offset, readerInput, addChipRTypeInput, AddChip.circuit, AddChip.rowView,
        Extracted.RTypeReader.toAdapterView, circuit_norm]

/-- An active Add row's three register timestamp decompositions come entirely from its finished
Byte-channel guarantees.  This is the chip-level navigation from the retained R-type reader to the
independent semantic row; unlike the chip `Spec`, it requires no Memory pull currency. -/
theorem addChip_activeTimestampBounds (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = addChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    RTypeTimestampBounds (decoded.toChipRow data).view := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = addChipDescriptor (p := p) := hchip
  subst hchip'
  exact rtypeTimestampBounds_of_contract AddChip.circuit AddChip.rowView
    AddChip.rtypeTimestampContract data physical guarantees real

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
/-- The reader's decode bound `op_a < 32`, read off the chip `Spec`'s composed R-type contract. -/
theorem addChip_opa_lt (inp : AddChip.Inputs (ZMod p)) (cols : AddChip.Columns (ZMod p))
    (data : ProverData (ZMod p)) (real : inp.is_real = 1)
    (spec : AddChip.Spec inp cols data) :
    (AddChip.rowView inp cols).adapter.op_a.val < 32 := by
  obtain ⟨hrspec, -, -⟩ := spec
  obtain ⟨-, -, -, -, -, hbounds, -⟩ := hrspec
  exact (hbounds real).1

/-- The row's own push `Requirements`, from the same open-inputs seam that yields `chipSpec`: the
finished Byte/Program channels, the vacuous State channel, and the grounded Memory guarantees make
`Component.weakSoundness` fire, and its second half is exactly the interaction requirements. -/
theorem fullRequirements_of_openSoundnessInputs
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (decoded : DecodedInstructionRow p)
    (decodedMem : decoded ∈ decodedInstructionRows (p := p) witness.tables)
    (openInputs : DecodedRowOpenSoundnessInputs decoded witness.data) :
    decoded.chip.table.operations.FullRequirements (decoded.environment witness.data) := by
  have finished := witness_decodedRow_finishedChannelGuarantees witness constraints balanced
    decoded decodedMem
  have guarantees := (DecodedRowChannelGuarantees.mk
    (decodedRow_stateChannelGuarantees decoded witness.data)
    finished.1 finished.2 openInputs.memory).full
    (decoded.usesSupportedBusChannels_of_mem witness.tables decodedMem)
  exact (Component.weakSoundness openInputs.assumptions
    (decodedInstructionRow_constraints witness constraints decoded decodedMem) guarantees).2

/-- Every produced Memory message of a row with proved push requirements is a well-formed `U64` —
in particular the `op_a` write value's range check reaches the wiring. -/
theorem producedMemoryMessages_isU64_of_fullRequirements (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p))
    (requirements : decoded.chip.table.operations.FullRequirements
      (decoded.environment data)) :
    ∀ m ∈ decoded.producedMemoryMessages data, MemoryMsg.isU64 m := by
  intro m hm
  unfold DecodedInstructionRow.producedMemoryMessages producedMessages at hm
  obtain ⟨interaction, hfilter, rfl⟩ := List.mem_map.mp hm
  obtain ⟨hmem, hpos⟩ := List.mem_filter.mp hfilter
  simp only [decide_eq_true_eq] at hpos
  have rawReq : interaction.raw.Requirements (decoded.environment data).data := by
    unfold DecodedInstructionRow.interactionsWith typedInteractionValuesWith at hmem
    obtain ⟨⟨abstract, amem⟩, -, rfl⟩ := List.mem_map.mp hmem
    exact requirements abstract (List.mem_of_mem_filter amem)
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  -- G1: the guarantee is now the pair `isU64 ∧ ClkBound`; the wiring wants only the value half.
  exact (interaction.guarantee_of_requirements (decoded.environment data).data hp rawReq hpos).1

/-! ### The wiring corollary and the end-to-end demo -/

/-- Assemble a decoded row's `RowWiring` from the R-type shape lemma and its exact Memory lists. -/
theorem rowWiring_rtype_of_decoded (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p))
    (bounds : ViewClockBounds (decoded.toChipRow data).view)
    (commit_eq : (decoded.toChipRow data).view.commit = Trace.CommitEffect.regWrite)
    (opa_lt : (decoded.toChipRow data).view.adapter.op_a.val < 32)
    (write_isU64 : Word.isU64 (decoded.toChipRow data).view.rdWrite)
    (consumed_eq : decoded.consumedMemoryMessages data =
      [rtypePriorMessage (decoded.toChipRow data).view
         (decoded.toChipRow data).view.adapter.op_a
         (decoded.toChipRow data).view.adapter.op_a_memory,
       rtypePriorMessage (decoded.toChipRow data).view
         ((decoded.toChipRow data).view.adapter.op_b[0])
         (decoded.toChipRow data).view.adapter.op_b_memory,
       rtypePriorMessage (decoded.toChipRow data).view
         ((decoded.toChipRow data).view.adapter.op_c[0])
         (decoded.toChipRow data).view.adapter.op_c_memory])
    (produced_eq : decoded.producedMemoryMessages data =
      [rtypeReadBackMessage (decoded.toChipRow data).view
         ((decoded.toChipRow data).view.adapter.op_b[0])
         (decoded.toChipRow data).view.adapter.op_b_memory 3,
       rtypeReadBackMessage (decoded.toChipRow data).view
         ((decoded.toChipRow data).view.adapter.op_c[0])
         (decoded.toChipRow data).view.adapter.op_c_memory 2,
       rtypeWriteMessage (decoded.toChipRow data).view]) :
    RowWiring (decoded.toChipRow data).view (decoded.ordinaryRowFacts data) := by
  refine rowWiring_rtype bounds commit_eq opa_lt write_isU64 rfl rfl ?_ ?_
  · rw [DecodedInstructionRow.ordinaryRowFacts_memPulls, consumed_eq]
    rfl
  · rw [DecodedInstructionRow.ordinaryRowFacts_memPushes]
    exact produced_eq

-- (The former Add-specific `addRow_engineFacts` validation instance was retired with the D0
-- conditional-feed refactor: `engineFacts_of_kind` now takes currency-`wiringOf`/`specOf` builders,
-- and the generic bundle consumer `ChipGroundingContracts.engineFacts` supersedes it.)

/-- **The R-type aligned-carrier constructor** (the `AlignedCarrier` sibling of
`rowWiring_rtype_of_decoded`): a genuine decoded six-pack row's `ordinaryRowFacts` feed `rowAligned_rtype`.
The three operand-index bounds come from Program decoding, while `timestampBounds` comes solely from
the retained R-type reader's Byte guarantees.  The received prior-record `ClkBound`s remain conditional
inputs to the final slot implication and are supplied later by the memory grounding walk. -/
theorem rowAligned_rtype_of_shape {chip : SupportedChip p}
    (shape : RTypeMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1)
    (bounds : ViewClockBounds (decoded.toChipRow data).view)
    (timestampBounds : RTypeTimestampBounds (decoded.toChipRow data).view)
    (opa_lt : (decoded.toChipRow data).view.adapter.op_a.val < 32)
    (opb_lt : ((decoded.toChipRow data).view.adapter.op_b[0]).val < 32)
    (opc_lt : ((decoded.toChipRow data).view.adapter.op_c[0]).val < 32) :
    AlignsWith (alignedOf (decoded.ordinaryRowFacts data)
        (rtypeTouches (decoded.toChipRow data).view (decoded.ordinaryRowFacts data)))
        (decoded.ordinaryRowFacts data) ∧
      (∀ tc ∈ rtypeTouches (decoded.toChipRow data).view (decoded.ordinaryRowFacts data),
        TouchOK (StateMsg.timeNat (decoded.ordinaryRowFacts data).statePull) tc.1 tc.2) ∧
      (∀ loc : MemLoc, List.IsChain
        (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2)
        ((rtypeTouches (decoded.toChipRow data).view (decoded.ordinaryRowFacts data)).filter
          (fun pq => MemoryMsg.locOf pq.2 = loc))) ∧
      (∀ tc ∈ rtypeTouches (decoded.toChipRow data).view (decoded.ordinaryRowFacts data),
        SP1Clean.Channels.MemoryMsg.ClkBound tc.2) ∧
      (∀ tc ∈ rtypeTouches (decoded.toChipRow data).view (decoded.ordinaryRowFacts data),
        SP1Clean.Channels.MemoryMsg.ClkBound (tc : Touch p).1.1 →
        MemoryMsg.timeNat (tc : Touch p).1.1 < MemoryMsg.timeNat tc.2) := by
  have consumed_eq := consumedMemoryMessages_eq_of_rtypeShape shape decoded data hchip real
  have produced_eq := producedMemoryMessages_eq_of_rtypeShape shape decoded data hchip real
  obtain ⟨hts_a, hts_b, hts_c⟩ := timestampBounds
  -- The conditional `slot` combines the Byte-derived local timestamp bounds with the pulled
  -- record's received `ClkBound`; neither side assumes the conclusion of the grounding walk.
  have hslots : ∀ tc ∈ rtypeTouches (decoded.toChipRow data).view (decoded.ordinaryRowFacts data),
      SP1Clean.Channels.MemoryMsg.ClkBound (tc : Touch p).1.1 →
      MemoryMsg.timeNat (tc : Touch p).1.1 < MemoryMsg.timeNat tc.2 := by
    intro tc htc hclk
    simp only [rtypeTouches, List.mem_cons, List.not_mem_nil, or_false] at htc
    rcases htc with rfl | rfl | rfl
    · exact TimeExtraction.memoryTimeNat_lt_of_activeTimestampBounds
        _ _ _ _ _ hclk hts_c rfl rfl rfl
    · exact TimeExtraction.memoryTimeNat_lt_of_activeTimestampBounds
        _ _ _ _ _ hclk hts_b rfl rfl rfl
    · exact TimeExtraction.memoryTimeNat_lt_of_activeTimestampBounds
        _ _ _ _ _ hclk hts_a rfl rfl rfl
  refine rowAligned_rtype bounds real opa_lt opb_lt opc_lt rfl ?_ ?_ hslots
  · rw [DecodedInstructionRow.ordinaryRowFacts_memPulls, consumed_eq]
    rfl
  · rw [DecodedInstructionRow.ordinaryRowFacts_memPushes]
    exact produced_eq

end AddAnchor

/-! ## R-type family: Sub -/

section SubAnchor

variable [Fact (2 ^ 25 < p)]

omit [Fact (2 ^ 25 < p)] in
/-- The Sub instruction descriptor (entry 3 of `supportedChips`). -/
def subChipDescriptor : SupportedChip p :=
  ⟨SubChip.kind, SubChip.circuit, rfl, [.SUB], .nonX0⟩

omit [Fact (2 ^ 25 < p)] in
noncomputable def subViewOf (env : Environment (ZMod p)) : Trace.RowView (ZMod p) :=
  SubChip.rowView ((⟨SubChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
    ((⟨SubChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env)

theorem subViewOf_decodeRow (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    ((subChipDescriptor (p := p)).decodeRow data physical).view =
      subViewOf (Environment.fromArray physical data) := rfl

theorem subChipDescriptor_table :
    (subChipDescriptor (p := p)).table =
      (⟨SubChip.circuit (p := p)⟩ : Component (ZMod p)) := rfl

omit [Fact (2 ^ 25 < p)] in
theorem subChip_circuit_output_eq (input : Var SubChip.Inputs (ZMod p)) (offset : ℕ) :
    (SubChip.circuit (p := p)).output input offset =
      (⟨input.is_real, input.state, input.adapter,
         ⟨Vector.mapRange 4 fun i => var { index := offset + i }⟩⟩ :
        Var SubChip.Columns (ZMod p)) := rfl

omit [Fact (2 ^ 25 < p)] in
/-- Sub's public exposed Memory list evaluates to the common R-type six-pack. -/
theorem subChip_memoryInteractionValues_eq (env : Environment (ZMod p)) :
    (⟨SubChip.circuit (p := p)⟩ : Component (ZMod p)).operations.interactionValuesWith
        (memoryChannel (p := p)).toRaw env =
      (rtypeMemoryInteractions (subViewOf env)).map TypedInteraction.raw := by
  rw [Operations.interactionValuesWith_eq_map, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval env)
      (((SubChip.main (varFromOffset SubChip.Inputs 0)).operations
        (size SubChip.Inputs)).interactionsWith (memoryChannel (p := p)).toRaw) = _
  rw [SubChip.interactionsWith_memory_eq]
  have inputEq : Eval.eval env (varFromOffset SubChip.Inputs 0) =
      (⟨SubChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset SubChip.Inputs 0 env
  have outputEq : Eval.eval env
      ((SubChip.circuit (p := p)).output (varFromOffset SubChip.Inputs 0)
        (size SubChip.Inputs)) =
      (⟨SubChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env := by
    simp only [Component.rowOutput, circuit_norm]
  simp only [SubChip.exposedMemoryInteractions, rtypeMemoryInteractions, List.map_cons,
    List.map_nil, TypedInteraction.pulledIfValue_raw, TypedInteraction.pushedIfValue_raw,
    Channel.eval_pulledIf, Channel.eval_pushedIf, eval_registerMemoryMessage]
  simp only [subViewOf, ← inputEq, ← outputEq, rtypePriorMessage, rtypeReadBackMessage,
    rtypeWriteMessage, SubChip.rowView, Extracted.RTypeReader.toAdapterView]
  simp only [circuit_norm, subChip_circuit_output_eq]

/-- Lift Sub's raw evaluated six-pack to the typed decoded-row adapter. -/
theorem subChip_typedMemoryInteractions_eq (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = subChipDescriptor (p := p)) :
    decoded.interactionsWith data memoryChannel =
      rtypeMemoryInteractions (decoded.toChipRow data).view := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = subChipDescriptor (p := p) := hchip
  subst hchip'
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [DecodedInstructionRow.interactionsWith_raw]
  simpa only [DecodedInstructionRow.environment, DecodedInstructionRow.toChipRow,
    subViewOf_decodeRow, subChipDescriptor_table] using
    subChip_memoryInteractionValues_eq (Environment.fromArray physical data)

/-- Sub instantiates the shared R-type six-pack contract. -/
theorem subChip_rtypeMemoryInteractionShape :
    RTypeMemoryInteractionShape (subChipDescriptor (p := p)) :=
  subChip_typedMemoryInteractions_eq

/-- The exact R-type reader input retained by `SubChip.main`. -/
def subChipRTypeInput (input : Var SubChip.Inputs (ZMod p)) (offset : ℕ) :
    Var Readers.RTypeReader.Inputs (ZMod p) :=
  let value : Word (Expression (ZMod p)) :=
    Vector.mapRange 4 fun i => var { index := offset + i }
  ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 2,
    value[0], value[1], value[2], value[3]⟩

omit [Fact (2 ^ 25 < p)] in
/-- Sub's retained R-type reader, through the family scalar timestamp contract. -/
theorem SubChip.rtypeTimestampContract :
    CircuitRTypeTimestampContract (p := p) (SubChip.circuit (p := p)) SubChip.rowView := by
  let input : Var SubChip.Inputs (ZMod p) := varFromOffset SubChip.Inputs 0
  let offset := size SubChip.Inputs
  let readerInput : Var Readers.RTypeReader.Inputs (ZMod p) := subChipRTypeInput input offset
  refine ⟨offset + 4, readerInput, ?_, ?_⟩
  · simp only [input, offset, readerInput, subChipRTypeInput, SubChip.circuit, SubChip.main,
      Readers.RTypeReader.circuit, circuit_norm]
  · intro env
    constructor <;>
      simp only [input, offset, readerInput, subChipRTypeInput, SubChip.circuit, SubChip.rowView,
        Extracted.RTypeReader.toAdapterView, circuit_norm]

/-- Finished Byte guarantees bound Sub's view clock limbs. -/
theorem subChip_viewClockBounds (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = subChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ViewClockBounds (decoded.toChipRow data).view := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = subChipDescriptor (p := p) := hchip
  subst hchip'
  exact viewClockBounds_of_cpuStateContract (SubChip.circuit (p := p)) SubChip.rowView
    SubChip.cpuStateTimeContract data physical guarantees real

/-- Finished Byte guarantees supply Sub's three timestamp decompositions. -/
theorem subChip_activeTimestampBounds (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = subChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    RTypeTimestampBounds (decoded.toChipRow data).view := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = subChipDescriptor (p := p) := hchip
  subst hchip'
  exact rtypeTimestampBounds_of_contract SubChip.circuit SubChip.rowView
    SubChip.rtypeTimestampContract data physical guarantees real

end SubAnchor

end SP1Clean.Soundness
