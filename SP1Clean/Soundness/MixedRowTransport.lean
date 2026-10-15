import SP1Clean.Soundness.RefreshWiring
import SP1Clean.Soundness.GenericWalk

/-! # Semantic transport for mixed execution rows

`ValueAligned` transports ordinary rows whose original reads all occur at window start.
System rows also read at offsets two and three. `WindowAligned` replaces that restriction with
the location's pre-effect read window. It transports step/frame facts over any trajectory and
survives refresh elimination and canonical State re-limbing. It does not identify the historical
truth of a rewritten prior record with that of the original record: only operand currency moves.
-/

namespace SP1Clean.Soundness.TimedGrounding

open SP1Clean.Semantics SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Each read observes the location before this row's effect. Register reads may occur at any
of offsets zero through three; RAM reads occur at offset zero. -/
def ReadsInWindow (row : RowFacts p) : Prop :=
  ∀ pull ∈ row.memPulls, StateMsg.timeNat row.statePull ≤ pull.2 ∧
    pull.2 ≤ StateMsg.timeNat row.statePull + readWindow (MemoryMsg.locOf pull.1)

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- Paired touch shape places every read inside its pre-effect window. -/
theorem RowOKCore.readsInWindow {initialClock : ℕ} {row : RowFacts p}
    (ok : RowOKCore initialClock row) : ReadsInWindow row := by
  intro pull member
  obtain ⟨_, _, touch⟩ := forall₂_exists_right ok.touches pull member
  exact ⟨touch.read_lo, touch.read_hi⟩

/-- Semantic alignment across a read permutation, refresh rewrite, or State re-limbing.
Both original and matched reads stay within the same pre-effect window. -/
structure WindowAligned (newer original : RowFacts p) : Prop where
  pullTime : StateMsg.timeNat newer.statePull = StateMsg.timeNat original.statePull
  pullPc : StateMsg.pcBits newer.statePull = StateMsg.pcBits original.statePull
  pushTime : StateMsg.timeNat newer.statePush = StateMsg.timeNat original.statePush
  pushPc : StateMsg.pcBits newer.statePush = StateMsg.pcBits original.statePush
  fetch : newer.fetch = original.fetch
  pushes : newer.memPushes.Perm original.memPushes
  pullClk : ∀ pull ∈ original.memPulls, MemoryMsg.ClkBound pull.1
  originalReads : ReadsInWindow original
  match_ : ∀ pull ∈ original.memPulls, ∃ matched ∈ newer.memPulls,
    MemoryMsg.locOf matched.1 = MemoryMsg.locOf pull.1 ∧ matched.1.value = pull.1.value ∧
    StateMsg.timeNat newer.statePull ≤ matched.2 ∧
      matched.2 ≤ StateMsg.timeNat newer.statePull + readWindow (MemoryMsg.locOf pull.1)

omit [Fact (2 ^ 17 < p)] in
/-- Currency of matched reads gives currency of the original operands, including mixed read
micro-times. The old record's low-clock bound is supplied independently of its value truth. -/
theorem WindowAligned.pullCurrency {program : Target.GuestProgram} {traj : Trajectory}
    {initial : SailState} {timeline : Timeline} {newer original : RowFacts p}
    (aligned : WindowAligned newer original)
    (state : LocalStateTruthG program traj timeline newer.statePull)
    (currency : ∀ pull ∈ newer.memPulls, MemoryMsg.isU64 pull.1 ∧ MemoryMsg.ClkBound pull.1 ∧
      LocalValueAtG traj initial timeline (MemoryMsg.locOf pull.1) pull.2 pull.1.value) :
    ∀ pull ∈ original.memPulls, MemoryMsg.isU64 pull.1 ∧ MemoryMsg.ClkBound pull.1 ∧
      LocalValueAtG traj initial timeline (MemoryMsg.locOf pull.1) pull.2 pull.1.value := by
  obtain ⟨n, _, _, time, _⟩ := state
  intro pull member
  obtain ⟨matched, matchedMem, loc, value, lo, hi⟩ := aligned.match_ pull member
  obtain ⟨word, _, current⟩ := currency matched matchedMem
  have window := aligned.originalReads pull member
  rw [loc, value] at current
  rw [time] at lo hi
  rw [← aligned.pullTime, time] at window
  refine ⟨?_, aligned.pullClk pull member,
    localValueAtG_shift_window _ lo hi window.1 window.2 current⟩
  unfold MemoryMsg.isU64 at word ⊢
  rwa [value] at word

omit [Fact (2 ^ 17 < p)] in
/-- A mixed row's step proof survives semantic alignment. -/
theorem WindowAligned.stepFact {program : Target.GuestProgram} {traj : Trajectory}
    {initial : SailState} {timeline : Timeline} {newer original : RowFacts p}
    (aligned : WindowAligned newer original)
    (step : LocalStepFactG program traj initial timeline original) :
    LocalStepFactG program traj initial timeline newer := by
  intro state currency
  obtain ⟨next, pushes⟩ := step
    (localStateTruthG_congr aligned.pullTime.symm aligned.pullPc.symm state)
    (aligned.pullCurrency state currency)
  exact ⟨localStateTruthG_congr aligned.pushTime aligned.pushPc next,
    fun message member => pushes message (aligned.pushes.mem_iff.mp member)⟩

omit [Fact (2 ^ 17 < p)] in
/-- A mixed row's frame proof survives semantic alignment. -/
theorem WindowAligned.frameFact {program : Target.GuestProgram} {traj : Trajectory}
    {initial : SailState} {timeline : Timeline} {newer original : RowFacts p}
    (aligned : WindowAligned newer original)
    (frame : FrameFactG program traj initial timeline original) :
    FrameFactG program traj initial timeline newer := by
  intro state currency loc value pushes current
  rw [aligned.pullTime] at current
  have preserved := frame
    (localStateTruthG_congr aligned.pullTime.symm aligned.pullPc.symm state)
    (aligned.pullCurrency state currency) loc value
    (fun message member => pushes message (aligned.pushes.mem_iff.mpr member)) current
  rw [aligned.pushTime]
  exact preserved

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- Refresh elimination preserves semantic alignment, including the matched read micro-times. -/
theorem WindowAligned.pullRewrite {newer original : RowFacts p} {touches : List (Touch p)}
    (aligned : WindowAligned newer original)
    (paired : newer.memPulls.length = newer.memPushes.length)
    (rewrite : List.Forall₂ PullRewrite (newer.memPulls.zip newer.memPushes) touches) :
    WindowAligned (alignedOf newer touches) original := by
  have pulls : (newer.memPulls.zip newer.memPushes).map Prod.fst = newer.memPulls :=
    List.map_fst_zip paired.le
  have pushes : touches.map Prod.snd = newer.memPushes := by
    rw [map_snd_eq_of_forall₂ (fun a b (h : PullRewrite a b) => h.2.1) rewrite,
      List.map_snd_zip paired.symm.le]
  refine ⟨aligned.pullTime, aligned.pullPc, aligned.pushTime, aligned.pushPc,
    aligned.fetch, ?_, aligned.pullClk, aligned.originalReads, ?_⟩
  · change (touches.map Prod.snd).Perm original.memPushes
    rw [pushes]
    exact aligned.pushes
  · intro pull member
    obtain ⟨matched, matchedMem, loc, value, lo, hi⟩ := aligned.match_ pull member
    rw [← pulls] at matchedMem
    obtain ⟨touch, touchMem, same⟩ := List.mem_map.mp matchedMem
    obtain ⟨updated, updatedMem, related⟩ := forall₂_exists_right rewrite touch touchMem
    refine ⟨updated.1, List.mem_map_of_mem updatedMem, ?_, ?_, ?_, ?_⟩
    · exact related.2.2.1.trans (same ▸ loc)
    · exact related.2.2.2.1.trans (same ▸ value)
    · change StateMsg.timeNat newer.statePull ≤ updated.1.2
      rw [related.1, same]
      exact lo
    · change updated.1.2 ≤ StateMsg.timeNat newer.statePull + readWindow (MemoryMsg.locOf pull.1)
      rw [related.1, same]
      exact hi

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- Canonical State limbs preserve the mixed-row semantic transport. -/
theorem WindowAligned.stateRespell {newer original : RowFacts p} (aligned : WindowAligned newer original)
    {pull push : StateMsg (ZMod p)}
    (pullTime : StateMsg.timeNat pull = StateMsg.timeNat newer.statePull)
    (pullPc : StateMsg.pcBits pull = StateMsg.pcBits newer.statePull)
    (pushTime : StateMsg.timeNat push = StateMsg.timeNat newer.statePush)
    (pushPc : StateMsg.pcBits push = StateMsg.pcBits newer.statePush) :
    WindowAligned (stateRespell newer pull push) original where
  pullTime := pullTime.trans aligned.pullTime
  pullPc := pullPc.trans aligned.pullPc
  pushTime := pushTime.trans aligned.pushTime
  pushPc := pushPc.trans aligned.pushPc
  fetch := aligned.fetch
  pushes := aligned.pushes
  pullClk := aligned.pullClk
  originalReads := aligned.originalReads
  match_ := by
    intro originalPull member
    obtain ⟨matched, matchedMem, loc, value, lo, hi⟩ := aligned.match_ originalPull member
    exact ⟨matched, matchedMem, loc, value, by simpa only [stateRespell_statePull, pullTime] using lo,
      by simpa only [stateRespell_statePull, pullTime] using hi⟩

end SP1Clean.Soundness.TimedGrounding
