import SP1Clean.Soundness.TimedGrounding
import SP1Clean.Soundness.Walk
import SP1Clean.Model.Semantics.GenericTruth
import SP1Clean.Model.Semantics.EventTime

/-! # The grounding walk over an arbitrary trajectory

`TimedGrounding.walkT` is the engine: given per-row step and frame facts, the row-shape discipline,
the timeline agreement, a true head, a true genesis frontier, and the two multiset balances, every
pull's guarantee holds. Its statement is already timeline-relative — `RowOKCore`'s window is a
`+8 ≤` lower bound, not an exact width — so a 264-tick row satisfies its *shape* obligations
verbatim.

What it is not generic in is the **step relation**. `LocalStateTruthT` demands a `SailChain`, and a
syscall step deliberately is not one, so no timeline makes a syscall row a walk member.

This file states the walk once over `Semantics.Trajectory` and derives the two instantiations:

* `walkT` — at `sailTrajectory`, recovering the existing engine *unchanged*. This is the acceptance
  test for the whole refactor: if a consumer of `walkT` has to move, the generalization was
  mis-stated.
* `walkE` — at `Semantics.eventTrajectory`, where a step may be an ordinary Sail step or a handled
  syscall, and the timeline is the transcript's own prefix-summed durations.

The three predicate bridges that `GenericTruth.lean` could not state — its import does not reach
`FrameFactT`/`LiveOKT`/`GroundedT` — are here, beside the walk that consumes them. -/

namespace SP1Clean.Soundness.TimedGrounding

open SP1Clean.Semantics
open SP1Clean.Soundness.Target
open SP1Clean.Channels (StateMsg MemoryMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## The remaining Sail bridges -/

omit [Fact (2 ^ 17 < p)] in
theorem frameFactG_sail {program : GuestProgram} {initial : SailState} {tl : Timeline}
    {r : RowFacts p} :
    FrameFactG program (sailTrajectory initial) initial tl r ↔ FrameFactT program initial tl r := by
  unfold FrameFactG FrameFactT
  simp only [localStateTruthG_sail, localValueAtG_sail]

omit [Fact (2 ^ 17 < p)] in
theorem liveOKG_sail {initial : SailState} {tl : Timeline} {t : ℕ}
    {live : MemLoc → Option (MemoryMsg (ZMod p))} :
    LiveOKG (sailTrajectory initial) initial tl t live ↔ LiveOKT initial tl t live := by
  unfold LiveOKG LiveOKT
  simp only [localMemTruthG_sail, localValueAtG_sail]

omit [Fact (2 ^ 17 < p)] in
theorem groundedG_sail {program : GuestProgram} {initial : SailState} {tl : Timeline}
    {r : RowFacts p} :
    GroundedG program (sailTrajectory initial) initial tl r ↔ GroundedT program initial tl r := by
  unfold GroundedG GroundedT
  simp only [localStateTruthG_sail, localMemTruthG_sail, localValueAtG_sail]

omit [Fact (2 ^ 17 < p)] in
/-- `pull_clkBound_of_balance` over the trajectory. Its only use of the frontier is the
`ClkBound` projection, which is trajectory-independent, so the generalization is a rename. -/
lemma pull_clkBound_of_balanceG {traj : Trajectory} {initial : SailState} {tl : Timeline} {initialClock t : ℕ}
    {rows : List (RowFacts p)} {live finM : MemLoc → Option (MemoryMsg (ZMod p))}
    (h_ok : ∀ r ∈ rows, RowOKCore initialClock r)
    (h_live : LiveOKG traj initial tl t live)
    (h_mbal : ∀ loc : MemLoc, optMS (live loc) + pushesAt rows loc
      = optMS (finM loc) + pullsAt rows loc)
    {r : RowFacts p} (hr : r ∈ rows) {mp : MemoryMsg (ZMod p) × ℕ} (hmp : mp ∈ r.memPulls) :
    SP1Clean.Channels.MemoryMsg.ClkBound mp.1 := by
  have hmp1_in : mp.1 ∈ rowPullsAt r (MemoryMsg.locOf mp.1) := by
    rw [rowPullsAt]; exact List.mem_filter.mpr ⟨List.mem_map.mpr ⟨mp, hmp, rfl⟩, by simp⟩
  have hmem_pull : mp.1 ∈ pullsAt rows (MemoryMsg.locOf mp.1) := by
    rw [pullsAt]; exact (mem_listSum_map _ rows mp.1).mpr ⟨r, hr, Multiset.mem_coe.mpr hmp1_in⟩
  have hmem_lhs : mp.1 ∈ optMS (live (MemoryMsg.locOf mp.1))
      + pushesAt rows (MemoryMsg.locOf mp.1) := by
    rw [h_mbal (MemoryMsg.locOf mp.1)]; exact Multiset.mem_add.mpr (Or.inr hmem_pull)
  rcases Multiset.mem_add.mp hmem_lhs with hlive_mem | hpush_mem
  · cases hlv : live (MemoryMsg.locOf mp.1) with
    | none => rw [hlv] at hlive_mem; simp at hlive_mem
    | some m' =>
      rw [hlv, optMS_some, Multiset.mem_singleton] at hlive_mem
      rw [hlive_mem]
      exact (h_live (MemoryMsg.locOf mp.1) m' hlv).2.1.2.1
  · rw [pushesAt] at hpush_mem
    obtain ⟨r', hr'_mem, hm'⟩ := (mem_listSum_map _ rows mp.1).mp hpush_mem
    exact (h_ok r' hr'_mem).pushClkBound mp.1
      (List.mem_of_mem_filter (Multiset.mem_coe.mp hm'))

/-! ## The epoch readers and shift lemmas, over the trajectory

Copies of the `…T` family with `chainState s0` replaced by the trajectory parameter. Nothing in them
inspects how a step was taken — they are pure window arithmetic over the timeline — which is why the
generalization is a rename. -/

omit [Fact (2 ^ 17 < p)] in
/-- `microValueG` at a register in the pre-write region of window `n`. -/
lemma microValueG_reg_pre {traj : Trajectory} {s0 : SailState} {tl : Timeline}
    {i : BitVec 5} {n τ : ℕ}
    (hlo : tl.start n ≤ τ) (hhi : τ < tl.start n + 4) :
    microValueG traj s0 tl (MemLoc.reg i) τ
      = (traj n).bind (locContent · (MemLoc.reg i)) := by
  have h0 : tl.start 0 ≤ tl.start n := tl.start_le_of_le (Nat.zero_le n)
  have hgap := tl.gap n
  unfold microValueG
  rw [if_neg (by omega), tl.stepOf_eq hlo (by omega)]
  have hpre : ¬ regEffectOffset ≤ τ - tl.start n := by
    simp only [regEffectOffset]; omega
  simp [hpre]

omit [Fact (2 ^ 17 < p)] in
/-- `microValueG` at a register in the post-write region of window `n` — extending through the
pre-write region of window `n + 1`. -/
lemma microValueG_reg_post {traj : Trajectory} {s0 : SailState} {tl : Timeline}
    {i : BitVec 5} {n τ : ℕ}
    (hlo : tl.start n + 4 ≤ τ) (hhi : τ < tl.start (n + 1) + 4) :
    microValueG traj s0 tl (MemLoc.reg i) τ
      = (traj (n + 1)).bind (locContent · (MemLoc.reg i)) := by
  have h0 : tl.start 0 ≤ tl.start n := tl.start_le_of_le (Nat.zero_le n)
  have hgap := tl.gap n
  have hgap' := tl.gap (n + 1)
  unfold microValueG
  by_cases hwin : τ < tl.start (n + 1)
  · rw [if_neg (by omega), tl.stepOf_eq (by omega) hwin]
    have hpost : regEffectOffset ≤ τ - tl.start n := by
      simp only [regEffectOffset]; omega
    simp [hpost]
  · rw [if_neg (by omega), tl.stepOf_eq (n := n + 1) (by omega) (by omega)]
    have hpre : ¬ regEffectOffset ≤ τ - tl.start (n + 1) := by
      simp only [regEffectOffset]; omega
    simp [hpre]

omit [Fact (2 ^ 17 < p)] in
/-- `microValueG` at a RAM cell at the pre-effect point of window `n` (exactly its start). -/
lemma microValueG_ram_pre {traj : Trajectory} {s0 : SailState} {tl : Timeline}
    {cell : RamCell} {n τ : ℕ}
    (hlo : tl.start n ≤ τ) (hhi : τ < tl.start n + 1) :
    microValueG traj s0 tl (MemLoc.ram cell) τ
      = (traj n).bind (locContent · (MemLoc.ram cell)) := by
  have h0 : tl.start 0 ≤ tl.start n := tl.start_le_of_le (Nat.zero_le n)
  have hgap := tl.gap n
  unfold microValueG
  rw [if_neg (by omega), tl.stepOf_eq hlo (by omega)]
  have hpre : ¬ ramEffectOffset ≤ τ - tl.start n := by
    simp only [ramEffectOffset]; omega
  simp [hpre]

omit [Fact (2 ^ 17 < p)] in
/-- `microValueG` at a RAM cell in the post-effect region of window `n` — extending through the
pre-effect point of window `n + 1`. -/
lemma microValueG_ram_post {traj : Trajectory} {s0 : SailState} {tl : Timeline}
    {cell : RamCell} {n τ : ℕ}
    (hlo : tl.start n + 1 ≤ τ) (hhi : τ < tl.start (n + 1) + 1) :
    microValueG traj s0 tl (MemLoc.ram cell) τ
      = (traj (n + 1)).bind (locContent · (MemLoc.ram cell)) := by
  have h0 : tl.start 0 ≤ tl.start n := tl.start_le_of_le (Nat.zero_le n)
  have hgap := tl.gap n
  have hgap' := tl.gap (n + 1)
  unfold microValueG
  by_cases hwin : τ < tl.start (n + 1)
  · rw [if_neg (by omega), tl.stepOf_eq (by omega) hwin]
    have hpost : ramEffectOffset ≤ τ - tl.start n := by
      simp only [ramEffectOffset]; omega
    simp [hpost]
  · rw [if_neg (by omega), tl.stepOf_eq (n := n + 1) (by omega) (by omega)]
    have hpre : ¬ ramEffectOffset ≤ τ - tl.start (n + 1) := by
      simp only [ramEffectOffset]; omega
    simp [hpre]

omit [Fact (2 ^ 17 < p)] in
/-- **Intra-epoch shift, register form** of `localValueAt_shift`. -/
lemma localValueAtG_shift_reg {traj : Trajectory} {initial : SailState} {tl : Timeline}
    {i : BitVec 5} {v : Word (ZMod p)} {n τ τ' : ℕ}
    (hwin : (tl.start n ≤ τ ∧ τ < tl.start n + 4 ∧ tl.start n ≤ τ' ∧ τ' < tl.start n + 4) ∨
            (tl.start n + 4 ≤ τ ∧ τ < tl.start (n + 1) + 4 ∧
             tl.start n + 4 ≤ τ' ∧ τ' < tl.start (n + 1) + 4))
    (h : LocalValueAtG traj initial tl (MemLoc.reg i) τ v) :
    LocalValueAtG traj initial tl (MemLoc.reg i) τ' v := by
  unfold LocalValueAtG at h ⊢
  rcases hwin with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · rwa [microValueG_reg_pre h3 h4, ← microValueG_reg_pre h1 h2]
  · rwa [microValueG_reg_post h3 h4, ← microValueG_reg_post h1 h2]

omit [Fact (2 ^ 17 < p)] in
/-- **Intra-epoch shift, RAM form** of `localValueAt_shift_ram`. -/
lemma localValueAtG_shift_ram {traj : Trajectory} {initial : SailState} {tl : Timeline}
    {cell : RamCell} {v : Word (ZMod p)} {n τ τ' : ℕ}
    (hwin : (tl.start n ≤ τ ∧ τ < tl.start n + 1 ∧ tl.start n ≤ τ' ∧ τ' < tl.start n + 1) ∨
            (tl.start n + 1 ≤ τ ∧ τ < tl.start (n + 1) + 1 ∧
             tl.start n + 1 ≤ τ' ∧ τ' < tl.start (n + 1) + 1))
    (h : LocalValueAtG traj initial tl (MemLoc.ram cell) τ v) :
    LocalValueAtG traj initial tl (MemLoc.ram cell) τ' v := by
  unfold LocalValueAtG at h ⊢
  rcases hwin with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · rwa [microValueG_ram_pre h3 h4, ← microValueG_ram_pre h1 h2]
  · rwa [microValueG_ram_post h3 h4, ← microValueG_ram_post h1 h2]

omit [Fact (2 ^ 17 < p)] in
/-- **Read-window shift, location-generic form** of `localValueAt_shift_window`. -/
lemma localValueAtG_shift_window {traj : Trajectory} {initial : SailState} {tl : Timeline} (loc : MemLoc)
    {v : Word (ZMod p)} {n τ τ' : ℕ}
    (hlo : tl.start n ≤ τ) (hhi : τ ≤ tl.start n + readWindow loc)
    (hlo' : tl.start n ≤ τ') (hhi' : τ' ≤ tl.start n + readWindow loc)
    (h : LocalValueAtG traj initial tl loc τ v) :
    LocalValueAtG traj initial tl loc τ' v := by
  cases loc with
  | reg i =>
    rw [readWindow_reg] at hhi hhi'
    exact localValueAtG_shift_reg (Or.inl ⟨hlo, by omega, hlo', by omega⟩) h
  | ram a =>
    rw [readWindow_ram] at hhi hhi'
    exact localValueAtG_shift_ram (Or.inl ⟨hlo, by omega, hlo', by omega⟩) h

omit [Fact (2 ^ 17 < p)] in
/-- **Currency at a window start**, location-generic. At `tl.start n` every location is still
pre-effect — offset `0` is below both `regEffectOffset` and `ramEffectOffset` — so a
`LocalValueAtG` fact there *is* the trajectory state's content at that location.

This is the `G` twin of `localValueAt_stepStart_iff`, and it is the whole reason an ordinary row's
step fact can be stated over an arbitrary trajectory: `RowWiring.advance_at` consumes its
`SailChain` argument *only* through the Sail version of this iff, never to reach the chip's
`advance`, which needs the state alone. -/
lemma localValueAtG_stepStart_iff {traj : Trajectory} {initial state : SailState} {tl : Timeline}
    {loc : MemLoc} {v : Word (ZMod p)} {n : ℕ} (htraj : traj n = some state) :
    LocalValueAtG traj initial tl loc (tl.start n) v ↔
      locContent state loc = some (Word.toBitVec64 v) := by
  unfold LocalValueAtG
  cases loc with
  | reg i => rw [microValueG_reg_pre (n := n) le_rfl (by omega), htraj, Option.bind_some]
  | ram a => rw [microValueG_ram_pre (n := n) le_rfl (by omega), htraj, Option.bind_some]

omit [Fact (2 ^ 17 < p)] in
/-- **A register read anywhere in the pre-write half reads the step's own state.** The generalization
of `localValueAtG_stepStart_iff` off the exact window start: any offset below `regEffectOffset` is
still pre-write, which is what lets a syscall row's `op_b`/`op_c` reads at `+3` and `+2` speak about
the state its `op_a` read at `+0` does. -/
lemma localValueAtG_regRead_of_traj {traj : Trajectory} {initial state : SailState}
    {tl : Timeline} {i : BitVec 5} {v : Word (ZMod p)} {n k : ℕ}
    (htraj : traj n = some state) (hk : k < 4)
    (h : LocalValueAtG traj initial tl (MemLoc.reg i) (tl.start n + k) v) :
    state.get_reg? i = some (Word.toBitVec64 v) := by
  unfold LocalValueAtG at h
  rw [microValueG_reg_pre (n := n) (by omega) (by omega), htraj, Option.bind_some] at h
  exact h

/-! ## The value-aligned carrier exchange, over any trajectory

`RowWiring.readTime` pins every pull to the row's window start, so it holds at the **ordinary**
carrier and not at the aligned one — which is why an instruction row's step and frame facts are
proved at the ordinary carrier and then transported.  The Sail transports
(`localStepFact_valueAligned_of_ordinary` and its frame twin) already exist; these are their
trajectory-indexed forms, and they are what let the mixed walk consume an instruction row at the
same carrier a syscall row uses. -/

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- `LocalStateTruthG` is a function of the message's ℕ time and 64-bit pc image. -/
theorem localStateTruthG_congr {program : GuestProgram} {traj : Trajectory} {tl : Timeline}
    {m m' : StateMsg (ZMod p)}
    (ht : StateMsg.timeNat m' = StateMsg.timeNat m)
    (hpc : StateMsg.pcBits m' = StateMsg.pcBits m)
    (h : LocalStateTruthG program traj tl m) :
    LocalStateTruthG program traj tl m' := by
  obtain ⟨n, state, htraj, htime, hpcEq, hrom, hcfg⟩ := h
  refine ⟨n, state, htraj, by rw [ht]; exact htime, ?_, hrom, hcfg⟩
  rw [show pcBits m'.pc0 m'.pc1 m'.pc2 = pcBits m.pc0 m.pc1 m.pc2 from hpc]
  exact hpcEq

omit [Fact (2 ^ 17 < p)] in
/-- Ordinary pull currency from the carrier's, trajectory-indexed.  Each matched pull is shifted
back to the ordinary window start — which is `tl.start n` for the step index the pulled state truth
names — and `isU64` travels along the value equality. -/
theorem ordinaryPullCurrencyG_of_valueAligned
    {program : GuestProgram} {traj : Trajectory} {initial : SailState} {tl : Timeline}
    {r_new r_ord : RowFacts p} (h : ValueAligned r_new r_ord)
    (hstateTruth : LocalStateTruthG program traj tl r_new.statePull)
    (hcurr_new : ∀ mp ∈ r_new.memPulls, MemoryMsg.isU64 mp.1 ∧
      MemoryMsg.ClkBound mp.1 ∧
      LocalValueAtG traj initial tl (MemoryMsg.locOf mp.1) mp.2 mp.1.value) :
    ∀ mp ∈ r_ord.memPulls, MemoryMsg.isU64 mp.1 ∧
      MemoryMsg.ClkBound mp.1 ∧
      LocalValueAtG traj initial tl (MemoryMsg.locOf mp.1) mp.2 mp.1.value := by
  obtain ⟨n, state, htraj, htime, -, -, -⟩ := hstateTruth
  intro mp hmp
  obtain ⟨mp', hmp'_mem, hloc, hval, hlo, hhi⟩ := h.match_ mp hmp
  obtain ⟨hu64, -, hval_new⟩ := hcurr_new mp' hmp'_mem
  rw [hloc, hval] at hval_new
  rw [htime] at hlo hhi
  refine ⟨?_, h.pullClk mp hmp, ?_⟩
  · unfold SP1Clean.Channels.MemoryMsg.isU64 at hu64 ⊢
    rwa [hval] at hu64
  · rw [h.ordTime mp hmp, ← h.pullTime, htime]
    exact localValueAtG_shift_window (MemoryMsg.locOf mp.1) hlo hhi le_rfl
      (Nat.le_add_right _ _) hval_new

omit [Fact (2 ^ 17 < p)] in
/-- `LocalStepFactG` transports from the ordinary carrier to a value-aligned one. -/
theorem localStepFactG_valueAligned_of_ordinary
    {program : GuestProgram} {traj : Trajectory} {initial : SailState} {tl : Timeline}
    {r_new r_ord : RowFacts p} (h : ValueAligned r_new r_ord)
    (step_ord : LocalStepFactG program traj initial tl r_ord) :
    LocalStepFactG program traj initial tl r_new := by
  intro hpull hcurr_new
  have hpull_ord : LocalStateTruthG program traj tl r_ord.statePull :=
    localStateTruthG_congr h.pullTime.symm h.pullPc.symm hpull
  have hcurr_ord := ordinaryPullCurrencyG_of_valueAligned h hpull hcurr_new
  obtain ⟨hpush_ord, hmem_ord⟩ := step_ord hpull_ord hcurr_ord
  refine ⟨localStateTruthG_congr h.pushTime h.pushPc hpush_ord, ?_⟩
  intro m hm
  exact hmem_ord m (h.pushes.mem_iff.mp hm)

omit [Fact (2 ^ 17 < p)] in
/-- `FrameFactG` transports the same way. -/
theorem frameFactG_valueAligned_of_ordinary
    {program : GuestProgram} {traj : Trajectory} {initial : SailState} {tl : Timeline}
    {r_new r_ord : RowFacts p} (h : ValueAligned r_new r_ord)
    (frame_ord : FrameFactG program traj initial tl r_ord) :
    FrameFactG program traj initial tl r_new := by
  intro hpull hcurr_new loc v hpush hstart
  have hpull_ord : LocalStateTruthG program traj tl r_ord.statePull :=
    localStateTruthG_congr h.pullTime.symm h.pullPc.symm hpull
  have hcurr_ord := ordinaryPullCurrencyG_of_valueAligned h hpull hcurr_new
  have hpush_ord : ∀ m ∈ r_ord.memPushes, MemoryMsg.locOf m = loc → m.value = v :=
    fun m hm => hpush m (h.pushes.mem_iff.mpr hm)
  have hstart_ord : LocalValueAtG traj initial tl loc
      (StateMsg.timeNat r_ord.statePull) v := by
    rw [← h.pullTime]; exact hstart
  have := frame_ord hpull_ord hcurr_ord loc v hpush_ord hstart_ord
  rw [h.pushTime]
  exact this

omit [Fact (2 ^ 17 < p)] in
/-- `LocalStepFactG` transports across a State re-spelling that preserves time and pc image.

The `ValueAligned` route above cannot serve here: `ValueAligned` demands `ordTime`, that every pull
sit at the row's window start, and a syscall row's three reads deliberately sit at `+0`, `+3` and
`+2`.  A bare re-spelling asks for none of that, and it is all a canonicalized State edge needs. -/
theorem localStepFactG_stateRespell {program : GuestProgram} {traj : Trajectory}
    {initial : SailState} {tl : Timeline} {r : RowFacts p} {pull push : StateMsg (ZMod p)}
    (hpullT : StateMsg.timeNat pull = StateMsg.timeNat r.statePull)
    (hpullP : StateMsg.pcBits pull = StateMsg.pcBits r.statePull)
    (hpushT : StateMsg.timeNat push = StateMsg.timeNat r.statePush)
    (hpushP : StateMsg.pcBits push = StateMsg.pcBits r.statePush)
    (h : LocalStepFactG program traj initial tl r) :
    LocalStepFactG program traj initial tl (stateRespell r pull push) := by
  intro hpull hcurr
  rw [stateRespell_statePull] at hpull
  rw [stateRespell_memPulls] at hcurr
  obtain ⟨hpushTruth, hmem⟩ := h (localStateTruthG_congr hpullT.symm hpullP.symm hpull) hcurr
  refine ⟨?_, ?_⟩
  · rw [stateRespell_statePush]
    exact localStateTruthG_congr hpushT hpushP hpushTruth
  · rw [stateRespell_memPushes]
    exact hmem

omit [Fact (2 ^ 17 < p)] in
/-- `FrameFactG` transports across a State re-spelling the same way — and needs one hypothesis
fewer, because a frame claim reads the pushed message's *time* and never its pc. -/
theorem frameFactG_stateRespell {program : GuestProgram} {traj : Trajectory}
    {initial : SailState} {tl : Timeline} {r : RowFacts p} {pull push : StateMsg (ZMod p)}
    (hpullT : StateMsg.timeNat pull = StateMsg.timeNat r.statePull)
    (hpullP : StateMsg.pcBits pull = StateMsg.pcBits r.statePull)
    (hpushT : StateMsg.timeNat push = StateMsg.timeNat r.statePush)
    (h : FrameFactG program traj initial tl r) :
    FrameFactG program traj initial tl (stateRespell r pull push) := by
  intro hpull hcurr loc v hpush hstart
  rw [stateRespell_statePull] at hpull
  rw [stateRespell_memPulls] at hcurr
  rw [stateRespell_memPushes] at hpush
  rw [stateRespell_statePull, hpullT] at hstart
  have result := h (localStateTruthG_congr hpullT.symm hpullP.symm hpull) hcurr loc v hpush hstart
  rw [stateRespell_statePush, hpushT]
  exact result

/-! ## The walk

The proof is `walkT`'s, with `chainState initial` replaced by the trajectory parameter throughout.
Nothing in the body inspects *how* a step was taken: the layer-A window arithmetic is
`RowOKCore`-only, layer B is the chain machinery over row-relative touch offsets, and layer C is
whatever `LocalStepFactG` supplies. The Sail-specific reasoning all lives in the *callers* that
discharge `LocalStepFactG`, which is exactly where a syscall row differs. -/

omit [Fact (2 ^ 17 < p)] in
/-- **The grounding walk, over any trajectory.** Statement identical to `walkT`'s with the
`…T` predicates replaced by their `…G` forms and the trajectory made a parameter. -/
theorem walkG (program : GuestProgram) (traj : Trajectory) (initial : SailState) (tl : Timeline)
    (initialClock : ℕ) (fin : StateMsg (ZMod p))
    (finM : MemLoc → Option (MemoryMsg (ZMod p))) :
    ∀ (N : ℕ) (rows : List (RowFacts p)) (head : StateMsg (ZMod p))
      (live : MemLoc → Option (MemoryMsg (ZMod p))),
      rows.length = N →
      (∀ r ∈ rows, LocalStepFactG program traj initial tl r) →
      (∀ r ∈ rows, FrameFactG program traj initial tl r) →
      (∀ r ∈ rows, RowOKCore initialClock r) →
      (∀ r ∈ rows, ∀ n : ℕ, StateMsg.timeNat r.statePull = tl.start n →
        StateMsg.timeNat r.statePush = tl.start (n + 1)) →
      LocalStateTruthG program traj tl head →
      LiveOKG traj initial tl (StateMsg.timeNat head) live →
      (head ::ₘ (↑(rows.map (·.statePush)) : Multiset (StateMsg (ZMod p)))
        = fin ::ₘ ↑(rows.map (·.statePull))) →
      (∀ loc : MemLoc, optMS (live loc) + pushesAt rows loc
        = optMS (finM loc) + pullsAt rows loc) →
      (∀ r ∈ rows, GroundedG program traj initial tl r) ∧
        LocalStateTruthG program traj tl fin ∧
        ∀ (loc : MemLoc) (m : MemoryMsg (ZMod p)), finM loc = some m →
          MemoryMsg.locOf m = loc ∧
          LocalMemTruthG traj initial tl m ∧
          LocalValueAtG traj initial tl loc (StateMsg.timeNat fin) m.value ∧
          MemoryMsg.timeNat m ≤ StateMsg.timeNat fin := by
  intro N
  induction N with
  | zero =>
    intro rows head live hlen _ _ _ _ h_head h_live h_sbal h_mbal
    obtain rfl : rows = [] := List.length_eq_zero_iff.mp hlen
    have h_fin : head = fin := by simpa using h_sbal
    subst h_fin
    refine ⟨by simp, h_head, fun loc m hm => ?_⟩
    have h_fm : optMS (live loc) = optMS (finM loc) := by
      simpa [pullsAt, pushesAt] using h_mbal loc
    rw [hm, optMS_some] at h_fm
    cases hlv : live loc with
    | none => rw [hlv, optMS_none] at h_fm; simp at h_fm
    | some m' =>
      rw [hlv, optMS_some, Multiset.singleton_inj] at h_fm
      subst h_fm
      exact h_live loc m' hlv
  | succ N ih =>
    intro rows head live hlen h_step h_frame h_ok h_tl h_head h_live h_sbal h_mbal
    have hne : rows ≠ [] := fun h => by simp [h] at hlen
    -- (A) the row with minimal state-pull time pulls `head`: any other candidate match in the
    -- balance would be a push, at least eight ticks after its own pull ≥ the minimum.
    obtain ⟨r, hr_mem, hr_min⟩ := exists_min_by (fun r => StateMsg.timeNat r.statePull) rows hne
    have h_rok := h_ok r hr_mem
    have hr_pull : r.statePull = head := by
      have hmem : r.statePull
          ∈ (head ::ₘ (↑(rows.map (·.statePush)) : Multiset (StateMsg (ZMod p)))) := by
        rw [h_sbal]
        exact Multiset.mem_cons_of_mem (Multiset.mem_coe.mpr (List.mem_map_of_mem hr_mem))
      rcases Multiset.mem_cons.mp hmem with h | h
      · exact h
      · exfalso
        obtain ⟨r'', hr''_mem, hr''_eq⟩ := List.mem_map.mp (Multiset.mem_coe.mp h)
        have h8 := (h_ok r'' hr''_mem).timeGap
        have hmin := hr_min r'' hr''_mem
        rw [hr''_eq] at h8
        omega
    have h_rtruth : LocalStateTruthG program traj tl r.statePull := by
      rw [hr_pull]; exact h_head
    have ht_head : StateMsg.timeNat r.statePull = StateMsg.timeNat head := by rw [hr_pull]
    -- the popped row's position on the timeline, and its committed window endpoints
    have hex := h_rtruth
    obtain ⟨nh, -, -, hpull_start, -, -, -⟩ := hex
    have hpush_start : StateMsg.timeNat r.statePush = tl.start (nh + 1) :=
      h_tl r hr_mem nh hpull_start
    have hgap8 := tl.gap nh
    -- pop `r` out of the batch
    obtain ⟨l1, l2, rfl⟩ : ∃ l1 l2, rows = l1 ++ r :: l2 := List.append_of_mem hr_mem
    have hlen' : (l1 ++ l2).length = N := by
      simp only [List.length_append, List.length_cons] at hlen ⊢; omega
    have hsub : ∀ r' ∈ l1 ++ l2, r' ∈ l1 ++ r :: l2 := fun r' hr' => mem_middle r hr'
    -- the SP-6 state gap (invariants 1 + 2): every remaining row's window starts ≥ t + 8
    have h_gap : ∀ r' ∈ l1 ++ l2,
        StateMsg.timeNat r.statePull + 8 ≤ StateMsg.timeNat r'.statePull := by
      refine stateBalance_remaining_ge_eight (fun r' h => (h_ok r' h).timeGap) hr_min
        (fun r' h => ?_) ht_head.symm hr_pull h_sbal
      rw [(h_ok r' h).align8, h_rok.align8]
    -- hence every remaining row's push is ≥ t + 8 — the gap the link derivation consumes
    have h_opush : ∀ loc : MemLoc, ∀ m ∈ pushesAt (l1 ++ l2) loc,
        StateMsg.timeNat r.statePull + 8 ≤ MemoryMsg.timeNat m := by
      intro loc m hm
      simp only [pushesAt, mem_listSum_map] at hm
      obtain ⟨r', hr'_mem, hm'⟩ := hm
      have hq : m ∈ r'.memPushes := List.mem_of_mem_filter (Multiset.mem_coe.mp hm')
      have h1 := pushTimeGe_core (h_ok r' (hsub r' hr'_mem)) hq
      have h2 := h_gap r' hr'_mem
      omega
    -- the pulled-record `ClkBound`s for `r`'s per-key touches, from the memory balance alone (1f):
    -- every pull record is the frontier or some row's own push, both `ClkBound`.  This is the
    -- currency-free input `chainOK` needs to rebuild each chain's `slot` (`prev_clk < access_clk`).
    have h_pullClk : ∀ (loc : MemLoc), ∀ pq ∈ rowTouchesAt r loc,
        SP1Clean.Channels.MemoryMsg.ClkBound (pq : Touch p).1.1 := fun loc pq hpq =>
      pull_clkBound_of_balanceG h_ok h_live h_mbal hr_mem
        (List.of_mem_zip (mem_rowTouchesAt.mp hpq).1).1
    have hcok : ∀ loc : MemLoc, ChainOK loc (StateMsg.timeNat r.statePull) (rowTouchesAt r loc) :=
      fun loc => h_rok.chainOK loc (h_pullClk loc)
    -- (B) the per-key chain forcing at every key `r` touches: the frontier holds the chain's head
    -- pull, the intra-row links are derived from balance, the whole chain cancels, and the chain's
    -- last push is the new frontier with the re-established time bound.
    have h_key : ∀ (loc : MemLoc) (hne' : rowTouchesAt r loc ≠ []),
        live loc = some ((rowTouchesAt r loc).head hne').1.1 ∧
          List.IsChain (fun a b : Touch p => b.1.1 = a.2) (rowTouchesAt r loc) ∧
          (((rowTouchesAt r loc).getLast hne').2 ::ₘ pushesAt (l1 ++ l2) loc
            = optMS (finM loc) + pullsAt (l1 ++ l2) loc) ∧
          MemoryMsg.timeNat ((rowTouchesAt r loc).getLast hne').2
            ≤ StateMsg.timeNat r.statePull + 4 := by
      intro loc hne'
      have hbal := h_mbal loc
      rw [pushesAt_pop, pullsAt_pop, rowPushesAt_eq h_rok.touches loc,
        rowPullsAt_eq h_rok.touches loc,
        add_left_comm (optMS (finM loc))
          (↑(chainPulls (rowTouchesAt r loc)) : Multiset (MemoryMsg (ZMod p)))] at hbal
      exact chainForcing_step_of_gap hne' (hcok loc) (h_opush loc) hbal
    -- each pull's source: the per-key chain forces it to carry the frontier record's value, and to
    -- be either that record itself (a chain-head pull) or one of the row's own pushes (a same-key
    -- re-read), read inside the location's pre-effect window
    have h_src : ∀ mp ∈ r.memPulls,
        (∃ m0, live (MemoryMsg.locOf mp.1) = some m0 ∧ mp.1.value = m0.value ∧
          (mp.1 = m0 ∨ mp.1 ∈ r.memPushes)) ∧
        StateMsg.timeNat r.statePull ≤ mp.2 ∧
        mp.2 ≤ StateMsg.timeNat r.statePull + readWindow (MemoryMsg.locOf mp.1) := by
      intro mp hmp
      obtain ⟨q, hq_zip⟩ := mem_zip_of_mem_left h_rok.touches mp hmp
      have hto : TouchOK (StateMsg.timeNat r.statePull) mp q :=
        List.forall₂_zip h_rok.touches hq_zip
      have hmem_own : (mp, q) ∈ rowTouchesAt r (MemoryMsg.locOf mp.1) :=
        mem_rowTouchesAt.mpr ⟨hq_zip, hto.loc_eq⟩
      have hne' : rowTouchesAt r (MemoryMsg.locOf mp.1) ≠ [] := List.ne_nil_of_mem hmem_own
      obtain ⟨hlive_eq, hlink, -, -⟩ := h_key _ hne'
      refine ⟨⟨_, hlive_eq, chain_pull_values _ (hcok _) hlink hne' (mp, q) hmem_own, ?_⟩,
        (hcok _).read_lo (mp, q) hmem_own, (hcok _).read_hi (mp, q) hmem_own⟩
      rcases chain_pull_head_or_push _ hne' hlink (mp, q) hmem_own with hhd | hpush
      · exact Or.inl hhd
      · refine Or.inr ?_
        obtain ⟨pq', hpq', hpq'_eq⟩ := mem_chainPushes.mp hpush
        rw [← hpq'_eq]
        exact (List.of_mem_zip (mem_rowTouchesAt.mp hpq').1).2
    -- read-time currency for `r`'s pulls: every chain pull carries the frontier value (nothing
    -- can follow a same-key write), current throughout the location's pre-effect read window
    have h_curr : ∀ mp ∈ r.memPulls, SP1Clean.Channels.MemoryMsg.isU64 mp.1 ∧
        SP1Clean.Channels.MemoryMsg.ClkBound mp.1 ∧
        LocalValueAtG traj initial tl (MemoryMsg.locOf mp.1) mp.2 mp.1.value := by
      intro mp hmp
      obtain ⟨⟨m0, hlive_eq, hveq, hsrc⟩, hlo, hhi⟩ := h_src mp hmp
      obtain ⟨-, hmt₀, hval₀, -⟩ := h_live _ _ hlive_eq
      refine ⟨by simpa [SP1Clean.Channels.MemoryMsg.isU64, hveq] using hmt₀.1, ?_, ?_⟩
      · -- `ClkBound`: a head pull is the frontier record (bound from `LiveOKG`'s
        -- `LocalMemTruthG`); a same-key re-read pull is one of the row's own pushes (bound from
        -- `RowOKCore.pushClkBound` — the currency-circularity break).
        rcases hsrc with rfl | hpush
        · exact hmt₀.2.1
        · exact h_rok.pushClkBound mp.1 hpush
      · rw [← hveq, ← ht_head] at hval₀
        refine localValueAtG_shift_window _ (n := nh) (le_of_eq hpull_start.symm) ?_ ?_ ?_ hval₀
        · rw [← hpull_start]; exact Nat.le_add_right _ _
        · rw [← hpull_start]; exact hlo
        · rw [← hpull_start]; exact hhi
    -- (C) fire the row's StepFact
    have h_after := h_step r hr_mem h_rtruth h_curr
    -- the row is GroundedG: head pulls are true frontier records, tail pulls are the row's own
    -- (just-fired) read-back pushes
    have h_ground_r : GroundedG program traj initial tl r := by
      refine ⟨h_rtruth, fun mp hmp => ⟨?_, (h_curr mp hmp).2.2⟩⟩
      obtain ⟨⟨m0, hlive_eq, -, hsrc⟩, -, -⟩ := h_src mp hmp
      rcases hsrc with rfl | hpush
      · exact (h_live _ _ hlive_eq).2.1
      · exact h_after.2 mp.1 hpush
    -- the new frontier: the chain's last push where the row touched, unchanged elsewhere
    have h_liveOK' : LiveOKG traj initial tl (StateMsg.timeNat r.statePush)
        (fun loc => ((rowTouchesAt r loc).getLast?.map (·.2)).or (live loc)) := by
      intro loc m hm
      dsimp only at hm
      by_cases hemp : rowTouchesAt r loc = []
      · -- untouched key: the frontier record persists via the row's frame
        rw [hemp] at hm
        simp only [List.getLast?_nil, Option.map_none, Option.none_or] at hm
        obtain ⟨hloc_m, hmt_m, hval_m, htime_m⟩ := h_live loc m hm
        refine ⟨hloc_m, hmt_m, ?_, by omega⟩
        refine h_frame r hr_mem h_rtruth h_curr loc m.value ?_ ?_
        · intro m' hm' hml
          exfalso
          have hmem' : m' ∈ rowPushesAt r loc := List.mem_filter.mpr ⟨hm', by simpa using hml⟩
          rw [rowPushesAt_eq h_rok.touches loc, hemp] at hmem'
          simp [chainPushes] at hmem'
        · rw [ht_head]; exact hval_m
      · -- touched key: the chain's last push is the new frontier record
        obtain ⟨hlive_eq, hlink, -, hlast⟩ := h_key loc hemp
        rw [List.getLast?_eq_some_getLast hemp] at hm
        simp only [Option.map_some, Option.some_or, Option.some.injEq] at hm
        subst hm
        have hlast_mem : (rowTouchesAt r loc).getLast hemp ∈ rowTouchesAt r loc :=
          List.getLast_mem hemp
        have hloc_q : MemoryMsg.locOf ((rowTouchesAt r loc).getLast hemp).2 = loc :=
          (hcok loc).push_loc _ hlast_mem
        have hq_mem : ((rowTouchesAt r loc).getLast hemp).2 ∈ r.memPushes :=
          (List.of_mem_zip (mem_rowTouchesAt.mp hlast_mem).1).2
        have hmt_q := h_after.2 _ hq_mem
        refine ⟨hloc_q, hmt_q, ?_, by omega⟩
        rcases (hcok loc).push_kind _ hlast_mem with ⟨hv, -⟩ | hw
        · -- read-back last slot: the whole chain is read-backs of the (still-current) frontier
          -- value — frame across
          obtain ⟨-, -, hval₀, -⟩ := h_live loc _ hlive_eq
          have hpushv := chain_push_values _ (hcok loc) hlink hemp hv
          refine h_frame r hr_mem h_rtruth h_curr loc
            ((rowTouchesAt r loc).getLast hemp).2.value ?_ ?_
          · intro m' hm' hml
            have hmem' : m' ∈ rowPushesAt r loc := List.mem_filter.mpr ⟨hm', by simpa using hml⟩
            rw [rowPushesAt_eq h_rok.touches loc] at hmem'
            obtain ⟨pq', hpq', hpq'_eq⟩ := mem_chainPushes.mp hmem'
            rw [← hpq'_eq, hpushv pq' hpq', hpushv _ hlast_mem]
          · rw [hpushv _ hlast_mem, ht_head]; exact hval₀
        · -- write last slot: the push's own MemTruth at `t + writeOffset`, shifted to the
          -- timeline's next step start
          have hmt := hmt_q.2.2; rw [hloc_q] at hmt
          cases loc with
          | reg i =>
            rw [writeOffset_reg] at hw
            exact localValueAtG_shift_reg (n := nh)
              (Or.inr ⟨by omega, by omega, by omega, by omega⟩) hmt
          | ram a =>
            rw [writeOffset_ram] at hw
            exact localValueAtG_shift_ram (n := nh)
              (Or.inr ⟨by omega, by omega, by omega, by omega⟩) hmt
    -- state balance advances: cancel the consumed head
    have h_sbal' : r.statePush ::ₘ (↑((l1 ++ l2).map (·.statePush)) : Multiset (StateMsg (ZMod p)))
        = fin ::ₘ ↑((l1 ++ l2).map (·.statePull)) := by
      rw [coe_map_pop, coe_map_pop, hr_pull, Multiset.cons_swap fin head] at h_sbal
      exact (Multiset.cons_inj_right _).mp h_sbal
    -- per-key memory balance advances: cancel the consumed frontier chain
    have h_mbal' : ∀ loc : MemLoc,
        optMS (((rowTouchesAt r loc).getLast?.map (·.2)).or (live loc)) + pushesAt (l1 ++ l2) loc
          = optMS (finM loc) + pullsAt (l1 ++ l2) loc := by
      intro loc
      by_cases hemp : rowTouchesAt r loc = []
      · have hbal := h_mbal loc
        rw [pushesAt_pop, pullsAt_pop, rowPushesAt_eq h_rok.touches loc,
          rowPullsAt_eq h_rok.touches loc, hemp] at hbal
        simp only [chainPushes, chainPulls, List.map_nil, Multiset.coe_nil, zero_add] at hbal
        rw [hemp]; simpa using hbal
      · obtain ⟨-, -, hcancel, -⟩ := h_key loc hemp
        rw [List.getLast?_eq_some_getLast hemp]
        simp only [Option.map_some, Option.some_or, optMS_some, Multiset.singleton_add]
        exact hcancel
    -- recurse on the rest
    obtain ⟨hg_rest, hfin, hfinM⟩ := ih (l1 ++ l2) r.statePush
      (fun loc => ((rowTouchesAt r loc).getLast?.map (·.2)).or (live loc)) hlen'
      (fun r' h => h_step r' (hsub r' h)) (fun r' h => h_frame r' (hsub r' h))
      (fun r' h => h_ok r' (hsub r' h)) (fun r' h => h_tl r' (hsub r' h))
      h_after.1 h_liveOK' h_sbal' h_mbal'
    refine ⟨?_, hfin, hfinM⟩
    intro r' hr'
    rcases List.mem_append.mp hr' with h | h
    · exact hg_rest r' (List.mem_append_left _ h)
    · rcases List.mem_cons.mp h with rfl | h
      · exact h_ground_r
      · exact hg_rest r' (List.mem_append_right _ h)

omit [Fact (2 ^ 17 < p)] in
/-- **The Sail instantiation recovers `walkT` exactly.** This is the refactor's acceptance test: it
must hold with no change to `walkT`'s statement. -/
theorem walkT_of_walkG (program : GuestProgram) (initial : SailState) (tl : Timeline)
    (initialClock : ℕ) (fin : StateMsg (ZMod p))
    (finM : MemLoc → Option (MemoryMsg (ZMod p))) :
    ∀ (N : ℕ) (rows : List (RowFacts p)) (head : StateMsg (ZMod p))
      (live : MemLoc → Option (MemoryMsg (ZMod p))),
      rows.length = N →
      (∀ r ∈ rows, LocalStepFactT program initial tl r) →
      (∀ r ∈ rows, FrameFactT program initial tl r) →
      (∀ r ∈ rows, RowOKCore initialClock r) →
      (∀ r ∈ rows, ∀ n : ℕ, StateMsg.timeNat r.statePull = tl.start n →
        StateMsg.timeNat r.statePush = tl.start (n + 1)) →
      LocalStateTruthT program initial tl head →
      LiveOKT initial tl (StateMsg.timeNat head) live →
      (head ::ₘ (↑(rows.map (·.statePush)) : Multiset (StateMsg (ZMod p)))
        = fin ::ₘ ↑(rows.map (·.statePull))) →
      (∀ loc : MemLoc, optMS (live loc) + pushesAt rows loc
        = optMS (finM loc) + pullsAt rows loc) →
      (∀ r ∈ rows, GroundedT program initial tl r) ∧
        LocalStateTruthT program initial tl fin ∧
        ∀ (loc : MemLoc) (m : MemoryMsg (ZMod p)), finM loc = some m →
          MemoryMsg.locOf m = loc ∧
          LocalMemTruthT initial tl m ∧
          LocalValueAtT initial tl loc (StateMsg.timeNat fin) m.value ∧
          MemoryMsg.timeNat m ≤ StateMsg.timeNat fin := by
  intro N rows head live hlen hstep hframe hrow htl hhead hlive hsbal hmbal
  have := walkG program (sailTrajectory initial) initial tl initialClock fin finM N rows head live
    hlen
    (fun r hr => localStepFactG_sail.mpr (hstep r hr))
    (fun r hr => frameFactG_sail.mpr (hframe r hr))
    hrow htl
    (localStateTruthG_sail.mpr hhead)
    (liveOKG_sail.mpr hlive)
    hsbal hmbal
  obtain ⟨hg, hfin, hfinM⟩ := this
  refine ⟨fun r hr => groundedG_sail.mp (hg r hr), localStateTruthG_sail.mp hfin, ?_⟩
  intro loc m hm
  obtain ⟨hkey, htruth, hval, htime⟩ := hfinM loc m hm
  exact ⟨hkey, localMemTruthG_sail.mp htruth, localValueAtG_sail.mp hval, htime⟩

omit [Fact (2 ^ 17 < p)] in
/-- **The event instantiation.** A step may be an ordinary Sail step or a handled syscall, and the
timeline is the transcript's own prefix-summed durations — so a 264-tick row occupies exactly one
timeline step, by construction rather than by hypothesis. -/
theorem walkE (handler : Machine.ExecutableSyscallHandler) (program : GuestProgram)
    (events : List Machine.ExecutionEvent) (initial : SailState) (initialClock : ℕ)
    (fin : StateMsg (ZMod p)) (finM : MemLoc → Option (MemoryMsg (ZMod p))) :
    ∀ (N : ℕ) (rows : List (RowFacts p)) (head : StateMsg (ZMod p))
      (live : MemLoc → Option (MemoryMsg (ZMod p))),
      rows.length = N →
      (∀ r ∈ rows, LocalStepFactG program (eventTrajectory handler program events initial) initial
        (eventTimeline events initialClock) r) →
      (∀ r ∈ rows, FrameFactG program (eventTrajectory handler program events initial) initial
        (eventTimeline events initialClock) r) →
      (∀ r ∈ rows, RowOKCore initialClock r) →
      (∀ r ∈ rows, ∀ n : ℕ,
        StateMsg.timeNat r.statePull = (eventTimeline events initialClock).start n →
        StateMsg.timeNat r.statePush = (eventTimeline events initialClock).start (n + 1)) →
      LocalStateTruthG program (eventTrajectory handler program events initial)
        (eventTimeline events initialClock) head →
      LiveOKG (eventTrajectory handler program events initial) initial
        (eventTimeline events initialClock) (StateMsg.timeNat head) live →
      (head ::ₘ (↑(rows.map (·.statePush)) : Multiset (StateMsg (ZMod p)))
        = fin ::ₘ ↑(rows.map (·.statePull))) →
      (∀ loc : MemLoc, optMS (live loc) + pushesAt rows loc
        = optMS (finM loc) + pullsAt rows loc) →
      (∀ r ∈ rows, GroundedG program (eventTrajectory handler program events initial) initial
          (eventTimeline events initialClock) r) ∧
        LocalStateTruthG program (eventTrajectory handler program events initial)
          (eventTimeline events initialClock) fin ∧
        ∀ (loc : MemLoc) (m : MemoryMsg (ZMod p)), finM loc = some m →
          MemoryMsg.locOf m = loc ∧
          LocalMemTruthG (eventTrajectory handler program events initial) initial
            (eventTimeline events initialClock) m ∧
          LocalValueAtG (eventTrajectory handler program events initial) initial
            (eventTimeline events initialClock) loc (StateMsg.timeNat fin) m.value ∧
          MemoryMsg.timeNat m ≤ StateMsg.timeNat fin :=
  walkG program (eventTrajectory handler program events initial) initial
    (eventTimeline events initialClock) initialClock fin finM

end SP1Clean.Soundness.TimedGrounding

namespace SP1Clean.Soundness

open SP1Clean.Semantics
open SP1Clean.Soundness.Target

variable {p : ℕ}

/-! ## Telescoping a State walk

Pure `Walk.IsWalk` arithmetic over an arbitrary row type — no grounding content, no instruction
class, no fixed divisor. These sat in `GroundingInternal` while the only walk was over decoded
instruction rows; they live here now because the syscall side needs them at `WalkedRow` and sits
below that file. -/

/-- A State-message walk with a row-dependent positive-width schedule has the expected endpoint
clock count.  No instruction class, fixed divisor, or concrete edge map is baked into this
telescoping theorem; the capstone instantiates it at the canonicalized decoded edge. -/
theorem clockCount_of_stateWalk_durations {α : Type*}
    (edge : α → Channels.StateMsg (ZMod p) × Channels.StateMsg (ZMod p))
    (duration : α → ℕ) :
    ∀ {initial final : Channels.StateMsg (ZMod p)}
      {rows : List α},
      Walk.IsWalk edge initial final rows →
      (∀ decoded ∈ rows,
        Semantics.StateMsg.timeNat (edge decoded).2 =
          Semantics.StateMsg.timeNat (edge decoded).1 + duration decoded) →
      Semantics.StateMsg.timeNat initial + (rows.map duration).sum =
        Semantics.StateMsg.timeNat final := by
  intro initial final rows walk steps
  induction rows generalizing initial with
  | nil =>
      change initial = final at walk
      subst final
      simp
  | cons decoded rows ih =>
      obtain ⟨source, tail⟩ := walk
      have sourceTime := congrArg Semantics.StateMsg.timeNat source
      have rowStep := steps decoded List.mem_cons_self
      have tailCount := ih tail (fun other otherMem =>
        steps other (List.mem_cons_of_mem decoded otherMem))
      simp only [List.map_cons, List.sum_cons]
      omega

/-- The telescoping endpoint-multiset balance of a State walk: the head plus each row's push equals the
final plus each row's pull, as multisets.  The `List`-level companion of
`RankedGrounding.endpointBalanced_of_balanced`, derived directly from `IsWalk` so it carries the
`statement.publicValues` endpoints natively — the exact State-balance hypothesis `TimedGrounding.walk`
consumes (after mapping the canonicalized edge onto the walk carrier's `statePush`/`statePull`). -/
theorem endpointBalance_of_stateWalk {α : Type*}
    (edge : α → Channels.StateMsg (ZMod p) × Channels.StateMsg (ZMod p)) :
    ∀ {initial final : Channels.StateMsg (ZMod p)}
      {rows : List α},
      Walk.IsWalk edge initial final rows →
      initial ::ₘ (↑(rows.map (fun d => (edge d).2)) :
          Multiset (Channels.StateMsg (ZMod p)))
        = final ::ₘ ↑(rows.map (fun d => (edge d).1)) := by
  intro initial final rows walk
  induction rows generalizing initial with
  | nil =>
      change initial = final at walk
      subst final
      rfl
  | cons decoded rows ih =>
      obtain ⟨source, tail⟩ := walk
      have ihEq := ih tail
      simp only [List.map_cons, Multiset.cons_coe, Multiset.coe_eq_coe] at ihEq ⊢
      rw [source]
      exact (List.Perm.cons initial ihEq).trans (List.Perm.swap final initial _)

/-- Locate a row in a State walk by the sum of all preceding row-dependent durations. -/
theorem statePullTime_of_stateWalk_durations {α : Type*}
    (edge : α → Channels.StateMsg (ZMod p) × Channels.StateMsg (ZMod p))
    (duration : α → ℕ) :
    ∀ {initial final : Channels.StateMsg (ZMod p)}
      {rows : List α},
      Walk.IsWalk edge initial final rows →
      (∀ decoded ∈ rows,
        Semantics.StateMsg.timeNat (edge decoded).2 =
          Semantics.StateMsg.timeNat (edge decoded).1 + duration decoded) →
      ∀ done decoded suffix, rows = done ++ decoded :: suffix →
        Semantics.StateMsg.timeNat (edge decoded).1 =
          Semantics.StateMsg.timeNat initial + (done.map duration).sum := by
  intro initial final rows walk steps done
  induction done generalizing initial rows with
  | nil =>
      intro decoded suffix rowsEq
      subst rows
      obtain ⟨source, -⟩ := walk
      simpa using congrArg Semantics.StateMsg.timeNat source
  | cons head done ih =>
      intro decoded suffix rowsEq
      subst rows
      obtain ⟨source, tail⟩ := walk
      have headStep := steps head List.mem_cons_self
      have tailSteps : ∀ row ∈ done ++ decoded :: suffix,
          Semantics.StateMsg.timeNat (edge row).2 =
            Semantics.StateMsg.timeNat (edge row).1 + duration row := by
        intro row rowMem
        exact steps row (List.mem_cons_of_mem head rowMem)
      have position := ih tail tailSteps decoded suffix rfl
      have sourceTime := congrArg Semantics.StateMsg.timeNat source
      simp only [List.map_cons, List.sum_cons]
      omega

/-- Every row of a duration-generic State walk begins in the same residue class modulo eight as the
public initial State record, provided each row's own window is a multiple of eight.

This is `RowOK.align8`'s input with the exact `+8` step removed, and it is what lets a 264-tick
syscall row join the walk without breaking alignment: `264 = 8 * 33`, so the residue survives a
mixed timeline.  The eight-tick `statePullAlign8_of_stateWalk` is this theorem at
`duration := fun _ => 8`. -/
theorem statePullAlign8_of_durations {α : Type*}
    (edge : α → Channels.StateMsg (ZMod p) × Channels.StateMsg (ZMod p))
    (duration : α → ℕ) :
    ∀ {initial final : Channels.StateMsg (ZMod p)}
      {rows : List α},
      Walk.IsWalk edge initial final rows →
      (∀ row ∈ rows, 8 ∣ duration row) →
      (∀ row ∈ rows,
        Semantics.StateMsg.timeNat (edge row).2 =
          Semantics.StateMsg.timeNat (edge row).1 + duration row) →
      ∀ row ∈ rows,
        Semantics.StateMsg.timeNat (edge row).1 % 8 =
          Semantics.StateMsg.timeNat initial % 8 := by
  intro initial final rows walk dvd steps row rowMem
  obtain ⟨done, suffix, rowsEq⟩ := List.append_of_mem rowMem
  have position :=
    statePullTime_of_stateWalk_durations edge duration walk steps done row suffix rowsEq
  have prefixDvd : 8 ∣ (done.map duration).sum := by
    refine List.dvd_sum ?_
    intro x xMem
    obtain ⟨a, aMem, rfl⟩ := List.mem_map.mp xMem
    exact dvd a (by rw [rowsEq]; exact List.mem_append_left _ aMem)
  obtain ⟨c, hc⟩ := prefixDvd
  omega


end SP1Clean.Soundness
