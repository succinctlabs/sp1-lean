import SP1Clean.Soundness.SystemMemoryRows
import SP1Clean.Soundness.SystemTouches

/-! # HALT step and frame facts

HALT parks the PC and preserves every register and RAM cell. Its three Memory pushes re-establish
the incoming register values at the constrained access clocks. This proof works over any trajectory
with that successor and does not execute ECALL through Sail or assume global Memory truth.
-/

namespace SP1Clean.Soundness

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Semantics TimedGrounding LeanRV64D.Defs

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance haltFieldLowerBound : Fact (2 ^ 17 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

private theorem halt_code_assert_mem (input : Var HaltChip.Inputs (ZMod p)) (offset : ℕ)
    (idx : Fin 4) : input.is_real * input.x5_memory.prev_value[idx.val] ∈
      ((HaltChip.main input).operations offset).shallowConstraints := by
  fin_cases idx <;> simp only [HaltChip.main, circuit_norm, Operations.shallowConstraints,
    List.mem_cons, true_or, or_true]

/-- The four gated assertions force the actual HALT code word to zero, before Memory grounding. -/
theorem HaltChip.codeZero_of_shallow
    (input : Var HaltChip.Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (shallow : ConstraintsHold.Shallow env ((HaltChip.main input).operations offset))
    (real : Expression.eval env input.is_real = 1) :
    Word.toBitVec64 (Eval.eval env input).x5_memory.prev_value = 0 := by
  have zeros (idx : Fin 4) : Expression.eval env input.x5_memory.prev_value[idx.val] = 0 := by
    have checked : Expression.eval env (input.is_real * input.x5_memory.prev_value[idx.val]) = 0 :=
      (constraintsHold_shallow_iff_forall_mem.mp shallow).1 _
      (halt_code_assert_mem input offset idx)
    change Expression.eval env input.is_real * Expression.eval env input.x5_memory.prev_value[idx.val] = 0 at checked
    rwa [real, one_mul] at checked
  rcases input with ⟨state, ⟨value5, time5⟩, ten, eleven, gate⟩
  have z0 : Expression.eval env value5[0] = 0 := zeros 0
  have z1 : Expression.eval env value5[1] = 0 := zeros 1
  have z2 : Expression.eval env value5[2] = 0 := zeros 2
  have z3 : Expression.eval env value5[3] = 0 := zeros 3
  simp only [Word.toBitVec64, Word.toNat, circuit_norm, z0, z1, z2, z3,
    ZMod.val_zero, zero_mul, add_zero]
  rfl

private theorem halt_exit_assert_mem (input : Var HaltChip.Inputs (ZMod p)) (offset : ℕ)
    (idx : Fin 3) : input.is_real * input.x10_memory.prev_value[idx.val + 1] ∈
      ((HaltChip.main input).operations offset).shallowConstraints := by
  fin_cases idx <;> simp only [HaltChip.main, circuit_norm, Operations.shallowConstraints,
    List.mem_cons, true_or, or_true]

/-- The legacy HALT row pins all three upper exit limbs to zero. This is a 16-bit restriction. -/
theorem HaltChip.exitHighZero_of_shallow
    (input : Var HaltChip.Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (shallow : ConstraintsHold.Shallow env ((HaltChip.main input).operations offset))
    (real : Expression.eval env input.is_real = 1) :
    (Eval.eval env input).x10_memory.prev_value[1] = 0 ∧
      (Eval.eval env input).x10_memory.prev_value[2] = 0 ∧
      (Eval.eval env input).x10_memory.prev_value[3] = 0 := by
  have zeros (idx : Fin 3) : Expression.eval env input.x10_memory.prev_value[idx.val + 1] = 0 := by
    have checked : Expression.eval env (input.is_real * input.x10_memory.prev_value[idx.val + 1]) = 0 :=
      (constraintsHold_shallow_iff_forall_mem.mp shallow).1 _ (halt_exit_assert_mem input offset idx)
    change Expression.eval env input.is_real * Expression.eval env input.x10_memory.prev_value[idx.val + 1] = 0 at checked
    rwa [real, one_mul] at checked
  rcases input with ⟨state, five, ⟨value10, time10⟩, eleven, gate⟩
  have z1 : Expression.eval env value10[1] = 0 := zeros 0
  have z2 : Expression.eval env value10[2] = 0 := zeros 1
  have z3 : Expression.eval env value10[3] = 0 := zeros 2
  simp only [circuit_norm, z1, z2, z3, and_self]

omit [Fact (2 ^ 25 < p)] in
/-- Memory hygiene supplies the low-limb bound; the three zero assertions leave a 16-bit exit. -/
theorem HaltChip.exit_lt_of_highZero (value : Word (ZMod p)) (small : Word.isU64 value)
    (high : value[1] = 0 ∧ value[2] = 0 ∧ value[3] = 0) :
    (Word.toBitVec64 value).toNat < 2 ^ 16 := by
  rw [Word.toBitVec64_toNat small, Word.toNat_def, high.1, high.2.1, high.2.2]
  simp only [ZMod.val_zero, zero_mul, add_zero]
  exact (Word.lt_cases_of_isU64 small).1

private theorem pcPark_content (state : SailState) (loc : MemLoc) :
    locContent { state with regs := state.regs.insert Register.PC Machine.haltPc } loc =
      locContent state loc := by
  cases loc with
  | reg idx => exact SailState.get_reg?_insert_of_ne (by revert idx; decide)
  | ram cell => rfl

private theorem pcPark_configured (state : SailState) (configured : Target.SailConfigured state) :
    Target.SailConfigured { state with regs := state.regs.insert Register.PC Machine.haltPc } := by
  refine SP1Clean.Advance.SailConfigured.congr configured
    (SailState.isInitialized_insert state configured.init _ _) ?_
  intro reg member
  have different : ¬ ((Register.PC == reg) = true) := by
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  show (state.regs.insert Register.PC Machine.haltPc).get? reg = state.regs.get? reg
  rw [Std.ExtDHashMap.get?_insert, dif_neg different]

omit [Fact (2 ^ 25 < p)] in
private theorem currency_of_unchanged {trajectory : Trajectory} {initial source target : SailState}
    {timeline : Timeline} {n time : ℕ} {loc : MemLoc} {value : Word (ZMod p)}
    (before : trajectory n = some source) (after : trajectory (n + 1) = some target)
    (unchanged : locContent target loc = locContent source loc)
    (content : locContent source loc = some (Word.toBitVec64 value))
    (lo : timeline.start n ≤ time) (hi : time ≤ timeline.start (n + 1)) :
    LocalValueAtG trajectory initial timeline loc time value := by
  unfold LocalValueAtG
  cases loc with
  | reg idx =>
    by_cases pre : time < timeline.start n + 4
    · rw [microValueG_reg_pre lo pre, before, Option.bind_some, content]
    · rw [microValueG_reg_post (n := n) (by omega) (by omega), after, Option.bind_some, unchanged, content]
  | ram cell =>
    by_cases pre : time < timeline.start n + 1
    · rw [microValueG_ram_pre lo pre, before, Option.bind_some, content]
    · rw [microValueG_ram_post (n := n) (by omega) (by omega), after, Option.bind_some, unchanged, content]

private theorem halt_push_time (row : HaltChip.Inputs (ZMod p))
    (clock : ((row.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧
      row.state.clk_16_24.val < 2 ^ 8)
    (block : Circuits.Types.RegisterAccessCols (ZMod p)) (idx : ZMod p) (off : ℕ) (bound : off ≤ 4) :
    MemoryMsg.timeNat (HaltChip.memPushedMessage row block idx off) =
        StateMsg.timeNat (HaltChip.statePulledMessage row) + off ∧
      MemoryMsg.ClkBound (HaltChip.memPushedMessage row block idx off) := by
  obtain ⟨small, addition⟩ := TimeExtraction.clkVal_small_add_of_cpuState_bounds
    row.state.clk_0_16 row.state.clk_16_24 off (by omega) clock.1 clock.2
  constructor
  · simp only [MemoryMsg.timeNat, HaltChip.memPushedMessage, StateMsg.timeNat,
      HaltChip.statePulledMessage, clkNat]
    omega
  · change (row.state.clk_0_16 + row.state.clk_16_24 * 65536 + (off : ZMod p)).val < 2 ^ 24
    omega

private theorem halt_pair_current {row : HaltChip.Inputs (ZMod p)}
    (clock : ((row.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧
      row.state.clk_16_24.val < 2 ^ 8)
    {trajectory : Trajectory} {initial source : SailState} {timeline : Timeline} {n : ℕ}
    (before : trajectory n = some source)
    (after : trajectory (n + 1) =
      some { source with regs := source.regs.insert Register.PC Machine.haltPc })
    (time : StateMsg.timeNat (HaltChip.statePulledMessage row) = timeline.start n)
    (block : Circuits.Types.RegisterAccessCols (ZMod p)) (idx : ZMod p) (off : ℕ) (bound : off ≤ 4)
    (current : MemoryMsg.isU64 (HaltChip.memPulledMessage row block idx) ∧
      LocalValueAtG trajectory initial timeline (MemoryMsg.locOf (HaltChip.memPulledMessage row block idx))
        (StateMsg.timeNat (HaltChip.statePulledMessage row)) block.prev_value) :
    LocalMemTruthG trajectory initial timeline (HaltChip.memPushedMessage row block idx off) := by
  have times := halt_push_time row clock block idx off bound
  have sameLoc : MemoryMsg.locOf (HaltChip.memPushedMessage row block idx off) =
      MemoryMsg.locOf (HaltChip.memPulledMessage row block idx) := rfl
  refine ⟨current.1, times.2, ?_⟩
  have currency := current.2
  rw [time] at currency
  have content := (localValueAtG_stepStart_iff before).mp currency
  apply currency_of_unchanged before after (pcPark_content source _)
  · rwa [sameLoc]
  · rw [times.1, time]; omega
  · rw [times.1, time]; have := timeline.gap n; omega

/-- Canonical HALT supplies both generic engine facts from its checked clock and its PC-only step.
The three prior records' hygiene and values enter only through the engine's incoming currency. -/
theorem halt_engineFactsG_of_currencyStep (row : HaltChip.Inputs (ZMod p))
    (clock : ((row.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧
      row.state.clk_16_24.val < 2 ^ 8)
    (program : Target.GuestProgram) (trajectory : Trajectory) (initial : SailState) (timeline : Timeline)
    (timeStep : ∀ n, StateMsg.timeNat (HaltChip.statePulledMessage row) = timeline.start n →
      StateMsg.timeNat (HaltChip.statePushedMessage row) = timeline.start (n + 1))
    (step : LocalStateTruthG program trajectory timeline (haltRowFacts row).statePull →
      (∀ mp ∈ (haltRowFacts row).memPulls, MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1 ∧
        LocalValueAtG trajectory initial timeline (MemoryMsg.locOf mp.1) mp.2 mp.1.value) →
      ∀ n, StateMsg.timeNat (HaltChip.statePulledMessage row) = timeline.start n →
      trajectory (n + 1) = (trajectory n).map
        (fun state => { state with regs := state.regs.insert Register.PC Machine.haltPc })) :
    LocalStepFactG program trajectory initial timeline (haltRowFacts row) ∧
      FrameFactG program trajectory initial timeline (haltRowFacts row) := by
  constructor
  · intro stateTruth currency
    have next := step stateTruth currency
    obtain ⟨n, source, before, time, _, rom, configured⟩ := stateTruth
    have after := next n time
    rw [before, Option.map_some] at after
    refine ⟨⟨n + 1, _, after, timeStep n time, ?_, rom, pcPark_configured source configured⟩, ?_⟩
    · change (source.regs.insert Register.PC Machine.haltPc).get? Register.PC =
        some (pcBits (1 : ZMod p) 0 0)
      simp only [Std.ExtDHashMap.get?_insert_self, pcBits, ZMod.val_one, ZMod.val_zero,
        zero_mul, add_zero]
      rfl
    · have a := currency _ (show (HaltChip.memPulledMessage row row.x5_memory 5,
          StateMsg.timeNat (HaltChip.statePulledMessage row)) ∈ (haltRowFacts row).memPulls from by simp [haltRowFacts, HaltChip.memoryPairs])
      have b := currency _ (show (HaltChip.memPulledMessage row row.x10_memory 10,
          StateMsg.timeNat (HaltChip.statePulledMessage row)) ∈ (haltRowFacts row).memPulls from by simp [haltRowFacts, HaltChip.memoryPairs])
      have c := currency _ (show (HaltChip.memPulledMessage row row.x11_memory 11,
          StateMsg.timeNat (HaltChip.statePulledMessage row)) ∈ (haltRowFacts row).memPulls from by simp [haltRowFacts, HaltChip.memoryPairs])
      intro message member
      simp only [haltRowFacts, HaltChip.memoryPairs, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact halt_pair_current clock before after time row.x5_memory 5 4 (by decide) ⟨a.1, a.2.2⟩
      · exact halt_pair_current clock before after time row.x10_memory 10 3 (by decide) ⟨b.1, b.2.2⟩
      · exact halt_pair_current clock before after time row.x11_memory 11 2 (by decide) ⟨c.1, c.2.2⟩
  · intro stateTruth currency loc value _ current
    have next := step stateTruth currency
    obtain ⟨n, source, before, time, _⟩ := stateTruth
    change StateMsg.timeNat (HaltChip.statePulledMessage row) = timeline.start n at time
    have after := next n time
    rw [before, Option.map_some] at after
    rw [show (haltRowFacts row).statePull = HaltChip.statePulledMessage row from rfl, time] at current
    rw [show (haltRowFacts row).statePush = HaltChip.statePushedMessage row from rfl, timeStep n time]
    apply (localValueAtG_stepStart_iff after).mpr
    rw [pcPark_content]
    exact (localValueAtG_stepStart_iff before).mp current

/-- Compatibility form for trajectories whose HALT successor is known unconditionally. -/
theorem halt_engineFactsG (row : HaltChip.Inputs (ZMod p))
    (clock : ((row.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧
      row.state.clk_16_24.val < 2 ^ 8)
    (program : Target.GuestProgram) (trajectory : Trajectory) (initial : SailState) (timeline : Timeline)
    (timeStep : ∀ n, StateMsg.timeNat (HaltChip.statePulledMessage row) = timeline.start n →
      StateMsg.timeNat (HaltChip.statePushedMessage row) = timeline.start (n + 1))
    (step : ∀ n, StateMsg.timeNat (HaltChip.statePulledMessage row) = timeline.start n →
      trajectory (n + 1) = (trajectory n).map
        (fun state => { state with regs := state.regs.insert Register.PC Machine.haltPc })) :
    LocalStepFactG program trajectory initial timeline (haltRowFacts row) ∧
      FrameFactG program trajectory initial timeline (haltRowFacts row) :=
  halt_engineFactsG_of_currencyStep row clock program trajectory initial timeline timeStep (fun _ _ => step)

end SP1Clean.Soundness
