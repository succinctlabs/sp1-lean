import SP1Clean.Model.Core.ExecutionReplay
import SP1Clean.Model.Core.ExecutionCompatibility
import SP1Clean.Model.Core.ExecutionWritePolicy
import SP1Clean.Model.Core.SailBookkeeping
import SP1Clean.Model.Core.QueueReplay
import SP1Clean.Model.SP1Field
import SP1CleanTest.Alignment.Audit.ActiveNativeCompleteness

/-! # Native local-path and terminal-boundary regressions

Two committed ECALLs execute ENTER followed by HALT from a non-boot clock, preserving nonempty
incoming host state and RAM. Each call is a separate semantic shard, and their joined path is the
same two-step execution. These test the semantic interface, not an AIR witness.
-/

namespace SP1CleanTest.Core.ExecutionPath

open SP1Clean SP1Clean.Model.Core SP1Clean.Machine SP1Clean.Soundness.Target
  LeanRV64D LeanRV64D.Defs

private def policy : HostPolicy := ⟨⟨fun _ => false, NativeLayout.guestMemory⟩, SP1Prime⟩

private def program : GuestProgram where
  rom := [(65536, 0x73), (65540, 0x73)]
  pc_start := 65536
  memImage := []
  rom_nodup := by decide
  rom_aligned := by simp
  rom_in_window := by simp
  rom_full_width := by simp

private def source : ExecutionState where
  sail := { (default : SailState) with
    regs := ((((default : SailState).regs.insert Register.PC 65536).insert Register.x5 3).insert
      Register.x10 70000).insert Register.x11 0
    mem := (∅ : Std.ExtHashMap ℕ (BitVec 8)).insertMany
      [(65536, 0x73), (65537, 0), (65538, 0), (65539, 0),
        (65540, 0x73), (65541, 0), (65542, 0), (65543, 0), (65552, 42)] }
  host := { io := ⟨[[7, 8]], [9]⟩ }
  clock := 17

private def enter : SP1Clean.Model.Core.HostExecution :=
  ⟨.enterUnconstrained, 70000, 0, 0, ⟨source.host, none⟩⟩

private def middle : ExecutionState :=
  ⟨enter.apply source.sail 65536, enter.effect.state, source.clock + 264⟩

private def halt : SP1Clean.Model.Core.HostExecution :=
  ⟨.halt, 70000, 0, 0, ⟨{ middle.host with exitCode := some 70000 }, none⟩⟩

private def target : ExecutionState :=
  ⟨halt.apply middle.sail 65540, halt.effect.state, middle.clock + 264⟩

private theorem enter_run : source.host.run policy (.ofSail source.sail) = some enter := by
  native_decide

private theorem halt_run : middle.host.run policy (.ofSail middle.sail) = some halt := by
  native_decide

private theorem enter_step : ExecutionStep policy program source
    (.syscall (enter.toEvent source.clock 65536)) middle := by
  exact .syscall (HostState.step_of_run (by native_decide) (by native_decide) (by native_decide) enter_run _)

private theorem halt_step : ExecutionStep policy program middle
    (.syscall (halt.toEvent middle.clock 65540)) target := by
  exact .syscall (HostState.step_of_run (by native_decide) (by native_decide) (by native_decide) halt_run _)

/-- Actual Sail memory is partial: every ECALL byte must be present, including its zero bytes.
The committed program and a valid host request cannot replace any missing instruction byte. -/
theorem rejectsMissingCodeBytes :
    ((List.range 4).map fun offset =>
      (source.host.step policy program source.clock
        { source.sail with mem := source.sail.mem.erase (65536 + offset) }).isNone) =
        [true, true, true, true] := by
  native_decide

/-- A cut preserves the code-memory obligation: corrupting a later ECALL rejects replay even
though that word is still present in the committed program and the HALT registers are valid. -/
theorem rejectsCorruptedContinuation :
    ((List.range 4).map fun offset =>
      (replayHost? policy program
        { middle with sail.mem := (middle.sail.mem.insert (65540 + offset)
          (if offset = 0 then 0 else 1)) }
        (halt.toEvent middle.clock 65540)).isNone) = [true, true, true, true] := by
  native_decide

/-- A continuing shard need not start at boot or end at HALT. -/
theorem continuingShard : ExecutionSegment policy program source 1 middle :=
  ⟨_, rfl, .cons enter_step (.nil _)⟩

/-- The terminal syscall is a single real step in the same local relation. -/
theorem terminalShard : ExecutionSegment policy program middle 1 target :=
  ⟨_, rfl, .cons halt_step (.nil _)⟩

theorem joinedShards : ExecutionSegment policy program source 2 target :=
  continuingShard.append terminalShard

theorem splitJoinedShards : ∃ boundary, ExecutionSegment policy program source 1 boundary ∧
    ExecutionSegment policy program boundary 1 target :=
  ExecutionSegment.add_iff.mp joinedShards

theorem polyFunPath : (executionSystem policy program).ReachableIn 2 source target :=
  ExecutionSegment.iff_reachableIn.mp joinedShards

/-- Identity at a terminal state adds no instruction and preserves every state component. -/
theorem terminalIdentity : ExecutionSegment policy program target 0 target := .refl target

private theorem target_halted : target.host.exitCode ≠ none := by native_decide

theorem rejectsAfterHalt (event : ExecutionEvent) (next : ExecutionState) :
    ¬ ExecutionStep policy program target event next :=
  ExecutionStep.not_of_halted target_halted

theorem rejectsPositiveTerminalSegment (steps : ℕ) (positive : 0 < steps)
    (next : ExecutionState) : ¬ ExecutionSegment policy program target steps next := by
  intro segment
  have stopped := segment.of_halted target_halted
  omega

/-- Host continuity cannot be replaced by equality of the PC and clock. -/
theorem rejectsForgedHost : ¬ ExecutionSegment policy program source 2
    { target with host := { target.host with io := ⟨[], [99]⟩ } } := by
  intro forged
  have equal := congrArg (fun state : ExecutionState => state.host.io.publicOutput)
    (joinedShards.deterministic forged)
  have wrong : target.host.io.publicOutput ≠ [99] := by native_decide
  exact wrong equal

/-- Even a zero-step shard cannot alter an unaccessed RAM location. -/
theorem rejectsForgedMemory : ¬ ExecutionSegment policy program target 0
    { target with sail := { target.sail with mem := target.sail.mem.insert 65552 99 } } := by
  intro forged
  have equal := congrArg (fun state : ExecutionState => state.sail.mem.get? 65552)
    (ExecutionSegment.zero_iff.mp forged)
  have wrong : (target.sail.mem.insert 65552 99).get? 65552 ≠ target.sail.mem.get? 65552 := by
    native_decide
  exact wrong equal

theorem observableResults : target.clock = 545 ∧ target.host.exitCode = some 70000 ∧
    target.host.io.hints = [[7, 8]] ∧ target.host.io.publicOutput = [9] ∧
    target.sail.mem.get? 65552 = some 42 ∧ target.sail.regs.get? Register.PC = some haltPc := by
  native_decide

/-- Direct replay threads ENTER's returned x5 into the next HALT dispatch. -/
theorem replayJoinedShards : replayEvents? policy program source
    [.syscall (enter.toEvent source.clock 65536), .syscall (halt.toEvent middle.clock 65540)] =
      some target :=
  (ExecutionPath.cons enter_step (.cons halt_step (.nil _))).replay

/-- Host replay rejects altered result and timestamp fields, rather than trusting event data. -/
theorem rejectsForgedEvent :
    replayHost? policy program source { enter.toEvent source.clock 65536 with result := 1 } = none ∧
    replayHost? policy program source { enter.toEvent source.clock 65536 with clock := 18 } = none := by
  native_decide

/-- The existing official-Sail/AIR self-jump anchor embeds as an ordinary local step. -/
theorem ordinaryContinues (host : HostState) (running : host.exitCode = none) (clock : ℕ) :
    ExecutionStep policy Audit.JointNonVacuity.anchorProgram
      ⟨Audit.JointNonVacuity.anchorState, host, clock⟩ .ordinary
      ⟨Audit.ActiveNativeCompleteness.activeTarget, host, clock + 8⟩ :=
  .ordinary running Audit.ActiveNativeCompleteness.anchor_notAboutToExecuteEcall
    Audit.ActiveNativeCompleteness.activeTarget_effect.normal

/-- A genuinely retiring JAL remains admitted by the write policy, even if every byte is read-only. -/
theorem ordinaryWritePermission (host : HostState) (running : host.exitCode = none) (clock : ℕ) :
    ExecutionPath { policy with memory.readOnly := fun _ => true } Audit.JointNonVacuity.anchorProgram
      ⟨Audit.JointNonVacuity.anchorState, host, clock⟩ [.ordinary]
      ⟨Audit.ActiveNativeCompleteness.activeTarget, host, clock + 8⟩ ∧
    ExecutionPath.WritesPermitted { policy with memory.readOnly := fun _ => true }
      Audit.JointNonVacuity.anchorProgram ⟨Audit.JointNonVacuity.anchorState, host, clock⟩ [.ordinary] := by
  refine ⟨.cons (.ordinary running Audit.ActiveNativeCompleteness.anchor_notAboutToExecuteEcall
    Audit.ActiveNativeCompleteness.activeTarget_effect.normal) (.nil _), ?_⟩
  intro n current atEvent replay
  have zero : n = 0 := by
    obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp atEvent
    simpa using bound
  subst n
  obtain rfl := Option.some.inj replay
  refine ⟨65536, 0x6f, .JAL (0, .Regidx 0), Audit.JointNonVacuity.anchorState_pc,
    Audit.ActiveNativeCompleteness.anchorProgram_fetchWord_selfJump,
    Audit.ActiveNativeCompleteness.activeExecution_configuredDecode, ?_⟩
  rfl

/-- Host-only composition needs no artificial ordinary-write obligation. -/
theorem hostWritePermission : ExecutionPath.WritesPermitted policy program source
    [.syscall (enter.toEvent source.clock 65536), .syscall (halt.toEvent middle.clock 65540)] := by
  rw [ExecutionPath.writesPermitted_cons_iff enter_step,
    ExecutionPath.writesPermitted_cons_iff halt_step]
  simp only [reduceCtorEq, false_implies, ExecutionPath.writesPermitted_nil, and_self]

/-- A real normally-retiring Sail instruction is still forbidden after the host has halted. -/
theorem rejectsRunnableAfterHalt :
    SailRetiresNormally Audit.JointNonVacuity.anchorState Audit.ActiveNativeCompleteness.activeTarget ∧
      ¬ ExecutionStep policy Audit.JointNonVacuity.anchorProgram
        ⟨Audit.JointNonVacuity.anchorState, { exitCode := some 0 }, 17⟩ .ordinary
        ⟨Audit.ActiveNativeCompleteness.activeTarget, { exitCode := some 0 }, 25⟩ :=
  ⟨Audit.ActiveNativeCompleteness.activeTarget_effect.normal,
    ExecutionStep.not_of_halted (by decide)⟩

/-- Prefix replay observes the complete intermediate host/Sail state and holds the exact endpoint
past the tape. Holding that endpoint does not permit a further ordinary instruction. -/
theorem replayPrefixStates :
    let events := [.syscall (enter.toEvent source.clock 65536), .syscall (halt.toEvent middle.clock 65540)]
    executionTrajectory policy program source events 1 = some middle ∧
      executionTrajectory policy program source events 2 = some target ∧
      executionTrajectory policy program source events 5 = some target := by
  refine ⟨(ExecutionPath.cons enter_step (.nil _)).replay, replayJoinedShards, ?_⟩
  exact (executionTrajectory_after _ _ _ _ _ (by decide)).trans replayJoinedShards

/-- Appending a real event after HALT fails, in contrast to the mathematical endpoint extension. -/
theorem replayStopsAfterHalt :
    replayEvents? policy program source
      ([.syscall (enter.toEvent source.clock 65536), .syscall (halt.toEvent middle.clock 65540)] ++ [.ordinary]) = none := by
  rw [replayEvents?_append, replayJoinedShards, Option.bind_some]
  simp only [replayEvents?, replayStep?, show target.host.exitCode = some 70000 from rfl,
    Option.isSome_some, Bool.true_or, ↓reduceIte, Option.bind_none]

/-- Official ordinary replay threads any running host unchanged, with its full state and clock. -/
theorem replayOrdinaryPreservesHost (host : HostState) (running : host.exitCode = none) (clock : ℕ) :
    executionTrajectory policy Audit.JointNonVacuity.anchorProgram
      ⟨Audit.JointNonVacuity.anchorState, host, clock⟩ [.ordinary] 1 =
        some ⟨Audit.ActiveNativeCompleteness.activeTarget, host, clock + 8⟩ :=
  (ExecutionPath.cons (ordinaryContinues host running clock) (.nil _)).replay

private noncomputable def bookkeepingSource (inhibit : Bool) : SailState :=
  { Audit.JointNonVacuity.anchorState with
    regs := (((((Audit.JointNonVacuity.anchorState.regs.insert .mcountinhibit
      (if inhibit then 4 else 0)).insert .minstretcfg 0).insert .minstret (BitVec.allOnes 64)).insert
      .nextPC 80000).insert .mcycle 73)
    cycleCount := 29
    sailOutput := #["earlier Sail output"] }

private theorem bookkeepingConfigured (inhibit : Bool) : SailConfigured (bookkeepingSource inhibit) := by
  apply Advance.SailConfigured.congr Audit.JointNonVacuity.anchorState_configured
  · exact SailState.isInitialized_insert _ (SailState.isInitialized_insert _
      (SailState.isInitialized_insert _ (SailState.isInitialized_insert _
        (SailState.isInitialized_insert _ Audit.JointNonVacuity.anchorState_configured.init _ _) _ _) _ _) _ _) _ _
  · intro R member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [bookkeepingSource, Std.ExtDHashMap.get?_insert] <;> rfl

/-- A real normally retiring self-jump wraps the retirement counter only when enabled, updates
nextPC, and preserves distinct nonzero simulator/CSR counters and nonempty Sail output. -/
theorem ordinaryBookkeeping (inhibit : Bool) :
    ∃ next, SailRetiresNormally (bookkeepingSource inhibit) next ∧
      next.regs.get? Register.nextPC = some 65536 ∧
      next.regs.get? Register.minstret_increment = some (!inhibit) ∧
      next.regs.get? Register.minstret = some (if inhibit then BitVec.allOnes 64 else 0) ∧
      next.regs.get? Register.mcycle = some 73 ∧
      next.cycleCount = 29 ∧ next.sailOutput = #["earlier Sail output"] := by
  have configured := bookkeepingConfigured inhibit
  have pc : (bookkeepingSource inhibit).regs.get? Register.PC = some 65536#64 := by
    simp only [bookkeepingSource, Std.ExtDHashMap.get?_insert]
    exact Audit.JointNonVacuity.anchorState_pc
  have rom : RomLoaded Audit.JointNonVacuity.anchorProgram (bookkeepingSource inhibit) :=
    Audit.JointNonVacuity.anchorState_romLoaded
  obtain ⟨next, _, effect⟩ := Advance.advance_of_jal_x0 (p := SP1Prime)
    (prog := Audit.JointNonVacuity.anchorProgram) (r := Audit.JointNonVacuity.jalView)
    configured rom (by rw [Audit.JointNonVacuity.jalView_rcvPc]; exact pc)
    Audit.JointNonVacuity.jalView_decodedInROM rfl rfl rfl
    (by rw [Audit.JointNonVacuity.jalView_sndPc]; decide)
    (fun imm bound => by
      have bytes : bitVecToWord (p := SP1Prime) ((0#21 : BitVec 21).signExtend 64) =
          bitVecToWord (imm.signExtend 64) := bound
      have value := congrArg Word.toBitVec64 bytes
      rw [toBitVec64_bitVecToWord, toBitVec64_bitVecToWord] at value
      rw [Audit.JointNonVacuity.jalView_rcvPc, Audit.JointNonVacuity.jalView_sndPc,
        show LeanRV64D.Functions.sign_extend (m := 64) imm = imm.signExtend 64 from rfl, ← value]
      decide)
  obtain ⟨increment, enabled, flag, retired⟩ := effect.retirement
  have observed : (LeanRV64D.Functions.should_inc_minstret Privilege.Machine).run
      (bookkeepingSource inhibit) = .ok (!inhibit) (bookkeepingSource inhibit) := by
    rw [TryStepReduction.run_should_inc_minstret _ configured.init]
    congr 1
    simp only [bookkeepingSource, Std.ExtDHashMap.get_insert, beq_iff_eq,
      reduceCtorEq, ↓reduceDIte, cast_eq]
    cases inhibit <;> decide
  have incrementEq : increment = !inhibit := by
    have same := enabled.symm.trans observed
    cases same
    rfl
  rw [incrementEq] at flag retired
  refine ⟨next, effect.normal, ?_, flag, ?_, ?_, effect.runtime⟩
  · rw [effect.nextPC, effect.pc, Audit.JointNonVacuity.jalView_sndPc]
    decide
  · rw [retired]
    simp only [bookkeepingSource, Std.ExtDHashMap.get?_insert]
    cases inhibit <;> decide
  · rw [effect.otherRegs Register.mcycle (by decide) (by decide) (by decide) (by decide)
      (fun index => by unfold reg_idx_to_Register; split <;> decide)]
    exact Std.ExtDHashMap.get?_insert_self

private def hostBookkeepingSource : ExecutionState :=
  { source with sail := { source.sail with
    regs := ((((source.sail.regs.insert Register.nextPC 80000).insert Register.minstret
      (BitVec.allOnes 64)).insert Register.minstret_increment true).insert Register.mcountinhibit 4).insert
        Register.minstretcfg 0 } }

private def hostBookkeepingMiddle : ExecutionState :=
  ⟨enter.apply hostBookkeepingSource.sail 65536, enter.effect.state, hostBookkeepingSource.clock + 264⟩

private def hostBookkeepingTarget : ExecutionState :=
  ⟨halt.apply hostBookkeepingMiddle.sail 65540, halt.effect.state, hostBookkeepingMiddle.clock + 264⟩

/-- A real ENTER/HALT path has no ordinary retirement. It keeps nonzero nextPC and minstret,
including an old increment flag different from the currently disabled retirement decision. -/
theorem hostBookkeeping :
    ExecutionPath policy program hostBookkeepingSource
      [.syscall (enter.toEvent source.clock 65536), .syscall (halt.toEvent middle.clock 65540)] hostBookkeepingTarget ∧
      hostBookkeepingTarget.sail.regs.get? Register.PC = some haltPc ∧
      hostBookkeepingTarget.sail.regs.get? Register.nextPC = some 80000 ∧
      hostBookkeepingTarget.sail.regs.get? Register.minstret = some (BitVec.allOnes 64) ∧
      hostBookkeepingTarget.sail.regs.get? Register.minstret_increment = some true ∧
      retirementEnabled hostBookkeepingSource.sail = false := by
  constructor
  · have first : ExecutionStep policy program hostBookkeepingSource
        (.syscall (enter.toEvent source.clock 65536)) hostBookkeepingMiddle :=
      .syscall (HostState.step_of_run (by native_decide) (by native_decide) (by native_decide) (by native_decide) _)
    have last : ExecutionStep policy program hostBookkeepingMiddle
        (.syscall (halt.toEvent middle.clock 65540)) hostBookkeepingTarget :=
      .syscall (HostState.step_of_run (by native_decide) (by native_decide) (by native_decide) (by native_decide) _)
    exact .cons first (.cons last (.nil _))
  · native_decide

/-- Observation arithmetic on mixed labels distinguishes retirement count from elapsed ticks,
and keeps the last ordinary nextPC across a trailing host suffix and HALT. This is not an AIR fixture. -/
theorem bookkeepingObservationExamples :
    ([ExecutionEvent.ordinary, .syscall (enter.toEvent 17 65536), .ordinary,
      .syscall (halt.toEvent 289 65540)].foldl
        (fun values event => retirementTick values event.isOrdinary) (true, some false, some (BitVec.allOnes 64)) =
          (true, some true, some 1)) ∧
    ([ExecutionEvent.ordinary, .syscall (enter.toEvent 17 65536), .ordinary].foldl
        (fun values event => retirementTick values event.isOrdinary) (false, some true, some 7) =
          (false, some false, some 7)) ∧
    nextPcAfter [.ordinary, .syscall (enter.toEvent 17 65536), .syscall (halt.toEvent 281 65540)]
      (some 80000) (some haltPc) = some 65536 ∧
    nextPcAfter [.syscall (enter.toEvent 17 65536), .ordinary] (some 80000) (some 90000) = some 90000 ∧
    nextPcAfter [.syscall (enter.toEvent 17 65536), .syscall (halt.toEvent 281 65540)]
      (some 80000) (some haltPc) = some 80000 ∧
    nextPcAfter [] (some 80000) (some 90000) = some 80000 := by
  decide

private def queueProgram : GuestProgram where
  rom := [(65536, 0x73), (65540, 0x73), (65544, 0x73)]
  pc_start := 65536
  memImage := []
  rom_nodup := by decide
  rom_aligned := by simp
  rom_in_window := by simp
  rom_full_width := by simp

private def queueSource : ExecutionState where
  sail := { (default : SailState) with
    regs := ((((default : SailState).regs.insert Register.PC 65536).insert Register.x5 241).insert
      Register.x10 65552).insert Register.x11 8
    mem := (∅ : Std.ExtHashMap ℕ (BitVec 8)).insertMany
      [(65536, 0x73), (65537, 0), (65538, 0), (65539, 0),
        (65540, 0x73), (65541, 0), (65542, 0), (65543, 0),
        (65544, 0x73), (65545, 0), (65546, 0), (65547, 0), (65576, 42)] }
  host := { io := ⟨[[1, 2, 3, 4, 5, 6, 7, 8], [11, 12, 13, 14, 15, 16, 17, 18]], [9]⟩ }
  clock := 2 ^ 24 - 263

private def readEvent (index : ℕ) : CoreSyscallEvent where
  clock := queueSource.clock + 264 * index
  pc := BitVec.ofNat 64 (65536 + 4 * index)
  nextPc := BitVec.ofNat 64 (65540 + 4 * index)
  rawCode := 241
  arg1 := 65552
  arg2 := 8
  result := 241

private def queueObserved (state : ExecutionState) :=
  (state.clock, state.host.io.hints, state.host.io.publicOutput,
    [65552, 65559, 65560, 65567, 65576].map fun address => state.sail.mem.get? address)

/-- Consecutive real HINT_READ replays consume the current hints, overwrite the same RAM span,
write the mandatory extra padding word, preserve unrelated RAM/output, and cross a 24-bit clock.
The third committed call fails on an empty queue. This is a semantic replay regression, not an AIR witness. -/
theorem queueHostReplay :
    let events := [.syscall (readEvent 0), .syscall (readEvent 1)]
    (replayEvents? policy queueProgram queueSource (events.take 1)).map queueObserved =
      some (queueSource.clock + 264, [[11, 12, 13, 14, 15, 16, 17, 18]], [9],
        [some 1, some 8, some 0, some 0, some 42]) ∧
      (replayEvents? policy queueProgram queueSource events).map queueObserved =
        some (queueSource.clock + 528, [], [9], [some 11, some 18, some 0, some 0, some 42]) ∧
      (replayEvents? policy queueProgram queueSource (events ++ [.syscall (readEvent 2)])).isNone = true ∧
      events.filterMap queueEvent? = [.read 8, .read 8] ∧
      HintQueue.replay? (events.filterMap queueEvent?) queueSource.host.io.hints = some [] := by
  simp only [List.take_succ_cons, List.take_zero, List.cons_append, List.nil_append, replayEvents?, replayStep?]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- WRITE may prepend hints despite having no label-only queue projection; the replay guard
must reject erasing this event. Allocation-aware replay remains the separate general model. -/
theorem queueWriteNeedsAllocation :
    let writing := .syscall { readEvent 0 with rawCode := 2, arg1 := 14, result := 2 }
    ¬ QueueProjectionSafe writing ∧ queueEvent? writing = none ∧
      (queueSource.host.writeOutput 14 [99]).map (·.io.hints) = some ([99] :: queueSource.host.io.hints) := by
  unfold QueueProjectionSafe
  native_decide

/-- A nonzero HALT from an evolved, nonempty host produces the same legacy Sail endpoint,
with the actual local clock. The fixed handler is immaterial on this fragment. -/
theorem legacyHaltEndpoint (handler : ExecutableSyscallHandler) :
    ∃ trace : EventExecutionTrace,
      traceOfEvents? handler.withHalt program middle.sail
        [.syscall (halt.toEvent middle.clock 65540)] = some trace ∧
      trace.Valid handler.withHalt.relation program ∧ trace.Clocked 281 ∧
      trace.finalState = target.sail ∧ target.host.exitCode = some 70000 ∧
      target.clock = 545 := by
  obtain ⟨trace, replay, valid, clocked, _, _, final, _⟩ :=
    (SP1Clean.Model.Core.ExecutionPath.cons halt_step (.nil _)).ordinaryHalt_trace
      (by simp [OrdinaryOrHalt, halt, SP1Clean.Model.Core.HostExecution.toEvent, SyscallKind.code]) handler
  exact ⟨trace, replay, valid, clocked, final, rfl, rfl⟩

/-- The legacy ordinary trajectory and complete replay agree throughout a genuine Sail step. -/
theorem legacyOrdinaryTrajectory (host : HostState) (running : host.exitCode = none)
    (clock position : ℕ) (covered : position ≤ 1) (handler : ExecutableSyscallHandler) :
    Semantics.eventTrajectory handler.withHalt Audit.JointNonVacuity.anchorProgram
      [.ordinary] Audit.JointNonVacuity.anchorState position =
      (executionTrajectory policy Audit.JointNonVacuity.anchorProgram
        ⟨Audit.JointNonVacuity.anchorState, host, clock⟩ [.ordinary] position).map ExecutionState.sail :=
  (SP1Clean.Model.Core.ExecutionPath.cons (ordinaryContinues host running clock) (.nil _)).ordinaryHalt_trajectory
    (by simp [OrdinaryOrHalt]) handler position covered

/-- A stopped identity remains empty in the compatibility projection; it does not resume HALT. -/
theorem legacyStoppedIdentity (handler : ExecutableSyscallHandler) :
    ∃ trace : EventExecutionTrace,
      traceOfEvents? handler.withHalt program target.sail [] = some trace ∧
      trace.Valid handler.withHalt.relation program ∧ trace.events = [] ∧
      trace.finalState = target.sail := by
  obtain ⟨trace, replay, valid, _, _, tape, final, _⟩ :=
    (SP1Clean.Model.Core.ExecutionPath.nil (policy := policy) (program := program) target).ordinaryHalt_trace
      (by simp) handler
  exact ⟨trace, replay, valid, tape, final⟩

/-- A non-HALT host call is outside this compatibility fragment even when concrete replay succeeds. -/
theorem enterOutsideLegacyFragment : ¬ OrdinaryOrHalt (.syscall (enter.toEvent source.clock 65536)) := by
  unfold OrdinaryOrHalt
  decide

end SP1CleanTest.Core.ExecutionPath
