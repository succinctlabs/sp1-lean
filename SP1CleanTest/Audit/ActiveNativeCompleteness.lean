import SP1Clean.Soundness.NativeCompleteness
import SP1CleanTest.Audit.ActiveTraceNonVacuity

/-!
# Active deterministic native-completeness audit

`NativeCompletenessNonVacuity` exercises the deterministic compiler on an honest empty shard, while
`ActiveTraceNonVacuity` exercises one circuit-built instruction row from a hand-assembled trace
source.  This audit joins the two: it starts from the official Sail `JAL x0, 0` step, embeds that
nonempty execution in the common semantic witness, and checks the deterministic compiler path.

The definitions are deliberately shared with the existing active AIR anchor.  A change to the Sail
step, semantic projector, event compiler, or JAL trace schema must therefore continue to agree on
one concrete non-padding row.
-/

open LeanRV64D.Defs
open LeanRV64D.Functions

namespace SP1Clean.Audit.ActiveNativeCompleteness

open SP1Clean.Execution SP1Clean.Soundness SP1Clean.TraceGen
open SP1Clean.Audit.JointNonVacuity
open SP1Clean.Audit.ActiveTraceNonVacuity
open SP1Clean.Soundness.Target

/-- The deterministic target of the proved official-Sail self-jump. -/
noncomputable def activeTarget : SailState := Classical.choose anchorStep

theorem activeTarget_step : SailStep anchorState activeTarget :=
  (Classical.choose_spec anchorStep).1

/-- The chosen official-Sail target has the exact JAL row effect used by the trace schema. -/
theorem activeTarget_effect :
    RowEffect anchorProgram jalView anchorState activeTarget :=
  (Classical.choose_spec anchorStep).2

/-- The one-transition official-Sail execution used to audit the native compiler. -/
noncomputable def activeExecution : Machine.EventExecutionTrace where
  initialState := anchorState
  transitions := [⟨.ordinary, activeTarget⟩]

@[simp] theorem activeExecution_initialState : activeExecution.initialState = anchorState := rfl

@[simp] theorem activeExecution_transitions :
    activeExecution.transitions = [⟨.ordinary, activeTarget⟩] := rfl

@[simp] theorem activeExecution_steps : activeExecution.steps = 1 := rfl

@[simp] theorem activeExecution_finalState : activeExecution.finalState = activeTarget := rfl

@[simp] theorem activeExecution_locatedTransitions :
    activeExecution.locatedTransitions =
      [⟨anchorState, ⟨.ordinary, activeTarget⟩⟩] := rfl

/-- Fetching the committed entry point yields the self-jump encoding. -/
theorem anchorProgram_fetchWord_selfJump :
    anchorProgram.fetchWord 65536#64 = some 0x0000006F#32 := by
  native_decide

/-- The configured Sail decoder recognizes the committed word as `JAL x0, 0`. -/
theorem anchor_decode_selfJump :
    (ext_decode 0x0000006F#32).run anchorState =
      .ok (instruction.JAL (0#21, .Regidx 0#5)) anchorState :=
  decode_jal_x0 anchorState anchorState_configured.init anchorState_configured.priv
    anchorState_configured.mseccfg_disabled

/-- The committed self-jump is not an ECALL. -/
theorem anchor_notAboutToExecuteEcall :
    ¬ Machine.AboutToExecuteEcall anchorProgram anchorState := by
  rintro ⟨pc, pcEq, fetch⟩
  rw [anchorState_pc] at pcEq
  injection pcEq with pcEq
  subst pc
  rw [anchorProgram_fetchWord_selfJump] at fetch
  exact (by native_decide : (0x0000006F#32 : BitVec 32) ≠ ECALL_ENC)
    (Option.some.inj fetch)

/-- The proof-free transition list is authenticated by the official Sail step. -/
theorem activeExecution_valid :
    activeExecution.Valid Machine.ExecutableSyscallHandler.haltOnly.relation anchorProgram := by
  exact .cons ⟨.ordinary, activeTarget⟩
    (.ordinary anchor_notAboutToExecuteEcall activeTarget_step) (.nil activeTarget)

theorem activeExecution_allOrdinary : activeExecution.AllOrdinary := by
  intro transition member
  simp only [activeExecution, List.mem_singleton] at member
  subst transition
  rfl

/-- The exact proof-independent projection shared by semantic validity and trace compilation. -/
noncomputable def activeView : SP1Clean.Semantics.SP1TransitionView where
  pc := 65536#64
  word := 0x0000006F#32
  decoded := .JAL (0#21, .Regidx 0#5)
  routeKey := ⟨.JAL, true⟩
  chipId := .jal
  accessPlan? := SP1Clean.Semantics.instructionAccessPlan?
    (.JAL (0#21, .Regidx 0#5)) anchorState activeTarget

theorem activeExecution_projected :
    SP1Clean.Semantics.projectSP1Transition? anchorProgram
      ⟨anchorState, ⟨.ordinary, activeTarget⟩⟩ = some activeView := by
  unfold SP1Clean.Semantics.projectSP1Transition?
  simp only [anchorState_pc, Option.bind_eq_bind, Option.bind_some,
    anchorProgram_fetchWord_selfJump]
  rw [SP1Clean.Semantics.decodeLocated?_eq_some_of anchorState_pc
    anchorProgram_fetchWord_selfJump anchor_decode_selfJump]
  rfl

theorem activeExecution_configuredDecode :
    ConfiguredDecode activeView.word activeView.decoded := by
  intro state configured
  exact decode_jal_x0 state configured.init configured.priv configured.mseccfg_disabled

/-- The active transition belongs to the exact supported 25-chip profile. -/
theorem activeExecution_supported :
    AllTransitionsSupported anchorProgram activeExecution := by
  intro located member
  rw [activeExecution_locatedTransitions, List.mem_singleton] at member
  subst located
  exact ⟨rfl, activeTarget_effect.normal, anchorState_configured, activeView,
    activeExecution_projected, activeExecution_configuredDecode⟩

/-- The self-jump has the single immutable `x0` access expected by the J-type compiler. -/
theorem activeView_accessPlan :
    activeView.accessPlan? = some
      [{ slot := .opA, loc := .reg 0#5, pulled := 0#64, pushed := 0#64 }] := by
  rfl

/-- The one-row event compiler succeeds for every incoming access frontier and row clock. -/
theorem activeView_instructionEventReady (frontier : SP1Clean.Semantics.AccessFrontier)
    (clock : ℕ) : InstructionEventReady activeView frontier clock := by
  unfold InstructionEventReady compileInstructionEvent?
  rw [activeView_accessPlan]
  rfl

/-- Every successful compiler result for the anchored input routes the exact circuit event. -/
theorem activeView_compiled_event
    {result : CompiledInstructionEvent}
    (generated : compileInstructionEvent? activeView SP1Clean.Semantics.AccessFrontier.initial 1 =
      some result) :
    result.routed = ⟨.jal, activeEvent⟩ := by
  unfold compileInstructionEvent? at generated
  rw [activeView_accessPlan] at generated
  injection generated with resultEq
  cases resultEq
  rfl

/-- The anchored input has a successful compiler result carrying the exact circuit event. -/
theorem activeView_compiled_event_exists :
    ∃ result,
      compileInstructionEvent? activeView SP1Clean.Semantics.AccessFrontier.initial 1 =
        some result ∧
      result.routed = ⟨.jal, activeEvent⟩ := by
  obtain ⟨result, generated⟩ :=
    instructionEventReady_iff.mp
      (activeView_instructionEventReady SP1Clean.Semantics.AccessFrontier.initial 1)
  exact ⟨result, generated, activeView_compiled_event generated⟩

/-- The optional chronological compiler succeeds on the active semantic execution. -/
theorem activeExecution_compileExecution?_exists :
    ∃ compiled, compileExecution? anchorProgram activeExecution 1 = some compiled := by
  apply compileExecution?_exists_of_views
  intro located member
  rw [activeExecution_locatedTransitions, List.mem_singleton] at member
  subst located
  exact ⟨activeView, activeExecution_projected, activeView_instructionEventReady⟩

/-- The successful deterministic compiler emits exactly one chronological instruction record. -/
theorem activeExecution_compiled_rows_length :
    (compileExecution anchorProgram activeExecution 1).rows.length = 1 := by
  obtain ⟨compiled, generated⟩ := activeExecution_compileExecution?_exists
  rw [compileExecution_eq_of_some generated]
  exact compileLocatedTransitions?_rows_length generated

/-- The nonempty execution embedded in the one common semantic witness. -/
noncomputable def activeSemanticWitness : Machine.CoreShardSemanticWitness :=
  Machine.CoreShardSemanticWitness.ofOrdinaryTrace anchorProgram ⟨[]⟩ activeExecution

/-- Evaluating the common semantic witness recovers the exact nonempty execution. -/
theorem activeSemanticWitness_trace :
    activeSemanticWitness.trace? (supportedCoreShardModel (p := SP1Prime)) =
      some activeExecution := by
  exact Machine.CoreShardSemanticWitness.trace?_ofOrdinaryTrace
    (supportedCoreShardModel (p := SP1Prime)) anchorProgram ⟨[]⟩ activeExecution
    activeExecution_valid activeExecution_allOrdinary

/-- The committed program is representable by the canonical native encoder. -/
theorem anchorProgram_encodable : Commit.Encodable anchorProgram :=
  anchorData_canonicalEncoding.encodable_progOf anchorData

@[simp] theorem activeSemanticWitness_evaluatedTrace :
    activeSemanticWitness.evaluatedTrace (supportedCoreShardModel (p := SP1Prime)) =
      activeExecution :=
  Machine.CoreShardSemanticWitness.evaluatedTrace_eq_of_trace? activeSemanticWitness_trace

/-- The active semantic source is a genuine member of the shared supported-shard language. -/
theorem activeExecution_semantic :
    SupportedCoreShardExecutionRelation activeStatement activeSemanticWitness where
  statementValid := activeTrace_wellFormed.boundary
  programWellFormed := anchorProgram_wellFormed
  programBound := rfl
  programValid := anchorProgram_encodable
  contractValid := trivial
  romLoaded := anchorState_romLoaded
  configured := anchorState_configured
  codeMemoryCompatible := anchor_codeMemoryCompatible
  memoryWellFormed := ⟨List.nodup_nil,
    fun cell member => absurd member List.not_mem_nil⟩
  memoryAgrees := fun cell member => absurd member List.not_mem_nil
  shardCase := by
    refine .execution [.ordinary] activeExecution rfl rfl activeSemanticWitness_trace
      activeExecution_valid ?_ ?_ ?_ ?_ ?_
    · trivial
    · rfl
    · change anchorState.regs.get? Register.PC = some 65536#64
      exact anchorState_pc
    · change activeTarget.regs.get? Register.PC = some 65536#64
      simpa only [jalView_sndPc] using activeTarget_effect.pc
    · exact ⟨activeExecution_allOrdinary, activeExecution_supported,
        by simp [CoreProfile.WithinOrdinaryRowLimit]⟩

/-- The circuit-built active witness also lies inside the shared bounded native relation. -/
theorem activeTrace_boundedNativeRelation :
    SupportedCoreNativeShardRelation activeStatement activeTrace.witness :=
  ⟨activeTrace_nativeRelation, by
    change CoreProfile.WithinOrdinaryRowLimit
      (realDecodedInstructionRows activeTrace.witness.data activeTrace.witness.tables).length
    rw [active_real_decoded_instruction_row_count]
    simp [CoreProfile.WithinOrdinaryRowLimit]⟩

/-- Bounded native soundness reconstructs the same shared semantic language from a genuinely
active circuit-built witness.  Together with `activeExecution_semantic` and the compiler checks
above, this rules out vacuity on both sides of the functional-correctness boundary. -/
theorem activeTrace_bounded_roundTrip :
    ∃ witness, SupportedCoreShardExecutionRelation activeStatement witness :=
  supported_core_native_shard_sound activeStatement activeTrace.witness
    activeTrace_boundedNativeRelation

end SP1Clean.Audit.ActiveNativeCompleteness
