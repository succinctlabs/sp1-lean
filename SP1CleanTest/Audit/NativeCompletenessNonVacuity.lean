import SP1Clean.Soundness.NativeCompleteness
import SP1Clean.Proofs.Completeness.NativeMemoryAgreement
import SP1Clean.Proofs.Completeness.NativeProgramAgreement
import SP1CleanTest.Audit.TraceNonVacuity

/-!
# Non-vacuity of deterministic native completeness

The deterministic native compiler is exercised on the smallest honest semantic shard: the
boundary-only execution at the concrete audit program and state.  Unlike the existing generated
trace anchor, this witness starts from `Machine.EventExecutionTrace`, runs through `nativeTrace`,
and therefore checks that the admissible-execution relation used by native completeness is jointly
satisfiable.
-/

open LeanRV64D.Defs

namespace SP1Clean.Audit.NativeCompletenessNonVacuity

open Air.Flat Circuit
open SP1Clean SP1Clean.Execution SP1Clean.Soundness SP1Clean.TraceGen
open SP1Clean.LookupAccessList
open SP1Clean.TraceGenTests
open SP1Clean.Audit.JointNonVacuity
open SP1Clean.Audit.TraceNonVacuity
open SP1Clean.Channels (stateChannel byteChannel programChannel memoryChannel)

/-- No syscall transition occurs in the boundary-only execution, so the handler is immaterial. -/
def anchorHandler : Machine.SyscallHandler := fun _ _ _ _ => False

/-- The proof-free, zero-transition semantic execution at the shared audit state. -/
noncomputable def anchorExecution : Machine.EventExecutionTrace where
  initialState := anchorState
  transitions := []

@[simp] theorem anchorExecution_initialState : anchorExecution.initialState = anchorState := rfl

@[simp] theorem anchorExecution_transitions : anchorExecution.transitions = [] := rfl

@[simp] theorem anchorExecution_locatedTransitions : anchorExecution.locatedTransitions = [] := rfl

@[simp] theorem anchorExecution_steps : anchorExecution.steps = 0 := rfl

@[simp] theorem anchorExecution_finalState : anchorExecution.finalState = anchorState := rfl

@[simp] theorem anchorExecution_finalClock (clock : ℕ) :
    anchorExecution.finalClock clock = clock := rfl

/-- The equal-endpoint public boundary satisfies the verifier's complete limb contract. -/
theorem pv_limbBounds : pv.LimbBounds := by
  rw [← anchorTrace_publicValues]
  exact anchorTrace_wellFormed.boundary

/-- The shared committed audit program is representable by the canonical native encoder. -/
theorem anchorProgram_encodable : Commit.Encodable anchorProgram :=
  anchorData_canonicalEncoding.encodable_progOf anchorData

/-- The boundary-only execution is an exact supported ordinary shard.  Transition-local fields
are vacuous; the non-vacuous content is the committed program and configured/ROM-loaded initial
Sail state inherited from the joint audit anchor. -/
theorem anchorExecution_semantic :
    SupportedOrdinaryShardExecutionRelation anchorHandler stmt anchorExecution where
  publicValuesWellFormed := pv_limbBounds
  programWellFormed := anchorProgram_wellFormed
  programEncodable := anchorProgram_encodable
  romLoaded := anchorState_romLoaded
  configured := anchorState_configured
  codeMemoryCompatible := anchor_codeMemoryCompatible
  segment := by
    refine ⟨Machine.EventTransitionsValid.nil anchorState, trivial, ?_, ?_, ?_⟩
    · simpa only [anchorExecution, stmt] using anchorBoundaryFacts.initialPc
    · change anchorState.regs.get? Register.PC =
        some (supportedPcBits (0 : ZMod SP1Prime) 1 0)
      rw [supportedPcBits_anchor]
      exact anchorState_pc
    · rfl
  allOrdinary := by
    intro transition member
    exact absurd member List.not_mem_nil
  supported := by
    intro located member
    exact absurd member List.not_mem_nil

/-- The zero-step shard is strictly inside the pinned Core row budget. -/
theorem anchorExecution_withinCoreRowLimit :
    CoreProfile.WithinOrdinaryRowLimit anchorExecution.steps := by
  simp [CoreProfile.WithinOrdinaryRowLimit]

/-- The optional compiler succeeds definitionally on the empty chronological transition list. -/
theorem anchorExecution_compileExecution?_eq :
    compileExecution? anchorProgram anchorExecution (nativeInitialClock stmt) =
      some (emptyCompiledExecution (nativeInitialClock stmt)) := rfl

/-- The total compiler therefore has the literal empty compiler result. -/
theorem anchorExecution_compileExecution_eq :
    compileExecution anchorProgram anchorExecution (nativeInitialClock stmt) =
      emptyCompiledExecution (nativeInitialClock stmt) := by
  exact compileExecution_eq_of_some anchorExecution_compileExecution?_eq

/-- Empty instruction and refresh buckets satisfy the compiler's local well-formedness contract. -/
theorem emptyCompiledExecution_wellFormed (clock : ℕ) :
    (emptyCompiledExecution clock).WellFormed := by
  constructor
  · intro id event member
    simp [emptyCompiledExecution, CompiledExecution.instructionEvents,
      EventBuckets.ofChronological] at member
  · intro event member
    simp [emptyCompiledExecution, CompiledExecution.memoryBumps] at member

/-- Concrete success and local correctness of the deterministic compiler. -/
theorem anchorExecution_compilerReady :
    NativeCompilerReady anchorProgram anchorExecution (nativeInitialClock stmt) :=
  ⟨emptyCompiledExecution (nativeInitialClock stmt), anchorExecution_compileExecution?_eq,
    emptyCompiledExecution_wellFormed _⟩

/-! ## Field-free readiness on the empty compiler stream -/

theorem anchor_nativeInitialClock : nativeInitialClock stmt = 1 := by native_decide

theorem anchor_nativeFinalClock : nativeFinalClock stmt = 1 := by native_decide

theorem anchor_nativeInitialPc : nativeInitialPc stmt = 65536 := by native_decide

theorem anchor_nativeFinalPc : nativeFinalPc stmt = 65536 := by native_decide

theorem anchor_nativeStateBoundary_initial_eq_final :
    (nativeStateBoundary stmt).initial = (nativeStateBoundary stmt).final := by
  simp only [nativeStateBoundary, anchor_nativeInitialClock, anchor_nativeInitialPc,
    anchor_nativeFinalClock, anchor_nativeFinalPc]
  rfl

theorem anchorExecution_routedEvents_nil :
    (compileExecution anchorProgram anchorExecution
      (nativeInitialClock stmt)).routedEvents = [] := by
  rw [anchorExecution_compileExecution_eq]
  rfl

theorem anchorExecution_memoryHistory_nil :
    (compileExecution anchorProgram anchorExecution
      (nativeInitialClock stmt)).memoryHistory = [] := by
  rw [anchorExecution_compileExecution_eq]
  rfl

theorem anchorExecution_stateBumpsReady :
    StateBumpReady
      (compileExecution anchorProgram anchorExecution
        (nativeInitialClock stmt)).routedEvents := by
  rw [anchorExecution_routedEvents_nil]
  intro routed member
  exact absurd member List.not_mem_nil

theorem anchorExecution_stateChronology :
    StateChronology (nativeStateBoundary stmt).initial
      (compileExecution anchorProgram anchorExecution
        (nativeInitialClock stmt)).routedEvents
      (nativeStateBoundary stmt).final := by
  rw [anchorExecution_routedEvents_nil]
  exact anchor_nativeStateBoundary_initial_eq_final

theorem anchorBase_instructionTable_table_nil (id : InstructionChipId) :
    ((nativeBaseTraceOfCompiled stmt
      (emptyCompiledExecution (nativeInitialClock stmt))).instructionTableFor id).table = [] := by
  cases id <;> rfl

theorem anchorExecution_stateProjection :
    NativeStateRowProjection stmt anchorExecution := by
  unfold NativeStateRowProjection
  have compiledEq :
      compileExecution stmt.program anchorExecution (nativeInitialClock stmt) =
        emptyCompiledExecution (nativeInitialClock stmt) := by
    simpa only [stmt] using anchorExecution_compileExecution_eq
  unfold nativeBaseTrace
  rw [compiledEq]
  have instructionLinksNil :
      stateInstrLinks
          (nativeBaseTraceOfCompiled stmt
            (emptyCompiledExecution (nativeInitialClock stmt))) = [] := by
    rw [SupportedCoreTraceWitness.stateInstrLinks_eq_flatMap]
    apply List.flatMap_eq_nil_iff.mpr
    intro id _
    unfold SupportedCoreTraceWitness.instructionStateLinksFor
    rw [anchorBase_instructionTable_table_nil]
    rfl
  rw [instructionLinksNil]
  rfl

theorem anchorExecution_memoryAddresses :
    MemoryAddressesCanonical
      (compileExecution anchorProgram anchorExecution
        (nativeInitialClock stmt)).memoryHistory := by
  rw [anchorExecution_memoryHistory_nil]
  intro access member
  exact absurd member List.not_mem_nil

theorem anchorExecution_memoryChronology :
    MemoryRecordChronology
      (compileExecution anchorProgram anchorExecution
        (nativeInitialClock stmt)).memoryHistory := by
  rw [anchorExecution_memoryHistory_nil]
  intro history member
  exact absurd member List.not_mem_nil

/-- A fully executable presentation of the empty compiler skeleton.  Its preprocessed occurrence
lists are deliberately empty because `skeletonLedger` omits that provider window. -/
def concreteBaseTrace : SupportedCoreTraceWitness SP1Prime where
  instructionEvents := fun _ => []
  providerOccurrences := fun _ => []
  data := anchorData
  hint := ProverHint.empty _
  boundary := pv

theorem anchorProgram_pc_start : anchorProgram.pc_start = 65536#64 := by native_decide

theorem anchorData_eq_nativeData :
    Commit.dataOfAt anchorProgram (nativeInitialClock stmt) = anchorData := by
  rw [anchor_nativeInitialClock]
  funext key arity
  simp only [Commit.dataOfAt, anchorData]
  split <;> simp_all [anchorProgram_rom, anchorProgram_memImage, anchorProgram_pc_start,
    Commit.romRowOf, Commit.pcStartRowOf, Commit.initClockRowOf]

theorem anchorExecution_nativeBaseTrace_eq :
    nativeBaseTrace stmt anchorExecution = concreteBaseTrace := by
  unfold nativeBaseTrace
  rw [show compileExecution stmt.program anchorExecution (nativeInitialClock stmt) =
      emptyCompiledExecution (nativeInitialClock stmt) by
    simpa only [stmt] using anchorExecution_compileExecution_eq]
  unfold nativeBaseTraceOfCompiled concreteBaseTrace nativeBaseProviderOccurrences
  rw [show Commit.dataOfAt stmt.program (nativeInitialClock stmt) = anchorData by
    simpa only [stmt] using anchorData_eq_nativeData]
  congr 1
  · funext id
    cases id <;> rfl

theorem concreteBaseTrace_skeletonLedger :
    concreteBaseTrace.skeletonLedger = anchorTrace.skeletonLedger := by
  rfl

def boundaryClosingKeys : List LookupKey :=
  [(InteractionKind.Byte, "SP1Byte", [3, 0, 0, 0]),
   (InteractionKind.Byte, "SP1Byte", [6, 1, 16, 0]),
   (InteractionKind.Byte, "SP1Byte", [6, 0, 16, 0]),
  ]

theorem concreteBaseTrace_closingKeyList :
    concreteBaseTrace.closingKeyList = boundaryClosingKeys := by
  native_decide

def boundarySkeletonLedger : LookupAccessList :=
  [(InteractionKind.State, "SP1State", [0, 1, 0, 1, 0], -1),
   (InteractionKind.State, "SP1State", [0, 1, 0, 1, 0], 1),
   (InteractionKind.Byte, "SP1Byte", [6, 1, 16, 0], -1),
   (InteractionKind.Byte, "SP1Byte", [6, 0, 16, 0], -1),
   (InteractionKind.Byte, "SP1Byte", [3, 0, 0, 0], -1),
   (InteractionKind.Byte, "SP1Byte", [6, 0, 16, 0], -1),
   (InteractionKind.Byte, "SP1Byte", [6, 1, 16, 0], -1),
   (InteractionKind.Byte, "SP1Byte", [6, 0, 16, 0], -1),
   (InteractionKind.Byte, "SP1Byte", [6, 1, 16, 0], -1),
   (InteractionKind.Byte, "SP1Byte", [6, 0, 16, 0], -1),
   (InteractionKind.Byte, "SP1Byte", [3, 0, 0, 0], -1),
   (InteractionKind.Byte, "SP1Byte", [6, 0, 16, 0], -1),
   (InteractionKind.Byte, "SP1Byte", [6, 1, 16, 0], -1),
   (InteractionKind.Byte, "SP1Byte", [6, 0, 16, 0], -1)]

theorem concreteBaseTrace_skeletonLedger_eq :
    concreteBaseTrace.skeletonLedger = boundarySkeletonLedger := by
  native_decide

theorem anchorExecution_byteConsumers :
    (nativeBaseTrace stmt anchorExecution).ByteConsumersOnlyPull := by
  rw [anchorExecution_nativeBaseTrace_eq]
  intro access member byte
  rw [concreteBaseTrace_skeletonLedger_eq] at member
  simp only [boundarySkeletonLedger, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;> simp [multOf] at byte ⊢

theorem anchorExecution_demandServable :
    (nativeBaseTrace stmt anchorExecution).DemandServable := by
  rw [anchorExecution_nativeBaseTrace_eq]
  constructor
  · intro key member _
    rw [concreteBaseTrace_closingKeyList] at member
    fin_cases member <;> norm_num [IsByteKey, ByteServable, cell]
  · intro key member program
    rw [concreteBaseTrace_closingKeyList] at member
    fin_cases member <;> simp at program

theorem anchorExecution_programProjection :
    NativeProgramRowProjection stmt anchorExecution := by
  intro key member program
  rw [anchorExecution_nativeBaseTrace_eq, concreteBaseTrace_closingKeyList] at member
  fin_cases member <;> simp at program

private theorem decodeInstructionTables_nil_of_tables_nil :
    ∀ (chips : List (SupportedChip SP1Prime)) (tables : List (Table (ZMod SP1Prime))),
      (∀ table ∈ tables, table.table = []) → decodeInstructionTables chips tables = [] := by
  intro chips
  induction chips with
  | nil =>
      intro tables _
      cases tables <;> rfl
  | cons chip chips ih =>
      intro tables empty
      cases tables with
      | nil => rfl
      | cons table tables =>
          rw [decodeInstructionTables, empty table (by simp)]
          simp only [List.map_nil, List.nil_append]
          apply ih tables
          intro tail member
          exact empty tail (by simp [member])

theorem concreteBase_instructionTable_table_nil (id : InstructionChipId) :
    (concreteBaseTrace.instructionTableFor id).table = [] := by
  cases id <;> rfl

theorem concreteBaseTrace_decodedInstructionRows_nil :
    decodedInstructionRows (p := SP1Prime) concreteBaseTrace.tables = [] := by
  unfold decodedInstructionRows
  change decodeInstructionTables supportedChips
    (concreteBaseTrace.tables.take instructionTableCount) = []
  rw [SupportedCoreTraceWitness.tables_take_instructionTables]
  apply decodeInstructionTables_nil_of_tables_nil
  intro table member
  rw [SupportedCoreTraceWitness.instructionTables] at member
  obtain ⟨id, _, rfl⟩ := List.mem_map.mp member
  exact concreteBase_instructionTable_table_nil id

theorem anchorExecution_nativeTrace_decodedInstructionRows_nil :
    decodedInstructionRows (p := SP1Prime)
      (nativeTrace stmt anchorExecution).witness.tables = [] := by
  rw [SupportedCoreTraceWitness.witness_tables]
  unfold nativeTrace
  rw [SupportedCoreTraceWitness.canonicalClosure_decodedInstructionRows,
    anchorExecution_nativeBaseTrace_eq]
  exact concreteBaseTrace_decodedInstructionRows_nil

theorem anchorExecution_memoryBumpTable_table_nil :
    (memoryBumpTable (nativeTrace stmt anchorExecution).witness).table = [] := by
  unfold nativeTrace nativeBaseTrace memoryBumpTable
  rw [show compileExecution stmt.program anchorExecution (nativeInitialClock stmt) =
      emptyCompiledExecution (nativeInitialClock stmt) by
    simpa only [stmt] using anchorExecution_compileExecution_eq]
  rfl

theorem anchorExecution_memoryProjection :
    NativeMemoryRowProjection stmt anchorExecution := by
  constructor
  · unfold physicalInstructionMemoryLedger
    rw [anchorExecution_nativeTrace_decodedInstructionRows_nil]
    rw [show compileExecution stmt.program anchorExecution (nativeInitialClock stmt) =
        emptyCompiledExecution (nativeInitialClock stmt) by
      simpa only [stmt] using anchorExecution_compileExecution_eq]
    rfl
  · unfold physicalMemoryBumpLedger typedTableInteractionsWith
    rw [anchorExecution_memoryBumpTable_table_nil]
    rw [show compileExecution stmt.program anchorExecution (nativeInitialClock stmt) =
        emptyCompiledExecution (nativeInitialClock stmt) by
      simpa only [stmt] using anchorExecution_compileExecution_eq]
    rfl

theorem anchorExecution_memoryGenesis :
    NativeMemoryGenesis anchorExecution.initialState
      (compileExecution anchorProgram anchorExecution
        (nativeInitialClock stmt)).memoryHistory := by
  rw [anchorExecution_memoryHistory_nil]
  intro history member
  exact absurd member List.not_mem_nil

/-! ## Exact finite footprint -/

/-- The canonical zero-step closure has two State interactions, twelve verifier Byte pulls, and
three aggregate Byte-provider pushes. -/
theorem anchorExecution_nativeTrace_interactions_length :
    (nativeTrace stmt anchorExecution).witness.interactions.length = 17 := by
  unfold nativeTrace nativeBaseTrace
  rw [show compileExecution stmt.program anchorExecution (nativeInitialClock stmt) =
      emptyCompiledExecution (nativeInitialClock stmt) by
    simpa only [stmt] using anchorExecution_compileExecution_eq]
  simp only [nativeBaseTraceOfCompiled]
  native_decide

open Classical in
private theorem witness_interactionsWith_length_le
    {F : Type} [FiniteField F] {PublicIO : TypeMap} [ProvableType PublicIO]
    {ensemble : Ensemble F PublicIO} (witness : EnsembleWitness ensemble)
    (channel : RawChannel F) :
    (witness.interactionsWith channel).length ≤ witness.interactions.length := by
  simp only [EnsembleWitness.interactionsWith, EnsembleWitness.interactions]
  induction witness.allTables with
  | nil => simp
  | cons table tables ih =>
      simp only [List.flatMap_cons, List.length_append]
      rw [Table.interactionsWith_eq_filter]
      exact Nat.add_le_add (List.length_filter_le _ _) ih

/-- Actual Clean occurrence capacity for the compiled boundary-only shard. -/
theorem anchorExecution_footprintFits :
    (NativeTraceFootprint.ofTrace (nativeTrace stmt anchorExecution)).Fits SP1Prime := by
  unfold NativeTraceFootprint.Fits NativeTraceFootprint.ofTrace
  have bound (channel : RawChannel (ZMod SP1Prime)) :
      ((nativeTrace stmt anchorExecution).witness.interactionsWith channel).length ≤ 17 := by
    rw [← anchorExecution_nativeTrace_interactions_length]
    exact witness_interactionsWith_length_le _ _
  simp only [Air.Flat.EnsembleWitness.interactionsWith_allTablesWitness]
  constructor
  · exact lt_of_le_of_lt (bound stateChannel.toRaw) (by native_decide)
  constructor
  · exact lt_of_le_of_lt (bound byteChannel.toRaw) (by native_decide)
  constructor
  · exact lt_of_le_of_lt (bound programChannel.toRaw) (by native_decide)
  · exact lt_of_le_of_lt (bound memoryChannel.toRaw) (by native_decide)

/-! ## Joint admissibility and capstone consequences -/

/-- Every readiness field of the deterministic compiler is jointly inhabited on the same honest
semantic execution. -/
theorem anchorExecution_nativeTraceReady : NativeTraceReady stmt anchorExecution where
  compiler := by simpa only [stmt] using anchorExecution_compilerReady
  stateBumps := by simpa only [stmt] using anchorExecution_stateBumpsReady
  stateChronology := by simpa only [stmt] using anchorExecution_stateChronology
  stateProjection := anchorExecution_stateProjection
  memoryAddresses := by simpa only [stmt] using anchorExecution_memoryAddresses
  memoryChronology := by simpa only [stmt] using anchorExecution_memoryChronology
  memoryProjection := anchorExecution_memoryProjection
  byteConsumers := anchorExecution_byteConsumers
  demandServable := anchorExecution_demandServable
  programProjection := anchorExecution_programProjection
  memoryGenesis := by simpa only [stmt] using anchorExecution_memoryGenesis

/-- The completeness theorem's exact source relation is nonempty. -/
theorem anchorExecution_admissible :
    SupportedCoreNativeAdmissibleExecutionRelation anchorHandler stmt anchorExecution :=
  ⟨⟨anchorExecution_semantic, anchorExecution_withinCoreRowLimit⟩,
    anchorExecution_nativeTraceReady, anchorExecution_footprintFits⟩

/-- The capacity-aligned functional capstone validates the compiler's literal 53-table witness in
the same bounded native relation consumed by soundness. -/
theorem anchorExecution_yields_boundedAirWitness :
    SupportedCoreNativeShardRelation stmt (nativeTrace stmt anchorExecution).witness :=
  (supported_core_native_shard_functionalCompleteness anchorHandler).map_valid
    stmt anchorExecution anchorExecution_admissible

/-- Forgetting only the named capacity restriction recovers the original native relation. -/
theorem anchorExecution_yields_airWitness :
    SupportedCoreNativeRelation stmt (nativeTrace stmt anchorExecution).witness :=
  anchorExecution_yields_boundedAirWitness.1

/-- Bounded native soundness returns a witness of the exact same shared semantic relation from that
generated AIR witness.  This exercises both directions without introducing an alternate execution
carrier. -/
theorem anchorExecution_bounded_roundTrip :
    ∃ execution,
      SupportedCoreOrdinaryShardExecutionRelation anchorHandler stmt execution :=
  supported_core_native_shard_sound anchorHandler stmt
    (nativeTrace stmt anchorExecution).witness anchorExecution_yields_boundedAirWitness

/-- The direct Clean statement consequence is therefore non-vacuous at the concrete boundary. -/
theorem anchorExecution_yields_ensembleStatement :
    (sp1Ensemble (p := SP1Prime)).Statement pv := by
  simpa only [stmt] using
    sp1Ensemble_statement_of_supported_execution anchorHandler stmt anchorExecution
      anchorExecution_admissible

end SP1Clean.Audit.NativeCompletenessNonVacuity
