import SP1Clean.Proofs.Completeness.NativeMemoryAgreement
import SP1Clean.Proofs.Completeness.NativeProgramAgreement

/-!
# Native compiler agreement with the semantic boundary

Program and Memory each prove their provider bindings in their own agreement modules.  This module
is the sole join point: it combines those independent bus facts with the exact ordinary execution's
initial state and public endpoints to construct `SemanticBoundaryBinding`.

Keeping the join outside either bus-specific module makes the separation explicit and gives the
native completeness capstone one direct semantic-boundary dependency.
-/

namespace SP1Clean.Soundness

open SP1Clean.Execution

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance nativeBoundaryAgreementFieldBound : Fact (2 ^ 24 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- The exact semantic relation supplies the ordinary initial state and program facts; the Program
and Memory agreement layers derive the two canonical provider bindings rather than storing them as
opaque readiness fields. -/
theorem NativeTraceReady.semanticBoundary
    {statement : SupportedCoreStatement p}
    {semanticWitness : Machine.CoreShardSemanticWitness}
    (ready : NativeTraceReady statement
      (semanticWitness.evaluatedTrace (supportedCoreShardModel (p := p))))
    (semantic : SupportedCoreShardExecutionRelation statement semanticWitness) :
    SemanticBoundaryBinding statement
      (nativeTrace statement
        (semanticWitness.evaluatedTrace (supportedCoreShardModel (p := p)))).witness := by
  let execution := semanticWitness.evaluatedTrace (supportedCoreShardModel (p := p))
  have publicWellFormed :=
    Execution.SupportedCoreShardExecutionValid.publicValuesWellFormed semantic
  have programEq := Execution.SupportedCoreShardExecutionValid.program_eq semantic
  have programWellFormed : statement.program.WellFormed := by
    simpa only [programEq] using semantic.programWellFormed
  have programEncodable : Commit.Encodable statement.program := by
    simpa only [programEq] using
      Execution.SupportedCoreShardExecutionValid.programEncodable semantic
  obtain ⟨-, -, -, initialPc, -, -, -, -⟩ :=
    Execution.SupportedCoreShardExecutionValid.evaluatedTrace_facts semantic
  have clockEncodable := nativeInitialClock_encodable statement publicWellFormed
  have programProvider := nativeTrace_programProviderBound semantic rfl ready.compiler
    ready.demandServable ready.programProjection
  refine InitialBoundaryFacts.binding (initial := semanticWitness.initialState) {
    programWellFormed := programWellFormed
    programCommitted := ?_
    initialPc := ?_
    initialClock := ?_
    romLoaded := ?_
    configured := semantic.configured
    codeMemoryCompatible := ?_
    programProvider := programProvider
    memoryProvider := ?_
    memoryProviderUnique := nativeTrace_memoryInitProviderUnique statement execution
      ready.memoryAddresses
    memoryFinalizeProviderUnique := nativeTrace_memoryFinalizeProviderUnique statement execution
      ready.memoryAddresses }
  · change Commit.StatementFor
      (Commit.dataOfAt statement.program (nativeInitialClock statement)) statement.program
    exact Commit.dataOfAt_statementFor (p := p) statement.program (nativeInitialClock statement)
      programWellFormed programEncodable clockEncodable
  · simpa only [execution, Machine.CoreShardSemanticWitness.evaluatedTrace_initialState,
      supportedCoreShardBoundary]
      using initialPc
  · change Commit.initClkNat
      (Commit.dataOfAt statement.program (nativeInitialClock statement)) =
        nativeInitialClock statement
    exact Commit.initClkNat_dataOfAt statement.program (nativeInitialClock statement)
      clockEncodable
  · simpa only [programEq] using semantic.romLoaded
  · rw [← programEq]
    exact semantic.codeMemoryCompatible
  · simpa only [nativeTrace, nativeBaseTrace, nativeBaseTraceOfCompiled,
      SupportedCoreTraceWitness.canonicalClosure_data,
      SupportedCoreTraceWitness.witness_data,
      Commit.initClkNat_dataOfAt statement.program (nativeInitialClock statement)
        clockEncodable, execution,
      Machine.CoreShardSemanticWitness.evaluatedTrace_initialState] using
        ready.memoryProviderBound

end SP1Clean.Soundness
