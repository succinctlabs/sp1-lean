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
    {handler : Machine.SyscallHandler} {statement : SupportedCoreStatement p}
    {execution : Machine.EventExecutionTrace}
    (ready : NativeTraceReady statement execution)
    (semantic : SupportedOrdinaryShardExecutionRelation handler statement execution) :
    SemanticBoundaryBinding statement (nativeTrace statement execution).witness := by
  have clockEncodable := nativeInitialClock_encodable statement
    semantic.publicValuesWellFormed
  have programProvider := nativeTrace_programProviderBound semantic ready.compiler
    ready.demandServable ready.programProjection ready.decodeStable
  refine ⟨execution.initialState, {
    programWellFormed := semantic.programWellFormed
    programCommitted := ?_
    initialPc := semantic.segment.2.2.1
    initialClock := ?_
    romLoaded := semantic.romLoaded
    configured := semantic.configured
    codeMemoryCompatible := semantic.codeMemoryCompatible
    programProvider := programProvider
    memoryProvider := ?_
    memoryProviderUnique := nativeTrace_memoryInitProviderUnique statement execution
      ready.memoryAddresses
    memoryFinalizeProviderUnique := nativeTrace_memoryFinalizeProviderUnique statement execution
      ready.memoryAddresses }⟩
  · change Commit.StatementFor
      (Commit.dataOfAt statement.program (nativeInitialClock statement)) statement.program
    exact Commit.dataOfAt_statementFor (p := p) statement.program (nativeInitialClock statement)
      semantic.programWellFormed semantic.programEncodable clockEncodable
  · change Commit.initClkNat
      (Commit.dataOfAt statement.program (nativeInitialClock statement)) =
        nativeInitialClock statement
    exact Commit.initClkNat_dataOfAt statement.program (nativeInitialClock statement)
      clockEncodable
  · simpa only [nativeTrace, nativeBaseTrace, nativeBaseTraceOfCompiled,
      SupportedCoreTraceWitness.canonicalClosure_data,
      SupportedCoreTraceWitness.witness_data,
      Commit.initClkNat_dataOfAt statement.program (nativeInitialClock statement)
        clockEncodable] using ready.memoryProviderBound

end SP1Clean.Soundness
