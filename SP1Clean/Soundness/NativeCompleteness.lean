import SP1Clean.Proofs.Completeness.NativeStateAgreement
import SP1Clean.Proofs.Completeness.NativeMemoryAgreement
import SP1Clean.Proofs.Completeness.NativeBoundaryAgreement
import SP1Clean.Soundness.AIRCompleteness

/-!
# Native ensemble completeness

This machine-completeness layer consumes the deterministic trace compiler from the assembly
stratum and closes the last Clean-specific fact: simultaneous balance of all four ensemble
channels.  Keeping it here preserves the architecture's `machine → assembly → machine
completeness` direction; the proof-independent trace map remains available below this capstone.
-/

namespace SP1Clean.Soundness

open SP1Clean.LookupAccessList
open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance nativeCompletenessFieldBound : Fact (2 ^ 24 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- All four Clean channels balance for the deterministic trace.  Byte/Program use direct
field-valued canonical closure; State/Memory use the two structural hand-offs. -/
theorem NativeTraceReady.balancedChannels
    {statement : SupportedCoreStatement p} {execution : Machine.EventExecutionTrace}
    (ready : NativeTraceReady statement execution)
    (publicWellFormed : statement.publicValues.LimbBounds)
    (fits : (NativeTraceFootprint.ofTrace (nativeTrace statement execution)).Fits p) :
    (nativeTrace statement execution).witness.BalancedChannels := by
  let compiled := TraceGen.compileExecution statement.program execution
    (nativeInitialClock statement)
  let stateKeys := chainTokens
    (stateInitToken (nativeTrace statement execution),
      chronologicalStateLinks (p := p) compiled.routedEvents,
      stateFinalToken (nativeTrace statement execution))
  let memoryKeys := (memoryHandoffChains (p := p) compiled.memoryHistory).flatMap chainTokens
  exact (nativeBaseTrace statement execution).canonicalClosure_balancedChannels_of_handoff
    (ready.wellFormed publicWellFormed) ready.demandServable
    (ready.skeletonNonpositive publicWellFormed) stateKeys memoryKeys
    (ready.stateLedgerPerm publicWellFormed) ready.memoryLedgerPerm
    (NativeTraceFootprint.interactionLengths fits)

/-- Functional completeness of the native ensemble on its exact deterministic compiler image.
The witness map is independent of the proof of admissibility. -/
noncomputable def supported_core_native_functionalCompleteness
    (handler : Machine.SyscallHandler) :
    WitnessRelation.FunctionalCompleteness (SupportedCoreNativeRelation (p := p))
      (SupportedCoreNativeAdmissibleExecutionRelation (p := p) handler) where
  map statement execution := (nativeTrace statement execution).witness
  map_valid statement execution valid := by
    obtain ⟨semantic, -, ready, fits⟩ := valid
    have constraints := ready.constraints semantic.publicValuesWellFormed
    have balanced := ready.balancedChannels semantic.publicValuesWellFormed fits
    exact ⟨⟨nativeTrace_witness_publicInput statement execution, constraints, balanced⟩,
      ready.semanticBoundary semantic⟩

/-- Existential form of deterministic whole-ensemble completeness. -/
theorem supported_core_native_complete (handler : Machine.SyscallHandler) :
    WitnessRelation.Complete (SupportedCoreNativeRelation (p := p))
      (SupportedCoreNativeAdmissibleExecutionRelation (p := p) handler) :=
  (supported_core_native_functionalCompleteness (p := p) handler).complete

/-- A supported admissible execution proves the literal Clean `Ensemble.Statement` at the
statement's public boundary. -/
theorem sp1Ensemble_statement_of_supported_execution
    (handler : Machine.SyscallHandler) (statement : SupportedCoreStatement p)
    (execution : Machine.EventExecutionTrace)
    (valid : SupportedCoreNativeAdmissibleExecutionRelation handler statement execution) :
    (sp1Ensemble (p := p)).Statement statement.publicValues := by
  obtain ⟨semantic, -, ready, fits⟩ := valid
  exact ⟨(nativeTrace statement execution).witness,
    nativeTrace_witness_publicInput statement execution,
    ready.constraints semantic.publicValuesWellFormed,
    ready.balancedChannels semantic.publicValuesWellFormed fits⟩

end SP1Clean.Soundness
