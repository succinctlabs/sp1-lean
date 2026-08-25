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
open SP1Clean.Execution

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
    obtain ⟨⟨semantic, -⟩, ready, fits⟩ := valid
    have constraints := ready.constraints semantic.publicValuesWellFormed
    have balanced := ready.balancedChannels semantic.publicValuesWellFormed fits
    exact ⟨⟨nativeTrace_witness_publicInput statement execution, constraints, balanced⟩,
      ready.semanticBoundary semantic⟩

/-- Capacity-aligned functional completeness.

The witness constructor is the same `nativeTrace`; the additional target fact follows from the
shared semantic row budget and the proved one-active-row-per-transition equation.  Thus the paired
soundness/completeness API uses `SupportedCoreNativeShardRelation` on the AIR side without defining
a second compiler or trace. -/
noncomputable def supported_core_native_shard_functionalCompleteness
    (handler : Machine.SyscallHandler) :
    WitnessRelation.FunctionalCompleteness (SupportedCoreNativeShardRelation (p := p))
      (SupportedCoreNativeAdmissibleExecutionRelation (p := p) handler) :=
  (supported_core_native_functionalCompleteness (p := p) handler).restrictAir
    (fun _ witness => CoreProfile.WithinOrdinaryRowLimit
      (realDecodedInstructionRows witness.data witness.tables).length) (by
    intro statement execution valid
    obtain ⟨⟨semantic, limit⟩, ready, -⟩ := valid
    change
      CoreProfile.WithinOrdinaryRowLimit
        (realDecodedInstructionRows (nativeTrace statement execution).witness.data
          (nativeTrace statement execution).witness.tables).length
    rw [ready.activeInstructionRows_length semantic.publicValuesWellFormed]
    exact limit)

/-- Existential form of deterministic whole-ensemble completeness. -/
theorem supported_core_native_complete (handler : Machine.SyscallHandler) :
    WitnessRelation.Complete (SupportedCoreNativeRelation (p := p))
      (SupportedCoreNativeAdmissibleExecutionRelation (p := p) handler) :=
  (supported_core_native_functionalCompleteness (p := p) handler).complete

/-- Existential projection of capacity-aligned native completeness. -/
theorem supported_core_native_shard_complete (handler : Machine.SyscallHandler) :
    WitnessRelation.Complete (SupportedCoreNativeShardRelation (p := p))
      (SupportedCoreNativeAdmissibleExecutionRelation (p := p) handler) :=
  (supported_core_native_shard_functionalCompleteness (p := p) handler).complete

/-- Bidirectional correctness on the one shared bounded shard relation, conditional only on the
transparent compiler-domain closure theorem.  The unqualified correctness name remains reserved
until `NativeTraceTotalOnSupportedCore` is proved. -/
theorem supported_core_native_shard_correct_of_totality
    (handler : Machine.SyscallHandler)
    (total : NativeTraceTotalOnSupportedCore (p := p) handler) :
    WitnessRelation.Correct (SupportedCoreNativeShardRelation (p := p))
      (Execution.SupportedCoreOrdinaryShardExecutionRelation handler) where
  sound := supported_core_native_shard_sound handler
  complete := by
    intro statement execution semantic
    exact supported_core_native_shard_complete handler statement execution
      ⟨semantic, total statement execution semantic⟩

/-- Public-language equality is now a direct consequence of the same single totality theorem. -/
theorem supported_core_native_shard_language_eq_of_totality
    (handler : Machine.SyscallHandler)
    (total : NativeTraceTotalOnSupportedCore (p := p) handler) :
    WitnessRelation.language (SupportedCoreNativeShardRelation (p := p)) =
      WitnessRelation.language (Execution.SupportedCoreOrdinaryShardExecutionRelation handler) :=
  (supported_core_native_shard_correct_of_totality handler total).language_eq

/-- A supported admissible execution proves the literal Clean `Ensemble.Statement` at the
statement's public boundary. -/
theorem sp1Ensemble_statement_of_supported_execution
    (handler : Machine.SyscallHandler) (statement : SupportedCoreStatement p)
    (execution : Machine.EventExecutionTrace)
    (valid : SupportedCoreNativeAdmissibleExecutionRelation handler statement execution) :
    (sp1Ensemble (p := p)).Statement statement.publicValues := by
  obtain ⟨⟨semantic, -⟩, ready, fits⟩ := valid
  exact ⟨(nativeTrace statement execution).witness,
    nativeTrace_witness_publicInput statement execution,
    ready.constraints semantic.publicValuesWellFormed,
    ready.balancedChannels semantic.publicValuesWellFormed fits⟩

end SP1Clean.Soundness
