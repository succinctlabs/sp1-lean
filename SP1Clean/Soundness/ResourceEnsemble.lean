import SP1Clean.Native.Operations.ResourceBoundary
import SP1Clean.FormalModel.ShardResources
import SP1Clean.Soundness.HostHintReadExecutionPath

/-! # Enforced endpoint resources for the installed mixed assembly

The public resource circuit is installed above the existing source-hint assembly. Projection
retains all physical tables and every ledger occurrence, so all earlier grounding and endpoint
theorems remain available. The new clock check bounds actual elapsed work and, for the native
preset, actual event count. Arbitrarily tighter event limits need a separate event inventory check.

Endpoint occupancy here concerns the supplied snapshots. Authenticating the complete outgoing
snapshot and intermediate peaks remains A4; WRITE/VERIFY and their request/allocation ledgers
remain A5. This intermediate assembly does not instantiate the full Shard soundness target.
-/

namespace SP1Clean.Soundness.ResourceEnsemble
open Circuit Air.Flat Model.Core Machine Semantics

variable {p : ℕ} [Fact p.Prime]

/-- Add resource assertions on a fresh channel while retaining the original tables and ledgers. -/
def install (limits : ResourceLimits) (source target : ExecutionSnapshot)
    (base : Ensemble (ZMod p) SP1PublicIO) : Ensemble (ZMod p) SP1PublicIO :=
  (ResourceBoundary.checker limits source target).install base

/-- Raw acceptance changes by exactly the necessary endpoint checks, in both directions. -/
theorem statement_iff [Fact (2 ^ 25 < p)] (limits : ResourceLimits) (source target : ExecutionSnapshot)
    (base : Ensemble (ZMod p) SP1PublicIO) (input : SP1PublicIO (ZMod p)) :
    (install limits source target base).Statement input ↔
      base.Statement input ∧ ResourceBoundary.Spec limits source target input :=
  (ResourceBoundary.checker limits source target).statement_iff base
    (ResourceBoundary.count_bound limits source target)
    (ResourceBoundary.Spec limits source target) (ResourceBoundary.checks_iff limits source target) input

/-- Completeness can add the resource circuit using only the semantic domain and header encoding. -/
theorem checks_of_admissible {limits : ResourceLimits} {image : ProgramImage}
    {source target : ExecutionSnapshot} {events : List ExecutionEvent} {input : SP1PublicIO (ZMod p)}
    (execution : FormalModel.Shard.AdmissibleExecution limits p image source target events)
    (clock : ResourceBoundary.ClockFor target input) (data : ProverData (ZMod p)) :
    (ResourceBoundary.checker limits source target).Checks input data :=
  (ResourceBoundary.checks_iff ..).mpr ⟨execution.boundaryBounds, clock⟩

variable [Fact (2 ^ 25 < p)]
local instance resourceClockBound : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- The current six-call assembly with actual endpoint-resource enforcement. -/
def ensemble (limits : ResourceLimits) (image : ProgramImage) (source target : ExecutionSnapshot)
    (final : HostHintQueue.State (ZMod p)) (bankFinal : HostState) (channels : List (RawChannel (ZMod p))) :
    Ensemble (ZMod p) SP1PublicIO :=
  install limits source target (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
    (HostHintReadLocal.sourceResources source.host.io.hints) channels
      (HostHintReadLocal.source_unique_names image source source.host.io.hints))

/-- A derived proof view retains every table of the original installed assembly. -/
def baseWitness {limits : ResourceLimits} {image : ProgramImage}
    {source target : ExecutionSnapshot} {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState}
    {channels : List (RawChannel (ZMod p))}
    (witness : EnsembleWitness (ensemble limits image source target final bankFinal channels)) :
    EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (HostHintReadLocal.sourceResources source.host.io.hints) channels
      (HostHintReadLocal.source_unique_names image source source.host.io.hints)) :=
  (ResourceBoundary.checker limits source target).project witness

/-- Original constraints remain available without unfolding the resource verifier at consumers. -/
theorem baseWitness_constraints {limits : ResourceLimits} {image : ProgramImage}
    {source target : ExecutionSnapshot} {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState}
    {channels : List (RawChannel (ZMod p))}
    (witness : EnsembleWitness (ensemble limits image source target final bankFinal channels))
    (constraints : witness.Constraints) : (baseWitness witness).Constraints :=
  ((ResourceBoundary.checker limits source target).project_constraints witness).mp constraints

/-- Original balances retain exactly their physical occurrence counts. -/
theorem baseWitness_balanced {limits : ResourceLimits} {image : ProgramImage}
    {source target : ExecutionSnapshot} {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState}
    {channels : List (RawChannel (ZMod p))}
    (witness : EnsembleWitness (ensemble limits image source target final bankFinal channels))
    (balanced : witness.BalancedChannels) : (baseWitness witness).BalancedChannels :=
  (((ResourceBoundary.checker limits source target).project_balanced_iff witness).mp balanced).1

/-- The actual added raw assertions establish the endpoint resource contract. -/
theorem resource_spec {limits : ResourceLimits} {image : ProgramImage}
    {source target : ExecutionSnapshot} {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState}
    {channels : List (RawChannel (ZMod p))}
    (witness : EnsembleWitness (ensemble limits image source target final bankFinal channels))
    (balanced : witness.BalancedChannels) : ResourceBoundary.Spec limits source target witness.publicInput :=
  (ResourceBoundary.checks_iff ..).mp
    (((ResourceBoundary.checker limits source target).project_balanced_iff witness).mp balanced).2.2

/-- The proof view leaves the public input unchanged. -/
@[simp] theorem baseWitness_publicInput {limits : ResourceLimits} {image : ProgramImage}
    {source target : ExecutionSnapshot} {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState}
    {channels : List (RawChannel (ZMod p))}
    (witness : EnsembleWitness (ensemble limits image source target final bankFinal channels)) :
    (baseWitness witness).publicInput = witness.publicInput :=
  (ResourceBoundary.checker limits source target).project_publicInput witness

/-- Constraints and balance yield the existing exhaustive path and literal resource bounds.
The actual target is deliberately distinguished from the supplied snapshot until A4 binds it. -/
theorem source_execution {limits : ResourceLimits} {image : ProgramImage}
    {source target : ExecutionSnapshot} {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState}
    {channels : List (RawChannel (ZMod p))} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble limits image source target final bankFinal channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∃ events actual, ExecutionPath ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
        source.realize events actual ∧
      ExecutionPath.WritesPermitted ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
        source.realize events ∧
      actual.clock = target.clock ∧
      (executionResources ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
        source.realize events) .ticks ≤ limits.ticks ∧
      8 * events.length ≤ target.clock - source.clock ∧
      ResourceBoundary.Spec limits source target witness.publicInput ∧
      events.Perm ((LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected
        (baseWitness witness)))).map NativeCore.ExecutionRow.event) ∧
      actual.sail.regs.get? LeanRV64D.Defs.Register.PC =
        some (StateMsg.pcBits (finalBoundaryStateMessage witness.publicInput)) ∧
      ∀ loc message, LocalCore.memoryFinalFrontier (HostLocalCore.localWitness (HostHintQueueBoundary.projected
          (baseWitness witness))) loc = some message →
        locContent actual.sail loc = some (Word.toBitVec64 message.value) := by
  have spec := resource_spec witness balanced
  obtain ⟨events, actual, path, permitted, inventory, clock, pc, memory⟩ :=
    HostHintReadCPU.source_execution valid (baseWitness witness)
      (baseWitness_constraints witness constraints) (baseWitness_balanced witness balanced)
  rw [baseWitness_publicInput] at clock pc
  obtain ⟨endpoint, ticks, count⟩ := spec.path_work path clock
  exact ⟨events, actual, path, permitted, endpoint, ticks, count, spec, inventory, pc, memory⟩

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
/-- The native tick ceiling implies its event ceiling without treating host calls as eight ticks. -/
theorem native_event_bound {events : List ExecutionEvent} {source target : ExecutionSnapshot}
    (bounds : ResourceBoundary.Bounds (ResourceLimits.native p) source target)
    (count : 8 * events.length ≤ target.clock - source.clock) :
    events.length ≤ (ResourceLimits.native p).events := by
  have ticks := bounds.2.2.2.1
  change target.clock - source.clock ≤ 2 ^ 24 at ticks
  change events.length ≤ 2 ^ 24 / 8
  omega

end SP1Clean.Soundness.ResourceEnsemble
