import SP1Clean.Native.Operations.SailBoundary
import SP1Clean.Soundness.HostFinalMemorySoundness

/-! # Install the supplied Sail frame above the complete Memory boundary

The target's Memory projection, register map, runtime fields, PC/clock and host-bank parameters
come from one complete supplied snapshot. The added public circuit preserves the full physical
ledger. Dynamic nextPC/retirement binding and complete host agreement remain open; this assembly
does not yet fill the end-to-end shard target.
-/

namespace SP1Clean.Soundness.HostSailBoundary

open Circuit Air.Flat Model.Core Semantics Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance sailLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance sailClockBound : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Bind the public endpoint and preserved Sail fields to the same target as the Memory checks. -/
def ensemble (image : ProgramImage) (source target : ExecutionSnapshot)
    (final : HostHintQueue.State (ZMod p))
    (others : List (HostLocalHandoff.Receiver (p := p))) (resources : List (Component (ZMod p)))
    (channels : List (RawChannel (ZMod p)))
    (names : HostFinalMemory.UniqueNames image source target.sail.memorySnapshot others resources) : Ensemble (ZMod p) SP1PublicIO :=
  (SailBoundary.checker source target).install
    (HostFinalMemory.ensemble image source target.sail.memorySnapshot final target.host others resources channels names)

variable {image : ProgramImage} {source target : ExecutionSnapshot}
  {final : HostHintQueue.State (ZMod p)}
  {others : List (HostLocalHandoff.Receiver (p := p))} {resources : List (Component (ZMod p))}
  {channels : List (RawChannel (ZMod p))}
  {names : HostFinalMemory.UniqueNames image source target.sail.memorySnapshot others resources}

/-- The Memory proof view retains every physical table, row, lookup environment and public field. -/
def baseWitness (witness : EnsembleWitness (ensemble image source target final others resources channels names)) :
    EnsembleWitness (HostFinalMemory.ensemble image source target.sail.memorySnapshot final target.host
      others resources channels names) := (SailBoundary.checker source target).project witness

/-- The added circuit preserves all original local checks. -/
theorem baseWitness_constraints (witness : EnsembleWitness (ensemble image source target final others resources channels names))
    (checked : witness.Constraints) : (baseWitness witness).Constraints :=
  ((SailBoundary.checker source target).project_constraints witness).mp checked

/-- The separate check channel preserves original balance and every original count bound. -/
theorem baseWitness_balanced (witness : EnsembleWitness (ensemble image source target final others resources channels names))
    (balanced : witness.BalancedChannels) : (baseWitness witness).BalancedChannels :=
  (((SailBoundary.checker source target).project_balanced_iff witness).mp balanced).1

/-- The verifier's actual assertions establish the finite target frame and canonical endpoints. -/
theorem target_spec (witness : EnsembleWitness (ensemble image source target final others resources channels names))
    (balanced : witness.BalancedChannels) : SailBoundary.Spec source target witness.publicInput :=
  (SailBoundary.checks_iff ..).mp
    (((SailBoundary.checker source target).project_balanced_iff witness).mp balanced).2.2

/-- The new checker contributes exactly its proved meaning to acceptance, in both directions. -/
theorem statement_iff (input : SP1PublicIO (ZMod p)) :
    (ensemble image source target final others resources channels names).Statement input ↔
      (HostFinalMemory.ensemble image source target.sail.memorySnapshot final target.host
        others resources channels names).Statement input ∧ SailBoundary.Spec source target input :=
  (SailBoundary.checker source target).statement_iff _ (SailBoundary.count_bound source target)
    (SailBoundary.Spec source target)
    (SailBoundary.checks_iff source target) input

/-- Raw acceptance binds the complete Memory comparison and the actual target register presence.
No static circuit-interface proof or endpoint certificate is a caller premise. -/
theorem source_target_checks
    (witness : EnsembleWitness (ensemble image source target final HostCallReceivers.available
      (HostHintReadLocal.sourceResources source.host.io.hints) channels
      (HostFinalMemory.source_unique_names image source target.sail.memorySnapshot)))
    (checked : witness.Constraints) (balanced : witness.BalancedChannels) :
    SailBoundary.Spec source target witness.publicInput ∧
      source.sail.memorySnapshot.checkFinal target.sail.memorySnapshot
        ((HostFinalMemory.finalRecords (baseWitness witness)).map
          fun record => (MemoryMsg.locOf record, Word.toBitVec64 record.value)) = true ∧
      target.sail.memorySnapshot.Realizes target.sail.realize := by
  have spec := target_spec witness balanced
  exact ⟨spec, HostFinalMemory.source_checkFinal (baseWitness witness)
    (baseWitness_constraints witness checked) (baseWitness_balanced witness balanced),
    spec.memorySnapshot_realizes⟩

end SP1Clean.Soundness.HostSailBoundary
