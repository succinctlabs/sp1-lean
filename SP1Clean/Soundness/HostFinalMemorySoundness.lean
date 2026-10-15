import SP1Clean.Soundness.HostFinalMemoryTransport
import SP1Clean.Soundness.HostFinalMemoryInventory

/-! # Complete target Memory comparison from raw host acceptance

The actual host witness supplies Byte closure and all five private channel balances.
The existing boundary theorem then checks the complete target, including every location
outside the physical final inventory. No endpoint certificate or witness-selected change
inventory is a premise. Full mixed Sail/host endpoint reconstruction remains a later consumer.
-/

namespace SP1Clean.Soundness.HostFinalMemory

open Circuit Air.Flat Channels Model.Core Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance finalSoundnessLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance finalSoundnessClockBound : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot} {target : MemorySnapshot}
  {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState}
  {others : List (HostLocalHandoff.Receiver (p := p))} {resources : List (Component (ZMod p))}
  {channels : List (RawChannel (ZMod p))}
  {names : UniqueNames image source target others resources}

/-- Complete comparison requires only inherited Byte guarantees and the actual membership and receipt balances. -/
theorem checkFinal_of_channels
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels names))
    (interface : PrivateInterface target others resources) (checked : witness.Constraints)
    (bytes : ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data byteChannel.toRaw)
    (balances : ∀ channel ∈ privateChannels (p := p) target, witness.BalancedChannel channel) :
    source.sail.memorySnapshot.checkFinal target
      ((finalRecords witness).map fun record => (MemoryMsg.locOf record, Word.toBitVec64 record.value)) = true := by
  apply FinalMemoryChecks.checkFinal_of_channels (boundaryWitness witness)
    ⟨by simp, by simp, by simp, by simp⟩ (boundaryWitness_constraints witness checked)
    (boundaryWitness_byte witness bytes)
  · intro ram
    have member : (FinalMemoryValue.channel ram).toRaw ∈ privateChannels (p := p) target := by
      cases ram <;> simp [privateChannels]
    exact boundaryWitness_balancedChannel witness interface _ member (balances _ member)
  · have member : FinalMemoryChange.channel.toRaw ∈ privateChannels (p := p) target := by simp [privateChannels]
    exact boundaryWitness_balancedChannel witness interface _ member (balances _ member)

  · intro channel known
    have member : channel ∈ privateChannels (p := p) target := by
      simp only [FinalMemoryChecks.membershipChannels, List.mem_cons, List.not_mem_nil, or_false] at known
      rcases known with rfl | rfl <;> simp [privateChannels]
    exact boundaryWitness_balancedChannel witness interface _ member (balances _ member)

/-- Complete raw host AIR acceptance implies the existing finite target Memory comparison.
The two interfaces describe fixed installed circuits, never properties of the supplied witness. -/
theorem checkFinal
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels names))
    (interface : HostHintReadLocal.ExtensionInterface others resources)
    (privacy : PrivateInterface target others resources)
    (checked : witness.Constraints) (balanced : witness.BalancedChannels) :
    source.sail.memorySnapshot.checkFinal target
      ((finalRecords witness).map fun record => (MemoryMsg.locOf record, Word.toBitVec64 record.value)) = true := by
  apply checkFinal_of_channels witness privacy checked (byte_guarantees witness interface checked (balanced _ ?_))
  · intro channel member
    apply balanced
    simp only [privateChannels, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;>
      simp [ensemble, ClosedVerifier.install, ClosedVerifier.withInteractions, withReceipts, withRegisters, FinalReceiptEnsemble.install, Ensemble.replaceComponent,
        FinalMemoryChangeBoundary.closed, FinalMemoryChangeBoundary.circuit, circuit_norm]
    all_goals apply Or.inl
    all_goals simp [base, HostHintQueueBoundary.ensemble, HaltPadding.install, Ensemble.replaceComponent,
      ClosedVerifier.install, ClosedVerifier.withInteractions, HostHintReadLocal.ensemble, HostLocalHandoff.ensemble,
      HostLocalCore.ensemble, PublicVerifier.install, HostLocalCore.baseEnsemble,
      FinalMemoryChecks.checkTables, StaticTable.component, StaticTable.provider, circuit_norm]
  · simp [ensemble, ClosedVerifier.install, ClosedVerifier.withInteractions, withReceipts, withRegisters, FinalReceiptEnsemble.install, Ensemble.replaceComponent,
      base, HostHintQueueBoundary.ensemble, HaltPadding.install, Ensemble.replaceComponent, HostHintReadLocal.ensemble,
      HostLocalHandoff.ensemble, HostLocalCore.ensemble, PublicVerifier.install, HostLocalCore.baseEnsemble, LocalCore.baseEnsemble,
      sp1Ensemble_channels]

/-- The concrete six-call registration needs only raw acceptance, with no caller interface proofs. -/
theorem source_checkFinal
    (witness : EnsembleWitness (ensemble image source target final bankFinal HostCallReceivers.available
      (HostHintReadLocal.sourceResources source.host.io.hints) channels (source_unique_names image source target)))
    (checked : witness.Constraints) (balanced : witness.BalancedChannels) :
    source.sail.memorySnapshot.checkFinal target
      ((finalRecords witness).map fun record => (MemoryMsg.locOf record, Word.toBitVec64 record.value)) = true :=
  checkFinal witness (HostHintReadLocal.source_interface source.host.io.hints)
    (source_privacy target source.host.io.hints) checked balanced

end SP1Clean.Soundness.HostFinalMemory
