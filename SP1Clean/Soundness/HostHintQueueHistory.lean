import SP1Clean.Soundness.HostQueueHistory
import SP1Clean.Soundness.HostHintQueueBoundary

/-! # Byte-exact queue replay from the installed AIR

Verifier-owned endpoints, actual record authentication, and exhaustive token ordering now derive
the current semantic queue at every physical HINT_LEN/HINT_READ event. Replay checks observed
length words and exact consumed lengths, and the final cursor decodes to the replay's remaining
bytes. Agreement with a separately claimed outgoing snapshot, WRITE/hook allocation edges, and
the mixed CPU/Memory execution remain separate obligations.
-/

namespace SP1Clean.Soundness.HostHintQueueHistory

open Circuit Air.Flat Model.Core Model.Core.HintQueue HostHintQueue HostHintReadLocal HostQueueOrder
open SP1Clean.Soundness.HostHintQueueBoundary

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- Complete replay, with current store/frontier truth at every prefix of the physical path. -/
def History (hints : List Bytes) (final : State (ZMod p)) (upper : Store) (path : List (Row (p := p))) : Prop :=
  ∃ finalStore finalHints, Extends (ofList hints).1 finalStore ∧ Extends finalStore upper ∧
    final.Binds finalStore finalHints ∧ replay? (path.map HostQueueHistory.event) hints = some finalHints ∧
    HintQueueHistory.Prefixes edge HostQueueHistory.event path (ofList hints).1 finalStore hints

/-- The authenticated terminal cursor determines exactly the bytes left by semantic replay. -/
theorem terminal_bytes {hints : List Bytes} {final : State (ZMod p)} {upper : Store}
    {path : List (Row (p := p))} (history : History hints final upper path) :
    ∃ remaining, replay? (path.map HostQueueHistory.event) hints = some remaining ∧
      decode? upper (Address.toNat final.head) = some remaining := by
  obtain ⟨_, remaining, _, bounded, binding, replayed, _⟩ := history
  exact ⟨remaining, replayed, decode?_of_represents (binding.2.2.2.extend bounded)⟩

/-- Grounding can recover the current store/frontier once its host queue agrees with prefix replay. -/
theorem History.current {hints atHints : List Bytes} {final : State (ZMod p)} {upper : Store}
    {path prior suffix : List (Row (p := p))} {row : Row (p := p)}
    (history : History hints final upper path) (split : path = prior ++ row :: suffix)
    (replayed : replay? (prior.map HostQueueHistory.event) hints = some atHints) :
    ∃ store, Extends store upper ∧ (edge row).1.Binds store atHints := by
  obtain ⟨_, _, _, bounded, _, _, prefixes⟩ := history
  obtain ⟨store, current, _, extended, actual, binding⟩ := prefixes prior row suffix split
  have equal := Option.some.inj (actual.symm.trans replayed)
  exact ⟨store, extended.trans bounded, equal ▸ binding⟩

variable {image : ProgramImage} {source : ExecutionSnapshot} {final : State (ZMod p)} {bankFinal : HostState}
  {resources : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
  {names : ((HostLocalCore.tables image source
    ((HostHintReadHandoff.receiver :: HostCallReceivers.available).map (·.component) ++
      (HostHintReadHandoff.wordResources ++ resources))).map (·.circuit.name)).Nodup}

/-- Every path prefix supplies its current queue from the AIR; callers supply no per-call head truth.
The current handler registry requires extra resources without additional queue-state edges. -/
theorem of_witness
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal
      HostCallReceivers.available resources channels names))
    (interface : ExtensionInterface HostCallReceivers.available resources)
    (upper : Store) (extension : Extends (ofList source.host.io.hints).1 upper)
    (authenticated : RecordAuthentication (projected witness) upper)
    (silent : ∀ component ∈ resources, stateChannel.toRaw ∉ component.circuit.channels)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∃ path : List (Row (p := p)),
      path.Perm (TransitionView.readIndexedRows indices (queueTables (projected witness)) witness.data) ∧
      Walk.IsWalk edge (SP1Clean.HostHintQueueBoundary.initial source.host.io.hints) final path ∧
      History source.host.io.hints final upper path := by
  obtain ⟨path, exhaustive, walk⟩ := queue_ordered witness interface upper authenticated silent constraints balanced
  have checks := projected_constraints witness constraints
  have records := record_channels witness balanced
  have specs := queue_specs (projected witness) interface upper authenticated checks records
  refine ⟨path, exhaustive, walk, ?_⟩
  apply HintQueueHistory.of_walk edge HostQueueHistory.event path _ final _ upper _ walk
    (source_binding witness balanced) extension
  intro row member
  have physical := exhaustive.mem_iff.mp member
  rw [← projected_data witness] at physical
  exact HostQueueHistory.advance row upper
    (rows_spec _ (projected witness).data (queueTables_aligned (projected witness)) specs row physical)
    (HostQueueHistory.records_of_witness (projected witness) upper authenticated records row physical)

/-- Source bytes and the installed AIR alone determine every observed length, queue pop, and final
reachable queue. This theorem does not require current-head or record-authentication premises. -/
theorem source_history
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∃ path : List (Row (p := p)),
      path.Perm (TransitionView.readIndexedRows indices (queueTables (projected witness)) witness.data) ∧
      Walk.IsWalk edge (SP1Clean.HostHintQueueBoundary.initial source.host.io.hints) final path ∧
      History source.host.io.hints final (ofList source.host.io.hints).1 path := by
  apply of_witness witness (source_interface source.host.io.hints) _ (.refl _)
    (source_authentication witness constraints) _ constraints balanced
  intro component member used
  have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
  simp only [sourceResources, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> change false = true at present <;> exact Bool.noConfusion present

end SP1Clean.Soundness.HostHintQueueHistory
