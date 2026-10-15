import SP1Clean.Soundness.HostLocalHandoff
import SP1Clean.Soundness.HostCallReceivers
import SP1Clean.Soundness.HostHintReadPartition

/-! # HINT_READ handler uniqueness from the instruction handoff

The actual handler consumes one full HostCall per physical row. Balanced handoff to these
handlers and the other handlers' unit pulls transfers instruction-clock uniqueness. The local
CPU theorem supplies producer uniqueness once the wrapper is projected onto its actual syscall
table. No caller supplies handler uniqueness or independently balanced per-call cursor tables.
-/

namespace SP1Clean.Soundness.HostHintReadHandoff

open Circuit Air.Flat HostHintReadCoverage

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

omit [Fact (2 ^ 25 < p)] in
private theorem eval_call (row : Var HostHintReadChip.Inputs (ZMod p)) (env : Environment (ZMod p)) :
    eval env row.call = (eval env row).call := by
  cases row
  simp only [circuit_norm]

theorem handler_values (env : Environment (ZMod p)) :
    handler.operations.interactionValuesWith HostCallChip.channel.toRaw env =
      [HostCallChip.channel.pulledValue (input env).call] := by
  simp only [Operations.interactionValuesWith, Component.interactionsWith_eq]
  change ((HostHintReadChip.main (varFromOffset HostHintReadChip.Inputs 0)).operations
    (size HostHintReadChip.Inputs)).interactionValuesWith HostCallChip.channel.toRaw env = _
  rw [HostHintReadChip.host_values, eval_call, eval_varFromOffset_valueFromOffset]
  rfl

/-- The real HINT_READ handler consumes one complete HostCall per physical row. -/
def receiver : HostLocalHandoff.Receiver (p := p) where
  component := handler
  message env := (input env).call
  interactions := handler_values

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- The real handler and both RAM-writing consumer variants satisfy the chronology interface.
Queue/word authentication and their remaining channel balances are separate obligations. -/
theorem auxiliaryInterface : HostLocalCore.AuxiliaryInterface
    [handler (p := p), (HintReadCoverage.view false).component, (HintReadCoverage.view true).component] := by
  apply HostLocalCore.AuxiliaryInterface.of_channels
  · intro component member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;>
      simp [handler, HintReadCoverage.view, HostHintReadChip.circuit, HintReadWordChip.circuit,
        Channels.byteChannel, Channels.memoryChannel, HostHintQueue.nodeChannel,
        HostHintQueue.wordChannel, HostHintQueue.stateChannel, HostCallChip.channel,
        HintReadWordChip.stateChannel, HostRamAccessChip.channel, WritePermissionProvider.channel, Channel.toRaw]
  · intro component member used
    have names := List.mem_map_of_mem (f := RawChannel.name) used
    have present := List.contains_iff_mem.mpr names
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> change false = true at present <;> contradiction

/-- The implemented handler registry includes the real HINT_READ receiver and all control,
commitment, and HINT_LEN variants. WRITE and VERIFY handlers are not yet registered. -/
def registeredReceivers : List (HostLocalHandoff.Receiver (p := p)) :=
  receiver :: HostCallReceivers.available

def wordResources : List (Component (ZMod p)) :=
  [(HintReadCoverage.view false).component, (HintReadCoverage.view true).component]

/-- The actual handler registry and word consumers satisfy the chronology interface. -/
theorem registeredInterface : HostLocalCore.AuxiliaryInterface
    ((registeredReceivers (p := p)).map (·.component) ++ wordResources) := by
  have member_split (component : Component (ZMod p))
      (member : component ∈ (registeredReceivers (p := p)).map (·.component) ++ wordResources) :
      component ∈ [handler, (HintReadCoverage.view false).component, (HintReadCoverage.view true).component] ∨
        component ∈ (HostCallReceivers.available (p := p)).map (·.component) := by
    simpa only [registeredReceivers, List.map_cons, List.mem_append, List.mem_cons,
      wordResources, receiver, List.not_mem_nil, or_false, or_assoc, or_left_comm, or_comm] using member
  constructor
  · intro component member env constraints
    rcases member_split component member with hint | other
    · exact auxiliaryInterface.byte component hint env constraints
    · exact HostCallReceivers.auxiliaryInterface.byte component other env constraints
  · intro component member
    rcases member_split component member with hint | other
    · exact auxiliaryInterface.state component hint
    · exact HostCallReceivers.auxiliaryInterface.state component other

/-- RAM word resources cannot forge or cancel any instruction-to-handler call. -/
theorem wordResources_hostCall_silent : ∀ component ∈ wordResources (p := p),
    HostCallChip.channel.toRaw ∉ component.circuit.channels := by
  intro component member used
  have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
  simp only [wordResources, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> change false = true at present <;> contradiction

private theorem callClock_nodup_of_receiver (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (unique : ((ReceiverView.tableMessages receiver table data).map HostCallLedger.clock).Nodup) :
    ((table.table.map (Environment.fromArray · data)).map HostHintReadPartition.callClock).Nodup := by
  simpa only [ReceiverView.tableMessages, receiver, List.map_map, Function.comp_def,
    HostCallLedger.clock, HostHintReadPartition.callClock, HostHintReadPartition.clock,
    HostHintReadChip.Inputs.first] using unique

/-- Registration and the actual CPU/HostCall evidence fix the physical handler clocks.
No Byte balance is required of this proof view. -/
theorem handler_clocks_nodup_of_registered_channels
    {image : Model.Core.ProgramImage} {source : Model.Core.ExecutionSnapshot}
    {receivers : List (HostLocalHandoff.Receiver (p := p))} {resources : List (Component (ZMod p))}
    {channels : List (RawChannel (ZMod p))}
    {names : ((HostLocalCore.tables image source (receivers.map (·.component) ++ resources)).map (·.circuit.name)).Nodup}
    (witness : EnsembleWitness (HostLocalHandoff.ensemble image source receivers resources channels names))
    (silent : ∀ component ∈ resources, HostCallChip.channel.toRaw ∉ component.circuit.channels)
    (constraints : witness.Constraints)
    (ordering : LocalCore.OrderingChannels (HostLocalCore.localWitness witness))
    (balanced : witness.BalancedChannel HostCallChip.channel.toRaw)
    (index : Fin receivers.length) (registered : receivers[index.val] = receiver) :
    let handlers := HostLocalHandoff.receiverTable witness index
    ((handlers.table.map (Environment.fromArray · witness.data)).map HostHintReadPartition.callClock).Nodup := by
  have unique := HostLocalHandoff.receiver_clocks_nodup_of_orderingChannels witness silent constraints ordering balanced
    index.val index.isLt
  rw [registered] at unique
  exact callClock_nodup_of_receiver (HostLocalHandoff.receiverTable witness index) witness.data unique

end SP1Clean.Soundness.HostHintReadHandoff
