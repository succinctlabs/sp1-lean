import SP1Clean.Soundness.HostLocalCoreLedger
import ToClean.Air.ReceiverView

/-! # Complete instruction-to-handler accounting in the installed local AIR

Receivers are registered together with their exact unit HostCall ledger. Resource components
may use the other protocols but must be silent on HostCall. The actual physical table suffix
then determines every consumed call. Constraints and the ensemble's own balance prove a
permutation with active instruction calls, and CPU chronology gives each handler unique clocks.
No independent witness projection, ledger equation, or handler inventory is a caller premise.
-/

namespace SP1Clean.Soundness.HostLocalHandoff

open Circuit Air.Flat Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

abbrev Receiver := ReceiverView (HostCallChip.channel (p := p))

abbrev ensemble (image : ProgramImage) (source : ExecutionSnapshot)
    (receivers : List (Receiver (p := p))) (resources : List (Component (ZMod p)))
    (channels : List (RawChannel (ZMod p)))
    (names : ((HostLocalCore.tables image source (receivers.map (·.component) ++ resources)).map (·.circuit.name)).Nodup) :=
  HostLocalCore.ensemble image source (receivers.map (·.component) ++ resources) channels names

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {receivers : List (Receiver (p := p))} {resources : List (Component (ZMod p))}
  {channels : List (RawChannel (ZMod p))}
  {names : ((HostLocalCore.tables image source (receivers.map (·.component) ++ resources)).map (·.circuit.name)).Nodup}

def receiverTables (witness : EnsembleWitness (ensemble image source receivers resources channels names)) :=
  (HostLocalCore.auxiliaryTables witness).take receivers.length

def resourceTables (witness : EnsembleWitness (ensemble image source receivers resources channels names)) :=
  (HostLocalCore.auxiliaryTables witness).drop receivers.length

theorem receiverTables_components (witness : EnsembleWitness (ensemble image source receivers resources channels names)) :
    (receiverTables witness).map (·.component) = receivers.map (·.component) := by
  simp only [receiverTables, List.map_take, HostLocalCore.auxiliaryTables_components]
  rw [← List.length_map (as := receivers) (f := fun view : Receiver (p := p) => view.component), List.take_left]

theorem resourceTables_components (witness : EnsembleWitness (ensemble image source receivers resources channels names)) :
    (resourceTables witness).map (·.component) = resources := by
  simp only [resourceTables, List.map_drop, HostLocalCore.auxiliaryTables_components]
  rw [← List.length_map (as := receivers) (f := fun view : Receiver (p := p) => view.component), List.drop_left]

theorem receiverTables_aligned (witness : EnsembleWitness (ensemble image source receivers resources channels names)) :
    List.Forall₂ (fun view table => view.component = table.component) receivers (receiverTables witness) :=
  ReceiverView.aligned_of_map_eq _ _ (receiverTables_components witness).symm

/-- A registered handler's actual physical table. -/
def receiverTable (witness : EnsembleWitness (ensemble image source receivers resources channels names))
    (index : Fin receivers.length) : Table (ZMod p) :=
  (receiverTables witness)[index.val]'(by rw [← (receiverTables_aligned witness).length_eq]; exact index.isLt)

theorem receiverTable_component (witness : EnsembleWitness (ensemble image source receivers resources channels names))
    (index : Fin receivers.length) : (receiverTable witness index).component = receivers[index.val].component := by
  have same := congrArg (fun tables => tables[index.val]?) (receiverTables_components witness)
  simp only [List.getElem?_map, List.getElem?_eq_getElem index.isLt] at same
  rw [List.getElem?_eq_getElem (by rw [← (receiverTables_aligned witness).length_eq]; exact index.isLt)] at same
  exact Option.some.inj same

/-- The complete typed receiver inventory is read from the actual witness, in registration order. -/
def calls (witness : EnsembleWitness (ensemble image source receivers resources channels names)) :=
  ReceiverView.messages receivers (receiverTables witness) witness.data

/-- All installed physical tables are accounted for, including instruction padding. -/
theorem hostCall_interactions (witness : EnsembleWitness (ensemble image source receivers resources channels names))
    (silent : ∀ component ∈ resources, HostCallChip.channel.toRaw ∉ component.circuit.channels) :
    witness.interactionsWith HostCallChip.channel.toRaw =
      (HostLocalCore.hostCallTable witness).interactionsWith witness.data HostCallChip.channel.toRaw ++
        (calls witness).map HostCallChip.channel.pulledValue := by
  rw [HostLocalCore.hostCall_interactions]
  have split : receiverTables witness ++ resourceTables witness = HostLocalCore.auxiliaryTables witness :=
    List.take_append_drop _ _
  rw [← split, List.flatMap_append]
  have resourceSilent : (resourceTables witness).flatMap (·.interactionsWith witness.data HostCallChip.channel.toRaw) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro table member
    apply table.interactionsWith_nil_of_channel_not_mem
    apply silent table.component
    rw [← resourceTables_components witness]
    exact List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
  rw [resourceSilent, List.append_nil, ReceiverView.messages_interactions _ _ witness.data (receiverTables_aligned witness)]
  rfl

/-- Complete handler accounting needs only the actual HostCall channel balance. -/
theorem calls_perm_of_balancedChannel (witness : EnsembleWitness (ensemble image source receivers resources channels names))
    (silent : ∀ component ∈ resources, HostCallChip.channel.toRaw ∉ component.circuit.channels)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel HostCallChip.channel.toRaw) :
    (HostCallLedger.calls (HostLocalCore.hostCallTable witness) witness.data).Perm (calls witness) := by
  apply HostCallLedger.calls_perm _ witness.data (HostLocalCore.hostCallTable_component witness)
    (constraints _ (HostLocalCore.hostCallTable_mem witness))
  rw [← hostCall_interactions witness silent]
  exact balanced

/-- Every handler occurrence corresponds to exactly one active instruction with the same full call. -/
theorem calls_perm (witness : EnsembleWitness (ensemble image source receivers resources channels names))
    (silent : ∀ component ∈ resources, HostCallChip.channel.toRaw ∉ component.circuit.channels)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    (HostCallLedger.calls (HostLocalCore.hostCallTable witness) witness.data).Perm (calls witness) :=
  calls_perm_of_balancedChannel witness silent constraints (balanced _ (List.mem_append_left _ (List.mem_cons_self ..)))

/-- CPU chronology and HostCall balance transfer uniqueness to every registered handler. -/
theorem calls_clocks_nodup_of_orderingChannels
    (witness : EnsembleWitness (ensemble image source receivers resources channels names))
    (silent : ∀ component ∈ resources, HostCallChip.channel.toRaw ∉ component.circuit.channels)
    (constraints : witness.Constraints)
    (ordering : LocalCore.OrderingChannels (HostLocalCore.localWitness witness))
    (balanced : witness.BalancedChannel HostCallChip.channel.toRaw) :
    ((calls witness).map HostCallLedger.clock).Nodup :=
  ((calls_perm_of_balancedChannel witness silent constraints balanced).map HostCallLedger.clock).nodup_iff.mp
    (HostLocalCore.hostCalls_clocks_nodup_of_orderingChannels witness constraints ordering)

/-- CPU ordering rules out duplicate handler clocks across the entire heterogeneous registry. -/
theorem calls_clocks_nodup (witness : EnsembleWitness (ensemble image source receivers resources channels names))
    (interface : HostLocalCore.AuxiliaryInterface (receivers.map (·.component) ++ resources))
    (silent : ∀ component ∈ resources, HostCallChip.channel.toRaw ∉ component.circuit.channels)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ((calls witness).map HostCallLedger.clock).Nodup :=
  calls_clocks_nodup_of_orderingChannels witness silent constraints
    (HostLocalCore.orderingChannels witness interface constraints balanced) (balanced _ (List.mem_append_left _ (List.mem_cons_self ..)))

/-- Select one physical handler from the registered clock inventory without whole-ensemble balance. -/
theorem receiver_clocks_nodup_of_orderingChannels
    (witness : EnsembleWitness (ensemble image source receivers resources channels names))
    (silent : ∀ component ∈ resources, HostCallChip.channel.toRaw ∉ component.circuit.channels)
    (constraints : witness.Constraints)
    (ordering : LocalCore.OrderingChannels (HostLocalCore.localWitness witness))
    (balanced : witness.BalancedChannel HostCallChip.channel.toRaw)
    (index : ℕ) (bound : index < receivers.length) :
    ((ReceiverView.tableMessages receivers[index]
      ((receiverTables witness)[index]'(by rw [← (receiverTables_aligned witness).length_eq]; exact bound)) witness.data).map
        HostCallLedger.clock).Nodup :=
  ReceiverView.tableMessages_keys_nodup _ _ witness.data (receiverTables_aligned witness) _
    (calls_clocks_nodup_of_orderingChannels witness silent constraints ordering balanced) index bound

/-- Every physical row of any registered handler inherits the global clock uniqueness. -/
theorem receiver_clocks_nodup (witness : EnsembleWitness (ensemble image source receivers resources channels names))
    (interface : HostLocalCore.AuxiliaryInterface (receivers.map (·.component) ++ resources))
    (silent : ∀ component ∈ resources, HostCallChip.channel.toRaw ∉ component.circuit.channels)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (index : ℕ) (bound : index < receivers.length) :
    ((ReceiverView.tableMessages receivers[index]
      ((receiverTables witness)[index]'(by rw [← (receiverTables_aligned witness).length_eq]; exact bound)) witness.data).map
        HostCallLedger.clock).Nodup :=
  receiver_clocks_nodup_of_orderingChannels witness silent constraints
    (HostLocalCore.orderingChannels witness interface constraints balanced)
    (balanced _ (List.mem_append_left _ (List.mem_cons_self ..))) index bound

end SP1Clean.Soundness.HostLocalHandoff
