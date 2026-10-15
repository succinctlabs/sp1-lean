import SP1Clean.Soundness.OrderedMemoryEnsemble
import SP1Clean.Proofs.Chips.OrderedInitialProvider

/-! # Native initialization tables with fixed control endpoints

Register and RAM initialization share one private ordering channel. The fixed endpoints are
zero and `2^48 + 1`; a terminal table closes the chain after the last address. The transition
views below are proved against the actual Clean circuits. Auxiliary tables may close Memory
and Byte interactions, but may not contribute to this private ordering channel.

This ensemble is an initialization subsystem for the native core. Integrating its authenticated
records into the instruction grounding argument remains separate from its inventory theorem.
-/

namespace SP1Clean.Soundness.InitialMemoryEnsemble

open Circuit Air.Flat SP1Clean.Model.Core SP1Clean.Channels SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

abbrev startKey := @OrderedMemoryEnsemble.startKey
abbrev endKey := @OrderedMemoryEnsemble.endKey

omit [Fact (2 ^ 17 < p)] in
theorem startKey_toNat : Word.toNat (startKey (p := p)) = 0 :=
  OrderedMemoryEnsemble.startKey_toNat

omit [Fact (2 ^ 17 < p)] in
theorem endKey_toNat : Word.toNat (endKey (p := p)) = 2 ^ 48 + 1 :=
  OrderedMemoryEnsemble.endKey_toNat

def providerView {Payload : TypeMap} [ProvableType Payload] (image : ProgramImage)
    (provider : GeneralFormalCircuit (ZMod p) Payload MemoryMsg)
    (binds : ∀ input output data, provider.Spec input output data → MemoryBoundary.InitialSpec image output)
    (privateChannel : (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw ∉ provider.channels) :
    TransitionView (OrderedBoundary.channel (p := p) OrderedInitialProvider.channelName) :=
  OrderedMemoryEnsemble.providerView OrderedInitialProvider.channelName (by decide)
    (MemoryBoundary.InitialSpec image) provider binds (fun _ valid => valid.canonical) privateChannel

def registerView (image : ProgramImage) :
    TransitionView (OrderedBoundary.channel (p := p) OrderedInitialProvider.channelName) :=
  providerView image (InitialRegisterProvider.circuit image) (fun _ _ _ valid => valid.1) (by
    simp [GeneralFormalCircuit.channels, InitialRegisterProvider.circuit, circuit_norm,
      OrderedBoundary.channel, OrderedInitialProvider.channelName, memoryChannel])

def ramView (image : ProgramImage) :
    TransitionView (OrderedBoundary.channel (p := p) OrderedInitialProvider.channelName) :=
  providerView image (InitialRamProvider.circuit image) (fun _ _ _ valid => valid.1) (by
    simp [GeneralFormalCircuit.channels, InitialRamProvider.circuit, circuit_norm,
      OrderedBoundary.channel, OrderedInitialProvider.channelName, memoryChannel, byteChannel])

def terminalView :
    TransitionView (OrderedBoundary.channel (p := p) OrderedInitialProvider.channelName) :=
  OrderedMemoryEnsemble.terminalView OrderedInitialProvider.channelName (by decide)

/-- These three components own the initialization ordering channel. -/
def views (image : ProgramImage) := [registerView (p := p) image, ramView image, terminalView]

/-- The three registered initialization tables have distinct canonical names. -/
theorem views_unique_names (image : ProgramImage) :
    ((views (p := p) image).map (·.component.circuit.name)).Nodup := by
  simp [views, registerView, ramView, terminalView, providerView,
    OrderedMemoryEnsemble.providerView, OrderedMemoryEnsemble.terminalView,
    OrderedMemoryProvider.circuit, OrderedBoundaryEnd.circuit,
    InitialRegisterProvider.circuit, InitialRamProvider.circuit, OrderedInitialProvider.channelName]
  decide

inductive TableId where
  | registers | ram | terminal
deriving DecidableEq

def tableIds : List TableId := [.registers, .ram, .terminal]

def viewFor (image : ProgramImage) : TableId →
    TransitionView (OrderedBoundary.channel (p := p) OrderedInitialProvider.channelName)
  | .registers => registerView image
  | .ram => ramView image
  | .terminal => terminalView

theorem views_eq_map (image : ProgramImage) : views (p := p) image = tableIds.map (viewFor image) := rfl

def ensemble (image : ProgramImage) (auxiliary : List (Component (ZMod p)))
    (channels : List (RawChannel (ZMod p)))
    (names : (((views (p := p) image).map (·.component) ++ auxiliary).map (·.circuit.name)).Nodup) :
    Ensemble (ZMod p) unit :=
  OrderedBoundaryEnsemble.ensemble OrderedInitialProvider.channelName startKey endKey
    (views image) auxiliary channels names

private theorem providerView_strict {Payload : TypeMap} [ProvableType Payload] (image : ProgramImage)
    (provider : GeneralFormalCircuit (ZMod p) Payload MemoryMsg)
    (binds : ∀ input output data, provider.Spec input output data → MemoryBoundary.InitialSpec image output)
    (privateChannel : (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw ∉ provider.channels)
    (env : Environment (ZMod p))
    (valid : (providerView image provider binds privateChannel).component.Spec env) :
    Word.toNat ((providerView image provider binds privateChannel).edge env).1 <
      Word.toNat ((providerView image provider binds privateChannel).edge env).2 :=
  valid.2.1.2.2

theorem views_strict (image : ProgramImage)
    (view : TransitionView (OrderedBoundary.channel (p := p) OrderedInitialProvider.channelName))
    (member : view ∈ views image) (env : Environment (ZMod p)) (valid : view.component.Spec env) :
    Word.toNat (view.edge env).1 < Word.toNat (view.edge env).2 := by
  simp only [views, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact providerView_strict image _ _ _ env valid
  · exact providerView_strict image _ _ _ env valid
  · exact valid.2

/-- The initialization inventory has no repeated current key, even across register and RAM
tables. The inputs are actual Clean balance and local table specifications, not a uniqueness
or endpoint-binding assumption. -/
theorem keys_nodup (image : ProgramImage) (auxiliary : List (Component (ZMod p)))
    (channels : List (RawChannel (ZMod p)))
    {names : (((views (p := p) image).map (·.component) ++ auxiliary).map (·.circuit.name)).Nodup}
    (witness : EnsembleWitness (ensemble image auxiliary channels names))
    (privateChannel : ∀ component ∈ auxiliary,
      (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw ∉ component.circuit.channels)
    (valid : witness.Spec) (balanced : witness.BalancedChannels) :
    ((OrderedBoundaryEnsemble.rows witness).map fun row => Word.toNat (row.1.edge row.2).2).Nodup := by
  exact OrderedBoundaryEnsemble.keys_nodup_of_specs witness privateChannel
    (views_strict image) valid balanced

/-- Recover a provider's returned record using Clean's own physical-row output decoder. -/
def recordFor (image : ProgramImage) (id : TableId) (env : Environment (ZMod p)) :
    Option (MemoryMsg (ZMod p)) :=
  match id with
  | .registers => some (({ circuit := OrderedInitialProvider.registerCircuit image } : Component (ZMod p)).rowOutput env)
  | .ram => some (({ circuit := OrderedInitialProvider.ramCircuit image } : Component (ZMod p)).rowOutput env)
  | .terminal => none

theorem recordFor_spec (image : ProgramImage) (id : TableId) (env : Environment (ZMod p))
    (valid : (viewFor image id).component.Spec env) (record : MemoryMsg (ZMod p))
    (found : recordFor image id env = some record) :
    MemoryBoundary.InitialSpec image record ∧
      Word.toNat ((viewFor image id).edge env).2 = (MemoryMsg.locOf record).busAddress + 1 := by
  cases id with
  | registers =>
    obtain rfl := Option.some.inj found
    exact ⟨valid.1, valid.2.2⟩
  | ram =>
    obtain rfl := Option.some.inj found
    exact ⟨valid.1, valid.2.2⟩
  | terminal => contradiction

/-- Initialization instantiates the common inventory theorem with boot-value authentication. -/
def inventory (image : ProgramImage) :
    OrderedMemoryEnsemble.Inventory OrderedInitialProvider.channelName (MemoryBoundary.InitialSpec (p := p) image) where
  Index := TableId
  tableIds := tableIds
  viewFor := viewFor image
  recordFor := recordFor image
  strict := by
    intro id env valid
    cases id with
    | registers => exact valid.2.1.2.2
    | ram => exact valid.2.1.2.2
    | terminal => exact valid.2
  recordFor_spec := recordFor_spec image

variable {image : ProgramImage} {auxiliary : List (Component (ZMod p))}
variable {channels : List (RawChannel (ZMod p))}
variable {names : (((views (p := p) image).map (·.component) ++ auxiliary).map (·.circuit.name)).Nodup}

def indexedRows (witness : EnsembleWitness (ensemble image auxiliary channels names)) :=
  TransitionView.readIndexedRows tableIds (witness.tables.take (views (p := p) image).length) witness.data

def records (witness : EnsembleWitness (ensemble image auxiliary channels names)) : List (MemoryMsg (ZMod p)) :=
  (indexedRows witness).filterMap fun row => recordFor image row.1 row.2

theorem indexedRows_spec (witness : EnsembleWitness (ensemble image auxiliary channels names))
    (valid : witness.Spec) :
    ∀ row ∈ indexedRows witness, (viewFor image row.1).component.Spec row.2 := by
  exact (inventory image).indexedRows_spec witness valid

/-- Every decoded provider record carries the authentic boot value at its canonical location. -/
theorem records_authentic (witness : EnsembleWitness (ensemble image auxiliary channels names))
    (valid : witness.Spec) : ∀ record ∈ records witness, MemoryBoundary.InitialSpec image record := by
  exact (inventory image).records_valid witness valid

/-- The combined register/RAM provider inventory is unique by decoded memory location.
This follows from actual control balance, even when the physical rows are permuted. -/
theorem records_locations_nodup (witness : EnsembleWitness (ensemble image auxiliary channels names))
    (privateChannel : ∀ component ∈ auxiliary,
      (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw ∉ component.circuit.channels)
    (valid : witness.Spec) (balanced : witness.BalancedChannels) :
    ((records witness).map MemoryMsg.locOf).Nodup := by
  exact (inventory image).records_locations_nodup witness privateChannel valid balanced

/-- The finite record decoder agrees exactly with each table's physical Memory interactions. -/
theorem recordFor_interactions (image : ProgramImage) (id : TableId) (env : Environment (ZMod p)) :
    (viewFor image id).component.operations.interactionValuesWith memoryChannel.toRaw env =
      ((recordFor image id env).toList).map memoryChannel.pushedValue := by
  cases id with
  | registers =>
    simp only [viewFor, registerView, providerView, OrderedMemoryEnsemble.providerView,
        Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations,
        OrderedMemoryProvider.circuit]
    rw [OrderedMemoryProvider.main_memory_interactions]
    simp only [InitialRegisterProvider.circuit]
    rw [InitialRegisterProvider.main_memory_interactions]
    simp only [List.map_cons, List.map_nil, Channel.eval_pushed]
    rfl
  | ram =>
    simp only [viewFor, ramView, providerView, OrderedMemoryEnsemble.providerView,
        Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations,
        OrderedMemoryProvider.circuit]
    rw [OrderedMemoryProvider.main_memory_interactions]
    simp only [InitialRamProvider.circuit]
    rw [InitialRamProvider.main_memory_interactions]
    simp only [List.map_cons, List.map_nil, Channel.eval_pushed]
    rfl
  | terminal =>
    exact OrderedMemoryEnsemble.terminalView_memory_interactions _ (by decide) env

/-- The physical boundary tables emit precisely the decoded records, with unit multiplicity. -/
theorem memory_interactions_eq (witness : EnsembleWitness (ensemble image auxiliary channels names)) :
    (witness.tables.take (inventory (p := p) image).views.length).flatMap (·.interactionsWith witness.data memoryChannel.toRaw) =
      (records witness).map memoryChannel.pushedValue := by
  exact (inventory image).memory_interactions_eq witness memoryChannel.pushedValue (recordFor_interactions image)

end SP1Clean.Soundness.InitialMemoryEnsemble
