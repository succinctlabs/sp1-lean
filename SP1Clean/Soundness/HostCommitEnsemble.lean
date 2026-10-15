import SP1Clean.Soundness.HostCommitBank
import ToClean.Air.EnsembleBuild
import ToClean.Air.TableBuild

/-! # A commitment bank bound by its actual Clean verifier

This composable ensemble registers the eight update tables and their terminal. Public input is
only the final bank words; the complete source host fixes the incoming bank, and the verifier
fixes its local seed and terminal clocks. Auxiliary
components may supply calls and Byte providers, but cannot write the private bank channel.
The soundness theorem derives local specs and endpoint balance from constraints and the actual
balanced ledger. Its auxiliary premises are static circuit-interface/provider proofs, not
witness-specific semantic boundary facts. Installation in the mixed machine remains separate.
-/

namespace SP1Clean.Soundness.HostCommitEnsemble

open Circuit Air.Flat HostCommitChip Model.Core HostCommitBank

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Canonical field words for the selected bank of the actual incoming host. -/
def sourceValues (deferred : Bool) (source : HostState) : Vector (Word (ZMod p)) 8 :=
  (if deferred then source.deferred else source.committed).map fun value =>
    Target.bitVecToWord (value.setWidth 64)

/-- Installing the source bank changes no part of the actual incoming host state. -/
theorem source_apply (deferred : Bool) (source : HostState) :
    (HostCommitBoundary.start (sourceValues (p := p) deferred source)).apply deferred source = source := by
  cases deferred <;> simp [HostCommitBoundary.start, sourceValues, State.apply, State.decode,
    Vector.map_map, Function.comp_def, Target.toBitVec64_bitVecToWord]

def ensemble (deferred : Bool) (source : HostState) (auxiliary : List (Component (ZMod p)))
    (channels : List (RawChannel (ZMod p)))
    (names : ((components (p := p) deferred ++ auxiliary).map (·.circuit.name)).Nodup) :
    Ensemble (ZMod p) (ProvableVector Word 8) where
  tables := components deferred ++ auxiliary
  unique_names := names
  channels := (stateChannel deferred).toRaw :: Channels.byteChannel.toRaw ::
    HostCallChip.channel.toRaw :: Channels.publicValuesChannel.toRaw :: channels
  verifier := HostCommitBoundary.verifierProgram deferred (sourceValues deferred source)

variable {source : HostState} {deferred : Bool} {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}

variable {names : ((components (p := p) deferred ++ auxiliary).map (·.circuit.name)).Nodup}

abbrev Witness := EnsembleWitness (ensemble deferred source auxiliary channels names)

variable (witness : Witness (p := p) (deferred := deferred) (source := source)
  (auxiliary := auxiliary) (channels := channels) (names := names))

def bankTables :=
  witness.tables.take (components (p := p) deferred).length

theorem tables_aligned :
    List.Forall₂ (fun index table => (view deferred index).component = table.component) indices (bankTables witness) := by
  have viewsAligned : List.Forall₂ (fun view table => view.component = table.component)
      (views deferred) (bankTables witness) := by
    apply TransitionView.aligned_of_map_eq
    have same := congrArg (List.take (components (p := p) deferred).length) witness.tables_map_component
    simpa only [← List.map_take, ensemble, List.take_left', HostCommitBank.components, List.length_map, bankTables] using same.symm
  simpa only [views, List.forall₂_map_left_iff] using viewsAligned

theorem auxiliary_silent
    (privateChannel : ∀ component ∈ auxiliary, (stateChannel deferred).toRaw ∉ component.circuit.channels) :
    (witness.tables.drop (components (p := p) deferred).length).flatMap
      (·.interactionsWith witness.data (stateChannel deferred).toRaw) = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro table member
  have same := congrArg (List.drop (components (p := p) deferred).length) witness.tables_map_component
  have mapped : (witness.tables.drop (components (p := p) deferred).length).map (·.component) = auxiliary := by
    simpa only [← List.map_drop, ensemble, List.drop_left'] using same
  have componentMem := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
  rw [mapped] at componentMem
  rw [Table.interactionsWith_eq_filter]
  apply List.filter_eq_nil_iff.mpr
  intro interaction member equal
  have sameChannel : interaction.channel = (stateChannel deferred).toRaw := by simpa using equal
  exact privateChannel table.component componentMem
    (sameChannel ▸ table.channel_mem_channels_of_mem_interactions witness.data interaction member)

/-- The public verifier fixes the final bank words without a boundary premise. -/
theorem interactions_eq
    (privateChannel : ∀ component ∈ auxiliary, (stateChannel deferred).toRaw ∉ component.circuit.channels) :
    witness.interactionsWith (stateChannel deferred).toRaw =
      [(stateChannel deferred).pushedValue (HostCommitBoundary.start (sourceValues deferred source)),
       (stateChannel deferred).pulledValue (HostCommitBoundary.final witness.publicInput)] ++
        (bankTables witness).flatMap (·.interactionsWith witness.data (stateChannel deferred).toRaw) := by
  have verifier : witness.verifierInteractionsWith (stateChannel deferred).toRaw =
      [(stateChannel deferred).pushedValue (HostCommitBoundary.start (sourceValues deferred source)),
       (stateChannel deferred).pulledValue (HostCommitBoundary.final witness.publicInput)] := by
    simp only [EnsembleWitness.verifierInteractionsWith, Ensemble.verifierOperations, ensemble,
      Verifier.Program.circuitOperations, Verifier.Program.operations, HostCommitBoundary.verifierProgram]
    rw [Verifier.ofInteractions_values, HostCommitBoundary.verifier_values,
      ProvableType.eval_fromInput_varFromOffset_zero]
  simp only [EnsembleWitness.interactionsWith, verifier, EnsembleWitness.tableContext,
    TableContext.interactionsWith]
  have split := List.take_append_drop (components (p := p) deferred).length witness.tables
  rw [← split, List.flatMap_append, auxiliary_silent witness privateChannel, List.append_nil]
  rfl

private theorem bank_byte_requirements (index : Index) (env : Environment (ZMod p))
    (constraints : (view (p := p) deferred index).component.operations.ConstraintsHold env) :
    (view deferred index).component.operations.ChannelRequirements Channels.byteChannel.toRaw env := by
  apply Operations.requirements_of_not_mem _ _ _
    ((view deferred index).component.inChannelsOrRequirements_of_constraints env constraints)
  cases index with
  | none => simp [view, terminalView, HostCommitBoundary.terminal, stateChannel, Channels.byteChannel, circuit_norm]
  | some slot => simp [view, HostCommitHistory.view, HostCommitChip.circuit,
      stateChannel, HostCallChip.channel, Channels.byteChannel, Channels.publicValuesChannel, circuit_norm]

/-- The bank's Byte guarantees follow from actual ensemble balance and its auxiliary providers. -/
theorem byte_guarantees
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (providers : ∀ component ∈ auxiliary, ∀ env, component.operations.ConstraintsHold env →
      component.operations.ChannelRequirements Channels.byteChannel.toRaw env) :
    ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data Channels.byteChannel.toRaw := by
  apply (witness.channelGuarantees_of_component_requirements Channels.byteChannel.toRaw constraints
    (balanced _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) ?_ ?_).2
  · intro input data
    apply Ensemble.verifierChannelRequirements_of_not_mem
    simp [ensemble, HostCommitBoundary.verifierProgram, Verifier.ofInteractions,
      HostCommitBoundary.verifierMain, stateChannel, Channels.byteChannel, circuit_norm]
  · intro component member env checked
    change component ∈ components deferred ++ auxiliary at member
    rcases List.mem_append.mp member with bank | auxiliary
    · obtain ⟨bankView, viewMem, rfl⟩ := List.mem_map.mp bank
      obtain ⟨index, _, rfl⟩ := List.mem_map.mp viewMem
      exact bank_byte_requirements index env checked
    · exact providers component auxiliary env checked

/-- Constraints and balance authenticate the public bank as the result of all its physical calls.
The auxiliary interface proofs can be discharged once when this subsystem is installed. -/
theorem sound
    (privateChannel : ∀ component ∈ auxiliary, (stateChannel deferred).toRaw ∉ component.circuit.channels)
    (providers : ∀ component ∈ auxiliary, ∀ env, component.operations.ConstraintsHold env →
      component.operations.ChannelRequirements Channels.byteChannel.toRaw env)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (policy : HostPolicy) (characteristic : policy.characteristic = p)
    (context : HostReadContext) :
    ∃ path : List (Row (p := p)),
      path.Perm (TransitionView.readIndexedRows indices (bankTables witness) witness.data) ∧
      Walk.IsWalk (edge deferred) (HostCommitBoundary.start (sourceValues deferred source)) (HostCommitBoundary.final witness.publicInput) path ∧
      path.foldlM (execute deferred policy context) source =
        some ((HostCommitBoundary.final witness.publicInput).apply deferred source) := by
  have inTables (table : Table (ZMod p)) (member : table ∈ bankTables witness) : table ∈ witness.tables :=
    List.mem_of_mem_take member
  have bank := balanced (stateChannel deferred).toRaw (List.mem_cons_self ..)
  change BalancedInteractions (witness.interactionsWith (stateChannel deferred).toRaw) at bank
  rw [interactions_eq witness privateChannel] at bank
  have history := ordered_history deferred (bankTables witness) witness.data (sourceValues deferred source) witness.publicInput (tables_aligned witness)
    (fun table member => constraints table (inTables table member))
    (fun table member => byte_guarantees witness constraints balanced providers table (inTables table member))
    bank policy characteristic context source
  simpa only [source_apply] using history

end SP1Clean.Soundness.HostCommitEnsemble
