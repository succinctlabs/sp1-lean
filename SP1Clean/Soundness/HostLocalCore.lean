import SP1Clean.Soundness.ProtectedLocalCoreProjection
import SP1Clean.Soundness.HostCallProjection
import SP1Clean.Soundness.HostCallOrder

/-! # Local AIR with the instruction-to-host wrapper installed

The protected local assembly retains its source/final inventories, ordinary chips, and permission
provider. Its syscall component is replaced by the full-code/WRITE-read wrapper; host components
are appended before allocating the public source-check channel. State chronology projects
independently of their Memory effects and of changes to canonical data.
Auxiliary Byte requirements and State silence are static component-interface obligations.
Complete host execution, source-record authentication, and outgoing Memory currency remain open.
-/

namespace SP1Clean.Soundness.HostLocalCore

open Circuit Air.Flat Channels Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def tables (image : ProgramImage) (source : ExecutionSnapshot) (auxiliary : List (Component (ZMod p))) :=
  (ProtectedLocalCore.tables image source).set 58 HostCallLedger.producer ++ auxiliary

/-- The host wrapper replaces the syscall key; appended resources retain their own keys. -/
theorem tables_names (image : ProgramImage) (source : ExecutionSnapshot)
    (auxiliary : List (Component (ZMod p))) :
    (tables image source auxiliary).map (·.circuit.name) =
      ((ProtectedLocalCore.tables (p := p) image source).map (·.circuit.name)).set 58
        (HostCallLedger.producer (p := p)).circuit.name ++ auxiliary.map (·.circuit.name) := by
  simp only [tables, List.map_append, List.map_set]

/-- Install the complete physical inventory before choosing the source-check channel. -/
def baseEnsemble (image : ProgramImage) (source : ExecutionSnapshot)
    (auxiliary : List (Component (ZMod p))) (channels : List (RawChannel (ZMod p)))
    (names : ((tables image source auxiliary).map (·.circuit.name)).Nodup) : Ensemble (ZMod p) SP1PublicIO where
  tables := tables image source auxiliary
  unique_names := names
  channels := HostCallChip.channel.toRaw :: WritePermissionProvider.channel.toRaw ::
    (LocalCore.baseEnsemble image source).channels ++ channels
  verifier := LocalCore.boundaryVerifier

/-- Source assertions are authenticated on a channel fresh for the complete host assembly. -/
def ensemble (image : ProgramImage) (source : ExecutionSnapshot)
    (auxiliary : List (Component (ZMod p))) (channels : List (RawChannel (ZMod p)))
    (names : ((tables image source auxiliary).map (·.circuit.name)).Nodup) : Ensemble (ZMod p) SP1PublicIO :=
  (LocalSourceBoundary.checker image source).install (baseEnsemble image source auxiliary channels names)

theorem tables_length (image : ProgramImage) (source : ExecutionSnapshot) (auxiliary : List (Component (ZMod p))) :
    (tables image source auxiliary).length = 62 + auxiliary.length := by
  simp only [tables, List.length_append, List.length_set, ProtectedLocalCore.tables_length]

theorem core_component (image : ProgramImage) (source : ExecutionSnapshot)
    (auxiliary : List (Component (ZMod p))) (index : Fin 61) :
    (tables image source auxiliary)[index.val]'(by rw [tables_length]; omega) =
      if 58 = index.val then HostCallLedger.producer else
        (ProtectedLocalCore.tables image source)[index.val]'(by rw [ProtectedLocalCore.tables_length]; omega) := by
  simp only [tables]
  rw [List.getElem_append_left (by simp only [List.length_set, ProtectedLocalCore.tables_length]; omega),
    List.getElem_set]

omit [Fact (2 ^ 25 < p)] in
private theorem unchanged_projection (original extended : Component (ZMod p))
    (assertions : extended.operations.constraints = original.operations.constraints)
    (lookups : extended.operations.lookups = original.operations.lookups)
    (byte : extended.operations.interactionsWith byteChannel.toRaw = original.operations.interactionsWith byteChannel.toRaw)
    (state : extended.operations.interactionsWith stateChannel.toRaw = original.operations.interactionsWith stateChannel.toRaw) :
    (∀ env, extended.operations.ConstraintsHold env → original.operations.ConstraintsHold env) ∧
    (∀ env, extended.operations.ChannelGuarantees byteChannel.toRaw env → original.operations.ChannelGuarantees byteChannel.toRaw env) ∧
      original.operations.interactionsWith stateChannel.toRaw = extended.operations.interactionsWith stateChannel.toRaw := by
  refine ⟨?_, ?_, state.symm⟩
  · intro env checked
    simpa only [Operations.ConstraintsHold, assertions, lookups] using checked
  · intro env guarantees
    exact Operations.channelGuarantees_of_interactionsWith_subset _ _ _ (byte ▸ List.Subset.refl _) env guarantees

/-- Every retained component projects its constraints, Byte guarantees, and complete State ledger. -/
theorem component_projection (image : ProgramImage) (source : ExecutionSnapshot)
    (auxiliary : List (Component (ZMod p))) (index : Fin 61) :
    let extended := (tables image source auxiliary)[index.val]'(by rw [tables_length]; omega)
    let original := (LocalCore.tables (p := p) image source)[index.val]'(by rw [LocalCore.tables_length]; exact index.isLt)
    (∀ env, extended.operations.ConstraintsHold env → original.operations.ConstraintsHold env) ∧
    (∀ env, extended.operations.ChannelGuarantees byteChannel.toRaw env → original.operations.ChannelGuarantees byteChannel.toRaw env) ∧
      original.operations.interactionsWith stateChannel.toRaw = extended.operations.interactionsWith stateChannel.toRaw := by
  dsimp only
  rw [core_component]
  by_cases wrapper : 58 = index.val
  · have same : index = ⟨58, by decide⟩ := Fin.ext wrapper.symm
    subst index
    simp only [↓reduceIte]
    exact ⟨HostCallProjection.constraints_original, HostCallProjection.byte_guarantees,
      HostCallProjection.state_interactions⟩
  · rw [if_neg wrapper]
    have old := ProtectedLocalCore.component_projection (p := p) image source index
    exact unchanged_projection _ _ old.1 old.2.1
      (old.2.2 _ (by simp [byteChannel, WritePermissionProvider.channel, Channel.toRaw]))
      (old.2.2 _ (by simp [stateChannel, WritePermissionProvider.channel, Channel.toRaw]))

/-- Host tables can add arbitrary Memory effects. Their Byte requirements must follow locally,
and they do not contribute CPU State edges. These are static circuit-interface properties. -/
structure AuxiliaryInterface (auxiliary : List (Component (ZMod p))) : Prop where
  byte : ∀ component ∈ auxiliary, ∀ env, component.operations.ConstraintsHold env →
    component.operations.ChannelRequirements byteChannel.toRaw env
  state : ∀ component ∈ auxiliary, stateChannel.toRaw ∉ component.circuit.channels

omit [Fact (2 ^ 25 < p)] in
/-- Static channel interfaces compose over appended physical component blocks. -/
theorem AuxiliaryInterface.append {left right : List (Component (ZMod p))}
    (first : AuxiliaryInterface left) (second : AuxiliaryInterface right) :
    AuxiliaryInterface (left ++ right) := by
  constructor
  · intro component member env checked
    rcases List.mem_append.mp member with member | member
    · exact first.byte component member env checked
    · exact second.byte component member env checked
  · intro component member
    rcases List.mem_append.mp member with member | member
    · exact first.state component member
    · exact second.state component member

omit [Fact (2 ^ 25 < p)] in
/-- Restriction and reordering preserve a component-local interface. -/
theorem AuxiliaryInterface.of_subset {left right : List (Component (ZMod p))}
    (interface : AuxiliaryInterface right) (subset : left ⊆ right) : AuxiliaryInterface left :=
  ⟨fun component member => interface.byte component (subset member),
    fun component member => interface.state component (subset member)⟩

omit [Fact (2 ^ 25 < p)] in
/-- Most host components only consume Byte checks; their declared interfaces suffice. -/
theorem AuxiliaryInterface.of_channels (auxiliary : List (Component (ZMod p)))
    (byte : ∀ component ∈ auxiliary, byteChannel.toRaw ∉ component.circuit.channelsWithRequirements)
    (state : ∀ component ∈ auxiliary, stateChannel.toRaw ∉ component.circuit.channels) :
    AuxiliaryInterface auxiliary := by
  refine ⟨?_, state⟩
  intro component member env constraints
  exact Operations.requirements_of_not_mem _ _ _
    (component.inChannelsOrRequirements_of_constraints env constraints) _ (byte component member)

private theorem protected_byte_requirements (image : ProgramImage) (source : ExecutionSnapshot)
    (component : Component (ZMod p)) (member : component ∈ ProtectedLocalCore.tables image source)
    (env : Environment (ZMod p)) (constraints : component.operations.ConstraintsHold env) :
    component.operations.ChannelRequirements byteChannel.toRaw env := by
  obtain ⟨index, bound, rfl⟩ := List.mem_iff_getElem.mp member
  have limit : index < 62 := by simpa only [ProtectedLocalCore.tables_length] using bound
  by_cases core : index < 61
  · have projection := ProtectedLocalCore.component_projection (p := p) image source ⟨index, core⟩
    have original := LocalCore.component_byte_requirements image source
      ((LocalCore.tables image source)[index]'(by rw [LocalCore.tables_length]; exact core))
      (List.getElem_mem _) env (by
        simpa only [Operations.ConstraintsHold, projection.1, projection.2.1] using constraints)
    apply Operations.channelRequirements_of_interactionsWith_subset _ _ _ ?_ env original
    rw [projection.2.2 byteChannel.toRaw (by simp [byteChannel, WritePermissionProvider.channel, Channel.toRaw])]
    exact List.Subset.refl _
  · have last : index = 61 := by omega
    subst index
    apply Operations.requirements_of_not_mem _ _ _
      (((ProtectedLocalCore.tables image source)[61]).inChannelsOrRequirements_of_constraints env constraints)
    change byteChannel.toRaw ∉ [WritePermissionProvider.channel.toRaw]
    simp [byteChannel, WritePermissionProvider.channel, Channel.toRaw]

/-- Every physical Byte provider proves its own local requirement. -/
theorem component_byte_requirements (image : ProgramImage) (source : ExecutionSnapshot)
    (auxiliary : List (Component (ZMod p))) (interface : AuxiliaryInterface auxiliary)
    (component : Component (ZMod p))
    (member : component ∈ tables image source auxiliary)
    (env : Environment (ZMod p)) (constraints : component.operations.ConstraintsHold env) :
    component.operations.ChannelRequirements byteChannel.toRaw env := by
  rcases List.mem_append.mp member with core | extra
  · rcases List.mem_or_eq_of_mem_set core with original | rfl
    · exact protected_byte_requirements image source component original env constraints
    · apply Operations.requirements_of_not_mem _ _ _
        (HostCallLedger.producer.inChannelsOrRequirements_of_constraints env constraints)
      change byteChannel.toRaw ∉ [memoryChannel.toRaw, HostCallChip.channel.toRaw]
      simp [byteChannel, memoryChannel, HostCallChip.channel, Channel.toRaw]
  · exact interface.byte component extra env constraints

private theorem suffix_components (image : ProgramImage) (source : ExecutionSnapshot)
    (auxiliary : List (Component (ZMod p))) :
    (tables image source auxiliary).drop 61 = { circuit := WritePermissionProvider.circuit image } :: auxiliary := by
  have suffix : (ProtectedLocalCore.tables (p := p) image source).drop 61 =
      [{ circuit := WritePermissionProvider.circuit image }] := by
    rw [ProtectedLocalCore.tables, List.drop_left' (by
      simp only [List.length_set, LocalCore.tables_length])]
  rw [tables, List.drop_append_of_le_length (by
    simp only [List.length_set, ProtectedLocalCore.tables_length]; omega),
    List.drop_set_of_lt (by decide), suffix]
  rfl


private theorem component_other_interactions (image : ProgramImage) (source : ExecutionSnapshot)
    (auxiliary : List (Component (ZMod p))) (index : Fin 61) (channel : RawChannel (ZMod p))
    (notByte : channel ≠ byteChannel.toRaw) (notMemory : channel ≠ memoryChannel.toRaw)
    (notCall : channel ≠ HostCallChip.channel.toRaw) (notPermission : channel ≠ WritePermissionProvider.channel.toRaw) :
    ((LocalCore.tables (p := p) image source)[index.val]'(by rw [LocalCore.tables_length]; exact index.isLt)).operations.interactionsWith channel =
      ((tables image source auxiliary)[index.val]'(by rw [tables_length]; omega)).operations.interactionsWith channel := by
  rw [core_component]
  by_cases wrapper : 58 = index.val
  · have same : index = ⟨58, by decide⟩ := Fin.ext wrapper.symm
    subst index
    simp only [↓reduceIte]
    exact HostCallProjection.other_interactions channel notByte notMemory notCall
  · rw [if_neg wrapper]
    exact ((ProtectedLocalCore.component_projection (p := p) image source index).2.2 channel notPermission).symm


private theorem component_width_eq (image : ProgramImage) (source : ExecutionSnapshot)
    (auxiliary : List (Component (ZMod p))) (index : Fin 61) (unchanged : 58 ≠ index.val) :
    ((LocalCore.tables (p := p) image source)[index.val]'(by rw [LocalCore.tables_length]; exact index.isLt)).width =
      ((tables image source auxiliary)[index.val]'(by rw [tables_length]; omega)).width := by
  rw [core_component, if_neg unchanged]
  exact (ProtectedLocalCore.component_layout image source index).1

private theorem component_layout (image : ProgramImage) (source : ExecutionSnapshot)
    (auxiliary : List (Component (ZMod p))) (index : Fin 61) :
    let original := (LocalCore.tables (p := p) image source)[index.val]'(by rw [LocalCore.tables_length]; exact index.isLt)
    let extended := (tables image source auxiliary)[index.val]'(by rw [tables_length]; omega)
    original.width ≤ extended.width ∧ original.fixedColumns = extended.fixedColumns := by
  dsimp only
  rw [core_component]
  by_cases wrapper : 58 = index.val
  · have same : index = ⟨58, by decide⟩ := Fin.ext wrapper.symm
    subst index
    simp only [↓reduceIte]
    exact ⟨by exact of_decide_eq_true rfl, rfl⟩
  · rw [if_neg wrapper]
    have old := ProtectedLocalCore.component_layout (p := p) image source index
    exact ⟨old.1.le, old.2⟩

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
  {names : ((tables image source auxiliary).map (·.circuit.name)).Nodup}

/-- A physical witness for the installed host inventory and its public source-check verifier. -/
abbrev Witness := EnsembleWitness (ensemble image source auxiliary channels names)

variable (witness : Witness (image := image) (source := source)
  (auxiliary := auxiliary) (channels := channels) (names := names))

/-- The automatically separated source-check channel for this complete physical inventory. -/
abbrev sourceChannel := (LocalSourceBoundary.checker (p := p) image source).channel
  (baseEnsemble image source auxiliary channels names)

/-- Balance authenticates the same complete source contract as the local execution assembly. -/
theorem source_balanced_iff :
    witness.BalancedChannel (sourceChannel (names := names) (channels := channels)) ↔
      LocalSourceBoundary.Spec image source witness.publicInput := by
  apply Iff.trans ?_ ((LocalSourceBoundary.checker image source).program_balanced_iff
    (baseEnsemble image source auxiliary channels names) witness.publicInput witness.data |>.trans ?_)
  · exact (congrArg BalancedInteractions
      ((LocalSourceBoundary.checker image source).installed_check_interactions
        (ens := baseEnsemble image source auxiliary channels names) witness)).to_iff
  · rw [LocalSourceBoundary.checks_iff]
    exact and_iff_right (LocalSourceBoundary.count_bound image source)

private theorem projectionLength :
    (LocalCore.ensemble (p := p) image source).tables.length ≤
      (ensemble image source auxiliary channels names).tables.length := by
  change (LocalCore.tables (p := p) image source).length ≤ (tables image source auxiliary).length
  rw [LocalCore.tables_length, tables_length]
  omega

private theorem projectionWidths (index : Fin (LocalCore.ensemble (p := p) image source).tables.length) :
    (LocalCore.ensemble (p := p) image source).tables[index.val].width ≤
      ((ensemble image source auxiliary channels names).tables[index.val]'(by
        have := projectionLength (names := names) (channels := channels); omega)).width :=
  (component_layout image source auxiliary ⟨index.val, by
    simpa only [LocalCore.tables_length] using (show index.val < (LocalCore.tables (p := p) image source).length from index.isLt)⟩).1

private theorem projectionFixed (index : Fin (LocalCore.ensemble (p := p) image source).tables.length) :
    (LocalCore.ensemble (p := p) image source).tables[index.val].fixedColumns =
      ((ensemble image source auxiliary channels names).tables[index.val]'(by
        have := projectionLength (names := names) (channels := channels); omega)).fixedColumns :=
  (component_layout image source auxiliary ⟨index.val, by
    simpa only [LocalCore.tables_length] using (show index.val < (LocalCore.tables (p := p) image source).length from index.isLt)⟩).2

private theorem projectionWidth_eq (index : Fin (LocalCore.ensemble (p := p) image source).tables.length)
    (unchanged : 58 ≠ index.val) :
    (LocalCore.ensemble (p := p) image source).tables[index.val].width =
      ((ensemble image source auxiliary channels names).tables[index.val]'(by
        have := projectionLength (names := names) (channels := channels); omega)).width :=
  component_width_eq image source auxiliary ⟨index.val, by
    simpa only [LocalCore.tables_length] using (show index.val < (LocalCore.tables (p := p) image source).length from index.isLt)⟩ unchanged

/-- Keep each original component's physical prefix and derive its canonical data from those rows. -/
def localWitness : EnsembleWitness (LocalCore.ensemble (p := p) image source) :=
  witness.projectPrefix (LocalCore.ensemble (p := p) image source) projectionLength projectionWidths projectionFixed

@[simp] theorem localWitness_publicInput : (localWitness witness).publicInput = witness.publicInput := rfl

/-- Non-wrapper components retain every complete physical row under their original interpretation. -/
theorem localWitness_table (index : Fin 61) (unchanged : 58 ≠ index.val) :
    (localWitness witness).tables[index.val]'(by
      rw [← (localWitness witness).same_length]
      change index.val < (LocalCore.tables (p := p) image source).length
      rw [LocalCore.tables_length]; exact index.isLt) =
      (witness.tables[index.val]'(by
        rw [← witness.same_length]; change index.val < (tables image source auxiliary).length
        rw [tables_length]; omega)).withComponent
        ((LocalCore.tables image source)[index.val]'(by rw [LocalCore.tables_length]; exact index.isLt))
        (by rw [← witness.same_circuits]; exact component_width_eq image source auxiliary index unchanged)
        (by rw [← witness.same_circuits]; exact (component_layout image source auxiliary index).2) := by
  rw [localWitness, witness.projectPrefix_getElem (index := ⟨index.val, by
    change index.val < (LocalCore.tables (p := p) image source).length
    rw [LocalCore.tables_length]; exact index.isLt⟩)]
  rw [Table.ext_iff]
  refine ⟨rfl, ?_⟩
  apply Table.projectPrefix_rows_of_width_eq
  rw [← witness.same_circuits]
  exact component_width_eq image source auxiliary index unchanged

theorem localWitness_constraints (constraints : witness.Constraints) : (localWitness witness).Constraints := by
  apply witness.projectPrefix_constraints_of (target := LocalCore.ensemble image source)
    projectionLength projectionWidths projectionFixed ?_ constraints
  intro index row rowWidth checked
  have bound : index.val < 61 := by
    simpa only [LocalCore.tables_length] using (show index.val < (LocalCore.tables (p := p) image source).length from index.isLt)
  change ((tables image source auxiliary)[index.val]'(by rw [tables_length]; omega)).operations.ConstraintsHold
    (Environment.fromArray row witness.data) at checked
  by_cases wrapper : 58 = index.val
  · have same : index = ⟨58, by change 58 < (LocalCore.tables (p := p) image source).length; rw [LocalCore.tables_length]; decide⟩ := Fin.ext wrapper.symm
    subst index
    rw [core_component image source auxiliary ⟨58, by decide⟩, if_pos rfl] at checked
    exact HostCallProjection.constraints_prefix row witness.data (localWitness witness).data checked
  · rw [projectionWidth_eq (names := names) (channels := channels) index wrapper, ← rowWidth, Array.extract_size]
    exact LocalCore.component_constraints_setData image source _ (List.getElem_mem _)
      ((component_projection image source auxiliary ⟨index.val, bound⟩).1 _ checked)

private theorem base_channel_registered (channel : RawChannel (ZMod p))
    (member : channel ∈ (LocalCore.baseEnsemble image source).channels) :
    channel ∈ (baseEnsemble image source auxiliary channels names).channels :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ member))

/-- Registered base channels retain their actual public-verifier ledger after physical projection. -/
theorem localWitness_verifier_interactions (channel : RawChannel (ZMod p))
    (member : channel ∈ (LocalCore.baseEnsemble image source).channels) :
    (localWitness witness).verifierInteractionsWith channel = witness.verifierInteractionsWith channel := by
  change (LocalCore.ensemble (p := p) image source).verifierOperations.interactionValuesWith channel
    (Environment.fromInput witness.publicInput (localWitness witness).data) =
      (ensemble image source auxiliary channels names).verifierOperations.interactionValuesWith channel
        (Environment.fromInput witness.publicInput witness.data)
  change ((LocalSourceBoundary.checker image source).install (LocalCore.baseEnsemble image source)).verifierOperations.interactionValuesWith channel
    (Environment.fromInput witness.publicInput (localWitness witness).data) =
      ((LocalSourceBoundary.checker image source).install (baseEnsemble image source auxiliary channels names)).verifierOperations.interactionValuesWith channel
        (Environment.fromInput witness.publicInput witness.data)
  rw [PublicVerifier.install_verifier_interactions_of_mem _ _ _ _ member,
    PublicVerifier.install_verifier_interactions_of_mem _ _ _ _ (base_channel_registered channel member)]
  exact Operations.interactionValuesWith_congr rfl

/-- Channels unaffected by the wrappers retain their complete registered ledger. -/
theorem localWitness_other (channel : RawChannel (ZMod p))
    (registered : channel ∈ (LocalCore.baseEnsemble image source).channels)
    (notByte : channel ≠ byteChannel.toRaw) (notMemory : channel ≠ memoryChannel.toRaw)
    (notCall : channel ≠ HostCallChip.channel.toRaw) (notPermission : channel ≠ WritePermissionProvider.channel.toRaw)
    (silent : ∀ component ∈ auxiliary, channel ∉ component.circuit.channels) :
    (localWitness witness).interactionsWith channel = witness.interactionsWith channel := by
  have physical := witness.projectPrefix_tables_interactions (target := LocalCore.ensemble image source)
    projectionLength projectionWidths projectionFixed channel ?_
  · change (localWitness witness).tables.flatMap (·.interactionsWith (localWitness witness).data channel) =
      (witness.tables.take (LocalCore.ensemble (p := p) image source).tables.length).flatMap (·.interactionsWith witness.data channel) at physical
    simp only [EnsembleWitness.interactionsWith, EnsembleWitness.tableContext, TableContext.interactionsWith]
    rw [localWitness_verifier_interactions witness channel registered, physical]
    congr 1
    conv_rhs => rw [← List.take_append_drop (LocalCore.ensemble (p := p) image source).tables.length witness.tables]
    rw [List.flatMap_append]
    have empty : (witness.tables.drop (LocalCore.ensemble (p := p) image source).tables.length).flatMap
        (·.interactionsWith witness.data channel) = [] := by
      change (witness.tables.drop (LocalCore.tables image source).length).flatMap _ = []
      rw [LocalCore.tables_length]
      apply List.flatMap_eq_nil_iff.mpr
      intro table member
      have mapped := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
      rw [List.map_drop, witness.tables_map_component] at mapped
      change table.component ∈ (tables image source auxiliary).drop 61 at mapped
      rw [suffix_components] at mapped
      apply table.interactionsWith_nil_of_channel_not_mem
      rcases List.mem_cons.mp mapped with same | extra
      · rw [same]
        change channel ∉ [WritePermissionProvider.channel.toRaw]
        simpa only [List.mem_singleton] using notPermission
      · exact silent table.component extra
    rw [empty, List.append_nil]
  · intro index row rowWidth
    have bound : index.val < 61 := by
      simpa only [LocalCore.tables_length] using (show index.val < (LocalCore.tables (p := p) image source).length from index.isLt)
    by_cases wrapper : 58 = index.val
    · have same : index = ⟨58, by change 58 < (LocalCore.tables (p := p) image source).length; rw [LocalCore.tables_length]; decide⟩ := Fin.ext wrapper.symm
      subst index
      change HostCallProjection.original.operations.interactionValuesWith channel _ =
        ((tables image source auxiliary)[58]'(by rw [tables_length]; omega)).operations.interactionValuesWith channel _
      rw [core_component image source auxiliary ⟨58, by decide⟩, if_pos rfl]
      exact HostCallProjection.other_values_prefix row witness.data (localWitness witness).data channel notByte notMemory notCall
    · rw [projectionWidth_eq (names := names) (channels := channels) index wrapper, ← rowWidth, Array.extract_size]
      have projected := component_other_interactions image source auxiliary ⟨index.val, bound⟩ channel notByte notMemory notCall notPermission
      change (LocalCore.ensemble (p := p) image source).tables[index.val].operations.interactionsWith channel =
        ((ensemble image source auxiliary channels names).tables[index.val]'(by
          have := projectionLength (names := names) (channels := channels); omega)).operations.interactionsWith channel at projected
      exact (congrArg (List.map (AbstractInteraction.eval
        (Environment.fromArray row (localWitness witness).data))) projected).trans
          (List.map_congr_left fun interaction _ => AbstractInteraction.eval_congr rfl)

/-- Host effects preserve the complete State ledger, including every repeated or disabled edge. -/
theorem localWitness_state (interface : AuxiliaryInterface auxiliary) :
    (localWitness witness).interactionsWith stateChannel.toRaw = witness.interactionsWith stateChannel.toRaw :=
  localWitness_other witness stateChannel.toRaw (by simp [LocalCore.baseEnsemble, sp1Ensemble_channels])
    (by simp [stateChannel, byteChannel, Channel.toRaw])
    (by simp [stateChannel, memoryChannel, Channel.toRaw])
    (by simp [stateChannel, HostCallChip.channel, Channel.toRaw])
    (by simp [stateChannel, WritePermissionProvider.channel, Channel.toRaw]) interface.state

/-- The full Program ledger survives when auxiliary host components do not emit fetches. -/
theorem localWitness_program
    (silent : ∀ component ∈ auxiliary, programChannel.toRaw ∉ component.circuit.channels) :
    (localWitness witness).interactionsWith programChannel.toRaw = witness.interactionsWith programChannel.toRaw :=
  localWitness_other witness programChannel.toRaw (by simp [LocalCore.baseEnsemble, sp1Ensemble_channels])
    (by simp [programChannel, byteChannel, Channel.toRaw])
    (by simp [programChannel, memoryChannel, Channel.toRaw])
    (by simp [programChannel, HostCallChip.channel, Channel.toRaw])
    (by simp [programChannel, WritePermissionProvider.channel, Channel.toRaw]) silent

/-- Fixed snapshot membership retains its physical rows and complete private ledger. -/
theorem localWitness_membership (channel : RawChannel (ZMod p))
    (known : channel ∈ SnapshotMemoryEnsemble.membershipChannels source.sail.memorySnapshot)
    (silent : ∀ component ∈ auxiliary, channel ∉ component.circuit.channels) :
    (localWitness witness).interactionsWith channel = witness.interactionsWith channel := by
  simp only [SnapshotMemoryEnsemble.membershipChannels, List.mem_cons,
    List.not_mem_nil, or_false] at known
  rcases known with rfl | rfl
  all_goals
    apply localWitness_other witness _ (by simp [LocalCore.baseEnsemble])
    · simp [StaticTable.channel, InitialMemoryLookup.membership, MemorySnapshot.registerTable,
        StaticTable.ofRows, byteChannel, Channel.toRaw]
    · simp [StaticTable.channel, InitialMemoryLookup.membership, MemorySnapshot.registerTable,
        StaticTable.ofRows, memoryChannel, Channel.toRaw]
    · simp [StaticTable.channel, InitialMemoryLookup.membership, MemorySnapshot.registerTable,
        StaticTable.ofRows, HostCallChip.channel, Channel.toRaw]
    · simp [StaticTable.channel, InitialMemoryLookup.membership, MemorySnapshot.registerTable,
        StaticTable.ofRows, WritePermissionProvider.channel, Channel.toRaw]
    · exact silent

omit [Fact (2 ^ 25 < p)] in
/-- Byte predicates depend on their message cells, not on canonical prover data. -/
private theorem byte_guarantees_setData (ops : Operations (ZMod p)) (row : Array (ZMod p))
    (data data' : ProverData (ZMod p))
    (guarantees : ops.ChannelGuarantees byteChannel.toRaw (Environment.fromArray row data)) :
    ops.ChannelGuarantees byteChannel.toRaw (Environment.fromArray row data') := by
  intro interaction member same
  have kept := guarantees interaction member same
  rw [← AbstractInteraction.eval_guarantees,
    AbstractInteraction.eval_congr (env := Environment.fromArray row data')
      (env' := Environment.fromArray row data) (i := interaction) rfl]
  rcases interaction with ⟨declared, mult, msg, assume⟩
  cases same
  simpa only [Interaction.Guarantees, AbstractInteraction.eval, AbstractInteraction.Guarantees,
    Interaction.msgVector, byteChannel, Channel.toRaw] using kept

/-- Transfer Byte guarantees at the projected canonical data; Byte balance need not project. -/
theorem localWitness_byte_of_guarantees
    (byte : ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data byteChannel.toRaw) :
    ∀ table ∈ (localWitness witness).tables,
      table.ChannelGuarantees (localWitness witness).data byteChannel.toRaw := by
  apply witness.projectPrefix_channelGuarantees_of (target := LocalCore.ensemble image source)
    projectionLength projectionWidths projectionFixed byteChannel.toRaw ?_ byte
  intro index row rowWidth guaranteed
  have bound : index.val < 61 := by
    simpa only [LocalCore.tables_length] using (show index.val < (LocalCore.tables (p := p) image source).length from index.isLt)
  change ((tables image source auxiliary)[index.val]'(by rw [tables_length]; omega)).operations.ChannelGuarantees
    byteChannel.toRaw (Environment.fromArray row witness.data) at guaranteed
  by_cases wrapper : 58 = index.val
  · have same : index = ⟨58, by change 58 < (LocalCore.tables (p := p) image source).length; rw [LocalCore.tables_length]; decide⟩ := Fin.ext wrapper.symm
    subst index
    rw [core_component image source auxiliary ⟨58, by decide⟩, if_pos rfl] at guaranteed
    exact HostCallProjection.byte_guarantees_prefix row witness.data (localWitness witness).data guaranteed
  · rw [projectionWidth_eq (names := names) (channels := channels) index wrapper, ← rowWidth, Array.extract_size]
    exact byte_guarantees_setData _ row witness.data (localWitness witness).data
      ((component_projection image source auxiliary ⟨index.val, bound⟩).2.1 _ guaranteed)

/-- Public Byte guarantees also transport through the actual verifier ledger. -/
theorem localWitness_verifier_byte
    (byte : (ensemble image source auxiliary channels names).VerifierChannelGuarantees
      witness.publicInput witness.data byteChannel.toRaw) :
    (LocalCore.ensemble (p := p) image source).VerifierChannelGuarantees
      (localWitness witness).publicInput (localWitness witness).data byteChannel.toRaw := by
  rw [EnsembleWitness.verifierChannelGuarantees_iff_forall] at byte ⊢
  intro interaction member
  have kept := byte interaction (by
    rw [← localWitness_verifier_interactions witness byteChannel.toRaw (by simp [LocalCore.baseEnsemble, sp1Ensemble_channels])]
    exact member)
  have channel := EnsembleWitness.channel_eq_of_mem_interactionsWith
    (EnsembleWitness.mem_interactionsWith.mpr (Or.inl member))
  rcases interaction with ⟨declared, mult, msg⟩
  cases channel
  exact kept

/-- Public boundary emissions supply their own requirements, independently of witness acceptance. -/
theorem verifier_requirements (env : Environment (ZMod p)) :
    (ensemble image source auxiliary channels names).verifierOperations.FullRequirements env := by
  change (LocalCore.boundaryVerifier.andThen ((LocalSourceBoundary.checker image source).program
    (baseEnsemble image source auxiliary channels names))).circuitOperations.FullRequirements env
  rw [Verifier.Program.andThen_requirements]
  exact ⟨LocalCore.boundaryVerifier_requirements env, Verifier.checkZeros_requirements _ _ _⟩

/-- Byte closure includes the public verifier and every physical table separately. -/
theorem byte_guarantees (interface : AuxiliaryInterface auxiliary) (constraints : witness.Constraints)
    (balanced : witness.BalancedChannel byteChannel.toRaw) :
    (ensemble image source auxiliary channels names).VerifierChannelGuarantees
      witness.publicInput witness.data byteChannel.toRaw ∧
      ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data byteChannel.toRaw := by
  apply witness.channelGuarantees_of_component_requirements byteChannel.toRaw constraints balanced
  · intro input data interaction emitted _
    exact verifier_requirements _ interaction emitted
  · exact component_byte_requirements image source auxiliary interface

/-- Physical Byte guarantees inherited from the complete assembly's own closure. -/
theorem localWitness_byte (interface : AuxiliaryInterface auxiliary) (constraints : witness.Constraints)
    (balanced : witness.BalancedChannel byteChannel.toRaw) :
    ∀ table ∈ (localWitness witness).tables,
      table.ChannelGuarantees (localWitness witness).data byteChannel.toRaw :=
  localWitness_byte_of_guarantees witness (byte_guarantees witness interface constraints balanced).2

/-- Chronology uses actual verifier/physical Byte guarantees, source-check balance and State balance. -/
theorem orderingChannels_of_guarantees (interface : AuxiliaryInterface auxiliary)
    (verifierByte : (ensemble image source auxiliary channels names).VerifierChannelGuarantees
      witness.publicInput witness.data byteChannel.toRaw)
    (byte : ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data byteChannel.toRaw)
    (sourceChecks : witness.BalancedChannel (sourceChannel (names := names) (channels := channels)))
    (state : witness.BalancedChannel stateChannel.toRaw) : LocalCore.OrderingChannels (localWitness witness) := by
  refine ⟨localWitness_verifier_byte witness verifierByte, localWitness_byte_of_guarantees witness byte, ?_, ?_⟩
  · exact (LocalCore.source_balanced_iff (localWitness witness)).mpr ((source_balanced_iff witness).mp sourceChecks)
  · change BalancedInteractions ((localWitness witness).interactionsWith stateChannel.toRaw)
    rw [localWitness_state witness interface]
    exact state

/-- The complete assembly supplies all chronology evidence through its own constraints and balance. -/
theorem orderingChannels (interface : AuxiliaryInterface auxiliary) (constraints : witness.Constraints)
    (balanced : witness.BalancedChannels) : LocalCore.OrderingChannels (localWitness witness) := by
  have byte := byte_guarantees witness interface constraints (balanced _ (by
    simp [ensemble, PublicVerifier.install, baseEnsemble, LocalCore.baseEnsemble, sp1Ensemble_channels]))
  exact orderingChannels_of_guarantees witness interface byte.1 byte.2
    (balanced _ (List.mem_append_right _ (List.mem_singleton_self _)))
    (balanced _ (by simp [ensemble, PublicVerifier.install, baseEnsemble, LocalCore.baseEnsemble, sp1Ensemble_channels]))

/-- Reuse the exhaustive CPU walk at the same public endpoints and actual host canonical data. -/
theorem executionRows_ordered_of_orderingChannels
    (constraints : witness.Constraints) (ordering : LocalCore.OrderingChannels (localWitness witness)) :
    ∃ ordered : List (NativeCore.ExecutionRow p), ordered.Perm (LocalCore.executionRows (localWitness witness)) ∧
      Walk.IsWalk (NativeCore.ExecutionRow.canonEdge witness.data)
        (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) ordered := by
  have edge : NativeCore.ExecutionRow.canonEdge (localWitness witness).data =
      NativeCore.ExecutionRow.canonEdge witness.data := by
    exact funext fun row => row.canonEdge_setData _ _
  have publicEq : (localWitness witness).publicInput = witness.publicInput := rfl
  simpa only [edge, publicEq] using LocalCore.executionRows_ordered_of_orderingChannels (localWitness witness)
    (localWitness_constraints witness constraints) ordering

/-- An exhaustive CPU walk retains every host-call instruction and all host RAM effects. -/
theorem executionRows_ordered (interface : AuxiliaryInterface auxiliary) (constraints : witness.Constraints)
    (balanced : witness.BalancedChannels) :
    ∃ ordered : List (NativeCore.ExecutionRow p), ordered.Perm (LocalCore.executionRows (localWitness witness)) ∧
      Walk.IsWalk (NativeCore.ExecutionRow.canonEdge witness.data)
        (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) ordered :=
  executionRows_ordered_of_orderingChannels witness constraints (orderingChannels witness interface constraints balanced)

/-- The installed syscall wrapper's actual physical table. -/
def hostCallTable : Table (ZMod p) :=
  witness.tables[58]'(by
    rw [← witness.same_length]
    change 58 < (tables image source auxiliary).length
    rw [tables_length]
    omega)

theorem hostCallTable_component : (hostCallTable witness).component = HostCallLedger.producer := by
  rw [hostCallTable, ← witness.same_circuits]
  exact (core_component image source auxiliary ⟨58, by decide⟩).trans (if_pos rfl)

theorem hostCallTable_mem : hostCallTable witness ∈ witness.tables := List.getElem_mem _

/-- The active instruction inventory is decoded from the same actual rows, including padding. -/
theorem hostCallTable_projection :
    ((HostCallLedger.activeRows (hostCallTable witness) witness.data).map fun env => (HostCallLedger.input env).instruction) =
      activeSystemRows (LocalCore.systemTable (localWitness witness) 3)
        (syscallInstrsRow (localWitness witness).data) (·.is_real) := by
  have rows : (LocalCore.systemTable (localWitness witness) 3).table =
      (hostCallTable witness).table.map (·.extract 0 (HostCallProjection.original (p := p)).width) := by
    rfl
  simp only [HostCallLedger.activeRows, activeSystemRows, rows,
    List.map_map, List.filter_map, Function.comp_def]
  have decode (row : Array (ZMod p)) :
      syscallInstrsRow (localWitness witness).data (row.extract 0 (HostCallProjection.original (p := p)).width) =
        (HostCallLedger.input (Environment.fromArray row witness.data)).instruction :=
    HostCallProjection.input_prefix row witness.data (localWitness witness).data
  simp only [decode]
  congr 1
  apply List.filter_congr
  intro row _
  exact decide_eq_decide.mpr Iff.rfl

/-- Host-call clock uniqueness follows from CPU chronology on the actual projected rows. -/
theorem hostCalls_clocks_nodup_of_orderingChannels
    (constraints : witness.Constraints) (ordering : LocalCore.OrderingChannels (localWitness witness)) :
    ((HostCallLedger.calls (hostCallTable witness) witness.data).map HostCallLedger.clock).Nodup :=
  LocalCore.hostCalls_clocks_nodup_of_orderingChannels (localWitness witness)
    (localWitness_constraints witness constraints) ordering
    (hostCallTable witness) witness.data (hostCallTable_projection witness)

/-- Distinct wrapper call clocks follow from the extended AIR's own constraints and balance. -/
theorem hostCalls_clocks_nodup (interface : AuxiliaryInterface auxiliary) (constraints : witness.Constraints)
    (balanced : witness.BalancedChannels) :
    ((HostCallLedger.calls (hostCallTable witness) witness.data).map HostCallLedger.clock).Nodup :=
  hostCalls_clocks_nodup_of_orderingChannels witness constraints (orderingChannels witness interface constraints balanced)

end SP1Clean.Soundness.HostLocalCore
