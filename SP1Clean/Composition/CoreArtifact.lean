import SP1Clean.Composition.CoreEnsemble
import SP1Clean.Soundness.AIR

/-! # Exact Core artifact at the native semantic boundary

`CoreEnsemble.lean` constructs the complete fifty-three-table native witness and proves all of its local
constraints.  This module names the remaining global translation endpoint that the exact-AIR /
verifier integration must discharge before that witness can enter the native semantic soundness
theorem.

The endpoint is intentionally explicit.  For every channel of the native ensemble it requires the
exact interaction count bound used by Clean.  Integer balance remains an explicit input only for
State and Memory; Byte and Program are derived from the native-consumer recount.  It separately
requires `SemanticBoundaryBinding`, an explicit contract connecting the committed program to the
provider/boundary meaning.  None of these fields is claimed to follow merely from the two
exact cluster relations, `ExactProviderTransportContract`, or `ExactNativeBoundaryContract`.
The Type-valued preprocessing inventory remains a visible construction argument rather than data
hidden behind any Prop-valued contract.

Once the integration layer combines ArkLib/exact-AIR balance extraction with the explicit
loader/platform/program/memory-boundary contracts to supply that global contract, the rest is
kernel-checked plumbing:
integer balance is converted to Clean's field-valued `BalancedChannels`, the already-proved local
constraints and semantic binding assemble `SupportedCoreNativeRelation`, and
`supported_core_native_sound` yields an official-Sail local execution segment.  No boot
reachability, shard composition, or cryptographic verifier theorem is asserted here.
-/

set_option autoImplicit false

namespace SP1Clean.Composition

-- The faithfulness vocabulary (`ChipOracle`, `ChipFaithful`, `ChipRowCodec`,
-- `nativeAccesses`) is at the stratum below; this namespace no longer encloses it since the
-- 2026-08 move out of `Faithful/Transport/`.
open SP1Clean.Faithful

open Circuit
open Air.Flat (EnsembleWitness)
open SP1Clean.Execution
open SP1Clean.LookupAccessList (LookupKey)
open SP1Clean.Soundness.Target

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance coreArtifactFieldBound : Fact (2 ^ 24 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Pair the caller-supplied program (whose authentication remains an explicit global obligation)
with the fourteen native boundary cells projected from the exact shard public values. -/
def exactNativeStatement {Digest : Type} (program : GuestProgram)
    (statement : SP1ShardStatement (ZMod p) Digest) : Soundness.SupportedCoreStatement p :=
  ⟨program, exactNativeBoundary statement.publicValues⟩

/-- **The remaining integration-to-native global translation endpoint.**

This contract is stated directly about the constructed fifty-three-table witness.  Its remaining
integer-balance field is the native `ℤ` balance property for State and Memory, before conversion to
Clean's field-valued balance; the separate
count field is exactly Clean's no-wrap premise.  `semanticBoundary` binds the projected public
boundary and the shared `ProverData` to the caller's program and a concrete initial Sail state.

An integration must derive `interactionCount` and `remainingIntegerBalance` from its PCS-authenticated
full-AIR witness and interaction argument.  It must derive `semanticBoundary` separately from
PCS-authenticated preprocessing together with explicit loader, platform, code-memory, program, and memory-boundary
contracts.  This structure records both obligations; it does not postulate that local AIR constraints
or ArkLib knowledge extraction alone imply them. -/
structure ExactNativeGlobalContract {Digest : Type}
    (program : GuestProgram) (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) : Prop where
  /-- The exact number of evaluated interactions on each native ensemble channel is smaller than
  the field characteristic. -/
  interactionCount : ∀ channel ∈ (Soundness.sp1Ensemble (p := p)).channels,
    ((exactNativeEnsembleWitness statement executionWitness memoryBoundaryWitness inventory data hint
      ).interactionsWith channel).length < p
  /-- The projected State and Memory access ledgers balance over the integers.  Byte and Program
  are deliberately absent: `exactNativeAllCleanAccesses_preprocessedBalance` derives them from the
  native recount contract. -/
  remainingIntegerBalance : ∀ channel,
    (channel = Channels.stateChannel.toRaw ∨ channel = Channels.memoryChannel.toRaw) →
    SP1Clean.LookupAccessList.isConsistentBalanced
      (((exactNativeEnsembleWitness statement executionWitness memoryBoundaryWitness inventory data hint
        ).interactionsWith channel).map Interaction.toAccess)
  /-- The shared prover data and providers describe the caller's program and the public initial
  boundary describes a concrete compatible Sail state. -/
  semanticBoundary : Soundness.SemanticBoundaryBinding
    (exactNativeStatement program statement)
    (exactNativeEnsembleWitness statement executionWitness memoryBoundaryWitness inventory data hint)

/-! ## Full-ledger to per-channel bridge -/

/-- Every supported instruction component declares only the four native ensemble channels. -/
private theorem instructionComponent_channels_subset
    (component : Air.Flat.Component (ZMod p))
    (componentMem : component ∈ Soundness.sp1Tables (p := p)) :
    component.circuit.channels ⊆ (Soundness.sp1Ensemble (p := p)).channels := by
  rw [Soundness.sp1Ensemble_channels]
  simp only [Soundness.sp1Tables, List.mem_map] at componentMem
  obtain ⟨chip, chipMem, rfl⟩ := componentMem
  exact Soundness.supportedChip_usesSupportedBusChannels chip chipMem

/-- Every native provider/boundary component also declares only the four ensemble channels. -/
private theorem providerComponent_channels_subset
    (component : Air.Flat.Component (ZMod p))
    (componentMem : component ∈ Soundness.sp1ProviderTables (p := p)) :
    component.circuit.channels ⊆ (Soundness.sp1Ensemble (p := p)).channels := by
  rw [Soundness.sp1Ensemble_channels]
  simp only [Soundness.sp1ProviderTables, List.mem_append] at componentMem
  rcases componentMem with (componentMem | componentMem) | componentMem
  · fin_cases componentMem <;>
      simp [GeneralFormalCircuit.channels, ByteChip.U8Range.circuit, ByteChip.MSB.circuit,
        ByteChip.AndByte.circuit, ByteChip.OrByte.circuit, ByteChip.XorByte.circuit,
        ByteChip.Ltu.circuit, circuit_norm]
  · simp only [Soundness.sp1RangeProviderTables, List.mem_map] at componentMem
    obtain ⟨width, -, rfl⟩ := componentMem
    simp [GeneralFormalCircuit.channels, RangeChip.circuitFor, RangeChip.circuit, circuit_norm]
  · fin_cases componentMem <;>
      simp [GeneralFormalCircuit.channels, ProgramProviderChip.circuit,
        MemoryProviderChip.circuit, MemoryFinalizeChip.circuit, MemoryBumpChip.circuit,
        StateBumpChip.circuit, circuit_norm]

/-- Every component of the concrete native ensemble is statically confined to its four channels. -/
private theorem ensembleComponent_channels_subset
    (component : Air.Flat.Component (ZMod p))
    (componentMem : component ∈ (Soundness.sp1Ensemble (p := p)).allTables) :
    component.circuit.channels ⊆ (Soundness.sp1Ensemble (p := p)).channels := by
  simp only [Air.Flat.Ensemble.allTables, List.mem_cons] at componentMem
  rcases componentMem with rfl | componentMem
  · change (Soundness.sp1StateVerifier (p := p)).channels ⊆ _
    rw [GeneralFormalCircuit.channels,
      show (Soundness.sp1StateVerifier (p := p)).channelsWithGuarantees =
        [Channels.stateChannel.toRaw, Channels.byteChannel.toRaw] from rfl,
      show (Soundness.sp1StateVerifier (p := p)).channelsWithRequirements = [] from rfl,
      Soundness.sp1Ensemble_channels]
    simp
  · rw [Soundness.sp1Ensemble_tables] at componentMem
    rcases List.mem_append.mp componentMem with instructionMem | providerMem
    · exact instructionComponent_channels_subset _ instructionMem
    · exact providerComponent_channels_subset _ providerMem

omit [Fact (2 ^ 25 < p)] in
/-- An evaluated table interaction uses a channel declared by its component. -/
private theorem tableInteraction_channel_mem
    (table : Air.Flat.Table (ZMod p))
    {interaction : Interaction (ZMod p)} (interactionMem : interaction ∈ table.interactions) :
    interaction.channel ∈ table.component.circuit.channels := by
  have all := (Air.Flat.Table.forall_interactions_iff table
    (fun i => i.channel ∈ table.component.circuit.channels)).2 (by
      intro row rowMem abstractInteraction abstractMem
      apply table.component.circuit.channels_subset table.component.rowInputVar
        table.component.rowOffset
      simp only [Operations.channels, List.mem_map]
      refine ⟨abstractInteraction, ?_, rfl⟩
      rw [Air.Flat.Component.interactions_eq] at abstractMem
      simpa only [Air.Flat.Component.rowOperations, Air.Flat.Component.rowInputVar,
        Air.Flat.Component.rowOffset] using abstractMem)
  exact all interaction interactionMem

/-- Every evaluated interaction of an `sp1Ensemble` witness uses one of its four registered
channels.  This is a structural theorem, independent of constraints or balance. -/
private theorem ensembleInteraction_channel_mem
    (witness : EnsembleWitness (Soundness.sp1Ensemble (p := p)))
    {interaction : Interaction (ZMod p)} (interactionMem : interaction ∈ witness.interactions) :
    interaction.channel ∈ (Soundness.sp1Ensemble (p := p)).channels := by
  simp only [EnsembleWitness.interactions, List.mem_flatMap] at interactionMem
  obtain ⟨table, tableMem, interactionMem⟩ := interactionMem
  apply ensembleComponent_channels_subset table.component
    (Air.Flat.EnsembleWitness.mem_allTables_component_of_mem_allTables
      (witness := witness) tableMem)
  exact tableInteraction_channel_mem table interactionMem

/-- Within the registered four-channel universe, `kindOf = Byte` identifies the Byte channel. -/
private theorem channel_eq_byte_of_mem_of_kind
    (channel : RawChannel (ZMod p))
    (channelMem : channel ∈ (Soundness.sp1Ensemble (p := p)).channels)
    (kindEq : kindOf channel.name = .Byte) :
    channel = Channels.byteChannel.toRaw := by
  rw [Soundness.sp1Ensemble_channels] at channelMem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at channelMem
  rcases channelMem with rfl | rfl | rfl | rfl
  · simp [kindOf, Channel.toRaw_name, Channels.stateChannel] at kindEq
  · rfl
  · simp [kindOf, Channel.toRaw_name, Channels.programChannel] at kindEq
  · simp [kindOf, Channel.toRaw_name, Channels.memoryChannel] at kindEq

/-- Within the registered four-channel universe, `kindOf = Program` identifies Program. -/
private theorem channel_eq_program_of_mem_of_kind
    (channel : RawChannel (ZMod p))
    (channelMem : channel ∈ (Soundness.sp1Ensemble (p := p)).channels)
    (kindEq : kindOf channel.name = .Program) :
    channel = Channels.programChannel.toRaw := by
  rw [Soundness.sp1Ensemble_channels] at channelMem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at channelMem
  rcases channelMem with rfl | rfl | rfl | rfl
  · simp [kindOf, Channel.toRaw_name, Channels.stateChannel] at kindEq
  · simp [kindOf, Channel.toRaw_name, Channels.byteChannel] at kindEq
  · rfl
  · simp [kindOf, Channel.toRaw_name, Channels.memoryChannel] at kindEq

/-- If a channel kind uniquely identifies `channel` in the evaluated full interaction list, then
the channel's access ledger is exactly the corresponding kind-filter of the full access ledger. -/
private theorem interactionsWith_map_toAccess_eq_filter_kind
    (witness : EnsembleWitness (Soundness.sp1Ensemble (p := p)))
    (channel : RawChannel (ZMod p)) (kind : InteractionKind)
    (channelKind : kindOf channel.name = kind)
    (unique : ∀ interaction ∈ witness.interactions,
      kindOf interaction.channel.name = kind → interaction.channel = channel) :
    (witness.interactionsWith channel).map Interaction.toAccess =
      (witness.interactions.map Interaction.toAccess).filter
        (fun access => decide (access.1 = kind)) := by
  classical
  have interactionsWithEq : witness.interactionsWith channel =
      witness.interactions.filter (fun interaction => decide (interaction.channel = channel)) := by
    simp only [EnsembleWitness.interactionsWith, EnsembleWitness.interactions,
      List.filter_flatMap]
    apply List.flatMap_congr
    intro table tableMem
    exact Air.Flat.Table.interactionsWith_eq_filter
  rw [interactionsWithEq, List.filter_map]
  apply congrArg (List.map Interaction.toAccess)
  apply List.filter_congr
  intro interaction interactionMem
  simp only [Function.comp_apply, Interaction.toAccess]
  rw [decide_eq_decide]
  constructor
  · rintro rfl
    exact channelKind
  · exact unique interaction interactionMem

/-- Filtering a full ledger by interaction kind preserves its multiplicity sum at keys of that
kind. -/
private theorem multiplicitySum_filter_kind (accesses : LookupAccessList)
    (kind : InteractionKind) (key : LookupKey) (keyKind : key.1 = kind) :
    LookupAccessList.multiplicitySum
        (accesses.filter (fun access => decide (access.1 = kind))) key =
      LookupAccessList.multiplicitySum accesses key := by
  induction accesses with
  | nil => rfl
  | cons head tail ih =>
      by_cases headKind : head.1 = kind
      · rw [List.filter_cons_of_pos (by simpa using headKind),
          LookupAccessList.multiplicitySum_cons,
          LookupAccessList.multiplicitySum_cons, ih]
      · rw [List.filter_cons_of_neg (by simpa using headKind), ih,
          LookupAccessList.multiplicitySum_cons]
        have keyNe : LookupAccessList.keyOf head ≠ key := by
          intro keyEq
          apply headKind
          change (LookupAccessList.keyOf head).1 = kind
          rw [keyEq, keyKind]
        rw [if_neg keyNe, zero_add]

/-- Per-key full-ledger balance for one interaction kind implies balance of that kind-filter. -/
private theorem isConsistentBalanced_filter_kind (accesses : LookupAccessList)
    (kind : InteractionKind)
    (balanced : ∀ key : LookupKey, key.1 = kind →
      LookupAccessList.multiplicitySum accesses key = 0) :
    LookupAccessList.isConsistentBalanced
      (accesses.filter (fun access => decide (access.1 = kind))) := by
  intro key
  by_cases keyKind : key.1 = kind
  · rw [multiplicitySum_filter_kind accesses kind key keyKind]
    exact balanced key keyKind
  · exact LookupAccessList.multiplicitySum_zero_of_kind
      (fun access accessMem => by
        have := (List.mem_filter.mp accessMem).2
        simpa only [decide_eq_true_eq, LookupAccessList.keyOf] using this)
      keyKind

/-- The native-consumer recount discharges the Byte and Program integer-balance obligations of the
constructed witness.  Only State and Memory remain for the global integration contract. -/
theorem exactNativeEnsembleWitness_preprocessedIntegerBalance {Digest : Type}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (recount : PreprocessedProviderRecountContract executionWitness inventory
      (exactNativeSkeletonLedger statement executionWitness memoryBoundaryWitness data hint))
    (channel : RawChannel (ZMod p))
    (channelCase : channel = Channels.byteChannel.toRaw ∨
      channel = Channels.programChannel.toRaw) :
    LookupAccessList.isConsistentBalanced
      (((exactNativeEnsembleWitness statement executionWitness memoryBoundaryWitness inventory data hint
        ).interactionsWith channel).map Interaction.toAccess) := by
  let witness := exactNativeEnsembleWitness statement executionWitness memoryBoundaryWitness
    inventory data hint
  rcases channelCase with rfl | rfl
  · rw [interactionsWith_map_toAccess_eq_filter_kind witness Channels.byteChannel.toRaw .Byte
      (by simp [kindOf, Channel.toRaw_name, Channels.byteChannel]) (by
        intro interaction interactionMem kindEq
        exact channel_eq_byte_of_mem_of_kind interaction.channel
          (ensembleInteraction_channel_mem witness interactionMem) kindEq),
      ← exactNativeAllCleanAccesses_eq_interactions statement executionWitness
        memoryBoundaryWitness inventory data hint]
    exact isConsistentBalanced_filter_kind _ .Byte fun key keyKind =>
      exactNativeAllCleanAccesses_preprocessedBalance statement executionWitness
        memoryBoundaryWitness inventory data hint recount key (Or.inl keyKind)
  · rw [interactionsWith_map_toAccess_eq_filter_kind witness Channels.programChannel.toRaw .Program
      (by simp [kindOf, Channel.toRaw_name, Channels.programChannel]) (by
        intro interaction interactionMem kindEq
        exact channel_eq_program_of_mem_of_kind interaction.channel
          (ensembleInteraction_channel_mem witness interactionMem) kindEq),
      ← exactNativeAllCleanAccesses_eq_interactions statement executionWitness
        memoryBoundaryWitness inventory data hint]
    exact isConsistentBalanced_filter_kind _ .Program fun key keyKind =>
      exactNativeAllCleanAccesses_preprocessedBalance statement executionWitness
        memoryBoundaryWitness inventory data hint recount key (Or.inr keyKind)

/-- The State/Memory endpoint plus the recount-derived Byte/Program balances and exact count bounds
give Clean balance on every native channel.  The access-list permutation is reflexive because each
integer-balance fact is stated on the canonical `Interaction.toAccess` projection; channel
homogeneity follows from Clean's own `EnsembleWitness.interactionsWith` membership lemma. -/
theorem exactNativeEnsembleWitness_balancedChannels {Digest : Type}
    (program : GuestProgram) (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (recount : PreprocessedProviderRecountContract executionWitness inventory
      (exactNativeSkeletonLedger statement executionWitness memoryBoundaryWitness data hint))
    (global : ExactNativeGlobalContract program statement executionWitness
      memoryBoundaryWitness inventory data hint) :
    (exactNativeEnsembleWitness statement executionWitness memoryBoundaryWitness inventory data hint
      ).BalancedChannels := by
  intro channel channelMem
  have integerBalance : LookupAccessList.isConsistentBalanced
      (((exactNativeEnsembleWitness statement executionWitness memoryBoundaryWitness inventory data hint
        ).interactionsWith channel).map Interaction.toAccess) := by
    have channelCase := channelMem
    rw [Soundness.sp1Ensemble_channels] at channelCase
    simp only [List.mem_cons, List.not_mem_nil, or_false] at channelCase
    rcases channelCase with state | byte | program | memory
    · exact global.remainingIntegerBalance channel (Or.inl state)
    · exact exactNativeEnsembleWitness_preprocessedIntegerBalance statement executionWitness
        memoryBoundaryWitness inventory data hint recount channel (Or.inl byte)
    · exact exactNativeEnsembleWitness_preprocessedIntegerBalance statement executionWitness
        memoryBoundaryWitness inventory data hint recount channel (Or.inr program)
    · exact global.remainingIntegerBalance channel (Or.inr memory)
  change BalancedInteractions
    ((exactNativeEnsembleWitness statement executionWitness memoryBoundaryWitness inventory data hint
      ).allTablesWitness.interactionsWith channel)
  rw [EnsembleWitness.interactionsWith_allTablesWitness]
  exact SP1Clean.LookupAccessList.balancedInteractions_of_isConsistentBalanced
    _ _ channel
    (fun _ interactionMem => EnsembleWitness.channel_eq_of_mem_interactionsWith interactionMem)
    (List.Perm.refl _)
    (global.interactionCount channel channelMem)
    integerBalance

/-- **The exact/native artifact satisfies the honest native machine relation.**

The provider and public-boundary contracts remain explicit local-constraint inputs.  The distinct
global contract supplies precisely channel balance and semantic binding; neither is inferred from
those local inputs. -/
theorem exactNativeArtifact_supportedCoreNativeRelation {Digest : Type}
    {binds : CoreAIR.Current.PreprocessedBinding p Digest}
    (program : GuestProgram) (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (transport : ExactProviderTransportContract binds statement
      executionWitness memoryBoundaryWitness inventory
      (exactNativeSkeletonLedger statement executionWitness memoryBoundaryWitness data hint))
    (boundary : ExactNativeBoundaryContract statement.publicValues)
    (global : ExactNativeGlobalContract program statement executionWitness
      memoryBoundaryWitness inventory data hint) :
    Soundness.SupportedCoreNativeRelation
      (exactNativeStatement program statement)
      (exactNativeEnsembleWitness statement executionWitness memoryBoundaryWitness inventory data hint) := by
  refine ⟨⟨rfl, ?_, ?_⟩, global.semanticBoundary⟩
  · exact exactNativeEnsembleWitness_constraints statement executionWitness
      memoryBoundaryWitness inventory data hint transport boundary
  · exact exactNativeEnsembleWitness_balancedChannels program statement executionWitness
      memoryBoundaryWitness inventory data hint transport.preprocessing global

/-- **Official-Sail consequence given the explicit exact/native global contract.**

This is deliberately shard-local.  It inherits the native capstone's ordinary eight-tick schedule
premise and does not assert boot reachability, halting, or cryptographic proof-system soundness. -/
theorem exactNativeArtifact_localExecution {Digest : Type}
    {binds : CoreAIR.Current.PreprocessedBinding p Digest}
    (model : Machine.SP1MachineModel) (ordinary : model.UsesOrdinarySchedule)
    (program : GuestProgram) (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (transport : ExactProviderTransportContract binds statement
      executionWitness memoryBoundaryWitness inventory
      (exactNativeSkeletonLedger statement executionWitness memoryBoundaryWitness data hint))
    (boundary : ExactNativeBoundaryContract statement.publicValues)
    (global : ExactNativeGlobalContract program statement executionWitness
      memoryBoundaryWitness inventory data hint) :
    ∃ execution, SupportedCoreLocalExecutionRelation model
      (exactNativeStatement program statement) execution := by
  exact Soundness.supported_core_native_sound model ordinary
    (exactNativeStatement program statement)
    (exactNativeEnsembleWitness statement executionWitness memoryBoundaryWitness inventory data hint)
    (exactNativeArtifact_supportedCoreNativeRelation program statement executionWitness
      memoryBoundaryWitness inventory data hint transport boundary global)

end SP1Clean.Composition
