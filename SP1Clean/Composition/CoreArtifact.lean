import SP1Clean.Composition.CoreEnsemble
import SP1Clean.Soundness.AIR
import SP1Clean.Soundness.EnsembleChannels

/-! # Exact Core artifact at the native semantic boundary

The exact integration supplies per-channel occurrence bounds, State/Memory/Exit integer balance
and authenticated semantic boundary binding for `CoreEnsemble`'s canonical witness. Byte/Program
balance follows from its consumer recount. These global obligations remain explicit; local AIR
constraints and cryptographic knowledge extraction do not establish them by themselves.

Combining those contracts yields the existing native relation and its ordinary shard-local Sail
consequence. This does not prove boot reachability, shard composition, verifier soundness or
completeness for mixed host execution.
-/

set_option autoImplicit false

namespace SP1Clean.Composition

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
    (statement : SP1ShardStatement (ZMod p) Digest) : SupportedCoreStatement p :=
  ⟨program, exactNativeBoundary statement.publicValues⟩

/-- **The remaining integration-to-native global translation endpoint.**

This contract is stated directly about the constructed 55-table witness.  Its remaining
integer-balance field is the native `ℤ` balance property for State, Memory and Exit, before conversion to
Clean's field-valued balance; the separate
count field is exactly Clean's no-wrap premise.  `semanticBoundary` binds the projected public
boundary and canonical physical-table data to the caller's program and a concrete initial Sail state.

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
  /-- The projected State, Memory, and Exit access ledgers balance over the integers. Byte and Program
  are deliberately absent: `exactNativeAllCleanAccesses_preprocessedBalance` derives them from the
  native recount contract. -/
  remainingIntegerBalance : ∀ channel,
    (channel = Channels.stateChannel.toRaw ∨ channel = Channels.memoryChannel.toRaw ∨
      channel = Channels.exitChannel.toRaw) →
    SP1Clean.LookupAccessList.isConsistentBalanced
      (((exactNativeEnsembleWitness statement executionWitness memoryBoundaryWitness inventory data hint
        ).interactionsWith channel).map Interaction.toAccess)
  /-- The canonical prover data and providers describe the caller's program and the public initial
  boundary describes a concrete compatible Sail state. -/
  semanticBoundary : Soundness.SemanticBoundaryBinding
    (exactNativeStatement program statement)
    (exactNativeEnsembleWitness statement executionWitness memoryBoundaryWitness inventory data hint)

/-! ## Full-ledger to per-channel bridge -/

/-- Per-key full-ledger balance for one interaction kind implies balance of that kind-filter. -/
private theorem isConsistentBalanced_filter_kind (accesses : LookupAccessList)
    (kind : InteractionKind)
    (balanced : ∀ key : LookupKey, key.1 = kind →
      LookupAccessList.multiplicitySum accesses key = 0) :
    LookupAccessList.isConsistentBalanced
      (accesses.filter (fun access => decide (access.1 = kind))) := by
  intro key
  by_cases keyKind : key.1 = kind
  · rw [LookupAccessList.multiplicitySum_filterKind accesses keyKind]
    exact balanced key keyKind
  · exact LookupAccessList.multiplicitySum_zero_of_kind
      (fun access accessMem => by
        have := (List.mem_filter.mp accessMem).2
        simpa only [decide_eq_true_eq, LookupAccessList.keyOf] using this)
      keyKind

/-- The native-consumer recount discharges the Byte and Program integer-balance obligations of the
constructed witness.  State, Memory and Exit remain for the global integration contract. -/
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
  · rw [Soundness.witness_channelLedger_eq_filter_kind witness Channels.byteChannel.toRaw
      (by simp [Soundness.sp1Ensemble_channels]) .Byte rfl,
      ← exactNativeAllCleanAccesses_eq_interactions statement executionWitness
        memoryBoundaryWitness inventory data hint]
    exact isConsistentBalanced_filter_kind _ .Byte fun key keyKind =>
      exactNativeAllCleanAccesses_preprocessedBalance statement executionWitness
        memoryBoundaryWitness inventory data hint recount key (Or.inl keyKind)
  · rw [Soundness.witness_channelLedger_eq_filter_kind witness Channels.programChannel.toRaw
      (by simp [Soundness.sp1Ensemble_channels]) .Program rfl,
      ← exactNativeAllCleanAccesses_eq_interactions statement executionWitness
        memoryBoundaryWitness inventory data hint]
    exact isConsistentBalanced_filter_kind _ .Program fun key keyKind =>
      exactNativeAllCleanAccesses_preprocessedBalance statement executionWitness
        memoryBoundaryWitness inventory data hint recount key (Or.inr keyKind)

/-- The transport's `SyscallInstrs` table is the manufactured empty one. Stated twice — once
positionally for the silence lemmas, once at `BumpDecode`'s accessor for the grounding boundary —
because the two consumers spell the same table differently. -/
private theorem exactNativeEnsembleWitness_syscallTable_nil {Digest : Type}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (Soundness.syscallInstrsTable (exactNativeEnsembleWitness statement executionWitness
      memoryBoundaryWitness inventory data hint)).table = [] := by
  show (extractedSyscallInstrsTable (p := p) data).table = []
  exact SyscallInstrsChip.traceTable_table _ _ _

private theorem exactNativeEnsembleWitness_syscallTable_nil' {Digest : Type}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ∀ t : Air.Flat.Table (ZMod p),
      (exactNativeEnsembleWitness statement executionWitness memoryBoundaryWitness inventory data
        hint).tables[Soundness.syscallTablePosition]? = some t → t.table = [] := by
  intro t ht
  have hpos : (exactNativeEnsembleWitness statement executionWitness memoryBoundaryWitness
      inventory data hint).tables[Soundness.syscallTablePosition]?
      = some (Soundness.syscallInstrsTable (exactNativeEnsembleWitness statement executionWitness
        memoryBoundaryWitness inventory data hint)) := rfl
  rw [hpos] at ht
  rw [← Option.some.inj ht]
  exact exactNativeEnsembleWitness_syscallTable_nil statement executionWitness
    memoryBoundaryWitness inventory data hint

/-- The transport meets the interim syscall boundary. Inactivity follows from the manufactured
empty `SyscallInstrs` table; `haltTablePresent` comes from the manufactured one-padding-row Halt
table, which the transport supplies precisely because the exact v6.4.0 cluster has none. -/
private theorem exactNativeEnsembleWitness_syscallTableInactive {Digest : Type}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    Soundness.SyscallTableInactive (exactNativeEnsembleWitness statement executionWitness
      memoryBoundaryWitness inventory data hint) where
  noActiveRows := by
    rw [Soundness.realSyscallInstrsRows, exactNativeEnsembleWitness_syscallTable_nil]
    rfl
  haltTablePresent := by
    show (extractedHaltTable (p := p) data).table ≠ []
    simp only [extractedHaltTable, HaltChip.haltTraceInputs]
    exact List.cons_ne_nil _ _

/-- The State/Memory/Exit endpoint plus the recount-derived Byte/Program balances and exact count bounds
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
    rcases channelCase with state | byte | program | memory | exit | syscall | publicValues
    · exact global.remainingIntegerBalance channel (Or.inl state)
    · exact exactNativeEnsembleWitness_preprocessedIntegerBalance statement executionWitness
        memoryBoundaryWitness inventory data hint recount channel (Or.inl byte)
    · exact exactNativeEnsembleWitness_preprocessedIntegerBalance statement executionWitness
        memoryBoundaryWitness inventory data hint recount channel (Or.inr program)
    · exact global.remainingIntegerBalance channel (Or.inr (Or.inl memory))
    · exact global.remainingIntegerBalance channel (Or.inr (Or.inr exit))
    · rw [syscall, Soundness.witness_syscallChannel_silent _
        (exactNativeEnsembleWitness_syscallTable_nil' statement executionWitness
          memoryBoundaryWitness inventory data hint)]
      exact fun k => rfl
    · rw [publicValues, Soundness.witness_publicValuesChannel_silent _
        (exactNativeEnsembleWitness_syscallTable_nil' statement executionWitness
          memoryBoundaryWitness inventory data hint)]
      exact fun k => rfl
  change BalancedInteractions
    ((exactNativeEnsembleWitness statement executionWitness memoryBoundaryWitness inventory data hint
      ).interactionsWith channel)
  exact SP1Clean.LookupAccessList.balancedInteractions_of_isConsistentBalanced
    _ _ channel
    (fun _ interactionMem => EnsembleWitness.channel_eq_of_mem_interactionsWith interactionMem)
    (List.Perm.refl _)
    (global.interactionCount channel channelMem)
    integerBalance

/-- **The exact/native artifact satisfies the honest native machine relation.**

The transport contract supplies physical constraints. The global contract supplies the remaining
channel balance and authenticated semantic binding; neither follows from local constraints alone. -/
theorem exactNativeArtifact_supportedCoreNativeRelation {Digest : Type}
    {binds : CoreAIR.Current.PreprocessedBinding p Digest}
    (program : GuestProgram) (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (transport : ExactProviderTransportContract binds statement
      executionWitness memoryBoundaryWitness inventory
      (exactNativeSkeletonLedger statement executionWitness memoryBoundaryWitness data hint))
    (global : ExactNativeGlobalContract program statement executionWitness
      memoryBoundaryWitness inventory data hint) :
    Soundness.SupportedCoreNativeRelation
      (exactNativeStatement program statement)
      (exactNativeEnsembleWitness statement executionWitness memoryBoundaryWitness inventory data hint) := by
  refine ⟨⟨rfl, ?_, ?_⟩, global.semanticBoundary,
    exactNativeEnsembleWitness_syscallTableInactive statement executionWitness
      memoryBoundaryWitness inventory data hint⟩
  · exact exactNativeEnsembleWitness_constraints statement executionWitness
      memoryBoundaryWitness inventory data hint transport
  · exact exactNativeEnsembleWitness_balancedChannels program statement executionWitness
      memoryBoundaryWitness inventory data hint transport.preprocessing global

/-- **Official-Sail consequence given the explicit exact/native global contract.**

This is deliberately shard-local: a normally-retiring official-Sail run between the committed
public endpoints, with no machine-model parameter or schedule hypothesis.  It does not assert
boot reachability, halting, or cryptographic proof-system soundness. -/
theorem exactNativeArtifact_sailExecution {Digest : Type}
    {binds : CoreAIR.Current.PreprocessedBinding p Digest}
    (program : GuestProgram) (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (transport : ExactProviderTransportContract binds statement
      executionWitness memoryBoundaryWitness inventory
      (exactNativeSkeletonLedger statement executionWitness memoryBoundaryWitness data hint))
    (global : ExactNativeGlobalContract program statement executionWitness
      memoryBoundaryWitness inventory data hint) :
    ∃ execution, SupportedCoreSailRelation
      (exactNativeStatement program statement) execution := by
  exact Soundness.supported_core_native_sound
    (exactNativeStatement program statement)
    (exactNativeEnsembleWitness statement executionWitness memoryBoundaryWitness inventory data hint)
    (exactNativeArtifact_supportedCoreNativeRelation program statement executionWitness
      memoryBoundaryWitness inventory data hint transport global)

end SP1Clean.Composition
