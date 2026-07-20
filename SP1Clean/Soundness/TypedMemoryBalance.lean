import SP1Clean.Soundness.TypedMemory
import SP1Clean.Soundness.ProviderBindings

/-! # The per-`MemLoc` Memory-channel balance

The Memory analogue of the State-axis balance chain in `TypedState`.  Where the State boundary is one
public verifier pair and the eleven providers contribute nothing, the Memory channel is the mirror
image: the boundary **verifier** contributes nothing, and the eleven providers contribute through the
two dedicated memory-boundary tables — the init provider (a per-address genesis *push*, index 34) and
the finalize provider (a per-address final *pull*, index 35).  The other nine byte/range/program
providers do not declare the Memory channel and so emit nothing on it.

Unlike State/Program, the decoded instruction rows' Memory interactions are **not** reduced to a fixed
closed form here.  A decoded row's produced/consumed memory messages are, by definition,
`producedMessages`/`consumedMessages` of its actual retained Clean interactions
(`DecodedInstructionRow.producedMemoryMessages`/`consumedMemoryMessages`), so the ensemble
decomposition threads them through verbatim — no per-chip `MemoryEmissionShape` sweep is needed.

The chain mirrors, lemma for lemma:

* `witness_verifierMemoryInteractions_eq_nil` ← `witness_verifierStateInteractions_eq` (here the
  verifier is nil, not the boundary pair);
* `witness_nonMemoryProviderTable_memoryInteractions_eq_nil` /
  `witness_providerMemoryInteractions_eq` ← `witness_providerStateInteractions_eq_nil` (here the
  providers are *non*-nil: `init ++ finalize`), themselves the two-table generalisation of the
  Program-provider pattern `witness_providerProgramInteractions_eq`;
* `producedMessages_typedEnsembleMemory_eq` / `consumedMessages_typedEnsembleMemory_eq` ←
  `producedMessages_typedEnsembleState_eq` / `consumedMessages_typedEnsembleState_eq`;
* `realDecodedMemory_perm` ← `realDecodedStateMessages_perm`.

The final `realDecodedMemory_perlocBalance` is the raw per-location multiset balance the timed
grounding walk (`TimedGrounding.walk`) consumes.  Two honest seams are deliberately left open for the
capstone/B5 assembly and flagged in the module below:

1. **Binary multiplicities are a hypothesis.** `producedMessages_perm_consumedMessages` needs every
   Memory interaction's signed multiplicity in `{-1, 0, 1}`.  For the *providers* this is the boolean
   witnessed `m` (`m*(m-1) = 0`); for the *chips* it is `±is_real`/`±is_real·(1-imm)`, binary via
   `witness_decodedInstructionRows_selectorBinary`.  Deriving the chip half needs the per-chip Memory
   emission shapes (the sweep this workstream defers), so it is taken as a premise `memBinary`, to be
   discharged by the `ChipGroundingContracts` bundle exactly as State discharges its `binary` premise.
2. **Symmetric (both-providers-both-sides) form.** The balance keeps `producedMessages` and
   `consumedMessages` of *both* boundary tables on *both* sides, rather than the asymmetric
   `init-produced ++ rows` / `finalize-consumed ++ rows`.  Collapsing to the asymmetric frontier form
   needs the provider *purity* facts (init only pushes, finalize only pulls) plus the
   `MemoryInitProviderUnique` per-location uniqueness — the `optMS (live)`/`optMS (finM)` frontier-Option
   packaging, which is B5's job.
-/

namespace SP1Clean.Soundness

open Air.Flat Circuit
open SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## Generic distribution of produced/consumed messages over `flatMap` -/

section Distribution

variable {Message : TypeMap} [ProvableType Message] {channel : Channel (ZMod p) Message}

omit [Fact (2 ^ 24 < p)] in
/-- Active produced messages distribute over a `flatMap`: the produced messages of a concatenated
family are the concatenation of each block's produced messages. -/
theorem producedMessages_flatMap {α : Type*} (l : List α)
    (f : α → List (TypedInteraction channel)) :
    producedMessages (l.flatMap f) = l.flatMap fun x => producedMessages (f x) := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.flatMap_cons, producedMessages_append, ih, List.flatMap_cons]

omit [Fact (2 ^ 24 < p)] in
/-- Active consumed messages distribute over a `flatMap`. -/
theorem consumedMessages_flatMap {α : Type*} (l : List α)
    (f : α → List (TypedInteraction channel)) :
    consumedMessages (l.flatMap f) = l.flatMap fun x => consumedMessages (f x) := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.flatMap_cons, consumedMessages_append, ih, List.flatMap_cons]

end Distribution

/-! ## The boundary verifier contributes nothing to the Memory channel -/

/-- The public State-boundary verifier does not participate in the Memory channel: it declares only
the State channel.  Mirror of `witness_verifierStateInteractions_eq`, but here the verifier's Memory
contribution is empty (State is where the verifier is active). -/
theorem witness_verifierMemoryInteractions_eq_nil
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    typedTableInteractionsWith witness.verifierTable memoryChannel = [] := by
  apply List.map_eq_nil_iff.mp
  rw [typedTableInteractionsWith_raw]
  apply Table.interactionsWith_nil_of_channel_not_mem
  change memoryChannel.toRaw ∉ [stateChannel.toRaw]
  simp [Channels.memoryChannel_eq_stateChannel_false]

/-! ## The nine non-memory providers contribute nothing to the Memory channel -/

/-- Every provider-table position except the two dedicated memory boundary tables (init at 34,
finalize at 35) has no Memory-channel interactions.  Positional, mirroring
`witness_nonProgramProviderTable_programInteractions_eq_nil`: the eight byte/range providers declare
only the Byte channel and the program provider only the Program channel. -/
theorem witness_nonMemoryProviderTable_memoryInteractions_eq_nil
    (witness : EnsembleWitness (sp1Ensemble (p := p))) (i : ℕ)
    (lower : 25 ≤ i) (upper : i < 36) (witnessBound : i < witness.tables.length)
    (notInit : i ≠ memoryInitProviderIndex) (notFinalize : i ≠ memoryFinalizeProviderIndex) :
    typedTableInteractionsWith witness.tables[i] memoryChannel = [] := by
  apply List.map_eq_nil_iff.mp
  rw [typedTableInteractionsWith_raw]
  apply Table.interactionsWith_nil_of_channel_not_mem
  have ensembleBound : i < (sp1Ensemble (p := p)).tables.length := by
    simp only [sp1Ensemble_tables, List.length_append, sp1Tables_length,
      sp1ProviderTables_length]
    omega
  have componentEq := witness.same_circuits i ensembleBound
  have providerBound : i - 25 < (sp1ProviderTables (p := p)).length := by
    simp only [sp1ProviderTables_length]
    omega
  have componentProviderEq : witness.tables[i].component =
      (sp1ProviderTables (p := p))[i - 25] := by
    rw [← componentEq]
    change (sp1Tables (p := p) ++ sp1ProviderTables (p := p))[i] = _
    rw [List.getElem_append_right (by simpa only [sp1Tables_length] using lower)]
    simp only [sp1Tables_length]
  rw [componentProviderEq]
  interval_cases i
  all_goals first
    | exact (notInit (by rfl)).elim
    | exact (notFinalize (by rfl)).elim
    | (change memoryChannel.toRaw ∉ [byteChannel.toRaw];
       simp [Channels.memoryChannel_eq_byteChannel_false])
    | (change memoryChannel.toRaw ∉ [programChannel.toRaw];
       simp [Channels.memoryChannel_eq_programChannel_false])

/-- The whole provider suffix's Memory interactions are exactly the init-provider table's followed by
the finalize-provider table's.  Structural, from the ensemble table order and each component's
declared channels; the two-table analogue of `witness_providerProgramInteractions_eq`. -/
theorem witness_providerMemoryInteractions_eq
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    (witness.tables.drop 25).flatMap (typedTableInteractionsWith · memoryChannel) =
      typedTableInteractionsWith (memoryInitProviderTable witness) memoryChannel ++
        typedTableInteractionsWith (memoryFinalizeProviderTable witness) memoryChannel := by
  have tablesLength : witness.tables.length = 36 := by
    rw [← witness.same_length]
    rfl
  rw [List.drop_eq_getElem_cons (i := 25) (by omega),
    List.drop_eq_getElem_cons (i := 26) (by omega),
    List.drop_eq_getElem_cons (i := 27) (by omega),
    List.drop_eq_getElem_cons (i := 28) (by omega),
    List.drop_eq_getElem_cons (i := 29) (by omega),
    List.drop_eq_getElem_cons (i := 30) (by omega),
    List.drop_eq_getElem_cons (i := 31) (by omega),
    List.drop_eq_getElem_cons (i := 32) (by omega),
    List.drop_eq_getElem_cons (i := 33) (by omega),
    List.drop_eq_getElem_cons (i := 34) (by omega),
    List.drop_eq_getElem_cons (i := 35) (by omega),
    List.drop_eq_nil_of_le (by omega)]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [witness_nonMemoryProviderTable_memoryInteractions_eq_nil witness 25 (by omega)
      (by omega) (by omega) (by decide) (by decide),
    witness_nonMemoryProviderTable_memoryInteractions_eq_nil witness 26 (by omega)
      (by omega) (by omega) (by decide) (by decide),
    witness_nonMemoryProviderTable_memoryInteractions_eq_nil witness 27 (by omega)
      (by omega) (by omega) (by decide) (by decide),
    witness_nonMemoryProviderTable_memoryInteractions_eq_nil witness 28 (by omega)
      (by omega) (by omega) (by decide) (by decide),
    witness_nonMemoryProviderTable_memoryInteractions_eq_nil witness 29 (by omega)
      (by omega) (by omega) (by decide) (by decide),
    witness_nonMemoryProviderTable_memoryInteractions_eq_nil witness 30 (by omega)
      (by omega) (by omega) (by decide) (by decide),
    witness_nonMemoryProviderTable_memoryInteractions_eq_nil witness 31 (by omega)
      (by omega) (by omega) (by decide) (by decide),
    witness_nonMemoryProviderTable_memoryInteractions_eq_nil witness 32 (by omega)
      (by omega) (by omega) (by decide) (by decide),
    witness_nonMemoryProviderTable_memoryInteractions_eq_nil witness 33 (by omega)
      (by omega) (by omega) (by decide) (by decide)]
  simp only [List.nil_append]
  rfl

/-! ## Exact Memory-channel decomposition of the whole ensemble witness -/

/-- Exact typed Memory-channel decomposition: the decoded instruction rows' Memory interactions,
followed by the init- and finalize-provider tables'.  The boundary verifier drops out. -/
theorem typedEnsembleMemoryInteractions_eq
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    typedEnsembleInteractionsWith witness memoryChannel =
      decodedWitnessInstructionInteractionsWith witness.data witness.tables memoryChannel ++
        (typedTableInteractionsWith (memoryInitProviderTable witness) memoryChannel ++
          typedTableInteractionsWith (memoryFinalizeProviderTable witness) memoryChannel) := by
  rw [typedEnsembleInteractionsWith_partition, witness_verifierMemoryInteractions_eq_nil,
    witness_providerMemoryInteractions_eq, List.nil_append]

/-- The decoded witness Memory interactions are the flattened per-row interaction lists — the
definitional carrier of the per-row `producedMemoryMessages`/`consumedMemoryMessages`. -/
theorem decodedWitnessMemoryInteractions_eq_flatMap
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    decodedWitnessInstructionInteractionsWith witness.data witness.tables memoryChannel =
      (decodedInstructionRows (p := p) witness.tables).flatMap
        fun decoded => decoded.interactionsWith witness.data memoryChannel := rfl

/-- Produced Memory messages of the whole witness: every decoded row's produced messages, followed by
the two boundary tables' produced messages.  The per-row terms are threaded verbatim through
`producedMemoryMessages` — no per-chip closed form.  Mirror of `producedMessages_typedEnsembleState_eq`. -/
theorem producedMessages_typedEnsembleMemory_eq
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    producedMessages (typedEnsembleInteractionsWith witness memoryChannel) =
      (decodedInstructionRows (p := p) witness.tables).flatMap
          (fun decoded => decoded.producedMemoryMessages witness.data) ++
        (producedMessages (typedTableInteractionsWith (memoryInitProviderTable witness)
            memoryChannel) ++
          producedMessages (typedTableInteractionsWith (memoryFinalizeProviderTable witness)
            memoryChannel)) := by
  have key : producedMessages
      (decodedWitnessInstructionInteractionsWith witness.data witness.tables memoryChannel)
      = (decodedInstructionRows (p := p) witness.tables).flatMap
          (fun decoded => decoded.producedMemoryMessages witness.data) := by
    rw [decodedWitnessMemoryInteractions_eq_flatMap]
    exact producedMessages_flatMap (decodedInstructionRows (p := p) witness.tables)
      (fun (decoded : DecodedInstructionRow p) => decoded.interactionsWith witness.data memoryChannel)
  rw [typedEnsembleMemoryInteractions_eq, producedMessages_append, producedMessages_append, key]

/-- Consumed Memory messages of the whole witness: every decoded row's consumed messages, followed by
the two boundary tables' consumed messages.  Mirror of `consumedMessages_typedEnsembleState_eq`. -/
theorem consumedMessages_typedEnsembleMemory_eq
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    consumedMessages (typedEnsembleInteractionsWith witness memoryChannel) =
      (decodedInstructionRows (p := p) witness.tables).flatMap
          (fun decoded => decoded.consumedMemoryMessages witness.data) ++
        (consumedMessages (typedTableInteractionsWith (memoryInitProviderTable witness)
            memoryChannel) ++
          consumedMessages (typedTableInteractionsWith (memoryFinalizeProviderTable witness)
            memoryChannel)) := by
  have key : consumedMessages
      (decodedWitnessInstructionInteractionsWith witness.data witness.tables memoryChannel)
      = (decodedInstructionRows (p := p) witness.tables).flatMap
          (fun decoded => decoded.consumedMemoryMessages witness.data) := by
    rw [decodedWitnessMemoryInteractions_eq_flatMap]
    exact consumedMessages_flatMap (decodedInstructionRows (p := p) witness.tables)
      (fun (decoded : DecodedInstructionRow p) => decoded.interactionsWith witness.data memoryChannel)
  rw [typedEnsembleMemoryInteractions_eq, consumedMessages_append, consumedMessages_append, key]

/-! ## The Memory-channel balance -/

/-- **Clean Memory balance as an exact typed endpoint permutation.** Under Clean channel balance and
binary Memory multiplicities, the produced Memory messages (every decoded row's read-backs/writes plus
the two boundary tables' pushes) are a permutation of the consumed Memory messages (every decoded row's
read-priors plus the two boundary tables' pulls).

`memBinary` is the honest deferred seam (see the module doc): it is the Memory analogue of the State
`binary` premise, to be discharged per chip/provider by the `ChipGroundingContracts` bundle. -/
theorem realDecodedMemory_perm
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (balanced : witness.BalancedChannels)
    (memBinary : ∀ interaction ∈ typedEnsembleInteractionsWith witness memoryChannel,
      signedVal interaction.mult = -1 ∨ signedVal interaction.mult = 0 ∨
        signedVal interaction.mult = 1) :
    ((decodedInstructionRows (p := p) witness.tables).flatMap
        (fun decoded => decoded.producedMemoryMessages witness.data) ++
      (producedMessages (typedTableInteractionsWith (memoryInitProviderTable witness) memoryChannel) ++
        producedMessages (typedTableInteractionsWith (memoryFinalizeProviderTable witness)
          memoryChannel))).Perm
    ((decodedInstructionRows (p := p) witness.tables).flatMap
        (fun decoded => decoded.consumedMemoryMessages witness.data) ++
      (consumedMessages (typedTableInteractionsWith (memoryInitProviderTable witness) memoryChannel) ++
        consumedMessages (typedTableInteractionsWith (memoryFinalizeProviderTable witness)
          memoryChannel))) := by
  classical
  have channelBalanced := typedInteractions_balanced witness balanced memoryChannel
    (by simp [sp1Ensemble_channels])
  have messagePerm := producedMessages_perm_consumedMessages
    (typedEnsembleInteractionsWith witness memoryChannel) channelBalanced memBinary
  rwa [producedMessages_typedEnsembleMemory_eq, consumedMessages_typedEnsembleMemory_eq]
    at messagePerm

/-- **The raw per-`MemLoc` Memory balance** consumed by the timed grounding walk.  Restricting the
whole-channel permutation to each location gives an exact multiset balance at that location: the
location's produced messages (its boundary genesis push plus every row's read-backs/writes there)
equal its consumed messages (its boundary final pull plus every row's read-priors there).

This is the raw multiset form; the `optMS (live loc)` / `optMS (finM loc)` frontier-Option packaging
(via `MemoryInitProviderUnique`), the provider purity that collapses the symmetric form, and the
all-rows→real-rows reduction are the remaining B5/capstone steps. -/
theorem realDecodedMemory_perlocBalance
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (balanced : witness.BalancedChannels)
    (memBinary : ∀ interaction ∈ typedEnsembleInteractionsWith witness memoryChannel,
      signedVal interaction.mult = -1 ∨ signedVal interaction.mult = 0 ∨
        signedVal interaction.mult = 1)
    (loc : Semantics.MemLoc) :
    (Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
      ((decodedInstructionRows (p := p) witness.tables).flatMap
          (fun decoded => decoded.producedMemoryMessages witness.data) ++
        (producedMessages (typedTableInteractionsWith (memoryInitProviderTable witness)
            memoryChannel) ++
          producedMessages (typedTableInteractionsWith (memoryFinalizeProviderTable witness)
            memoryChannel))) : Multiset (MemoryMsg (ZMod p))) =
    Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
      ((decodedInstructionRows (p := p) witness.tables).flatMap
          (fun decoded => decoded.consumedMemoryMessages witness.data) ++
        (consumedMessages (typedTableInteractionsWith (memoryInitProviderTable witness)
            memoryChannel) ++
          consumedMessages (typedTableInteractionsWith (memoryFinalizeProviderTable witness)
            memoryChannel))) := by
  classical
  have coeEq := Multiset.coe_eq_coe.mpr (realDecodedMemory_perm witness balanced memBinary)
  rw [coeEq]

end SP1Clean.Soundness
