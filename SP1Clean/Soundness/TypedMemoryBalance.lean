import SP1Clean.Soundness.TypedMemorySelectors
import SP1Clean.Soundness.ProviderBindings
import SP1Clean.Soundness.BumpDecode

/-! # The per-`MemLoc` Memory-channel balance

The Memory analogue of the State-axis balance chain in `TypedState`.  Where the State boundary is one
public verifier pair and the state-silent provider prefix contribute nothing, the Memory channel is
the mirror image: the boundary **verifier** contributes nothing, and the provider suffix contributes
through the two dedicated memory-boundary tables — the init provider (a per-address genesis *push*,
index 49) and the finalize provider (a per-address final *pull*, index 50) — plus MemoryBump at 51.
The byte/range/program providers do not declare the Memory channel and so emit nothing on it.

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
grounding walk (`TimedGrounding.walk`) consumes.  The two seams once flagged here are now **both
closed**:

1. **Binary multiplicities** — the intermediate lemmas still take a `memBinary` premise, but it is
   discharged in this same file by `witness_memoryMultiplicityBinary` (§"Witness-level structural
   Memory obligations"): the providers' boolean witnessed `m` (`m*(m-1) = 0`) plus the registry-wide
   selector-gating theorem for the instruction rows.
2. **Symmetric (both-providers-both-sides) form** — the collapse to the asymmetric frontier form
   (provider purity + `MemoryInitProviderUnique`/`MemoryFinalizeProviderUnique` uniqueness, the
   `optMS (live)`/`optMS (finM)` frontier-Option packaging) landed in `Soundness/MemoryFrontier.lean`
   (`memoryFrontierBalance`).
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
  change memoryChannel.toRaw ∉
    [stateChannel.toRaw, Channels.byteChannel.toRaw, Channels.exitChannel.toRaw]
  simp [Channels.memoryChannel_eq_stateChannel_false, Channels.memoryChannel_eq_byteChannel_false,
    Channels.memoryChannel_eq_exitChannel_false]

/-! ## The non-memory providers contribute nothing to the Memory channel -/

/-- Every provider-table position except the three memory-touching tables (init at 49, finalize at
50, and — W3 — the MemoryBump refresh table at 51) has no Memory-channel interactions.  Positional,
mirroring `witness_nonProgramProviderTable_programInteractions_eq_nil`: the byte/range
providers declare only the Byte channel, the program provider only the Program channel, and the
StateBump table (52) only Byte and State. -/
theorem witness_nonMemoryProviderTable_memoryInteractions_eq_nil
    (witness : EnsembleWitness (sp1Ensemble (p := p))) (i : ℕ)
    (lower : instructionTableCount ≤ i) (upper : i < ensembleTableCount)
    (witnessBound : i < witness.tables.length)
    (notInit : i ≠ memoryInitProviderIndex) (notFinalize : i ≠ memoryFinalizeProviderIndex)
    (notBump : i ≠ memoryBumpIndex) (notHalt : i ≠ haltIndex) :
    typedTableInteractionsWith witness.tables[i] memoryChannel = [] := by
  change 25 ≤ i at lower
  change i < 54 at upper
  change i ≠ 53 at notHalt
  apply List.map_eq_nil_iff.mp
  rw [typedTableInteractionsWith_raw]
  apply Table.interactionsWith_nil_of_channel_not_mem
  have ensembleBound : i < (sp1Ensemble (p := p)).tables.length := by
    rw [witness.same_length]
    exact witnessBound
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
    | exact (notBump (by rfl)).elim
    | exact (notHalt (by rfl)).elim
    | (change memoryChannel.toRaw ∉ [byteChannel.toRaw];
       simp [Channels.memoryChannel_eq_byteChannel_false])
    | (change memoryChannel.toRaw ∉ [programChannel.toRaw];
       simp [Channels.memoryChannel_eq_programChannel_false])
    | (change memoryChannel.toRaw ∉
         [(byteChannel (p := p)).toRaw, (Channels.stateChannel (p := p)).toRaw];
       simp [Channels.memoryChannel_eq_byteChannel_false,
         Channels.memoryChannel_eq_stateChannel_false])

/-- The whole provider suffix's Memory interactions are exactly the init-provider table's followed by
the finalize-provider table's, followed by — W3 — the MemoryBump refresh table's.  Structural,
from the ensemble table order and each component's declared channels; the three-table analogue of
`witness_providerProgramInteractions_eq`. -/
theorem witness_providerMemoryInteractions_eq
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    (witness.tables.drop 25).flatMap (typedTableInteractionsWith · memoryChannel) =
      typedTableInteractionsWith (memoryInitProviderTable witness) memoryChannel ++
        (typedTableInteractionsWith (memoryFinalizeProviderTable witness) memoryChannel ++
          (typedTableInteractionsWith (memoryBumpTable witness) memoryChannel ++
            typedTableInteractionsWith (haltTable witness) memoryChannel)) := by
  have tablesLength : witness.tables.length = 54 := by
    rw [← witness.same_length]
    simp [sp1Ensemble_tables, sp1Tables_length, sp1ProviderTables_length]
  have interactionsAtOther (i : ℕ) (lower : instructionTableCount ≤ i)
      (upper : i < ensembleTableCount) (bound : i < witness.tables.length)
      (notInit : i ≠ memoryInitProviderIndex) (notFinalize : i ≠ memoryFinalizeProviderIndex)
      (notBump : i ≠ memoryBumpIndex) (notHalt : i ≠ haltIndex) :
      typedTableInteractionsWith witness.tables[i] memoryChannel = [] :=
    witness_nonMemoryProviderTable_memoryInteractions_eq_nil witness i lower upper bound
      notInit notFinalize notBump notHalt
  repeat rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_nil_of_le (by omega)]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp [interactionsAtOther, instructionTableCount, ensembleTableCount, programProviderIndex,
    byteProviderTableCount, rangeProviderTableCount, memoryInitProviderIndex,
    memoryFinalizeProviderIndex, memoryBumpIndex, haltIndex, nonBumpProviderTableCount,
    stateSilentProviderTableCount, memoryInitProviderTable, memoryFinalizeProviderTable,
    memoryBumpTable, haltTable]

/-! ## Exact Memory-channel decomposition of the whole ensemble witness -/

/-- Exact typed Memory-channel decomposition: the decoded instruction rows' Memory interactions,
followed by the init-, finalize-, and — W3 — MemoryBump tables'.  The boundary verifier drops
out. -/
theorem typedEnsembleMemoryInteractions_eq
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    typedEnsembleInteractionsWith witness memoryChannel =
      decodedWitnessInstructionInteractionsWith witness.data witness.tables memoryChannel ++
        (typedTableInteractionsWith (memoryInitProviderTable witness) memoryChannel ++
          (typedTableInteractionsWith (memoryFinalizeProviderTable witness) memoryChannel ++
            (typedTableInteractionsWith (memoryBumpTable witness) memoryChannel ++
              typedTableInteractionsWith (haltTable witness) memoryChannel))) := by
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
          (producedMessages (typedTableInteractionsWith (memoryFinalizeProviderTable witness)
            memoryChannel) ++
            (producedMessages (typedTableInteractionsWith (memoryBumpTable witness)
              memoryChannel) ++
              producedMessages (typedTableInteractionsWith (haltTable witness)
                memoryChannel)))) := by
  rw [typedEnsembleMemoryInteractions_eq, producedMessages_append, producedMessages_append,
    producedMessages_append, producedMessages_append,
    decodedWitnessMemoryInteractions_eq_flatMap, producedMessages_flatMap]
  rfl

/-- Consumed Memory messages of the whole witness: every decoded row's consumed messages, followed by
the two boundary tables' consumed messages.  Mirror of `consumedMessages_typedEnsembleState_eq`. -/
theorem consumedMessages_typedEnsembleMemory_eq
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    consumedMessages (typedEnsembleInteractionsWith witness memoryChannel) =
      (decodedInstructionRows (p := p) witness.tables).flatMap
          (fun decoded => decoded.consumedMemoryMessages witness.data) ++
        (consumedMessages (typedTableInteractionsWith (memoryInitProviderTable witness)
            memoryChannel) ++
          (consumedMessages (typedTableInteractionsWith (memoryFinalizeProviderTable witness)
            memoryChannel) ++
            (consumedMessages (typedTableInteractionsWith (memoryBumpTable witness)
              memoryChannel) ++
              consumedMessages (typedTableInteractionsWith (haltTable witness)
                memoryChannel)))) := by
  rw [typedEnsembleMemoryInteractions_eq, consumedMessages_append, consumedMessages_append,
    consumedMessages_append, consumedMessages_append,
    decodedWitnessMemoryInteractions_eq_flatMap, consumedMessages_flatMap]
  rfl

/-! ## The Memory-channel balance -/

/-- **Clean Memory balance as an exact typed endpoint permutation.** Under Clean channel balance and
binary Memory multiplicities, the produced Memory messages (every decoded row's read-backs/writes plus
the two boundary tables' pushes) are a permutation of the consumed Memory messages (every decoded row's
read-priors plus the two boundary tables' pulls).

`memBinary` is the Memory analogue of the State `binary` premise; it is discharged below by
`witness_memoryMultiplicityBinary` (physical constraints alone), so it is a threaded intermediate
hypothesis here, not an open seam. -/
theorem realDecodedMemory_perm
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (balanced : witness.BalancedChannels)
    (memBinary : ∀ interaction ∈ typedEnsembleInteractionsWith witness memoryChannel,
      signedVal interaction.mult = -1 ∨ signedVal interaction.mult = 0 ∨
        signedVal interaction.mult = 1) :
    ((decodedInstructionRows (p := p) witness.tables).flatMap
        (fun decoded => decoded.producedMemoryMessages witness.data) ++
      (producedMessages (typedTableInteractionsWith (memoryInitProviderTable witness) memoryChannel) ++
        (producedMessages (typedTableInteractionsWith (memoryFinalizeProviderTable witness)
          memoryChannel) ++
          (producedMessages (typedTableInteractionsWith (memoryBumpTable witness)
            memoryChannel) ++
            producedMessages (typedTableInteractionsWith (haltTable witness)
              memoryChannel))))).Perm
    ((decodedInstructionRows (p := p) witness.tables).flatMap
        (fun decoded => decoded.consumedMemoryMessages witness.data) ++
      (consumedMessages (typedTableInteractionsWith (memoryInitProviderTable witness) memoryChannel) ++
        (consumedMessages (typedTableInteractionsWith (memoryFinalizeProviderTable witness)
          memoryChannel) ++
          (consumedMessages (typedTableInteractionsWith (memoryBumpTable witness)
            memoryChannel) ++
            consumedMessages (typedTableInteractionsWith (haltTable witness)
              memoryChannel))))) := by
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
          (producedMessages (typedTableInteractionsWith (memoryFinalizeProviderTable witness)
            memoryChannel) ++
            (producedMessages (typedTableInteractionsWith (memoryBumpTable witness)
              memoryChannel) ++
              producedMessages (typedTableInteractionsWith (haltTable witness)
                memoryChannel))))) : Multiset (MemoryMsg (ZMod p))) =
    Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
      ((decodedInstructionRows (p := p) witness.tables).flatMap
          (fun decoded => decoded.consumedMemoryMessages witness.data) ++
        (consumedMessages (typedTableInteractionsWith (memoryInitProviderTable witness)
            memoryChannel) ++
          (consumedMessages (typedTableInteractionsWith (memoryFinalizeProviderTable witness)
            memoryChannel) ++
            (consumedMessages (typedTableInteractionsWith (memoryBumpTable witness)
              memoryChannel) ++
              consumedMessages (typedTableInteractionsWith (haltTable witness)
                memoryChannel))))) := by
  classical
  rw [Multiset.coe_eq_coe.mpr (realDecodedMemory_perm witness balanced memBinary)]

/-! ## Provider purity: the boundary tables only push (init) / only pull (finalize)

The two premises `initPure`/`finPure` of `MemoryFrontier.memoryFrontierBalance`.  Each boundary
provider emits exactly **one** explicit, boolean-gated Memory interaction per row — the init provider a
`memoryChannel.pushIf m` (`MemoryProviderChip`), the finalize provider a `memoryChannel.pullIf m`
(`MemoryFinalizeChip`) — with `m` forced into `{0, 1}` by the inline `assertZero (m * (m - 1))` gate.
So under `witness.Constraints` the init provider's signed multiplicity is `signedVal m ∈ {0, 1}` (never
`-1`) and the finalize provider's is `signedVal (-m) ∈ {-1, 0}` (never `1`).  Hence the init table
contributes nothing to `consumedMessages` (the `signedVal = -1` side) and the finalize table nothing to
`producedMessages` (the `signedVal = 1` side). -/

/-- `MemoryProviderChip`'s range-check subcircuit declares no channels, so it emits no Memory
interaction; its `FlatOperation.interactions` filtered to `memoryChannel` is empty. -/
lemma wordRangeCheck_no_memory (offset : ℕ) (w : Var Word (ZMod p)) :
    Operations.interactionsWith memoryChannel.toRaw
      [Operation.subcircuit (WordRangeCheck.circuit.toSubcircuit offset w)] = [] := by
  have h := InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil
    WordRangeCheck.circuit memoryChannel.toRaw (n := offset) w ([] : Operations (ZMod p))
    List.not_mem_nil List.not_mem_nil
  rwa [Operations.interactionsWith_nil] at h

/-- The init provider's boolean gate `assertZero (m * (m - 1))` forces its explicit multiplicity
input into `{0, 1}`. -/
theorem memoryInitProvider_gate_binary (input : Var MemoryProviderChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (constraints : ConstraintsHold.Shallow env ((MemoryProviderChip.main input).operations offset)) :
    Expression.eval env input.multiplicity = 0 ∨
      Expression.eval env input.multiplicity = 1 := by
  have allShallow := (constraintsHold_shallow_iff_forall_mem.mp constraints).1
  have gate := allShallow (input.multiplicity * (input.multiplicity - 1))
    (by simp only [MemoryProviderChip.main, circuit_norm, Operations.shallowConstraints,
      List.mem_cons, or_true, true_or])
  simp only [eval_sub, Expression.eval] at gate
  exact bool_of_mul_pred gate

/-- The init provider's only Memory interaction is its single `pushIf input.multiplicity`; the
range-check subcircuit contributes nothing. -/
theorem memoryInitProvider_memoryInteractions
    (input : Var MemoryProviderChip.Inputs (ZMod p)) (offset : ℕ) :
    ((MemoryProviderChip.main input).operations offset).interactionsWith memoryChannel.toRaw =
      [(pushedIf (channel := memoryChannel) input.multiplicity input.toMessage).toRaw] := by
  classical
  simp only [MemoryProviderChip.main, circuit_norm]
  rw [show List.filter (fun i => decide (i.channel = memoryChannel.toRaw))
      (FlatOperation.interactions (WordRangeCheck.circuit.toSubcircuit offset input.value).ops.toFlat)
      = [] from by
    have h := wordRangeCheck_no_memory offset input.value
    simpa [Operations.interactionsWith_subcircuit, Operations.interactionsWith_nil] using h]
  rfl

/-- Every typed Memory interaction the init-provider component emits has multiplicity equal to the
explicit multiplicity input. -/
theorem memoryInitProvider_typedMult (env : Environment (ZMod p))
    (i : TypedInteraction (memoryChannel (p := p)))
    (hi : i ∈ typedInteractionValuesWith (⟨MemoryProviderChip.circuit⟩ : Component (ZMod p)).operations
      memoryChannel env) :
    i.mult = env.get (size MemoryMsg) := by
  have hint : (⟨MemoryProviderChip.circuit⟩ : Component (ZMod p)).operations.interactionsWith
      memoryChannel.toRaw =
      [(pushedIf (channel := memoryChannel)
        (varFromOffset MemoryProviderChip.Inputs 0).multiplicity
        (varFromOffset MemoryProviderChip.Inputs 0).toMessage).toRaw] := by
    rw [Component.interactionsWith_eq, Component.rowOperations_mk]
    exact memoryInitProvider_memoryInteractions (varFromOffset MemoryProviderChip.Inputs 0)
      (size MemoryProviderChip.Inputs)
  have hraw : i.raw ∈ (typedInteractionValuesWith
      (⟨MemoryProviderChip.circuit⟩ : Component (ZMod p)).operations memoryChannel env).map
      TypedInteraction.raw := List.mem_map_of_mem hi
  rw [typedInteractionValuesWith_raw, Operations.interactionValuesWith_eq_map, hint] at hraw
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at hraw
  rw [TypedInteraction.mult, hraw]
  simp only [AbstractInteraction.eval, ChannelInteraction.toRaw_mult, pushedIf_mult,
    MemoryProviderChip.Inputs.varFromOffset_multiplicity, Expression.eval, Nat.zero_add]

/-- Every active init-provider Memory interaction has signed multiplicity in `{0, 1}` (a push at a
boolean gate), never `-1`. -/
theorem memoryInitProvider_signedVal (env : Environment (ZMod p))
    (constraints : (⟨MemoryProviderChip.circuit⟩ : Component (ZMod p)).operations.ConstraintsHold env)
    (i : TypedInteraction (memoryChannel (p := p)))
    (hi : i ∈ typedInteractionValuesWith (⟨MemoryProviderChip.circuit⟩ : Component (ZMod p)).operations
      memoryChannel env) :
    signedVal i.mult = 0 ∨ signedVal i.mult = 1 := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 24 < p); omega
  have hmult := memoryInitProvider_typedMult env i hi
  have shallow := shallowConstraints_of_componentConstraints MemoryProviderChip.circuit env constraints
  have hbool := memoryInitProvider_gate_binary (varFromOffset MemoryProviderChip.Inputs 0)
    (size MemoryProviderChip.Inputs) env shallow
  simp only [MemoryProviderChip.Inputs.varFromOffset_multiplicity, Expression.eval,
    Nat.zero_add] at hbool
  rw [hmult, signedVal_is_real hp hbool]
  rcases val_of_binary hp hbool with hv | hv <;> simp [hv]

omit [Fact (2 ^ 24 < p)] in
/-- Shared tail of `initPure`/`finPure`: a message list is empty once no interaction in it carries
the selecting signed multiplicity. -/
private lemma map_message_filter_eq_nil {c : ℤ}
    (interactions : List (TypedInteraction (memoryChannel (p := p))))
    (h : ∀ i ∈ interactions, signedVal i.mult ≠ c) :
    (interactions.filter fun i => signedVal i.mult = c).map TypedInteraction.message = [] := by
  have hfilter : (interactions.filter fun i => signedVal i.mult = c) = [] :=
    List.filter_eq_nil_iff.mpr fun i hi => by simpa using h i hi
  rw [hfilter, List.map_nil]

/-- Table-level form of `memoryInitProvider_signedVal`: every typed Memory interaction of the
init-provider *table* is a boolean-gated push, its per-row circuit constraints coming from
`witness.Constraints`. -/
private theorem memoryInitProviderTable_signedVal
    (witness : EnsembleWitness (sp1Ensemble (p := p))) (constraints : witness.Constraints)
    (i : TypedInteraction (memoryChannel (p := p)))
    (hi : i ∈ typedTableInteractionsWith (memoryInitProviderTable witness) memoryChannel) :
    signedVal i.mult = 0 ∨ signedVal i.mult = 1 := by
  rw [typedTableInteractionsWith] at hi
  obtain ⟨row, rowMem, hi⟩ := List.mem_flatMap.mp hi
  rw [memoryInitProviderTable_component witness] at hi
  have tableConstraints : (memoryInitProviderTable witness).Constraints :=
    constraints (memoryInitProviderTable witness) (witness.mem_allTables_of_mem_tables
      (List.getElem_mem (memoryInitProviderIndex_lt_tablesLength witness)))
  have rowConstraints := tableConstraints row rowMem
  rw [memoryInitProviderTable_component witness] at rowConstraints
  exact memoryInitProvider_signedVal _ rowConstraints i hi

/-- **`initPure`.** The Memory-init boundary provider only pushes, so it contributes nothing to the
Memory channel's consumed side: `consumedMessages` (the `signedVal = -1` filter) is empty. -/
theorem initPure (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) :
    consumedMessages (typedTableInteractionsWith (memoryInitProviderTable witness) memoryChannel)
      = [] := by
  have key : ∀ i ∈ typedTableInteractionsWith (memoryInitProviderTable witness) memoryChannel,
      signedVal i.mult ≠ -1 := fun i hi => by
    rcases memoryInitProviderTable_signedVal witness constraints i hi with h | h <;> rw [h] <;>
      norm_num
  unfold consumedMessages
  exact map_message_filter_eq_nil _ key

omit [Fact (2 ^ 24 < p)] in
/-- The finalize provider's only Memory interaction is its single explicit-multiplicity pull. -/
theorem memoryFinalizeProvider_memoryInteractions
    (input : Var MemoryFinalizeChip.Inputs (ZMod p)) (offset : ℕ) :
    ((MemoryFinalizeChip.main input).operations offset).interactionsWith memoryChannel.toRaw =
      [(pulledIf (channel := memoryChannel) input.multiplicity input.toMessage).toRaw] := by
  simp only [MemoryFinalizeChip.main, circuit_norm]

omit [Fact (2 ^ 24 < p)] in
/-- The finalize provider's boolean gate forces its explicit multiplicity input into `{0, 1}`. -/
theorem memoryFinalizeProvider_gate_binary
    (input : Var MemoryFinalizeChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (constraints : ConstraintsHold.Shallow env ((MemoryFinalizeChip.main input).operations offset)) :
    Expression.eval env input.multiplicity = 0 ∨
      Expression.eval env input.multiplicity = 1 := by
  have allShallow := (constraintsHold_shallow_iff_forall_mem.mp constraints).1
  have gate := allShallow (input.multiplicity * (input.multiplicity - 1))
    (by simp only [MemoryFinalizeChip.main, circuit_norm, Operations.shallowConstraints,
      List.mem_cons, true_or])
  simp only [eval_sub, Expression.eval] at gate
  exact bool_of_mul_pred gate

omit [Fact (2 ^ 24 < p)] in
/-- Every typed Memory interaction the finalize-provider component emits has multiplicity `-m`, the
negation of its explicit selector input. -/
theorem memoryFinalizeProvider_typedMult (env : Environment (ZMod p))
    (i : TypedInteraction (memoryChannel (p := p)))
    (hi : i ∈ typedInteractionValuesWith (⟨MemoryFinalizeChip.circuit⟩ : Component (ZMod p)).operations
      memoryChannel env) :
    i.mult = -(env.get (size MemoryMsg)) := by
  have hint : (⟨MemoryFinalizeChip.circuit⟩ : Component (ZMod p)).operations.interactionsWith
      memoryChannel.toRaw =
      [(pulledIf (channel := memoryChannel)
        (varFromOffset MemoryFinalizeChip.Inputs 0).multiplicity
        (varFromOffset MemoryFinalizeChip.Inputs 0).toMessage).toRaw] := by
    rw [Component.interactionsWith_eq, Component.rowOperations_mk]
    exact memoryFinalizeProvider_memoryInteractions (varFromOffset MemoryFinalizeChip.Inputs 0)
      (size MemoryFinalizeChip.Inputs)
  have hraw : i.raw ∈ (typedInteractionValuesWith
      (⟨MemoryFinalizeChip.circuit⟩ : Component (ZMod p)).operations memoryChannel env).map
      TypedInteraction.raw := List.mem_map_of_mem hi
  rw [typedInteractionValuesWith_raw, Operations.interactionValuesWith_eq_map, hint] at hraw
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at hraw
  rw [TypedInteraction.mult, hraw]
  simp only [AbstractInteraction.eval, ChannelInteraction.toRaw_mult, pulledIf_mult,
    MemoryFinalizeChip.Inputs.varFromOffset_multiplicity, Expression.eval, Nat.zero_add, neg_one_mul]

/-- Every active finalize-provider Memory interaction has signed multiplicity in `{-1, 0}` (a pull at
a boolean gate), never `1`. -/
theorem memoryFinalizeProvider_signedVal (env : Environment (ZMod p))
    (constraints : (⟨MemoryFinalizeChip.circuit⟩ : Component (ZMod p)).operations.ConstraintsHold env)
    (i : TypedInteraction (memoryChannel (p := p)))
    (hi : i ∈ typedInteractionValuesWith (⟨MemoryFinalizeChip.circuit⟩ : Component (ZMod p)).operations
      memoryChannel env) :
    signedVal i.mult = 0 ∨ signedVal i.mult = -1 := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 24 < p); omega
  have hmult := memoryFinalizeProvider_typedMult env i hi
  have shallow :=
    shallowConstraints_of_componentConstraints MemoryFinalizeChip.circuit env constraints
  have hbool := memoryFinalizeProvider_gate_binary (varFromOffset MemoryFinalizeChip.Inputs 0)
    (size MemoryFinalizeChip.Inputs) env shallow
  simp only [MemoryFinalizeChip.Inputs.varFromOffset_multiplicity, Expression.eval,
    Nat.zero_add] at hbool
  rw [hmult, signedVal_neg_is_real hp hbool]
  rcases val_of_binary hp hbool with hv | hv <;> simp [hv]

/-- Table-level form of `memoryFinalizeProvider_signedVal` (finalize analogue of
`memoryInitProviderTable_signedVal`). -/
private theorem memoryFinalizeProviderTable_signedVal
    (witness : EnsembleWitness (sp1Ensemble (p := p))) (constraints : witness.Constraints)
    (i : TypedInteraction (memoryChannel (p := p)))
    (hi : i ∈ typedTableInteractionsWith (memoryFinalizeProviderTable witness) memoryChannel) :
    signedVal i.mult = 0 ∨ signedVal i.mult = -1 := by
  rw [typedTableInteractionsWith] at hi
  obtain ⟨row, rowMem, hi⟩ := List.mem_flatMap.mp hi
  rw [memoryFinalizeProviderTable_component witness] at hi
  have tableConstraints : (memoryFinalizeProviderTable witness).Constraints :=
    constraints (memoryFinalizeProviderTable witness) (witness.mem_allTables_of_mem_tables
      (List.getElem_mem (memoryFinalizeProviderIndex_lt_tablesLength witness)))
  have rowConstraints := tableConstraints row rowMem
  rw [memoryFinalizeProviderTable_component witness] at rowConstraints
  exact memoryFinalizeProvider_signedVal _ rowConstraints i hi

/-- **`finPure`.** The Memory-finalize boundary provider only pulls, so it contributes nothing to the
Memory channel's produced side: `producedMessages` (the `signedVal = 1` filter) is empty. -/
theorem finPure (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) :
    producedMessages (typedTableInteractionsWith (memoryFinalizeProviderTable witness) memoryChannel)
      = [] := by
  have key : ∀ i ∈ typedTableInteractionsWith (memoryFinalizeProviderTable witness) memoryChannel,
      signedVal i.mult ≠ 1 := fun i hi => by
    rcases memoryFinalizeProviderTable_signedVal witness constraints i hi with h | h <;> rw [h] <;>
      norm_num
  unfold producedMessages
  exact map_message_filter_eq_nil _ key

/-! ## Witness-level structural Memory obligations -/

omit [Fact (2 ^ 24 < p)] in
/-- The MemoryBump circuit's inline boolean gate, extracted from the shallow constraint list. -/
private theorem memoryBump_gate_binary [Fact (2 ^ 17 < p)]
    (r : Var MemoryBumpChip.Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : ConstraintsHold.Shallow env ((MemoryBumpChip.main r).operations offset)) :
    (ProvableStruct.eval env r).is_real = 0 ∨ (ProvableStruct.eval env r).is_real = 1 := by
  have allShallow := (constraintsHold_shallow_iff_forall_mem.mp constraints).1
  have gate := allShallow (r.is_real * (r.is_real - 1)) (by
    change (r.is_real * (r.is_real - 1)) ∈ Operations.shallowConstraints
      ([.assert _, .interact _, .interact _, .interact _, .interact _, .assert _, .assert _,
        .assert _, .interact _, .interact _, .interact _, .interact _] : Operations (ZMod p))
    simp only [circuit_norm, Operations.shallowConstraints, List.mem_cons, true_or])
  simp only [circuit_norm] at gate
  exact bool_of_mul_pred gate

/-- Every MemoryBump row's selector is boolean, from its table constraints alone (the inline gate
is an ungated assert — no channel guarantee is needed, so this is non-circular for the memory
balance). -/
private theorem memoryBumpTable_is_real_binary
    (witness : EnsembleWitness (sp1Ensemble (p := p))) (constraints : witness.Constraints) :
    ∀ row ∈ (memoryBumpTable witness).table,
      (memoryBumpRow (memoryBumpTable witness) row).is_real = 0 ∨
        (memoryBumpRow (memoryBumpTable witness) row).is_real = 1 := by
  haveI : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  intro row rowMem
  have tableConstraints : (memoryBumpTable witness).Constraints :=
    constraints _ (witness.mem_allTables_of_mem_tables
      (List.getElem_mem (memoryBumpIndex_lt_tablesLength witness)))
  have rowConstraints := tableConstraints row rowMem
  rw [memoryBumpTable_component witness] at rowConstraints
  have shallow := shallowConstraints_of_componentConstraints MemoryBumpChip.circuit
    ((memoryBumpTable witness).environment row) rowConstraints
  have hbool := memoryBump_gate_binary (varFromOffset MemoryBumpChip.Inputs 0)
    (size MemoryBumpChip.Inputs) ((memoryBumpTable witness).environment row) shallow
  rw [show (memoryBumpRow (memoryBumpTable witness) row).is_real =
      (ProvableStruct.eval ((memoryBumpTable witness).environment row)
        (varFromOffset MemoryBumpChip.Inputs 0 :
          Var MemoryBumpChip.Inputs (ZMod p))).is_real from by
    rw [memoryBumpRow_eq, ProvableStruct.eval_eq_eval]]
  exact hbool

/-- Every typed Memory interaction of the MemoryBump table is boolean-gated: a pull (`-is_real`),
padding (`0`), or a push (`+is_real`). -/
private theorem memoryBumpTable_signedVal
    (witness : EnsembleWitness (sp1Ensemble (p := p))) (constraints : witness.Constraints)
    (i : TypedInteraction (memoryChannel (p := p)))
    (hi : i ∈ typedTableInteractionsWith (memoryBumpTable witness) memoryChannel) :
    signedVal i.mult = -1 ∨ signedVal i.mult = 0 ∨ signedVal i.mult = 1 := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 24 < p); omega
  rw [memoryBumpTable_typedMemory] at hi
  obtain ⟨row, rowMem, hi⟩ := List.mem_flatMap.mp hi
  have hbool := memoryBumpTable_is_real_binary witness constraints row rowMem
  rcases List.mem_cons.mp hi with rfl | hi
  · rw [TypedInteraction.pulledIfValue_mult, signedVal_neg_is_real hp hbool]
    rcases val_of_binary hp hbool with hv | hv <;> rw [hv] <;> norm_num
  · rw [List.mem_singleton.mp hi, TypedInteraction.pushedIfValue_mult,
      signedVal_is_real hp hbool]
    rcases val_of_binary hp hbool with hv | hv <;> rw [hv] <;> norm_num

private theorem haltTable_memory_signedVal
    (witness : EnsembleWitness (sp1Ensemble (p := p))) (constraints : witness.Constraints)
    (i : TypedInteraction (memoryChannel (p := p)))
    (hi : i ∈ typedTableInteractionsWith (haltTable witness) memoryChannel) :
    signedVal i.mult = -1 ∨ signedVal i.mult = 0 ∨ signedVal i.mult = 1 := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 24 < p); omega
  rw [haltTable_typedMemory] at hi
  obtain ⟨row, rowMem, hi⟩ := List.mem_flatMap.mp hi
  have hbool := witness_haltRows_selectorBinary witness constraints row rowMem
  have pullCase : ∀ msg : MemoryMsg (ZMod p),
      i = TypedInteraction.pulledIfValue memoryChannel
        (haltRow (haltTable witness) row).is_real msg →
      signedVal i.mult = -1 ∨ signedVal i.mult = 0 ∨ signedVal i.mult = 1 := by
    rintro msg rfl
    rw [TypedInteraction.pulledIfValue_mult, signedVal_neg_is_real hp hbool]
    rcases val_of_binary hp hbool with hv | hv <;> rw [hv] <;> norm_num
  have pushCase : ∀ msg : MemoryMsg (ZMod p),
      i = TypedInteraction.pushedIfValue memoryChannel
        (haltRow (haltTable witness) row).is_real msg →
      signedVal i.mult = -1 ∨ signedVal i.mult = 0 ∨ signedVal i.mult = 1 := by
    rintro msg rfl
    rw [TypedInteraction.pushedIfValue_mult, signedVal_is_real hp hbool]
    rcases val_of_binary hp hbool with hv | hv <;> rw [hv] <;> norm_num
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullCase _ rfl
  · exact pushCase _ rfl
  · exact pullCase _ rfl
  · exact pushCase _ rfl
  · exact pullCase _ rfl
  · exact pushCase _ rfl

/-- Physical constraints alone give the signed-binary multiplicity bound for every Memory
interaction in the supported ensemble.  Instruction rows use the registry-wide selector-gating
theorem; the only provider participants use their own boolean multiplicity columns. -/
theorem witness_memoryMultiplicityBinary
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) :
    ∀ interaction ∈ typedEnsembleInteractionsWith witness memoryChannel,
      signedVal interaction.mult = -1 ∨ signedVal interaction.mult = 0 ∨
        signedVal interaction.mult = 1 := by
  rw [typedEnsembleMemoryInteractions_eq]
  intro interaction interactionMem
  rcases List.mem_append.mp interactionMem with instructionMem | providerMem
  · rw [decodedWitnessMemoryInteractions_eq_flatMap] at instructionMem
    obtain ⟨decoded, decodedMem, rowInteractionMem⟩ := List.mem_flatMap.mp instructionMem
    exact decoded.memoryInteractions_signedBinary witness.data witness.tables decodedMem
      (decodedInstructionRow_constraints witness constraints decoded decodedMem)
      interaction rowInteractionMem
  · rcases List.mem_append.mp providerMem with initMem | tailMem
    · rcases memoryInitProviderTable_signedVal witness constraints interaction initMem with
        zero | positive
      · exact Or.inr (Or.inl zero)
      · exact Or.inr (Or.inr positive)
    rcases List.mem_append.mp tailMem with finalizeMem | bumpMem
    · rcases memoryFinalizeProviderTable_signedVal witness constraints interaction finalizeMem with
        zero | negative
      · exact Or.inr (Or.inl zero)
      · exact Or.inl negative
    rcases List.mem_append.mp bumpMem with bumpMem | haltMem
    · exact memoryBumpTable_signedVal witness constraints interaction bumpMem
    · exact haltTable_memory_signedVal witness constraints interaction haltMem

/-- A constrained padding instruction row has no active Memory message.  This is a direct
consequence of selector booleanity and the fact that every retained Memory interaction is gated by
that selector; it is not an execution or trace-generation assumption. -/
theorem witness_paddingMemoryEmpty
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) :
    ∀ decoded ∈ decodedInstructionRows (p := p) witness.tables,
      (decoded.toChipRow witness.data).is_real ≠ 1 →
        decoded.producedMemoryMessages witness.data = [] ∧
          decoded.consumedMemoryMessages witness.data = [] := by
  intro decoded decodedMem padding
  exact decoded.paddingMemoryMessages_eq_nil witness.data witness.tables decodedMem
    (decodedInstructionRow_constraints witness constraints decoded decodedMem) padding

end SP1Clean.Soundness
