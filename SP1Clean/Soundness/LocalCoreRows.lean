import SP1Clean.Soundness.LocalCoreMemory
import SP1Clean.Soundness.LocalCoreDecode
import SP1Clean.Soundness.CoreTableProjection

/-! # Physical mixed rows of the local shard assembly

The physical instruction and system tables decode into one execution-row carrier. Memory refresh
pairs remain separate because they do not execute instructions. Exact ledger projections remove
only disabled rows and Memory-silent providers, retaining every active HALT and syscall occurrence.
This module establishes the row-level balance needed before refresh elimination and timed walking;
it does not assert an execution order or host semantics.
-/

namespace SP1Clean.Soundness.LocalCore

open SP1Clean.Soundness.NativeCore (ExecutionRow typedTableInteractions_nil byteProvider_channel_silent
  flatMap_split flatMap_filter_inactive pushesAt_flatMap pullsAt_flatMap verifier_state_interactions_of_values)
open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics
open TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

private theorem witness_length {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) : witness.tables.length = 61 := by
  rw [← witness.same_length]
  exact tables_length image source

/-- The fixed register inventory is separate from the sparse source Memory providers. -/
def registerMembershipTable {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) : Table (ZMod p) :=
  witness.tables[59]'(by have := witness_length witness; omega)

theorem registerMembershipTable_component {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    (registerMembershipTable witness).component =
      SnapshotMemoryEnsemble.registerMembership source.sail.memorySnapshot :=
  (witness.same_circuits 59 (by change 59 < (tables image source).length; rw [tables_length]; decide)).symm

/-- Fixed interval rows remain in the physical inventory, independently of RAM demand. -/
def ramMembershipTable {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) : Table (ZMod p) :=
  witness.tables[60]'(by have := witness_length witness; omega)

theorem ramMembershipTable_component {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    (ramMembershipTable witness).component = SnapshotMemoryEnsemble.ramMembership source.sail.memorySnapshot :=
  (witness.same_circuits 60 (by
    change 60 < (tables image source).length
    rw [tables_length]; decide)).symm

/-- Fixed membership contributes only its own ledger, including all zero-count rows. -/
theorem ramMembershipTable_silent {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (channel : RawChannel (ZMod p)) (different : channel.name ≠ "sp1.native.initial_memory") :
    channel ∉ (ramMembershipTable witness).component.circuit.channels := by
  rw [ramMembershipTable_component]
  change channel ∉ [(InitialMemoryLookup.membership source.sail.memorySnapshot.memory (2 ^ 48)
    "sp1.native.initial_memory").channel.toRaw]
  intro member
  exact different (congrArg RawChannel.name (List.mem_singleton.mp member))

/-- The physical refresh, StateBump, HALT, and syscall tables, in their registered order. -/
def systemTable {image : ProgramImage} {source : ExecutionSnapshot} (witness : EnsembleWitness (ensemble (p := p) image source))
    (index : Fin 4) : Table (ZMod p) :=
  witness.tables[55 + index.val]'(by have := witness_length witness; omega)

theorem systemTable_component {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) (index : Fin 4) :
    (systemTable witness index).component =
      ([{ circuit := MemoryBumpChip.circuit }, { circuit := StateBumpChip.circuit }, { circuit := HaltChip.circuit },
        { circuit := SyscallInstrsChip.circuit }] : List (Component (ZMod p)))[index.val] := by
  have same := witness.same_circuits (55 + index.val)
    (by change 55 + index.val < (tables image source).length; rw [tables_length]; omega)
  apply same.symm.trans
  fin_cases index <;> rfl

theorem systemTable_mem {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) (index : Fin 4) :
    systemTable witness index ∈ witness.tables :=
  List.getElem_mem _

theorem systemTable_constraints {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) (constraints : witness.Constraints)
    (index : Fin 4) : (systemTable witness index).Constraints witness.data :=
  constraints _ (systemTable_mem witness index)

private theorem systemTables_eq {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    witness.tables.drop 55 = [systemTable witness 0, systemTable witness 1,
      systemTable witness 2, systemTable witness 3, registerMembershipTable witness, ramMembershipTable witness] := by
  have length := witness_length witness
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
    List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
    List.drop_eq_getElem_cons (by omega),
    List.drop_eq_getElem_cons (by omega),
    List.drop_eq_nil_of_le (by omega)]
  rfl

private theorem byteTables_memory_silent {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    ((witness.tables.drop 32).take 23).flatMap (typedTableInteractionsWith · witness.data memoryChannel) = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro table member
  apply typedTableInteractions_nil
  have mapped := List.mem_map_of_mem (f := fun t : Table (ZMod p) => t.component) member
  rw [List.map_take, List.map_drop, witness.tables_map_component] at mapped
  change table.component ∈ (sp1ProviderTables (p := p)).take 23 at mapped
  exact byteProvider_channel_silent table.component mapped memoryChannel.toRaw
    (by simp [memoryChannel_eq_byteChannel_false])

/-- The complete physical Memory interior: ordinary rows plus the three participating system
tables. Fixed Program, Byte/Range, and StateBump are proved Memory-silent. -/
theorem memoryInterior_split {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    memoryInterior witness =
      (instructionTables witness).flatMap (typedTableInteractionsWith · witness.data memoryChannel) ++
      typedTableInteractionsWith (systemTable witness 0) witness.data memoryChannel ++
      typedTableInteractionsWith (systemTable witness 2) witness.data memoryChannel ++
      typedTableInteractionsWith (systemTable witness 3) witness.data memoryChannel := by
  have programSilent : typedTableInteractionsWith (programTable witness) witness.data memoryChannel = [] := by
    apply typedTableInteractions_nil
    rw [programTable_component]
    change memoryChannel.toRaw ∉ [programChannel.toRaw]
    simp [memoryChannel_eq_programChannel_false]
  have stateSilent : typedTableInteractionsWith (systemTable witness 1) witness.data memoryChannel = [] := by
    apply typedTableInteractions_nil
    rw [systemTable_component]
    change memoryChannel.toRaw ∉ [byteChannel.toRaw, stateChannel.toRaw]
    simp [memoryChannel_eq_byteChannel_false, memoryChannel_eq_stateChannel_false]
  have registerSilent : typedTableInteractionsWith (registerMembershipTable witness) witness.data memoryChannel = [] := by
    apply typedTableInteractions_nil
    rw [registerMembershipTable_component]
    change memoryChannel.toRaw ∉ [source.sail.memorySnapshot.registerTable.channel.toRaw]
    simp [memoryChannel, StaticTable.channel, MemorySnapshot.registerTable, StaticTable.ofRows, Channel.toRaw]
  have ramSilent : typedTableInteractionsWith (ramMembershipTable witness) witness.data memoryChannel = [] := by
    apply typedTableInteractions_nil
    exact ramMembershipTable_silent witness _ (by simp [memoryChannel, Channel.toRaw])
  have head : witness.tables.drop 6 = programTable witness :: witness.tables.drop 7 := by
    rw [List.drop_eq_getElem_cons (by have := witness_length witness; omega)]
    rfl
  rw [memoryInterior, head, List.flatMap_cons, programSilent, List.nil_append,
    flatMap_split witness.tables _ 7 25, flatMap_split witness.tables _ 32 23,
    byteTables_memory_silent, List.nil_append, systemTables_eq]
  simp only [List.flatMap_cons, List.flatMap_nil, stateSilent, ramSilent, registerSilent, List.nil_append,
    List.append_nil, List.append_assoc, instructionTables]

/-- Active ordinary rows decoded from the unchanged physical instruction batch. -/
noncomputable def activeInstructionRows {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) : List (DecodedInstructionRow p) :=
  (instructionRows witness).filter (fun row => (row.toChipRow witness.data).is_real = 1)

/-- The complete physical event inventory, before State-bus ordering. -/
noncomputable def executionRows {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) : List (ExecutionRow p) :=
  (activeInstructionRows witness).map .instruction ++
    (activeSystemRows (systemTable witness 2) (haltRow witness.data) (·.is_real)).map .halt ++
    (activeSystemRows (systemTable witness 3) (syscallInstrsRow witness.data) (·.is_real)).map .syscall

/-- Actual active refresh pairs, kept separate from instruction execution. -/
noncomputable def memoryRefreshes {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    List (MemoryMsg (ZMod p) × MemoryMsg (ZMod p)) :=
  (activeSystemRows (systemTable witness 0) (memoryBumpRow witness.data) (·.is_real)).flatMap MemoryBumpChip.memoryPairs

/-- Selecting active ordinary rows preserves both complete Memory message lists. -/
theorem activeInstructionRows_memory {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) (constraints : witness.Constraints) :
    producedMessages ((instructionTables witness).flatMap (typedTableInteractionsWith · witness.data memoryChannel)) =
        (activeInstructionRows witness).flatMap (·.producedMemoryMessages witness.data) ∧
    consumedMessages ((instructionTables witness).flatMap (typedTableInteractionsWith · witness.data memoryChannel)) =
        (activeInstructionRows witness).flatMap (·.consumedMemoryMessages witness.data) := by
  have ledger : (instructionTables witness).flatMap (typedTableInteractionsWith · witness.data memoryChannel) =
      (instructionRows witness).flatMap (·.interactionsWith witness.data memoryChannel) :=
    (decodedInstructionInteractionsWith_eq_tables witness.data memoryChannel
      (instructionTables_aligned witness)).symm
  have padding : ∀ row ∈ instructionRows witness, (row.toChipRow witness.data).is_real ≠ 1 →
      row.producedMemoryMessages witness.data = [] ∧ row.consumedMemoryMessages witness.data = [] := by
    intro row member disabled
    exact row.paddingMemoryMessages_eq_nil witness.data (witness.tables.drop 7) member
      (instructionRows_constraints witness constraints row member) disabled
  rw [ledger, producedMessages_flatMap, consumedMessages_flatMap]
  constructor
  · exact (flatMap_filter_inactive _ _ _ (fun row member inactive =>
      (padding row member (by simpa using inactive)).1)).symm
  · exact (flatMap_filter_inactive _ _ _ (fun row member inactive =>
      (padding row member (by simpa using inactive)).2)).symm

/-- The mixed execution carrier plus the separate refresh pairs accounts for exactly the
interior's active Memory messages, at every location and with their full multiplicities. -/
theorem executionRows_memory_projection {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (loc : MemLoc) :
    pushesAt ((executionRows witness).map (ExecutionRow.facts witness.data)) loc +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑((memoryRefreshes witness).map Prod.snd) : Multiset _) =
      Multiset.filter (fun message => MemoryMsg.locOf message = loc)
        (↑(producedMessages (memoryInterior witness)) : Multiset _) ∧
    pullsAt ((executionRows witness).map (ExecutionRow.facts witness.data)) loc +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑((memoryRefreshes witness).map Prod.fst) : Multiset _) =
      Multiset.filter (fun message => MemoryMsg.locOf message = loc)
        (↑(consumedMessages (memoryInterior witness)) : Multiset _) := by
  have ordinary := activeInstructionRows_memory witness constraints
  have refresh := memoryBumpRows_projection (systemTable witness 0) witness.data (systemTable_component witness 0)
    (systemTable_constraints witness constraints 0)
  have halt := haltRows_projection (systemTable witness 2) witness.data (systemTable_component witness 2)
    (systemTable_constraints witness constraints 2)
  have syscall := syscallRows_projection (systemTable witness 3) witness.data (systemTable_component witness 3)
    (systemTable_constraints witness constraints 3)
  rw [pushesAt_flatMap, pullsAt_flatMap, memoryInterior_split]
  simp only [producedMessages_append, consumedMessages_append, ordinary.1, ordinary.2,
    refresh.1, refresh.2, halt.1, halt.2, syscall.1, syscall.2,
    executionRows, List.map_append, List.flatMap_append, List.flatMap_map, ExecutionRow.facts,
    DecodedInstructionRow.ordinaryRowFacts_memPushes, DecodedInstructionRow.ordinaryRowFacts_memPulls,
    haltRowFacts, syscallRowFacts, SyscallInstrsChip.memoryPairs, memoryRefreshes,
    List.map_flatMap, List.map_map, Function.comp_def, List.map_id_fun',
    List.map_cons, List.map_nil, filter_coe_append]
  constructor <;> ac_rfl

/-- The authenticated Memory balance in the timed engine's row vocabulary. All active instruction,
HALT, and syscall rows are absorbed exactly once; actual refresh pairs are the only side terms. -/
theorem executionRows_memory_balance {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) (loc : MemLoc) :
    optMS (memoryInitialFrontier witness loc) +
        pushesAt ((executionRows witness).map (ExecutionRow.facts witness.data)) loc +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑((memoryRefreshes witness).map Prod.snd) : Multiset _) =
      optMS (memoryFinalFrontier witness loc) +
        pullsAt ((executionRows witness).map (ExecutionRow.facts witness.data)) loc +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑((memoryRefreshes witness).map Prod.fst) : Multiset _) := by
  rw [add_assoc, add_assoc, (executionRows_memory_projection witness constraints loc).1,
    (executionRows_memory_projection witness constraints loc).2]
  exact memory_frontier_balance witness constraints balanced loc

end SP1Clean.Soundness.LocalCore
