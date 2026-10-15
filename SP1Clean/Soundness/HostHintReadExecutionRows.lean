import SP1Clean.Soundness.HostLocalCoreRows
import SP1Clean.Soundness.HostHintReadCPUMemory
import SP1Clean.Soundness.HostQueueCallProjection
import SP1Clean.Soundness.HostLocalCoreProgram

/-! # CPU execution rows with their installed hint Memory effects

Each event keeps its State edge and fetch and adds the physical hint words assigned to it by
the two installed ledgers. The present source registry derives absence of WRITE, so its wrapper's
x12 pair is disabled; this is a proved property of that registry, not an inactivity premise or
a restriction on the eventual eight-call capstone. Future WRITE installation must retain that pair.
-/

namespace SP1Clean.Soundness.HostHintReadCPU

open Circuit Air.Flat Channels Model.Core Semantics NativeCore HostHintReadLocal TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance executionClockBound : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance executionLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- The original CPU event and its complete additional hint-word footprint. -/
noncomputable def eventFacts (data : ProverData (ZMod p)) (words : List (HintReadCoverage.Row (p := p)))
    (event : ExecutionRow p) : RowFacts p :=
  { event.facts data with
    memPulls := (event.facts data).memPulls ++ (wordsAt data words event).map (fun row => (touch row).1)
    memPushes := (event.facts data).memPushes ++ (wordsAt data words event).map (fun row => (touch row).2) }

/-- Added Memory effects preserve the complete instruction State edge and committed fetch. -/
theorem eventFacts_state_fetch (data : ProverData (ZMod p)) (words : List (HintReadCoverage.Row (p := p)))
    (event : ExecutionRow p) :
    (eventFacts data words event).statePull = (event.facts data).statePull ∧
      (eventFacts data words event).statePush = (event.facts data).statePush ∧
      (eventFacts data words event).fetch = (event.facts data).fetch := ⟨rfl, rfl, rfl⟩

/-- The enlarged execution rows add exactly their grouped words to both Memory aggregates. -/
theorem eventFacts_memory (data : ProverData (ZMod p)) (words : List (HintReadCoverage.Row (p := p)))
    (cpu : List (ExecutionRow p)) (loc : MemLoc) :
    TimedGrounding.pushesAt (cpu.map (eventFacts data words)) loc =
        TimedGrounding.pushesAt (cpu.map (ExecutionRow.facts data)) loc +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑((cpu.flatMap (wordsAt data words)).map (fun row => (touch row).2)) : Multiset _) ∧
    TimedGrounding.pullsAt (cpu.map (eventFacts data words)) loc =
        TimedGrounding.pullsAt (cpu.map (ExecutionRow.facts data)) loc +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑((cpu.flatMap (wordsAt data words)).map (fun row => (touch row).1.1)) : Multiset _) := by
  constructor
  · have split := (List.flatMap_append_perm cpu (fun event => (event.facts data).memPushes)
      (fun event => (wordsAt data words event).map (fun row => (touch row).2))).symm
    have same := congrArg (Multiset.filter (fun message => MemoryMsg.locOf message = loc))
      (Multiset.coe_eq_coe.mpr split)
    simpa only [pushesAt_flatMap, List.flatMap_map, Function.comp_def, eventFacts, List.map_flatMap,
      filter_coe_append] using same
  · have split := (List.flatMap_append_perm cpu (fun event => (event.facts data).memPulls.map Prod.fst)
      (fun event => (wordsAt data words event).map (fun row => (touch row).1.1))).symm
    have same := congrArg (Multiset.filter (fun message => MemoryMsg.locOf message = loc))
      (Multiset.coe_eq_coe.mpr split)
    simpa only [pullsAt_flatMap, List.flatMap_map, Function.comp_def, eventFacts, List.map_append,
      List.map_map, List.map_flatMap, filter_coe_append] using same

private theorem unit_signs : signedVal (1 : ZMod p) = 1 ∧ signedVal (-1 : ZMod p) = -1 := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 25 < p); omega
  constructor
  · rw [signedVal_is_real hp (Or.inr rfl), ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
    norm_num
  · rw [signedVal_neg_is_real hp (Or.inr rfl), ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
    norm_num

/-- Both physical word variants emit exactly one prior and one pushed complete record. -/
theorem word_memory_messages (tables : List (Table (ZMod p))) (data : ProverData (ZMod p))
    (aligned : List.Forall₂ (fun last table => (HintReadCoverage.view last).component = table.component)
      HintReadCoverage.variants tables) :
    producedMessages (tables.flatMap (typedTableInteractionsWith · data memoryChannel)) =
        (TransitionView.readIndexedRows HintReadCoverage.variants tables data).map (fun row => (touch row).2) ∧
      consumedMessages (tables.flatMap (typedTableInteractionsWith · data memoryChannel)) =
        (TransitionView.readIndexedRows HintReadCoverage.variants tables data).map (fun row => (touch row).1.1) := by
  have ledger : tables.flatMap (typedTableInteractionsWith · data memoryChannel) =
      (TransitionView.readIndexedRows HintReadCoverage.variants tables data).flatMap (fun row =>
        [TypedInteraction.pulledIfValue memoryChannel 1 (touch row).1.1,
         TypedInteraction.pushedIfValue memoryChannel 1 (touch row).2]) := by
    apply List.map_injective_iff.mpr TypedInteraction.raw_injective
    simp only [List.map_flatMap, typedTableInteractionsWith_raw, List.map_cons, List.map_nil,
      TypedInteraction.pulledIfValue_raw, TypedInteraction.pushedIfValue_raw, touch]
    exact HintReadWriteLedger.memory_ledger tables data aligned
  rw [ledger, producedMessages_flatMap, consumedMessages_flatMap]
  simp [producedMessages, consumedMessages, unit_signs.1, unit_signs.2]
  exact ⟨List.flatMap_pure_eq_map _ _, List.flatMap_pure_eq_map _ _⟩

private theorem write_word_bits :
    Word.toBitVec64 (HostCallChip.writeWord (R := ZMod p)) = SyscallKind.write.code := by
  have two : (2 : ZMod p).val = 2 := ZMod.val_natCast_of_lt
    (show 2 < p by have := Fact.out (p := 2 ^ 25 < p); omega)
  simp [HostCallChip.writeWord, Word.toBitVec64, Word.toNat, two, SyscallKind.code]

private theorem extra_disabled (input : HostCallChip.Inputs (ZMod p))
    (safe : Word.toBitVec64 (input.message (HostCallChip.writeFlag input.instruction.op_a_memory.prev_value)).code ≠
      SyscallKind.write.code) :
    (input.read (HostCallChip.writeFlag input.instruction.op_a_memory.prev_value)).is_real = 0 := by
  have different : input.instruction.op_a_memory.prev_value ≠ HostCallChip.writeWord := by
    intro same
    apply safe
    change Word.toBitVec64 input.instruction.op_a_memory.prev_value = _
    rw [same, write_word_bits]
  simp only [HostCallChip.Inputs.read, HostCallChip.writeFlag, if_neg different, mul_zero]

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {resources : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
  {names : ((HostLocalCore.tables image source
    ((HostHintReadHandoff.receiver :: HostCallReceivers.available).map (·.component) ++
      (HostHintReadHandoff.wordResources ++ resources))).map (·.circuit.name)).Nodup}

/-- The current physical receiver registry disables every x12 pair, including padding.
The general extended ledger still retains WRITE's pair when that handler is installed later. -/
theorem wrapper_disabled
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels names))
    (interface : ExtensionInterface HostCallReceivers.available resources)
    (constraints : witness.Constraints) (bytes : witness.BalancedChannel byteChannel.toRaw)
    (calls : witness.BalancedChannel HostCallChip.channel.toRaw)
    (specs : ∀ table ∈ queueTables witness, table.Spec witness.data) :
    ∀ env ∈ (HostLocalCore.hostCallTable witness).table.map (Environment.fromArray · witness.data),
      (HostCallProjection.extraRead env).is_real = 0 := by
  have safe := (HostQueueCallProjection.calls_projection witness interface constraints bytes specs).1
  have handoff := HostLocalHandoff.calls_perm_of_balancedChannel witness (resources_hostCall_silent interface) constraints calls
  intro env member
  have checked : HostCallLedger.producer.operations.ConstraintsHold env := by
    obtain ⟨physical, present, rfl⟩ := List.mem_map.mp member
    have checked := constraints _ (HostLocalCore.hostCallTable_mem witness) physical present
    rwa [HostLocalCore.hostCallTable_component] at checked
  rcases HostCallLedger.binary_of_constraints env checked with inactive | active
  · simp only [HostCallProjection.extraRead, HostCallChip.Inputs.read, inactive, zero_mul]
  · apply extra_disabled (HostCallLedger.input env)
    apply safe
    apply handoff.mem_iff.mp
    exact List.mem_map.mpr ⟨env,
      List.mem_filter.mpr ⟨member, by simpa only [decide_eq_true_eq] using active⟩, rfl⟩

private theorem wrapper_messages_nil
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels names))
    (disabled : ∀ env ∈ (HostLocalCore.hostCallTable witness).table.map (Environment.fromArray · witness.data),
      (HostCallProjection.extraRead env).is_real = 0) :
    producedMessages (HostLocalCore.wrapperMemory witness) = [] ∧
      consumedMessages (HostLocalCore.wrapperMemory witness) = [] := by
  have zero : signedVal (0 : ZMod p) = 0 := by simp [signedVal]
  rw [HostLocalCore.wrapperMemory, producedMessages_flatMap, consumedMessages_flatMap]
  constructor
  all_goals
    apply List.flatMap_eq_nil_iff.mpr
    intro env member
    simp [producedMessages, consumedMessages, disabled env member, zero]

private theorem auxiliary_memory_words
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels names))
    (silent : ∀ component ∈ (HostHintReadHandoff.receiver :: HostCallReceivers.available).map (·.component) ++ resources,
      memoryChannel.toRaw ∉ component.circuit.channels) :
    HostLocalCore.auxiliaryMemory witness = (wordTables witness).flatMap (typedTableInteractionsWith · witness.data memoryChannel) := by
  have receivers : (HostLocalHandoff.receiverTables witness).flatMap (typedTableInteractionsWith · witness.data memoryChannel) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro table member
    apply typedTableInteractions_nil
    apply silent
    apply List.mem_append_left
    rw [← HostLocalHandoff.receiverTables_components witness]
    exact List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
  have resourcesSilent : ((HostLocalHandoff.resourceTables witness).drop 2).flatMap
      (typedTableInteractionsWith · witness.data memoryChannel) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro table member
    apply typedTableInteractions_nil
    apply silent
    apply List.mem_append_right
    have component := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
    rw [List.map_drop, HostLocalHandoff.resourceTables_components] at component
    simpa only [HostHintReadHandoff.wordResources, List.cons_append, List.nil_append,
      List.drop_succ_cons, List.drop_zero] using component
  have split : HostLocalHandoff.receiverTables witness ++ HostLocalHandoff.resourceTables witness =
      HostLocalCore.auxiliaryTables witness := List.take_append_drop _ _
  rw [HostLocalCore.auxiliaryMemory, ← split, List.flatMap_append, receivers, List.nil_append]
  rw [← List.take_append_drop 2 (HostLocalHandoff.resourceTables witness), List.flatMap_append,
    resourcesSilent, List.append_nil]
  rfl

variable {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState}

omit [Fact (2 ^ 25 < p)] in
private theorem messages_perm (left right : List (TypedInteraction (memoryChannel (p := p))))
    (perm : left.Perm right) :
    (producedMessages left).Perm (producedMessages right) ∧
      (consumedMessages left).Perm (consumedMessages right) :=
  ⟨(perm.filter _).map _, (perm.filter _).map _⟩

/-- Every active host Memory contribution of the installed source assembly belongs to its
word tables. The zero x12 pairs remain in the raw ledger and disappear only by signed activity. -/
theorem source_memory_messages
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    (producedMessages (HostLocalCore.memoryInterior (HostHintQueueBoundary.projected witness))).Perm
      (producedMessages (LocalCore.memoryInterior (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))) ++
        producedMessages ((wordTables (HostHintQueueBoundary.projected witness)).flatMap (typedTableInteractionsWith · witness.data memoryChannel))) ∧
    (consumedMessages (HostLocalCore.memoryInterior (HostHintQueueBoundary.projected witness))).Perm
      (consumedMessages (LocalCore.memoryInterior (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))) ++
        consumedMessages ((wordTables (HostHintQueueBoundary.projected witness)).flatMap (typedTableInteractionsWith · witness.data memoryChannel))) := by
  have checked := HostHintQueueBoundary.projected_constraints witness constraints
  have records := HostHintQueueBoundary.record_channels witness balanced
  have calls := HostHintQueueBoundary.projected_hostCall_balancedChannel witness balanced
  have interface := source_interface (p := p) source.host.io.hints
  have specs := queue_specs _ interface _ (HostHintQueueBoundary.source_authentication witness constraints) checked records
  have empty := wrapper_messages_nil _ (wrapper_disabled _ interface checked records.byte calls specs)
  have words := auxiliary_memory_words (HostHintQueueBoundary.projected witness) (source_memory_silent source)
  have perm := HostLocalCore.memoryInterior_perm (HostHintQueueBoundary.projected witness) checked
  have messages := messages_perm _ _ perm
  simpa only [producedMessages_append, consumedMessages_append, empty.1, empty.2, List.append_nil,
    words, HostHintQueueBoundary.projected_data] using messages

/-- The actual CPU inventory with all installed hint-word Memory effects attached. -/
noncomputable def sourceExecutionRows
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))) : List (RowFacts p) :=
  (LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))).map
    (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
      (wordTables (HostHintQueueBoundary.projected witness)) witness.data))

/-- Every active physical Memory record is in its enlarged CPU row or an actual refresh pair.
No host access remains as an unaccounted side ledger. -/
theorem source_execution_memory_projection
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) (loc : MemLoc) :
    TimedGrounding.pushesAt (sourceExecutionRows witness) loc +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑((LocalCore.memoryRefreshes (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))).map Prod.snd) : Multiset _) =
      Multiset.filter (fun message => MemoryMsg.locOf message = loc)
        (↑(producedMessages (HostLocalCore.memoryInterior (HostHintQueueBoundary.projected witness))) : Multiset _) ∧
    TimedGrounding.pullsAt (sourceExecutionRows witness) loc +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑((LocalCore.memoryRefreshes (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))).map Prod.fst) : Multiset _) =
      Multiset.filter (fun message => MemoryMsg.locOf message = loc)
        (↑(consumedMessages (HostLocalCore.memoryInterior (HostHintQueueBoundary.projected witness))) : Multiset _) := by
  have checked := HostLocalCore.localWitness_constraints _ (HostHintQueueBoundary.projected_constraints witness constraints)
  have original := LocalCore.executionRows_memory_projection _ checked loc
  have sameFacts : ExecutionRow.facts (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).data =
      ExecutionRow.facts witness.data := funext fun row => row.facts_setData _ _
  rw [sameFacts] at original
  have enlarged := eventFacts_memory witness.data
    (TransitionView.readIndexedRows HintReadCoverage.variants (wordTables (HostHintQueueBoundary.projected witness)) witness.data)
    (LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))) loc
  have partition := source_words_partition witness constraints balanced _ (List.Perm.refl _)
  have groupedPushes := congrArg (Multiset.filter (fun message => MemoryMsg.locOf message = loc))
    (Multiset.coe_eq_coe.mpr (partition.map (fun row => (touch row).2)))
  have groupedPulls := congrArg (Multiset.filter (fun message => MemoryMsg.locOf message = loc))
    (Multiset.coe_eq_coe.mpr (partition.map (fun row => (touch row).1.1)))
  have words := word_memory_messages _ witness.data (wordTables_aligned (HostHintQueueBoundary.projected witness))
  have messages := source_memory_messages witness constraints balanced
  have fullPushes := congrArg (Multiset.filter (fun message => MemoryMsg.locOf message = loc))
    (Multiset.coe_eq_coe.mpr messages.1)
  have fullPulls := congrArg (Multiset.filter (fun message => MemoryMsg.locOf message = loc))
    (Multiset.coe_eq_coe.mpr messages.2)
  rw [filter_coe_append, words.1] at fullPushes
  rw [filter_coe_append, words.2] at fullPulls
  constructor
  · rw [sourceExecutionRows, enlarged.1, groupedPushes, add_right_comm, original.1]
    exact fullPushes.symm
  · rw [sourceExecutionRows, enlarged.2, groupedPulls, add_right_comm, original.2]
    exact fullPulls.symm

/-- The full source/final inventories balance the enlarged execution rows and real refreshes.
This is record conservation before the grounding walk establishes predecessor value currency. -/
theorem source_execution_memory_balance
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) (loc : MemLoc) :
    Multiset.filter (fun message => MemoryMsg.locOf message = loc)
        (↑((SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).records
          (LocalCore.sourceWitness (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)))) : Multiset _) +
      TimedGrounding.pushesAt (sourceExecutionRows witness) loc +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑((LocalCore.memoryRefreshes (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))).map Prod.snd) : Multiset _) =
    Multiset.filter (fun message => MemoryMsg.locOf message = loc)
        (↑(FinalMemoryEnsemble.records (LocalCore.finalWitness
          (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)))) : Multiset _) +
      TimedGrounding.pullsAt (sourceExecutionRows witness) loc +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑((LocalCore.memoryRefreshes (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))).map Prod.fst) : Multiset _) := by
  have physical := source_memory_records_perm witness constraints balanced
  have balance := congrArg (Multiset.filter (fun message => MemoryMsg.locOf message = loc))
    (Multiset.coe_eq_coe.mpr physical)
  rw [filter_coe_append, filter_coe_append] at balance
  have projection := source_execution_memory_projection witness constraints balanced loc
  rw [add_assoc, add_assoc, projection.1, projection.2]
  exact balance

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
private theorem append_aligned {aligned original : RowFacts p} (facts : AlignedFacts aligned original)
    (extra : List (Touch p))
    (localOK : ∀ access ∈ extra, TouchOK (StateMsg.timeNat original.statePull) access.1 access.2)
    (chain : ∀ loc, List.IsChain (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2)
      (extra.filter (fun access => MemoryMsg.locOf access.2 = loc)))
    (pushBound : ∀ access ∈ extra, MemoryMsg.ClkBound access.2)
    (slot : ∀ access ∈ extra, MemoryMsg.timeNat access.1.1 < MemoryMsg.timeNat access.2)
    (disjoint : ∀ message ∈ original.memPushes, ∀ access ∈ extra,
      MemoryMsg.locOf message ≠ MemoryMsg.locOf access.2) :
    AlignedFacts
      { aligned with
        memPulls := aligned.memPulls ++ extra.map Prod.fst
        memPushes := aligned.memPushes ++ extra.map Prod.snd }
      { original with
        memPulls := original.memPulls ++ extra.map Prod.fst
        memPushes := original.memPushes ++ extra.map Prod.snd } := by
  have zipped : (aligned.memPulls ++ extra.map Prod.fst).zip
      (aligned.memPushes ++ extra.map Prod.snd) = rowTouches aligned ++ extra := by
    rw [List.zip_append (List.forall₂_iff_zip.mp facts.touches).1]
    simp only [List.zip_map', Prod.mk.eta]
    exact congrArg (rowTouches aligned ++ ·) (List.map_id extra)
  refine ⟨facts.statePull, facts.statePush, facts.fetch, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨facts.memory.pushes.append_right _, by
      simpa only [List.map_append] using facts.memory.pulls.append_right (extra.map Prod.fst |>.map Prod.fst)⟩
  · apply List.rel_append facts.touches
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro access member
    rw [facts.statePull]
    exact localOK access member
  · intro loc
    change List.IsChain _ (((aligned.memPulls ++ extra.map Prod.fst).zip
      (aligned.memPushes ++ extra.map Prod.snd)).filter _)
    rw [zipped, List.filter_append]
    by_cases empty : rowTouchesAt aligned loc = []
    · change List.IsChain _ (rowTouchesAt aligned loc ++ _)
      rw [empty, List.nil_append]
      exact chain loc
    · obtain ⟨access, member⟩ := List.exists_mem_of_ne_nil _ empty
      have selected := mem_rowTouchesAt.mp member
      have absent : extra.filter (fun access => MemoryMsg.locOf access.2 = loc) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro other otherMem selectedOther
        have same := of_decide_eq_true selectedOther
        exact disjoint access.2
          (facts.memory.pushes.mem_iff.mp (List.of_mem_zip selected.1).2) other otherMem
          (selected.2.trans same.symm)
      rw [absent, List.append_nil]
      exact facts.chain loc
  · intro message member
    rcases List.mem_append.mp member with old | added
    · exact facts.pushBound message old
    · obtain ⟨access, present, rfl⟩ := List.mem_map.mp added
      exact pushBound access present
  · change ∀ access ∈ (aligned.memPulls ++ extra.map Prod.fst).zip
      (aligned.memPushes ++ extra.map Prod.snd), _
    rw [zipped]
    intro access member low high
    rcases List.mem_append.mp member with old | added
    · exact facts.slot access old low high
    · exact slot access added

private theorem syscall_register_pushes (row : SyscallInstrsChip.Inputs (ZMod p))
    (operands : row.op_a = 5 ∧ row.op_b = 10 ∧ row.op_c = 11)
    (message : MemoryMsg (ZMod p)) (member : message ∈ (syscallRowFacts row).memPushes) :
    ∃ index, MemoryMsg.locOf message = MemLoc.reg index := by
  have a := (syscallRow_locOf_reg row (i := 5#5) (by norm_num; exact operands.1.symm)
    row.op_a_memory row.op_a_value 4).2
  have b := (syscallRow_locOf_reg row (i := 10#5) (by norm_num; exact operands.2.1.symm)
    row.op_b_memory row.op_b_memory.prev_value 3).2
  have c := (syscallRow_locOf_reg row (i := 11#5) (by norm_num; exact operands.2.2.symm)
    row.op_c_memory row.op_c_memory.prev_value 2).2
  simp only [syscallRowFacts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  exacts [⟨_, a⟩, ⟨_, b⟩, ⟨_, c⟩]

omit [Fact (2 ^ 25 < p)] in
private theorem ram_not_register (input : HostRamAccessChip.Inputs (ZMod p))
    (facts : HostRamTouches.AccessFacts input) (index : BitVec 5) :
    MemoryMsg.locOf input.pushed ≠ MemLoc.reg index := by
  intro same
  have bound := facts.ram.1
  rw [facts.canonical.2.2, same] at bound
  change 2 ^ 16 ≤ index.toNat at bound
  have := index.isLt
  omega

private theorem time_of_clock (data : ProverData (ZMod p)) (left right : ExecutionRow p)
    (same : cpuClock data left = cpuClock data right) :
    StateMsg.timeNat (left.edge data).1 = StateMsg.timeNat (right.edge data).1 := by
  have values := congrArg (fun key : ZMod p × ZMod p => clkNat key.1 key.2) same
  simpa only [cpuClock, StateMsg.timeNat] using values

private theorem source_word_owner
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (event : ExecutionRow p)
    (eventMem : event ∈ LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)))
    (row : HintReadCoverage.Row (p := p))
    (member : row ∈ wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
      (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event) :
    ∃ env ∈ HostCallLedger.activeRows (HostLocalCore.hostCallTable (HostHintQueueBoundary.projected witness)) witness.data,
      event = .syscall (HostCallLedger.input env).instruction := by
  have checked := HostHintQueueBoundary.projected_constraints witness constraints
  have calls := HostHintQueueBoundary.projected_hostCall_balancedChannel witness balanced
  have cursor := HostHintQueueBoundary.projected_cursor_balancedChannel witness balanced
  have interface := source_interface (p := p) source.host.io.hints
  have ordering := HostHintQueueBoundary.projected_orderingChannels witness interface constraints balanced
  obtain ⟨physical, selected⟩ := List.mem_filter.mp member
  have owner := word_cpu (HostHintQueueBoundary.projected witness) interface checked calls cursor
  simp only [HostHintQueueBoundary.projected_data] at owner
  obtain ⟨_, _, env, active, _, cpuMem, clock⟩ := owner
    (source_word_steps witness constraints balanced) row physical
  have unique := LocalCore.executionRows_times_nodup_of_orderingChannels
    (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))
    (HostLocalCore.localWitness_constraints _ checked)
    ordering
  simp_rw [ExecutionRow.edge_setData _ (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).data witness.data] at unique
  refine ⟨env, active, List.inj_on_of_nodup_map unique eventMem cpuMem ?_⟩
  have same := (of_decide_eq_true selected).symm.trans clock.symm
  exact time_of_clock witness.data _ _ same

private theorem source_word_disjoint (valid : image.Valid)
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (event : ExecutionRow p)
    (eventMem : event ∈ LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)))
    (message : MemoryMsg (ZMod p)) (messageMem : message ∈ (event.facts witness.data).memPushes)
    (row : HintReadCoverage.Row (p := p))
    (member : row ∈ wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
      (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event) :
    MemoryMsg.locOf message ≠ MemoryMsg.locOf (touch row).2 := by
  obtain ⟨env, active, same⟩ := source_word_owner witness constraints balanced event eventMem row member
  have committed := HostLocalCore.hostCall_program_committed valid (HostHintQueueBoundary.projected witness)
    (source_program_silent source) (HostHintQueueBoundary.projected_constraints witness constraints)
    (HostHintQueueBoundary.projected_core_balancedChannel witness balanced programChannel.toRaw
      (by simp [LocalCore.baseEnsemble, sp1Ensemble_channels]))
  simp only [HostHintQueueBoundary.projected_data] at committed
  have operands := syscall_operands_of_committed _ _ (committed env active)
  rw [same] at messageMem
  obtain ⟨index, location⟩ := syscall_register_pushes _ operands message messageMem
  have retained : row ∈ TransitionView.readIndexedRows HintReadCoverage.variants
      (wordTables (HostHintQueueBoundary.projected witness)) (HostHintQueueBoundary.projected witness).data := by
    simpa only [HostHintQueueBoundary.projected_data] using (List.mem_filter.mp member).1
  have facts := source_word_touches witness constraints balanced row retained
  rw [location]
  exact (ram_not_register _ facts index).symm

/-- Every actual CPU event admits aligned register and hint-RAM touches from the complete AIR.
The enlarged row retains its original State edge, fetch, and all physical Memory occurrences. -/
theorem source_event_aligned (valid : image.Valid)
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (event : ExecutionRow p)
    (eventMem : event ∈ LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))) :
    ∃ aligned, AlignedFacts aligned (eventFacts witness.data
      (TransitionView.readIndexedRows HintReadCoverage.variants
        (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event) := by
  have checked := HostHintQueueBoundary.projected_constraints witness constraints
  have records := HostHintQueueBoundary.record_channels witness balanced
  have interface := source_interface (p := p) source.host.io.hints
  have bytes := HostLocalCore.localWitness_byte (HostHintQueueBoundary.projected witness)
    (auxiliaryInterface interface) checked records.byte
  have program : (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).BalancedChannel
      programChannel.toRaw := by
    change BalancedInteractions ((HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).interactionsWith _)
    rw [HostLocalCore.localWitness_program _ (source_program_silent source)]
    exact HostHintQueueBoundary.projected_core_balancedChannel witness balanced programChannel.toRaw
      (by simp [LocalCore.baseEnsemble, sp1Ensemble_channels])
  obtain ⟨aligned, facts⟩ := LocalCore.executionRows_aligned_of_channels valid
    (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))
    (HostLocalCore.localWitness_constraints _ checked) bytes program eventMem
  rw [event.facts_setData (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).data witness.data] at facts
  have hostFacts := source_touches_at valid witness constraints balanced event
  rw [ExecutionRow.edge_eq_facts] at hostFacts
  have combined := append_aligned facts
    ((wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
      (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event).map touch)
    (by
      intro access member
      obtain ⟨row, present, rfl⟩ := List.mem_map.mp member
      exact (hostFacts row present).1)
    (source_touches_chain witness constraints balanced event)
    (by
      intro access member
      obtain ⟨row, present, rfl⟩ := List.mem_map.mp member
      exact (hostFacts row present).2.1)
    (by
      intro access member
      obtain ⟨row, present, rfl⟩ := List.mem_map.mp member
      exact (hostFacts row present).2.2)
    (by
      intro message messageMem access member
      obtain ⟨row, present, rfl⟩ := List.mem_map.mp member
      exact source_word_disjoint valid witness constraints balanced event eventMem message messageMem row present)
  exact ⟨_, by simpa only [eventFacts, List.map_map, Function.comp_def] using combined⟩

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
private theorem align_facts (originals : List (RowFacts p))
    (available : ∀ original ∈ originals, ∃ aligned, AlignedFacts aligned original) :
    ∃ rows, List.Forall₂ AlignedFacts rows originals := by
  induction originals with
  | nil => exact ⟨[], .nil⟩
  | cons head tail ih =>
    obtain ⟨aligned, headOK⟩ := available head List.mem_cons_self
    obtain ⟨rows, tailOK⟩ := ih (fun row member => available row (List.mem_cons_of_mem _ member))
    exact ⟨aligned :: rows, .cons headOK tailOK⟩

/-- An exhaustive ordered CPU walk with aligned host footprints and the complete Memory
aggregates. This directly transports source/final record balance to the aligned rows. -/
theorem source_ordered_aligned_rows (valid : image.Valid)
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∃ (ordered : List (ExecutionRow p)) (rows : List (RowFacts p)),
      ordered.Perm (LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))) ∧
      Walk.IsWalk (ExecutionRow.canonEdge witness.data)
        (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) ordered ∧
      List.Forall₂ AlignedFacts rows (ordered.map (eventFacts witness.data
        (TransitionView.readIndexedRows HintReadCoverage.variants
          (wordTables (HostHintQueueBoundary.projected witness)) witness.data))) ∧
      ∀ loc, pushesAt rows loc = pushesAt (sourceExecutionRows witness) loc ∧
        pullsAt rows loc = pullsAt (sourceExecutionRows witness) loc := by
  obtain ⟨ordered, exhaustive, walk⟩ := HostLocalCore.executionRows_ordered_of_orderingChannels
    (HostHintQueueBoundary.projected witness)
    (HostHintQueueBoundary.projected_constraints witness constraints)
    (HostHintQueueBoundary.projected_orderingChannels witness (source_interface source.host.io.hints) constraints balanced)
  simp only [HostHintQueueBoundary.projected_data, HostHintQueueBoundary.projected_publicInput] at walk
  obtain ⟨rows, aligned⟩ := align_facts (ordered.map (eventFacts witness.data
    (TransitionView.readIndexedRows HintReadCoverage.variants (wordTables (HostHintQueueBoundary.projected witness)) witness.data))) (by
      intro original member
      obtain ⟨event, present, rfl⟩ := List.mem_map.mp member
      exact source_event_aligned valid witness constraints balanced event (exhaustive.mem_iff.mp present))
  refine ⟨ordered, rows, exhaustive, walk, aligned, ?_⟩
  intro loc
  have ledger := rowAggregates_of_permutation (aligned.imp (fun _ _ facts => facts.memory)) loc
  rw [pushesAt_perm (exhaustive.map _) loc, pullsAt_perm (exhaustive.map _) loc] at ledger
  exact ledger

end SP1Clean.Soundness.HostHintReadCPU
