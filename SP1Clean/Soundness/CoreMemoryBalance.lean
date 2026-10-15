import SP1Clean.Soundness.NativeCoreFinalBoundary
import SP1Clean.Soundness.MemoryFrontier

/-! # Shared Memory balance rules for the native core

Component-local multiplicity proofs cover the common instruction/provider suffix used by both
boot and local assemblies. Unit boundary emissions reduce count-bounded Clean balance to an exact
record permutation and per-location optional-frontier equation. No execution or value-currency
premise enters these algebraic rules.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- Every physical Memory interaction is disabled or has unit signed multiplicity. -/
def MemoryBinary (component : Component (ZMod p)) : Prop :=
  ∀ data physical, component.operations.ConstraintsHold (Environment.fromArray physical data) →
    ∀ interaction ∈ component.operations.interactionValuesWith memoryChannel.toRaw
      (Environment.fromArray physical data),
      signedVal interaction.mult = -1 ∨ signedVal interaction.mult = 0 ∨ signedVal interaction.mult = 1

omit [Fact (2 ^ 24 < p)] in
/-- Components with no Memory interactions satisfy the multiplicity condition without constraints. -/
theorem memoryBinary_of_silent (component : Component (ZMod p))
    (silent : memoryChannel.toRaw ∉ component.circuit.channels) : MemoryBinary component := by
  intro data physical _ interaction member
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq] at member
  change interaction ∈ (((component.circuit.main (varFromOffset component.Input 0)).operations
    (size component.Input)).interactionsWith memoryChannel.toRaw).map _ at member
  rw [InteractionRecovery.interactionsWith_main_eq_nil component.circuit.base _ _ _ silent] at member
  contradiction

private theorem instruction_memoryBinary (component : Component (ZMod p))
    (member : component ∈ sp1Tables (p := p)) : MemoryBinary component := by
  obtain ⟨chip, chipMem, rfl⟩ := List.mem_map.mp member
  intro data physical constraints interaction emitted
  obtain ⟨source, sourceMem, rfl⟩ := List.mem_map.mp emitted
  exact signedVal_binary_of_selector_gated _ _
    (supportedChip_selectorConstraintShape chip chipMem data physical constraints)
    (supportedChip_memorySelectorConstraintShape chip chipMem data physical constraints source sourceMem)

private theorem memoryBinary_of_gated {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (gate : Var Input (ZMod p) → Expression (ZMod p))
    (gated : ∀ input offset (env : Environment (ZMod p)),
      ∀ interaction ∈ ((circuit.main input).operations offset).interactionsWith memoryChannel.toRaw,
        env interaction.mult = -(env (gate input)) ∨ env interaction.mult = 0 ∨
          env interaction.mult = env (gate input))
    (binary : ∀ input offset env,
      ConstraintsHold.Shallow env ((circuit.main input).operations offset) →
        env (gate input) = 0 ∨ env (gate input) = 1) : MemoryBinary { circuit } := by
  intro data physical constraints interaction member
  have bound := binary (varFromOffset Input 0) (size Input) (Environment.fromArray physical data)
    (shallowConstraints_of_componentConstraints circuit _ constraints)
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq] at member
  obtain ⟨source, sourceMem, rfl⟩ := List.mem_map.mp member
  exact signedVal_binary_of_selector_gated _ _ bound
    (gated (varFromOffset Input 0) (size Input) _ source sourceMem)

private theorem halt_memoryBinary : MemoryBinary ({ circuit := HaltChip.circuit } : Component (ZMod p)) := by
  apply memoryBinary_of_gated HaltChip.circuit (fun input => input.is_real) ?_
    HaltChip.selectorBinary_of_shallow
  intro input offset env
  change ∀ interaction ∈ ((HaltChip.main input).operations offset).interactionsWith memoryChannel.toRaw,
    env interaction.mult = -(env input.is_real) ∨ env interaction.mult = 0 ∨
      env interaction.mult = env input.is_real
  rw [HaltChip.interactionsWith_memory_eq]
  simp [HaltChip.exposedMemoryInteractions, Channel.pulledIf, Channel.pushedIf,
    ChannelInteraction.toRaw, pulledIf_mult, pushedIf_mult, Expression.eval]

private theorem syscall_memoryBinary : MemoryBinary ({ circuit := SyscallInstrsChip.circuit } : Component (ZMod p)) := by
  apply memoryBinary_of_gated SyscallInstrsChip.circuit (fun input => input.is_real) ?_
    SyscallInstrsChip.selectorBinary_of_shallow
  intro input offset env
  change ∀ interaction ∈ ((SyscallInstrsChip.main input).operations offset).interactionsWith memoryChannel.toRaw,
    env interaction.mult = -(env input.is_real) ∨ env interaction.mult = 0 ∨
      env interaction.mult = env input.is_real
  rw [Faithful.syscallInstrsInteractionsWith_memory]
  simp [ChannelInteraction.toRaw, Expression.eval]

private theorem memoryBump_memoryBinary : MemoryBinary ({ circuit := MemoryBumpChip.circuit } : Component (ZMod p)) := by
  apply memoryBinary_of_gated MemoryBumpChip.circuit (fun input => input.is_real) ?_
    MemoryBumpChip.selectorBinary_of_shallow
  intro input offset env
  change ∀ interaction ∈ ((MemoryBumpChip.main input).operations offset).interactionsWith memoryChannel.toRaw,
    env interaction.mult = -(env input.is_real) ∨ env interaction.mult = 0 ∨
      env interaction.mult = env input.is_real
  rw [memoryBumpMain_memoryInteractions]
  simp [Channel.pulledIf, Channel.pushedIf, ChannelInteraction.toRaw, pulledIf_mult,
    pushedIf_mult, Expression.eval]

private theorem remainingProvider_memoryBinary (component : Component (ZMod p))
    (member : component ∈ (sp1ProviderTables (p := p)).take 23 ++ sp1ProviderTables.drop 26) :
    MemoryBinary component := by
  rw [sp1ProviderTables, ← List.map_take, ← List.map_drop, ← List.map_append] at member
  obtain ⟨id, idMem, rfl⟩ := List.mem_map.mp member
  have noProgram : .program ∉ ProviderTableId.all.take 23 ++ ProviderTableId.all.drop 26 := by decide
  have noInit : .memoryInit ∉ ProviderTableId.all.take 23 ++ ProviderTableId.all.drop 26 := by decide
  have noFinal : .memoryFinalize ∉ ProviderTableId.all.take 23 ++ ProviderTableId.all.drop 26 := by decide
  cases id with
  | program => exact (noProgram idMem).elim
  | memoryInit => exact (noInit idMem).elim
  | memoryFinalize => exact (noFinal idMem).elim
  | halt => exact halt_memoryBinary
  | syscallInstrs => exact syscall_memoryBinary
  | memoryBump => exact memoryBump_memoryBinary
  | byte provider =>
      apply memoryBinary_of_silent
      cases provider <;> change memoryChannel.toRaw ∉ [byteChannel.toRaw]
      all_goals simp [memoryChannel_eq_byteChannel_false]
  | range width =>
      apply memoryBinary_of_silent
      change memoryChannel.toRaw ∉ [byteChannel.toRaw]
      simp [memoryChannel_eq_byteChannel_false]
  | stateBump =>
      apply memoryBinary_of_silent
      change memoryChannel.toRaw ∉ [byteChannel.toRaw, stateChannel.toRaw]
      simp [memoryChannel_eq_byteChannel_false, memoryChannel_eq_stateChannel_false]

/-- Unit Memory multiplicities for every component after the two boundary inventories. -/
theorem interior_memoryBinary (image : ProgramImage) (component : Component (ZMod p))
    (member : component ∈ afterFinalTables image) : MemoryBinary component := by
  simp only [afterFinalTables, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | member) | member
  · apply memoryBinary_of_silent
    change memoryChannel.toRaw ∉ [programChannel.toRaw]
    simp [memoryChannel_eq_programChannel_false]
  · exact instruction_memoryBinary component member
  · exact remainingProvider_memoryBinary component (List.mem_append.mpr member)

private theorem memory_unitSigns :
    signedVal (1 : ZMod p) = 1 ∧ signedVal (-1 : ZMod p) = -1 := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 24 < p); omega
  constructor
  · rw [signedVal_is_real hp (Or.inr rfl), ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
    norm_num
  · rw [signedVal_neg_is_real hp (Or.inr rfl), ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
    norm_num

private theorem initial_activeMessages (records : List (MemoryMsg (ZMod p))) :
    producedMessages (records.map (TypedInteraction.pushedIfValue memoryChannel 1)) = records ∧
    consumedMessages (records.map (TypedInteraction.pushedIfValue memoryChannel 1)) = [] := by
  simp [producedMessages, consumedMessages, List.filter_map, Function.comp_def, memory_unitSigns.1]

private theorem final_activeMessages (records : List (MemoryMsg (ZMod p))) :
    producedMessages (records.map (TypedInteraction.pushedIfValue memoryChannel (-1))) = [] ∧
    consumedMessages (records.map (TypedInteraction.pushedIfValue memoryChannel (-1))) = records := by
  simp [producedMessages, consumedMessages, List.filter_map, Function.comp_def, memory_unitSigns.2]

/-- Unit boundary records preserve signed binarity of the complete interior ledger. -/
theorem memoryBoundary_signedBinary (initial final : List (MemoryMsg (ZMod p)))
    (interior : List (TypedInteraction (memoryChannel (p := p))))
    (binary : ∀ interaction ∈ interior,
      signedVal interaction.mult = -1 ∨ signedVal interaction.mult = 0 ∨ signedVal interaction.mult = 1) :
    ∀ interaction ∈ initial.map (TypedInteraction.pushedIfValue memoryChannel 1) ++
      final.map (TypedInteraction.pushedIfValue memoryChannel (-1)) ++ interior,
      signedVal interaction.mult = -1 ∨ signedVal interaction.mult = 0 ∨ signedVal interaction.mult = 1 := by
  intro interaction member
  rcases List.mem_append.mp member with boundary | inside
  · rcases List.mem_append.mp boundary with initial | final
    · obtain ⟨message, _, rfl⟩ := List.mem_map.mp initial
      exact Or.inr (Or.inr memory_unitSigns.1)
    · obtain ⟨message, _, rfl⟩ := List.mem_map.mp final
      exact Or.inl memory_unitSigns.2
  · exact binary interaction inside

/-- Complete-message balance becomes source-plus-pushes permuted with final-plus-pulls. -/
theorem memoryBoundary_records_perm (initial final : List (MemoryMsg (ZMod p)))
    (interior : List (TypedInteraction (memoryChannel (p := p))))
    (binary : ∀ interaction ∈ interior,
      signedVal interaction.mult = -1 ∨ signedVal interaction.mult = 0 ∨ signedVal interaction.mult = 1)
    (balanced : BalancedInteractions ((initial.map (TypedInteraction.pushedIfValue memoryChannel 1) ++
      final.map (TypedInteraction.pushedIfValue memoryChannel (-1)) ++ interior).map TypedInteraction.raw)) :
    (initial ++ producedMessages interior).Perm (final ++ consumedMessages interior) := by
  classical
  have paired := producedMessages_perm_consumedMessages _ balanced
    (memoryBoundary_signedBinary initial final interior binary)
  simpa only [producedMessages_append, consumedMessages_append,
    (initial_activeMessages _).1, (initial_activeMessages _).2,
    (final_activeMessages _).1, (final_activeMessages _).2, List.append_nil, List.nil_append] using paired

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private theorem optMS_records_frontier (records : List (MemoryMsg (ZMod p)))
    (unique : (records.map MemoryMsg.locOf).Nodup) (loc : MemLoc) :
    optMS (records.filter (fun message => decide (MemoryMsg.locOf message = loc))).head? =
      Multiset.filter (fun message => MemoryMsg.locOf message = loc) (↑records : Multiset _) := by
  rw [optMS_head?_eq_coe _ (pairwise_distinct_filter_length_le_one MemoryMsg.locOf _ loc
    (List.pairwise_map.mp unique)), Multiset.filter_coe]

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- Distinct boundary locations turn the record permutation into the timed engine's equation. -/
theorem memoryBoundary_frontier_balance (initial final produced consumed : List (MemoryMsg (ZMod p)))
    (initialUnique : (initial.map MemoryMsg.locOf).Nodup)
    (finalUnique : (final.map MemoryMsg.locOf).Nodup)
    (balanced : (initial ++ produced).Perm (final ++ consumed)) (loc : MemLoc) :
    optMS (initial.filter (fun message => decide (MemoryMsg.locOf message = loc))).head? +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc) (↑produced : Multiset _) =
      optMS (final.filter (fun message => decide (MemoryMsg.locOf message = loc))).head? +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc) (↑consumed : Multiset _) := by
  rw [optMS_records_frontier _ initialUnique, optMS_records_frontier _ finalUnique]
  have filtered := congrArg (Multiset.filter (fun message => MemoryMsg.locOf message = loc))
    (Multiset.coe_eq_coe.mpr balanced)
  simpa only [filter_coe_append] using filtered

end SP1Clean.Soundness.NativeCore
