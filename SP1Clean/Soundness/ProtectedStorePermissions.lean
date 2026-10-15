import SP1Clean.Soundness.WritePermissionBalance
import SP1Clean.Proofs.Chips.ProtectedStore
import SP1Clean.Soundness.TypedSelectors

/-! # Permission requests of the four store components

The emitted requests use the original chip's computed address and real-row selector. Original
instruction circuits are silent on the new channel. Their selector constraints therefore make
all added contributions either zero or unit pulls; padding cannot manufacture a provider.
-/

namespace SP1Clean.Soundness.WritePermission

open Circuit Air.Flat SP1Clean.Model.Core SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

theorem byte_emission (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    ((ProtectedStore.byte (p := p)).main input |>.operations offset).interactionsWith
      WritePermissionProvider.channel.toRaw =
      [(WritePermissionProvider.channel.pulledIf input.is_real
        ((StoreByteChip.circuit input).output offset).address_operation.addr_operation.value).toRaw] := by
  have silent : WritePermissionProvider.channel.toRaw ∉ (StoreByteChip.circuit (p := p)).channels :=
    by
      rw [GeneralFormalCircuit.channels,
        show (StoreByteChip.circuit (p := p)).channelsWithGuarantees =
          (StoreByteChip.elaborated (p := p)).channelsWithGuarantees from rfl,
        show (StoreByteChip.circuit (p := p)).channelsWithRequirements =
          [stateChannel.toRaw, memoryChannel.toRaw] from rfl]
      simp only [circuit_norm]
      simp [WritePermissionProvider.channel, stateChannel, memoryChannel, byteChannel,
        programChannel]
  have quiet (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :=
    InteractionRecovery.interactionsWith_main_eq_nil StoreByteChip.circuit.base
      WritePermissionProvider.channel.toRaw input offset silent
  simp only [Operations.interactionsWith, StoreByteChip.circuit, Circuit.operations] at quiet
  simp only [ProtectedStore.byte, circuit_norm, GeneralFormalCircuit.toSubcircuit_interactions,
    quiet, List.nil_append]

theorem half_emission (input : Var StoreHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    ((ProtectedStore.half (p := p)).main input |>.operations offset).interactionsWith
      WritePermissionProvider.channel.toRaw =
      List.ofFn (fun index : Fin 2 => (WritePermissionProvider.channel.pulledIf input.is_real
        (Address.offset ((StoreHalfChip.circuit input).output offset).address_operation.addr_operation.value
          (.const (index.val : ZMod p)))).toRaw) := by
  have silent : WritePermissionProvider.channel.toRaw ∉ (StoreHalfChip.circuit (p := p)).channels :=
    by
      rw [GeneralFormalCircuit.channels,
        show (StoreHalfChip.circuit (p := p)).channelsWithGuarantees =
          (StoreHalfChip.elaborated (p := p)).channelsWithGuarantees from rfl,
        show (StoreHalfChip.circuit (p := p)).channelsWithRequirements =
          [stateChannel.toRaw, memoryChannel.toRaw] from rfl]
      simp only [circuit_norm]
      simp [WritePermissionProvider.channel, stateChannel, memoryChannel, byteChannel,
        programChannel]
  have quiet (input : Var StoreHalfChip.Inputs (ZMod p)) (offset : ℕ) :=
    InteractionRecovery.interactionsWith_main_eq_nil StoreHalfChip.circuit.base
      WritePermissionProvider.channel.toRaw input offset silent
  simp only [Operations.interactionsWith, StoreHalfChip.circuit, Circuit.operations] at quiet
  simp only [ProtectedStore.half, circuit_norm, GeneralFormalCircuit.toSubcircuit_interactions,
    quiet, List.nil_append, Circuit.forEach.operations_eq, List.ofFn_succ, List.ofFn_zero,
    List.flatten_cons, List.flatten_nil, List.append_nil, Vector.getElem_range]

theorem word_emission (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) :
    ((ProtectedStore.word (p := p)).main input |>.operations offset).interactionsWith
      WritePermissionProvider.channel.toRaw =
      List.ofFn (fun index : Fin 4 => (WritePermissionProvider.channel.pulledIf input.is_real
        (Address.offset ((StoreWordChip.circuit input).output offset).address_operation.addr_operation.value
          (.const (index.val : ZMod p)))).toRaw) := by
  have silent : WritePermissionProvider.channel.toRaw ∉ (StoreWordChip.circuit (p := p)).channels :=
    by
      rw [GeneralFormalCircuit.channels,
        show (StoreWordChip.circuit (p := p)).channelsWithGuarantees =
          (StoreWordChip.elaborated (p := p)).channelsWithGuarantees from rfl,
        show (StoreWordChip.circuit (p := p)).channelsWithRequirements =
          [stateChannel.toRaw, memoryChannel.toRaw] from rfl]
      simp only [circuit_norm]
      simp [WritePermissionProvider.channel, stateChannel, memoryChannel, byteChannel,
        programChannel]
  have quiet (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) :=
    InteractionRecovery.interactionsWith_main_eq_nil StoreWordChip.circuit.base
      WritePermissionProvider.channel.toRaw input offset silent
  simp only [Operations.interactionsWith, StoreWordChip.circuit, Circuit.operations] at quiet
  simp only [ProtectedStore.word, circuit_norm, GeneralFormalCircuit.toSubcircuit_interactions,
    quiet, List.nil_append, Circuit.forEach.operations_eq, List.ofFn_succ, List.ofFn_zero,
    List.flatten_cons, List.flatten_nil, List.append_nil, Vector.getElem_range]

theorem double_emission (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) :
    ((ProtectedStore.double (p := p)).main input |>.operations offset).interactionsWith
      WritePermissionProvider.channel.toRaw =
      List.ofFn (fun index : Fin 8 => (WritePermissionProvider.channel.pulledIf input.is_real
        (Address.offset ((StoreDoubleChip.circuit input).output offset).address_operation.addr_operation.value
          (.const (index.val : ZMod p)))).toRaw) := by
  have silent : WritePermissionProvider.channel.toRaw ∉ (StoreDoubleChip.circuit (p := p)).channels :=
    by
      rw [GeneralFormalCircuit.channels,
        show (StoreDoubleChip.circuit (p := p)).channelsWithGuarantees =
          (StoreDoubleChip.elaborated (p := p)).channelsWithGuarantees from rfl,
        show (StoreDoubleChip.circuit (p := p)).channelsWithRequirements =
          [stateChannel.toRaw, memoryChannel.toRaw] from rfl]
      simp only [circuit_norm]
      simp [WritePermissionProvider.channel, stateChannel, memoryChannel, byteChannel,
        programChannel]
  have quiet (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) :=
    InteractionRecovery.interactionsWith_main_eq_nil StoreDoubleChip.circuit.base
      WritePermissionProvider.channel.toRaw input offset silent
  simp only [Operations.interactionsWith, StoreDoubleChip.circuit, Circuit.operations] at quiet
  simp only [ProtectedStore.double, circuit_norm, GeneralFormalCircuit.toSubcircuit_interactions,
    quiet, List.nil_append, Circuit.forEach.operations_eq, List.ofFn_succ, List.ofFn_zero,
    List.flatten_cons, List.flatten_nil, List.append_nil, Vector.getElem_range]

theorem byte_pulls : Pulls ({ circuit := ProtectedStore.byte (p := p) } : Component (ZMod p)) := by
  intro data physical constraints interaction member
  have checked : ({ circuit := StoreByteChip.circuit } : Component (ZMod p)).operations.ConstraintsHold
      (Environment.fromArray physical data) := by
    simpa only [Operations.ConstraintsHold, ProtectedStore.byte_constraints,
      ProtectedStore.byte_lookups] using constraints
  have binary := StoreByteChip.mainSelectorBinary.binary (varFromOffset StoreByteChip.Inputs 0)
    (size StoreByteChip.Inputs) (Environment.fromArray physical data)
    (shallowConstraints_of_componentConstraints StoreByteChip.circuit _ checked)
  simp only [circuit_norm] at binary
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq] at member
  change interaction ∈ (((ProtectedStore.byte.main (varFromOffset StoreByteChip.Inputs 0)).operations
    (size StoreByteChip.Inputs)).interactionsWith WritePermissionProvider.channel.toRaw).map _ at member
  rw [byte_emission] at member
  obtain rfl := List.mem_singleton.mp member
  simp only [Channel.eval_pulledIf, Channel.pulledIfValue, neg_eq_zero, neg_inj]
  simpa only [circuit_norm] using binary

theorem half_pulls : Pulls ({ circuit := ProtectedStore.half (p := p) } : Component (ZMod p)) := by
  intro data physical constraints interaction member
  have checked : ({ circuit := StoreHalfChip.circuit } : Component (ZMod p)).operations.ConstraintsHold
      (Environment.fromArray physical data) := by
    simpa only [Operations.ConstraintsHold, ProtectedStore.half_constraints,
      ProtectedStore.half_lookups] using constraints
  have binary := StoreHalfChip.mainSelectorBinary.binary (varFromOffset StoreHalfChip.Inputs 0)
    (size StoreHalfChip.Inputs) (Environment.fromArray physical data)
    (shallowConstraints_of_componentConstraints StoreHalfChip.circuit _ checked)
  simp only [circuit_norm] at binary
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq] at member
  change interaction ∈ (((ProtectedStore.half.main (varFromOffset StoreHalfChip.Inputs 0)).operations
    (size StoreHalfChip.Inputs)).interactionsWith WritePermissionProvider.channel.toRaw).map _ at member
  rw [half_emission] at member
  obtain ⟨emitted, emissionMem, rfl⟩ := List.mem_map.mp member
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp emissionMem
  simp only [Channel.eval_pulledIf, Channel.pulledIfValue, neg_eq_zero, neg_inj]
  simpa only [circuit_norm] using binary

theorem word_pulls : Pulls ({ circuit := ProtectedStore.word (p := p) } : Component (ZMod p)) := by
  intro data physical constraints interaction member
  have checked : ({ circuit := StoreWordChip.circuit } : Component (ZMod p)).operations.ConstraintsHold
      (Environment.fromArray physical data) := by
    simpa only [Operations.ConstraintsHold, ProtectedStore.word_constraints,
      ProtectedStore.word_lookups] using constraints
  have binary := StoreWordChip.mainSelectorBinary.binary (varFromOffset StoreWordChip.Inputs 0)
    (size StoreWordChip.Inputs) (Environment.fromArray physical data)
    (shallowConstraints_of_componentConstraints StoreWordChip.circuit _ checked)
  simp only [circuit_norm] at binary
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq] at member
  change interaction ∈ (((ProtectedStore.word.main (varFromOffset StoreWordChip.Inputs 0)).operations
    (size StoreWordChip.Inputs)).interactionsWith WritePermissionProvider.channel.toRaw).map _ at member
  rw [word_emission] at member
  obtain ⟨emitted, emissionMem, rfl⟩ := List.mem_map.mp member
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp emissionMem
  simp only [Channel.eval_pulledIf, Channel.pulledIfValue, neg_eq_zero, neg_inj]
  simpa only [circuit_norm] using binary

theorem double_pulls : Pulls ({ circuit := ProtectedStore.double (p := p) } : Component (ZMod p)) := by
  intro data physical constraints interaction member
  have checked : ({ circuit := StoreDoubleChip.circuit } : Component (ZMod p)).operations.ConstraintsHold
      (Environment.fromArray physical data) := by
    simpa only [Operations.ConstraintsHold, ProtectedStore.double_constraints,
      ProtectedStore.double_lookups] using constraints
  have binary := StoreDoubleChip.mainSelectorBinary.binary (varFromOffset StoreDoubleChip.Inputs 0)
    (size StoreDoubleChip.Inputs) (Environment.fromArray physical data)
    (shallowConstraints_of_componentConstraints StoreDoubleChip.circuit _ checked)
  simp only [circuit_norm] at binary
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq] at member
  change interaction ∈ (((ProtectedStore.double.main (varFromOffset StoreDoubleChip.Inputs 0)).operations
    (size StoreDoubleChip.Inputs)).interactionsWith WritePermissionProvider.channel.toRaw).map _ at member
  rw [double_emission] at member
  obtain ⟨emitted, emissionMem, rfl⟩ := List.mem_map.mp member
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp emissionMem
  simp only [Channel.eval_pulledIf, Channel.pulledIfValue, neg_eq_zero, neg_inj]
  simpa only [circuit_norm] using binary

end SP1Clean.Soundness.WritePermission
