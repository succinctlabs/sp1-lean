import SP1Clean.Native.Chips.MulChip.Defs
import SP1Clean.Proofs.CircuitProofStart

/-! # Structural metadata for the MUL chip

This module isolates the subcircuit-list normalization needed by the public circuit bundle.  It is
kept out of the semantic proof so changes to witness elaboration do not force Lean to revisit MUL's
expensive arithmetic completeness theorem while developing channel metadata. -/

namespace SP1Clean.MulChip

open Circuit
open SP1Clean.Channels (stateChannel memoryChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- MUL's only external requirement channels are the State and Memory channels of its retained
readers.  The multiplication operation has no requirements, and all chip-owned equations are shallow
`assertZero`s. -/
theorem requirementsChannelsLawful_main (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).RequirementsChannelsLawful
      (elaborated (p := p)).channelsWithGuarantees
      [stateChannel.toRaw, memoryChannel.toRaw] := by
  dsimp only [Operations.RequirementsChannelsLawful]
  refine ⟨?_, ?_, ?_⟩
  · simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
      witnessVectorNative, CircuitNormalization.witnessNative_apply_eq,
      subcircuitWithAssertion, assertion, assertZero, Operations.localLength]
    simp only [Operations.subcircuitChannelsWithRequirements_append,
      Operations.subcircuitChannelsWithRequirements_witness,
      Operations.subcircuitChannelsWithRequirements_subcircuit,
      Operations.subcircuitChannelsWithRequirements_assert,
      Operations.subcircuitChannelsWithRequirements_nil,
      GeneralFormalCircuit.toSubcircuit_channelsWithRequirements,
      FormalAssertion.toSubcircuit_channelsWithRequirements,
      Readers.CPUState.channelsWithRequirements_eq, MulOperation.circuit,
      Readers.RTypeReader.circuit, Readers.RegisterWrite.circuit,
      List.nil_append, List.append_nil]
    simp only [List.subset_def, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  · intro channel hChannel
    simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
      witnessVectorNative, CircuitNormalization.witnessNative_apply_eq,
      subcircuitWithAssertion, assertion, assertZero, Operations.localLength,
      Operations.shallowChannels_append, Operations.shallowChannels_witness,
      Operations.shallowChannels_subcircuit, Operations.shallowChannels_assert,
      Operations.shallowChannels_nil, List.nil_append] at hChannel
    exact (List.not_mem_nil hChannel).elim
  · intro env _hConstraints
    rw [Operations.inChannelsOrRequirements_iff_forall_mem]
    intro interaction hInteraction
    simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
      witnessVectorNative, CircuitNormalization.witnessNative_apply_eq,
      subcircuitWithAssertion, assertion, assertZero, Operations.localLength,
      Operations.shallowInteractions_append, Operations.shallowInteractions_witness,
      Operations.shallowInteractions_subcircuit, Operations.shallowInteractions_assert,
      Operations.shallowInteractions_nil, List.nil_append] at hInteraction
    exact (List.not_mem_nil hInteraction).elim

/-- The retained R-type reader occurs immediately after MUL's 54-cell witness prefix.  This folded
membership lemma prevents timestamp proofs from normalizing every multiplication assertion. -/
theorem rTypeReader_mem (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ⟨offset + 54,
      Readers.RTypeReader.circuit.toSubcircuit (offset + 54) (rTypeReaderInput input offset)⟩ ∈
      ((main input).operations offset).subcircuits := by
  simp only [main, rTypeReaderInput, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
    witnessVectorNative, subcircuitWithAssertion, assertion, assertZero, Operations.localLength,
    Operations.subcircuits_witness,
    Operations.subcircuits_subcircuit, Operations.subcircuits_assert,
    Operations.subcircuits_nil, GeneralFormalCircuit.toSubcircuit_localLength,
    FormalAssertion.toSubcircuit_localLength, Readers.CPUState.circuit_localLength,
    MulOperation.circuit_localLength, Readers.RTypeReader.circuit_localLength,
    List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil, or_false, circuit_norm]
  right
  right
  left
  rfl

end SP1Clean.MulChip
