import SP1Clean.Native.Operations.HostRamBytes
import SP1Clean.Model.Core.HostReadWords
import ToClean.Circuit.InteractionRecovery

/-! # Canonical bytes from a bounded host read

The existing safe decoder establishes byte bounds and exact reassembly. The read channel
supplies the aligned guest address and word bounds from the producing RAM row's local proof.
No caller supplies byte equations to soundness.
-/

namespace SP1Clean.HostRamBytes

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

private theorem bytes_spec (input : Inputs (ZMod p)) (read : input.read.Valid)
    (decoded : U16toU8OperationSafe.DecompSpec input.read.value ⟨input.low⟩) :
    Spec input (bytes (256 : ZMod p)⁻¹ input) := by
  have bounded : ∀ index : Fin 8, (bytes (256 : ZMod p)⁻¹ input)[index].val < 256 := by
    intro index
    fin_cases index
    · exact (decoded 0).1
    · exact (decoded 0).2.1
    · exact (decoded 1).1
    · exact (decoded 1).2.1
    · exact (decoded 2).1
    · exact (decoded 2).2.1
    · exact (decoded 3).1
    · exact (decoded 3).2.1
  have packed : Word.ofBytes (bytes (256 : ZMod p)⁻¹ input) = input.read.value := by
    apply Vector.ext
    intro index bound
    interval_cases index
    all_goals simp only [Word.ofBytes, bytes, circuit_norm]
    all_goals rw [mul_left_comm, mul_inv_cancel₀ val_256_ne_zero, mul_one, add_sub_cancel]
  exact ⟨read, bounded, packed ▸ Word.toBitVec64_ofByteFields _ bounded⟩

theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main
    (fun _ _ => True) (fun input output _ => Spec input output) := by
  circuit_proof_start [U16toU8OperationSafe.circuit, U16toU8OperationSafe.Assumptions,
    HostRamReadChip.channel, bytes]
  obtain ⟨decoded, read⟩ := h_holds
  obtain ⟨⟨_, _, _, _, _, values⟩, low⟩ := h_input
  have evalValue (index : ℕ) (bound : index < 4) :
      env input_var_read_value[index] = input_read_value[index] := by
    rw [← values, Vector.getElem_map]
  have evalLow (index : ℕ) (bound : index < 4) :
      env input_var_low[index] = input_low[index] := by
    rw [← low, Vector.getElem_map]
  simp only [evalValue, evalLow]
  simpa only [Spec, bytes, circuit_norm] using bytes_spec ⟨_, _⟩ read (decoded rfl)

theorem completeness : GeneralFormalCircuit.Completeness (ZMod p) main
    (fun input _ _ => ProverAssumptions input) (fun _ _ _ => True) := by
  circuit_proof_start [U16toU8OperationSafe.circuit, U16toU8OperationSafe.Assumptions,
    HostRamReadChip.channel]
  obtain ⟨read, low⟩ := h_assumptions
  refine ⟨?_, read⟩
  rw [low]
  exact U16toU8OperationSafe.spec_populate (read.2.2.2.2 0) (read.2.2.2.2 1)
    (read.2.2.2.2 2) (read.2.2.2.2 3) 1

def circuit : GeneralFormalCircuit (ZMod p) Inputs (fields 8) where
  main
  elaborated
  Spec input output _ := Spec input output
  ProverAssumptions input _ _ := ProverAssumptions input
  soundness
  completeness
  channelsWithRequirements := []
  requirementsChannelsLawful input offset := by
    preserve_tactic_target
    refine ⟨?_, ?_, ?_⟩
    · simp only [main, circuit_norm]
    · simp only [main, circuit_norm]
    · intro env _
      -- Inspect the single shallow pull without unfolding the read channel's semantic predicate.
      rw [Operations.inChannelsOrRequirements_iff_forall_mem]
      have shallow : ((main input).operations offset).shallowInteractions =
          [(HostRamReadChip.channel.pulled input.read).toRaw] := by
        simp only [main, circuit_norm]
      intro interaction member
      rw [shallow, List.mem_singleton] at member
      subst interaction
      apply Or.inr
      rw [ChannelInteraction.toRaw_requirements]
      intro impossible
      exact (impossible (by simp only [circuit_norm])).elim

@[circuit_norm, explicit_circuit_norm]
theorem circuit_localLength (input : Var Inputs (ZMod p)) : circuit.localLength input = 0 := rfl

@[circuit_norm, explicit_circuit_norm]
theorem channelsWithGuarantees_eq : (circuit (p := p)).channelsWithGuarantees =
    [Channels.byteChannel.toRaw, HostRamReadChip.channel.toRaw] := rfl

@[circuit_norm, explicit_circuit_norm]
theorem channelsWithRequirements_eq : circuit.channelsWithRequirements =
    ([] : List (RawChannel (ZMod p))) := rfl

omit [Fact (2 ^ 17 < p)] in
theorem populate_assumptions (read : HostRamReadChip.Message (ZMod p)) (valid : read.Valid) :
    ProverAssumptions (populate read) := ⟨valid, rfl⟩

omit [Fact (2 ^ 17 < p)] in
/-- Once the consumed word is grounded, the circuit output is the host's exact byte read. -/
theorem Spec.readBytes {input : Inputs (ZMod p)} {output : Vector (ZMod p) 8}
    (checked : Spec input output) (context : Model.Core.HostReadContext)
    (observed : context.ObservesWord (Word.toNat input.read.address)
      (Word.toBitVec64 input.read.value)) :
    context.readBytes? (Word.toNat input.read.address) 8 =
      some (output.map fun byte => BitVec.ofNat 8 byte.val).toList := by
  rw [checked.2.2] at observed
  exact Model.Core.HostReadContext.readBytes_of_word _ _ _ observed

open scoped Classical

/-- The decoder consumes exactly the supplied read, preserving its full clock/address/value key. -/
theorem main_read_interactions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith HostRamReadChip.channel.toRaw =
      [(HostRamReadChip.channel.pulled input.read).toRaw] := by
  have decoder := InteractionRecovery.filter_interactions_formalAssertion_eq_nil
    U16toU8OperationSafe.circuit HostRamReadChip.channel.toRaw
    (n := offset) ⟨input.read.value, ⟨input.low⟩, 1⟩
    (by simp [U16toU8OperationSafe.circuit, circuit_norm,
      HostRamReadChip.channel, Channels.byteChannel]) List.not_mem_nil
  simp only [main, circuit_norm, Operations.interactionsWith, List.nil_append]
  simp [circuit_norm]
  simpa using decoder

/-- Byte extraction adds no physical Memory touch. -/
theorem main_memory_interactions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith Channels.memoryChannel.toRaw = [] := by
  exact InteractionRecovery.interactionsWith_main_eq_nil circuit.base
    Channels.memoryChannel.toRaw input offset
    (by simp [circuit, elaborated, circuit_norm, HostRamReadChip.channel,
      Channels.memoryChannel, Channels.byteChannel])

/-- The evaluated ledger retains the consumed word without a re-encoding premise. -/
theorem read_values (input : Var Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((main input).operations offset).interactionValuesWith HostRamReadChip.channel.toRaw env =
      [HostRamReadChip.channel.pulledValue (Eval.eval env input.read)] := by
  simp only [Operations.interactionValuesWith, main_read_interactions,
    List.map_cons, List.map_nil, Channel.eval_pulled]

end SP1Clean.HostRamBytes
