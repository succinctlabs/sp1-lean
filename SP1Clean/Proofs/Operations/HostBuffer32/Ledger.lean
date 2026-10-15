import SP1Clean.Proofs.Operations.HostBuffer32

/-! # The complete buffer interaction ledger

Byte decoding and address gadgets add only their declared range checks. The buffer consumes
one full shared-read key per covering word and produces one complete buffer key. It adds no
physical Memory access.
-/

namespace SP1Clean.HostBuffer32

open Circuit
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Exactly one logical shared read for every covering word, in address order. -/
theorem main_read_interactions (offset : Fin 8) (input : Var (Inputs offset) (ZMod p)) (n : ℕ) :
    ((main offset input).operations n).interactionsWith HostRamReadChip.channel.toRaw =
      input.cells.toList.map (fun cell => (HostRamReadChip.channel.pulled cell.read).toRaw) := by
  have add (n : ℕ) (row : Var AddOperation.Inputs (ZMod p)) :=
    InteractionRecovery.filter_interactions_formalAssertion_eq_nil AddOperation.circuit
      HostRamReadChip.channel.toRaw (n := n) row
      (by simp [AddOperation.circuit, circuit_norm, HostRamReadChip.channel, Channels.byteChannel])
      List.not_mem_nil
  have pair (n : ℕ) (row : Var (ProvablePair fieldPair fieldPair) (ZMod p)) :=
    InteractionRecovery.filter_interactions_formalAssertion_eq_nil (Gadgets.Equality.circuit fieldPair)
      HostRamReadChip.channel.toRaw (n := n) row List.not_mem_nil List.not_mem_nil
  have vector (n : ℕ) (row : Var (ProvablePair (fields 32) (fields 32)) (ZMod p)) :=
    InteractionRecovery.filter_interactions_formalAssertion_eq_nil (Gadgets.Equality.circuit (fields 32))
      HostRamReadChip.channel.toRaw (n := n) row List.not_mem_nil List.not_mem_nil
  have read (n : ℕ) (cell : Var HostRamBytes.Inputs (ZMod p)) :
      (FlatOperation.interactions (HostRamBytes.circuit.toSubcircuit n cell).ops.toFlat).filter
          (fun interaction => interaction.channel = HostRamReadChip.channel.toRaw) =
        [(HostRamReadChip.channel.pulled cell.read).toRaw] := by
    rw [GeneralFormalCircuit.toSubcircuit_interactions]
    exact HostRamBytes.main_read_interactions cell n
  simp only [main, circuit_norm, Operations.interactionsWith, List.filter_append,
    List.filter_flatten, List.map_ofFn, Function.comp_def, add, pair, vector, read]
  simp [circuit_norm, channel, HostRamReadChip.channel]
  rw [← Vector.toList_ofFn]
  rw [← Vector.toList_map]
  congr 1
  ext index bound
  simp

/-- One complete buffer is offered to a call consumer, retaining clock, query, and every byte. -/
theorem main_buffer_interactions (offset : Fin 8) (input : Var (Inputs offset) (ZMod p)) (n : ℕ) :
    ((main offset input).operations n).interactionsWith channel.toRaw =
      [(channel.pushed input.message).toRaw] := by
  have add (n : ℕ) (row : Var AddOperation.Inputs (ZMod p)) :=
    InteractionRecovery.filter_interactions_formalAssertion_eq_nil AddOperation.circuit
      channel.toRaw (n := n) row
      (by simp [AddOperation.circuit, circuit_norm, channel, Channels.byteChannel])
      List.not_mem_nil
  have pair (n : ℕ) (row : Var (ProvablePair fieldPair fieldPair) (ZMod p)) :=
    InteractionRecovery.filter_interactions_formalAssertion_eq_nil (Gadgets.Equality.circuit fieldPair)
      channel.toRaw (n := n) row List.not_mem_nil List.not_mem_nil
  have vector (n : ℕ) (row : Var (ProvablePair (fields 32) (fields 32)) (ZMod p)) :=
    InteractionRecovery.filter_interactions_formalAssertion_eq_nil (Gadgets.Equality.circuit (fields 32))
      channel.toRaw (n := n) row List.not_mem_nil List.not_mem_nil
  have read (n : ℕ) (cell : Var HostRamBytes.Inputs (ZMod p)) :
      (FlatOperation.interactions (HostRamBytes.circuit.toSubcircuit n cell).ops.toFlat).filter
          (fun interaction => interaction.channel = channel.toRaw) = [] := by
    rw [GeneralFormalCircuit.toSubcircuit_interactions]
    exact InteractionRecovery.interactionsWith_main_eq_nil HostRamBytes.circuit.base
      channel.toRaw cell n
      (by simp [circuit_norm, HostRamReadChip.channel, channel, Channels.byteChannel])
  simp only [main, circuit_norm, Operations.interactionsWith, List.filter_append,
    List.filter_flatten, List.map_ofFn, Function.comp_def, add, pair, vector, read]
  simp [circuit_norm]

/-- A buffer consumer does not create an additional physical RAM access. -/
theorem main_memory_interactions (offset : Fin 8) (input : Var (Inputs offset) (ZMod p)) (n : ℕ) :
    ((main offset input).operations n).interactionsWith Channels.memoryChannel.toRaw = [] := by
  exact InteractionRecovery.interactionsWith_main_eq_nil (circuit offset).base
    Channels.memoryChannel.toRaw input n
    (by simp [circuit, elaborated, circuit_norm, HostRamReadChip.channel,
      channel, Channels.memoryChannel, Channels.byteChannel])

/-- The evaluated read ledger retains every consumed word's complete key. -/
theorem read_values (offset : Fin 8) (input : Var (Inputs offset) (ZMod p)) (n : ℕ)
    (env : Environment (ZMod p)) :
    ((main offset input).operations n).interactionValuesWith HostRamReadChip.channel.toRaw env =
      input.cells.toList.map (fun cell => HostRamReadChip.channel.pulledValue (Eval.eval env cell.read)) := by
  simp only [Operations.interactionValuesWith, main_read_interactions, List.map_map,
    Function.comp_def, Channel.eval_pulled]

/-- The evaluated buffer ledger has one message, preserving all 32 bytes. -/
theorem buffer_values (offset : Fin 8) (input : Var (Inputs offset) (ZMod p)) (n : ℕ)
    (env : Environment (ZMod p)) :
    ((main offset input).operations n).interactionValuesWith channel.toRaw env =
      [channel.pushedValue (Eval.eval env input.message)] := by
  simp only [Operations.interactionValuesWith, main_buffer_interactions, List.map_cons,
    List.map_nil, Channel.eval_pushed]

end SP1Clean.HostBuffer32
