import SP1Clean.Proofs.Chips.HostRamAccessChip.Formal

/-! # The actual host-access interaction ledger

The composed circuit retains exactly its prior/new Memory pair and one call-facing record.
These equations concern Clean's evaluated operations, so later ensemble transport cannot
substitute an unrelated footprint or discard the host's accesses.
-/

namespace SP1Clean.HostRamAccessChip

open Circuit Channels
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (p > 2) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

omit [Fact (2 ^ 25 < p)] in
set_option linter.unusedSectionVars false in
private theorem range_empty (target : RawChannel (ZMod p)) (n : ℕ) (bound : 2 ^ n < p)
    (input : Var field (ZMod p)) (offset : ℕ) :
    (FlatOperation.interactions ((Gadgets.ToBits.rangeCheck n bound).toSubcircuit offset input).ops.toFlat).filter
      (fun (interaction : AbstractInteraction (ZMod p)) => decide (interaction.channel = target)) = [] := by
  exact InteractionRecovery.filter_interactions_formalAssertion_eq_nil
    (Gadgets.ToBits.rangeCheck n bound) target input List.not_mem_nil List.not_mem_nil

private theorem word_empty (target : RawChannel (ZMod p)) (input : Var Word (ZMod p)) (offset : ℕ) :
    (FlatOperation.interactions (WordRangeCheck.circuit.toSubcircuit offset input).ops.toFlat).filter
      (fun (interaction : AbstractInteraction (ZMod p)) => decide (interaction.channel = target)) = [] := by
  exact InteractionRecovery.filter_interactions_formalAssertion_eq_nil
    WordRangeCheck.circuit target input List.not_mem_nil List.not_mem_nil

private theorem reader_memory (input : Var Readers.MemoryAccess.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.MemoryAccess.circuit.main input).operations offset).interactionsWith memoryChannel.toRaw =
      [(memoryChannel.pulledIf input.is_real
        ⟨input.mem.access_timestamp.prev_high, input.mem.access_timestamp.prev_low,
          input.addr0, input.addr1, input.addr2, input.mem.prev_value⟩).toRaw,
       (memoryChannel.pushedIf input.is_real
        ⟨input.clk_high, input.clk_low + 1, input.addr0, input.addr1, input.addr2, input.new_value⟩).toRaw] := by
  have equalityEmpty (args : Var (ProvablePair field field) (ZMod p)) (n : ℕ) :=
    @InteractionRecovery.filter_interactions_formalAssertion_eq_nil
      (ZMod p) _ (ProvablePair field field) ProvablePair.instance (Gadgets.Equality.circuit field)
      memoryChannel.toRaw n args List.not_mem_nil List.not_mem_nil
  simp [Readers.MemoryAccess.circuit, Readers.MemoryAccess.main, circuit_norm, equalityEmpty,
    Operations.interactionsWith]

theorem main_memory_interactions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      [(memoryChannel.pulled input.prior).toRaw, (memoryChannel.pushed input.pushed).toRaw] := by
  have addressEmpty (n : ℕ) := InteractionRecovery.interactionsWith_main_eq_nil
    AddressOperation.circuit.base memoryChannel.toRaw (FinalRamProvider.addressInput input.pushed) n
    (by simp [AddressOperation.circuit, circuit_norm, memoryChannel, byteChannel])
  simp only [main, circuit_norm, List.nil_append]
  have readerPair := reader_memory (p := p)
  simp only [Operations.interactionsWith] at addressEmpty readerPair ⊢
  simp only [GeneralFormalCircuit.toSubcircuit_interactions, addressEmpty, readerPair,
    word_empty, range_empty, List.nil_append]
  simp [Inputs.reader, Inputs.prior, Inputs.pushed, channel, memoryChannel, circuit_norm]

theorem main_host_interactions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith channel.toRaw =
      [(channel.pushed input.message).toRaw] := by
  have addressEmpty (n : ℕ) := InteractionRecovery.interactionsWith_main_eq_nil
    AddressOperation.circuit.base channel.toRaw (FinalRamProvider.addressInput input.pushed) n
    (by simp [AddressOperation.circuit, circuit_norm, channel, byteChannel])
  have readerEmpty (n : ℕ) := InteractionRecovery.interactionsWith_main_eq_nil
    Readers.MemoryAccess.circuit.base channel.toRaw input.reader n
    (by simp [Readers.MemoryAccess.circuit, circuit_norm, channel, byteChannel, memoryChannel])
  simp only [main, circuit_norm, List.nil_append]
  simp only [Operations.interactionsWith] at addressEmpty readerEmpty ⊢
  simp only [GeneralFormalCircuit.toSubcircuit_interactions, addressEmpty, readerEmpty,
    word_empty, range_empty, List.nil_append]

theorem memory_values (input : Var Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((main input).operations offset).interactionValuesWith memoryChannel.toRaw env =
      [memoryChannel.pulledValue (Eval.eval env input.prior),
       memoryChannel.pushedValue (Eval.eval env input.pushed)] := by
  simp only [Operations.interactionValuesWith, main_memory_interactions,
    List.map_cons, List.map_nil, Channel.eval_pulled, Channel.eval_pushed]

theorem host_values (input : Var Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((main input).operations offset).interactionValuesWith channel.toRaw env =
      [channel.pushedValue (Eval.eval env input.message)] := by
  simp only [Operations.interactionValuesWith, main_host_interactions,
    List.map_cons, List.map_nil, Channel.eval_pushed]

end SP1Clean.HostRamAccessChip
