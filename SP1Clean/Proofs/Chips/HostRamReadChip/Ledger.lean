import SP1Clean.Proofs.Chips.HostRamReadChip.Formal
import SP1Clean.Proofs.Chips.HostRamAccessChip.Ledger
import Clean.Air.Balance

/-! # Physical and logical ledgers of shared host reads

One prior/new Memory pair survives composition, regardless of sharing. The lower-level
coordination pair cancels internally. Logical reads use separate unit-weight messages, so
the global count guard counts each possible copy.
-/

namespace SP1Clean.HostRamReadChip

open Circuit Channels
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

omit [Fact (2 ^ 25 < p)] in
private theorem equality_empty (target : RawChannel (ZMod p))
    (input : Var (ProvablePair Word Word) (ZMod p)) (offset : ℕ) :
    (FlatOperation.interactions
      ((Gadgets.Equality.circuit Word).toSubcircuit offset input).ops.toFlat).filter
        (fun (interaction : AbstractInteraction (ZMod p)) => decide (interaction.channel = target)) =
      [] := by
  exact InteractionRecovery.filter_interactions_formalAssertion_eq_nil
    (Gadgets.Equality.circuit Word) target input List.not_mem_nil List.not_mem_nil

private theorem ram_main : (HostRamAccessChip.circuit (p := p)).main =
    HostRamAccessChip.main := rfl

omit [Fact (2 ^ 25 < p)] in
private theorem boolean_empty (target : RawChannel (ZMod p))
    (input : Var field (ZMod p)) (offset : ℕ) :
    (FlatOperation.interactions (assertBool.toSubcircuit offset input).ops.toFlat).filter
        (fun (interaction : AbstractInteraction (ZMod p)) => decide (interaction.channel = target)) =
      [] := by
  exact InteractionRecovery.filter_interactions_formalAssertion_eq_nil
    assertBool target input List.not_mem_nil List.not_mem_nil

theorem main_memory_interactions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      [(memoryChannel.pulled input.ram.prior).toRaw,
       (memoryChannel.pushed input.ram.pushed).toRaw] := by
  have ram := HostRamAccessChip.main_memory_interactions (p := p)
  simp only [main, circuit_norm, List.nil_append]
  have boolean := boolean_empty (p := p)
  simp only [circuit_norm] at boolean
  simp only [Operations.interactionsWith, Circuit.operations] at ram ⊢
  simp only [GeneralFormalCircuit.toSubcircuit_interactions, ram_main, ram, equality_empty,
    boolean, List.nil_append]
  simp [circuit_norm, channel, HostRamAccessChip.channel, memoryChannel]

theorem main_access_interactions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith HostRamAccessChip.channel.toRaw =
      [(HostRamAccessChip.channel.pushed input.ram.message).toRaw,
       (HostRamAccessChip.channel.pulled input.ram.message).toRaw] := by
  have ram := HostRamAccessChip.main_host_interactions (p := p)
  simp only [main, circuit_norm, List.nil_append]
  have boolean := boolean_empty (p := p)
  simp only [circuit_norm] at boolean
  simp only [Operations.interactionsWith, Circuit.operations] at ram ⊢
  simp only [GeneralFormalCircuit.toSubcircuit_interactions, ram_main, ram, equality_empty,
    boolean, List.nil_append]
  simp [circuit_norm, channel, HostRamAccessChip.channel]

theorem main_read_interactions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith channel.toRaw =
      [(channel.pushed input.message).toRaw,
       (channel.pushedIf input.shared input.message).toRaw] := by
  have ram (n : ℕ) := InteractionRecovery.interactionsWith_main_eq_nil
    HostRamAccessChip.circuit.base channel.toRaw input.ram n
    (by simp [HostRamAccessChip.circuit, HostRamAccessChip.elaborated,
      circuit_norm, channel, HostRamAccessChip.channel, memoryChannel, byteChannel])
  simp only [main, circuit_norm, List.nil_append]
  have boolean := boolean_empty (p := p)
  simp only [circuit_norm] at boolean
  simp only [Operations.interactionsWith, Circuit.operations] at ram ⊢
  simp only [GeneralFormalCircuit.toSubcircuit_interactions, ram, equality_empty,
    boolean, List.nil_append]
  simp [circuit_norm, channel, HostRamAccessChip.channel]

theorem memory_values (input : Var Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((main input).operations offset).interactionValuesWith memoryChannel.toRaw env =
      [memoryChannel.pulledValue (Eval.eval env input.ram.prior),
       memoryChannel.pushedValue (Eval.eval env input.ram.pushed)] := by
  simp only [Operations.interactionValuesWith, main_memory_interactions,
    List.map_cons, List.map_nil, Channel.eval_pulled, Channel.eval_pushed]

theorem access_values (input : Var Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((main input).operations offset).interactionValuesWith HostRamAccessChip.channel.toRaw env =
      [HostRamAccessChip.channel.pushedValue (Eval.eval env input.ram.message),
       HostRamAccessChip.channel.pulledValue (Eval.eval env input.ram.message)] := by
  simp only [Operations.interactionValuesWith, main_access_interactions,
    List.map_cons, List.map_nil, Channel.eval_pulled, Channel.eval_pushed]

theorem read_values (input : Var Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((main input).operations offset).interactionValuesWith channel.toRaw env =
      [channel.pushedValue (Eval.eval env input.message),
       channel.pushedIfValue (env input.shared) (Eval.eval env input.message)] := by
  simp only [Operations.interactionValuesWith, main_read_interactions,
    List.map_cons, List.map_nil, Channel.eval_pushed, Channel.eval_pushedIf, ProvableType.eval_field]

/-- A read row has no net access-coordination demand, for every environment. -/
theorem access_balance (input : Var Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (message : Array (ZMod p)) :
    balanceOf (((main input).operations offset).interactionValuesWith
      HostRamAccessChip.channel.toRaw env) message = 0 := by
  rw [access_values]
  simp only [balanceOf_cons]
  by_cases equal : (toElements (Eval.eval env input.ram.message)).toArray = message <;>
    simp [Channel.pushedValue, Channel.pulledValue, equal, balanceOf]

end SP1Clean.HostRamReadChip
