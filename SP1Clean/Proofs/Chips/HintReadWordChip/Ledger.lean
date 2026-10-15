import SP1Clean.Proofs.Chips.HintReadWordChip.Formal
import SP1Clean.Proofs.Chips.HostRamAccessChip.Ledger
import SP1Clean.Proofs.Operations.HintReadStepLedger
import Clean.Air.Balance

/-! # Physical hint word ledgers

Every row contributes one Memory transfer, one immutable word pull, eight byte permissions,
and an exact cursor edge. The internal access-coordination pair cancels for every environment.
The coverage proof consumes these equations for actual circuit operations.
-/

namespace SP1Clean.HintReadWordChip

open Circuit Channels
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

private theorem ram_main : (HostRamAccessChip.circuit (p := p)).main = HostRamAccessChip.main := rfl
private theorem step_main (last : Bool) : (HintReadStep.circuit (p := p) last).main = HintReadStep.main last := rfl

theorem main_state_interactions (last : Bool) (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main last input).operations offset).interactionsWith stateChannel.toRaw =
      [(stateChannel.pulled input.previous).toRaw, (stateChannel.pushed input.next).toRaw] := by
  have ram (n : ℕ) := InteractionRecovery.interactionsWith_main_eq_nil
    HostRamAccessChip.circuit.base stateChannel.toRaw input.ram n
    (by simp [HostRamAccessChip.circuit, HostRamAccessChip.elaborated, circuit_norm,
      stateChannel, HostRamAccessChip.channel,
      memoryChannel, byteChannel])
  have step (n : ℕ) := HintReadStep.main_nonbyte_interactions (p := p) last (input.step last) n
    stateChannel.toRaw (by simp [stateChannel, byteChannel, circuit_norm])
  simp only [main, circuit_norm, List.nil_append]
  simp only [Operations.interactionsWith, Circuit.operations, ram_main] at ram step ⊢
  simp only [GeneralFormalCircuit.toSubcircuit_interactions, ram_main, step_main, ram,
    step]
  simp [circuit_norm, stateChannel, HostHintQueue.wordChannel, HostRamAccessChip.channel,
    WritePermissionProvider.channel, Circuit.forEach.operations_eq,
    List.ofFn_succ, List.ofFn_zero]

theorem main_word_interactions (last : Bool) (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main last input).operations offset).interactionsWith HostHintQueue.wordChannel.toRaw =
      [(HostHintQueue.wordChannel.pulled (input.step last).word).toRaw] := by
  have ram (n : ℕ) := InteractionRecovery.interactionsWith_main_eq_nil
    HostRamAccessChip.circuit.base HostHintQueue.wordChannel.toRaw input.ram n
    (by simp [HostRamAccessChip.circuit, HostRamAccessChip.elaborated, circuit_norm,
      HostHintQueue.wordChannel, HostRamAccessChip.channel,
      memoryChannel, byteChannel])
  have step (n : ℕ) := HintReadStep.main_nonbyte_interactions (p := p) last (input.step last) n
    HostHintQueue.wordChannel.toRaw (by simp [HostHintQueue.wordChannel, byteChannel, circuit_norm])
  simp only [main, circuit_norm, List.nil_append]
  simp only [Operations.interactionsWith, Circuit.operations, ram_main] at ram step ⊢
  simp only [GeneralFormalCircuit.toSubcircuit_interactions, ram_main, step_main, ram,
    step]
  simp [circuit_norm, stateChannel, HostHintQueue.wordChannel, HostRamAccessChip.channel,
    WritePermissionProvider.channel, Circuit.forEach.operations_eq,
    List.ofFn_succ, List.ofFn_zero]

theorem main_memory_interactions (last : Bool) (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main last input).operations offset).interactionsWith memoryChannel.toRaw =
      [(memoryChannel.pulled input.ram.prior).toRaw, (memoryChannel.pushed input.ram.pushed).toRaw] := by
  have ram := HostRamAccessChip.main_memory_interactions (p := p)
  have step (n : ℕ) := HintReadStep.main_nonbyte_interactions (p := p) last (input.step last) n
    memoryChannel.toRaw (by simp [memoryChannel, byteChannel, circuit_norm])
  simp only [main, circuit_norm, List.nil_append]
  simp only [Operations.interactionsWith, Circuit.operations] at ram step ⊢
  simp only [GeneralFormalCircuit.toSubcircuit_interactions, ram_main, step_main, ram,
    step]
  simp [circuit_norm, stateChannel, HostHintQueue.wordChannel, HostRamAccessChip.channel,
    WritePermissionProvider.channel, memoryChannel, Circuit.forEach.operations_eq,
    List.ofFn_succ, List.ofFn_zero]

theorem main_access_interactions (last : Bool) (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main last input).operations offset).interactionsWith HostRamAccessChip.channel.toRaw =
      [(HostRamAccessChip.channel.pushed input.ram.message).toRaw,
       (HostRamAccessChip.channel.pulled input.ram.message).toRaw] := by
  have ram := HostRamAccessChip.main_host_interactions (p := p)
  have step (n : ℕ) := HintReadStep.main_nonbyte_interactions (p := p) last (input.step last) n
    HostRamAccessChip.channel.toRaw (by simp [HostRamAccessChip.channel, byteChannel, circuit_norm])
  simp only [main, circuit_norm, List.nil_append]
  simp only [Operations.interactionsWith, Circuit.operations] at ram step ⊢
  simp only [GeneralFormalCircuit.toSubcircuit_interactions, ram_main, step_main, ram,
    step]
  simp [circuit_norm, stateChannel, HostHintQueue.wordChannel, HostRamAccessChip.channel,
    WritePermissionProvider.channel, Circuit.forEach.operations_eq,
    List.ofFn_succ, List.ofFn_zero]

theorem main_permission_interactions (last : Bool) (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main last input).operations offset).interactionsWith WritePermissionProvider.channel.toRaw =
      List.ofFn (fun index : Fin 8 =>
        (WritePermissionProvider.channel.pulled (Address.offset input.address (.const (index.val : ZMod p)))).toRaw) := by
  have ram (n : ℕ) := InteractionRecovery.interactionsWith_main_eq_nil
    HostRamAccessChip.circuit.base WritePermissionProvider.channel.toRaw input.ram n
    (by simp [HostRamAccessChip.circuit, HostRamAccessChip.elaborated, circuit_norm,
      HostRamAccessChip.channel,
      WritePermissionProvider.channel, memoryChannel, byteChannel])
  have step (n : ℕ) := HintReadStep.main_nonbyte_interactions (p := p) last (input.step last) n
    WritePermissionProvider.channel.toRaw (by simp [WritePermissionProvider.channel, byteChannel, circuit_norm])
  simp only [main, circuit_norm, List.nil_append]
  simp only [Operations.interactionsWith, Circuit.operations, ram_main] at ram step ⊢
  simp only [GeneralFormalCircuit.toSubcircuit_interactions, ram_main, step_main, ram,
    step]
  simp [circuit_norm, stateChannel, HostHintQueue.wordChannel, HostRamAccessChip.channel,
    WritePermissionProvider.channel, Circuit.forEach.operations_eq,
    List.ofFn_succ, List.ofFn_zero]

theorem state_values (last : Bool) (input : Var Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((main last input).operations offset).interactionValuesWith stateChannel.toRaw env =
      [stateChannel.pulledValue (Eval.eval env input.previous),
       stateChannel.pushedValue (Eval.eval env input.next)] := by
  simp only [Operations.interactionValuesWith, main_state_interactions,
    List.map_cons, List.map_nil, Channel.eval_pulled, Channel.eval_pushed]

theorem word_values (last : Bool) (input : Var Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((main last input).operations offset).interactionValuesWith HostHintQueue.wordChannel.toRaw env =
      [HostHintQueue.wordChannel.pulledValue (Eval.eval env (input.step last).word)] := by
  simp only [Operations.interactionValuesWith, main_word_interactions,
    List.map_cons, List.map_nil, Channel.eval_pulled]

theorem memory_values (last : Bool) (input : Var Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((main last input).operations offset).interactionValuesWith memoryChannel.toRaw env =
      [memoryChannel.pulledValue (Eval.eval env input.ram.prior),
       memoryChannel.pushedValue (Eval.eval env input.ram.pushed)] := by
  simp only [Operations.interactionValuesWith, main_memory_interactions,
    List.map_cons, List.map_nil, Channel.eval_pulled, Channel.eval_pushed]

theorem access_values (last : Bool) (input : Var Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((main last input).operations offset).interactionValuesWith HostRamAccessChip.channel.toRaw env =
      [HostRamAccessChip.channel.pushedValue (Eval.eval env input.ram.message),
       HostRamAccessChip.channel.pulledValue (Eval.eval env input.ram.message)] := by
  simp only [Operations.interactionValuesWith, main_access_interactions,
    List.map_cons, List.map_nil, Channel.eval_pulled, Channel.eval_pushed]

theorem access_balance (last : Bool) (input : Var Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p)) (message : Array (ZMod p)) :
    balanceOf (((main last input).operations offset).interactionValuesWith
      HostRamAccessChip.channel.toRaw env) message = 0 := by
  rw [access_values]
  simp only [balanceOf_cons]
  by_cases equal : (toElements (Eval.eval env input.ram.message)).toArray = message <;>
    simp [Channel.pushedValue, Channel.pulledValue, equal, balanceOf]

end SP1Clean.HintReadWordChip
