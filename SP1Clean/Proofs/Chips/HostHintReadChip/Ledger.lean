import SP1Clean.Proofs.Chips.HostHintReadChip.Formal
import SP1Clean.Proofs.Operations.HintReadSpanLedger
import SP1Clean.Proofs.Operations.HintReadStepLedger

/-! # Physical HINT_READ coordination ledger

The handler consumes one instruction call, current queue token, node, and authenticated final
word. It emits the popped queue token and the two complete word-walk endpoints. RAM updates
and byte permissions belong exclusively to the physical word consumers.
-/

namespace SP1Clean.HostHintReadChip

open Circuit Air.Flat
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

omit [Fact (2 ^ 25 < p)] in
private theorem equality_empty (k : ℕ) (target : RawChannel (ZMod p))
    (input : Var (ProvablePair (fields k) (fields k)) (ZMod p)) (offset : ℕ) :
    (FlatOperation.interactions ((Gadgets.Equality.circuit (fields k)).toSubcircuit offset input).ops.toFlat).filter
      (fun (i : AbstractInteraction (ZMod p)) => decide (i.channel = target)) = [] :=
  InteractionRecovery.filter_interactions_formalAssertion_eq_nil
    (Gadgets.Equality.circuit (fields k)) target input List.not_mem_nil List.not_mem_nil

theorem main_nonbyte_interactions (input : Var Inputs (ZMod p)) (offset : ℕ)
    (target : RawChannel (ZMod p)) (notByte : target ≠ Channels.byteChannel.toRaw) :
    ((main input).operations offset).interactionsWith target =
      [(HostHintQueue.wordChannel.pulled input.endStep.word).toRaw,
       (HostHintQueue.nodeChannel.pulled input.node).toRaw,
       (HostCallChip.channel.pulled input.call).toRaw,
       (HostHintQueue.stateChannel.pulled input.previous).toRaw,
       (HostHintQueue.stateChannel.pushed input.next).toRaw,
       (HintReadWordChip.stateChannel.pushed input.first).toRaw,
       (HintReadWordChip.stateChannel.pulled input.final).toRaw].filter
        (fun i => decide (i.channel = target)) := by
  have clockEmpty (n : ℕ) := InteractionRecovery.interactionsWith_main_eq_nil
    ClockOrder.circuit.base target input.clock n (by simp [ClockOrder.circuit, circuit_norm])
  have spanEmpty (n : ℕ) := HintReadSpan.main_other_interactions target notByte input.span n
  have step (n : ℕ) := HintReadStep.main_nonbyte_interactions true input.endStep n target notByte
  simp only [main, circuit_norm, List.nil_append]
  simp only [Operations.interactionsWith] at clockEmpty spanEmpty step ⊢
  simp only [GeneralFormalCircuit.toSubcircuit_interactions,
    HintReadSpan.circuit, HintReadStep.circuit, clockEmpty, spanEmpty, step,
    equality_empty, List.nil_append]
  by_cases selected : HostHintQueue.wordChannel.toRaw = target <;>
    simp [List.filter_cons, circuit_norm, selected]

theorem main_host_interactions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith HostCallChip.channel.toRaw =
      [(HostCallChip.channel.pulled input.call).toRaw] := by
  rw [main_nonbyte_interactions _ _ _ (by simp [HostCallChip.channel, Channels.byteChannel, Channel.toRaw])]
  simp [circuit_norm, HostCallChip.channel, HostHintQueue.nodeChannel, HostHintQueue.wordChannel,
    HostHintQueue.stateChannel, HintReadWordChip.stateChannel]

theorem main_queue_interactions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith HostHintQueue.stateChannel.toRaw =
      [(HostHintQueue.stateChannel.pulled input.previous).toRaw,
       (HostHintQueue.stateChannel.pushed input.next).toRaw] := by
  rw [main_nonbyte_interactions _ _ _ (by simp [HostHintQueue.stateChannel, Channels.byteChannel, Channel.toRaw])]
  simp [circuit_norm, HostCallChip.channel, HostHintQueue.nodeChannel, HostHintQueue.wordChannel,
    HostHintQueue.stateChannel, HintReadWordChip.stateChannel]

theorem main_cursor_interactions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith HintReadWordChip.stateChannel.toRaw =
      [(HintReadWordChip.stateChannel.pushed input.first).toRaw,
       (HintReadWordChip.stateChannel.pulled input.final).toRaw] := by
  rw [main_nonbyte_interactions _ _ _ (by simp [HintReadWordChip.stateChannel, Channels.byteChannel, Channel.toRaw])]
  simp [circuit_norm, HostCallChip.channel, HostHintQueue.nodeChannel, HostHintQueue.wordChannel,
    HostHintQueue.stateChannel, HintReadWordChip.stateChannel]

theorem main_node_interactions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith HostHintQueue.nodeChannel.toRaw =
      [(HostHintQueue.nodeChannel.pulled input.node).toRaw] := by
  rw [main_nonbyte_interactions _ _ _ (by simp [HostHintQueue.nodeChannel, Channels.byteChannel, Channel.toRaw])]
  simp [circuit_norm, HostCallChip.channel, HostHintQueue.nodeChannel, HostHintQueue.wordChannel,
    HostHintQueue.stateChannel, HintReadWordChip.stateChannel]

theorem main_word_interactions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith HostHintQueue.wordChannel.toRaw =
      [(HostHintQueue.wordChannel.pulled input.endStep.word).toRaw] := by
  rw [main_nonbyte_interactions _ _ _ (by simp [HostHintQueue.wordChannel, Channels.byteChannel, Channel.toRaw])]
  simp [circuit_norm, HostCallChip.channel, HostHintQueue.nodeChannel, HostHintQueue.wordChannel,
    HostHintQueue.stateChannel, HintReadWordChip.stateChannel]

theorem host_values (input : Var Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((main input).operations offset).interactionValuesWith HostCallChip.channel.toRaw env =
      [HostCallChip.channel.pulledValue (Eval.eval env input.call)] := by
  simp only [Operations.interactionValuesWith, main_host_interactions,
    List.map_cons, List.map_nil, Channel.eval_pulled]

theorem queue_values (input : Var Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((main input).operations offset).interactionValuesWith HostHintQueue.stateChannel.toRaw env =
      [HostHintQueue.stateChannel.pulledValue (Eval.eval env input.previous),
       HostHintQueue.stateChannel.pushedValue (Eval.eval env input.next)] := by
  simp only [Operations.interactionValuesWith, main_queue_interactions,
    List.map_cons, List.map_nil, Channel.eval_pulled, Channel.eval_pushed]

omit [Fact (2 ^ 25 < p)] in
private theorem eval_endpoints (env : Environment (ZMod p)) (input : Var Inputs (ZMod p)) :
    Eval.eval env input.first = (Eval.eval env input).first ∧
      Eval.eval env input.final = (Eval.eval env input).final := by
  rcases input with ⟨call, previous, node, span, lastIndex, lastValue⟩
  rcases call with ⟨high, low, code, arg1, arg2, result, length⟩
  rcases node with ⟨pointer, tail, length⟩
  rcases span with ⟨start, quotients, length, last, count⟩
  simp only [Inputs.first, Inputs.final, circuit_norm, and_self]

theorem cursor_values (input : Var Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((main input).operations offset).interactionValuesWith HintReadWordChip.stateChannel.toRaw env =
      [HintReadWordChip.stateChannel.pushedValue (Eval.eval env input).first,
       HintReadWordChip.stateChannel.pulledValue (Eval.eval env input).final] := by
  simp only [Operations.interactionValuesWith, main_cursor_interactions,
    List.map_cons, List.map_nil, Channel.eval_pulled, Channel.eval_pushed,
    (eval_endpoints env input).1, (eval_endpoints env input).2]

end SP1Clean.HostHintReadChip
