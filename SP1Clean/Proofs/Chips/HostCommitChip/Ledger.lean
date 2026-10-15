import SP1Clean.Proofs.Chips.HostCommitChip.Formal

/-! # Commitment calls on the actual Clean ledger

Each row consumes one instruction handoff, replaces one bank state, and supplies the original
instruction's historical PublicValues entries. Byte checks remain internal subcircuits.
These projections do not supply the bank's initial/final endpoints or prove global balance.
-/

namespace SP1Clean.HostCommitChip

open Circuit Channels
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

omit [Fact (2 ^ 25 < p)] in
private theorem equality_empty (target : RawChannel (ZMod p))
    (input : Var (ProvablePair Word Word) (ZMod p)) (offset : ℕ) :
    (FlatOperation.interactions ((Gadgets.Equality.circuit Word).toSubcircuit offset input).ops.toFlat).filter
      (fun (i : AbstractInteraction (ZMod p)) => decide (i.channel = target)) = [] :=
  InteractionRecovery.filter_interactions_formalAssertion_eq_nil
    (Gadgets.Equality.circuit Word) target input List.not_mem_nil List.not_mem_nil

private theorem bytes_empty (target : RawChannel (ZMod p)) (different : target ≠ byteChannel.toRaw)
    (input : Var U16toU8OperationSafe.Inputs (ZMod p)) (offset : ℕ) :
    (FlatOperation.interactions (U16toU8OperationSafe.circuit.toSubcircuit offset input).ops.toFlat).filter
      (fun (i : AbstractInteraction (ZMod p)) => decide (i.channel = target)) = [] := by
  apply InteractionRecovery.filter_interactions_formalAssertion_eq_nil
  · simpa [U16toU8OperationSafe.circuit, circuit_norm] using different
  · exact List.not_mem_nil

/-- The per-call public records, before evaluation. They are intentionally historical values. -/
def publicInteractions (deferred : Bool) (slot : Fin 8) (input : Var Inputs (ZMod p)) :
    List (AbstractInteraction (ZMod p)) :=
  if deferred then
    [(publicValuesChannel.pushed ⟨147, 1⟩).toRaw,
     (publicValuesChannel.pushed ⟨Expression.const ((72 + slot.val : ℕ) : ZMod p),
       input.call.arg2[0] + input.call.arg2[1] * 65536⟩).toRaw]
  else
    (publicValuesChannel.pushed ⟨145, 1⟩).toRaw :: List.ofFn (fun i : Fin 4 =>
      (publicValuesChannel.pushed
        ⟨Expression.const ((32 + 4 * slot.val + i.val : ℕ) : ZMod p),
         (input.digest (Expression.const (256 : ZMod p)⁻¹))[i]⟩).toRaw)

private theorem main_nonbyte (deferred : Bool) (slot : Fin 8) (input : Var Inputs (ZMod p))
    (offset : ℕ) (target : RawChannel (ZMod p)) (different : target ≠ byteChannel.toRaw) :
    ((main deferred slot input).operations offset).interactionsWith target =
      ([(HostCallChip.channel.pulled input.call).toRaw,
        ((stateChannel deferred).pulled input.previous).toRaw,
        ((stateChannel deferred).pushed (input.next slot)).toRaw] ++
        publicInteractions deferred slot input).filter (fun i => decide (i.channel = target)) := by
  have clockEmpty (n : ℕ) := InteractionRecovery.interactionsWith_main_eq_nil
    ClockOrder.circuit.base target input.clock n
    (by simp [ClockOrder.circuit, circuit_norm])
  have boundEmpty (n : ℕ) := InteractionRecovery.interactionsWith_main_eq_nil
    (BoundedWord.circuit (bound p deferred) (bound_fits p deferred)).base target
    ⟨input.call.arg2, input.comparison⟩ n
    (by simpa [BoundedWord.circuit, circuit_norm] using different)
  cases deferred <;> simp only [main, circuit_norm, List.nil_append]
  all_goals
    simp only [Operations.interactionsWith] at clockEmpty boundEmpty ⊢
    simp only [GeneralFormalCircuit.toSubcircuit_interactions, clockEmpty, boundEmpty,
      equality_empty, bytes_empty target different, List.nil_append]
    simp [publicInteractions, circuit_norm, List.ofFn_succ, List.filter_cons]

theorem main_host_interactions (deferred : Bool) (slot : Fin 8)
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main deferred slot input).operations offset).interactionsWith HostCallChip.channel.toRaw =
      [(HostCallChip.channel.pulled input.call).toRaw] := by
  rw [main_nonbyte deferred slot input offset _ (by simp [HostCallChip.channel, byteChannel, circuit_norm])]
  cases deferred <;> simp [publicInteractions, HostCallChip.channel, stateChannel,
    publicValuesChannel, circuit_norm, List.ofFn_succ]

theorem main_state_interactions (deferred : Bool) (slot : Fin 8)
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main deferred slot input).operations offset).interactionsWith (stateChannel deferred).toRaw =
      [((stateChannel deferred).pulled input.previous).toRaw,
       ((stateChannel deferred).pushed (input.next slot)).toRaw] := by
  rw [main_nonbyte deferred slot input offset _ (by cases deferred <;> simp [stateChannel, byteChannel, circuit_norm])]
  cases deferred <;> simp [publicInteractions, HostCallChip.channel, stateChannel,
    publicValuesChannel, circuit_norm, List.ofFn_succ]

theorem main_public_interactions (deferred : Bool) (slot : Fin 8)
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main deferred slot input).operations offset).interactionsWith publicValuesChannel.toRaw =
      publicInteractions deferred slot input := by
  rw [main_nonbyte deferred slot input offset _ (by simp [publicValuesChannel, byteChannel, circuit_norm])]
  cases deferred <;> simp [publicInteractions, HostCallChip.channel, stateChannel,
    publicValuesChannel, circuit_norm, List.ofFn_succ]

theorem host_values (deferred : Bool) (slot : Fin 8) (input : Var Inputs (ZMod p))
    (offset : ℕ) (env : Environment (ZMod p)) :
    ((main deferred slot input).operations offset).interactionValuesWith HostCallChip.channel.toRaw env =
      [HostCallChip.channel.pulledValue (Eval.eval env input.call)] := by
  simp only [Operations.interactionValuesWith, main_host_interactions,
    List.map_cons, List.map_nil, Channel.eval_pulled]

theorem state_values (deferred : Bool) (slot : Fin 8) (input : Var Inputs (ZMod p))
    (offset : ℕ) (env : Environment (ZMod p)) :
    ((main deferred slot input).operations offset).interactionValuesWith (stateChannel deferred).toRaw env =
      [(stateChannel deferred).pulledValue (Eval.eval env input.previous),
       (stateChannel deferred).pushedValue (Eval.eval env (input.next slot))] := by
  simp only [Operations.interactionValuesWith, main_state_interactions,
    List.map_cons, List.map_nil, Channel.eval_pulled, Channel.eval_pushed]

end SP1Clean.HostCommitChip
