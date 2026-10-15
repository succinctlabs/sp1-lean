import SP1Clean.Native.Operations.OrdinaryObservation
import ToClean.Circuit.InteractionRecovery
import Clean.Air.FlatComponent

/-! # Exact ordinary observation ledgers

The receipt pull and observation transition are read from the actual composed program. Its
four Byte pulls remain separate obligations, discharged in the enclosing physical assembly.
-/

namespace SP1Clean.OrdinaryObservation

open Circuit Channels Air.Flat
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- The existing word gadgets need only the weaker field bound. -/
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

private theorem main_nonbyte (enabled : Bool) (input : Var Inputs (ZMod p))
    (offset : ℕ) (target : RawChannel (ZMod p)) (different : target ≠ byteChannel.toRaw) :
    ((main enabled input).operations offset).interactionsWith target =
      [(InstructionReceipt.channel.pulled input.receipt).toRaw,
        (stateChannel.pulled input.previous).toRaw,
        (stateChannel.pushed input.next).toRaw].filter (fun i => decide (i.channel = target)) := by
  have clockEmpty (n : ℕ) := InteractionRecovery.interactionsWith_main_eq_nil
    ClockOrder.circuit.base target input.clock n (by simp [ClockOrder.circuit, circuit_norm])
  have wordEmpty (n : ℕ) :
      (FlatOperation.interactions (WordRangeCheck.circuit.toSubcircuit n input.previous.counter).ops.toFlat).filter
        (fun i => decide (i.channel = target)) = [] :=
    InteractionRecovery.filter_interactions_formalAssertion_eq_nil
      WordRangeCheck.circuit target input.previous.counter List.not_mem_nil List.not_mem_nil
  have addEmpty (n : ℕ) :
      (FlatOperation.interactions (AddOperation.circuit.toSubcircuit n
        ⟨input.previous.counter, increment enabled, ⟨input.counter⟩, 1⟩).ops.toFlat).filter
        (fun i => decide (i.channel = target)) = [] :=
    InteractionRecovery.filter_interactions_formalAssertion_eq_nil
      AddOperation.circuit target ⟨input.previous.counter, increment enabled, ⟨input.counter⟩, 1⟩
      (by simpa [AddOperation.circuit, circuit_norm] using different) List.not_mem_nil
  simp only [Operations.interactionsWith] at clockEmpty ⊢
  simp only [main, circuit_norm, GeneralFormalCircuit.toSubcircuit_interactions, List.filter_append,
    clockEmpty, wordEmpty, addEmpty, List.nil_append]

/-- Each row consumes precisely one ordinary receipt. -/
theorem main_receipt_interactions (enabled : Bool) (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main enabled input).operations offset).interactionsWith InstructionReceipt.channel.toRaw =
      [(InstructionReceipt.channel.pulled input.receipt).toRaw] := by
  rw [main_nonbyte enabled input offset _ (by simp [InstructionReceipt.channel, byteChannel, circuit_norm])]
  simp [InstructionReceipt.channel, stateChannel, circuit_norm]

/-- Each row is one literal unit transition of the observation state. -/
theorem main_state_interactions (enabled : Bool) (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main enabled input).operations offset).interactionsWith stateChannel.toRaw =
      [(stateChannel.pulled input.previous).toRaw, (stateChannel.pushed input.next).toRaw] := by
  rw [main_nonbyte enabled input offset _ (by simp [stateChannel, byteChannel, circuit_norm])]
  simp [InstructionReceipt.channel, stateChannel, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
/-- Computed observation fields commute with evaluation of the original row. -/
theorem eval_next (env : Environment (ZMod p)) (input : Var Inputs (ZMod p)) :
    Eval.eval env input.next = (Eval.eval env input).next := by
  rcases input with ⟨⟨high, low, pc0, pc1, pc2⟩, previous, counter⟩
  simp only [Inputs.next, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
private theorem eval_previous (env : Environment (ZMod p)) (input : Var Inputs (ZMod p)) :
    Eval.eval env input.previous = (Eval.eval env input).previous := by
  rcases input with ⟨receipt, previous, counter⟩
  simp only [circuit_norm]

omit [Fact (2 ^ 25 < p)] in
private theorem eval_receipt (env : Environment (ZMod p)) (input : Var Inputs (ZMod p)) :
    Eval.eval env input.receipt = (Eval.eval env input).receipt := by
  rcases input with ⟨receipt, previous, counter⟩
  simp only [circuit_norm]

/-- The exact receipt is read from the actual component input. -/
theorem receipt_values (enabled : Bool) (env : Environment (ZMod p)) :
    ({ circuit := circuit enabled } : Component (ZMod p)).operations.interactionValuesWith
      InstructionReceipt.channel.toRaw env =
        [InstructionReceipt.channel.pulledValue (valueFromOffset Inputs 0 env).receipt] := by
  simp only [Operations.interactionValuesWith, Component.interactionsWith_eq,
    Component.rowOperations, circuit, main_receipt_interactions, List.map_cons, List.map_nil,
    Channel.eval_pulled, eval_receipt, eval_varFromOffset_valueFromOffset]

/-- The exact transition is read from the same physical input, without a copied witness. -/
theorem state_values (enabled : Bool) (env : Environment (ZMod p)) :
    ({ circuit := circuit enabled } : Component (ZMod p)).operations.interactionValuesWith stateChannel.toRaw env =
      [stateChannel.pulledValue (valueFromOffset Inputs 0 env).previous,
        stateChannel.pushedValue (valueFromOffset Inputs 0 env).next] := by
  simp only [Operations.interactionValuesWith, Component.interactionsWith_eq,
    Component.rowOperations, circuit, main_state_interactions, List.map_cons, List.map_nil,
    Channel.eval_pulled, Channel.eval_pushed, eval_previous, eval_next,
    eval_varFromOffset_valueFromOffset]

/-- Eighteen supplied cells plus 186 generated cells give the exact physical row width. -/
theorem width (enabled : Bool) : ({ circuit := circuit (p := p) enabled } : Component (ZMod p)).width = 204 := by
  cases enabled <;> rfl

end SP1Clean.OrdinaryObservation
