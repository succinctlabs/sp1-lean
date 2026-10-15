import SP1Clean.Proofs.Chips.HostHintLengthChip.Formal
import SP1Clean.Native.Operations.HintQueueSource
import ToClean.Circuit.InteractionRecovery
import ToClean.Air.ChannelClosure

/-! # HINT_LEN and source nodes on the physical Clean ledger

The handler consumes one complete instruction call, replaces the current queue state, and
consumes one node precisely in the nonempty case. The fixed source provider authenticates its
node from raw lookup constraints. Head chronology and authorization of later allocations remain
responsibilities of the enclosing assembly.
-/

namespace SP1Clean

open Circuit Air.Flat HostHintQueue
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

namespace HostHintLengthChip

omit [Fact (2 ^ 25 < p)] in
private theorem equality_empty (k : ℕ) (target : RawChannel (ZMod p))
    (input : Var (ProvablePair (fields k) (fields k)) (ZMod p)) (offset : ℕ) :
    (FlatOperation.interactions ((Gadgets.Equality.circuit (fields k)).toSubcircuit offset input).ops.toFlat).filter
      (fun (i : AbstractInteraction (ZMod p)) => decide (i.channel = target)) = [] :=
  InteractionRecovery.filter_interactions_formalAssertion_eq_nil
    (Gadgets.Equality.circuit (fields k)) target input List.not_mem_nil List.not_mem_nil

private theorem main_filtered (empty : Bool) (input : Var Inputs (ZMod p)) (offset : ℕ)
    (target : RawChannel (ZMod p)) :
    ((main empty input).operations offset).interactionsWith target =
      ((if empty then [] else [(nodeChannel.pulled input.node).toRaw]) ++
        [(HostCallChip.channel.pulled input.call).toRaw,
         (stateChannel.pulled input.previous).toRaw,
         (stateChannel.pushed input.next).toRaw]).filter (fun i => decide (i.channel = target)) := by
  have clockEmpty (n : ℕ) := InteractionRecovery.interactionsWith_main_eq_nil
    ClockOrder.circuit.base target input.clock n (by simp [ClockOrder.circuit, circuit_norm])
  cases empty <;> simp only [main, circuit_norm, List.nil_append]
  all_goals
    simp only [Operations.interactionsWith] at clockEmpty ⊢
    simp only [GeneralFormalCircuit.toSubcircuit_interactions, clockEmpty,
      equality_empty, List.nil_append]
    simp [circuit_norm, List.filter_cons]

theorem main_host_interactions (empty : Bool) (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main empty input).operations offset).interactionsWith HostCallChip.channel.toRaw =
      [(HostCallChip.channel.pulled input.call).toRaw] := by
  rw [main_filtered]
  cases empty <;> simp [HostCallChip.channel, stateChannel, nodeChannel, circuit_norm]

theorem main_state_interactions (empty : Bool) (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main empty input).operations offset).interactionsWith stateChannel.toRaw =
      [(stateChannel.pulled input.previous).toRaw, (stateChannel.pushed input.next).toRaw] := by
  rw [main_filtered]
  cases empty <;> simp [HostCallChip.channel, stateChannel, nodeChannel, circuit_norm]

theorem main_node_interactions (empty : Bool) (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main empty input).operations offset).interactionsWith nodeChannel.toRaw =
      if empty then [] else [(nodeChannel.pulled input.node).toRaw] := by
  rw [main_filtered]
  cases empty <;> simp [HostCallChip.channel, stateChannel, nodeChannel, circuit_norm]

theorem main_other_interactions (empty : Bool) (input : Var Inputs (ZMod p)) (offset : ℕ)
    (target : RawChannel (ZMod p)) (notHost : target ≠ HostCallChip.channel.toRaw)
    (notState : target ≠ stateChannel.toRaw) (notNode : target ≠ nodeChannel.toRaw) :
    ((main empty input).operations offset).interactionsWith target = [] := by
  apply InteractionRecovery.interactionsWith_main_eq_nil (circuit empty).base target input offset
  cases empty <;> simp [circuit, circuit_norm, notHost, notState, notNode]

theorem host_values (empty : Bool) (input : Var Inputs (ZMod p))
    (offset : ℕ) (env : Environment (ZMod p)) :
    ((main empty input).operations offset).interactionValuesWith HostCallChip.channel.toRaw env =
      [HostCallChip.channel.pulledValue (Eval.eval env input.call)] := by
  simp only [Operations.interactionValuesWith, main_host_interactions,
    List.map_cons, List.map_nil, Channel.eval_pulled]

theorem state_values (empty : Bool) (input : Var Inputs (ZMod p))
    (offset : ℕ) (env : Environment (ZMod p)) :
    ((main empty input).operations offset).interactionValuesWith stateChannel.toRaw env =
      [stateChannel.pulledValue (Eval.eval env input.previous),
       stateChannel.pushedValue (Eval.eval env input.next)] := by
  simp only [Operations.interactionValuesWith, main_state_interactions,
    List.map_cons, List.map_nil, Channel.eval_pulled, Channel.eval_pushed]

theorem node_values (empty : Bool) (input : Var Inputs (ZMod p))
    (offset : ℕ) (env : Environment (ZMod p)) :
    ((main empty input).operations offset).interactionValuesWith nodeChannel.toRaw env =
      if empty then [] else [nodeChannel.pulledValue (Eval.eval env input.node)] := by
  cases empty <;> simp only [Operations.interactionValuesWith, main_node_interactions,
    Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, Channel.eval_pulled]

theorem component_spec_of_node (empty : Bool) (env : Environment (ZMod p))
    (constraints : ({ circuit := circuit empty } : Component (ZMod p)).operations.ConstraintsHold env)
    (node : ({ circuit := circuit empty } : Component (ZMod p)).operations.ChannelGuarantees nodeChannel.toRaw env) :
    ({ circuit := circuit empty } : Component (ZMod p)).Spec env := by
  apply (Component.weakSoundness (by trivial) constraints ?_).1
  rw [Operations.guarantees_iff _ _ _ (({ circuit := circuit empty } : Component (ZMod p)).inChannelsOrGuarantees env)]
  intro selected member
  cases empty
  · change selected ∈ [nodeChannel.toRaw, HostCallChip.channel.toRaw, stateChannel.toRaw] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact node
    · exact Operations.channelGuarantees_of_trivial _ (by simp [HostCallChip.channel, Channel.toRaw]) _ _
    · exact Operations.channelGuarantees_of_trivial _ (by simp [stateChannel, Channel.toRaw]) _ _
  · change selected ∈ [HostCallChip.channel.toRaw, stateChannel.toRaw] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact Operations.channelGuarantees_of_trivial _ (by simp [HostCallChip.channel, Channel.toRaw]) _ _
    · exact Operations.channelGuarantees_of_trivial _ (by simp [stateChannel, Channel.toRaw]) _ _

end HostHintLengthChip

namespace HostHintQueue

omit [Fact (2 ^ 25 < p)] in
theorem source_node_interactions (hints : List Model.Core.Bytes)
    (input : Var Model.Core.HintQueue.NodeRecord (ZMod p)) (offset : ℕ) :
    ((sourceMain hints input).operations offset).interactionsWith nodeChannel.toRaw =
      [(nodeChannel.pushed input).toRaw] := by
  simp [sourceMain, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
theorem source_node_values (hints : List Model.Core.Bytes)
    (input : Var Model.Core.HintQueue.NodeRecord (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((sourceMain hints input).operations offset).interactionValuesWith nodeChannel.toRaw env =
      [nodeChannel.pushedValue (Eval.eval env input)] := by
  simp only [Operations.interactionValuesWith, source_node_interactions,
    List.map_cons, List.map_nil, Channel.eval_pushed]

theorem source_other_interactions (hints : List Model.Core.Bytes)
    (input : Var Model.Core.HintQueue.NodeRecord (ZMod p)) (offset : ℕ)
    (target : RawChannel (ZMod p)) (different : target ≠ nodeChannel.toRaw) :
    ((sourceMain hints input).operations offset).interactionsWith target = [] := by
  apply InteractionRecovery.interactionsWith_main_eq_nil (source hints).base target input offset
  simpa [source, circuit_norm] using different

/-- Lookup constraints authenticate the actual source bytes without any node-channel premise. -/
theorem source_spec_of_constraints (hints : List Model.Core.Bytes) (env : Environment (ZMod p))
    (constraints : ({ circuit := source hints } : Component (ZMod p)).operations.ConstraintsHold env) :
    ({ circuit := source hints } : Component (ZMod p)).Spec env := by
  apply (Component.weakSoundness (by trivial) constraints ?_).1
  rw [Operations.guarantees_iff _ _ _ (({ circuit := source hints } : Component (ZMod p)).inChannelsOrGuarantees env)]
  intro selected member
  change selected ∈ [] at member
  exact False.elim (List.not_mem_nil member)

end HostHintQueue
end SP1Clean
