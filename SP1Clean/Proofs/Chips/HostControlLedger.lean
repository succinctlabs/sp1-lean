import SP1Clean.Proofs.Chips.HostHaltChip.Formal
import SP1Clean.Proofs.Chips.HostEnterChip.Formal
import ToClean.Circuit.InteractionRecovery
import ToClean.Air.ChannelClosure

/-! # The physical ledgers of native control handlers

Each handler consumes exactly one full HostCall message. HALT additionally uses Byte checks;
neither handler emits Memory, State, Exit, or PublicValues records. Local semantic contracts
follow from raw constraints and, for HALT, the enclosing ensemble's Byte guarantees.
-/

namespace SP1Clean

open Circuit Channels Air.Flat
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
private theorem control_equality_empty (target : RawChannel (ZMod p))
    (input : Var (ProvablePair Word Word) (ZMod p)) (offset : ℕ) :
    (FlatOperation.interactions ((Gadgets.Equality.circuit Word).toSubcircuit offset input).ops.toFlat).filter
      (fun (i : AbstractInteraction (ZMod p)) => decide (i.channel = target)) = [] :=
  InteractionRecovery.filter_interactions_formalAssertion_eq_nil
    (Gadgets.Equality.circuit Word) target input List.not_mem_nil List.not_mem_nil

namespace HostHaltChip

theorem main_host_interactions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith HostCallChip.channel.toRaw =
      [(HostCallChip.channel.pulled input.call).toRaw] := by
  have bounded := InteractionRecovery.interactionsWith_main_eq_nil
    (BoundedWord.circuit (bound p) bound_fits).base HostCallChip.channel.toRaw
    ⟨input.call.arg1, input.comparison⟩ offset
    (by simp [BoundedWord.circuit, circuit_norm, HostCallChip.channel, byteChannel])
  simp only [main, circuit_norm, List.nil_append]
  simp only [Operations.interactionsWith, Circuit.operations] at bounded ⊢
  simp only [GeneralFormalCircuit.toSubcircuit_interactions,
    control_equality_empty, List.nil_append]
  simpa [circuit_norm, HostExitBoundary.channel, HostCallChip.channel, Channel.toRaw] using bounded

theorem host_values (input : Var Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((main input).operations offset).interactionValuesWith HostCallChip.channel.toRaw env =
      [HostCallChip.channel.pulledValue (Eval.eval env input.call)] := by
  simp only [Operations.interactionValuesWith, main_host_interactions,
    List.map_cons, List.map_nil, Channel.eval_pulled]

/-- In particular, the handler cannot supply another Exit or alter the instruction Memory ledger. -/
theorem main_other_interactions (target : RawChannel (ZMod p))
    (notByte : target ≠ byteChannel.toRaw) (notHost : target ≠ HostCallChip.channel.toRaw)
    (notExit : target ≠ HostExitBoundary.channel.toRaw)
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith target = [] := by
  apply InteractionRecovery.interactionsWith_main_eq_nil circuit.base target input offset
  simp [circuit, circuit_norm, notByte, notHost, notExit]

theorem component_spec_of_byte (env : Environment (ZMod p))
    (constraints : ({ circuit := circuit } : Component (ZMod p)).operations.ConstraintsHold env)
    (byte : ({ circuit := circuit } : Component (ZMod p)).operations.ChannelGuarantees byteChannel.toRaw env) :
    ({ circuit := circuit } : Component (ZMod p)).Spec env := by
  apply (Component.weakSoundness (by trivial) constraints ?_).1
  rw [Operations.guarantees_iff _ _ _ (({ circuit := circuit } : Component (ZMod p)).inChannelsOrGuarantees env)]
  intro selected member
  change selected ∈ [byteChannel.toRaw, HostCallChip.channel.toRaw] at member
  rcases List.mem_cons.mp member with rfl | member
  · exact byte
  · obtain rfl := List.mem_singleton.mp member
    exact Operations.channelGuarantees_of_trivial _ (by simp [HostCallChip.channel, Channel.toRaw]) _ _

/-- The checked host handler emits exactly one complete terminal receipt. -/
theorem terminal_values (input : Var Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((main input).operations offset).interactionValuesWith HostExitBoundary.channel.toRaw env =
      [HostExitBoundary.channel.pushedValue (Eval.eval env input.call.arg1)] := by
  have bounded := InteractionRecovery.interactionsWith_main_eq_nil
    (BoundedWord.circuit (bound p) bound_fits).base HostExitBoundary.channel.toRaw
    ⟨input.call.arg1, input.comparison⟩ offset
    (by simp [BoundedWord.circuit, circuit_norm, HostExitBoundary.channel, byteChannel])
  have raw : ((main input).operations offset).interactionsWith HostExitBoundary.channel.toRaw =
      [(HostExitBoundary.channel.pushed input.call.arg1).toRaw] := by
    simp only [main, circuit_norm, List.nil_append]
    simp only [Operations.interactionsWith, Circuit.operations] at bounded ⊢
    simp only [GeneralFormalCircuit.toSubcircuit_interactions,
      control_equality_empty, List.nil_append]
    simpa [circuit_norm, HostExitBoundary.channel, HostCallChip.channel, Channel.toRaw] using bounded
  simp only [Operations.interactionValuesWith, raw, List.map_cons, List.map_nil, Channel.eval_pushed]

end HostHaltChip

namespace HostEnterChip

omit [Fact (2 ^ 17 < p)] in
theorem main_host_interactions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith HostCallChip.channel.toRaw =
      [(HostCallChip.channel.pulled input).toRaw] := by
  simp only [main, circuit_norm, control_equality_empty, List.nil_append]

omit [Fact (2 ^ 17 < p)] in
theorem host_values (input : Var Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((main input).operations offset).interactionValuesWith HostCallChip.channel.toRaw env =
      [HostCallChip.channel.pulledValue (Eval.eval env input)] := by
  simp only [Operations.interactionValuesWith, main_host_interactions,
    List.map_cons, List.map_nil, Channel.eval_pulled]

omit [Fact (2 ^ 17 < p)] in
theorem main_other_interactions (target : RawChannel (ZMod p))
    (notHost : target ≠ HostCallChip.channel.toRaw) (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith target = [] := by
  apply InteractionRecovery.interactionsWith_main_eq_nil circuit.base target input offset
  simp [circuit, circuit_norm, notHost]

omit [Fact (2 ^ 17 < p)] in
theorem component_spec_of_constraints (env : Environment (ZMod p))
    (constraints : ({ circuit := circuit } : Component (ZMod p)).operations.ConstraintsHold env) :
    ({ circuit := circuit } : Component (ZMod p)).Spec env := by
  apply (Component.weakSoundness (by trivial) constraints ?_).1
  rw [Operations.guarantees_iff _ _ _ (({ circuit := circuit } : Component (ZMod p)).inChannelsOrGuarantees env)]
  intro selected member
  change selected ∈ [HostCallChip.channel.toRaw] at member
  obtain rfl := List.mem_singleton.mp member
  exact Operations.channelGuarantees_of_trivial _ (by simp [HostCallChip.channel, Channel.toRaw]) _ _

end HostEnterChip
end SP1Clean
