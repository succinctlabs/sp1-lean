import SP1Clean.FormalModel.Contracts.FinalMemoryChange
import Clean.Gadgets.Boolean
import ToClean.Circuit.InteractionRecovery

/-! # Boolean selection of a validated final location

This operation is composed inside target-value checkers, with the same complete record. It
publishes one tagged key when selected and retains the disabled physical interaction otherwise.
-/

namespace SP1Clean.FinalMemoryChange

open Circuit Channels

variable {p : ℕ} [Fact p.Prime]

/-- Check Boolean selection and publish this record's tagged key. -/
def main (ram : Bool) (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertBool input.selected
  channel.pushIf input.selected (key ram input.record)

instance elaborated (ram : Bool) : ElaboratedCircuit (ZMod p) Inputs unit (main ram) := by
  elaborate_circuit

/-- Proof-complete selection subcircuit; record authentication belongs to its caller. -/
def circuit (ram : Bool) : GeneralFormalCircuit (ZMod p) Inputs unit where
  main := main ram
  elaborated := elaborated ram
  Spec input _ _ := Spec input
  ProverAssumptions input _ _ := Spec input
  channelsWithRequirements := [channel.toRaw]
  soundness := by circuit_proof_start [channel]; exact h_holds
  completeness := by circuit_proof_start [channel]; exact h_assumptions

theorem eval_key (ram : Bool) (record : Var MemoryMsg (ZMod p)) (env : Environment (ZMod p)) :
    eval env (key ram record) = key ram (eval env record) := by
  cases ram <;> simp only [key, MemoryBoundary.address, circuit_norm]

theorem values (ram : Bool) (input : Var Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((main ram input).operations offset).interactionValuesWith channel.toRaw env =
      [channel.pushedIfValue (eval env input.selected) (key ram (eval env input.record))] := by
  have raw : ((main ram input).operations offset).interactionsWith channel.toRaw =
      [(channel.pushedIf input.selected (key ram input.record)).toRaw] := by
    have empty := InteractionRecovery.filter_interactions_formalAssertion_eq_nil
      (assertBool (p := p)) channel.toRaw input.selected (by simp [circuit_norm])
      (by simp [circuit_norm]) (n := offset)
    simpa only [main, circuit_norm, List.nil_append] using
      congrArg (fun entries => entries ++ [(channel.pushedIf input.selected (key ram input.record)).toRaw]) empty
  simp only [Operations.interactionValuesWith, raw, List.map_cons, List.map_nil,
    Channel.eval_pushedIf, eval_key]

end SP1Clean.FinalMemoryChange
