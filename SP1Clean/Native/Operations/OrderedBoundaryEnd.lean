import SP1Clean.Native.Operations.OrderedBoundary

/-! # Closing an ordered boundary inventory

The final key is fixed in the circuit. One terminal row connects the last occupied key to it;
the same construction accepts an empty inventory by connecting the start directly to the end.
Multiplicity and uniqueness of this terminal row are consequences of global control balance.
-/

namespace SP1Clean.OrderedBoundaryEnd

open Circuit OrderedBoundary

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def main (name : String) (final : Word (ZMod p))
    (input : Var TerminalInputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let _ ← OrderedBoundary.circuit name ⟨input.previous, const final, input.comparison⟩

def circuit (name : String) (final : Word (ZMod p)) :
    GeneralFormalCircuit (ZMod p) TerminalInputs unit where
  name := s!"sp1.native.{name}.terminal"
  main := main name final
  Spec input _ _ := TerminalSpec final input
  ProverAssumptions input _ _ :=
    OrderedBoundary.ProverAssumptions ⟨input.previous, final, input.comparison⟩
  channelsWithRequirements := [(channel name).toRaw]
  soundness := by
    circuit_proof_start [OrderedBoundary.circuit]
    have finalEq : Vector.map (Expression.eval env) (Vector.map Expression.const final) = final := by
      simp only [Vector.map_map, Function.comp_def, Expression.eval]
      exact Vector.map_id _
    rw [finalEq] at h_holds
    exact ⟨h_holds.1, h_holds.2.2⟩
  completeness := by
    circuit_proof_start [OrderedBoundary.circuit]
    have finalEq : Vector.map (Expression.eval env.toEnvironment) (Vector.map Expression.const final) = final := by
      simp only [Vector.map_map, Function.comp_def, Expression.eval]
      exact Vector.map_id _
    rw [finalEq]
    exact h_assumptions

def populate (previous final : Word (ZMod p)) : TerminalInputs (ZMod p) :=
  ⟨previous, LtOperationUnsigned.populate previous final⟩

theorem populate_assumptions (name : String) (previous final : Word (ZMod p))
    (previousBound : Word.isU64 previous) (finalBound : Word.isU64 final)
    (increases : Word.toNat previous < Word.toNat final)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (circuit name final).ProverAssumptions (populate previous final) data hint :=
  OrderedBoundary.populate_assumptions previous final previousBound finalBound increases

theorem main_interactions (name : String) (distinct : name ≠ "SP1Byte") (final : Word (ZMod p))
    (input : Var TerminalInputs (ZMod p)) (offset : ℕ) :
    ((main name final input).operations offset).interactionsWith (channel name).toRaw =
      [((channel name).pulled input.previous).toRaw, ((channel name).pushed (const final)).toRaw] := by
  have pair (args : Var OrderedBoundary.Inputs (ZMod p)) (n : ℕ) :=
    OrderedBoundary.main_interactions name distinct args n
  simp only [Operations.interactionsWith] at pair
  simp only [main, circuit_norm, GeneralFormalCircuit.toSubcircuit_interactions,
    OrderedBoundary.circuit, pair]

theorem interactionValues (name : String) (distinct : name ≠ "SP1Byte") (final : Word (ZMod p))
    (input : Var TerminalInputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((main name final input).operations offset).interactionValuesWith (channel name).toRaw env =
      [(channel name).pulledValue (Eval.eval env input.previous), (channel name).pushedValue final] := by
  simp only [Operations.interactionValuesWith, main_interactions name distinct, List.map_cons,
    List.map_nil, Channel.eval_pulled, Channel.eval_pushed, ProvableType.eval_const]

/-- Closing an ordered inventory adds no lookup operations. -/
@[circuit_norm] theorem main_lookups (name : String) (final : Word (ZMod p))
    (input : Var TerminalInputs (ZMod p)) (offset : ℕ) :
    ((main name final input).operations offset).lookups = [] := by
  simp [main, OrderedBoundary.circuit, circuit_norm]

end SP1Clean.OrderedBoundaryEnd
