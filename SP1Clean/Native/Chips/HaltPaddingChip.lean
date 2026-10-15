import SP1Clean.Proofs.Chips.HaltChip.Formal
import ToClean.Circuit.SubcircuitProjection
import ToClean.Air.EnsembleProjection

/-! # Legacy Exit padding in the mixed host assembly

Active HALT uses the full syscall instruction and host handler. Until the old public Exit
participation rule is replaced, this component retains only the legacy table's padding rows.
The wrapper preserves every old interaction and adds one zero-selector constraint.
-/

namespace SP1Clean.HaltPaddingChip

open Circuit Air.Flat

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def main (input : Var HaltChip.Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let _ ← HaltChip.circuit input
  assertZero input.is_real

instance elaborated : ElaboratedCircuit (ZMod p) HaltChip.Inputs unit main := by
  elaborate_circuit

def circuit : GeneralFormalCircuit (ZMod p) HaltChip.Inputs unit where
  name := (HaltChip.circuit (p := p)).name
  main
  elaborated
  Spec input _ _ := HaltChip.Spec input ∧ input.is_real = 0
  ProverAssumptions input _ _ := HaltChip.Spec input ∧ input.is_real = 0
  channelsWithRequirements := HaltChip.circuit.channelsWithRequirements
  soundness := by circuit_proof_all [main]
  completeness := by circuit_proof_all [main, HaltChip.circuit]

def original : Component (ZMod p) := { circuit := HaltChip.circuit }
def component : Component (ZMod p) := { circuit := circuit }

private theorem main_interactions (input : Var HaltChip.Inputs (ZMod p)) (offset : ℕ)
    (selected : RawChannel (ZMod p)) :
    ((main input).operations offset).interactionsWith selected =
      ((HaltChip.main input).operations offset).interactionsWith selected := by
  simp only [main, Operations.interactionsWith, circuit_norm,
    GeneralFormalCircuit.toSubcircuit_interactions, HaltChip.circuit]

theorem interactions (selected : RawChannel (ZMod p)) :
    component.operations.interactionsWith selected = original.operations.interactionsWith selected := by
  simp only [component, original, Component.interactionsWith_eq]
  exact main_interactions _ _ selected

private theorem main_constraints (input : Var HaltChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p)) :
    ((main input).operations offset).ConstraintsHold env ↔
      ((HaltChip.main input).operations offset).ConstraintsHold env ∧
        Expression.eval env input.is_real = 0 := by
  simp only [main, circuit_norm, HaltChip.circuit,
    or_imp, forall_and, forall_eq]
  tauto

omit [Fact (2 ^ 17 < p)] in
private theorem eval_gate (input : Var HaltChip.Inputs (ZMod p)) (env : Environment (ZMod p)) :
    Expression.eval env input.is_real = (eval env input).is_real := by
  cases input
  simp only [circuit_norm]

theorem constraints (env : Environment (ZMod p)) :
    component.operations.ConstraintsHold env ↔ original.operations.ConstraintsHold env ∧
      (original.rowInput env).is_real = 0 := by
  simp only [component, original, Component.constraintsHold_iff]
  change ((main (varFromOffset HaltChip.Inputs 0)).operations (size HaltChip.Inputs)).ConstraintsHold env ↔
    ((HaltChip.main (varFromOffset HaltChip.Inputs 0)).operations (size HaltChip.Inputs)).ConstraintsHold env ∧
      (valueFromOffset HaltChip.Inputs 0 env).is_real = 0
  rw [main_constraints, eval_gate, eval_varFromOffset_valueFromOffset]

end SP1Clean.HaltPaddingChip
