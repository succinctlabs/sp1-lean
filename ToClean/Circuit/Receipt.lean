module

public import Clean.Air.FlatComponent
public import ToClean.Circuit.SubcircuitProjection
public import ToClean.Circuit.InteractionRecovery

/-! # Gated receipts from an existing circuit row

Clean has no wrapper publishing an additional typed observation of a circuit's existing cells.
This addition composes the original formal circuit and retains its name, contract, witness
generation, assertions and lookups. The receipt channel has trivial local meaning: its global consumer must
authenticate the observation through the proved exact ledger. SP1's ordinary State receipts use
this to retain the original instruction decoder and whole-chip proof boundary.
-/

@[expose] public section

namespace Circuit.Receipt

open Air.Flat

variable {F : Type} [FiniteField F]
  {Input Output Message : TypeMap} [ProvableType Input] [ProvableType Output] [ProvableType Message]

/-- Symbolic observations of existing cells, with the original circuit's starting offset.
No witness cells or runtime choice are introduced by this projection. -/
structure Projection (F : Type) (Input Message : TypeMap) where
  /-- The original activity expression. -/
  gate : Input (Expression F) → ℕ → Expression F
  /-- Payload expressions in the original physical row. -/
  message : Input (Expression F) → ℕ → Message (Expression F)

/-- Compose the original circuit, then publish the specified observation. -/
def main (provider : GeneralFormalCircuit F Input Output) (channel : Channel F Message)
    (projection : Projection F Input Message) (input : Var Input F) : Circuit F (Var Output F) :=
  fun offset => (do
    let output ← provider input
    channel.pushIf (projection.gate input offset) (projection.message input offset)
    return output) offset

attribute [local circuit_norm] List.subset_append_left

/-- Offset-aware projection does not change the provider's elaborated witness layout. -/
instance elaborated (provider : GeneralFormalCircuit F Input Output) (channel : Channel F Message)
    (projection : Projection F Input Message) :
    ElaboratedCircuit F Input Output (main provider channel projection) where
  localLength := provider.localLength
  localLength_eq := by
    preserve_tactic_target
    intros
    simp only [main, circuit_norm]
  output := provider.output
  output_eq := by
    preserve_tactic_target
    intros
    simp only [main, circuit_norm]
  subcircuitsConsistent := by
    preserve_tactic_target
    intros
    simp only [main, circuit_norm]
  channelsWithGuarantees := provider.channelsWithGuarantees
  channelsLawful := by
    preserve_tactic_target
    intro input offset
    simp only [main, circuit_norm]

/-- The receipt leaves the provider's local semantic and prover contracts unchanged. -/
def circuit (provider : GeneralFormalCircuit F Input Output) (channel : Channel F Message)
    (trivial : ∀ message data, channel.Guarantees message data)
    (projection : Projection F Input Message) : GeneralFormalCircuit F Input Output where
  name := provider.name
  main := main provider channel projection
  elaborated := elaborated provider channel projection
  Assumptions := provider.Assumptions
  Spec := provider.Spec
  ProverAssumptions := provider.ProverAssumptions
  ProverSpec := provider.ProverSpec
  channelsWithRequirements := provider.channelsWithRequirements ++ [channel.toRaw]
  soundness := by
    circuit_proof_start [main]
    exact ⟨h_holds h_assumptions, Or.inr h_assumptions, fun _ _ => trivial _ _⟩
  completeness := by
    circuit_proof_start [main]
    exact ⟨h_assumptions, (h_env h_assumptions).2⟩

variable (provider : GeneralFormalCircuit F Input Output) (channel : Channel F Message)
  (trivial : ∀ message data, channel.Guarantees message data) (projection : Projection F Input Message)

/-- Publishing a receipt does not widen the original row. -/
theorem width : ({ circuit := circuit provider channel trivial projection } : Component F).width =
    ({ circuit := provider } : Component F).width := rfl

/-- The complete original assertion list is retained literally. -/
theorem constraints : ({ circuit := circuit provider channel trivial projection } : Component F).operations.constraints =
    ({ circuit := provider } : Component F).operations.constraints := by
  simp only [Component.constraints_eq, Component.rowOperations, circuit, main, circuit_norm]

/-- Every original lookup is retained literally. -/
theorem lookups : ({ circuit := circuit provider channel trivial projection } : Component F).operations.lookups =
    ({ circuit := provider } : Component F).operations.lookups := by
  simp only [Component.lookups_eq, Component.rowOperations, circuit, main, circuit_norm]

/-- The only added interaction is the gated observation of the original cells. -/
theorem receipt_interactions (input : Var Input F) (offset : ℕ) :
    (((circuit provider channel trivial projection).main input).operations offset).interactionsWith channel.toRaw =
      ((provider.main input).operations offset).interactionsWith channel.toRaw ++
        [(channel.pushedIf (projection.gate input offset) (projection.message input offset)).toRaw] := by
  simp only [circuit, main, circuit_norm, GeneralFormalCircuit.toSubcircuit_interactions]
  rfl

/-- All occurrences on every other channel are unchanged, including disabled occurrences. -/
theorem interactions (selected : RawChannel F) (different : selected ≠ channel.toRaw) :
    ({ circuit := circuit provider channel trivial projection } : Component F).operations.interactionsWith selected =
      ({ circuit := provider } : Component F).operations.interactionsWith selected := by
  simp only [Component.interactionsWith_eq, Component.rowOperations, circuit, main, circuit_norm,
    GeneralFormalCircuit.toSubcircuit_interactions, Ne.symm different, ↓reduceIte, List.append_nil]
  rfl

/-- A fresh channel receives exactly the observation evaluated in the original physical row. -/
theorem row_receipt (silent : channel.toRaw ∉ provider.channels) (env : Environment F) :
    ({ circuit := circuit provider channel trivial projection } : Component F).operations.interactionValuesWith
      channel.toRaw env =
        [channel.pushedIfValue (Eval.eval env (projection.gate (varFromOffset Input 0) (size Input)))
          (Eval.eval env (projection.message (varFromOffset Input 0) (size Input)))] := by
  simp only [Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations]
  rw [receipt_interactions, InteractionRecovery.interactionsWith_main_eq_nil provider.base _ _ _ silent]
  simp only [List.nil_append, List.map_cons, List.map_nil, Channel.eval_pushedIf]

end Circuit.Receipt
