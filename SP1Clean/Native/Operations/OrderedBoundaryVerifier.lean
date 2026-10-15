import SP1Clean.Native.Operations.OrderedBoundary
import ToClean.Circuit.VerifierInteractions

/-! # Fixed endpoints for an ordered inventory

The verifier contributes exactly one initial push and one final pull. Both messages are
circuit constants, so neither the public input nor the witness can select the endpoints.
It has no witness cells and composes into an ensemble's verifier.
-/

namespace SP1Clean.OrderedBoundaryVerifier

open Circuit OrderedBoundary

variable {p : ℕ} [Fact p.Prime]

def main (name : String) (initial final : Word (ZMod p)) (_ : Var unit (ZMod p)) :
    Circuit (ZMod p) Unit := do
  (channel name).push (const initial)
  (channel name).pull (const final)

def circuit (name : String) (initial final : Word (ZMod p)) :
    GeneralFormalCircuit (ZMod p) unit unit where
  main := main name initial final
  Spec _ _ _ := True
  ProverAssumptions _ _ _ := True
  soundness := by circuit_proof_start [channel]
  completeness := by circuit_proof_start [channel]

@[circuit_norm] theorem circuit_localLength (name : String) (initial final : Word (ZMod p))
    (input : Var unit (ZMod p)) :
    (circuit name initial final).localLength input = 0 := rfl

theorem main_interactions (name : String) (initial final : Word (ZMod p))
    (input : Var unit (ZMod p)) (offset : ℕ) :
    ((main name initial final input).operations offset).interactionsWith (channel name).toRaw =
      [((channel name).pushed (const initial)).toRaw,
       ((channel name).pulled (const final)).toRaw] := by
  simp only [main, circuit_norm]

theorem interactionValues (name : String) (initial final : Word (ZMod p))
    (input : Var unit (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((main name initial final input).operations offset).interactionValuesWith (channel name).toRaw env =
      [(channel name).pushedValue initial, (channel name).pulledValue final] := by
  simp only [Operations.interactionValuesWith, main_interactions, List.map_cons, List.map_nil,
    Channel.eval_pushed, Channel.eval_pulled, ProvableType.eval_const]

/-- The fixed endpoints are public verifier traffic, with no committed table. -/
def verifierProgram (name : String) (initial final : Word (ZMod p)) :
    Verifier.Program (ZMod p) unit where
  main _ := Verifier.ofInteractions ((main name initial final ()).operations 0).interactions (by
    intro interaction member env
    simp only [main, circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;>
      simp [AbstractInteraction.Requirements, AbstractInteraction.Guarantees,
        ChannelInteraction.toRaw, channel, Channel.toRaw, circuit_norm])

end SP1Clean.OrderedBoundaryVerifier
