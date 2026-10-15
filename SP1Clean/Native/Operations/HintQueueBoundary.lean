import SP1Clean.Proofs.Operations.HintQueueCursor
import ToClean.Air.VerifierExtension

/-! # Verifier-owned hint queue endpoints

The source token is computed from the complete incoming hint queue, including its allocation
frontier. The final cursor is fixed by the ensemble instance. This circuit anchors exactly one
path when installed in the verifier; it does not identify the final cursor's reachable bytes
with an outgoing snapshot. That semantic binding requires the ordered allocation/head history.
-/

namespace SP1Clean.HostHintQueueBoundary

open Circuit Air.Flat Model.Core Model.Core.HintQueue HostHintQueue

variable {p : ℕ} [Fact p.Prime]

def initial (hints : List Bytes) : State (ZMod p) :=
  State.encode 0 (ofList hints).2 hints.length

def main (hints : List Bytes) (final : State (ZMod p)) (_ : Var unit (ZMod p)) :
    Circuit (ZMod p) Unit := do
  assertZero (.const (if hints.length < 2 ^ 48 then 0 else 1))
  stateChannel.push (const (initial hints))
  stateChannel.pull (const final)

instance elaborated (hints : List Bytes) (final : State (ZMod p)) :
    ElaboratedCircuit (ZMod p) unit unit (main hints final) := by elaborate_circuit

def circuit (hints : List Bytes) (final : State (ZMod p)) :
    GeneralFormalCircuit (ZMod p) unit unit where
  main := main hints final
  elaborated := elaborated hints final
  Spec _ _ _ := hints.length < 2 ^ 48
  ProverAssumptions _ _ _ := hints.length < 2 ^ 48
  channelsWithRequirements := [stateChannel.toRaw]
  soundness := by
    circuit_proof_start [main, stateChannel]
    split_ifs at h_holds with fits
    · exact fits
    · simp at h_holds
  completeness := by
    circuit_proof_start [main, stateChannel]
    simp only [if_pos h_assumptions]

theorem interactions (hints : List Bytes) (final : State (ZMod p)) (offset : ℕ) :
    ((main hints final ()).operations offset).interactionsWith stateChannel.toRaw =
      [(stateChannel.pushed (const (initial hints))).toRaw,
       (stateChannel.pulled (const final)).toRaw] := by simp only [main, circuit_norm]

theorem values (hints : List Bytes) (final : State (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((main hints final ()).operations offset).interactionValuesWith stateChannel.toRaw env =
      [stateChannel.pushedValue (initial hints), stateChannel.pulledValue final] := by
  simp only [Operations.interactionValuesWith, interactions, List.map_cons, List.map_nil,
    Channel.eval_pushed, Channel.eval_pulled, ProvableType.eval_const]

/-- Static raw-operation laws, including every channel, justify the singleton adapter. -/
def closed (hints : List Bytes) (final : State (ZMod p)) : ClosedVerifier (ZMod p) where
  name := "host-hint-queue"
  circuit := circuit hints final
  assumptions := by intros; trivial
  lookups := by simp only [circuit, main, circuit_norm]
  public_interactions := by
    intro interaction member env
    simp only [circuit, main, circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;>
      simp [circuit_norm, ChannelInteraction.toRaw, AbstractInteraction.Guarantees,
        AbstractInteraction.Requirements, Channel.toRaw, Expression.eval]

  length_zero := rfl
  constraints := by intros; simp only [circuit, main, circuit_norm]
  interactions := by
    intro offset env channel
    by_cases same : channel = stateChannel.toRaw
    · subst channel
      exact (values hints final offset env).trans (values hints final 0 _).symm
    · simp only [circuit, main, Operations.interactionValuesWith, Operations.interactionsWith,
        circuit_norm, List.filter_cons, List.filter_nil, ChannelInteraction.toRaw,
        Ne.symm same, decide_false,
        Bool.false_eq_true, ↓reduceIte, List.map_nil]

theorem initial_binds [Fact (2 ^ 17 < p)] (hints : List Bytes) (fits : hints.length < 2 ^ 48) :
    (initial (p := p) hints).Binds (ofList hints).1 hints := State.source_binds 0 hints fits

end SP1Clean.HostHintQueueBoundary
