import SP1Clean.Native.Operations.HostCommitBoundary
import ToClean.Air.VerifierExtension
import ToClean.Circuit.SubcircuitProjection

/-! # Verifier-owned local commitment-bank endpoints

Both banks' incoming and outgoing words are fixed by the enclosing statement. This zero-input
wrapper invokes the existing bank verifier once; its singleton representation retains exactly
those two interactions. The bank terminal remains a physical table with a private last timestamp.
-/

namespace SP1Clean.HostCommitEndpoint

open Circuit Air.Flat HostCommitChip
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

def main (deferred : Bool) (source target : Vector (Word (ZMod p)) 8)
    (_ : Var unit (ZMod p)) : Circuit (ZMod p) Unit := do
  let _ ← HostCommitBoundary.verifier deferred source (const (M := ProvableVector Word 8) target)
  pure ()

def circuit (deferred : Bool) (source target : Vector (Word (ZMod p)) 8) :
    GeneralFormalCircuit (ZMod p) unit unit where
  main := main deferred source target
  Spec _ _ _ := True
  ProverAssumptions _ _ _ := True
  channelsWithRequirements := [(stateChannel deferred).toRaw]
  soundness := by circuit_proof_start [main]; exact Or.inr trivial
  completeness := by circuit_proof_start [main]; trivial

omit [Fact (2 ^ 25 < p)] in
private theorem unfolded (deferred : Bool) (source target : Vector (Word (ZMod p)) 8)
    (offset : ℕ) (env : Environment (ZMod p)) (channel : RawChannel (ZMod p)) :
    ((main deferred source target ()).operations offset).interactionValuesWith channel env =
      Operations.interactionValuesWith channel
        ((HostCommitBoundary.verifierMain deferred source (const (M := ProvableVector Word 8) target)).operations offset)
        env := by
  simp only [main, Operations.interactionValuesWith, Operations.interactionsWith, circuit_norm,
    GeneralFormalCircuit.toSubcircuit_interactions, HostCommitBoundary.verifier]

omit [Fact (2 ^ 25 < p)] in
theorem values (deferred : Bool) (source target : Vector (Word (ZMod p)) 8)
    (offset : ℕ) (env : Environment (ZMod p)) (channel : RawChannel (ZMod p)) :
    ((main deferred source target ()).operations offset).interactionValuesWith channel env =
      if channel = (stateChannel deferred).toRaw then
        [(stateChannel deferred).pushedValue (HostCommitBoundary.start source),
         (stateChannel deferred).pulledValue (HostCommitBoundary.final target)] else [] := by
  by_cases same : channel = (stateChannel deferred).toRaw
  · subst channel
    rw [unfolded, HostCommitBoundary.verifier_values]
    simp only [ProvableType.eval_const, ↓reduceIte]
  · rw [unfolded]
    simp only [HostCommitBoundary.verifierMain,
      Operations.interactionValuesWith, Operations.interactionsWith, circuit_norm,
      ChannelInteraction.toRaw, List.filter_cons, List.filter_nil, Ne.symm same, decide_false,
      Bool.false_eq_true, ↓reduceIte, List.map_nil, if_neg same]

/-- The verifier extension cannot depend on witness-selected offsets or ambient row cells. -/
def closed (deferred : Bool) (source target : Vector (Word (ZMod p)) 8) : ClosedVerifier (ZMod p) where
  name := "host-commit"
  circuit := circuit deferred source target
  assumptions := by intros; trivial
  lookups := by simp only [circuit, main, circuit_norm, HostCommitBoundary.verifier, HostCommitBoundary.verifierMain]
  public_interactions := by
    intro interaction member env
    simp only [circuit, main, circuit_norm, GeneralFormalCircuit.toSubcircuit_interactions, HostCommitBoundary.verifier, HostCommitBoundary.verifierMain, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;>
      simp [circuit_norm, ChannelInteraction.toRaw, AbstractInteraction.Guarantees,
        AbstractInteraction.Requirements, Channel.toRaw, Expression.eval]

  length_zero := rfl
  constraints := by
    intros
    simp only [circuit, main, circuit_norm, HostCommitBoundary.verifier, HostCommitBoundary.verifierMain]
  interactions := by
    intro offset env channel
    exact (values deferred source target offset env channel).trans (values deferred source target 0 _ channel).symm

end SP1Clean.HostCommitEndpoint
