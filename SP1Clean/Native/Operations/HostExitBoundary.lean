import SP1Clean.Model.Semantics.Decode
import SP1Clean.Model.HostExit
import ToClean.Air.VerifierExtension

/-! # Optional terminal status at a local host boundary

A running-to-stopped boundary consumes one complete exit word. HALT handlers supply that
receipt; padding supplies none. A stopped source must retain its exact optional exit code.
The endpoint circuit has no witness cells and does not infer status from the numeric code.
-/

namespace SP1Clean.HostExitBoundary

open Circuit Air.Flat Soundness
open scoped Classical

variable {p : ℕ} [Fact p.Prime]

def encode (code : BitVec 32) : Word (ZMod p) := Target.bitVecToWord (code.setWidth 64)

def main (source target : Option (BitVec 32)) (_ : Var unit (ZMod p)) : Circuit (ZMod p) Unit := do
  assertZero (.const (if source = none ∨ source = target then 0 else 1))
  channel.pullIf (.const (if source = none ∧ target.isSome then 1 else 0))
    (const (encode (target.getD 0)))

instance elaborated (source target : Option (BitVec 32)) :
    ElaboratedCircuit (ZMod p) unit unit (main source target) := by
  elaborate_circuit

def circuit (source target : Option (BitVec 32)) : GeneralFormalCircuit (ZMod p) unit unit where
  main := main source target
  elaborated := elaborated source target
  Spec _ _ _ := source = none ∨ source = target
  ProverAssumptions _ _ _ := source = none ∨ source = target
  channelsWithRequirements := [channel.toRaw]
  soundness := by
    cases source <;> cases target <;>
      circuit_proof_all [main, channel]
  completeness := by
    cases source <;> cases target <;>
      circuit_proof_all [main, channel]

theorem values (source target : Option (BitVec 32)) (offset : ℕ) (env : Environment (ZMod p))
    (selected : RawChannel (ZMod p)) :
    ((main source target ()).operations offset).interactionValuesWith selected env =
      if selected = channel.toRaw then
        [channel.pulledIfValue (if source = none ∧ target.isSome then 1 else 0)
          (encode (target.getD 0))] else [] := by
  by_cases same : selected = channel.toRaw
  · subst selected
    have raw : ((main source target ()).operations offset).interactionsWith channel.toRaw =
        [((channel (p := p)).pulledIf (.const (if source = none ∧ target.isSome then 1 else 0))
          (const (encode (target.getD 0)))).toRaw] := by simp only [main, circuit_norm]
    rw [Operations.interactionValuesWith, raw]
    simp only [List.map_cons, List.map_nil, Channel.eval_pulledIf, ProvableType.eval_const,
      ↓reduceIte, CircuitType.eval_expr, Expression.eval]
  · simp [main, Operations.interactionValuesWith, Operations.interactionsWith,
      circuit_norm, ChannelInteraction.toRaw, Ne.symm same, same]

def closed (source target : Option (BitVec 32)) : ClosedVerifier (ZMod p) where
  name := "host-exit"
  circuit := circuit source target
  assumptions := by intros; trivial
  lookups := by simp only [circuit, main, circuit_norm]
  public_interactions := by
    intro interaction member env
    simp only [circuit, main, circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at member
    obtain rfl := member
    simp only [circuit_norm, ChannelInteraction.toRaw, ↓reduceIte,
      AbstractInteraction.Requirements, Channel.toRaw, Expression.eval]
    split_ifs <;> simp

  length_zero := rfl
  constraints := by
    intros
    simp only [circuit, main, circuit_norm]
  interactions := by
    intro offset env selected
    exact (values source target offset env selected).trans (values source target 0 _ selected).symm

end SP1Clean.HostExitBoundary
