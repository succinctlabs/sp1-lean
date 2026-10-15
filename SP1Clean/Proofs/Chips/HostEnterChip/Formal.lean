import SP1Clean.Native.Chips.HostEnterChip.Defs
import Clean.Utils.Tactics

/-! # The zero-effect native control handler

The handler checks the canonical call and zero result with no witness cells. The same semantic
contract supplies local completeness, and no constructor needs auxiliary comparison columns.
-/

namespace SP1Clean.HostEnterChip

open Circuit

variable {p : ℕ} [Fact p.Prime]

private theorem eval_zero (env : Environment (ZMod p)) :
    Vector.map (Expression.eval env) (Vector.map Expression.const (0 : Word (ZMod p))) = 0 := by
  simp only [Vector.map_map, Function.comp_def, Expression.eval]
  exact Vector.map_id _

def circuit : GeneralFormalCircuit (ZMod p) Inputs unit where
  name := "sp1.native.enter"
  main
  elaborated
  Spec input _ _ := Spec input
  ProverAssumptions input _ _ := Spec input
  channelsWithRequirements := [HostCallChip.channel.toRaw]
  soundness := by
    circuit_proof_start [Gadgets.Equality.circuit, HostCallChip.channel, codeWord]
    simpa only [eval_zero, codeWord, circuit_norm] using h_holds
  completeness := by
    circuit_proof_start [Gadgets.Equality.circuit, HostCallChip.channel, codeWord]
    simpa only [eval_zero, Spec, codeWord, circuit_norm] using h_assumptions
  requirementsChannelsLawful := by
    preserve_tactic_target
    intro input offset
    simp [main, circuit_norm, HostCallChip.channel]

end SP1Clean.HostEnterChip
