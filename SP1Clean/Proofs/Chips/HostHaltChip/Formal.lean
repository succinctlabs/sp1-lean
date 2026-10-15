import SP1Clean.Native.Chips.HostHaltChip.Defs

/-! # Soundness, completeness, and construction of native HALT handlers

The complete exit bound is semantic. Comparison columns are computed by the constructor and
used only by local completeness; no external Exit value or handler-success fact is assumed.
-/

namespace SP1Clean.HostHaltChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def ProverAssumptions (input : Inputs (ZMod p)) : Prop :=
  Spec input ∧ input.comparison = LtOperationUnsigned.populate input.call.arg1 (BoundedWord.limit (bound p))

omit [Fact (2 ^ 17 < p)] in
private theorem eval_zero (env : Environment (ZMod p)) :
    Vector.map (Expression.eval env) (Vector.map Expression.const (0 : Word (ZMod p))) = 0 := by
  simp only [Vector.map_map, Function.comp_def, Expression.eval]
  exact Vector.map_id _

theorem soundness : GeneralFormalCircuit.Soundness (Output := unit) (ZMod p) main
    (fun _ _ => True) (fun input _ _ => Spec input) := by
  circuit_proof_start [Gadgets.Equality.circuit, BoundedWord.circuit, HostCallChip.channel, HostExitBoundary.channel]
  simpa only [eval_zero, CallSpec, BoundedWord.Spec] using h_holds

theorem completeness : GeneralFormalCircuit.Completeness (Output := unit) (ZMod p) main
    (fun input _ _ => ProverAssumptions input) (fun _ _ _ => True) := by
  circuit_proof_start [Gadgets.Equality.circuit, BoundedWord.circuit, HostCallChip.channel, HostExitBoundary.channel]
  obtain ⟨⟨code, result, length, value⟩, comparison⟩ := h_assumptions
  simpa only [eval_zero] using And.intro code ⟨result, length, value, comparison⟩

def circuit : GeneralFormalCircuit (ZMod p) Inputs unit where
  name := "sp1.native.host_halt"
  main
  elaborated
  Spec input _ _ := Spec input
  ProverAssumptions input _ _ := ProverAssumptions input
  channelsWithRequirements := [HostCallChip.channel.toRaw, HostExitBoundary.channel.toRaw]
  soundness := soundness
  completeness := completeness
  requirementsChannelsLawful := by
    preserve_tactic_target
    intro input offset
    simp [main, circuit_norm, BoundedWord.circuit, HostCallChip.channel, HostExitBoundary.channel]

def populate (call : HostCallChip.Message (ZMod p)) : Inputs (ZMod p) :=
  ⟨call, LtOperationUnsigned.populate call.arg1 (BoundedWord.limit (bound p))⟩

omit [Fact (2 ^ 17 < p)] in
theorem populate_assumptions (call : HostCallChip.Message (ZMod p)) (valid : CallSpec call) :
    ProverAssumptions (populate call) := ⟨valid, rfl⟩

end SP1Clean.HostHaltChip
