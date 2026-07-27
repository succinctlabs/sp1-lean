import SP1Clean.Native.Operations.ShiftLeftOperation.Core
import SP1Clean.Model.InteractionRecovery
import Clean.Utils.Tactics

/-! # `ShiftLeftCore` — proof boundary for ShiftLeft's assertion tail

The native circuit emits the chip-local constraint tail. Its folded public contract is
`ShiftLeftChip.CoreSpec`, so parent proofs need not repeatedly normalize the full assertion list.
-/

namespace SP1Clean.ShiftLeftCore

open Circuit
open Extracted (ShiftLeftCols)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The assertion block has no semantic precondition. -/
def Assumptions (_ : ShiftLeftCols (ZMod p)) : Prop := True

omit [Fact (2 ^ 17 < p)] in
theorem soundness :
    FormalAssertion.Soundness (ZMod p) main Assumptions ShiftLeftChip.CoreSpec := by
  circuit_proof_start [ShiftLeftChip.CoreSpec]
  obtain ⟨-, ⟨-, -, -, -, ⟨hbpv, -, -⟩, -, -, -⟩, ha, hcb, -, -, -, hsu,
    hlo, hhi, hlr, -, -, -, -⟩ := h_input
  have ev {n : ℕ} {xs : Vector (Expression (ZMod p)) n} {ys : Vector (ZMod p) n}
      (h : Vector.map (Expression.eval env) xs = ys) (i : ℕ) (hi : i < n) :
      Expression.eval env xs[i] = ys[i] := by
    rw [← h, Vector.getElem_map]
  simp only [ev hbpv, ev ha, ev hcb, ev hsu, ev hlo, ev hhi, ev hlr] at h_holds
  exact h_holds

omit [Fact (2 ^ 17 < p)] in
theorem completeness :
    FormalAssertion.Completeness (ZMod p) main Assumptions ShiftLeftChip.CoreSpec := by
  circuit_proof_start [ShiftLeftChip.CoreSpec]
  obtain ⟨-, ⟨-, -, -, -, ⟨hbpv, -, -⟩, -, -, -⟩, ha, hcb, -, -, -, hsu,
    hlo, hhi, hlr, -, -, -, -⟩ := h_input
  have ev {n : ℕ} {xs : Vector (Expression (ZMod p)) n} {ys : Vector (ZMod p) n}
      (h : Vector.map (Expression.eval env.toEnvironment) xs = ys) (i : ℕ) (hi : i < n) :
      Expression.eval env.toEnvironment xs[i] = ys[i] := by
    rw [← h, Vector.getElem_map]
  simp only [ev hbpv, ev ha, ev hcb, ev hsu, ev hlo, ev hhi, ev hlr]
  exact h_spec

/-- The zero-witness ShiftLeft chip-local tail as a Clean `FormalAssertion`. -/
def circuit : FormalAssertion (ZMod p) ShiftLeftCols where
  main
  elaborated
  Assumptions := Assumptions
  Spec := ShiftLeftChip.CoreSpec
  soundness := soundness
  completeness := completeness
  channelsWithRequirements := []

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithRequirements_eq :
    (circuit (p := p)).channelsWithRequirements = ([] : List (RawChannel (ZMod p))) := rfl

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (cols : Var ShiftLeftCols (ZMod p)) :
    circuit.localLength cols = 0 := rfl

omit [Fact (2 ^ 17 < p)] in
/-- The assertion-only core contributes no interaction on any channel when composed. -/
theorem interactionsWith_subcircuit_eq_nil (channel : RawChannel (ZMod p))
    (cols : Var ShiftLeftCols (ZMod p)) (offset : ℕ) (ops : Operations (ZMod p)) :
    Operations.interactionsWith channel
        (.subcircuit (circuit.toSubcircuit offset cols) :: ops) =
      Operations.interactionsWith channel ops := by
  exact InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil
    circuit channel cols ops (by exact List.not_mem_nil)
      (by exact List.not_mem_nil)

end SP1Clean.ShiftLeftCore
