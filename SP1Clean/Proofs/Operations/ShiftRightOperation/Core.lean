import SP1Clean.Native.Operations.ShiftRightOperation.Core
import SP1Clean.Model.InteractionRecovery
import Clean.Utils.Tactics

/-! # `ShiftRightCore` — proof boundary for the inline ShiftRight assertions

The native circuit emits the 53-assert tail of the chip-local constraint block.  Its folded public
contract is `ShiftRightChip.CoreSpec`; parent chip proofs consume that one proposition instead of
repeatedly normalizing the tail.  The five leading gate constraints remain in the parent so the
combined gate is available to Clean's shallow channel-law proof.
-/

namespace SP1Clean.ShiftRightCore

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The assertion block has no semantic precondition: its own constraints establish the complete
structural `AssertSpec`. -/
def Assumptions (_ : ShiftRightChip.Columns (ZMod p)) : Prop := True

omit [Fact (2 ^ 17 < p)] in
theorem soundness :
    FormalAssertion.Soundness (ZMod p) main Assumptions ShiftRightChip.CoreSpec := by
  circuit_proof_start [ShiftRightChip.CoreSpec]
  obtain ⟨-, ⟨-, -, -, -, ⟨hbpv, -, -⟩, -, -, -⟩, ha, -, -, hcb, -, -, -, -,
    hlo, hhi, hlr, hsu, -, -, -, -, -⟩ := h_input
  have ev {n : ℕ} {xs : Vector (Expression (ZMod p)) n} {ys : Vector (ZMod p) n}
      (h : Vector.map (Expression.eval env) xs = ys) (i : ℕ) (hi : i < n) :
      Expression.eval env xs[i] = ys[i] := by
    rw [← h, Vector.getElem_map]
  simp only [ev hbpv, ev ha, ev hcb, ev hlo, ev hhi, ev hlr, ev hsu] at h_holds
  exact h_holds

omit [Fact (2 ^ 17 < p)] in
theorem completeness :
    FormalAssertion.Completeness (ZMod p) main Assumptions ShiftRightChip.CoreSpec := by
  circuit_proof_start [ShiftRightChip.CoreSpec]
  obtain ⟨-, ⟨-, -, -, -, ⟨hbpv, -, -⟩, -, -, -⟩, ha, -, -, hcb, -, -, -, -,
    hlo, hhi, hlr, hsu, -, -, -, -, -⟩ := h_input
  have ev {n : ℕ} {xs : Vector (Expression (ZMod p)) n} {ys : Vector (ZMod p) n}
      (h : Vector.map (Expression.eval env.toEnvironment) xs = ys) (i : ℕ) (hi : i < n) :
      Expression.eval env.toEnvironment xs[i] = ys[i] := by
    rw [← h, Vector.getElem_map]
  simp only [ev hbpv, ev ha, ev hcb, ev hlo, ev hhi, ev hlr, ev hsu]
  exact h_spec

/-- The 53-assert ShiftRight chip-local tail as a zero-witness Clean `FormalAssertion`. -/
def circuit : FormalAssertion (ZMod p) ShiftRightChip.Columns where
  main
  elaborated
  Assumptions := Assumptions
  Spec := ShiftRightChip.CoreSpec
  soundness := soundness
  completeness := completeness
  channelsWithRequirements := []

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithRequirements_eq :
    (circuit (p := p)).channelsWithRequirements = ([] : List (RawChannel (ZMod p))) := rfl

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (cols : Var ShiftRightChip.Columns (ZMod p)) :
    circuit.localLength cols = 0 := rfl

omit [Fact (2 ^ 17 < p)] in
/-- The assertion-only core contributes no interaction on any channel when composed.  Keeping this
as a named compositional lemma lets parent exposure proofs erase the folded core without unfolding
its 53 assertions. -/
theorem interactionsWith_subcircuit_eq_nil (channel : RawChannel (ZMod p))
    (cols : Var ShiftRightChip.Columns (ZMod p)) (offset : ℕ) (ops : Operations (ZMod p)) :
    Operations.interactionsWith channel
        (.subcircuit (circuit.toSubcircuit offset cols) :: ops) =
      Operations.interactionsWith channel ops :=
  InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil
    circuit channel cols ops List.not_mem_nil List.not_mem_nil

end SP1Clean.ShiftRightCore
