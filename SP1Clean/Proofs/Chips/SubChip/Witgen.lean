import SP1Clean.Proofs.Chips.SubChip.Formal
import ToClean.Circuit.WitgenBridge

/-! # `SP1Clean.SubChip` — honest witness generation (`ComputableWitnesses`)

The second instance of the witgen bridge (see `AddChip/Witgen.lean` for the programme note): Sub's
witness generators read only cells *below* the row's starting offset — its own inputs — so Clean's
array-backed interpreter provably reproduces them (`Circuit.witgen_usesLocalWitnesses`).

Sub composes the same six operations as Add in the same order, so the proof is the same shape; the
only difference is that its single witnessed value is the two's-complement sum
`SubOperation.populateIR`, whose complement limbs are `Expression` arithmetic over the operands and
so carry no extra environment dependence. -/

namespace SP1Clean.SubChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Sub's row has computable witnesses: every witnessed cell is a function of the input row alone.

`FlatOperation.forAll_witnessCongr_of_subcircuit` dispatches the five zero-witness subcircuits by
their cell count, without unfolding them, and `SubOperation.populateIR_congr` discharges the one real
obligation from the input agreement that `FormalCircuitBase.ComputableWitnesses` supplies. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnesses := by
  intro n input env env'
  simp only [circuit, main, circuit_norm, Operations.forAllFlat, Operations.forAll]
  refine ⟨FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    fun _ h_input => ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_⟩
  · simp [circuit_norm]
  · -- `eval_opBVal`/`eval_opCVal` are stated in `circuit_norm`'s own orientation, so the
    -- struct-level input agreement projects straight onto the operand words.
    refine SubOperation.populateIR_congr env env' _ _ (fun i hi => ?_) (fun i hi => ?_)
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.op_b_val) h_input
      simp only [eval_opBVal] at hv
      simpa [Vector.getElem_map] using congrArg (fun v : Word (ZMod p) => v[i]) hv
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.op_c_val) h_input
      simp only [eval_opCVal] at hv
      simpa [Vector.getElem_map] using congrArg (fun v : Word (ZMod p) => v[i]) hv
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]

end SP1Clean.SubChip
