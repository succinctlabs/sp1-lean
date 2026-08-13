import SP1Clean.Proofs.Chips.AddChip.Formal
import ToClean.Circuit.WitgenBridge

/-! # `SP1Clean.AddChip` — honest witness generation (`ComputableWitnesses`)

The first instance of the **witgen bridge** (completeness programme, phase 0): the chip's witness
generators read only cells *below* the row's starting offset — i.e. its own inputs — so Clean's
array-backed interpreter `Circuit.witgen` provably reproduces them
(`Circuit.witgen_usesLocalWitnesses`). That is the step which turns the chip's `completeness` field
from "any environment consistent with my generators satisfies my constraints" into "the row my
generator *built* satisfies my constraints".

Provable only because the row is on the exportable witness IR: the witness payload is
`AddOperation.populateIR` over the input expressions alone, and `populateIR_congr` is its
environment-locality statement (the counterpart of the semantic `populateIR_eval`). A chip still
reading `ProverHint` inside a witness closure could not satisfy Clean's `ComputableWitnesses` at
all — `ProverEnvironment.AgreesBelow` does not constrain `hint` — which is one reason the
hint-driven chips move to typed `Unconstrained*` inputs during the cutover. -/

namespace SP1Clean.AddChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Add's row has computable witnesses: every witnessed cell is a function of the input row alone.

The proof is the shape every ported chip repeats. `circuit_norm` reduces the composed operation list
to its single witness obligation; `FlatOperation.forAll_witnessCongr_of_subcircuit` dispatches the five
zero-witness subcircuits by their cell count, without unfolding them; and `populateIR_congr`
discharges the one real obligation from the input-agreement hypothesis that
`FormalCircuitBase.ComputableWitnesses` supplies at each witness step.

The two `key` steps cross a normalisation gap: `circuit_norm` sends every `Eval.eval` to
`ProvableStruct.eval` (Clean's `eval_eq_eval` is `↓ high`, and that is the form the input-agreement
hypothesis arrives in), while the chip's own component-evaluation lemmas are keyed on `Eval.eval`. -/
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
    refine AddOperation.populateIR_congr env env' _ _ (fun i hi => ?_) (fun i hi => ?_)
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

end SP1Clean.AddChip
