import SP1Clean.Native.Operations.AddressOperation
import ToClean.Circuit.WitgenBridge

/-! # `SP1Clean.AddressOperation` — honest witness generation (`ComputableWitnesses`)

The first **gadget-level** instance of the witgen bridge, and the reason it exists: every memory
chip witnesses its address cells inside this composed sub-circuit rather than in its own `main`, so
a load's `ComputableWitnesses` cannot dispatch the child by its `localLength` (it is `4`, not `0`).
`FlatOperation.forAll_witnessCongr_of_generalSubcircuit` consumes this theorem instead.

Two witness steps, one of each kind the obligation admits:

* the three address limbs, `AddrAddOperation.populateIR` over the two operand words — a function of
  the input row, discharged from the input-agreement hypothesis;
* the reserved-page inverse `is_real · (value[1] + value[2])⁻¹`, which reads two cells **this same
  sub-circuit witnessed three positions earlier**. That is the case `ComputableWitnesses` is stated
  to permit (a generator may read the environment below its own offset), so it is discharged from
  the environment-agreement hypothesis, exactly as `JalrChip`'s alignment bit is. -/

namespace SP1Clean.AddressOperation

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The address gadget's witnesses are computable: the limbs from the input operands, the inverse
from cells this sub-circuit already witnessed. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnesses := by
  intro n input env env'
  simp only [circuit, main, circuit_norm, Operations.forAllFlat, Operations.forAll]
  refine ⟨fun _ h_input => ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    fun h_agree h_input => ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_⟩
  · refine AddrAddOperation.populateIR_congr env env' _ _ (fun i hi => ?_) (fun i hi => ?_)
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.b) h_input
      simpa [Vector.getElem_map] using congrArg (fun v : Word (ZMod p) => v[i]) hv
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.cc) h_input
      simpa [Vector.getElem_map] using congrArg (fun v : Word (ZMod p) => v[i]) hv
  · simp [circuit_norm]
  · have hsel : Expression.eval env.toEnvironment input.is_real
        = Expression.eval env'.toEnvironment input.is_real := by
      simpa [circuit_norm] using congrArg (fun r : Inputs (ZMod p) => r.is_real) h_input
    rw [Witgen.WitgenIR.eval_ofFExprs_one, Witgen.WitgenIR.eval_ofFExprs_one]
    simp only [Witgen.FExpr.eval, Expression.eval, hsel,
      h_agree.get_eq (show n + 1 < 3 + n by omega),
      h_agree.get_eq (show n + 2 < 3 + n by omega)]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]

end SP1Clean.AddressOperation
