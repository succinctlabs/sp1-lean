import SP1Clean.Math.Word
import SP1Clean.Extracted.IsZeroOperation

/-! # `IsZeroOperation` — `populate` (the witness generator)

SP1's `IsZeroOperation::populate` ported natively. `isZeroWitness` (vector form) is retained for the
conformance check in `WitnessTests/IsZeroOperationWitness.lean`. `spec_populate` lives in `Formal` to
avoid an import cycle through the composing ops. -/

namespace SP1Clean.IsZeroOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Native port of SP1's `IsZeroOperation::populate`: `#v[inverse, result]`.
On `a = 0`, returns `[0, 1]`; on `a ≠ 0`, returns `[a⁻¹, 0]`. -/
def isZeroWitness (a : ZMod p) : Vector (ZMod p) 2 :=
  if a = 0 then #v[0, 1] else #v[a⁻¹, 0]

/-- The witnessed column struct `⟨inverse, result⟩` — `isZeroWitness` packaged as the extracted
`IsZeroOperation` columns the composing op threads in. -/
def populate (a : ZMod p) : Extracted.IsZeroOperation (ZMod p) :=
  if a = 0 then ⟨0, 1⟩ else ⟨a⁻¹, 0⟩

section FE

/-- The witness-IR twin of `populate`: `⟨x⁻¹, if x = 0 then 1 else 0⟩` (the IR's `.inv` shares
the `0⁻¹ = 0` convention, so the inverse cell needs no dispatch). -/
def populateFE (x : Witgen.FExpr (ZMod p)) : Extracted.IsZeroOperation (Witgen.FExpr (ZMod p)) :=
  ⟨.inv x, .ite (x =? (0 : ZMod p)) 1 0⟩

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating the twin is `populate` on the evaluated operand. -/
theorem populateFE_eval (env : ProverEnvironment (ZMod p)) (x : Witgen.FExpr (ZMod p))
    (v : ZMod p) (hx : Witgen.FExpr.eval { env := env } x = v) :
    Witgen.eval { env := env } (populateFE x) = populate v := by
  by_cases hv : v = 0 <;>
    simp [populateFE, populate, circuit_norm, explicit_provable_type, hx, hv,
      Witgen.StructEval.eval.go, ProvableStruct.toComponents, ProvableStruct.fromComponents]

omit [Fact (2 ^ 17 < p)] in
/-- Environment-locality of the twin. -/
theorem populateFE_congr (env env' : ProverEnvironment (ZMod p)) (x : Witgen.FExpr (ZMod p))
    (hx : Witgen.FExpr.eval { env := env } x = Witgen.FExpr.eval { env := env' } x) :
    Witgen.eval { env := env } (populateFE x) = Witgen.eval { env := env' } (populateFE x) := by
  simp [populateFE, circuit_norm, explicit_provable_type, hx,
    Witgen.StructEval.eval.go, ProvableStruct.toComponents, ProvableStruct.fromComponents]

end FE

end SP1Clean.IsZeroOperation
