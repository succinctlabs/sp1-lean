import SP1Clean.FormalModel.Contracts.Operations
import Clean.Circuit.Basic

/-! # `U16MSBOperation` — `populate` (the witness generator)

The witness assignment `populate_msb` (the high bit of `a`, threaded in by the composing operation),
its witness-IR twin `populate_msbF`, and `spec_populate` (the witnessed `msb` satisfies the gadget
`Spec`). The elaborated `eval` circuit is hand-maintained in the sibling `Defs.lean`; the arithmetic
core is in `RawSpec`; the `FormalAssertion` contract in `Formal`. -/

namespace SP1Clean.U16MSBOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- SP1's `eval_msb` witness: the high bit of `a` (`a.val / 2^15`). -/
def populate_msb (a : ZMod p) : ZMod p := ((a.val / 32768 : ℕ) : ZMod p)

omit [Fact (2 ^ 17 < p)] in
/-- The closed form of the witness: the `2^15` division is the high-bit indicator. Both the
booleanness lemma and the `Spec` obligation are instances of this one case split. -/
private lemma populate_msb_eq {a : ZMod p} (ha : a.val < 2 ^ 16) :
    populate_msb a = if a.val ≥ 32768 then 1 else 0 := by
  simp only [populate_msb]
  by_cases hge : a.val ≥ 32768
  · rw [if_pos hge, show a.val / 32768 = 1 by omega, Nat.cast_one]
  · rw [if_neg hge, show a.val / 32768 = 0 by omega, Nat.cast_zero]

omit [Fact (2 ^ 17 < p)] in
/-- `populate_msb` is always boolean (for a genuine 16-bit `a`) — the composing operation uses this to
discharge the gadget's (now unconditional) `msb` booleanness obligation on every row. -/
theorem populate_msb_bool {a : ZMod p} (ha : a.val < 2 ^ 16) :
    populate_msb a = 0 ∨ populate_msb a = 1 := by
  rw [populate_msb_eq ha]; split <;> simp

omit [Fact (2 ^ 17 < p)] in
/-- `populate_msb a` satisfies the gadget `Spec` for any `is_real`. The composing operation uses this
to discharge its assertion obligation. -/
theorem spec_populate {a : ZMod p} (ha : a.val < 2 ^ 16) (is_real : ZMod p) :
    Spec (⟨a, ⟨populate_msb a⟩, is_real⟩ : Inputs (ZMod p)) :=
  ⟨populate_msb_bool ha, fun _ => populate_msb_eq ha⟩

/-! ## Witness IR

The exportable `FExpr` twin of `populate_msb`, for composition into the witness-IR programs of the
operations that thread a high bit (`Lt`'s sign compare, `Mul`'s sign extension, the shift chips'
operand msbs). Deliberately **not** `@[circuit_norm]` — consumers name it in their `simp only` sets
beside their own `populateIR` (the opacity doctrine, see `AddOperation/Populate.lean`). -/

/-- The `FExpr` twin of `populate_msb`: the high bit of a 16-bit operand, as the u64-sort division
`x.val / 2^15`. -/
def populate_msbF (x : Witgen.FExpr (ZMod p)) : Witgen.FExpr (ZMod p) :=
  (x.val / 32768).toField

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating the `FExpr` twin is exactly `populate_msb` on the evaluated operand. The 16-bit
bound keeps the u64-sorted `val` from wrapping, so the IR's division agrees with `populate_msb`'s
ℕ division. -/
theorem populate_msbF_eval (ctx : Witgen.Ctx (ZMod p)) (x : Witgen.FExpr (ZMod p))
    (hx : (x.eval ctx).val < 2 ^ 16) :
    (populate_msbF x).eval ctx = populate_msb (x.eval ctx) := by
  simp only [populate_msbF, populate_msb, circuit_norm, FiniteField.fromNat]

omit [Fact (2 ^ 17 < p)] in
/-- Environment-locality of the `FExpr` twin (the `ComputableWitnesses` counterpart of
`populate_msbF_eval` — a congruence, so it needs no bounds). -/
theorem populate_msbF_congr (ctx ctx' : Witgen.Ctx (ZMod p)) (x : Witgen.FExpr (ZMod p))
    (hx : x.eval ctx = x.eval ctx') :
    (populate_msbF x).eval ctx = (populate_msbF x).eval ctx' := by
  simp only [populate_msbF, circuit_norm, -Witgen.u64Wrap, hx]

end SP1Clean.U16MSBOperation
