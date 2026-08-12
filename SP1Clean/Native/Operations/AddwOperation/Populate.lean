import SP1Clean.Math.Word
import SP1Clean.FormalModel.Contracts.Operations
import Clean.Circuit.Basic

/-! # `AddwOperation` — `populate` (the witness generator)

SP1's `AddwOperation::populate` ported natively: the low two u16 limbs of `(a+b) mod 2^32`
(`addwValueWitness`) and bit 15 of the high result limb (`addwMsbWitness`, via the nested
`U16MSBOperation::populate_msb`), packaged into the native `Columns` struct. The
composing `AddwChip` witnesses the columns with this. `spec_populate` lives in `Formal` (it references
`Spec`, which — to avoid an import cycle through the composed `U16MSBOperation.Formal` — also lives in
`Formal`). Only `a[0..1]`/`b[0..1]` are read; the high limbs are ignored, matching ADDW. -/

namespace SP1Clean.AddwOperation

open Circuit Witgen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Native witness function ported from SP1's `AddwOperation::populate`: the low two u16 limbs of
`(a+b) mod 2^32`. (Only `a[0..1]`/`b[0..1]` are read; the high limbs are ignored, matching ADDW.) -/
def addwValueWitness (a b : Word (ZMod p)) : Vector (ZMod p) 2 :=
  let s0 := a[0].val + b[0].val
  let s1 := a[1].val + b[1].val + s0 / 65536
  #v[((s0 % 65536 : ℕ) : ZMod p), ((s1 % 65536 : ℕ) : ZMod p)]

/-- The `msb` column SP1's `populate` writes: bit 15 of the high result limb `value[1]`
(`= value[1].val / 2^15`), via the nested `U16MSBOperation::populate_msb`. -/
def addwMsbWitness (a b : Word (ZMod p)) : ZMod p :=
  (((addwValueWitness a b)[1].val / 32768 : ℕ) : ZMod p)

/-- The witnessed column struct: the two low result limbs `value` and the sign bit `msb`. The
composing `AddwChip` witnesses the columns with this. -/
def populate (a b : Word (ZMod p)) : Columns (ZMod p) :=
  ⟨addwValueWitness a b, ⟨addwMsbWitness a b⟩⟩

/-! ## Witness IR

The exportable form of the two witness functions (see `AddOperation/Populate.lean` for the pattern).
`msbIR` re-derives the high limb rather than reading the witnessed cell, exactly as
`addwMsbWitness` re-derives it from `addwValueWitness`. -/

/-- The shared carry chain: the two low base-2^16 limbs of `(a + b) mod 2^32`, as `letU` steps. -/
def valueProgram (a b : Word (Expression (ZMod p))) : Witgen.M (ZMod p) (VExpr (ZMod p) 2) := do
  let s0 ← letU (a[0].val + b[0].val)
  let s1 ← letU (a[1].val + b[1].val + s0 / 65536)
  return .lit #v[(s0 % 65536).toField, (s1 % 65536).toField]

/-- Bit 15 of the high result limb, re-derived from the same carry chain. -/
def msbProgram (a b : Word (Expression (ZMod p))) : Witgen.M (ZMod p) (VExpr (ZMod p) 1) := do
  let s0 ← letU (a[0].val + b[0].val)
  let s1 ← letU (a[1].val + b[1].val + s0 / 65536)
  return .lit #v[(s1 % 65536 / 32768).toField]

/-- The assembled (exportable) witness IR for the two low limbs. Plain def, not `@[circuit_norm]` —
the chip-proof boundary stays folded here; cross it with `valueIR_eval` only. -/
def valueIR (a b : Word (Expression (ZMod p))) : WitgenIR (ZMod p) 2 :=
  (valueProgram a b).toIR

/-- The assembled (exportable) witness IR for the sign bit. -/
def msbIR (a b : Word (Expression (ZMod p))) : WitgenIR (ZMod p) 1 :=
  (msbProgram a b).toIR

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating the value IR is exactly `addwValueWitness` on the evaluated operand words. -/
theorem valueIR_eval (env : ProverEnvironment (ZMod p))
    (a b : Word (Expression (ZMod p))) (va vb : Word (ZMod p))
    (hva : #v[Expression.eval env.toEnvironment a[0], Expression.eval env.toEnvironment a[1],
              Expression.eval env.toEnvironment a[2], Expression.eval env.toEnvironment a[3]] = va)
    (hvb : #v[Expression.eval env.toEnvironment b[0], Expression.eval env.toEnvironment b[1],
              Expression.eval env.toEnvironment b[2], Expression.eval env.toEnvironment b[3]] = vb)
    (ha : va.isU64) (hb : vb.isU64) :
    (valueIR a b).eval env = addwValueWitness va vb := by
  obtain ⟨ha0, ha1, _, _⟩ := Word.lt_cases_of_isU64 ha
  obtain ⟨hb0, hb1, _, _⟩ := Word.lt_cases_of_isU64 hb
  have hA : ∀ (i : ℕ) (h : i < 4), Expression.eval env.toEnvironment a[i] = va[i] := by
    intro i h; rw [← hva]; interval_cases i <;> simp
  have hB : ∀ (i : ℕ) (h : i < 4), Expression.eval env.toEnvironment b[i] = vb[i] := by
    intro i h; rw [← hvb]; interval_cases i <;> simp
  simp [valueIR, valueProgram, addwValueWitness, circuit_norm,
    Witgen.WitgenIR.eval, Witgen.evalSteps, Witgen.VExpr.eval, FiniteField.fromNat,
    hA 0 (by omega), hA 1 (by omega), hB 0 (by omega), hB 1 (by omega)]

/-- Evaluating the msb IR is exactly `addwMsbWitness` on the evaluated operand words.

Unlike `valueIR_eval` this needs the field bound: `addwMsbWitness` reads `.val` of an already-cast
limb, which contributes a `% p` that `2 ^ 17 < p` removes. -/
theorem msbIR_eval (env : ProverEnvironment (ZMod p))
    (a b : Word (Expression (ZMod p))) (va vb : Word (ZMod p))
    (hva : #v[Expression.eval env.toEnvironment a[0], Expression.eval env.toEnvironment a[1],
              Expression.eval env.toEnvironment a[2], Expression.eval env.toEnvironment a[3]] = va)
    (hvb : #v[Expression.eval env.toEnvironment b[0], Expression.eval env.toEnvironment b[1],
              Expression.eval env.toEnvironment b[2], Expression.eval env.toEnvironment b[3]] = vb)
    (ha : va.isU64) (hb : vb.isU64) :
    (msbIR a b).eval env = #v[addwMsbWitness va vb] := by
  have hp : 2 ^ 17 < p := Fact.out
  have hmod : ∀ x : ℕ, x % 65536 % p = x % 65536 := fun x =>
    Nat.mod_eq_of_lt (by have := Nat.mod_lt x (show 0 < 65536 by omega); omega)
  obtain ⟨ha0, ha1, _, _⟩ := Word.lt_cases_of_isU64 ha
  obtain ⟨hb0, hb1, _, _⟩ := Word.lt_cases_of_isU64 hb
  have hA : ∀ (i : ℕ) (h : i < 4), Expression.eval env.toEnvironment a[i] = va[i] := by
    intro i h; rw [← hva]; interval_cases i <;> simp
  have hB : ∀ (i : ℕ) (h : i < 4), Expression.eval env.toEnvironment b[i] = vb[i] := by
    intro i h; rw [← hvb]; interval_cases i <;> simp
  simp [msbIR, msbProgram, addwMsbWitness, addwValueWitness, circuit_norm,
    Witgen.WitgenIR.eval, Witgen.evalSteps, Witgen.VExpr.eval, FiniteField.fromNat, hmod,
    hA 0 (by omega), hA 1 (by omega), hB 0 (by omega), hB 1 (by omega)]

omit [Fact (2 ^ 17 < p)] in
/-- Environment-locality of the value IR (the `ComputableWitnesses` counterpart of `valueIR_eval`). -/
theorem valueIR_congr (env env' : ProverEnvironment (ZMod p))
    (a b : Word (Expression (ZMod p)))
    (hA : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment a[i] = Expression.eval env'.toEnvironment a[i])
    (hB : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment b[i] = Expression.eval env'.toEnvironment b[i]) :
    (valueIR a b).eval env = (valueIR a b).eval env' := by
  simp [valueIR, valueProgram, circuit_norm,
    Witgen.WitgenIR.eval, Witgen.evalSteps, Witgen.VExpr.eval,
    hA 0 (by omega), hA 1 (by omega), hB 0 (by omega), hB 1 (by omega)]

omit [Fact (2 ^ 17 < p)] in
/-- Environment-locality of the msb IR. -/
theorem msbIR_congr (env env' : ProverEnvironment (ZMod p))
    (a b : Word (Expression (ZMod p)))
    (hA : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment a[i] = Expression.eval env'.toEnvironment a[i])
    (hB : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment b[i] = Expression.eval env'.toEnvironment b[i]) :
    (msbIR a b).eval env = (msbIR a b).eval env' := by
  simp [msbIR, msbProgram, circuit_norm,
    Witgen.WitgenIR.eval, Witgen.evalSteps, Witgen.VExpr.eval,
    hA 0 (by omega), hA 1 (by omega), hB 0 (by omega), hB 1 (by omega)]

end SP1Clean.AddwOperation
