import SP1Clean.Math.Word
import SP1Clean.FormalModel.Contracts.Operations
import SP1Clean.Native.Operations.SubOperation.Populate
import Clean.Circuit.Basic

/-! # `SubwOperation` — `populate` (the witness generator, borrow-form analog of `AddwOperation`)

SP1's `SubwOperation::populate` ported natively: the low two u16 limbs of `(a-b) mod 2^32` in
two's-complement borrow form (`subwValueWitness`, carry init `1`, complement `65535 - b[i]`) and bit 15
of the high result limb (`subwMsbWitness`), packaged into the native `Columns` struct.
The composing `SubwChip` witnesses the columns with this; `spec_populate` lives in `Formal`. -/

namespace SP1Clean.SubwOperation

open Circuit Witgen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Native witness function ported from SP1's `SubwOperation::populate`: the low two u16 limbs of
`(a-b) mod 2^32` in two's-complement borrow form (carry init `1`). -/
def subwValueWitness (a b : Word (ZMod p)) : Vector (ZMod p) 2 :=
  let s0 := a[0].val + (65535 - b[0].val) + 1
  let s1 := a[1].val + (65535 - b[1].val) + s0 / 65536
  #v[((s0 % 65536 : ℕ) : ZMod p), ((s1 % 65536 : ℕ) : ZMod p)]

/-- The `msb` column SP1's `populate` writes: bit 15 of `value[1]`. -/
def subwMsbWitness (a b : Word (ZMod p)) : ZMod p :=
  (((subwValueWitness a b)[1].val / 32768 : ℕ) : ZMod p)

/-- The witnessed column struct: the two low result limbs `value` and the sign bit `msb`. -/
def populate (a b : Word (ZMod p)) : Columns (ZMod p) :=
  ⟨subwValueWitness a b, ⟨subwMsbWitness a b⟩⟩

/-! ## Witness IR

The exportable form, following `AddwOperation`'s two-program split. As in `SubOperation`, the
per-limb complement `65535 - bᵢ` is taken at *field-expression* level (the u64 sort has no
subtraction) and bridged by `SubOperation.val_complement`. -/

/-- The two low base-2^16 limbs of the W result, as inline witness IR (running sums are ordinary
Lean `let`s — see `AddOperation.populateIR`). -/
def valueIR (a b : Word (Expression (ZMod p))) : WitgenIR (ZMod p) 2 :=
  let s0 : U64Expr (ZMod p) := a[0].val + ((65535 : Expression (ZMod p)) - b[0]).val + 1
  let s1 : U64Expr (ZMod p) := a[1].val + ((65535 : Expression (ZMod p)) - b[1]).val + s0 / 65536
  .ofFExprs #v[(s0 % 65536).toField, (s1 % 65536).toField]

/-- Bit 15 of the high result limb, re-derived from the same carry chain. -/
def msbIR (a b : Word (Expression (ZMod p))) : WitgenIR (ZMod p) 1 :=
  let s0 : U64Expr (ZMod p) := a[0].val + ((65535 : Expression (ZMod p)) - b[0]).val + 1
  let s1 : U64Expr (ZMod p) := a[1].val + ((65535 : Expression (ZMod p)) - b[1]).val + s0 / 65536
  .ofFExprs #v[(s1 % 65536 / 32768).toField]

/-- Evaluating the value IR is exactly `subwValueWitness` on the evaluated operand words. -/
theorem valueIR_eval (env : ProverEnvironment (ZMod p))
    (a b : Word (Expression (ZMod p))) (va vb : Word (ZMod p))
    (hva : #v[Expression.eval env.toEnvironment a[0], Expression.eval env.toEnvironment a[1],
              Expression.eval env.toEnvironment a[2], Expression.eval env.toEnvironment a[3]] = va)
    (hvb : #v[Expression.eval env.toEnvironment b[0], Expression.eval env.toEnvironment b[1],
              Expression.eval env.toEnvironment b[2], Expression.eval env.toEnvironment b[3]] = vb)
    (ha : va.isU64) (hb : vb.isU64) :
    (valueIR a b).eval env = subwValueWitness va vb := by
  obtain ⟨ha0, ha1, _, _⟩ := Word.lt_cases_of_isU64 ha
  obtain ⟨hb0, hb1, _, _⟩ := Word.lt_cases_of_isU64 hb
  have hA : ∀ (i : ℕ) (h : i < 4), Expression.eval env.toEnvironment a[i] = va[i] := by
    intro i h; rw [← hva]; interval_cases i <;> simp
  have hB : ∀ (i : ℕ) (h : i < 4), Expression.eval env.toEnvironment b[i] = vb[i] := by
    intro i h; rw [← hvb]; interval_cases i <;> simp
  apply Vector.ext; intro i hi
  interval_cases i <;>
    simp only [valueIR, subwValueWitness, circuit_norm, FiniteField.fromNat,
      hA 0 (by omega), hA 1 (by omega), hB 0 (by omega), hB 1 (by omega),
      SubOperation.val_complement hb0, SubOperation.val_complement hb1]

/-- Evaluating the msb IR is exactly `subwMsbWitness` on the evaluated operand words. -/
theorem msbIR_eval (env : ProverEnvironment (ZMod p))
    (a b : Word (Expression (ZMod p))) (va vb : Word (ZMod p))
    (hva : #v[Expression.eval env.toEnvironment a[0], Expression.eval env.toEnvironment a[1],
              Expression.eval env.toEnvironment a[2], Expression.eval env.toEnvironment a[3]] = va)
    (hvb : #v[Expression.eval env.toEnvironment b[0], Expression.eval env.toEnvironment b[1],
              Expression.eval env.toEnvironment b[2], Expression.eval env.toEnvironment b[3]] = vb)
    (ha : va.isU64) (hb : vb.isU64) :
    (msbIR a b).eval env = #v[subwMsbWitness va vb] := by
  have hp : 2 ^ 17 < p := Fact.out
  have hmod : ∀ x : ℕ, x % 65536 % p = x % 65536 := fun x =>
    Nat.mod_eq_of_lt (by have := Nat.mod_lt x (show 0 < 65536 by omega); omega)
  obtain ⟨ha0, ha1, _, _⟩ := Word.lt_cases_of_isU64 ha
  obtain ⟨hb0, hb1, _, _⟩ := Word.lt_cases_of_isU64 hb
  have hA : ∀ (i : ℕ) (h : i < 4), Expression.eval env.toEnvironment a[i] = va[i] := by
    intro i h; rw [← hva]; interval_cases i <;> simp
  have hB : ∀ (i : ℕ) (h : i < 4), Expression.eval env.toEnvironment b[i] = vb[i] := by
    intro i h; rw [← hvb]; interval_cases i <;> simp
  apply Vector.ext; intro i hi
  interval_cases i
  simp only [msbIR, subwMsbWitness, subwValueWitness, circuit_norm, FiniteField.fromNat,
      ZMod.val_natCast, hmod,
      hA 0 (by omega), hA 1 (by omega), hB 0 (by omega), hB 1 (by omega),
      SubOperation.val_complement hb0, SubOperation.val_complement hb1]

omit [Fact (2 ^ 17 < p)] in
/-- Environment-locality of the value IR. -/
theorem valueIR_congr (env env' : ProverEnvironment (ZMod p))
    (a b : Word (Expression (ZMod p)))
    (hA : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment a[i] = Expression.eval env'.toEnvironment a[i])
    (hB : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment b[i] = Expression.eval env'.toEnvironment b[i]) :
    (valueIR a b).eval env = (valueIR a b).eval env' := by
  apply Vector.ext; intro i hi
  interval_cases i <;>
    simp only [valueIR, circuit_norm, -Witgen.u64Wrap,
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
  apply Vector.ext; intro i hi
  interval_cases i
  simp only [msbIR, circuit_norm, -Witgen.u64Wrap,
      hA 0 (by omega), hA 1 (by omega), hB 0 (by omega), hB 1 (by omega)]

end SP1Clean.SubwOperation
