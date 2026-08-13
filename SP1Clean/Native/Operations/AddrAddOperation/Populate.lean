import SP1Clean.FormalModel.Contracts.Operations
import SP1Clean.Math.Word
import SP1Clean.Extracted.AddrAddOperation
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # `AddrAddOperation` — `populate` (the witness generator)

SP1's `AddrAddOperation::populate` ported natively; `spec_populate` proves the result satisfies `Spec`.
Witness-conformance anchor: `SP1CleanTest/WitnessTests/AddrAddOperationWitness.lean`.
Circuit hand-maintained in the sibling `Defs.lean`, arithmetic core in `RawSpec`,
`FormalAssertion` in `Formal`. -/

namespace SP1Clean.AddrAddOperation

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

instance : Fact (p > 2) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- Native port of SP1's `AddrAddOperation::populate`: the three base-2^16 limbs of `(a + b) mod 2^48`. -/
def populate (a b : Word (ZMod p)) : Vector (ZMod p) 3 :=
  let s0 := a[0].val + b[0].val
  let s1 := a[1].val + b[1].val + s0 / 65536
  let s2 := a[2].val + b[2].val + s1 / 65536
  #v[((s0 % 65536 : ℕ) : ZMod p), ((s1 % 65536 : ℕ) : ZMod p), ((s2 % 65536 : ℕ) : ZMod p)]

/-- The witness-IR form of `populate`, over the composing chip's input *expressions*: the three
base-2^16 limbs of `(a + b) mod 2^48`. Every intermediate is `< 2^17`, far from the u64 wrap.

This is `AddOperation.populateIR` one limb shorter, and for the same reason its running sums are
ordinary Lean `let`s: they inline into each output rather than becoming shared `letU` steps, which
keeps the IR a plain `ofFExprs` with no locals array and keeps `populateIR_eval` a `simp only`. -/
def populateIR (a b : Word (Expression (ZMod p))) : Witgen.WitgenIR (ZMod p) 3 :=
  let s0 : Witgen.U64Expr (ZMod p) := a[0].val + b[0].val
  let s1 : Witgen.U64Expr (ZMod p) := a[1].val + b[1].val + s0 / 65536
  let s2 : Witgen.U64Expr (ZMod p) := a[2].val + b[2].val + s1 / 65536
  .ofFExprs #v[(s0 % 65536).toField, (s1 % 65536).toField, (s2 % 65536).toField]

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating the witness IR is exactly `populate` on the evaluated operand words, stated in the
`#v[…]`-of-`Expression.eval` form the chip completeness context carries via `vec4_eval`. The `isU64`
bounds keep every u64-sorted intermediate below `2^64`, so the IR's wrapping arithmetic agrees with
`populate`'s ℕ arithmetic. -/
theorem populateIR_eval (env : ProverEnvironment (ZMod p))
    (a b : Word (Expression (ZMod p))) (va vb : Word (ZMod p))
    (hva : #v[Expression.eval env.toEnvironment a[0], Expression.eval env.toEnvironment a[1],
              Expression.eval env.toEnvironment a[2], Expression.eval env.toEnvironment a[3]] = va)
    (hvb : #v[Expression.eval env.toEnvironment b[0], Expression.eval env.toEnvironment b[1],
              Expression.eval env.toEnvironment b[2], Expression.eval env.toEnvironment b[3]] = vb)
    (ha : va.isU64) (hb : vb.isU64) :
    (populateIR a b).eval env = populate va vb := by
  obtain ⟨ha0, ha1, ha2, ha3⟩ := Word.lt_cases_of_isU64 ha
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64 hb
  have hA : ∀ (i : ℕ) (h : i < 4), Expression.eval env.toEnvironment a[i] = va[i] := by
    intro i h; rw [← hva]; interval_cases i <;> simp
  have hB : ∀ (i : ℕ) (h : i < 4), Expression.eval env.toEnvironment b[i] = vb[i] := by
    intro i h; rw [← hvb]; interval_cases i <;> simp
  apply Vector.ext; intro i hi
  interval_cases i <;>
    simp only [populateIR, populate, circuit_norm, FiniteField.fromNat,
      hA 0 (by omega), hA 1 (by omega), hA 2 (by omega),
      hB 0 (by omega), hB 1 (by omega), hB 2 (by omega)]

omit [Fact (2 ^ 17 < p)] in
/-- Environment-locality of the witness IR: it reads the environment only through the operand
expressions, so two environments agreeing there produce the same witnesses. This is the
`ComputableWitnesses` counterpart of `populateIR_eval` (and needs no bounds — it is a congruence,
not an evaluation). -/
theorem populateIR_congr (env env' : ProverEnvironment (ZMod p))
    (a b : Word (Expression (ZMod p)))
    (hA : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment a[i] = Expression.eval env'.toEnvironment a[i])
    (hB : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment b[i] = Expression.eval env'.toEnvironment b[i]) :
    (populateIR a b).eval env = (populateIR a b).eval env' := by
  apply Vector.ext; intro i hi
  -- No arithmetic here: both sides differ only in the operand evaluations, so unfold the IR
  -- evaluator alone (naming `circuit_norm` would fire `u64Wrap`'s `omega` with no bounds in scope).
  interval_cases i <;>
    simp only [populateIR, circuit_norm, -Witgen.u64Wrap,
      hA 0 (by omega), hA 1 (by omega), hA 2 (by omega),
      hB 0 (by omega), hB 1 (by omega), hB 2 (by omega)]

/-- `populate a b` satisfies the gadget `Spec` when the 64-bit-truncated sum is a valid 48-bit
address. The composing chip uses this completeness-side condition to discharge its assertion
obligation; soundness derives the same bound from the AIR. -/
theorem spec_populate {a b : Word (ZMod p)} (ha : a.isU64) (hb : b.isU64)
    (hfit : (Word.toNat a + Word.toNat b) % 2 ^ 64 < 2 ^ 48) (is_real : ZMod p) :
    Spec (⟨a, b, { value := populate a b }, is_real⟩ : Inputs (ZMod p)) := by
  have hp : 2 ^ 17 < p := Fact.out
  obtain ⟨ha0, ha1, ha2, ha3⟩ := Word.lt_cases_of_isU64 ha
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64 hb
  intro _
  dsimp only
  have hv0 : ((populate a b)[0]).val = (a[0].val + b[0].val) % 65536 := by
    simp only [populate, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero]
    exact ZMod.val_natCast_of_lt (by omega)
  have hv1 : ((populate a b)[1]).val
      = (a[1].val + b[1].val + (a[0].val + b[0].val) / 65536) % 65536 := by
    simp only [populate, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
    exact ZMod.val_natCast_of_lt (by omega)
  have hv2 : ((populate a b)[2]).val
      = (a[2].val + b[2].val + (a[1].val + b[1].val + (a[0].val + b[0].val) / 65536) / 65536) % 65536 := by
    simp only [populate, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
    exact ZMod.val_natCast_of_lt (by omega)
  have hsum48 : Word.toNat a + Word.toNat b
      = ((populate a b)[0]).val + 65536 * ((populate a b)[1]).val
        + 65536 ^ 2 * ((populate a b)[2]).val
        + (a[3].val + b[3].val + (a[2].val + b[2].val
            + (a[1].val + b[1].val + (a[0].val + b[0].val) / 65536) / 65536) / 65536) * 2 ^ 48 := by
    rw [hv0, hv1, hv2]; simp only [Word.toNat_def]; omega
  refine ⟨?_, ?_, ?_, ?_, hfit⟩
  · rw [hsum48]; omega
  · rw [hv0]; omega
  · rw [hv1]; omega
  · rw [hv2]; omega

end SP1Clean.AddrAddOperation
