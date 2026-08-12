import SP1Clean.FormalModel.Contracts.Operations
import SP1Clean.Math.Word
import SP1Clean.Model.Channels
import SP1Clean.Model.ByteTable
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # `AddOperation` — `populate` (the witness generator)

The familiar limb-wise population algorithm, implemented locally; `spec_populate` proves the result
satisfies `Spec`. It complements the Rust implementation but is not required to share its data shape.

Two forms of the same algorithm live here:
* `populate` — the pure value-level function (the semantic anchor; `spec_populate` and the
  `SP1CleanTest` Rust-conformance battery are stated against it, unchanged);
* `populateProgram`/`populateIR` — the **exportable witness-IR** form consumed by the chip `main`
  (`witnessIR`), mirroring `populate` line-for-line in Clean's `Witgen.M` builder. `populateIR_eval`
  ties the two, so chip completeness proofs rewrite the witness obligation to `populate` exactly as
  they did against the retired `witnessVectorNative` closure.

`populateIR` is deliberately **not** `@[circuit_norm]`: chip proofs keep their witness obligation
folded at this boundary (the repo's opacity doctrine), and only `populateIR_eval` crosses it. -/

namespace SP1Clean.AddOperation

open Circuit Witgen
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

instance : Fact (p > 2) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- The four base-2^16 limbs of `(a + b) mod 2^64`. Chip-level populate/trace conformance checks the
assembled row against Rust; there is intentionally no operation-level extraction boundary. -/
def populate (a b : Word (ZMod p)) : Word (ZMod p) :=
  let s0 := a[0].val + b[0].val
  let s1 := a[1].val + b[1].val + s0 / 65536
  let s2 := a[2].val + b[2].val + s1 / 65536
  let s3 := a[3].val + b[3].val + s2 / 65536
  #v[((s0 % 65536 : ℕ) : ZMod p), ((s1 % 65536 : ℕ) : ZMod p),
     ((s2 % 65536 : ℕ) : ZMod p), ((s3 % 65536 : ℕ) : ZMod p)]

/-- The witness-IR form of `populate`, over the chip's input *expressions*: the four base-2^16 limbs
of `(a + b) mod 2^64`, with the running sums shared as `letU` steps (u64-sorted — every intermediate
is `< 2^17`, far from the `2^64` wrap). -/
def populateProgram (a b : Word (Expression (ZMod p))) : Witgen.M (ZMod p) (VExpr (ZMod p) 4) := do
  let s0 ← letU (a[0].val + b[0].val)
  let s1 ← letU (a[1].val + b[1].val + s0 / 65536)
  let s2 ← letU (a[2].val + b[2].val + s1 / 65536)
  let s3 ← letU (a[3].val + b[3].val + s2 / 65536)
  return .lit #v[(s0 % 65536).toField, (s1 % 65536).toField,
                 (s2 % 65536).toField, (s3 % 65536).toField]

/-- The assembled (exportable) witness IR for the Add limbs. Plain def, not `@[circuit_norm]` —
the chip-proof boundary stays folded here; cross it with `populateIR_eval` only. -/
def populateIR (a b : Word (Expression (ZMod p))) : WitgenIR (ZMod p) 4 :=
  (populateProgram a b).toIR

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating the witness IR is exactly `populate` on the evaluated operand words (stated with the
evaluated words abstracted, in the `#v[…]`-of-`Expression.eval` form the chip completeness context
carries via `vec4_eval`). The `isU64` bounds keep every u64-sorted intermediate below `2^64`, so the
IR's wrapping arithmetic agrees with `populate`'s ℕ arithmetic. -/
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
  simp [populateIR, populateProgram, populate, circuit_norm,
    Witgen.WitgenIR.eval, Witgen.evalSteps, Witgen.VExpr.eval, FiniteField.fromNat,
    hA 0 (by omega), hA 1 (by omega), hA 2 (by omega), hA 3 (by omega),
    hB 0 (by omega), hB 1 (by omega), hB 2 (by omega), hB 3 (by omega)]

/-- `populate a b` satisfies the gadget `Spec` for any `is_real` (the conclusion is `is_real = 1`-gated,
so it holds unconditionally). The composing chip uses this to discharge its assertion obligation. -/
theorem spec_populate {a b : Word (ZMod p)} (ha : a.isU64) (hb : b.isU64) (is_real : ZMod p) :
    Spec (⟨a, b, { value := populate a b }, is_real⟩ : Inputs (ZMod p)) := by
  have hp : 2 ^ 17 < p := Fact.out
  obtain ⟨ha0, ha1, ha2, ha3⟩ := Word.lt_cases_of_isU64 ha
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64 hb
  intro _
  have hVU : (populate a b).isU64 := by
    apply Word.isU64_of_cases <;>
      simp only [populate, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ] <;>
      (rw [ZMod.val_natCast_of_lt (by omega)]; omega)
  refine ⟨hVU, ?_⟩
  rw [← BitVec.toNat_inj, BitVec.toNat_add, Word.toBitVec64_toNat hVU,
      Word.toBitVec64_toNat ha, Word.toBitVec64_toNat hb,
      Word.toNat_def, Word.toNat_def, Word.toNat_def]
  simp only [populate, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega),
      ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)]
  omega

end SP1Clean.AddOperation
