import SP1Clean.FormalModel.Contracts.Operations
import SP1Clean.Math.Word
import SP1Clean.Model.Channels
import SP1Clean.Model.ByteTable
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # `SubOperation` — `populate` (the witness generator)

The local subtraction witness generator; `spec_populate` proves the result satisfies `Spec`.
Circuit in `Defs`, arithmetic core in `RawSpec`, `FormalAssertion` in `Formal`.

`populateProgram`/`populateIR` are the exportable witness-IR form (see
`AddOperation/Populate.lean` for the pattern). The per-limb two's-complement `65535 - bᵢ` is taken
at the *field-expression* level (`(65535 - b[i]).val`) because the u64 sort has no subtraction; under
the `isU64` bound the field complement's value is exactly the ℕ complement, which `populateIR_eval`
proves. -/

namespace SP1Clean.SubOperation

open Circuit Witgen
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

instance : Fact (p > 2) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- The four base-2^16 limbs of `(a - b) mod 2^64` via two's-complement (`65535 - bᵢ` per
limb, carry init `1`). Chip-level populate/trace conformance checks the assembled row against Rust;
there is intentionally no operation-level extraction boundary. -/
def populate (a b : Word (ZMod p)) : Word (ZMod p) :=
  let s0 := a[0].val + (65535 - b[0].val) + 1
  let s1 := a[1].val + (65535 - b[1].val) + s0 / 65536
  let s2 := a[2].val + (65535 - b[2].val) + s1 / 65536
  let s3 := a[3].val + (65535 - b[3].val) + s2 / 65536
  #v[((s0 % 65536 : ℕ) : ZMod p), ((s1 % 65536 : ℕ) : ZMod p),
     ((s2 % 65536 : ℕ) : ZMod p), ((s3 % 65536 : ℕ) : ZMod p)]

/-- The per-limb two's-complement `65535 - bᵢ`, taken in the field: below `2 ^ 16` the field
difference's value is the ℕ difference (no wraparound, since `2 ^ 17 < p`). This is the bridge the
witness IR needs, whose u64 sort has no subtraction. -/
theorem val_complement {y : ZMod p} (hy : y.val < 2 ^ 16) :
    ((65535 : ZMod p) - y).val = 65535 - y.val := by
  have hp : 2 ^ 17 < p := Fact.out
  have h : (65535 : ZMod p) - y = ((65535 - y.val : ℕ) : ZMod p) := by
    rw [Nat.cast_sub (by omega)]
    push_cast [ZMod.natCast_val, ZMod.cast_id]
    ring
  rw [h, ZMod.val_natCast_of_lt (by omega)]

/-- The witness-IR form of `populate`: the four base-2^16 limbs of `(a - b) mod 2^64`, with the
running sums shared as `letU` steps. The complement `65535 - bᵢ` is a *field* expression (see
`val_complement`); everything else is u64-sorted and stays far below the `2 ^ 64` wrap. -/
def populateProgram (a b : Word (Expression (ZMod p))) : Witgen.M (ZMod p) (VExpr (ZMod p) 4) := do
  let s0 ← letU (a[0].val + ((65535 : Expression (ZMod p)) - b[0]).val + 1)
  let s1 ← letU (a[1].val + ((65535 : Expression (ZMod p)) - b[1]).val + s0 / 65536)
  let s2 ← letU (a[2].val + ((65535 : Expression (ZMod p)) - b[2]).val + s1 / 65536)
  let s3 ← letU (a[3].val + ((65535 : Expression (ZMod p)) - b[3]).val + s2 / 65536)
  return .lit #v[(s0 % 65536).toField, (s1 % 65536).toField,
                 (s2 % 65536).toField, (s3 % 65536).toField]

/-- The assembled (exportable) witness IR for the Sub limbs. Plain def, not `@[circuit_norm]` —
the chip-proof boundary stays folded here; cross it with `populateIR_eval` only. -/
def populateIR (a b : Word (Expression (ZMod p))) : WitgenIR (ZMod p) 4 :=
  (populateProgram a b).toIR

/-- Evaluating the witness IR is exactly `populate` on the evaluated operand words. -/
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
    hB 0 (by omega), hB 1 (by omega), hB 2 (by omega), hB 3 (by omega),
    val_complement hb0, val_complement hb1, val_complement hb2, val_complement hb3]

/-- `populate a b` satisfies the gadget `Spec` for any `is_real`. The composing chip uses this to
discharge its assertion obligation.

Heartbeat budget: measured 2026-07 by ladder (control run at 1 heartbeat gave a real `elaborator`
timeout). Passes at 20000 and 10000, fails at 5000 (`whnf` at the signature), so the floor is in
(5000, 10000] and the plain default carries ≥20× headroom. The former 2000000 ceiling was ~200-400×
over and was removed; the structurally identical `AddOperation.spec_populate` never carried one. -/
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
  rw [BitVec.eq_sub_iff_add_eq, ← BitVec.toNat_inj, BitVec.toNat_add,
      Word.toBitVec64_toNat hVU, Word.toBitVec64_toNat hb, Word.toBitVec64_toNat ha,
      Word.toNat_def, Word.toNat_def, Word.toNat_def]
  simp only [populate, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega),
      ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)]
  omega

end SP1Clean.SubOperation
