import SP1Clean.Specs.Operation
import SP1Clean.Foundations.Word
import SP1Clean.Foundations.Channels
import SP1Clean.Foundations.ByteTable
import SP1Clean.Extracted.AddOperation
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # `AddOperation` — `populate` (the witness generator)

SP1's `AddOperation::populate` — the witness generator the composing chip uses to fill `cols.value` —
ported natively, plus `spec_populate` (the result satisfies the gadget `Spec`). The elaborated
`AddOperation::eval` circuit (`main` + `ElaboratedCircuit`) is the auto-generated sibling `Extracted`
module; the arithmetic core is in `RawSpec`; the `FormalAssertion` contract
(soundness/completeness/`circuit`) in `Formal`. -/

namespace SP1Clean.AddOperation

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

instance : Fact (p > 2) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

omit [Fact p.Prime] in
/-- `16 < p`, so the `Range` byte-row width column `16` round-trips through `byteRowSpec_range`. -/
lemma h16p : (16 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega

/-- The native witness assignment, **field-generic** over `ZMod p`: given the operand words `a`,
`b`, the result word whose limbs are the four base-2^16 limbs of `(a + b) mod 2^64` (limb 0 = low).
This is SP1's `AddOperation::populate` ported to Lean — the bit-decomposition (`.val`, `% / 65536`)
is intrinsically over ℕ, but the function's domain/codomain are the chip's `Word (ZMod p)`, so the
ℕ never escapes. The **composing chip** witnesses `value` with it (the gadget itself is a pure
assertion); `WitnessTests/AddOperationWitness.lean` checks it reproduces SP1's real `populate` at SP1's
concrete field (KoalaBear, where SP1's prover runs) — the conformance tie to the Rust source. -/
def populate (a b : Word (ZMod p)) : Word (ZMod p) :=
  let s0 := a[0].val + b[0].val
  let s1 := a[1].val + b[1].val + s0 / 65536
  let s2 := a[2].val + b[2].val + s1 / 65536
  let s3 := a[3].val + b[3].val + s2 / 65536
  #v[((s0 % 65536 : ℕ) : ZMod p), ((s1 % 65536 : ℕ) : ZMod p),
     ((s2 % 65536 : ℕ) : ZMod p), ((s3 % 65536 : ℕ) : ZMod p)]

/-- The result `value = populate a b` satisfies the gadget `Spec` for any `is_real`. This is the
witness-reconstruction the composing chip uses to discharge the `assertion AddOperation.circuit`'s
completeness obligation (`FormalAssertion.toSubcircuit` injects `Assumptions ∧ Spec` of the sub into the
parent's prover side). Independent of `is_real` because the `Spec` conclusion is `is_real = 1`-gated and
holds unconditionally. -/
theorem spec_populate {a b : Word (ZMod p)} (ha : a.isU64) (hb : b.isU64) (is_real : ZMod p) :
    Spec (⟨a, b, { value := populate a b }, is_real⟩ : Inputs (ZMod p)) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
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
