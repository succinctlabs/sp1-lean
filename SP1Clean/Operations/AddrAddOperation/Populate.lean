import SP1Clean.Specs.Operation
import SP1Clean.Foundations.Word
import SP1Clean.Extracted.AddrAddOperation
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # `AddrAddOperation` — `populate` (the witness generator)

SP1's `AddrAddOperation::populate` — the witness generator the composing chip uses to fill
`cols.value` — ported natively, plus `spec_populate` (the result satisfies the gadget `Spec`). The
elaborated `AddrAddOperation::eval` circuit (`main` + `ElaboratedCircuit`) is the auto-generated
sibling `Extracted` module; the arithmetic core is in `RawSpec`; the `FormalAssertion` contract
(soundness/completeness/`circuit`) in `Formal`.

No `WITNESS_OPERATIONS` conformance anchor is emitted for AddrAdd (the Rust `witness_vectors` binary
has no AddrAdd dispatch), consistent with the other range-checked leaf migrations
(U16Compare/U16MSB/Bitwise/IsEqualWord). -/

namespace SP1Clean.AddrAddOperation

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

instance : Fact (p > 2) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

omit [Fact p.Prime] in
/-- `16 < p`, so the `Range` byte-row width column `16` round-trips through `byteRowSpec_range`. -/
lemma h16p : (16 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega

/-- The native witness assignment, **field-generic** over `ZMod p`: the three base-2^16 limbs of
`(a + b) mod 2^48` (limb 0 = low). SP1's `AddrAddOperation::populate` ported to Lean — the
bit-decomposition (`.val`, `% / 65536`) is intrinsically over ℕ, but the function's domain/codomain
are the chip's `Word`/`Vector (ZMod p) 3`, so the ℕ never escapes. The composing chip witnesses
`value` with it (the gadget itself is a pure assertion). -/
def populate (a b : Word (ZMod p)) : Vector (ZMod p) 3 :=
  let s0 := a[0].val + b[0].val
  let s1 := a[1].val + b[1].val + s0 / 65536
  let s2 := a[2].val + b[2].val + s1 / 65536
  #v[((s0 % 65536 : ℕ) : ZMod p), ((s1 % 65536 : ℕ) : ZMod p), ((s2 % 65536 : ℕ) : ZMod p)]

set_option maxHeartbeats 4000000 in
/-- The result `value = populate a b` satisfies the gadget `Spec` for any `is_real`. This is the
witness-reconstruction the composing chip uses to discharge the `assertion AddrAddOperation.circuit`'s
completeness obligation. Independent of `is_real` because the `Spec` conclusion is `is_real = 1`-gated
and holds unconditionally. -/
theorem spec_populate {a b : Word (ZMod p)} (ha : a.isU64) (hb : b.isU64) (is_real : ZMod p) :
    Spec (⟨a, b, { value := populate a b }, is_real⟩ : Inputs (ZMod p)) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  obtain ⟨ha0, ha1, ha2, ha3⟩ := Word.lt_cases_of_isU64 ha
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64 hb
  intro _
  -- reduce the structure projection `{value := populate a b}.value` to `populate a b`
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
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsum48]; omega
  · rw [hv0]; omega
  · rw [hv1]; omega
  · rw [hv2]; omega

end SP1Clean.AddrAddOperation
