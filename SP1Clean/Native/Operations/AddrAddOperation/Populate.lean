import SP1Clean.FormalModel.Contracts.Operations
import SP1Clean.Math.Word
import SP1Clean.Extracted.AddrAddOperation
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # `AddrAddOperation` — `populate` (the witness generator)

SP1's `AddrAddOperation::populate` ported natively; `spec_populate` proves the result satisfies `Spec`.
No conformance anchor (the Rust `witness_vectors` binary has no AddrAdd dispatch).
Circuit in `Extracted`, arithmetic core in `RawSpec`, `FormalAssertion` in `Formal`. -/

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

/-- `populate a b` satisfies the gadget `Spec` when the 64-bit-truncated sum is a valid 48-bit
address. The composing chip uses this completeness-side condition to discharge its assertion
obligation; soundness derives the same bound from the AIR. -/
theorem spec_populate {a b : Word (ZMod p)} (ha : a.isU64) (hb : b.isU64)
    (hfit : (Word.toNat a + Word.toNat b) % 2 ^ 64 < 2 ^ 48) (is_real : ZMod p) :
    Spec (⟨a, b, { value := populate a b }, is_real⟩ : Inputs (ZMod p)) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
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
