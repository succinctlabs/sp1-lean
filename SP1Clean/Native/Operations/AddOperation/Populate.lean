import SP1Clean.FormalModel.Contracts.Operations
import SP1Clean.Math.Word
import SP1Clean.Model.Channels
import SP1Clean.Model.ByteTable
import SP1Clean.Extracted.AddOperation
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # `AddOperation` — `populate` (the witness generator)

SP1's `AddOperation::populate` ported natively; `spec_populate` proves the result satisfies `Spec`.
Circuit in `Extracted`, arithmetic core in `RawSpec`, `FormalAssertion` in `Formal`. -/

namespace SP1Clean.AddOperation

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

instance : Fact (p > 2) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

omit [Fact p.Prime] in
/-- `16 < p`, so the `Range` byte-row width column `16` round-trips through `byteRowSpec_range`. -/
lemma h16p : (16 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega

/-- Native port of SP1's `AddOperation::populate`: the four base-2^16 limbs of `(a + b) mod 2^64`.
Conformance to SP1's Rust `populate` checked by `WitnessTests/AddOperationWitness.lean`. -/
def populate (a b : Word (ZMod p)) : Word (ZMod p) :=
  let s0 := a[0].val + b[0].val
  let s1 := a[1].val + b[1].val + s0 / 65536
  let s2 := a[2].val + b[2].val + s1 / 65536
  let s3 := a[3].val + b[3].val + s2 / 65536
  #v[((s0 % 65536 : ℕ) : ZMod p), ((s1 % 65536 : ℕ) : ZMod p),
     ((s2 % 65536 : ℕ) : ZMod p), ((s3 % 65536 : ℕ) : ZMod p)]

/-- `populate a b` satisfies the gadget `Spec` for any `is_real` (the conclusion is `is_real = 1`-gated,
so it holds unconditionally). The composing chip uses this to discharge its assertion obligation. -/
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
