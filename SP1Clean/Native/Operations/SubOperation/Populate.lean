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
Circuit in `Defs`, arithmetic core in `RawSpec`, `FormalAssertion` in `Formal`. -/

namespace SP1Clean.SubOperation

open Circuit
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

/-- `populate a b` satisfies the gadget `Spec` for any `is_real`. The composing chip uses this to
discharge its assertion obligation.

Heartbeat budget: measured 2026-07 by ladder (control run at 1 heartbeat gave a real `elaborator`
timeout). Passes at 20000 and 10000, fails at 5000 (`whnf` at the signature), so the floor is in
(5000, 10000] and the plain default carries ≥20× headroom. The former 2000000 ceiling was ~200-400×
over and was removed; the structurally identical `AddOperation.spec_populate` never carried one. -/
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
  rw [BitVec.eq_sub_iff_add_eq, ← BitVec.toNat_inj, BitVec.toNat_add,
      Word.toBitVec64_toNat hVU, Word.toBitVec64_toNat hb, Word.toBitVec64_toNat ha,
      Word.toNat_def, Word.toNat_def, Word.toNat_def]
  simp only [populate, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega),
      ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)]
  omega

end SP1Clean.SubOperation
