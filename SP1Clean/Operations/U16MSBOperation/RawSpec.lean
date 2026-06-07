import SP1Clean.Foundations.Word
import SP1Clean.Extracted.U16MSBOperation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases

/-! # `U16MSBOperation` — the arithmetic core (`RawSpec` + the high-bit lemma)

The structural booleanness + range form `RawSpec` (the literal meaning of SP1's `U16MSBOperation`
constraint list at `is_real = 1`, stated against the result column `cols.msb`), and the native
high-bit lemma `msb_of_raw` the gadget's soundness routes through: `msb` boolean + `2*a - msb·2^16`
a genuine 16-bit value force `msb` to be the high bit of `a` (`a.val ≥ 2^15`). The auto-generated
circuit (`Inputs`/`main`/`elaborated`) lives in the sibling `Extracted` module; the `populate_msb`
witness in `Populate`; the `FormalAssertion` contract (soundness/completeness/`circuit`) in `Formal`.

Mirrors `sp1/crates/core/machine/src/operations/msb.rs` (the `eval_msb` sends a single
`ByteOpcode::Range` lookup on `2*a - msb*2^16`); `Faithful/U16MSBOperation.lean` anchors this to the
extracted `constraints`. -/

namespace SP1Clean.U16MSBOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

instance : Fact (p > 2) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

omit [Fact p.Prime] in
/-- `16 < p`, so the `Range` byte-row width column `16` round-trips through `byteRowSpec_range`. -/
lemma h16p : (16 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega

/-- The booleanness + range form of the msb constraint (the literal meaning of the extracted
constraint list at `is_real = 1`), stated against the result column `cols.msb`. The range term
`2 * a - cols.msb * 65536` is `2*a - msb*2^16` (the auto-generated `main`'s normal form). -/
def RawSpec (a : ZMod p) (cols : Extracted.U16MSBOperation (ZMod p)) : Prop :=
  (cols.msb = 0 ∨ cols.msb = 1) ∧ (2 * a - cols.msb * 65536).val < 2 ^ 16

set_option maxHeartbeats 2000000 in
/-- Forward (soundness) core: booleanness + range force `msb` to be the high bit of `a`. -/
theorem msb_of_raw {a : ZMod p} {cols : Extracted.U16MSBOperation (ZMod p)}
    (ha : a.val < 2 ^ 16) (h_raw : RawSpec a cols) :
    cols.msb = if a.val ≥ 32768 then 1 else 0 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  obtain ⟨hbool, hr⟩ := h_raw
  have h2 : (2 * a : ZMod p).val = 2 * a.val := by
    rw [two_mul, ZMod.val_add_of_lt (by omega)]; omega
  rcases hbool with h0 | h1
  · rw [h0] at hr ⊢
    simp only [zero_mul, sub_zero] at hr
    rw [h2] at hr
    rw [if_neg (by omega)]
  · rw [h1] at hr ⊢
    simp only [one_mul] at hr
    have hge : a.val ≥ 32768 := by
      have hsum : (2 * a - 65536 : ZMod p) + 65536 = 2 * a := by ring
      have hbound : (2 * a - 65536 : ZMod p).val + (65536 : ZMod p).val < p := by
        rw [val_65536_zmod_p]; omega
      have hval := ZMod.val_add_of_lt hbound
      rw [hsum, h2, val_65536_zmod_p] at hval
      omega
    rw [if_pos hge]

end SP1Clean.U16MSBOperation
