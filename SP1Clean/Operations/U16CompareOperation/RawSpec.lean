import SP1Clean.Foundations.Word
import SP1Clean.Extracted.U16CompareOperation
import Mathlib.Tactic.LinearCombination

/-! # `U16CompareOperation` — the arithmetic core (`RawSpec` + the order lemma)

The structural booleanness + range form `RawSpec` (the literal meaning of SP1's `U16CompareOperation`
constraint list at `is_real = 1`, stated against the result column `cols.bit`), and the native order
lemma `compare_of_raw` the gadget's soundness routes through: `bit` boolean + `(a - b + bit·2^16)` a
genuine 16-bit value force `bit = (a < b)`. The auto-generated circuit (`Inputs`/`main`/`elaborated`)
lives in the sibling `Extracted` module; the `populate_bit` witness in `Populate`; the `FormalAssertion`
contract (soundness/completeness/`circuit`) in `Formal`. -/

namespace SP1Clean.U16CompareOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact p.Prime] in
/-- `16 < p`, so the `Range` byte-row width column `16` round-trips through `byteRowSpec_range`. -/
lemma h16p : (16 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega

/-- The literal meaning of SP1's `U16CompareOperation` constraint list at `is_real = 1`: `bit` is
boolean and `(a - b) + bit * 2^16` is a genuine 16-bit value. -/
def RawSpec (a b : ZMod p) (cols : Extracted.U16CompareOperation (ZMod p)) : Prop :=
  (cols.bit = 0 ∨ cols.bit = 1) ∧ (a - b + cols.bit * 65536).val < 2 ^ 16

/-- Soundness core: `bit` boolean + `(a - b + bit·2^16)` a genuine 16-bit value force `bit = (a < b)`. -/
theorem compare_of_raw {a b : ZMod p} {cols : Extracted.U16CompareOperation (ZMod p)}
    (ha : a.val < 2 ^ 16) (hb : b.val < 2 ^ 16) (h_raw : RawSpec a b cols) :
    cols.bit = if a.val < b.val then 1 else 0 := by
  obtain ⟨hbit, hlt⟩ := h_raw
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  set v := (a - b + cols.bit * 65536).val with hv_def
  have hcong : (v : ZMod p) = a - b + cols.bit * 65536 := by rw [hv_def, ZMod.natCast_zmod_val]
  have ea : ((a.val : ℕ) : ZMod p) = a := ZMod.natCast_zmod_val a
  have eb : ((b.val : ℕ) : ZMod p) = b := ZMod.natCast_zmod_val b
  rcases hbit with h0 | h1
  · rw [h0] at hcong
    have e : ((a.val : ℕ) : ZMod p) = ((b.val + v : ℕ) : ZMod p) := by
      rw [ea]; push_cast; rw [eb]; linear_combination -hcong
    have hnat : a.val = b.val + v := by
      have hval := congrArg ZMod.val e
      rwa [ZMod.val_natCast_of_lt (show a.val < p by omega),
        ZMod.val_natCast_of_lt (show b.val + v < p by omega)] at hval
    rw [h0, if_neg (show ¬ a.val < b.val by omega)]
  · rw [h1] at hcong
    have e : ((a.val + 65536 : ℕ) : ZMod p) = ((b.val + v : ℕ) : ZMod p) := by
      push_cast; rw [ea, eb]; linear_combination -hcong
    have hnat : a.val + 65536 = b.val + v := by
      have hval := congrArg ZMod.val e
      rwa [ZMod.val_natCast_of_lt (show a.val + 65536 < p by omega),
        ZMod.val_natCast_of_lt (show b.val + v < p by omega)] at hval
    rw [h1, if_pos (show a.val < b.val by omega)]

end SP1Clean.U16CompareOperation
