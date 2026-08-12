import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! # Binary-field gates and BitVec comparisons

Field-generic helper lemmas for **binary (boolean) field elements** (`x = 0 ∨ x = 1`) and the two
`BitVec` order comparisons (`slt`/`ult`). These recur in the chip decision/selector proofs (Branch's
signed/unsigned branch decision, Lt's flag selectors); collected here so any chip can reuse them
rather than re-proving a private copy. Pure `ZMod p` / `BitVec` facts — no SP1-specific or circuit
dependency. -/

namespace SP1Clean

variable {p : ℕ}

/-- A boolean field element has `val ≤ 1`. -/
lemma bool_val_le [Fact p.Prime] {x : ZMod p} (h : x = 0 ∨ x = 1) : x.val ≤ 1 := by
  rcases h with h | h <;> simp [h, ZMod.val_one]

/-- A gated byte pull/push leaves an off-gate `Requirements` conjunct on a reader/operation/chip
soundness goal under Clean `main` (post-`cedc171b`): `¬-x = -1 → ¬x = 0 → channel.Guarantees …`,
where `x` is the `is_real` gate. It is **vacuous** under the binary gate `x = 0 ∨ x = 1` — the two
hypotheses are jointly contradictory (`x = 1` forces `-x = -1`; `x = 0` is excluded) — so any `P`
follows. Lets each such conjunct close as `fun h1 h0 => off_gate_vacuous hbin h1 h0`. -/
lemma off_gate_vacuous {x : ZMod p} (h : x = 0 ∨ x = 1) {P : Prop}
    (h1 : ¬-x = -1) (h0 : ¬x = 0) : P := by
  rcases h with h | h
  · exact absurd h h0
  · exact absurd (by rw [h]) h1

/-- Distinct field elements have distinct `val`s. -/
lemma val_ne [NeZero p] {x y : ZMod p} (h : x ≠ y) : x.val ≠ y.val := fun hv =>
  h (by rw [← ZMod.natCast_zmod_val x, ← ZMod.natCast_zmod_val y, hv])

/-- A field element equal to `if P then 1 else 0` is `1` iff `P` holds. -/
lemma eq_one_iff_of_ite [Fact p.Prime] {x : ZMod p} {P : Prop} [Decidable P]
    (h : x = if P then 1 else 0) : x = 1 ↔ P := by
  by_cases hP : P <;> simp [h, hP]

/-- A field element equal to `1 - (if P then 1 else 0)` is `1` iff `P` fails. -/
lemma eq_one_iff_of_one_sub_ite [Fact p.Prime] {x : ZMod p} {P : Prop} [Decidable P]
    (h : x = 1 - (if P then 1 else 0)) : x = 1 ↔ ¬ P := by
  by_cases hP : P <;> simp [h, hP]

/-- A binary `x` with `x = 1 ↔ P` is `if P then 1 else 0` (completeness direction of
`eq_one_iff_of_ite`). -/
lemma bool_eq_ite_of_iff {x : ZMod p} (hx : x = 0 ∨ x = 1) {P : Prop} [Decidable P]
    (h : x = 1 ↔ P) : x = if P then 1 else 0 := by
  by_cases hP : P
  · rw [if_pos hP]; exact h.mpr hP
  · rw [if_neg hP]; exact hx.resolve_right fun h1 => hP (h.mp h1)

/-- A binary `x` with `x = 1 ↔ y = 0` (for binary `y`) is `1 - y`. -/
lemma bool_eq_one_sub [Fact p.Prime] {x y : ZMod p} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1)
    (h : x = 1 ↔ y = 0) : x = 1 - y := by
  rcases hy with rfl | rfl
  · rw [sub_zero]; exact h.mpr rfl
  · rw [sub_self]; exact hx.resolve_right fun hx1 => one_ne_zero (h.mp hx1)

/-- `BitVec.slt` as a signed-`toInt` comparison. -/
lemma slt_true_iff {w : ℕ} (x y : BitVec w) : x.slt y = true ↔ x.toInt < y.toInt := by
  simp [BitVec.slt]

/-- `BitVec.slt` false as the negated signed comparison. -/
lemma slt_false_iff {w : ℕ} (x y : BitVec w) : x.slt y = false ↔ ¬ x.toInt < y.toInt := by
  simp [BitVec.slt]

/-- `BitVec.ult` as an unsigned-`toNat` comparison. -/
lemma ult_true_iff {w : ℕ} (x y : BitVec w) : x.ult y = true ↔ x.toNat < y.toNat := by
  simp [BitVec.ult]

/-- `BitVec.ult` false as the negated unsigned comparison. -/
lemma ult_false_iff {w : ℕ} (x y : BitVec w) : x.ult y = false ↔ ¬ x.toNat < y.toNat := by
  simp [BitVec.ult]

end SP1Clean
