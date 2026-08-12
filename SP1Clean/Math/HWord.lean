import Clean.Circuit.Basic
import Clean.Utils.Field
import Mathlib.Tactic.LinearCombination

/-! # Minimal half-word (32-bit) foundation

A trimmed 2-limb companion to `Math/Word.lean`. An `HWord` is two little-endian 16-bit limbs
of a field element; `toBitVec32` reassembles the 32-bit value. Only the surface the SLLW shift core
needs is kept: `isU32`, `toNat`, `toBitVec32`, the load-bearing `toBitVec32_toNat`, and their
small case/bound helper lemmas. The 32→64
sign-extension fill is **not** re-derived here — the SLLW assembly reuses
`Word.toBitVec64_signExtend_word` (`Math/Word.lean`) on the four-limb output word
directly. -/

namespace SP1Clean

variable {p : ℕ}

/-- A 32-bit value as two little-endian 16-bit limbs. -/
abbrev HWord (F : Type) := Vector F 2

namespace HWord

/-- Each limb is a genuine 16-bit value. -/
def isU32 [NeZero p] (w : HWord (ZMod p)) : Prop :=
  ∀ i : Fin 2, w[i].val < 2 ^ 16

lemma isU32_of_cases [NeZero p] {w : HWord (ZMod p)}
    (h0 : w[0].val < 2 ^ 16) (h1 : w[1].val < 2 ^ 16) : w.isU32 := by
  intro i; fin_cases i <;> simpa [isU32]

lemma lt_cases_of_isU32 [NeZero p] {w : HWord (ZMod p)} (hw : w.isU32) :
    w[0].val < 2 ^ 16 ∧ w[1].val < 2 ^ 16 :=
  ⟨hw 0, hw 1⟩

/-- Little-endian reassembly to `ℕ`. -/
def toNat [NeZero p] (w : HWord (ZMod p)) : ℕ :=
  w[0].val + w[1].val * 2 ^ 16

lemma toNat_def [NeZero p] (w : HWord (ZMod p)) :
    w.toNat = w[0].val + w[1].val * 2 ^ 16 := rfl

lemma toNat_lt_of_isU32 [NeZero p] {w : HWord (ZMod p)} (hw : w.isU32) : w.toNat < 2 ^ 32 := by
  have := lt_cases_of_isU32 hw
  simp only [toNat]; omega

/-- The 32-bit value of the half-word. -/
def toBitVec32 [NeZero p] (w : HWord (ZMod p)) : BitVec 32 :=
  BitVec.ofNat 32 (toNat w)

lemma toBitVec32_toNat [NeZero p] {w : HWord (ZMod p)} (hw : w.isU32) :
    w.toBitVec32.toNat = w.toNat := by
  simp only [toBitVec32, BitVec.toNat_ofNat, toNat]
  have := lt_cases_of_isU32 hw
  omega

end HWord

end SP1Clean
