import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

/-! # Numeric address ranges

A range is data, not a memory store or an execution model. Bytes use a half-open interval;
spans also admit an empty request at the upper endpoint, matching the host read policy.
Natural arithmetic checks the entire span before any narrowing to an architectural word.
-/

namespace SP1Clean.Model.Core

/-- Natural-number bounds for bytes and finite byte spans. -/
structure AddressRange where
  /-- Inclusive lower endpoint. -/
  lower : ℕ
  /-- Exclusive upper endpoint for nonempty byte membership. -/
  upper : ℕ
deriving DecidableEq, Repr, Inhabited

namespace AddressRange

/-- The endpoints occur in their intended order. -/
def Valid (range : AddressRange) : Prop := range.lower ≤ range.upper

/-- Membership of one byte in the half-open range. -/
abbrev Contains (range : AddressRange) (address : ℕ) : Prop :=
  range.lower ≤ address ∧ address < range.upper

/-- Full span containment, admitting an empty span at the upper endpoint. -/
abbrev ContainsSpan (range : AddressRange) (address length : ℕ) : Prop :=
  range.lower ≤ address ∧ address + length ≤ range.upper

instance (range : AddressRange) : Decidable range.Valid := inferInstanceAs (Decidable (_ ≤ _))
instance (range : AddressRange) (address : ℕ) : Decidable (range.Contains address) :=
  inferInstanceAs (Decidable (_ ∧ _))
instance (range : AddressRange) (address length : ℕ) : Decidable (range.ContainsSpan address length) :=
  inferInstanceAs (Decidable (_ ∧ _))

@[simp] theorem containsSpan_one (range : AddressRange) (address : ℕ) :
    range.ContainsSpan address 1 ↔ range.Contains address := by
  unfold ContainsSpan Contains
  omega

theorem ContainsSpan.valid {range : AddressRange} {address length : ℕ}
    (inside : range.ContainsSpan address length) : range.Valid := by
  unfold ContainsSpan Valid at *
  omega

theorem ContainsSpan.byte {range : AddressRange} {address length offset : ℕ}
    (inside : range.ContainsSpan address length) (bound : offset < length) :
    range.Contains (address + offset) := by
  unfold ContainsSpan Contains at *
  omega

theorem ContainsSpan.subspan {range : AddressRange} {address length offset count : ℕ}
    (inside : range.ContainsSpan address length) (bound : offset + count ≤ length) :
    range.ContainsSpan (address + offset) count := by
  unfold ContainsSpan at *
  omega

theorem ContainsSpan.mono {small large : AddressRange} {address length : ℕ}
    (inside : small.ContainsSpan address length)
    (lower : large.lower ≤ small.lower) (upper : small.upper ≤ large.upper) :
    large.ContainsSpan address length := ⟨Nat.le_trans lower inside.1, Nat.le_trans inside.2 upper⟩

end AddressRange
end SP1Clean.Model.Core
