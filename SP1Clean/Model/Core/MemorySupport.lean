import SP1Clean.Model.Core.MemoryEquality
import Mathlib.Data.Finset.Card

/-! # Canonical sparse boundary size

Only live nonzero bytes in the represented address domain contribute. Duplicate writes,
shadowed values, explicit zeros and out-of-domain history do not increase the count.
-/

namespace SP1Clean.Model.Core.ByteMemory

/-- The finite nonzero support of the represented memory, independent of update history. -/
def supportBelow (memory : ByteMemory) (limit : ℕ) : Finset ℕ :=
  memory.entries.toFinset.image Prod.fst |>.filter
    (fun address => address < limit ∧ memory.read address ≠ 0)

/-- Live addresses cannot outnumber the supplied bindings, even with duplicates and zeros. -/
theorem supportBelow_card_le (memory : ByteMemory) (limit : ℕ) :
    (memory.supportBelow limit).card ≤ memory.entries.length :=
  (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans (List.toFinset_card_le _))

@[simp] theorem mem_supportBelow (memory : ByteMemory) (limit address : ℕ) :
    address ∈ memory.supportBelow limit ↔ address < limit ∧ memory.read address ≠ 0 := by
  simp only [supportBelow, Finset.mem_filter]
  constructor
  · exact And.right
  · intro live
    refine ⟨?_, live⟩
    by_contra absent
    have zero := memory.read_eq_zero_of_absent address (by
      intro entry member equal
      exact absent (Finset.mem_image.mpr ⟨entry, List.mem_toFinset.mpr member, equal⟩))
    exact live.2 zero

/-- Equivalent finite boundaries have the same canonical support, not merely the same size. -/
theorem supportBelow_congr {left right : ByteMemory} {limit : ℕ}
    (same : left.agreesBelow right limit = true) :
    left.supportBelow limit = right.supportBelow limit := by
  apply Finset.ext
  intro address
  simp only [mem_supportBelow]
  by_cases bounded : address < limit
  · rw [(agreesBelow_iff _ _ _).mp same address bounded]
  · simp only [bounded, false_and]

end SP1Clean.Model.Core.ByteMemory
