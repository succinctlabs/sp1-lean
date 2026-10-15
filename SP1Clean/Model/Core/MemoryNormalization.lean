import SP1Clean.Model.Core.MemorySupport
import Mathlib.Data.Finset.Sort

/-! # Canonical sparse memory for fixed-table construction

Execution memory retains update history. Fixed tables instead need a deterministic image whose
size reflects live bytes, independently of duplicate writes, explicit zeros and out-of-window
history. Normalization preserves every read below the supplied limit and enumerates only the
already finite nonzero support; it never traverses the architectural address space.
-/

namespace SP1Clean.Model.Core.ByteMemory

/-- Increasing live addresses paired with their final byte values, each appearing once. -/
def canonicalBelow (memory : ByteMemory) (limit : ℕ) : ByteMemory :=
  ⟨((memory.supportBelow limit).sort (· ≤ ·)).map fun address => (address, memory.read address)⟩

/-- The normalized representation has exactly the semantic number of live bytes. -/
theorem canonicalBelow_length (memory : ByteMemory) (limit : ℕ) :
    (memory.canonicalBelow limit).entries.length = (memory.supportBelow limit).card := by
  simp [canonicalBelow]

/-- Normalization preserves every bounded read and clears only addresses outside its window. -/
theorem canonicalBelow_read (memory : ByteMemory) (limit address : ℕ) :
    (memory.canonicalBelow limit).read address =
      if address < limit then memory.read address else 0 := by
  by_cases live : address ∈ memory.supportBelow limit
  · rw [if_pos ((mem_supportBelow memory limit address).mp live).1]
    apply read_eq_of_mem
    · exact List.mem_map.mpr ⟨address, (Finset.mem_sort (· ≤ ·)).mpr live, rfl⟩
    · intro entry member same
      obtain ⟨key, _, rfl⟩ := List.mem_map.mp member
      exact congrArg memory.read same
  · have absent : (memory.canonicalBelow limit).read address = 0 := by
      apply read_eq_zero_of_absent
      intro entry member same
      obtain ⟨key, present, rfl⟩ := List.mem_map.mp member
      exact live (same ▸ (Finset.mem_sort (· ≤ ·)).mp present)
    rw [absent]
    split
    · next bounded =>
        by_contra nonzero
        exact live ((mem_supportBelow memory limit address).mpr ⟨bounded, Ne.symm nonzero⟩)
    · rfl

/-- Equivalent bounded memories produce the same canonical image, regardless of history. -/
theorem canonicalBelow_congr {left right : ByteMemory} {limit : ℕ}
    (same : left.agreesBelow right limit = true) :
    left.canonicalBelow limit = right.canonicalBelow limit := by
  unfold canonicalBelow
  rw [supportBelow_congr same]
  congr 1
  apply List.map_congr_left
  intro address present
  have bounded := ((mem_supportBelow right limit address).mp
    ((Finset.mem_sort (· ≤ ·)).mp present)).1
  rw [(agreesBelow_iff left right limit).mp same address bounded]

end SP1Clean.Model.Core.ByteMemory
