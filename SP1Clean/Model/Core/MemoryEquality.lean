import SP1Clean.Model.Core.Memory

/-! # Executable extensional equality of sparse memory

Comparing update-history lists is too strict, while comparing only a trace's accessed addresses
is too weak. It suffices to compare reads at the union of both histories' keys: every omitted
address has value zero on both sides. The check is finite even for the 48-bit native window.
-/

namespace SP1Clean.Model.Core.ByteMemory

/-- Compare a selected set of addresses using the union of both finite supports. -/
def agreesOn (left right : ByteMemory) (selected : ℕ → Bool) : Bool :=
  (left.entries ++ right.entries).all fun entry =>
    if selected entry.1 then left.read entry.1 == right.read entry.1 else true

theorem agreesOn_iff (left right : ByteMemory) (selected : ℕ → Bool) :
    left.agreesOn right selected = true ↔
      ∀ address, selected address = true → left.read address = right.read address := by
  rw [agreesOn, List.all_eq_true]
  constructor
  · intro checked address chosen
    by_cases present : ∃ entry ∈ left.entries ++ right.entries, entry.1 = address
    · obtain ⟨entry, member, equal⟩ := present
      simpa only [equal, chosen, ↓reduceIte, beq_iff_eq] using checked entry member
    · have absent : ∀ entry ∈ left.entries ++ right.entries, entry.1 ≠ address := by
        simpa only [not_exists, not_and] using present
      rw [left.read_eq_zero_of_absent address (fun entry member =>
        absent entry (List.mem_append_left _ member)),
        right.read_eq_zero_of_absent address (fun entry member =>
          absent entry (List.mem_append_right _ member))]
  · intro agrees entry _
    split
    next chosen => exact beq_iff_eq.mpr (agrees entry.1 chosen)
    next => rfl

/-- Compare all bytes below a limit using only the finite supports of the two memories. -/
def agreesBelow (left right : ByteMemory) (limit : ℕ) : Bool :=
  left.agreesOn right (fun address => decide (address < limit))

theorem agreesBelow_iff (left right : ByteMemory) (limit : ℕ) :
    left.agreesBelow right limit = true ↔
      ∀ address < limit, left.read address = right.read address := by
  simp only [agreesBelow, agreesOn_iff, decide_eq_true_eq]

end SP1Clean.Model.Core.ByteMemory
