import SP1Clean.Model.Semantics.MicroTime
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! # Timelines for finite lists of execution widths

A mixed execution list determines its clock by prefix-summing row widths. Past the list, the
clock advances by eight solely to totalize the timeline. This construction needs no instruction
or host-event interpretation; each physical row's duration can be justified separately.
-/

namespace SP1Clean.Semantics.Timeline

/-- The prefix-summed clock of a finite width list, with eight-tick padding after its end. -/
def ofDurations (initialClock : ℕ) (widths : List ℕ) (bounded : ∀ width ∈ widths, 8 ≤ width) : Timeline where
  start n := initialClock + (widths.take n).sum + 8 * (n - widths.length)
  gap n := by
    by_cases inside : n < widths.length
    · have width := bounded widths[n] (List.getElem_mem inside)
      rw [List.sum_take_succ widths n inside]
      have current : n - widths.length = 0 := by omega
      have next : n + 1 - widths.length = 0 := by omega
      rw [current, next]
      omega
    · rw [List.take_of_length_le (by omega : widths.length ≤ n),
        List.take_of_length_le (by omega : widths.length ≤ n + 1)]
      omega

/-- Inside the list, the clock is its ordinary prefix sum. -/
theorem ofDurations_start_le (initialClock : ℕ) (widths : List ℕ) (bounded : ∀ width ∈ widths, 8 ≤ width)
    {n : ℕ} (inside : n ≤ widths.length) :
    (ofDurations initialClock widths bounded).start n = initialClock + (widths.take n).sum := by
  simp only [ofDurations, Nat.sub_eq_zero_of_le inside, Nat.mul_zero, Nat.add_zero]

/-- The initial clock is unchanged, including for an empty list. -/
@[simp] theorem ofDurations_start_zero (initialClock : ℕ) (widths : List ℕ)
    (bounded : ∀ width ∈ widths, 8 ≤ width) :
    (ofDurations initialClock widths bounded).start 0 = initialClock := by
  simp [ofDurations]

/-- A covered row advances by exactly its supplied duration. -/
theorem ofDurations_step (initialClock : ℕ) (widths : List ℕ) (bounded : ∀ width ∈ widths, 8 ≤ width)
    {n : ℕ} (inside : n < widths.length) :
    (ofDurations initialClock widths bounded).start (n + 1) =
      (ofDurations initialClock widths bounded).start n + widths[n] := by
  rw [ofDurations_start_le _ _ _ (by omega), ofDurations_start_le _ _ _ inside.le,
    List.sum_take_succ widths n inside, Nat.add_assoc]

/-- The final covered clock is the sum of all supplied widths. -/
@[simp] theorem ofDurations_end (initialClock : ℕ) (widths : List ℕ) (bounded : ∀ width ∈ widths, 8 ≤ width) :
    (ofDurations initialClock widths bounded).start widths.length = initialClock + widths.sum := by
  simp [ofDurations]

end SP1Clean.Semantics.Timeline
