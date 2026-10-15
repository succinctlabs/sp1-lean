import SP1Clean.Model.Semantics.DurationTime
import SP1Clean.Soundness.GenericWalk

/-! # The timeline determined by a State walk

A structurally valid row has a positive natural clock gap. Prefix-summing those gaps constructs
a total timeline and makes every row advance to its actual successor index. This is independent
of instruction decoding, event interpretation, and the trajectory subsequently grounded.
-/

namespace SP1Clean.Soundness.TimedGrounding

open SP1Clean.Semantics SP1Clean.Channels

variable {p : ℕ}

/-- The natural width of a row's State edge. -/
def rowDuration (row : RowFacts p) : ℕ :=
  StateMsg.timeNat row.statePush - StateMsg.timeNat row.statePull

/-- The State edges determine their own timeline; only the structural lower bound is needed. -/
noncomputable def rowTimeline (initialClock : ℕ) (rows : List (RowFacts p))
    (gap : ∀ row ∈ rows, StateMsg.timeNat row.statePull + 8 ≤ StateMsg.timeNat row.statePush) : Timeline :=
  Timeline.ofDurations initialClock (rows.map rowDuration) (by
    intro width member
    obtain ⟨row, rowMem, rfl⟩ := List.mem_map.mp member
    have bounded := gap row rowMem
    unfold rowDuration
    omega)

/-- The constructed timeline starts at the supplied public clock. -/
@[simp] theorem rowTimeline_start (initialClock : ℕ) (rows : List (RowFacts p))
    (gap : ∀ row ∈ rows, StateMsg.timeNat row.statePull + 8 ≤ StateMsg.timeNat row.statePush) :
    (rowTimeline initialClock rows gap).start 0 = initialClock := by
  exact Timeline.ofDurations_start_zero _ _ _

private theorem duration_step {rows : List (RowFacts p)}
    (gap : ∀ row ∈ rows, StateMsg.timeNat row.statePull + 8 ≤ StateMsg.timeNat row.statePush) :
    ∀ row ∈ rows, StateMsg.timeNat row.statePush = StateMsg.timeNat row.statePull + rowDuration row := by
  intro row member
  have bounded := gap row member
  unfold rowDuration
  omega

/-- A row at a known list position starts at that position's prefix-summed clock. -/
theorem rowTimeline_pullTime_of_getElem? [Fact p.Prime]
    {initial final : StateMsg (ZMod p)} {rows : List (RowFacts p)}
    (walk : Walk.IsWalk (fun row : RowFacts p => (row.statePull, row.statePush)) initial final rows)
    (gap : ∀ row ∈ rows, StateMsg.timeNat row.statePull + 8 ≤ StateMsg.timeNat row.statePush)
    {row : RowFacts p} {n : ℕ} (atIndex : rows[n]? = some row) :
    StateMsg.timeNat row.statePull = (rowTimeline (StateMsg.timeNat initial) rows gap).start n := by
  obtain ⟨bound, rfl⟩ := List.getElem?_eq_some_iff.mp atIndex
  have split : rows = rows.take n ++ rows[n] :: rows.drop (n + 1) := by
    rw [List.getElem_cons_drop, List.take_append_drop]
  have pull := statePullTime_of_stateWalk_durations _ rowDuration walk (duration_step gap)
    (rows.take n) rows[n] (rows.drop (n + 1)) split
  rw [rowTimeline, Timeline.ofDurations_start_le _ _ _ (by simpa using Nat.le_of_lt bound),
    ← List.map_take]
  exact pull

/-- Every row's State successor is the next index of the constructed timeline. -/
theorem rowTimeline_step_of_walk [Fact p.Prime]
    {initial final : StateMsg (ZMod p)} {rows : List (RowFacts p)}
    (walk : Walk.IsWalk (fun row : RowFacts p => (row.statePull, row.statePush)) initial final rows)
    (gap : ∀ row ∈ rows, StateMsg.timeNat row.statePull + 8 ≤ StateMsg.timeNat row.statePush) :
    ∀ row ∈ rows, ∀ n, StateMsg.timeNat row.statePull = (rowTimeline (StateMsg.timeNat initial) rows gap).start n →
      StateMsg.timeNat row.statePush = (rowTimeline (StateMsg.timeNat initial) rows gap).start (n + 1) := by
  intro row member n atIndex
  obtain ⟨done, suffix, rowsEq⟩ := List.append_of_mem member
  have pull := statePullTime_of_stateWalk_durations _ rowDuration walk (duration_step gap) done row suffix rowsEq
  have prefixLength : done.length ≤ (rows.map rowDuration).length := by
    simp only [List.length_map, rowsEq, List.length_append, List.length_cons]
    omega
  have prefixRows : ((rows.map rowDuration).take done.length) = done.map rowDuration := by
    rw [rowsEq, List.map_append, ← List.length_map (f := rowDuration) (as := done), List.take_left]
  have atPrefix : (rowTimeline (StateMsg.timeNat initial) rows gap).start done.length =
      StateMsg.timeNat initial + (done.map rowDuration).sum := by
    rw [rowTimeline, Timeline.ofDurations_start_le _ _ _ prefixLength, prefixRows]
  have increasing : StrictMono (rowTimeline (StateMsg.timeNat initial) rows gap).start :=
    fun _ _ less => Timeline.start_lt_of_lt _ less
  have injective := increasing.injective
  have index : n = done.length := injective (atIndex.symm.trans (pull.trans atPrefix.symm))
  subst n
  have nextPrefix : done.length + 1 ≤ (rows.map rowDuration).length := by
    simp only [List.length_map, rowsEq, List.length_append, List.length_cons]
    omega
  have next : ((rows.map rowDuration).take (done.length + 1)).sum =
      (done.map rowDuration).sum + rowDuration row := by
    rw [List.sum_take_succ _ _ (by omega), prefixRows]
    congr 1
    simp [rowsEq, List.getElem_append_right]
  rw [rowTimeline, Timeline.ofDurations_start_le _ _ _ nextPrefix, next]
  have step := duration_step gap row member
  omega

/-- The timeline's last covered index is exactly the public final State clock. -/
theorem rowTimeline_end_of_walk [Fact p.Prime]
    {initial final : StateMsg (ZMod p)} {rows : List (RowFacts p)}
    (walk : Walk.IsWalk (fun row : RowFacts p => (row.statePull, row.statePush)) initial final rows)
    (gap : ∀ row ∈ rows, StateMsg.timeNat row.statePull + 8 ≤ StateMsg.timeNat row.statePush) :
    (rowTimeline (StateMsg.timeNat initial) rows gap).start rows.length = StateMsg.timeNat final := by
  have count := clockCount_of_stateWalk_durations _ rowDuration walk (duration_step gap)
  rw [rowTimeline, ← List.length_map (f := rowDuration) (as := rows), Timeline.ofDurations_end]
  exact count

end SP1Clean.Soundness.TimedGrounding
