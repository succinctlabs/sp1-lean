import SP1Clean.Model.Core.MemoryNormalization

/-! # Finite interval tables for sparse initial memory

A fixed lookup table cannot enumerate the native 48-bit address space. Constant-value intervals
represent zero-filled gaps and live bytes in one finite table. Normalize the update history to
sorted nonzero support before splitting intervals, so its size depends on represented memory.
The first binding still determines each byte; no prover-supplied nonmembership evidence or dense
memory enumeration is required.

Empty intervals are harmless: they contain no address and need no special padding semantics.
-/

namespace SP1Clean.Model.Core

/-- A constant byte value on a half-open address interval. -/
structure MemoryInterval where
  lower : ℕ
  upper : ℕ
  value : BitVec 8
deriving DecidableEq, Repr

namespace MemoryInterval

def Contains (interval : MemoryInterval) (address : ℕ) : Prop :=
  interval.lower ≤ address ∧ address < interval.upper

instance (interval : MemoryInterval) (address : ℕ) : Decidable (interval.Contains address) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Replace one byte while retaining the intervals on both sides. Out-of-range writes have
no effect on this interval. -/
def write (interval : MemoryInterval) (address : ℕ) (value : BitVec 8) : List MemoryInterval :=
  if interval.Contains address then
    [⟨interval.lower, address, interval.value⟩, ⟨address, address + 1, value⟩,
      ⟨address + 1, interval.upper, interval.value⟩]
  else [interval]

/-- Every new interval remains inside its source and has exactly the updated byte value. -/
theorem write_sound (interval : MemoryInterval) (address query : ℕ) (value : BitVec 8)
    (next : MemoryInterval) (member : next ∈ interval.write address value)
    (inside : next.Contains query) :
    interval.Contains query ∧ next.value = if address = query then value else interval.value := by
  unfold write at member
  split at member
  · next contains =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      all_goals simp only [Contains] at contains inside ⊢
      · exact ⟨by omega, by rw [if_neg (by omega)]⟩
      · exact ⟨by omega, by rw [if_pos (by omega)]⟩
      · exact ⟨by omega, by rw [if_neg (by omega)]⟩
  · next outside =>
      obtain rfl := List.mem_singleton.mp member
      exact ⟨inside, by rw [if_neg (by intro equal; subst query; exact outside inside)]⟩

/-- Splitting an interval loses no address. -/
theorem write_complete (interval : MemoryInterval) (address query : ℕ) (value : BitVec 8)
    (inside : interval.Contains query) :
    ∃ next ∈ interval.write address value, next.Contains query := by
  unfold write
  split
  · next contains =>
      rcases lt_trichotomy query address with before | equal | after
      · exact ⟨⟨interval.lower, address, interval.value⟩, by simp, inside.1, before⟩
      · subst query
        exact ⟨⟨address, address + 1, value⟩, by simp, le_rfl, Nat.lt_succ_self _⟩
      · exact ⟨⟨address + 1, interval.upper, interval.value⟩, by simp,
          (show address + 1 ≤ query by omega), inside.2⟩
  · exact ⟨interval, by simp, inside⟩

/-- Exactly one child contains each address in the source interval. -/
theorem write_count (interval : MemoryInterval) (address query : ℕ) (value : BitVec 8) :
    (interval.write address value).countP (fun next => decide (next.Contains query)) =
      if interval.Contains query then 1 else 0 := by
  unfold write
  split
  · next inside =>
      simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq]
      split_ifs <;> simp only [Contains] at * <;> omega
  · simp

private theorem write_length (interval : MemoryInterval) (address : ℕ) (value : BitVec 8) :
    (interval.write address value).length = 1 + 2 * if interval.Contains address then 1 else 0 := by
  unfold write
  split <;> simp_all

theorem writes_count (intervals : List MemoryInterval) (address query : ℕ) (value : BitVec 8) :
    (intervals.flatMap (fun interval => interval.write address value)).countP
      (fun interval => decide (interval.Contains query)) =
    intervals.countP (fun interval => decide (interval.Contains query)) := by
  induction intervals with
  | nil => rfl
  | cons interval rest ih =>
      simp only [List.flatMap_cons, List.countP_append, write_count, ih, List.countP_cons,
        decide_eq_true_eq]
      omega

theorem writes_length (intervals : List MemoryInterval) (address : ℕ) (value : BitVec 8) :
    (intervals.flatMap (fun interval => interval.write address value)).length =
      intervals.length + 2 * intervals.countP (fun interval => decide (interval.Contains address)) := by
  induction intervals with
  | nil => rfl
  | cons interval rest ih =>
      simp only [List.flatMap_cons, List.length_append, write_length, ih, List.length_cons,
        List.countP_cons, decide_eq_true_eq]
      omega

/-- Splitting preserves the fixed address-space bounds, even for empty children. -/
theorem write_bounds (interval : MemoryInterval) (address limit : ℕ) (value : BitVec 8)
    (bounds : interval.lower ≤ interval.upper ∧ interval.upper ≤ limit)
    (next : MemoryInterval) (member : next ∈ interval.write address value) :
    next.lower ≤ next.upper ∧ next.upper ≤ limit := by
  unfold write at member
  split at member
  · next inside =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      all_goals simp only [Contains] at inside; dsimp only; omega
  · obtain rfl := List.mem_singleton.mp member
    exact bounds

end MemoryInterval

namespace ByteMemory

private def intervalRows (limit : ℕ) : List (ℕ × BitVec 8) → List MemoryInterval
  | [] => [⟨0, limit, 0⟩]
  | (address, value) :: rest =>
      (intervalRows limit rest).flatMap (fun interval => interval.write address value)

/-- A finite, concrete table realizing sparse memory throughout the bounded address space. -/
private def rawIntervals (memory : ByteMemory) (limit : ℕ) : List MemoryInterval :=
  intervalRows limit memory.entries

/-- Every in-range address belongs to exactly one table row; out-of-range addresses belong to none. -/
private theorem rawIntervals_count (memory : ByteMemory) (limit query : ℕ) :
    (memory.rawIntervals limit).countP (fun interval => decide (interval.Contains query)) =
      if query < limit then 1 else 0 := by
  rcases memory with ⟨entries⟩
  change (intervalRows limit entries).countP _ = _
  induction entries with
  | nil => simp [intervalRows, MemoryInterval.Contains]
  | cons entry rest ih =>
      rw [intervalRows, MemoryInterval.writes_count, ih]

/-- The fixed table grows with the supplied sparse image, not the size of the address space. -/
private theorem rawIntervals_length_le (memory : ByteMemory) (limit : ℕ) :
    (memory.rawIntervals limit).length ≤ 2 * memory.entries.length + 1 := by
  rcases memory with ⟨entries⟩
  change (intervalRows limit entries).length ≤ 2 * entries.length + 1
  induction entries with
  | nil => simp [intervalRows]
  | cons entry rest ih =>
      rw [intervalRows, MemoryInterval.writes_length]
      have count := (ByteMemory.mk rest).rawIntervals_count limit entry.1
      change (intervalRows limit rest).countP _ = _ at count
      rw [count]
      simp only [List.length_cons]
      split <;> omega

/-- Every endpoint fits the chosen address-space bound. -/
private theorem rawIntervals_bounds (memory : ByteMemory) (limit : ℕ) (interval : MemoryInterval)
    (member : interval ∈ memory.rawIntervals limit) :
    interval.lower ≤ interval.upper ∧ interval.upper ≤ limit := by
  rcases memory with ⟨entries⟩
  change interval ∈ intervalRows limit entries at member
  induction entries generalizing interval with
  | nil =>
      obtain rfl := List.mem_singleton.mp member
      exact ⟨Nat.zero_le _, le_rfl⟩
  | cons entry rest ih =>
      obtain ⟨source, sourceMem, nextMem⟩ := List.mem_flatMap.mp member
      exact source.write_bounds entry.1 limit entry.2 (ih source sourceMem) interval nextMem

/-- Lookup membership and interval containment imply the exact canonical memory value. -/
private theorem rawIntervals_sound (memory : ByteMemory) (limit : ℕ) (interval : MemoryInterval)
    (member : interval ∈ memory.rawIntervals limit) (query : ℕ) (inside : interval.Contains query) :
    query < limit ∧ memory.read query = interval.value := by
  rcases memory with ⟨entries⟩
  change interval ∈ intervalRows limit entries at member
  induction entries generalizing interval with
  | nil =>
      obtain rfl := List.mem_singleton.mp member
      exact ⟨inside.2, rfl⟩
  | cons entry rest ih =>
      obtain ⟨source, sourceMem, nextMem⟩ := List.mem_flatMap.mp member
      have split := source.write_sound entry.1 query entry.2 interval nextMem inside
      have prior := ih source split.1 sourceMem
      refine ⟨prior.1, ?_⟩
      change ((ByteMemory.mk rest).write entry.1 entry.2).read query = interval.value
      rw [read_write, prior.2, split.2]

/-- Every in-range address has a lookup row. Table generation therefore adds no execution-
dependent readiness condition to memory initialization. -/
private theorem rawIntervals_complete (memory : ByteMemory) (limit query : ℕ) (inside : query < limit) :
    ∃ interval ∈ memory.rawIntervals limit, interval.Contains query := by
  rcases memory with ⟨entries⟩
  change ∃ interval ∈ intervalRows limit entries, interval.Contains query
  induction entries with
  | nil => exact ⟨⟨0, limit, 0⟩, by simp [intervalRows], Nat.zero_le _, inside⟩
  | cons entry rest ih =>
      obtain ⟨interval, member, contains⟩ := ih
      obtain ⟨next, nextMem, nextContains⟩ := interval.write_complete entry.1 query entry.2 contains
      exact ⟨next, List.mem_flatMap.mpr ⟨interval, member, nextMem⟩, nextContains⟩

/-- Fixed intervals depend on live memory, not its update history. -/
def intervals (memory : ByteMemory) (limit : ℕ) : List MemoryInterval :=
  (memory.canonicalBelow limit).rawIntervals limit

/-- Every bounded address belongs to exactly one interval, including zero-filled gaps. -/
theorem intervals_count (memory : ByteMemory) (limit query : ℕ) :
    (memory.intervals limit).countP (fun interval => decide (interval.Contains query)) =
      if query < limit then 1 else 0 :=
  (memory.canonicalBelow limit).rawIntervals_count limit query

/-- The interval inventory is bounded by semantic live-byte support. -/
theorem intervals_length_le (memory : ByteMemory) (limit : ℕ) :
    (memory.intervals limit).length ≤ 2 * (memory.supportBelow limit).card + 1 := by
  have bound := (memory.canonicalBelow limit).rawIntervals_length_le limit
  simpa only [intervals, canonicalBelow_length] using bound

/-- Every endpoint fits the chosen address-space bound. -/
theorem intervals_bounds (memory : ByteMemory) (limit : ℕ) (interval : MemoryInterval)
    (member : interval ∈ memory.intervals limit) :
    interval.lower ≤ interval.upper ∧ interval.upper ≤ limit :=
  (memory.canonicalBelow limit).rawIntervals_bounds limit interval member

/-- Fixed-row membership and containment establish the original memory's byte value. -/
theorem intervals_sound (memory : ByteMemory) (limit : ℕ) (interval : MemoryInterval)
    (member : interval ∈ memory.intervals limit) (query : ℕ) (inside : interval.Contains query) :
    query < limit ∧ memory.read query = interval.value := by
  have facts := (memory.canonicalBelow limit).rawIntervals_sound limit interval member query inside
  exact ⟨facts.1, by simpa only [canonicalBelow_read, if_pos facts.1] using facts.2⟩

/-- Normalization loses no address and adds no caller readiness condition. -/
theorem intervals_complete (memory : ByteMemory) (limit query : ℕ) (inside : query < limit) :
    ∃ interval ∈ memory.intervals limit, interval.Contains query :=
  (memory.canonicalBelow limit).rawIntervals_complete limit query inside

/-- Finite interval lookup characterizes the memory function exactly. -/
theorem intervals_iff (memory : ByteMemory) (limit query : ℕ) (value : BitVec 8) :
    (∃ interval ∈ memory.intervals limit, interval.Contains query ∧ interval.value = value) ↔
      query < limit ∧ memory.read query = value := by
  constructor
  · rintro ⟨interval, member, inside, rfl⟩
    exact memory.intervals_sound limit interval member query inside
  · rintro ⟨inside, valueEq⟩
    obtain ⟨interval, member, contains⟩ := memory.intervals_complete limit query inside
    exact ⟨interval, member, contains,
      (memory.intervals_sound limit interval member query contains).2.symm.trans valueEq⟩

/-- Executable lookup-row selection for the witness compiler. -/
def intervalAt? (memory : ByteMemory) (limit query : ℕ) : Option MemoryInterval :=
  (memory.intervals limit).find? (fun interval => decide (interval.Contains query))

theorem intervalAt?_sound (memory : ByteMemory) (limit query : ℕ) (interval : MemoryInterval)
    (found : memory.intervalAt? limit query = some interval) :
    interval ∈ memory.intervals limit ∧ interval.Contains query ∧
      query < limit ∧ memory.read query = interval.value := by
  have member := List.mem_of_find?_eq_some found
  have contains : interval.Contains query := by simpa using List.find?_some found
  exact ⟨member, contains, memory.intervals_sound limit interval member query contains⟩

/-- The executable selector succeeds exactly on the semantic address window. -/
theorem intervalAt?_isSome_iff (memory : ByteMemory) (limit query : ℕ) :
    (memory.intervalAt? limit query).isSome = true ↔ query < limit := by
  constructor
  · intro present
    obtain ⟨interval, found⟩ := Option.isSome_iff_exists.mp present
    exact (memory.intervalAt?_sound limit query interval found).2.2.1
  · intro inside
    obtain ⟨interval, member, contains⟩ := memory.intervals_complete limit query inside
    cases found : memory.intervalAt? limit query with
    | none =>
        have := List.find?_eq_none.mp found interval member
        simp [contains] at this
    | some interval => rfl

end ByteMemory

end SP1Clean.Model.Core
