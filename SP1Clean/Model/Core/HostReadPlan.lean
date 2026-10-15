import SP1Clean.Model.Core.MemorySpan
import Mathlib.Data.List.Perm.Basic

/-! # Physical reads for one or two host buffers

There is one physical row per covered cell. Its sharing bit is computed from membership in
both spans; expanding the rows into logical reads recovers exactly the two buffer inventories,
including their overlap. WRITE uses an empty second span, and VERIFY_SP1_PROOF uses both.
This plan does not authenticate the buffers' addresses or their bytes.
-/

namespace SP1Clean.Model.Core.HostReadPlan

structure Entry where
  cell : ℕ
  shared : Bool
deriving DecidableEq, Repr

def ofSpans (first second : MemorySpan) : List Entry :=
  (MemorySpan.unionCells [first, second]).map fun cell =>
    ⟨cell, decide (cell ∈ first.cells ∧ cell ∈ second.cells)⟩

def logicalCells (entries : List Entry) : List ℕ :=
  entries.flatMap fun entry => if entry.shared then [entry.cell, entry.cell] else [entry.cell]

theorem physical_cells (first second : MemorySpan) :
    (ofSpans first second).map Entry.cell = MemorySpan.unionCells [first, second] := by
  simp [ofSpans, List.map_map, Function.comp_def]

/-- Sharing never duplicates a physical Memory access. -/
theorem physical_nodup (first second : MemorySpan) :
    ((ofSpans first second).map Entry.cell).Nodup := by
  rw [physical_cells]
  exact MemorySpan.nodup_unionCells _

private theorem logical_count (cells : List ℕ) (shared : ℕ → Bool) (cell : ℕ) :
    (logicalCells (cells.map fun value => ⟨value, shared value⟩)).count cell =
      (if shared cell then 2 else 1) * cells.count cell := by
  unfold logicalCells
  induction cells with
  | nil => simp
  | cons value cells ih =>
    by_cases equal : value = cell
    · subst value
      cases flag : shared cell with
      | false => simp [flag, ih]
      | true =>
        simp [flag, ih, Nat.mul_add]
    · cases flag : shared value <;>
        simp [flag, ih, equal]

/-- The actual one-or-two read multiplicities recover both requested cell lists exactly. -/
theorem logical_cells_perm (first second : MemorySpan) :
    (logicalCells (ofSpans first second)).Perm (first.cells ++ second.cells) := by
  apply List.perm_iff_count.mpr
  intro cell
  rw [ofSpans, logical_count, List.count_append,
    (MemorySpan.nodup_unionCells _).count,
    first.nodup_cells.count, second.nodup_cells.count]
  by_cases left : cell ∈ first.cells <;> by_cases right : cell ∈ second.cells <;>
    simp [MemorySpan.mem_unionCells, left, right]

end SP1Clean.Model.Core.HostReadPlan
