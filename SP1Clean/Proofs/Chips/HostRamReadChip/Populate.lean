import SP1Clean.Proofs.Chips.HostRamReadChip.Formal
import SP1Clean.Proofs.Chips.HostRamAccessChip.Populate
import SP1Clean.Model.Core.HostReadPlan

/-! # Constructing shared host RAM reads

The constructor preserves the prior word and computes every timestamp column. The span
constructor uses the semantic plan's distinct physical cells and computed sharing bits.
The supplying Memory history remains responsible for the prior record at each cell.
-/

namespace SP1Clean.HostRamReadChip

open Circuit Channels Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

def populate (prior : MemoryMsg (ZMod p)) (clkHigh clk0 clk1 : ZMod p)
    (shared : Bool) : Inputs (ZMod p) :=
  ⟨HostRamAccessChip.populate prior clkHigh clk0 clk1 prior.value, if shared then 1 else 0⟩

theorem populate_assumptions (prior : MemoryMsg (ZMod p)) (clkHigh clk0 clk1 : ZMod p)
    (shared : Bool) (valid : HostRamAccessChip.Domain prior clkHigh clk0 clk1 prior.value) :
    ProverAssumptions (populate prior clkHigh clk0 clk1 shared) := by
  refine ⟨HostRamAccessChip.populate_assumptions _ _ _ _ _ valid, rfl, ?_⟩
  cases shared <;> simp [populate, IsBool]

def populateSpans (first second : MemorySpan) (prior : ℕ → MemoryMsg (ZMod p))
    (clkHigh clk0 clk1 : ZMod p) : List (Inputs (ZMod p)) :=
  (HostReadPlan.ofSpans first second).map fun entry =>
    populate (prior entry.cell) clkHigh clk0 clk1 entry.shared

/-- Bounded, strictly earlier records suffice; no sharing or timestamp witness is supplied. -/
theorem populateSpans_assumptions (first second : MemorySpan) (prior : ℕ → MemoryMsg (ZMod p))
    (clkHigh clk0 clk1 : ZMod p)
    (valid : ∀ cell ∈ MemorySpan.unionCells [first, second],
      HostRamAccessChip.Domain (prior cell) clkHigh clk0 clk1 (prior cell).value) :
    ∀ input ∈ populateSpans first second prior clkHigh clk0 clk1, ProverAssumptions input := by
  intro input member
  simp only [populateSpans, List.mem_map] at member
  obtain ⟨entry, member, rfl⟩ := member
  apply populate_assumptions
  apply valid entry.cell
  rw [← HostReadPlan.physical_cells]
  exact List.mem_map.mpr ⟨entry, member, rfl⟩

omit [Fact (2 ^ 25 < p)] in
private theorem populate_address (prior : MemoryMsg (ZMod p)) (clkHigh clk0 clk1 : ZMod p)
    (shared : Bool) :
    MemoryBoundary.address (populate prior clkHigh clk0 clk1 shared).ram.pushed =
      MemoryBoundary.address prior := rfl

omit [Fact (2 ^ 25 < p)] in
/-- A history indexed by the correct cell produces exactly the minimal physical address list.
The key premise is explicit: local validity alone does not identify a history entry's index. -/
theorem populateSpans_addresses (first second : MemorySpan) (prior : ℕ → MemoryMsg (ZMod p))
    (clkHigh clk0 clk1 : ZMod p)
    (keys : ∀ cell ∈ MemorySpan.unionCells [first, second],
      Word.toNat (MemoryBoundary.address (prior cell)) = cell * 8) :
    (populateSpans first second prior clkHigh clk0 clk1).map
        (fun input => Word.toNat (MemoryBoundary.address input.ram.pushed)) =
      (MemorySpan.unionCells [first, second]).map (· * 8) := by
  rw [← HostReadPlan.physical_cells]
  simp only [populateSpans, List.map_map, Function.comp_def, populate_address]
  apply List.map_congr_left
  intro entry member
  apply keys entry.cell
  rw [← HostReadPlan.physical_cells]
  exact List.mem_map.mpr ⟨entry, member, rfl⟩

omit [Fact (2 ^ 25 < p)] in
/-- Correctly indexed history records never create duplicate physical read addresses. -/
theorem populateSpans_addresses_nodup (first second : MemorySpan)
    (prior : ℕ → MemoryMsg (ZMod p)) (clkHigh clk0 clk1 : ZMod p)
    (keys : ∀ cell ∈ MemorySpan.unionCells [first, second],
      Word.toNat (MemoryBoundary.address (prior cell)) = cell * 8) :
    ((populateSpans first second prior clkHigh clk0 clk1).map
      (fun input => Word.toNat (MemoryBoundary.address input.ram.pushed))).Nodup := by
  rw [populateSpans_addresses _ _ _ _ _ _ keys]
  exact (MemorySpan.nodup_unionCells _).map (fun _ _ equal => by omega)

end SP1Clean.HostRamReadChip
