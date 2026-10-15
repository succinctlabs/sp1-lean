import SP1Clean.Model.Core.ResourceLimits
import SP1Clean.Model.Core.HostExecution
import SP1Clean.Model.Core.MemorySpan

/-! # Range consumers at boundary and cell-cover edges

These use a non-SP1 range to check that the host interpreter and span arithmetic consume the
shared data. They do not claim that an arbitrary range is realized by the pinned Sail platform.
-/

namespace SP1CleanTest.Core.ResourceLayout
open SP1Clean.Model.Core

private def window : AddressRange := ⟨24, 56⟩
private def policy : HostMemoryPolicy := ⟨fun address => address == 55, window⟩
private def context : HostReadContext := ⟨fun _ => none, fun _ => some 9⟩

/-- Empty reads may name the upper endpoint, but not addresses outside the range. -/
theorem emptyEdges :
    context.readGuest? policy 56 0 = some [] ∧
      context.readGuest? policy 57 0 = none ∧ context.readGuest? policy 23 0 = none := by decide +kernel

/-- A readable protected byte is not writable, including a same-value write. -/
theorem protectionAndUpperEdge :
    context.readGuest? policy 55 1 = some [9] ∧ policy.permits 55 1 = false ∧
      context.readGuest? policy 55 2 = none ∧ policy.permits 56 0 = true := by decide +kernel

/-- An unaligned two-byte read covers two cells within the same declared range. -/
theorem crossingCells : (MemorySpan.mk 31 2).cells = [3, 4] ∧
    ∀ cell ∈ (MemorySpan.mk 31 2).cells, window.ContainsSpan (cell * 8) 8 := by
  refine ⟨by decide +kernel, ?_⟩
  exact MemorySpan.cell_in_range _ _ (by decide) (by decide) (by decide)

/-- Reversed ranges accept no span, including empty requests. -/
theorem malformedRange (address length : ℕ) : ¬ (AddressRange.mk 56 24).ContainsSpan address length := by
  intro inside
  have valid := inside.valid
  contradiction

end SP1CleanTest.Core.ResourceLayout
