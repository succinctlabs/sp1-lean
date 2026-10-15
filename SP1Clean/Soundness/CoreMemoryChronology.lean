import SP1Clean.Soundness.CoreTouches

/-! # Shared Memory clock bounds and physical refresh chronology

Natural-time ranking, both 24-bit record bounds, and the MemoryBump comparison are independent
of source values and initialization policy. Assemblies obtain consumed-record bounds from their
own source/push/refresh balance before applying the physical refresh comparison.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance coreMemoryChronologyField24 : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance coreMemoryChronologyField17 : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Both limbs of a Memory record represent genuine 24-bit clocks. -/
def MemoryClockBounds (message : MemoryMsg (ZMod p)) : Prop :=
  MemoryMsg.ClkBound message ∧ message.clk_high.val < 2 ^ 24

theorem walk_rank_bound {α V : Type*} (edge : α → V × V) (rank : V → ℕ)
    {initial final : V} {rows : List α} (walk : Walk.IsWalk edge initial final rows)
    (advance : ∀ row ∈ rows, rank (edge row).1 ≤ rank (edge row).2) :
    rank initial ≤ rank final ∧ ∀ row ∈ rows, rank (edge row).2 ≤ rank final := by
  induction rows generalizing initial with
  | nil => exact ⟨le_of_eq (congrArg rank walk), by simp⟩
  | cons head tail ih =>
    obtain ⟨source, rest⟩ := walk
    have tailBound := ih rest (fun row member => advance row (List.mem_cons_of_mem _ member))
    refine ⟨?_, ?_⟩
    · rw [← source]
      exact (advance head List.mem_cons_self).trans tailBound.1
    · intro row member
      rcases List.mem_cons.mp member with rfl | member
      · exact tailBound.1
      · exact tailBound.2 row member

-- Keep the decoded table row opaque while projecting the refresh theorem's time conclusion.
theorem memoryBump_row_order (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (component : table.component = { circuit := MemoryBumpChip.circuit })
    (constraints : table.Constraints data) (byte : table.ChannelGuarantees data byteChannel.toRaw)
    {physical : Array (ZMod p)} (member : physical ∈ table.table)
    (real : (memoryBumpRow data physical).is_real = 1)
    (bounds : MemoryClockBounds (MemoryBumpChip.pulledMessage (memoryBumpRow data physical))) :
    MemoryMsg.timeNat (MemoryBumpChip.pulledMessage (memoryBumpRow data physical)) <
      MemoryMsg.timeNat (MemoryBumpChip.pushedMessage (memoryBumpRow data physical)) :=
  (memoryBump_isRefresh_of_component table data component constraints byte member real bounds.1 bounds.2).2

end SP1Clean.Soundness.NativeCore
