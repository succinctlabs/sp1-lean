import SP1Clean.Soundness.NativeCoreRows
import SP1Clean.Soundness.CoreRowBalance

/-! # Memory balance through mixed-row alignment and refresh elimination

Memory balance needs per-row message permutations, independently of read currency points. The
ordinary `AlignsWith` relation also requires all original reads at the row start, so it cannot be
imposed on syscall rows. `RowMemoryPermutation` states only the two ledger equalities and admits
the syscall carrier unchanged. It is an internal transport interface, not an AIR premise.

The raw combined AIR supplies the balance. Refresh elimination additionally needs strict order
of the actual refresh timestamps and the aligned rows' structural `RowOKCore` facts. Those
chronology obligations form the reusable interface discharged by `NativeCoreMemoryOrder`. The result
is the exact refresh-free Memory equation for the generic timed walk, without an inactivity or
semantic-boundary assumption.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics
open TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- Reordering the exact mixed inventory and aligning each occurrence's Memory messages preserves
the authenticated balance. No ordinary-row currency restriction is imposed on system rows. -/
theorem memory_balance_of_row_projection {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (ordered : List (ExecutionRow p)) (exhaustive : ordered.Perm (executionRows witness))
    (rows : List (RowFacts p))
    (projection : List.Forall₂ RowMemoryPermutation rows (ordered.map (ExecutionRow.facts witness.data)))
    (loc : MemLoc) :
    optMS (memoryInitialFrontier witness loc) + pushesAt rows loc +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑((memoryRefreshes witness).map Prod.snd) : Multiset _) =
      optMS (memoryFinalFrontier witness loc) + pullsAt rows loc +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑((memoryRefreshes witness).map Prod.fst) : Multiset _) := by
  rw [(rowAggregates_of_permutation projection loc).1, (rowAggregates_of_permutation projection loc).2,
    pushesAt_perm (exhaustive.map _) loc, pullsAt_perm (exhaustive.map _) loc]
  exact executionRows_memory_balance witness constraints balanced loc

/-- Each actual refresh preserves the complete value and location, independently of its clocks. -/
theorem memoryRefreshes_preserve {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) :
    ∀ pair ∈ memoryRefreshes witness,
      (MemoryMsg.locOf pair.1, pair.1.value) = (MemoryMsg.locOf pair.2, pair.2.value) := by
  intro pair member
  obtain ⟨row, _, member⟩ := List.mem_flatMap.mp member
  obtain rfl := List.mem_singleton.mp member
  rfl

/-- Eliminate the actual refresh pairs after chronology and aligned touch shape are established.
Each aligned input row survives, with its State edge and fetch unchanged, and each pull is
rewritten only to an equal-value record at the same location and a no-later time. Final records
retain the same value/location relation to the returned frontier. This supplies the generic walk's
Memory balance; it does not discharge its State, step, frame, or timeline premises. -/
theorem memory_refresh_free_of_chronology {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (ordered : List (ExecutionRow p)) (exhaustive : ordered.Perm (executionRows witness))
    (rows : List (RowFacts p))
    (projection : List.Forall₂ RowMemoryPermutation rows (ordered.map (ExecutionRow.facts witness.data)))
    (initialClock : ℕ) (rowOK : ∀ row ∈ rows, RowOKCore initialClock row)
    (refreshOrder : ∀ pair ∈ memoryRefreshes witness, MemoryMsg.timeNat pair.1 < MemoryMsg.timeNat pair.2) :
    ∃ (touches : List (List (Touch p))) (final : MemLoc → Option (MemoryMsg (ZMod p))),
      List.Forall₂ (List.Forall₂ PullRewrite) (rows.map rowTouches) touches ∧
      (∀ loc, optMS (memoryInitialFrontier witness loc) +
          pushesAt ((rows.zip touches).map (fun pair => alignedOf pair.1 pair.2)) loc =
        optMS (final loc) + pullsAt ((rows.zip touches).map (fun pair => alignedOf pair.1 pair.2)) loc) ∧
      (rows.zip touches).map Prod.fst = rows ∧
      (∀ loc message, memoryFinalFrontier witness loc = some message →
        ∃ earlier, final loc = some earlier ∧ MemoryMsg.locOf earlier = MemoryMsg.locOf message ∧
          earlier.value = message.value ∧ MemoryMsg.timeNat earlier ≤ MemoryMsg.timeNat message) :=
  refresh_free_of_balance rows (memoryInitialFrontier witness) (memoryFinalFrontier witness)
    (memoryRefreshes witness) initialClock rowOK
    (memory_balance_of_row_projection witness constraints balanced ordered exhaustive rows projection)
    (memoryRefreshes_preserve witness) refreshOrder

end SP1Clean.Soundness.NativeCore
