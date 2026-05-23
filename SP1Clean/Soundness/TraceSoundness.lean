import SP1Clean.Soundness.MemoryConsistencyClock
import SP1Clean.Soundness.StateConsistency
import SP1Clean.Soundness.IsRealBinary
import SP1Clean.Multiplicity

/-! # End-to-end trace-level soundness statement

This file wires together the four trace-shape bundles delivered by
Phases A–D of the SP1Clean trace-soundness plan into a single
end-to-end theorem.

## Scope (what this file proves)

Given the four trace-shape bundles
- `TraceClkValid` (Phase A.3) — per-row clk bounds + inter-row clk
  separation;
- `TraceStateValid` (Phase B.2) — PC chain handoff between adjacent
  real rows;
- `TraceIsRealBinary` (Phase D.1) — `is_real ∈ {0, 1}` per row;
- `h_online` — verifier-supplied online memory consistency of the
  aggregated memory access list;

plus a list of chip rows `rows` and their per-row `Spec`s, the
theorem concludes:
- the memory bus has an offline-consistent permutation
  (`chip_specs_admit_offline_bridge` from Phase A.2);
- the state bus's PC chain holds (`TraceStateValid` projection);
- `is_real ∈ {0, 1}` per row.

## Scope (what this file does NOT prove)

The link to a concrete `LeanRV64D.SailState` evolution is deferred to
future work. The plan's full
`trace_soundness : ∃ s_final, Sail.execute_trace s₀ rows.length = …`
form requires:
1. Per-chip `correct_*` theorems analogous to those in
   `SP1Chips/*`, transferred to the SP1Clean side. These don't exist
   yet for any pilot chip.
2. A `Sail.execute_trace` trace-level executor wrapping
   `LeanRV64D`'s per-instruction step (not present in upstream Sail
   today; estimated ~50 LOC of trace-recursion).

The statement here captures the *purely constraint-level* trace
soundness conclusion: the AIR constraints' trace-shape evidence
suffices to certify the trace as a valid memory- and PC-bus history.
The remaining Sail-link follows from per-chip correctness work.

## Verification

After this file lands, the closure check is:
- `lake build SP1Clean.Soundness` succeeds with zero error/warning;
- `#print axioms trace_soundness_aggregateMemory` shows only
  `Classical.choice`, `Quot.sound`, `propext`. -/

namespace SP1Clean.Soundness

open SP1Clean

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The trace-level soundness conclusion (memory + state buses):
given per-row chip `Spec`s plus the bundled trace-shape facts, the
aggregated memory accesses admit an offline-consistent permutation
and the state bus's PC chain holds. -/
theorem trace_soundness_aggregateMemory
    (rows : List (ChipRow p))
    (clkIncrement : ZMod p)
    (h_specs : ∀ row ∈ rows, ChipRow.Spec row)
    (h_clk : TraceClkValid rows)
    (h_state : TraceStateValid rows clkIncrement)
    (h_online :
      MemoryAccessList.isConsistentOnline (aggregateMemoryAccesses rows)
        (aggregateMemoryAccesses_isTimestampSorted rows h_clk)) :
    (∃ permuted : AddressSortedMemoryAccessList,
        permuted.val.Perm (aggregateMemoryAccesses rows) ∧
        MemoryAccessList.isConsistentOffline permuted.val permuted.property)
      ∧ pcChainProp clkIncrement (aggregateStateAccesses rows)
      ∧ TraceIsRealBinary rows := by
  refine ⟨?_, h_state.chain_holds, traceIsRealBinary_of_chip_specs rows h_specs⟩
  have h_sorted := aggregateMemoryAccesses_isTimestampSorted rows h_clk
  have h_nodup := aggregateMemoryAccesses_Notimestampdup rows h_clk
  exact (chip_specs_admit_offline_bridge rows h_specs h_sorted h_nodup).mp h_online

/-- Trace-soundness with state-bus boundary closure (iter-8 Phase 4):
strengthens `trace_soundness_aggregateMemory` with `TraceStateBoundary`,
which ties the first row's `pc` to a committed `initial_pc` and the
last row's `next_pc` to `final_pc`. This is the version with closed
state bus — combined with the existing PC chain, the trace witnesses
a complete `initial_pc → final_pc` execution path. -/
theorem trace_soundness_with_boundary
    (rows : List (ChipRow p))
    (clkIncrement : ZMod p) (initial_pc final_pc : Vector (ZMod p) 3)
    (h_specs : ∀ row ∈ rows, ChipRow.Spec row)
    (h_clk : TraceClkValid rows)
    (h_state : TraceStateValid rows clkIncrement)
    (h_boundary : TraceStateBoundary rows initial_pc final_pc)
    (h_online :
      MemoryAccessList.isConsistentOnline (aggregateMemoryAccesses rows)
        (aggregateMemoryAccesses_isTimestampSorted rows h_clk)) :
    (∃ permuted : AddressSortedMemoryAccessList,
        permuted.val.Perm (aggregateMemoryAccesses rows) ∧
        MemoryAccessList.isConsistentOffline permuted.val permuted.property)
      ∧ pcChainProp clkIncrement (aggregateStateAccesses rows)
      ∧ TraceIsRealBinary rows
      ∧ TraceStateBoundary rows initial_pc final_pc := by
  obtain ⟨h_mem, h_chain, h_isReal⟩ :=
    trace_soundness_aggregateMemory rows clkIncrement h_specs h_clk h_state h_online
  exact ⟨h_mem, h_chain, h_isReal, h_boundary⟩

end SP1Clean.Soundness
