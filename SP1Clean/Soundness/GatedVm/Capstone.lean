import SP1Clean.Soundness.GatedVm.SailDispatch
import SP1Clean.Soundness.GatedVm.StateBridge

/-! # The gated whole-program execution capstone (path b, assembled)

The meaningful whole-machine result, assembled from the two axiom-clean halves built in
`SailDispatch.lean` (`chipRows_step_sound`) and `StateBridge.lean` (`state_trail_of_balance`):

  per-row chip `Spec`s  +  gated state-bus balance  ⟹  every real instruction is RISC-V-Sail-correct
                                                       ∧  ∃ an execution trail `pc_start → … → next_pc`

Compared with the bespoke `traceValid_of_specs_and_balance''`, this **drops
every trace-shape side condition** — `clkInjective`, `TraceClkAdvance`, `TraceMemClkValid`,
`memPrevLink`, `prevTs < clk`, `MemRowWellFormed`, `MemProviderGenesis` — because the transition path
is forced by the gated state-bus balance *alone* (the Eulerian `exists_trail`), not reconstructed from a
clk-ordered adjacency. So it is **strictly ≥ bespoke** (same conclusion content — a valid execution from
the public initial pc to the public final pc — under a strictly smaller hypothesis set), built on the
reusable `GatedVm` machinery rather than `TraceValid`.

**Trust boundary.** `h_bal` (the native `isConsistentBalanced` of the state bus + boundary) is the
LogUp/GKR backend assumption — *exactly* the trust boundary the bespoke capstone already takes (inside
`TraceMachineBalancedWith'`). Deriving it instead from Clean's ensemble `Statement.BalancedChannels`
(the `FormalEnsemble` wrapping) is a documented *strengthening beyond bespoke*, tracked as future work;
it is not needed for ≥-bespoke parity. -/

namespace SP1Clean.Soundness

open SP1Clean
open SP1Clean.LookupAccessList
open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- A gated whole-program execution certificate over a heterogeneous trace: every real row is
RISC-V-Sail-correct, and the rows' `current → next` transitions compose (by balance) into a path from
the public initial state key `initEntry` to the public final state key `finalEntry`. The trail's rows
are a sub-multiset of the trace's real rows (`trail_rows_real`), so each carries `sailEquiv`. -/
structure GatedExecution (rows : List (ChipRow p)) (initEntry finalEntry : List ℕ) : Prop where
  /-- Every real instruction agrees with its RISC-V Sail spec, for any state honouring its reads. -/
  step_sound : ∀ r ∈ rows, r.is_real = 1 → ∀ s : SailState, r.sailEquiv s
  /-- The committed `pc_start`/`next_pc` are the endpoints of a valid transition trail of real rows. -/
  trail : ∃ path : List (Trace.RowView (ZMod p)),
            GatedVm.IsWalk (fun r => stateEdge (stateAccess r))
              (InteractionKind.State, "SP1State", initEntry)
              (InteractionKind.State, "SP1State", finalEntry) path
            ∧ (↑path : Multiset (Trace.RowView (ZMod p))) ≤ realRowEdges (rows.map ChipRow.view)

/-- **The gated capstone.** From per-row chip `Spec`s (`h_spec`), binary gating (`hbin`), and the gated
state-bus balance with the genesis/finalization boundary (`h_bal`, the trust boundary), the whole trace
is a valid whole-program execution from `pc_start` to `next_pc`. No clock injectivity / advance / memory
side conditions — the path is forced by balance alone. -/
theorem gatedExecution_of_specs_and_balance
    (rows : List (ChipRow p)) (data : ProverData (ZMod p)) (initEntry finalEntry : List ℕ)
    (h_spec : ∀ r ∈ rows, r.chipSpec data)
    (hbin : ∀ r ∈ rows.map ChipRow.view, r.is_real = 0 ∨ r.is_real = 1)
    (h_bal : isConsistentBalanced (aggregateChipRows (rows.map ChipRow.view) stateLookups
              ++ [(InteractionKind.State, "SP1State", initEntry, (1 : ℤ)),
                  (InteractionKind.State, "SP1State", finalEntry, (-1 : ℤ))])) :
    GatedExecution rows initEntry finalEntry where
  step_sound := GatedVm.chipRows_step_sound rows data h_spec
  trail := state_trail_of_balance (rows.map ChipRow.view) hbin initEntry finalEntry h_bal

end SP1Clean.Soundness
