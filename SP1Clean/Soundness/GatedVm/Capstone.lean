import SP1Clean.Soundness.GatedVm.SailDispatch
import SP1Clean.Soundness.GatedVm.StateBridge

/-! # The gated whole-program execution capstone (assembled)

> **FROZEN (consolidation step 0, 2026-07-09).** Legacy soundness path — scheduled for deletion at the cutover (proposal §5.6). Do NOT add new lemmas against this module; new soundness work targets the timed-grounding engine (proposal §3.2).

The trail half of the whole-machine result, built on `StateBridge.lean`'s
`state_trail_of_balance`:

  gated state-bus balance  ⟹  ∃ an execution trail `pc_start → … → next_pc`

(the per-row Sail-correctness conjunct was retired from this structure — instruction semantics now
route through the timed-grounding engine and the chip `advance` lemmas, not this legacy path).
The transition path is forced by the gated state-bus balance *alone* (the Eulerian `exists_trail`),
with **no** clock-injectivity, clock-advance, or memory side conditions.

**Trust boundary.** `h_bal` (the native `isConsistentBalanced` of the state bus + boundary) is the
LogUp/GKR backend assumption. Deriving it from Clean's ensemble `Statement.BalancedChannels` (the
`FormalEnsemble` wrapping) is tracked as future work. -/

namespace SP1Clean.Soundness

open SP1Clean
open SP1Clean.LookupAccessList
open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- A gated whole-program execution certificate over a heterogeneous trace: the rows'
`current → next` transitions compose (by balance) into a path from
the public initial state key `initEntry` to the public final state key `finalEntry`. The trail's rows
are a sub-multiset of the trace's real rows (`trail_rows_real`). (Trail-only: the former per-row
Sail-correctness conjunct is retired from this structure.) -/
structure GatedExecution (rows : List (ChipRow p)) (initEntry finalEntry : List ℕ) : Prop where
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
    (_h_spec : ∀ r ∈ rows, r.chipSpec data)
    (hbin : ∀ r ∈ rows.map ChipRow.view, r.is_real = 0 ∨ r.is_real = 1)
    (h_bal : isConsistentBalanced (aggregateChipRows (rows.map ChipRow.view) stateLookups
              ++ [(InteractionKind.State, "SP1State", initEntry, (1 : ℤ)),
                  (InteractionKind.State, "SP1State", finalEntry, (-1 : ℤ))])) :
    GatedExecution rows initEntry finalEntry where
  trail := state_trail_of_balance (rows.map ChipRow.view) hbin initEntry finalEntry h_bal

end SP1Clean.Soundness
