import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Utils.Field
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations.Field
import SP1Foundations.Word
import SP1Clean.MemoryAccess
import SP1Clean.Chips.Structs

/-! # Boundary memory chips: `MemoryGlobalInit` and `MemoryGlobalFinalize`

SP1 emits two boundary memory chips to close the global memory bus:
`MemoryGlobalInit` and `MemoryGlobalFinalize`
(see `/home/dtumad/Documents/sp1/crates/core/machine/src/memory/global.rs:256-298`).
Both share the same column layout (`MemoryInitCols`); they differ only
in the bus they emit on (`MemoryGlobalInitControl` vs.
`MemoryGlobalFinalizeControl`, `InteractionKind` 14 / 15) and in the
direction of the address-monotonicity check.

## Role in the trace-soundness pipeline

The interior chips (Add, Lt, Load*, Store*, ...) emit per-row memory
accesses keyed by `(clk, addr)`. For the offline-consistency theorem
(`Clean.Utils.OfflineMemory`) to close, every accessed address must
have an INIT record (claiming the initial value) and a FINALIZE record
(claiming the final value being read out). The boundary chips supply
these "ghost" first/last records.

## Phase 4 status (iter-8, [[clean-pilot-iter8-table-bridging]])

This file ships the **column struct + ChipRow constructors only**. The
chip's `Spec` is `True` (placeholder); the internal constraint surface
(range checks on `addr`/`prev_addr`/`value`, the `lt_cols` monotonicity
assertion, the two `IsZeroOperation` arms on `is_prev_addr_zero` /
`is_index_zero`) is deferred to a follow-up sub-iter that promotes
`MemoryGlobalCols` to a full `FormalAssertion` analogous to the
interior chips.

The boundary records' contribution to `aggregateMemoryAccesses` is
likewise minimal in Phase 4: both `memInit` and `memFinalize` emit an
empty access list. The full bus closure (concatenating boundary tuples
with interior tuples) is iter-8 Phase 4.5 follow-up work.
-/

namespace SP1Clean.MemoryGlobal

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Minimal `Spec` for boundary chips. Phase 4 ships only the
`is_real * (is_real - 1) = 0` binary gate — the gate that SP1's source
emits at `global.rs:313` (`builder.assert_bool(local.is_real)`).
The internal constraints (range checks on addr/prev_addr/value,
monotonicity via `lt_cols`, the two IsZero witnesses) are deferred to a
follow-up sub-iter that lifts `MemoryGlobalCols` to a full
`FormalAssertion`.

The binary gate is included because downstream trace-soundness
infrastructure (`TraceIsRealBinary` in `Soundness/IsRealBinary.lean`)
needs `is_real ∈ {0, 1}` on every chip row — including boundary rows. -/
def Spec (cols : MemoryGlobalCols (ZMod p)) : Prop :=
  cols.is_real * (cols.is_real - 1) = 0

/-! ## Bus-side memoryAccess emission (placeholder for Phase 4)

When fully wired into the trace-soundness pipeline, boundary chips
emit `MemoryAccess` records that close the global memory bus:

- `MemoryGlobalInit`: one access at timestamp `(0, 0)` claiming
  `prev_value = 0` (no previous access) and writing `cols.value`.
- `MemoryGlobalFinalize`: one access at `(cols.clk_high, cols.clk_low)`
  reading `cols.value` as the final value at `cols.addr`.

Phase 4 returns an empty list — the boundary records' contribution to
`aggregateMemoryAccesses` is deferred to a follow-up sub-iter
(Phase 4.5) that:
1. Threads boundary tuples into the trace-level `MemoryAccessList`.
2. Provides the matching `memoryAccessSpec` discharge.
3. Verifies the timestamp-sorted / Notimestampdup properties hold
   across the combined boundary + interior list. -/

/-- Per-chip memory-access list for the `MemoryGlobalInit` chip.
Placeholder: emits empty list in Phase 4. The eventual full emission
is one access at timestamp `(0, 0)` per `cols.addr` writing
`cols.value`. -/
def initMemoryAccesses (_cols : MemoryGlobalCols (ZMod p)) :
    List ((SP1Clean.MemoryAccess (ZMod p)) × Word (ZMod p)) :=
  []

/-- Per-chip memory-access list for the `MemoryGlobalFinalize` chip.
Placeholder: emits empty list in Phase 4. The eventual full emission
is one access at `(cols.clk_high, cols.clk_low)` per `cols.addr`
reading `cols.value` as the final value. -/
def finalizeMemoryAccesses (_cols : MemoryGlobalCols (ZMod p)) :
    List ((SP1Clean.MemoryAccess (ZMod p)) × Word (ZMod p)) :=
  []

end SP1Clean.MemoryGlobal
