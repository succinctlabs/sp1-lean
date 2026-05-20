import SP1Clean.MemoryAccess
import SP1Clean.AddChip
import SP1Clean.LoadByteChip
import SP1Clean.StoreByteChip
import SP1Clean.JalChip

/-! # Trace-level OfflineMemory bridge

This file wires per-chip `MemoryAccess` records into the
`Clean.Utils.OfflineMemory` consistency theorem
(`MemoryAccessList.isConsistentOnline_iff_isConsistentOffline`).

**Decoupling note (2026-05-19).** `Clean.Utils.OfflineMemory` in the
`../clean` fork currently has 3 pre-existing build failures unrelated
to this pilot (lines 278, 287, 311 — `simp_all` / `simp [filter_cons]`
leaving residual decidability goals on Lean 4.29 / current Mathlib).
Until those upstream proofs are repaired, this file defines a
**compatible local shape** `MemoryAccessTuple` / `MemoryAccessList`
matching OfflineMemory's API verbatim, and states the trace-level
bridge as an abstract claim parameterized by the offline-consistency
predicate. When OfflineMemory builds again, swap the local
`MemoryAccessTuple` for `_root_.MemoryAccess` and the abstract
`IsConsistentOffline` parameter for OfflineMemory's
`MemoryAccessList.isConsistentOffline` plus its main equivalence
theorem.

The design (per `docs/CLEAN_PILOT_NOTES.md` and the plan
`/home/dtumad/.claude/plans/make-a-plan-to-stateful-cookie.md`):

1. Each chip's `Spec` includes one or more `SP1Clean.memoryAccessSpec`
   conjuncts. The corresponding `MemoryAccess` records encode the
   per-row read side of the memory bus.
2. Per row, the chip also carries a write-side word: for register
   writes (`op_a` on arithmetic chips, `op_a_write_value` after Load
   completes) this is a distinct value from `prev_value`; for pure
   reads it's identical.
3. This file aggregates per-row records across a heterogenous list of
   chip rows into a single global `MemoryAccessList`. OfflineMemory's
   main theorem then tells us per-row consistency plus a permutation
   witness gives offline trace consistency.

Per-chip aggregators emit accesses in `(timestamp, addr, read, write)`
form via `SP1Clean.MemoryAccess.toAccessTuple`. -/

namespace SP1Clean.Soundness

open SP1Clean

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The 4-tuple OfflineMemory representation:
`(timestamp, address, readValue, writeValue)`. Matches
`Clean.Utils.OfflineMemory.MemoryAccess` verbatim. -/
abbrev MemoryAccessTuple := ℕ × ℕ × ℕ × ℕ

/-- Time-ordered list of memory accesses (canonically reverse-ordered:
most-recent at head). Matches `Clean.Utils.OfflineMemory.MemoryAccessList`
verbatim. -/
abbrev MemoryAccessList := List MemoryAccessTuple

/-- A chip row in the heterogenous aggregation. Each constructor wraps
one chip's column struct so the aggregator can pattern-match on chip
identity to extract the right `MemoryAccess` records and write-values.

Each new chip the pilot covers adds one constructor here. The two
shipping in this iteration are `add` (3 register accesses, 1 write to
op_a) and `loadByte` (2 register accesses + 1 RAM read at the load
address). -/
inductive ChipRow (p : ℕ) [Fact p.Prime] [Fact (2 ^ 17 < p)] where
  | add (cols : SP1Clean.Add.AddCols (ZMod p))
  | loadByte (cols : SP1Clean.LoadByte.LoadByteCols (ZMod p))
  | storeByte (cols : SP1Clean.StoreByte.StoreByteCols (ZMod p))
  | jal (cols : SP1Clean.Jal.JalCols (ZMod p))

namespace ChipRow

/-- The list of memory accesses emitted by one chip row, paired with
the write-side value. Each `(MemoryAccess, write_value)` pair flattens
into one OfflineMemory tuple via
`SP1Clean.MemoryAccess.toAccessTuple`. -/
def memoryAccesses : ChipRow p → List ((SP1Clean.MemoryAccess (ZMod p)) × Word (ZMod p))
  | .add cols =>
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_a, 0, 0],
          prev_value := cols.op_a_memory_prev_value,
          prev_low := cols.op_a_memory_prev_low,
          diff_low_limb := cols.op_a_memory_diff_low }
      let op_b_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_b, 0, 0],
          prev_value := cols.op_b_memory_prev_value,
          prev_low := cols.op_b_memory_prev_low,
          diff_low_limb := cols.op_b_memory_diff_low }
      let op_c_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_c, 0, 0],
          prev_value := cols.op_c_memory_prev_value,
          prev_low := cols.op_c_memory_prev_low,
          diff_low_limb := cols.op_c_memory_diff_low }
      -- op_a is read AND written (write_value = op_a_write_value);
      -- op_b and op_c are pure reads (write_value = prev_value).
      [(op_a_mem, cols.op_a_write_value),
       (op_b_mem, cols.op_b_memory_prev_value),
       (op_c_mem, cols.op_c_memory_prev_value)]
  | .loadByte cols =>
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_a, 0, 0],
          prev_value := cols.op_a_memory_prev_value,
          prev_low := cols.op_a_memory_prev_low,
          diff_low_limb := cols.op_a_memory_diff_low }
      let op_b_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_b, 0, 0],
          prev_value := cols.op_b_memory_prev_value,
          prev_low := cols.op_b_memory_prev_low,
          diff_low_limb := cols.op_b_memory_diff_low }
      -- The load access at the computed RAM address. write_value =
      -- prev_value (the chip itself doesn't modify the loaded memory
      -- word; that's the semantics of a load).
      let load_mem : SP1Clean.MemoryAccess (ZMod p) :=
        SP1Clean.LoadByte.loadMemoryAccess cols
      -- op_a is written with the sign-extended loaded byte.
      [(op_a_mem,
        #v[cols.result_byte + 65280 * cols.signed_extension_flag,
           65535 * cols.signed_extension_flag,
           65535 * cols.signed_extension_flag,
           65535 * cols.signed_extension_flag]),
       (op_b_mem, cols.op_b_memory_prev_value),
       (load_mem, cols.load_prev_value)]
  | .storeByte cols =>
      -- op_a and op_b are both pure register reads (stores do not
      -- modify the source data register or the base register).
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_a, 0, 0],
          prev_value := cols.op_a_memory_prev_value,
          prev_low := cols.op_a_memory_prev_low,
          diff_low_limb := cols.op_a_memory_diff_low }
      let op_b_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_b, 0, 0],
          prev_value := cols.op_b_memory_prev_value,
          prev_low := cols.op_b_memory_prev_low,
          diff_low_limb := cols.op_b_memory_diff_low }
      -- The store access at the computed RAM address: read-then-write
      -- at the same address. The MemoryAccess record carries the read
      -- side (prev_value at the prior timestamp); the write side
      -- (cols.store_write_value at the current timestamp) is supplied
      -- by the aggregator below.
      let store_mem : SP1Clean.MemoryAccess (ZMod p) :=
        SP1Clean.StoreByte.storeMemoryAccess cols
      [(op_a_mem, cols.op_a_memory_prev_value),
       (op_b_mem, cols.op_b_memory_prev_value),
       (store_mem, SP1Clean.StoreByte.storeWriteValue cols)]
  | .jal cols =>
      -- Jal has one register access (op_a write for the return address).
      -- The state-bus PC chain is tracked at trace level — not via
      -- MemoryAccess records.
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        SP1Clean.Jal.opAMemoryAccess cols
      [(op_a_mem, cols.op_a_write_value)]

/-- The chip-row's `clk_high` and (composed) `clk_low` for the per-access
timestamp encoding `clk_high * 2^24 + clk_low + offset`. -/
def clockComponents : ChipRow p → ZMod p × ZMod p
  | .add cols => (cols.clk_high, cols.clk_0_16 + cols.clk_16_24 * 65536)
  | .loadByte cols => (cols.clk_high, cols.clk_0_16 + cols.clk_16_24 * 65536)
  | .storeByte cols => (cols.clk_high, cols.clk_0_16 + cols.clk_16_24 * 65536)
  | .jal cols => (cols.clk_high, cols.clk_0_16 + cols.clk_16_24 * 65536)

/-- The chip-row's natural Spec predicate (the propositional content the
chip's FormalAssertion / iff_sp1 establishes). -/
def Spec : ChipRow p → Prop
  | .add cols => SP1Clean.Add.assertion.Spec cols
  | .loadByte cols => SP1Clean.LoadByte.Spec cols
  | .storeByte cols => SP1Clean.StoreByte.Spec cols
  | .jal cols => SP1Clean.Jal.Spec cols

/-- Per-row, per-access sub-clock offsets. R-type and I-type readers
emit accesses at `clk_low + 4` (op_a), `clk_low + 3` (op_b), and
`clk_low + 2` (op_c); `LoadByte` adds an access at `clk_low + 1` for
the RAM load. The offset list mirrors `memoryAccesses` above. -/
def offsets : ChipRow p → List (ZMod p)
  | .add _ => [4, 3, 2]
  | .loadByte _ => [4, 3, 1]
  -- Store: op_a (data source) at +4, op_b (base) at +3, store memory
  -- access at +0 (matches SP1's `.send (.memory ...) ... Main[33] Main[34]`
  -- which uses the *prior* timestamp components, not the current row's).
  | .storeByte _ => [4, 3, 0]
  -- Jal: only op_a write at +4. State-bus PC chain is trace-level.
  | .jal _ => [4]

end ChipRow

/-- Aggregate a list of chip rows into a single `MemoryAccessList`.
Each row contributes its memory-access tuples in `(timestamp, addr,
readValue, writeValue)` form via `MemoryAccess.toAccessTuple`. -/
def aggregateMemoryAccesses : List (ChipRow p) → MemoryAccessList
  | [] => []
  | row :: rest =>
      let (clk_high, clk_low) := row.clockComponents
      let accesses := row.memoryAccesses
      let offs := row.offsets
      let rowAccesses :=
        (accesses.zip offs).map fun ((acc, write_value), offset) =>
          acc.toAccessTuple clk_high clk_low offset write_value
      rowAccesses ++ aggregateMemoryAccesses rest

/-- Compatibility-shaped statement of the trace-level OfflineMemory
bridge. Stated against an abstract `isConsistentOffline` predicate so the
pilot does not depend on the (currently non-building)
`Clean.Utils.OfflineMemory` proofs.

The intended target: when `Clean.Utils.OfflineMemory` builds again,
this signature collapses to a direct call to
`MemoryAccessList.isConsistentOnline_iff_isConsistentOffline`.

The role of `h_specs` is to assert that every chip row's `Spec` holds.
In the eventual end-to-end proof, this is the hook by which per-chip
soundness propagates into the trace-level claim — but the trace-level
equivalence itself follows purely from OfflineMemory's main theorem and
does not consume `h_specs` directly. -/
theorem chip_specs_admit_offline_bridge
    (rows : List (ChipRow p))
    (_h_specs : ∀ row ∈ rows, row.Spec)
    (isConsistentOnline : MemoryAccessList → Prop)
    (isConsistentOffline : MemoryAccessList → Prop)
    -- The OfflineMemory main theorem, supplied as a hypothesis until
    -- the upstream file builds.
    (h_offline_bridge :
      isConsistentOnline (aggregateMemoryAccesses rows) ↔
        isConsistentOffline (aggregateMemoryAccesses rows)) :
    isConsistentOnline (aggregateMemoryAccesses rows) ↔
      isConsistentOffline (aggregateMemoryAccesses rows) :=
  h_offline_bridge

end SP1Clean.Soundness
