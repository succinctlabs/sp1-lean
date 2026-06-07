import Mathlib.Data.ZMod.Basic
import SP1Clean.Foundations.InteractionBus
import SP1Clean.Foundations.Word

/-! # The `MemoryProvider` receiver — the closed Memory bus's init/finalize boundary

SP1's memory soundness is **timestamp-ordered offline memory** on a *closed* bus: every register/RAM
access `send`s the prior value at the previous timestamp and `receive`s the new value at the current
timestamp, and the LogUp argument balances them — a read's receive is cancelled by the *next* access's
send (it claims the same `(clk, addr, value)` prior), which is exactly "a read returns the most recent
write." Two contributions per address are left unmatched *within* the trace: the **first** access's send
(its claimed genesis prior) and the **last** access's receive (the final committed value). SP1's
**Memory Global init/finalize** chips (`crates/core/machine/src/memory/{local,global}.rs`) materialize
those boundary rows; their preprocessed/public-value trace carries exactly the per-address initial and
final `(clk, addr, value)` records, and balancing the bus against them closes the chain.

This module models that boundary receiver natively — the closed-bus sibling of `Chips/ProgramChip.lean`'s
`ProgramProvider`. A `MemoryProvider initSpec` is any Memory-bus contribution list whose every entry sits
at the key of some `initSpec`-valid boundary record. As with the byte/program buses, the Memory-bus key is
the *full* `ZMod.val`-projection of the timestamp, the three address limbs, and the four value limbs, so
(val injective) **the key determines the record** — the fact that lets the boundary's membership transfer.

**Single-shard scope.** This models one trace's init/finalize boundary. SP1's *cross-shard* memory
argument (per-shard init/final states chained through public values, address-disjointness, the global
Septic cumulative sum) is a separate multi-shard layer: it instantiates this `MemoryProvider` per shard
and chains the boundaries. The single-shard model deliberately captures neither disjointness nor the
global sum. -/

namespace SP1Clean.MemoryGlobalChip

open SP1Clean
open SP1Clean.LookupAccessList

variable {p : ℕ} [NeZero p]

/-- One memory-boundary record: the clock components, the three 16-bit address limbs, and the value
`Word` — the meaningful columns of the Memory-bus key (mirrors `Soundness/MemoryConsistency.lean`'s
`memoryLookups`/`memAccessLookups` 9-tuple). For a register boundary `addr1 = addr2 = 0` (the register
index in `addr0`); for a real RAM boundary all three limbs are the 48-bit address. -/
structure MemInitRow (F : Type) where
  clk_high : F
  clk_low : F
  addr0 : F
  addr1 : F
  addr2 : F
  value : Word F

/-- The val-projected Memory-bus key of a boundary record — the 9-tuple `memoryLookups` sends, with the
clock, the three address limbs, and the four value limbs through `ZMod.val`. -/
def memRowKey (row : MemInitRow (ZMod p)) : LookupKey :=
  (.Memory, "SP1Memory",
    [row.clk_high.val, row.clk_low.val, row.addr0.val, row.addr1.val, row.addr2.val,
      row.value[0].val, row.value[1].val, row.value[2].val, row.value[3].val])

/-- **The key determines the record.** The Memory-bus key is the full `ZMod.val`-projection of every
meaningful field, and `ZMod.val` is injective (`[NeZero p]`), so two records with the same key are equal
(the `value` `Word` recovered limb-by-limb via `Vector.ext`). The closed-bus analogue of
`ProgramChip.programRow_eq_of_key`. -/
theorem memRow_eq_of_key {r1 r2 : MemInitRow (ZMod p)} (h : memRowKey r1 = memRowKey r2) :
    r1 = r2 := by
  simp only [memRowKey, Prod.mk.injEq, List.cons.injEq, and_true, true_and] at h
  obtain ⟨hch, hcl, h0, h1, h2, hv0, hv1, hv2, hv3⟩ := h
  cases r1; cases r2
  simp only [MemInitRow.mk.injEq]
  refine ⟨ZMod.val_injective p hch, ZMod.val_injective p hcl, ZMod.val_injective p h0,
    ZMod.val_injective p h1, ZMod.val_injective p h2, ?_⟩
  apply Vector.ext; intro i hi
  rcases i with _ | _ | _ | _ | i
  · exact ZMod.val_injective p hv0
  · exact ZMod.val_injective p hv1
  · exact ZMod.val_injective p hv2
  · exact ZMod.val_injective p hv3
  · exact absurd hi (by omega)

/-- The **`MemoryProvider`**: any Memory-bus contribution list whose every entry sits at the key of some
`initSpec`-valid boundary record. The native, predicate-characterized content of SP1's preprocessed Memory
Global init/finalize chips — its trace carries *only* valid boundary records. Generic over `initSpec`
(the per-address genesis/final value predicate), exactly as `ProgramChip.ProgramProvider` is characterized
by `ProgramRowSpec`. -/
def MemoryProvider (initSpec : MemInitRow (ZMod p) → Prop) (prov : LookupAccessList) : Prop :=
  ∀ b ∈ prov, ∃ row : MemInitRow (ZMod p), initSpec row ∧ keyOf b = memRowKey row

omit [NeZero p] in
/-- Every Memory-provider entry carries `InteractionKind.Memory` (its key is a `memRowKey`). The
cross-bus-disjointness input `memoryBalance_of_machine` consumes (mirrors `programProvider_kind`). -/
theorem memProvider_kind {initSpec : MemInitRow (ZMod p) → Prop} {prov : LookupAccessList}
    (h : MemoryProvider initSpec prov) : ∀ b ∈ prov, (keyOf b).1 = InteractionKind.Memory := by
  intro b hb
  obtain ⟨row, _, hk⟩ := h b hb
  rw [hk, memRowKey]

/-- A boundary contribution whose key a `MemoryProvider` carries is an `initSpec`-valid record. (The
provider has a valid record at that key; the key determines the record.) The closed-bus analogue of
`ProgramChip.inROM_of_provider`. -/
theorem initRow_of_provider {initSpec : MemInitRow (ZMod p) → Prop} {row : MemInitRow (ZMod p)}
    {prov : LookupAccessList} (h_prov : MemoryProvider initSpec prov) {b : LookupAccess} (hb : b ∈ prov)
    (hk : keyOf b = memRowKey row) : initSpec row := by
  obtain ⟨row', h_spec, h_key⟩ := h_prov b hb
  rw [hk] at h_key
  rw [memRow_eq_of_key h_key]
  exact h_spec

end SP1Clean.MemoryGlobalChip
