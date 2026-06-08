import SP1Clean.Foundations.InteractionBus

/-! # `ChipAir` / `Machine` — the multi-chip bus aggregate

Bundles each chip's per-row interaction contributions into a `Machine`, so SP1's cross-chip
**Σsends = Σreceives** (the global LogUp balance over every chip's interactions on the shared buses)
becomes *expressible*: `Machine.busBalance`. Built directly on `Foundations/InteractionBus.lean`'s
computable `List`/`ℤ` core (`aggregateChipRows`/`multiplicitySum`/`isConsistentBalanced`) — never through
the `noncomputable` `Operations.interactionsWith` — so it stays axiom-clean and permutation-invariant.

**Statement layer only.** This makes the multi-chip balance *sayable* and decomposes it per chip
(`multiplicitySum_busAggregate_cons`); it does **not** prove `busBalance ⟹ pcChainProp` / offline-memory /
ROM-membership. Those stay threaded as the per-bus `Trace*Link`s in `Soundness/*Consistency.lean`
(`docs/bus-model.md`). `InteractionScope` (multi-shard) is deferred. -/

namespace SP1Clean

open SP1Clean.LookupAccessList

variable {Row : Type}

/-- One chip's interaction-bus contribution: a name, the per-row `LookupAccessList` it emits (its sends
and receives across *all* buses, in trace-emission order), and whether it is part of the machine. Mirrors
SP1's per-`Air` interaction set (`crates/hypercube`'s `Chip`/`MachineAir`). -/
structure ChipAir (Row : Type) where
  name : String
  perRow : Row → LookupAccessList
  included : Bool := true

/-- A machine is a list of chips (all over a shared row type, the single-shard slice). -/
abbrev Machine (Row : Type) := List (ChipAir Row)

/-- Aggregate every *included* chip's per-row contributions into one trace-level bus. `rowsOf` supplies
each chip's rows (for the single-chip/single-shard slice, every chip gets the same trace). -/
def Machine.busAggregate (m : Machine Row) (rowsOf : ChipAir Row → List Row) : LookupAccessList :=
  m.flatMap (fun c => if c.included then aggregateChipRows (rowsOf c) c.perRow else [])

/-- The machine's global bus is balanced: every `(kind, table, entry)` key's signed multiplicity sums to
zero across all chips. This is SP1's cross-chip "Σsends = Σreceives" / the LogUp/GKR closure — the global
soundness premise (here only *expressed*, not derived). -/
def Machine.busBalance (m : Machine Row) (rowsOf : ChipAir Row → List Row) : Prop :=
  (Machine.busAggregate m rowsOf).isConsistentBalanced

@[simp] theorem busAggregate_nil (rowsOf : ChipAir Row → List Row) :
    Machine.busAggregate ([] : Machine Row) rowsOf = [] := rfl

theorem busAggregate_cons (c : ChipAir Row) (m : Machine Row) (rowsOf : ChipAir Row → List Row) :
    Machine.busAggregate (c :: m) rowsOf =
      (if c.included then aggregateChipRows (rowsOf c) c.perRow else [])
        ++ Machine.busAggregate m rowsOf := by
  simp [Machine.busAggregate]

/-- **Per-chip decomposition of the bus balance.** Each key's machine-wide signed multiplicity is the sum
of the per-chip multiplicities — so "the machine balances" is exactly "the per-chip sends and receives
cancel at every key". This is the structural fact that grounds `busBalance` in the per-bus
`Soundness/*Consistency.lean` projections. -/
theorem multiplicitySum_busAggregate_cons (c : ChipAir Row) (m : Machine Row)
    (rowsOf : ChipAir Row → List Row) (k : LookupKey) :
    multiplicitySum (Machine.busAggregate (c :: m) rowsOf) k =
      (if c.included then multiplicitySum (aggregateChipRows (rowsOf c) c.perRow) k else 0) +
        multiplicitySum (Machine.busAggregate m rowsOf) k := by
  rw [busAggregate_cons, multiplicitySum_append]
  by_cases h : c.included <;> simp [h, multiplicitySum_nil]

end SP1Clean
