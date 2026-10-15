import SP1Clean.Proofs.Chips.SyscallInstrsChip.Formal
import ToClean.Air.TableBuild

/-! # `SyscallInstrs` table: component and (for now empty) witness generation

The build-side substrate the deterministic completeness compiler needs to place SP1's syscall chip
at ensemble position 54.

**This table is empty, and that is the point of contrast with `HaltChip`.** The halt table carries
exactly one row on every shard, because its Exit contribution is a *gated pair* — `pushIf is_real`
alongside `pushIf (1 - is_real) ⟨0⟩` — so the anti-gated zero-code push is what balances the
state-boundary verifier's ungated pull, and a zero-row halt table would leave that pull unmatched.
The syscall row emits a single positively-gated Exit push instead, so an empty table contributes
`[]` on every one of the seven buses and disturbs no balance argument at all.

That makes the honest interim shape an empty row list rather than a padding row, and it is why the
facts below are vacuous rather than proved against a concrete row. When the compiler learns to emit
real syscall events (the phase that also retires `HaltChip`), `Occurrence .syscallInstrs` stops
being `Empty`, this map becomes a real row builder, and these theorems acquire a
`ComputableWitnesses` obligation that an empty table does not have. -/

namespace SP1Clean.SyscallInstrsChip

open Circuit
open Air.Flat

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The `SyscallInstrs` table as a flat-AIR component. -/
def component : Component (ZMod p) := { circuit := circuit }

/-- The table's row list from its (for now uninhabited) occurrence list: no rows. Stated as the
literal empty list rather than `events.map Empty.elim`, so every fact below is a `rfl` away. -/
def syscallInstrsTraceInputs (_events : List Empty) : List ((component (p := p)).Input (ZMod p)) := []

@[simp] theorem syscallInstrsTraceInputs_eq_nil (events : List Empty) :
    syscallInstrsTraceInputs (p := p) events = [] := rfl

/-- The built table has no rows. Every fact below is this one plus vacuity. -/
theorem traceTable_table (events : List Empty) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    (Table.build (component (p := p)) (syscallInstrsTraceInputs events) data hint).table = [] := by
  rfl

theorem traceTable_constraints (events : List Empty) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    (Table.build (component (p := p)) (syscallInstrsTraceInputs events) data hint).Constraints data := by
  intro row hrow
  rw [traceTable_table] at hrow
  exact absurd hrow List.not_mem_nil

theorem traceTable_guarantees (events : List Empty) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    (Table.build (component (p := p)) (syscallInstrsTraceInputs events) data hint).Guarantees data := by
  intro row hrow
  rw [traceTable_table] at hrow
  exact absurd hrow List.not_mem_nil

/-- The table is silent on every channel — including the two buses it is the only table able to
speak on. -/
theorem traceTable_interactionsWith (events : List Empty) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (channel : RawChannel (ZMod p)) :
    (Table.build (component (p := p)) (syscallInstrsTraceInputs events) data hint).interactionsWith data
      channel = [] := by
  rfl

end SP1Clean.SyscallInstrsChip
