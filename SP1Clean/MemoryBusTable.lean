import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Utils.Field
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Clean.SP1Lookup

/-! # Clean-side mirror of SP1's memory-bus interactions

Mirrors SP1's `send (.memory clk_high prev_low addr_0 addr_1 addr_2 v0 v1 v2 v3) mult`
/ `receive (.memory …) mult` interactions. Unlike `ByteOpcodeTable` (a static
lookup table), the memory bus has **no per-row table-membership check**: a
memory-bus tuple is valid iff the global multiplicity-weighted multiset
across all rows sums to zero per `(addr, clk)` key. That check lives at the
trace level via `LookupAccessList.isConsistentBalanced` from
`SP1Lookup.lean`; here we expose a `MemoryBusTable` whose `Contains` is
unconditionally `True` so chip-level `lookupGated` calls discharge their
row-level obligation trivially while still emitting the bus-tuple data for
trace-level aggregation.

Row layout `#v[clk_high, prev_low, addr_0, addr_1, addr_2, v0, v1, v2, v3]`
matches `AirInteraction.memory` from `SP1Foundations/Constraint.lean:30-39`. -/

namespace SP1Clean

variable {p : ℕ} [Fact p.Prime]

/-- The memory-bus table. `Contains := Soundness := Completeness := True` —
row-level membership is trivial; per-key multiplicity balance is enforced
at the trace level. -/
def MemoryBusTable : Table (ZMod p) (fields 9) where
  name := "SP1Memory"
  Contains _ _ := True
  Soundness _ _ := True
  Completeness _ _ := True

end SP1Clean

namespace SP1Clean

/-- Default row for `MemoryBusTable`: the all-zero 9-tuple. Trivially in
the table since `Contains := True`. -/
instance MemoryBusTable.hasDefaultRow {p : ℕ} [Fact p.Prime] :
    SP1Lookup.HasDefaultRow
      (SP1Clean.MemoryBusTable : Table (ZMod p) (fields 9)) where
  defaultRow := #v[(0 : ZMod p), 0, 0, 0, 0, 0, 0, 0, 0]
  defaultRow_in_table := fun _ => trivial

end SP1Clean

/-! ## `MemoryBusGated` — `lookupGated` for `MemoryBusTable` as a `FormalAssertion`

Wraps a single `lookupGated` call on `MemoryBusTable` into a Clean
`FormalAssertion` (analogous to `SP1Lookup.byteOpcodeGated`) so chips
can compose memory-bus emissions as clean subcircuits via `circuit_proof_start`
rather than wrestling with inline `lookupGated` operations. The chip-level
`Spec` is the disjunctive form `mult = 0 ∨ True`, which collapses to `True`
— the memory bus has no per-row table-membership check; multiplicity
balance is enforced at the trace level. -/

namespace SP1Lookup.MemoryBusGated

open Circuit

variable {p : ℕ} [Fact p.Prime]

/-- Inputs: the 9-element memory tuple and the shared multiplicity. -/
structure Inputs (F : Type) where
  entry : Vector F 9
  mult : F
deriving ProvableStruct

@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit :=
  SP1Lookup.lookupGated SP1Clean.MemoryBusTable input.entry input.mult

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.MemoryBusGated"
  main := main
  localLength _ := 9
  localLength_eq _ _ := by simp only [main, circuit_norm]
  subcircuitsConsistent _ _ := by simp +arith only [main, circuit_norm]

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- Disjunctive Spec: vacuous when `mult = 0`; otherwise `True` (memory
bus has no row-level membership check). -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  input.mult = 0 ∨ True

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  intro offset env input_var input h_input _ _
  -- Spec is `mult = 0 ∨ True`; the right disjunct is always available.
  exact Or.inr trivial

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  intro offset env input_var h_env input h_input _ _
  -- Bridge to lookupGated's completeness with `Or.inr trivial` (MemoryBusTable
  -- accepts any entry).
  apply SP1Lookup.lookupGated_completeness_of_disjunctive
    SP1Clean.MemoryBusTable input_var.entry input_var.mult env offset h_env
  exact Or.inr trivial

end MemoryBusGated

/-- Multiplicity-gated single-row memory-bus emission, as a Clean
`FormalAssertion`. Chip-level Spec is trivial (`True`); the actual
memory-bus consistency lives at the trace level. -/
@[reducible]
def memoryBusGated {p : ℕ} [Fact p.Prime] :
    FormalAssertion (ZMod p) MemoryBusGated.Inputs :=
  { MemoryBusGated.elaborated with
    Assumptions := MemoryBusGated.Assumptions,
    Spec := MemoryBusGated.Spec,
    soundness := MemoryBusGated.soundness,
    completeness := MemoryBusGated.completeness }

end SP1Lookup
