import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Utils.Field
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Clean.SP1Lookup

/-! # Clean-side mirror of SP1's state-bus interactions

Mirrors SP1's `send (.state clk_high clk_low pc0 pc1 pc2) mult` /
`receive (.state ...) mult` interactions. Like the memory bus, the state
bus has **no per-row table-membership check**: a state-bus tuple is valid
iff the global multiplicity-weighted multiset across all rows sums to zero
per `(clk, pc)` key. That check lives at the trace level via
`SP1Clean/Soundness/StateConsistency.lean` (`aggregateStateAccesses` /
`pcChainProp`); here we expose a `StateBusTable` whose `Contains` is
unconditionally `True` so chip-level `lookupGated` calls discharge their
row-level obligation trivially while still emitting the bus-tuple data for
trace-level aggregation.

Row layout `#v[clk_high, clk_combined, pc[0], pc[1], pc[2]]` matches
`AirInteraction.state` from `SP1Foundations/Constraint.lean:12`. -/

namespace SP1Clean

variable {p : ℕ} [Fact p.Prime]

/-- The state-bus table. `Contains := Soundness := Completeness := True` —
row-level membership is trivial; per-key multiplicity balance is enforced
at the trace level by `pcChainProp` over `aggregateStateAccesses`. -/
def StateBusTable : Table (ZMod p) (fields 5) where
  name := "SP1State"
  Contains _ _ := True
  Soundness _ _ := True
  Completeness _ _ := True

end SP1Clean

namespace SP1Clean

/-- Default row for `StateBusTable`: the all-zero 5-tuple. Trivially in
the table since `Contains := True`. -/
instance StateBusTable.hasDefaultRow {p : ℕ} [Fact p.Prime] :
    SP1Lookup.HasDefaultRow
      (SP1Clean.StateBusTable : Table (ZMod p) (fields 5)) where
  defaultRow := #v[(0 : ZMod p), 0, 0, 0, 0]
  defaultRow_in_table := fun _ => trivial

end SP1Clean

/-! ## `StateBusGated` — `lookupGated` for `StateBusTable` as a `FormalAssertion`

Wraps a single `lookupGated` call on `StateBusTable` into a Clean
`FormalAssertion` (analogous to `SP1Lookup.MemoryBusGated`) so CPUState
can compose state-bus emissions (receive at current `pc`, send at
`next_pc`) as clean subcircuits. The chip-level `Spec` is the disjunctive
form `mult = 0 ∨ True`, which collapses to `True` — the state bus has no
per-row table-membership check; multiplicity balance is enforced at the
trace level. -/

namespace SP1Lookup.StateBusGated

open Circuit

variable {p : ℕ} [Fact p.Prime]

/-- Inputs: the 5-element state tuple and the shared multiplicity. -/
structure Inputs (F : Type) where
  entry : Vector F 5
  mult : F
deriving ProvableStruct

@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit :=
  SP1Lookup.lookupGated SP1Clean.StateBusTable input.entry input.mult

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.StateBusGated"
  main := main
  localLength _ := 5
  localLength_eq _ _ := by simp only [main, circuit_norm]
  subcircuitsConsistent _ _ := by simp +arith only [main, circuit_norm]

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- Disjunctive Spec: vacuous when `mult = 0`; otherwise `True` (state
bus has no row-level membership check). -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  input.mult = 0 ∨ True

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  intro offset env input_var input h_input _ _
  exact Or.inr trivial

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  intro offset env input_var h_env input h_input _ _
  apply SP1Lookup.lookupGated_completeness_of_disjunctive
    SP1Clean.StateBusTable input_var.entry input_var.mult env offset h_env
  exact Or.inr trivial

end StateBusGated

/-- Multiplicity-gated single-row state-bus emission, as a Clean
`FormalAssertion`. Chip-level Spec is trivial (`True`); the actual
state-bus consistency lives at the trace level via `pcChainProp`. -/
@[reducible]
def stateBusGated {p : ℕ} [Fact p.Prime] :
    FormalAssertion (ZMod p) StateBusGated.Inputs :=
  { StateBusGated.elaborated with
    Assumptions := StateBusGated.Assumptions,
    Spec := StateBusGated.Spec,
    soundness := StateBusGated.soundness,
    completeness := StateBusGated.completeness }

end SP1Lookup
