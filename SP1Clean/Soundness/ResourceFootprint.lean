import SP1Clean.Soundness.ResourceEnsemble
import ToClean.Air.Footprint

/-! # Physical resource consumers for the installed native assembly

Count actual physical tables and every verifier ledger occurrence. The endpoint checker preserves
all physical rows and adds exactly six occurrences on its fresh assertion channel. Raw acceptance
supplies every registered channel's native field-count ceiling. Tighter independent ceilings and
full mixed construction demand remain A4/A5/A6 obligations; they are not capstone caller premises.
-/

namespace SP1Clean.Soundness.ResourceEnsemble
open Circuit Air.Flat Model.Core Machine

variable {p : ℕ} [Fact p.Prime]

/-- Rows and old ledgers are unchanged; the new assertion channel requires exactly six occurrences. -/
theorem physicalFits_iff {limits : ResourceLimits} {source target : ExecutionSnapshot}
    {base : Ensemble (ZMod p) SP1PublicIO}
    (witness : EnsembleWitness (install limits source target base)) :
    witness.PhysicalFits limits.tableRows limits.channelOccurrences ↔
      ((ResourceBoundary.checker limits source target).project witness).PhysicalFits
        limits.tableRows limits.channelOccurrences ∧ 6 ≤ limits.channelOccurrences :=
  (ResourceBoundary.checker limits source target).project_physicalFits witness _ _

/-- Every registered ledger of an accepted witness satisfies the native inclusive field ceiling.
This covers arbitrary installed host/boundary channels rather than a selected channel enum. -/
theorem accepted_channel_budget {base : Ensemble (ZMod p) SP1PublicIO}
    (witness : EnsembleWitness base) (balanced : witness.BalancedChannels) :
    ∀ channel ∈ base.channels,
      witness.channelOccurrences channel ≤ (ResourceLimits.native p).channelOccurrences := by
  have capacity : witness.ChannelCapacity p := by
    simpa only [ZMod.ringChar_zmod_n] using witness.channelCapacity_of_balanced balanced
      (by simpa only [ZMod.ringChar_zmod_n] using (Fact.out : p.Prime).pos)
  intro channel member
  have bound := capacity channel member
  change _ ≤ p - 1
  omega

/-- Any table emitting into a registered channel inherits its physical height bound, even with
inactive rows. A silent table needs a separate height check; balance cannot bound it. -/
theorem accepted_table_budget {base : Ensemble (ZMod p) SP1PublicIO}
    (witness : EnsembleWitness base) (balanced : witness.BalancedChannels)
    {table : Table (ZMod p)} (member : table ∈ witness.tables)
    {channel : RawChannel (ZMod p)} (registered : channel ∈ base.channels)
    (emits : 0 < table.component.channelWidth channel) :
    table.length ≤ (ResourceLimits.native p).tableRows :=
  (witness.table_length_le_occurrences member channel emits).trans
    (accepted_channel_budget witness balanced channel registered)

/-- For a base witness that fits, the six assertion occurrences are the exact remaining cost.
No row, provider occurrence or host resource is dropped by the adapter. -/
theorem lift_physicalFits {limits : ResourceLimits} {source target : ExecutionSnapshot}
    {base : Ensemble (ZMod p) SP1PublicIO} (witness : EnsembleWitness base)
    (fits : witness.PhysicalFits limits.tableRows limits.channelOccurrences) :
    ((ResourceBoundary.checker limits source target).lift witness).PhysicalFits
      limits.tableRows limits.channelOccurrences ↔ 6 ≤ limits.channelOccurrences :=
  (physicalFits_iff (limits := limits) (source := source) (target := target)
    ((ResourceBoundary.checker limits source target).lift witness)).trans (and_iff_right fits)

/-- An admissible endpoint and accepted base witness satisfy the installed verifier. Its exact
six-occurrence overhead remains explicit for arbitrary budgets; the semantic domain is unchanged.
Remaining mixed construction belongs to A6. -/
theorem lift_of_admissible [Fact (2 ^ 25 < p)] {limits : ResourceLimits} {image : ProgramImage}
    {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    {base : Ensemble (ZMod p) SP1PublicIO} (witness : EnsembleWitness base)
    (execution : FormalModel.Shard.AdmissibleExecution limits p image source target events)
    (clock : ResourceBoundary.ClockFor target witness.publicInput)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (fits : witness.PhysicalFits limits.tableRows limits.channelOccurrences) :
    let lifted := (ResourceBoundary.checker limits source target).lift witness
    lifted.Constraints ∧ lifted.BalancedChannels ∧
      (lifted.PhysicalFits limits.tableRows limits.channelOccurrences ↔ 6 ≤ limits.channelOccurrences) := by
  refine ⟨constraints, ?_, lift_physicalFits witness fits⟩
  apply ((ResourceBoundary.checker limits source target).project_balanced_iff _).mpr
  exact ⟨balanced, ResourceBoundary.count_bound limits source target,
    checks_of_admissible execution clock witness.data⟩

end SP1Clean.Soundness.ResourceEnsemble
