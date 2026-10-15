module

public import ToClean.Air.PublicVerifier
public import ToClean.Air.VerifierExtension

/-! # Exact physical ensemble accounting

Clean's raw balance condition bounds occurrence counts but has no shared interface relating them
to physical table heights and static circuit interaction widths. This addition counts the literal
ledger: zero multiplicities, duplicate keys, padding and every verifier interaction all count. The
native compiler and installed resource verifier consume these equations; no semantic execution
model or conservative admission predicate is introduced.
-/

@[expose] public section

namespace Air.Flat
open Circuit

variable {F : Type} [FiniteField F] {PublicIO : TypeMap} [ProvableType PublicIO]

/-- Number of syntactic interactions with this channel in each physical row. -/
noncomputable def Component.channelWidth (component : Component F) (channel : RawChannel F) : ℕ :=
  (component.operations.interactionsWith channel).length

/-- Every physical row contributes its full circuit width, even if all multiplicities are zero. -/
theorem Table.interactionsWith_length (table : Table F) (data : ProverData F) (channel : RawChannel F) :
    (table.interactionsWith data channel).length = table.length * table.component.channelWidth channel := by
  simp only [Table.interactionsWith, List.length_flatMap, Operations.interactionValuesWith, List.length_map]
  simp [Component.channelWidth, Table.length, List.sum_replicate]

namespace EnsembleWitness
variable {ens : Ensemble F PublicIO}

/-- Exact heights of the committed physical tables. The verifier contributes no physical row. -/
def tableHeights (witness : EnsembleWitness ens) : List ℕ := witness.tables.map Table.length

/-- Exact per-channel cost, summed over the literal physical inventory. -/
noncomputable def channelOccurrences (witness : EnsembleWitness ens) (channel : RawChannel F) : ℕ :=
  (ens.verifierOperations.interactionsWith channel).length +
    (witness.tables.map fun table => table.length * table.component.channelWidth channel).sum

/-- The static height-times-width computation is exactly the evaluated ledger's occurrence count. -/
theorem channelOccurrences_eq_length (witness : EnsembleWitness ens) (channel : RawChannel F) :
    witness.channelOccurrences channel = (witness.interactionsWith channel).length := by
  simp only [channelOccurrences, EnsembleWitness.interactionsWith, verifierInteractionsWith,
    tableContext, TableContext.interactionsWith, List.length_append, List.length_flatMap,
    Operations.interactionValuesWith, List.length_map, Table.interactionsWith_length]

/-- Physical height accounting follows the canonical table inventory exactly. -/
theorem tableHeights_eq (witness : EnsembleWitness ens) :
    witness.tableHeights = witness.tables.map Table.length := rfl

/-- Separate the verifier's exact cost from every provider, instruction and administrative table. -/
theorem channelOccurrences_eq (witness : EnsembleWitness ens) (channel : RawChannel F) :
    witness.channelOccurrences channel = (ens.verifierOperations.interactionsWith channel).length +
      (witness.tables.map fun table => table.length * table.component.channelWidth channel).sum := rfl

/-- Each table's full contribution is bounded by the total; duplicate tables remain repeated terms. -/
theorem table_cost_le (witness : EnsembleWitness ens) {table : Table F}
    (member : table ∈ witness.tables) (channel : RawChannel F) :
    table.length * table.component.channelWidth channel ≤ witness.channelOccurrences channel := by
  apply le_trans (b := (witness.tables.map fun table => table.length * table.component.channelWidth channel).sum)
  · apply List.single_le_sum (fun _ _ => Nat.zero_le _)
    exact List.mem_map.mpr ⟨table, member, rfl⟩
  · exact Nat.le_add_left ..

/-- A table with a real syntactic channel interaction spends at least one occurrence per row.
Multiplicity zero does not make a row free. -/
theorem table_length_le_occurrences (witness : EnsembleWitness ens) {table : Table F}
    (member : table ∈ witness.tables) (channel : RawChannel F)
    (positive : 0 < table.component.channelWidth channel) :
    table.length ≤ witness.channelOccurrences channel :=
  (Nat.le_mul_of_pos_right _ positive).trans (witness.table_cost_le member channel)

/-- Inclusive physical budgets, measured from actual rows and every registered channel. -/
def PhysicalFits (witness : EnsembleWitness ens) (rows occurrences : ℕ) : Prop :=
  (∀ height ∈ witness.tableHeights, height ≤ rows) ∧
    ∀ channel ∈ ens.channels, witness.channelOccurrences channel ≤ occurrences

/-- Clean's finite-characteristic capacity condition, over the complete registered-channel list. -/
def ChannelCapacity (witness : EnsembleWitness ens) (characteristic : ℕ) : Prop :=
  ∀ channel ∈ ens.channels, witness.channelOccurrences channel < characteristic

/-- The shared capacity interface is precisely the existing raw ledger bound. -/
theorem channelCapacity_iff (witness : EnsembleWitness ens) (characteristic : ℕ) :
    witness.ChannelCapacity characteristic ↔
      ∀ channel ∈ ens.channels, (witness.interactionsWith channel).length < characteristic := by
  simp only [ChannelCapacity, channelOccurrences_eq_length]

/-- Inclusive resource ceilings below the characteristic suffice for Clean's occurrence bound. -/
theorem PhysicalFits.capacity {witness : EnsembleWitness ens} {rows occurrences characteristic : ℕ}
    (fits : witness.PhysicalFits rows occurrences) (small : occurrences < characteristic) :
    witness.ChannelCapacity characteristic :=
  fun channel member => Nat.lt_of_le_of_lt (fits.2 channel member) small

/-- Accepted witnesses already satisfy the exact all-channel finite-field capacity condition. -/
theorem channelCapacity_of_balanced (witness : EnsembleWitness ens)
    (balanced : witness.BalancedChannels) (positive : 0 < ringChar F) :
    witness.ChannelCapacity (ringChar F) := by
  intro channel member
  rw [channelOccurrences_eq_length]
  exact (balanced channel member).1.resolve_right (Nat.ne_of_gt positive)

/-- Adding raw rows has additive cost; field cancellation cannot recover spent occurrence capacity. -/
theorem table_cost_append (component : Component F) (channel : RawChannel F) (left right : ℕ) :
    (left + right) * component.channelWidth channel =
      left * component.channelWidth channel + right * component.channelWidth channel := Nat.add_mul ..

/-- An exact per-table expansion and its verifier cost suffice for physical construction bounds.
This is an arithmetic construction lemma, not an added semantic-domain premise. -/
theorem physicalFits_iff (witness : EnsembleWitness ens) (rows occurrences : ℕ) :
    witness.PhysicalFits rows occurrences ↔
      (∀ table ∈ witness.tables, table.length ≤ rows) ∧
        ∀ channel ∈ ens.channels, (ens.verifierOperations.interactionsWith channel).length +
          (witness.tables.map fun table => table.length * table.component.channelWidth channel).sum ≤ occurrences := by
  simp only [PhysicalFits, tableHeights_eq, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, channelOccurrences_eq]

end EnsembleWitness

namespace PublicVerifier
variable (check : PublicVerifier F PublicIO) {ens : Ensemble F PublicIO}

/-- Public checks allocate no physical rows, so every physical table height is retained. -/
theorem project_tableHeights (witness : EnsembleWitness (check.install ens)) :
    (check.project witness).tableHeights = witness.tableHeights := by
  simp only [EnsembleWitness.tableHeights_eq, project_tables]

/-- Every channel other than the added check channel retains its exact occurrence count. -/
theorem project_channelOccurrences (witness : EnsembleWitness (check.install ens)) (channel : RawChannel F)
    (different : check.channel ens ≠ channel) :
    (check.project witness).channelOccurrences channel = witness.channelOccurrences channel := by
  simp only [EnsembleWitness.channelOccurrences_eq_length, check.project_interactions witness channel different]

/-- The added channel counts two literal occurrences for each assertion, even for repeated zeros. -/
theorem installed_channelOccurrences (witness : EnsembleWitness (check.install ens)) :
    witness.channelOccurrences (check.channel ens) =
      2 * (check.assertions (varFromOffset PublicIO 0)).length := by
  rw [EnsembleWitness.channelOccurrences_eq_length, check.installed_check_interactions]
  change ((Verifier.checkZeros (check.channelName ens)
    (check.assertions (varFromOffset PublicIO 0))).circuitOperations.interactionValuesWith
      (Verifier.zeroChannel (check.channelName ens)).toRaw
      (Environment.fromInput witness.publicInput witness.data)).length = _
  rw [Verifier.checkZeros_values]
  simp [List.length_flatMap, Nat.mul_comm]

/-- Installation adds exactly the new channel's occurrence cost to the physical budget obligations. -/
theorem project_physicalFits (witness : EnsembleWitness (check.install ens)) (rows occurrences : ℕ) :
    witness.PhysicalFits rows occurrences ↔
      (check.project witness).PhysicalFits rows occurrences ∧
        2 * (check.assertions (varFromOffset PublicIO 0)).length ≤ occurrences := by
  have different (channel : RawChannel F) (member : channel ∈ ens.channels) :
      check.channel ens ≠ channel := by
    intro same
    exact check.channel_not_mem ens (same ▸ member)
  constructor
  · intro fits
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa only [project_tableHeights] using fits.1
    · intro channel member
      rw [check.project_channelOccurrences witness channel (different channel member)]
      exact fits.2 channel (List.mem_append_left _ member)
    · rw [← check.installed_channelOccurrences witness]
      exact fits.2 (check.channel ens) (by simp [install])
  · rintro ⟨fits, bound⟩
    refine ⟨?_, ?_⟩
    · simpa only [project_tableHeights] using fits.1
    · intro channel member
      change channel ∈ ens.channels ++ [check.channel ens] at member
      rcases List.mem_append.mp member with member | member
      · rw [← check.project_channelOccurrences witness channel (different channel member)]
        exact fits.2 channel member
      · obtain rfl := List.mem_singleton.mp member
        rwa [check.installed_channelOccurrences witness]

end PublicVerifier
namespace ClosedVerifier
variable (closed : ClosedVerifier F) {ens : Ensemble F PublicIO}

/-- Closed boundaries allocate no committed rows; only their verifier ledger changes. -/
theorem project_tableHeights (witness : EnsembleWitness (closed.install ens)) :
    (closed.project witness).tableHeights = witness.tableHeights := by
  simp only [EnsembleWitness.tableHeights_eq, project_tables]

/-- The new check channel retains both occurrences of each assertion, including equal zeros. -/
theorem installed_channelOccurrences (witness : EnsembleWitness (closed.install ens)) :
    witness.channelOccurrences (closed.channel ens) = 2 * closed.operations.constraints.length := by
  rw [EnsembleWitness.channelOccurrences_eq_length, closed.installed_check_interactions]
  change ((Verifier.checkZeros (closed.channelName ens) closed.operations.constraints).circuitOperations.interactionValuesWith
    (Verifier.zeroChannel (closed.channelName ens)).toRaw
    (Environment.fromInput witness.publicInput witness.data)).length = _
  rw [Verifier.checkZeros_values]
  simp [List.length_flatMap, Nat.mul_comm]

end ClosedVerifier

end Air.Flat
