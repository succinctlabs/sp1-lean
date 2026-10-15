module

public import ToClean.Air.EnsembleBuild
public import ToClean.Air.FiniteLookup

/-! # Executable checking of finite ensemble witnesses

Clean's witness-generation checks reject legacy lookups and normalize away zero-multiplicity
occurrences. This addition authenticates finite lookup membership and proves an executable check
equivalent to the raw constraints and channel balances, including their occurrence bounds.

The checker evaluates Clean's canonical physical data and complete interaction ledger directly.
The public verifier contributes interactions, never a synthetic physical table. This API belongs
upstream beside ensemble checking; it has no serialization or witness-generation dependency.
-/

@[expose] public section

namespace Air.Flat

open Circuit

variable {F : Type} [FiniteField F]
variable {PublicIO : TypeMap} [ProvableType PublicIO] {ens : Ensemble F PublicIO}

/-- Finite lookup meanings and channel identities needed to execute the raw ensemble relation.
Component names and physical order are already authenticated by the ensemble itself. -/
structure EnsembleCheck (ens : Ensemble F PublicIO) where
  /-- Finite enumerations authenticated against the original lookup predicates. -/
  lookups : List (FiniteLookup F)
  lookups_unique : (lookups.map (fun lookup => lookup.table.name)).Nodup
  lookups_complete : ∀ component ∈ ens.tables, ∀ lookup ∈ component.operations.lookups,
    ∃ fixed ∈ lookups, fixed.table = lookup.table
  channels_unique : (ens.channels.map RawChannel.name).Nodup
  channels_complete : ∀ component ∈ ens.tables,
    ∀ interaction ∈ component.operations.interactions, interaction.channel ∈ ens.channels
  verifier_channels_complete : ∀ interaction ∈ ens.verifierOperations.interactions,
    interaction.channel ∈ ens.channels

variable [DecidableEq F]

/-- Check the complete finite support and the raw occurrence capacity of an interaction list. -/
def checkInteractionBalance (characteristic : ℕ) (interactions : List (Interaction F)) : Bool :=
  decide (interactions.length < characteristic ∨ characteristic = 0) &&
    interactions.all (fun interaction => balanceOf interactions interaction.msg == 0)

/-- Messages outside the enumerated support have zero balance as well. -/
theorem checkInteractionBalance_iff (characteristic : ℕ) [CharP F characteristic]
    (interactions : List (Interaction F)) :
    checkInteractionBalance characteristic interactions = true ↔ BalancedInteractions interactions := by
  simp only [checkInteractionBalance, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq, BalancedInteractions, ringChar.eq F characteristic]
  apply and_congr_right
  intro _
  constructor
  · intro checked message
    by_cases present : ∃ interaction ∈ interactions, interaction.msg = message
    · obtain ⟨interaction, member, rfl⟩ := present
      exact checked interaction member
    · rw [balanceOf_eq_of_const_mult (mult := 0)
        (fun interaction member equal => (present ⟨interaction, member, equal⟩).elim), zero_mul]
  · intro checked interaction _
    exact checked interaction.msg

namespace EnsembleCheck

/-- Membership in the authenticated finite lookup inventory. -/
def containsFixed (description : EnsembleCheck ens) (name : String) (entry : Array F) : Bool :=
  description.lookups.any (fun fixed => fixed.table.name == name &&
    fixed.rows.any (fun row => row.toArray == entry))

/-- Lookup names identify the original predicate, independently of the prover-data environment. -/
theorem containsFixed_iff (description : EnsembleCheck ens) {component : Component F}
    (member : component ∈ ens.tables) {lookup : Lookup F}
    (used : lookup ∈ component.operations.lookups) (env : Environment F) :
    description.containsFixed lookup.table.name (lookup.entry.map env).toArray = true ↔
      lookup.Contains env := by
  obtain ⟨fixed, fixedMem, tableEq⟩ := description.lookups_complete component member lookup used
  rcases lookup with ⟨table, entry⟩
  cases tableEq
  change description.containsFixed fixed.table.name (entry.map env).toArray = true ↔
    fixed.table.Contains (env.data fixed.table.name fixed.table.arity) (entry.map env)
  rw [fixed.realizes]
  simp only [containsFixed, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨selected, selectedMem, nameEq, row, rowMem, rowEq⟩
    have selectedEq := List.inj_on_of_nodup_map description.lookups_unique selectedMem fixedMem nameEq
    subst selected
    rw [Vector.toArray_inj.mp rowEq] at rowMem
    exact rowMem
  · intro member
    exact ⟨fixed, fixedMem, rfl, entry.map env, member, rfl⟩

/-- Evaluate the component's actual assertions and authenticated fixed lookups. -/
def checkRow (description : EnsembleCheck ens) (component : Component F)
    (env : Environment F) : Bool :=
  component.operations.constraints.all (fun expression => env expression == 0) &&
    component.operations.lookups.all (fun lookup =>
      description.containsFixed lookup.table.name (lookup.entry.map env).toArray)

/-- Row checking agrees with Clean's constraint predicate, including nested subcircuits. -/
theorem checkRow_iff (description : EnsembleCheck ens) {component : Component F}
    (member : component ∈ ens.tables) (env : Environment F) :
    description.checkRow component env = true ↔ component.operations.ConstraintsHold env := by
  simp only [checkRow, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
    Operations.ConstraintsHold]
  apply and_congr_right
  intro _
  exact forall₂_congr fun lookup used => description.containsFixed_iff member used env

/-- Check every physical row under the canonical data of its containing witness. -/
def checkTable (description : EnsembleCheck ens) (data : ProverData F) (table : Table F) : Bool :=
  table.table.all (fun row =>
    description.checkRow table.component (Environment.fromArray row data))

/-- Finite table checking agrees with the table's raw constraints. -/
theorem checkTable_iff (description : EnsembleCheck ens) (data : ProverData F) {table : Table F}
    (member : table.component ∈ ens.tables) :
    description.checkTable data table = true ↔ table.Constraints data := by
  simp only [checkTable, List.all_eq_true, Table.Constraints]
  exact forall₂_congr fun row _ => description.checkRow_iff member (Environment.fromArray row data)

omit [DecidableEq F] in
/-- Every evaluated occurrence, including the separate verifier's, uses a registered channel. -/
theorem interaction_registered (description : EnsembleCheck ens) (witness : EnsembleWitness ens)
    {interaction : Interaction F} (member : interaction ∈ witness.interactions) :
    interaction.channel ∈ ens.channels := by
  simp only [EnsembleWitness.interactions, List.mem_append, Operations.interactionValues,
    List.mem_map, List.mem_flatMap, Table.interactions] at member
  rcases member with ⟨abstract, used, rfl⟩ | ⟨table, tableMem, row, _, abstract, used, rfl⟩
  · exact description.verifier_channels_complete abstract used
  · exact description.channels_complete table.component
      (EnsembleWitness.mem_component_of_mem tableMem) abstract used

omit [DecidableEq F] in
/-- Filtering the canonical ledger by name preserves exactly the registered raw channel. -/
theorem interactionsNamed_eq (description : EnsembleCheck ens) (witness : EnsembleWitness ens)
    {channel : RawChannel F} (registered : channel ∈ ens.channels) :
    witness.interactions.filter (fun interaction => interaction.channel.name == channel.name) =
      witness.interactionsWith channel := by
  classical
  rw [witness.interactionsWith_eq_filter]
  apply List.filter_congr
  intro interaction member
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  exact ⟨List.inj_on_of_nodup_map description.channels_unique
    (description.interaction_registered witness member) registered, congrArg RawChannel.name⟩

/-- Check raw constraints and balances without removing repeated or disabled interactions. -/
def checkWitness (description : EnsembleCheck ens) (characteristic : ℕ)
    (witness : EnsembleWitness ens) : Bool :=
  let ledger := witness.interactions
  witness.tables.all (description.checkTable witness.data) &&
    ens.channels.all (fun channel =>
      checkInteractionBalance characteristic
        (ledger.filter fun interaction => interaction.channel.name == channel.name))

/-- Computed acceptance is equivalent to the two raw Clean witness predicates. -/
theorem checkWitness_iff (description : EnsembleCheck ens) (characteristic : ℕ)
    [CharP F characteristic] (witness : EnsembleWitness ens) :
    description.checkWitness characteristic witness = true ↔
      witness.Constraints ∧ witness.BalancedChannels := by
  rw [EnsembleWitness.constraints_iff]
  simp only [checkWitness, Bool.and_eq_true, List.all_eq_true,
    EnsembleWitness.BalancedChannels]
  apply and_congr
  · exact forall₂_congr fun table member => description.checkTable_iff witness.data
      (EnsembleWitness.mem_component_of_mem member)
  · apply forall₂_congr
    intro channel registered
    rw [checkInteractionBalance_iff, description.interactionsNamed_eq witness registered]

/-- A checked physical witness establishes the ensemble's public statement. -/
theorem statement_of_checkWitness (description : EnsembleCheck ens) (characteristic : ℕ)
    [CharP F characteristic] (witness : EnsembleWitness ens)
    (checked : description.checkWitness characteristic witness = true) :
    ens.Statement witness.publicInput :=
  ⟨witness, rfl, (description.checkWitness_iff characteristic witness).mp checked⟩

end EnsembleCheck

end Air.Flat
