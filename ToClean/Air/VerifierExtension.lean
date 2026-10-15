module

public import ToClean.Air.VerifierChannel
public import ToClean.Circuit.VerifierInteractions
public import Clean.Circuit.Foundations

/-! # Exactly-once closed circuits in an ensemble verifier

Clean's public verifier can run a closed circuit's certified interactions and enforce its raw
assertions through a fresh zero-check channel. This adapter reuses the circuit's semantic proof
and Clean's verifier operations. The physical table inventory and its canonical prover data stay
unchanged. A singleton table is available only as a local proof representation, evaluated at
explicit data; it is never appended to the committed inventory.

Zero witness length alone does not establish independence from ambient cells. The adapter also
requires the circuit's static transport laws, absent lookups, and Clean's unconditional admission
proof for each verifier interaction. These are construction obligations, not execution premises.
Move this adapter upstream when Clean supplies equivalent circuit-to-verifier composition.
-/

@[expose] public section

namespace Air.Flat
open Circuit

variable {F : Type} [FiniteField F]

/-- A proved closed boundary admitted to Clean's public verifier. -/
structure ClosedVerifier (F : Type) [FiniteField F] where
  /-- Stable stem used when allocating this boundary's fresh assertion channel. -/
  name : String
  circuit : GeneralFormalCircuit F unit unit
  assumptions : ∀ data, circuit.Assumptions () data
  length_zero : circuit.localLength () = 0
  lookups : ((circuit.main ()).operations 0).lookups = []
  public_interactions : ∀ interaction ∈ ((circuit.main ()).operations 0).interactions, ∀ env,
    if interaction.assumeGuarantees then interaction.Requirements env else interaction.Guarantees env
  constraints : ∀ offset env, ((circuit.main ()).operations offset).ConstraintsHold env ↔
    ((circuit.main ()).operations 0).ConstraintsHold (Environment.fromInput (Input := unit) () env.data)
  interactions : ∀ offset env channel,
    ((circuit.main ()).operations offset).interactionValuesWith channel env =
      ((circuit.main ()).operations 0).interactionValuesWith channel
        (Environment.fromInput (Input := unit) () env.data)

namespace ClosedVerifier
variable (closed : ClosedVerifier F)

/-- Literal raw operations of the proved circuit, at its closed input. -/
abbrev operations : Operations F := (closed.circuit.main ()).operations 0

/-- Acceptance of the source circuit at the ensemble's explicit data. -/
def Checks (data : ProverData F) : Prop :=
  closed.operations.ConstraintsHold (Environment.fromInput (Input := unit) () data)

/-- The added check ledger spends two occurrences for every assertion. -/
def CountBound : Prop :=
  2 * closed.operations.constraints.length < ringChar F ∨ ringChar F = 0

/-- A local proof representation; this row is not a committed ensemble table. -/
def singleton : Table F where
  component := { circuit := closed.circuit }
  table := [#[]]
  uniform_width := by
    intro row member
    obtain rfl := List.mem_singleton.mp member
    rw [Component.width, GeneralFormalCircuit.size_eq]
    simpa only [Array.size_empty, show size unit = 0 from rfl, Nat.zero_add] using closed.length_zero.symm

theorem singleton_constraints (data : ProverData F) :
    closed.singleton.Constraints data ↔ closed.Checks data := by
  simp only [Table.Constraints, singleton, List.mem_singleton, forall_eq]
  exact Component.constraintsHold_iff _

theorem singleton_interactions (data : ProverData F) (channel : RawChannel F) :
    closed.singleton.interactionsWith data channel =
      closed.operations.interactionValuesWith channel (Environment.fromInput (Input := unit) () data) := by
  simp only [Table.interactionsWith, singleton, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Operations.interactionValuesWith, Component.interactionsWith_eq]
  rfl

/-- Every source interaction is admitted through Clean's own verifier operation constructor. -/
def emit : Verifier F Unit :=
  Verifier.ofInteractions closed.operations.interactions closed.public_interactions

theorem emit_interactions : closed.emit.circuitOperations.interactions = closed.operations.interactions :=
  Verifier.ofInteractions_interactions _ _

theorem emit_values (env : Environment F) (channel : RawChannel F) :
    closed.emit.circuitOperations.interactionValuesWith channel env =
      closed.operations.interactionValuesWith channel (Environment.fromInput (Input := unit) () env.data) := by
  rw [emit, Verifier.ofInteractions_values]
  exact closed.interactions 0 env channel

variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-- Interaction-only projection, used to choose a channel disjoint from all existing traffic. -/
def interactionProgram : Verifier.Program F PublicIO where
  main _ := closed.emit

/-- Retain the source interactions while forgetting only the added assertion checks. -/
def withInteractions (ens : Ensemble F PublicIO) : Ensemble F PublicIO where
  tables := ens.tables
  unique_names := ens.unique_names
  channels := ens.channels ++ closed.circuit.channels
  verifier := ens.verifier.andThen closed.interactionProgram

/-- Freshness includes the boundary's original interactions as well as the enclosing ensemble. -/
abbrev channelName (ens : Ensemble F PublicIO) : String :=
  VerifierChannel.channelName closed.name (closed.withInteractions ens)

/-- Dedicated channel for the boundary's raw assertions. -/
abbrev channel (ens : Ensemble F PublicIO) : RawChannel F :=
  VerifierChannel.channel closed.name (closed.withInteractions ens)

/-- Reuse the proved circuit's semantic specification in Clean's public verifier. -/
def program (ens : Ensemble F PublicIO) : Verifier.Program F PublicIO where
  main _ := do
    closed.emit
    Verifier.checkZeros (closed.channelName ens) closed.operations.constraints
  Spec _ data := closed.circuit.Spec () () data
  soundness := by
    intro env guarantees
    simp only [Verifier.operations_bind, Verifier.Operations.circuitOperations,
      Verifier.Operations.interactions, List.map_append, Operations.FullGuarantees,
      Operations.interactions_append, List.forall_mem_append] at guarantees
    have original : closed.operations.FullGuarantees env := by
      rw [Operations.FullGuarantees, ← closed.emit_interactions]
      exact guarantees.1
    have checks := (Verifier.checkZeros_guarantees (closed.channelName ens)
      closed.operations.constraints env).mp guarantees.2
    have checked : closed.operations.ConstraintsHold env := by
      refine ⟨checks, ?_⟩
      simp [operations, closed.lookups]
    exact (closed.circuit.original_full_soundness 0 env () (closed.assumptions _)
      checked original).1

/-- Invoke the boundary once without adding a physical row or changing canonical prover data. -/
def install (ens : Ensemble F PublicIO) : Ensemble F PublicIO where
  tables := ens.tables
  unique_names := ens.unique_names
  channels := (closed.withInteractions ens).channels ++ [closed.channel ens]
  verifier := ens.verifier.andThen (closed.program ens)

/-- The assertion adapter supplies its own requirements; the source interactions retain theirs. -/
theorem program_requirements (ens : Ensemble F PublicIO) (env : Environment F)
    (requirements : closed.operations.FullRequirements env) :
    (closed.program ens).circuitOperations.FullRequirements env := by
  change (closed.emit >>= fun _ =>
    Verifier.checkZeros (closed.channelName ens) closed.operations.constraints).circuitOperations.FullRequirements env
  simp only [Verifier.circuitOperations, Verifier.operations_bind, Verifier.Operations.circuitOperations,
    Verifier.Operations.interactions, List.map_append, Operations.FullRequirements,
    Operations.interactions_append, List.forall_mem_append]
  constructor
  · change closed.emit.circuitOperations.FullRequirements env
    unfold Operations.FullRequirements
    rw [closed.emit_interactions]
    exact requirements
  · exact Verifier.checkZeros_requirements _ _ _

/-- Forget the boundary while retaining all committed rows. -/
def project {ens : Ensemble F PublicIO} (witness : EnsembleWitness (closed.install ens)) :
    EnsembleWitness ens :=
  EnsembleWitness.ofTables ens witness.tables witness.publicInput witness.tables_map_component

@[simp] theorem project_tables {ens : Ensemble F PublicIO} (witness : EnsembleWitness (closed.install ens)) :
    (closed.project witness).tables = witness.tables := rfl

@[simp] theorem project_data {ens : Ensemble F PublicIO} (witness : EnsembleWitness (closed.install ens)) :
    (closed.project witness).data = witness.data := rfl

@[simp] theorem project_publicInput {ens : Ensemble F PublicIO} (witness : EnsembleWitness (closed.install ens)) :
    (closed.project witness).publicInput = witness.publicInput := rfl

/-- Raw physical constraints are unchanged; verifier assertions are enforced by balance. -/
theorem project_constraints {ens : Ensemble F PublicIO} (witness : EnsembleWitness (closed.install ens)) :
    witness.Constraints ↔ (closed.project witness).Constraints := Iff.rfl

/-- Forget only the assertion checks, keeping the exactly-once boundary interactions. -/
def interactionView {ens : Ensemble F PublicIO} (witness : EnsembleWitness (closed.install ens)) :
    EnsembleWitness (closed.withInteractions ens) :=
  EnsembleWitness.ofTables _ witness.tables witness.publicInput witness.tables_map_component

@[simp] theorem interactionView_data {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness (closed.install ens)) :
    (closed.interactionView witness).data = witness.data := rfl

/-- Exact verifier ledger, including all old traffic and two occurrences per new assertion. -/
theorem verifier_interactions (ens : Ensemble F PublicIO) (env : Environment F) (selected : RawChannel F) :
    (closed.install ens).verifierOperations.interactionValuesWith selected env =
      (closed.withInteractions ens).verifierOperations.interactionValuesWith selected env ++
        (Verifier.checkZeros (closed.channelName ens) closed.operations.constraints).circuitOperations.interactionValuesWith
          selected env := by
  simp only [install, withInteractions, Ensemble.verifierOperations, Verifier.Program.andThen_values]
  change _ ++ ((closed.emit >>= fun _ => Verifier.checkZeros (closed.channelName ens)
    closed.operations.constraints).circuitOperations.interactionValuesWith selected env) = _
  simp only [Verifier.circuitOperations, Verifier.operations_bind, Verifier.Operations.circuitOperations,
    Verifier.Operations.interactions, List.map_append, Operations.interactionValuesWith,
    Operations.interactionsWith, Operations.interactions_append, List.filter_append, List.map_append,
    List.append_assoc]
  rfl

/-- On every other channel, removing assertion checks preserves the complete literal ledger. -/
theorem interactionView_interactions {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness (closed.install ens)) (selected : RawChannel F)
    (different : closed.channel ens ≠ selected) :
    (closed.interactionView witness).interactionsWith selected = witness.interactionsWith selected := by
  change _ = (closed.install ens).verifierOperations.interactionValuesWith selected
    (Environment.fromInput witness.publicInput witness.data) ++ _
  rw [closed.verifier_interactions,
    Verifier.checkZeros_other_values _ _ _ _ different, List.append_nil]
  rfl

/-- Only the added assertion program can emit on its fresh channel. -/
theorem installed_check_interactions {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness (closed.install ens)) :
    witness.interactionsWith (closed.channel ens) =
      (Verifier.checkZeros (closed.channelName ens) closed.operations.constraints).circuitOperations.interactionValuesWith
        (closed.channel ens) (Environment.fromInput witness.publicInput witness.data) := by
  have fresh := VerifierChannel.fresh closed.name (closed.withInteractions ens)
  have physical : witness.tableContext.interactionsWith (closed.channel ens) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro table member
    apply List.flatMap_eq_nil_iff.mpr
    intro row _
    exact fresh.tables table.component
      (EnsembleWitness.mem_component_of_mem (witness := closed.interactionView witness) member) _
  change (closed.install ens).verifierOperations.interactionValuesWith (closed.channel ens)
    (Environment.fromInput witness.publicInput witness.data) ++ _ = _
  rw [closed.verifier_interactions, fresh.verifier, List.nil_append, physical, List.append_nil]

/-- Balance on the new channel enforces exactly the original closed checks and occurrence bound. -/
theorem check_balanced_iff {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness (closed.install ens)) :
    witness.BalancedChannel (closed.channel ens) ↔ closed.CountBound ∧ closed.Checks witness.data := by
  rw [EnsembleWitness.BalancedChannel, closed.installed_check_interactions]
  change BalancedInteractions ((Verifier.checkZeros (closed.channelName ens) closed.operations.constraints).circuitOperations.interactionValuesWith
    (Verifier.zeroChannel (closed.channelName ens)).toRaw (Environment.fromInput witness.publicInput witness.data)) ↔ _
  rw [Verifier.checkZeros_balanced_iff]
  have transport := closed.constraints 0 (Environment.fromInput witness.publicInput witness.data)
  simpa [CountBound, Checks, Operations.ConstraintsHold, closed.lookups] using
    and_congr (Iff.rfl (a := closed.CountBound)) transport

/-- The assertion channel is separate from both the original registry and the boundary channels. -/
theorem channel_not_mem (ens : Ensemble F PublicIO) :
    closed.channel ens ∉ ens.channels ++ closed.circuit.channels :=
  (VerifierChannel.fresh closed.name (closed.withInteractions ens)).unregistered

/-- On a registered channel, installation adds exactly the source circuit's literal emissions.
The fresh assertion channel contributes no occurrence, including zero multiplicities. -/
theorem install_verifier_interactions_of_mem (ens : Ensemble F PublicIO) (env : Environment F)
    (selected : RawChannel F) (registered : selected ∈ ens.channels) :
    (closed.install ens).verifierOperations.interactionValuesWith selected env =
      ens.verifierOperations.interactionValuesWith selected env ++
        closed.operations.interactionValuesWith selected
          (Environment.fromInput (Input := unit) () env.data) := by
  have different : closed.channel ens ≠ selected := by
    intro same
    exact closed.channel_not_mem ens (same ▸ List.mem_append_left _ registered)
  change (ens.verifier.andThen (closed.program ens)).circuitOperations.interactionValuesWith selected env = _
  rw [Verifier.Program.andThen_values]
  have append : (closed.program ens).circuitOperations.interactionValuesWith selected env =
      closed.emit.circuitOperations.interactionValuesWith selected env ++
        (Verifier.checkZeros (closed.channelName ens) closed.operations.constraints).circuitOperations.interactionValuesWith
          selected env := by
    simp only [Verifier.Program.circuitOperations, Verifier.Program.operations, program,
      Verifier.circuitOperations, Verifier.operations_bind, Verifier.Operations.circuitOperations,
      Verifier.Operations.interactions, List.map_append, Operations.interactionValuesWith,
      Operations.interactionsWith, Operations.interactions_append, List.filter_append]
  rw [append, Verifier.checkZeros_other_values _ _ _ _ different, List.append_nil, closed.emit_values]

/-- Removing only the new checks leaves the original ledger plus one boundary invocation.
The permutation moves that invocation past the physical rows without dropping any occurrence. -/
theorem interactionView_interactions_perm {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness (closed.install ens)) (selected : RawChannel F) :
    ((closed.interactionView witness).interactionsWith selected).Perm
      ((closed.project witness).interactionsWith selected ++
        closed.singleton.interactionsWith witness.data selected) := by
  change ((ens.verifier.andThen closed.interactionProgram).circuitOperations.interactionValuesWith selected
    (Environment.fromInput witness.publicInput witness.data) ++
      witness.tables.flatMap (fun table => table.interactionsWith witness.data selected)).Perm _
  rw [Verifier.Program.andThen_values]
  change ((_ ++ closed.emit.circuitOperations.interactionValuesWith selected
    (Environment.fromInput witness.publicInput witness.data)) ++ _).Perm _
  rw [closed.emit_values, ← closed.singleton_interactions]
  change ((_ ++ closed.singleton.interactionsWith witness.data selected) ++ _).Perm
    ((_ ++ witness.tables.flatMap (fun table => table.interactionsWith witness.data selected)) ++ _)
  simp only [List.append_assoc]
  exact (List.perm_append_comm ..).append_left _

/-- Channels unused by the boundary retain balance and the full original occurrence bound. -/
theorem project_balancedChannel {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness (closed.install ens)) (selected : RawChannel F)
    (registered : selected ∈ ens.channels) (silent : selected ∉ closed.circuit.channels)
    (balanced : witness.BalancedChannel selected) : (closed.project witness).BalancedChannel selected := by
  have different : closed.channel ens ≠ selected := by
    intro same
    exact closed.channel_not_mem ens (show closed.channel ens ∈ ens.channels ++ closed.circuit.channels from
      same ▸ List.mem_append_left _ registered)
  have empty : closed.singleton.interactionsWith witness.data selected = [] :=
    closed.singleton.interactionsWith_nil_of_channel_not_mem silent
  have permutation := closed.interactionView_interactions_perm witness selected
  rw [closed.interactionView_interactions witness selected different, empty, List.append_nil] at permutation
  exact balancedInteractions_of_perm balanced permutation

/-- Accepted boundaries retain the original interactions and enforce every assertion. -/
theorem balanced_iff {ens : Ensemble F PublicIO} (witness : EnsembleWitness (closed.install ens)) :
    witness.BalancedChannels ↔ (closed.interactionView witness).BalancedChannels ∧
      closed.CountBound ∧ closed.Checks witness.data := by
  have fresh := VerifierChannel.fresh closed.name (closed.withInteractions ens)
  have different (selected : RawChannel F) (member : selected ∈ (closed.withInteractions ens).channels) :
      closed.channel ens ≠ selected := by
    intro same
    exact fresh.unregistered (show closed.channel ens ∈ (closed.withInteractions ens).channels from same ▸ member)
  constructor
  · intro balanced
    refine ⟨?_, (closed.check_balanced_iff witness).mp (balanced _ (by simp [install]))⟩
    intro selected member
    change BalancedInteractions ((closed.interactionView witness).interactionsWith selected)
    rw [closed.interactionView_interactions witness selected (different selected member)]
    exact balanced selected (List.mem_append_left _ member)
  · rintro ⟨original, bound, checked⟩ selected member
    rcases List.mem_append.mp member with member | member
    · change BalancedInteractions (witness.interactionsWith selected)
      rw [← closed.interactionView_interactions witness selected (different selected member)]
      exact original selected member
    · obtain rfl := List.mem_singleton.mp member
      exact (closed.check_balanced_iff witness).mpr ⟨bound, checked⟩

end ClosedVerifier
end Air.Flat
