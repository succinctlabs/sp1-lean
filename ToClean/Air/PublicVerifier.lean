module

public import ToClean.Air.VerifierChannel
public import ToClean.Circuit.VerifierAssertions
public import Clean.Circuit.Foundations

/-! # Public assertions in an interaction-only verifier

This adapter reuses the assertions and semantic specification of a proved zero-witness circuit.
It installs those assertions through Clean's ordinary verifier interactions: each checked value is
pulled on a dedicated channel and zero is pushed. Physical rows and their canonical derived data
are preserved. The new ledger retains two occurrences per assertion, including repeated zeros.

Installation derives a fresh channel name from the complete registered and actual interaction
inventory. Only Clean's occurrence bound remains a static composition obligation; an execution
caller supplies no extra freshness, readiness or validity hypothesis.
The adapter belongs upstream beside `Verifier.Program` and should disappear when Clean provides
an equivalent public-assertion interface.
-/

@[expose] public section

namespace Air.Flat
open Circuit

variable {F : Type} [FiniteField F] {PublicIO : TypeMap} [ProvableType PublicIO]

/-- A proved public assertion circuit with no private cells, lookups or channel traffic. -/
structure PublicVerifier (F : Type) [FiniteField F] (PublicIO : TypeMap) [ProvableType PublicIO] where
  /-- Human-readable prefix for the automatically separated check-channel name. -/
  name : String
  /-- The semantic proof boundary supplying the actual public assertions. -/
  circuit : GeneralFormalCircuit F PublicIO unit
  /-- The checker requires no unverified soundness precondition. -/
  assumptions : ∀ input data, circuit.Assumptions input data
  /-- Public assertions allocate no private cells. -/
  length_zero : ∀ input, circuit.localLength input = 0
  /-- Every raw lookup obligation is absent. -/
  lookups : ∀ input offset, ((circuit.main input).operations offset).lookups = []
  /-- Channel traffic is supplied solely by the assertion adapter. -/
  interactions : ∀ input offset, ((circuit.main input).operations offset).interactions = []

namespace PublicVerifier
variable (check : PublicVerifier F PublicIO)

/-- The literal assertions of the existing proved circuit. -/
def assertions (input : Var PublicIO F) : List (Expression F) :=
  ((check.circuit.main input).operations (size PublicIO)).constraints

/-- Fresh name derived from the complete original interaction inventory. -/
abbrev channelName (ens : Ensemble F PublicIO) : String :=
  VerifierChannel.channelName check.name ens

/-- Dedicated channel enforcing the public assertions. -/
abbrev channel (ens : Ensemble F PublicIO) : RawChannel F :=
  VerifierChannel.channel check.name ens

/-- Raw acceptance of the original public assertion circuit. -/
def Checks (input : PublicIO F) (data : ProverData F) : Prop :=
  ((check.circuit.main (varFromOffset PublicIO 0)).operations (size PublicIO)).ConstraintsHold
    (Environment.fromInput input data)

/-- Exact count bound for the added pull/push pairs, including repeated zero checks. -/
def CountBound : Prop :=
  2 * (check.assertions (varFromOffset PublicIO 0)).length < ringChar F ∨ ringChar F = 0

/-- Clean's verifier program retains the circuit's semantic specification. -/
def program (ens : Ensemble F PublicIO) : Verifier.Program F PublicIO where
  main input := Verifier.checkZeros (check.channelName ens) (check.assertions input)
  Spec input data := check.circuit.Spec input () data
  soundness := by
    intro env guarantees
    have checked := (Verifier.checkZeros_guarantees (check.channelName ens)
      (check.assertions (varFromOffset PublicIO 0)) env).mp guarantees
    have constraints :
        ((check.circuit.main (varFromOffset PublicIO 0)).operations (size PublicIO)).ConstraintsHold env := by
      refine ⟨checked, ?_⟩
      simp [check.lookups]
    have silent :
        ((check.circuit.main (varFromOffset PublicIO 0)).operations (size PublicIO)).FullGuarantees env := by
      simp [Operations.FullGuarantees, check.interactions]
    exact (check.circuit.original_full_soundness (size PublicIO) env
      (varFromOffset PublicIO 0) (check.assumptions _ _) constraints silent).1

/-- Balance on the fresh channel enforces exactly the old raw assertions and the count bound. -/
theorem program_balanced_iff (ens : Ensemble F PublicIO) (input : PublicIO F) (data : ProverData F) :
    BalancedInteractions ((check.program ens).circuitOperations.interactionValuesWith (check.channel ens)
      (Environment.fromInput input data)) ↔ check.CountBound ∧ check.Checks input data := by
  change BalancedInteractions ((Verifier.checkZeros (check.channelName ens)
    (check.assertions (varFromOffset PublicIO 0))).circuitOperations.interactionValuesWith
      (Verifier.zeroChannel (check.channelName ens)).toRaw (Environment.fromInput input data)) ↔ _
  rw [Verifier.checkZeros_balanced_iff]
  simp [CountBound, Checks, assertions, Operations.ConstraintsHold, check.lookups]

/-- Append checks using the existing verifier monad and retain the physical inventory. -/
def install (ens : Ensemble F PublicIO) : Ensemble F PublicIO where
  tables := ens.tables
  unique_names := ens.unique_names
  channels := ens.channels ++ [check.channel ens]
  verifier := ens.verifier.andThen (check.program ens)

private theorem fresh (ens : Ensemble F PublicIO) : VerifierChannel.Fresh check.name ens :=
  VerifierChannel.fresh check.name ens

/-- Automatic installation never reuses a registered channel. -/
theorem channel_not_mem (ens : Ensemble F PublicIO) : check.channel ens ∉ ens.channels :=
  (check.fresh ens).unregistered

/-- Forget the additional public check, preserving the literal committed table list. -/
def project {ens : Ensemble F PublicIO} (witness : EnsembleWitness (check.install ens)) :
    EnsembleWitness ens :=
  EnsembleWitness.ofTables ens witness.tables witness.publicInput witness.tables_map_component

/-- Projection preserves public input. -/
@[simp] theorem project_publicInput {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness (check.install ens)) :
    (check.project witness).publicInput = witness.publicInput := rfl

/-- Projection preserves canonical committed data because it preserves the physical rows. -/
@[simp] theorem project_data {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness (check.install ens)) :
    (check.project witness).data = witness.data := rfl

/-- Projection preserves every physical table and row. -/
@[simp] theorem project_tables {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness (check.install ens)) :
    (check.project witness).tables = witness.tables := rfl

/-- Use the same committed rows as a candidate for the strengthened verifier. -/
def lift {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) :
    EnsembleWitness (check.install ens) :=
  EnsembleWitness.ofTables (check.install ens) witness.tables witness.publicInput
    witness.tables_map_component

/-- Physical constraints are identical; the public checks are enforced through balance. -/
theorem project_constraints {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness (check.install ens)) :
    witness.Constraints ↔ (check.project witness).Constraints := Iff.rfl

/-- Installing public assertions preserves the verifier's complete ledger on every other channel. -/
theorem install_verifier_interactions (ens : Ensemble F PublicIO) (env : Environment F)
    (selected : RawChannel F) (different : check.channel ens ≠ selected) :
    (check.install ens).verifierOperations.interactionValuesWith selected env =
      ens.verifierOperations.interactionValuesWith selected env := by
  change (ens.verifier.andThen (check.program ens)).circuitOperations.interactionValuesWith selected env = _
  rw [Verifier.Program.andThen_values]
  change _ ++ (Verifier.checkZeros (check.channelName ens)
    (check.assertions (varFromOffset PublicIO 0))).circuitOperations.interactionValuesWith selected env = _
  rw [Verifier.checkZeros_other_values _ _ _ _ different, List.append_nil]

/-- Public assertions leave every previously registered verifier channel unchanged. -/
theorem install_verifier_interactions_of_mem (ens : Ensemble F PublicIO) (env : Environment F)
    (selected : RawChannel F) (registered : selected ∈ ens.channels) :
    (check.install ens).verifierOperations.interactionValuesWith selected env =
      ens.verifierOperations.interactionValuesWith selected env := by
  apply check.install_verifier_interactions
  intro same
  exact check.channel_not_mem ens (same ▸ registered)

/-- Projection preserves the literal ledger of every other channel. -/
theorem project_interactions {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness (check.install ens)) (selected : RawChannel F)
    (different : check.channel ens ≠ selected) :
    (check.project witness).interactionsWith selected = witness.interactionsWith selected := by
  change _ = (check.install ens).verifierOperations.interactionValuesWith
    selected (Environment.fromInput witness.publicInput witness.data) ++ _
  rw [check.install_verifier_interactions ens _ selected different]
  rfl

/-- On the fresh channel, the installed ledger is exactly the public check program. -/
theorem installed_check_interactions {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness (check.install ens)) :
    witness.interactionsWith (check.channel ens) =
      (check.program ens).circuitOperations.interactionValuesWith (check.channel ens)
        (Environment.fromInput witness.publicInput witness.data) := by
  have fresh := check.fresh ens
  have original := VerifierChannel.Fresh.empty_ledger check.name fresh (check.project witness)
  have physical : witness.tableContext.interactionsWith (check.channel ens) = [] := by
    simpa only [EnsembleWitness.interactionsWith, EnsembleWitness.verifierInteractionsWith,
      fresh.verifier, List.nil_append, EnsembleWitness.tableContext,
      TableContext.interactionsWith, project_tables, project_data] using original
  change (ens.verifier.andThen (check.program ens)).circuitOperations.interactionValuesWith (check.channel ens)
    (Environment.fromInput witness.publicInput witness.data) ++
      witness.tableContext.interactionsWith (check.channel ens) = _
  rw [Verifier.Program.andThen_values, fresh.verifier, List.nil_append, physical, List.append_nil]

/-- Installation preserves old balance and enforces the new assertions with their exact count bound. -/
theorem project_balanced_iff {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness (check.install ens)) :
    witness.BalancedChannels ↔
      (check.project witness).BalancedChannels ∧ check.CountBound ∧
        check.Checks witness.publicInput witness.data := by
  have fresh := check.fresh ens
  constructor
  · intro balanced
    have own := balanced (check.channel ens) (by simp [install])
    rw [EnsembleWitness.BalancedChannel, check.installed_check_interactions] at own
    refine ⟨?_, (check.program_balanced_iff ens _ _).mp own⟩
    intro selected member
    have different : check.channel ens ≠ selected := by
      intro equal
      exact fresh.unregistered (show check.channel ens ∈ ens.channels from equal ▸ member)
    change BalancedInteractions ((check.project witness).interactionsWith selected)
    rw [check.project_interactions witness selected different]
    exact balanced selected (List.mem_append_left _ member)
  · rintro ⟨original, bound, checked⟩ selected member
    change selected ∈ ens.channels ++ [check.channel ens] at member
    rcases List.mem_append.mp member with member | member
    · have different : check.channel ens ≠ selected := by
        intro equal
        exact fresh.unregistered (show check.channel ens ∈ ens.channels from equal ▸ member)
      change BalancedInteractions (witness.interactionsWith selected)
      rw [← check.project_interactions witness selected different]
      exact original selected member
    · have same : selected = check.channel ens := List.mem_singleton.mp member
      subst selected
      change BalancedInteractions (witness.interactionsWith (check.channel ens))
      rw [check.installed_check_interactions]
      exact (check.program_balanced_iff ens _ _).mpr ⟨bound, checked⟩

/-- The installed statement adds exactly the public semantic contract to the original statement. -/
theorem statement_iff (ens : Ensemble F PublicIO)
    (bound : check.CountBound) (meaning : PublicIO F → Prop)
    (checks : ∀ input data, check.Checks input data ↔ meaning input) (input : PublicIO F) :
    (check.install ens).Statement input ↔ ens.Statement input ∧ meaning input := by
  constructor
  · rintro ⟨witness, same, constraints, balanced⟩
    obtain ⟨original, _, checked⟩ := (check.project_balanced_iff witness).mp balanced
    refine ⟨⟨check.project witness, same,
      (check.project_constraints witness).mp constraints, original⟩, ?_⟩
    rw [← same]
    exact (checks ..).mp checked
  · rintro ⟨⟨witness, same, constraints, balanced⟩, spec⟩
    refine ⟨check.lift witness, same, constraints, ?_⟩
    apply (check.project_balanced_iff (check.lift witness)).mpr
    exact ⟨balanced, bound, (checks ..).mpr (same ▸ spec)⟩

end PublicVerifier
end Air.Flat
