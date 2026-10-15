import ToClean.Air.EnsembleCheck
import ToClean.Air.TableBuild
import SP1Clean.Model.SP1Field
import ToClean.Air.PublicVerifier
import Clean.Utils.Tactics

/-! # Regression checks for finite ensemble acceptance

The same physical witness is checked against the raw statement theorem. Mutations separate
fixed membership, public boundary balance, and occurrence counts; disabled interactions still
consume capacity. These computations use the test library's existing compiler trust boundary.
-/

namespace SP1CleanTest.Core.EnsembleCheck

open Air.Flat Circuit
abbrev Fp := ZMod SP1Clean.SP1Prime

def values : Channel Fp field where
  name := "values"
  Guarantees _ _ := True

def allowed : StaticTable Fp field where
  name := "allowed"
  length := 2
  row index := if index.val = 0 then 7 else 9
  index value := if value = 7 then 0 else 1
  Spec value := value = 7 ∨ value = 9
  contains_iff := by
    intro value
    constructor
    · rintro ⟨index, rfl⟩
      split <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩

def provider : GeneralFormalCircuit Fp field unit where
  main value := do
    lookup allowed.toTable value
    values.push value
  Spec value _ _ := value = 7 ∨ value = 9
  ProverAssumptions value _ _ := value = 7 ∨ value = 9
  channelsWithRequirements := [values.toRaw]
  soundness := by
    circuit_proof_start [allowed, values]
    simp_all
  completeness := by
    circuit_proof_start [allowed, values]
    simp_all

def verifier : Verifier.Program Fp field where
  main value := Verifier.pull values value
  Spec _ _ := True
  soundness := by intro _ _; trivial

def ensemble : Ensemble Fp field where
  tables := [{ circuit := provider }]
  unique_names := by simp
  channels := [values.toRaw]
  verifier := verifier

/-- Finite meanings for the physical lookup and both sides of the public channel. -/
def description : Air.Flat.EnsembleCheck ensemble where
  lookups := [FiniteLookup.ofStatic allowed]
  lookups_unique := by simp
  lookups_complete := by
    simp [ensemble, Component.lookups_eq, Component.rowOperations, provider, circuit_norm]
    rfl
  channels_unique := by simp [ensemble]
  channels_complete := by
    simp [ensemble, Component.interactions_eq, Component.rowOperations, provider, circuit_norm]
  verifier_channels_complete := by
    simp [ensemble, Ensemble.verifierOperations, verifier, Verifier.Program.circuitOperations,
      circuit_norm]

/-- Static lookups need no prover-supplied data. -/
def data : ProverData Fp := fun _ _ => #[]

/-- Physical provider rows with the exact public input retained in the verifier. -/
def witness (publicInput : Fp) (rows : List Fp) : EnsembleWitness ensemble :=
  EnsembleWitness.ofTables ensemble
    [Table.build { circuit := provider } rows data (ProverHint.empty Fp)] publicInput rfl

/-- Both allowed values accept; malformed membership and boundary inventories reject. -/
def outcomes : List (String × Bool × Bool) :=
  [("allowed-seven", true, description.checkWitness SP1Clean.SP1Prime (witness 7 [7])),
   ("allowed-nine", true, description.checkWitness SP1Clean.SP1Prime (witness 9 [9])),
   ("forbidden-eight", false, description.checkWitness SP1Clean.SP1Prime (witness 8 [8])),
   ("missing-provider", false, description.checkWitness SP1Clean.SP1Prime (witness 7 [])),
   ("duplicate-provider", false, description.checkWitness SP1Clean.SP1Prime (witness 7 [7, 7])),
   ("wrong-public-input", false, description.checkWitness SP1Clean.SP1Prime (witness 9 [7]))]

/-- Every named outcome comes from checking the physical witness. -/
theorem outcomes_correct : outcomes.all (fun outcome => outcome.2.1 == outcome.2.2) = true := by
  native_decide

/-- The computed positive case proves the actual raw Clean statement. -/
theorem accepted_statement : ensemble.Statement 7 :=
  description.statement_of_checkWitness SP1Clean.SP1Prime (witness 7 [7]) (by native_decide)

instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- A field-small channel used only to expose the strict occurrence limit. -/
def tinyChannel : Channel (ZMod 3) field where
  name := "tiny"
  Guarantees _ _ := True

/-- Disabled interactions still occupy a position in the physical ledger. -/
def disabled : Interaction (ZMod 3) :=
  ⟨tinyChannel.toRaw, 0, #[0], rfl, false⟩

/-- Disabled occurrences below the characteristic are admissible. -/
theorem below_capacity : checkInteractionBalance 3 [disabled, disabled] = true := by native_decide

/-- Multiplicity zero does not bypass the strict characteristic limit. -/
theorem at_capacity : checkInteractionBalance 3 [disabled, disabled, disabled] = false := by native_decide

/-- The failed capacity check implies failure of the original raw predicate. -/
theorem disabled_capacity_is_raw : ¬ BalancedInteractions [disabled, disabled, disabled] := by
  rw [← checkInteractionBalance_iff 3]
  exact Bool.false_ne_true ∘ (at_capacity.symm.trans ·)

/-- The public assertion keeps its original semantic proof boundary. -/
def assertedVerifier : GeneralFormalCircuit Fp field unit where
  main value := assertZero (value - 7)
  Spec value _ _ := value = 7
  ProverAssumptions value _ _ := value = 7
  soundness := by
    circuit_proof_start
    exact sub_eq_zero.mp h_holds
  completeness := by
    circuit_proof_start
    simp_all

/-- The existing semantic assertion is installed through ordinary verifier interactions. -/
def publicCheck : PublicVerifier Fp field where
  name := "boundary"
  circuit := assertedVerifier
  assumptions := by intros; trivial
  length_zero := by intro value; rfl
  lookups := by intros; rfl
  interactions := by intros; rfl

/-- Public checks need no physical prover table. -/
def boundaryEnsemble : Ensemble Fp field := publicCheck.install (.empty Fp field)

/-- The generated check channel is the only channel in this table-free ensemble. -/
def boundaryDescription : Air.Flat.EnsembleCheck boundaryEnsemble where
  lookups := []
  lookups_unique := by simp
  lookups_complete := by simp [boundaryEnsemble, PublicVerifier.install, Ensemble.empty]
  channels_unique := by simp [boundaryEnsemble, PublicVerifier.install, Ensemble.empty]
  channels_complete := by simp [boundaryEnsemble, PublicVerifier.install, Ensemble.empty]
  verifier_channels_complete := by
    simp [boundaryEnsemble, PublicVerifier.install, Ensemble.verifierOperations,
      PublicVerifier.program, PublicVerifier.assertions, publicCheck, assertedVerifier,
      Ensemble.empty, Verifier.Program.circuitOperations, Verifier.Program.andThen,
      Verifier.Program.empty, Verifier.checkZeros, Verifier.checkZero, circuit_norm]
    rfl

/-- Public input is retained even with no prover tables. -/
def boundaryWitness (value : Fp) : EnsembleWitness boundaryEnsemble :=
  EnsembleWitness.ofTables boundaryEnsemble [] value rfl

/-- The satisfying public assertion accepts. -/
theorem verifier_accepts :
    boundaryDescription.checkWitness SP1Clean.SP1Prime (boundaryWitness 7) = true := by native_decide

/-- An invalid public assertion rejects independently of any row or balance checks. -/
theorem verifier_rejects :
    boundaryDescription.checkWitness SP1Clean.SP1Prime (boundaryWitness 9) = false := by native_decide

end SP1CleanTest.Core.EnsembleCheck
