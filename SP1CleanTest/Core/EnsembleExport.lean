import Clean.Air.Extraction.Rust
import SP1CleanTest.Core.EnsembleCheck

/-! # Built-in Rust export of fixed membership and a public boundary

The legacy lookup fixture's allowed values become verifier-fixed columns. Clean owns lowering,
Rust rendering and witness scheduling. The finite checker independently checks the generated
physical rows and the separate public verifier; generation is not a completeness theorem.
-/

namespace SP1CleanTest.Core.EnsembleExport

open Air.Flat Circuit
open EnsembleCheck (Fp values verifier)

/-- A fixed allowed value, its request count and a constrained generated square. -/
def provider : GeneralFormalCircuit Fp fieldPair field where
  name := "allowed"
  main input := do
    let square ← witness (.expr (input.1 * input.1) : Witgen.FExpr Fp)
    assertZero (square - input.1 * input.1)
    values.emit input.2 input.1
    return square
  Spec input output _ := output = input.1 * input.1
  channelsWithRequirements := [values.toRaw]
  soundness := by
    circuit_proof_start [EnsembleCheck.values]
    rw [← h_input]
    exact sub_eq_zero.mp h_holds
  completeness := by
    circuit_proof_start [EnsembleCheck.values]
    simp_all

/-- The original finite lookup meaning is supplied by the verifier, independently of prover data. -/
def fixed : FixedColumns Fp where
  height := 2
  program := .ofFExprs #v[.listGetAtIndex [.const 7, .const 9]]
  valid := by rfl

/-- The multiplicity is prover-owned; the allowed value is the fixed prefix. -/
def component : Component Fp where
  circuit := provider
  fixedColumns := some fixed
  fixed_width_le_input := by decide

/-- One physical provider with the original separate public pull. -/
def ensemble : Ensemble Fp field where
  tables := [component]
  unique_names := by simp
  channels := [values.toRaw]
  verifier := verifier

/-- Built-in preallocation updates only the count, selected by the actual emitted message. -/
def config : WitnessGeneration.Config Fp unit where
  modes := [.preallocated {
    rows := 2
    input := .ofFExprs #v[.const 0]
    input_valid := by rfl
    handlers := [{ interaction := 0, column := 1 }]
  }]
  padding := [{ input := #[7, 0], minimumRows := 2 }]
  fuel := 8

/-- Independent raw acceptance includes all occurrences, including the unused fixed row. -/
def description : Air.Flat.EnsembleCheck ensemble where
  lookups := []
  lookups_unique := by simp
  lookups_complete := by
    simp [ensemble, component, Component.lookups_eq, Component.rowOperations, provider, circuit_norm]
  channels_unique := by simp [ensemble]
  channels_complete := by
    simp [ensemble, component, Component.interactions_eq, Component.rowOperations, provider, circuit_norm]
  verifier_channels_complete := by
    simp [ensemble, Ensemble.verifierOperations, EnsembleCheck.verifier,
      Verifier.Program.circuitOperations, circuit_norm]

/-- Use Clean's scheduler with no external prover input or custom witness evaluator. -/
def generate (value : Fp) : Except String (EnsembleWitness ensemble) :=
  WitnessGeneration.generate ensemble config value ()

/-- The entire output is rendered by Clean's built-in exporter. -/
def rust : Except String String :=
  Extraction.Rust.ensembleToRust "FixedMembership" ensemble config

/-- Check generation against raw constraints and the full ledger. -/
def accepts (value : Fp) : Bool :=
  match generate value with
  | .ok witness => description.checkWitness SP1Clean.SP1Prime witness
  | .error _ => false

/-- Both original allowed values pass, while the forged member has no fixed provider. -/
theorem membership_cases : [accepts 7, accepts 9, accepts 8] = [true, true, false] := by
  native_decide

/-- Lowering and Rust rendering both succeed on the fixed-column representation. -/
theorem export_succeeds : rust.isOk = true := by native_decide

end SP1CleanTest.Core.EnsembleExport
