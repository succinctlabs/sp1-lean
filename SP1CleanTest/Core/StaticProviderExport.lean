import Clean.Air.Extraction.Rust
import SP1Clean.Model.SP1Field
import ToClean.Air.StaticProvider
import ToClean.Air.EnsembleCheck
import ToClean.Circuit.StaticTable

/-! # Built-in export of empty, padded and duplicate membership tables

Use the production ToClean provider and Clean's scheduler directly. Independent raw checks retain
every original row and every inactive occurrence. Rust supplies separate fixed-row expectations
and backend mutations; these fixtures do not assert scheduler completeness or a lowering proof.
-/

namespace SP1CleanTest.Core.StaticProviderExport

open Air.Flat Circuit

abbrev Fp := ZMod SP1Clean.SP1Prime
abbrev Requests := ProvableVector field 2

def table (rows : List Fp) : StaticTable Fp field :=
  StaticTable.ofRows "fixture.membership" rows

def verifier (rows : List Fp) : Verifier.Program Fp Requests where
  main requests := do
    Verifier.pull (table rows).channel ⟨requests[0], 1⟩
    Verifier.pull (table rows).channel ⟨requests[1], 1⟩

def ensemble (rows : List Fp) : Ensemble Fp Requests where
  tables := [(table rows).component]
  unique_names := by simp
  channels := [(table rows).channel.toRaw]
  verifier := verifier rows

def emptyEnsemble (rows : List Fp) : Ensemble Fp unit where
  tables := [(table rows).component]
  unique_names := by simp
  channels := [(table rows).channel.toRaw]

def config (rows : List Fp) : WitnessGeneration.Config Fp unit where
  modes := [.preallocated {
    rows := (table rows).height
    input := .ofFExprs #v[.const 0]
    input_valid := by rfl
    handlers := [{ interaction := 0, column := 2 }]
  }]
  padding := [{ input := #[0, 0, 0], minimumRows := (table rows).height }]
  fuel := 8

def description (rows : List Fp) : Air.Flat.EnsembleCheck (ensemble rows) where
  lookups := []
  lookups_unique := by simp
  lookups_complete := by
    simp [ensemble, Component.lookups_eq, Component.rowOperations,
      StaticTable.component, StaticTable.provider, circuit_norm]
  channels_unique := by simp [ensemble]
  channels_complete := by
    simp [ensemble, Component.interactions_eq, Component.rowOperations,
      StaticTable.component, StaticTable.provider, circuit_norm]
  verifier_channels_complete := by
    simp [ensemble, Ensemble.verifierOperations, verifier,
      Verifier.Program.circuitOperations, circuit_norm]

def emptyDescription (rows : List Fp) : Air.Flat.EnsembleCheck (emptyEnsemble rows) where
  lookups := []
  lookups_unique := by simp
  lookups_complete := by
    simp [emptyEnsemble, Component.lookups_eq, Component.rowOperations,
      StaticTable.component, StaticTable.provider, circuit_norm]
  channels_unique := by simp [emptyEnsemble]
  channels_complete := by
    simp [emptyEnsemble, Component.interactions_eq, Component.rowOperations,
      StaticTable.component, StaticTable.provider, circuit_norm]
  verifier_channels_complete := by
    simp [emptyEnsemble, Ensemble.verifierOperations, Verifier.Program.circuitOperations,
      Verifier.Program.empty, circuit_norm]

def generate (rows : List Fp) (requests : Requests Fp) :
    Except String (EnsembleWitness (ensemble rows)) :=
  WitnessGeneration.generate (ensemble rows) (config rows) requests ()

def generateEmpty (rows : List Fp) : Except String (EnsembleWitness (emptyEnsemble rows)) :=
  WitnessGeneration.generate (emptyEnsemble rows) (config rows) () ()

/-- Include a real zero payload beside zero padding and repeated first/non-first payloads. -/
def fixtures : List (String × List Fp) :=
  [("empty", []), ("singleton", [0]), ("uneven", [7, 0, 9]),
    ("duplicates", [0, 7, 0, 7, 9]), ("zeroes", [0, 0, 0, 0, 0])]

def requests : List (Requests Fp) :=
  ([0, 7, 9, 11] : List Fp).flatMap fun a =>
    ([0, 7, 9, 11] : List Fp).map fun b => #v[a, b]

def rustExports : List (String × Except String String) := fixtures.flatMap fun (name, rows) =>
  [(s!"static_{name}.rs", Extraction.Rust.ensembleToRust "StaticMembership" (ensemble rows) (config rows)),
   (s!"static_{name}_unused.rs", Extraction.Rust.ensembleToRust "UnusedMembership" (emptyEnsemble rows) (config rows))]

theorem cases_correct : fixtures.all (fun (_, rows) => requests.all fun request =>
    (match generate rows request with
    | .ok witness => (description rows).checkWitness SP1Clean.SP1Prime witness
    | .error _ => false) == (rows.contains request[0] && rows.contains request[1])) = true := by
  native_decide

theorem unused_correct : fixtures.all (fun (_, rows) =>
    (generateEmpty rows).map (fun witness =>
      (emptyDescription rows).checkWitness SP1Clean.SP1Prime witness &&
        witness.interactions.length == (table rows).height &&
        witness.interactions.all (·.mult == 0)) == .ok true) = true := by native_decide

theorem exports_succeed : rustExports.all (fun entry => entry.2.isOk) = true := by native_decide

end SP1CleanTest.Core.StaticProviderExport
