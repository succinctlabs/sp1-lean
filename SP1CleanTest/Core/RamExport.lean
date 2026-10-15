import SP1CleanTest.Core.ComponentExport
import SP1Clean.Proofs.Chips.SnapshotRamProvider
import SP1Clean.Native.Operations.FinalRamValue
import ToClean.Air.EnsembleCheck
import ToClean.Air.TableBuild

/-! # Built-in Rust export of RAM rows and fixed interval membership

Clean owns witness execution, fixed rows, scheduling and lowering. The closed membership fixture
checks the production interval provider. Component fixtures retain their external Byte and Memory
interactions; Rust checks those separately. They do not establish full-ensemble generation.
-/

namespace SP1CleanTest.Core.RamExport

open Air.Flat Circuit SP1Clean SP1Clean.Model.Core

abbrev Fp := ZMod SP1Prime
abbrev Requests := ProvableVector MemoryIntervalRow 2

/-- Unsorted entries include first-write precedence, a sparse gap and the final native byte. -/
def memory : ByteMemory :=
  ⟨[(131072, 18), (65536, 17), (65536, 99), (65543, 171),
    (131071, 254), (2 ^ 48 - 1, 255)]⟩

def snapshot : MemorySnapshot := ⟨Vector.replicate 32 0, memory⟩

def table (name : String) : StaticTable Fp MemoryIntervalRow :=
  InitialMemoryLookup.membership memory (2 ^ 48) name

def verifier (name : String) : Verifier.Program Fp Requests where
  main requests := do
    Verifier.pull (table name).channel ⟨requests[0], 1⟩
    Verifier.pull (table name).channel ⟨requests[1], 1⟩

def ensemble (name : String) : Ensemble Fp Requests where
  tables := [(table name).component]
  unique_names := by simp
  channels := [(table name).channel.toRaw]
  verifier := verifier name

def config (name : String) : WitnessGeneration.Config Fp unit where
  modes := [.preallocated {
    rows := (table name).height
    input := .ofFExprs #v[.const 0]
    input_valid := by rfl
    handlers := [{ interaction := 0, column := 10 }]
  }]
  padding := [{ input := Array.replicate 11 0, minimumRows := (table name).height }]
  fuel := 8

def description (name : String) : Air.Flat.EnsembleCheck (ensemble name) where
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

def generate (name : String) (requests : Requests Fp) :
    Except String (EnsembleWitness (ensemble name)) :=
  WitnessGeneration.generate (ensemble name) (config name) requests ()

/-- The complete normalized interval inventory, then a repeated request and independent forgeries. -/
def cases : List (String × Requests Fp × Bool) :=
  let rows := (memory.intervals (2 ^ 48)).map (MemoryInterval.encode (p := SP1Prime))
  let first : MemoryIntervalRow Fp := (⟨65536, 65537, 17⟩ : MemoryInterval).encode
  rows.zipIdx |>.map (fun (row, index) => (s!"interval-{index}", #v[row, first], true)) |>.append
    [("repeated", #v[first, first], true),
     ("forged-byte", #v[(⟨65536, 65537, 99⟩ : MemoryInterval).encode, first], false),
     ("forged-lower", #v[(⟨65535, 65537, 17⟩ : MemoryInterval).encode, first], false),
     ("forged-upper", #v[(⟨65536, 65538, 17⟩ : MemoryInterval).encode, first], false)]

def exportRow {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (name : String) (circuit : GeneralFormalCircuit Fp Input Output) : Except String String :=
  let component := ComponentExport.ensemble { circuit }
  let registered := { component with channels := component.channels ++
    [(table "sp1.native.initial_memory").channel.toRaw,
     (table "sp1.native.target_memory").channel.toRaw, (FinalMemoryValue.channel true).toRaw] }
  Extraction.Rust.ensembleToRust name registered (ComponentExport.config Input)

def rustExports : List (String × Except String String) :=
  [("ram_byte.rs", exportRow "RamByte" (InitialMemoryLookup.circuit memory (2 ^ 48) (by norm_num))),
   ("ram_word.rs", exportRow "RamWord" (InitialMemoryRead.circuit memory)),
   ("ram_source.rs", exportRow "RamSource" (SnapshotRamProvider.circuit snapshot)),
   ("ram_target.rs", exportRow "RamTarget" (FinalRamValue.circuit snapshot)),
   ("ram_source_membership.rs", Extraction.Rust.ensembleToRust "RamSourceMembership"
     (ensemble "sp1.native.initial_memory") (config "sp1.native.initial_memory")),
   ("ram_target_membership.rs", Extraction.Rust.ensembleToRust "RamTargetMembership"
     (ensemble "sp1.native.target_memory") (config "sp1.native.target_memory"))]

/-- Public test inputs cover carries, sparse gaps, native bounds and malformed field limbs. -/
def rowCases : List (String × Component Fp × List (List Fp)) :=
  let addresses := [0, 31, 32, 65529, 65536, 65537, 65543, 131064, 131065, 131072,
    2 ^ 48 - 8, 2 ^ 48 - 7, 2 ^ 48 - 1, 2 ^ 48]
  let words := addresses.map fun address =>
    (Soundness.Target.bitVecToWord (p := SP1Prime) (BitVec.ofNat 64 address)).toList
  let inputs := words ++ [[65536, 0, 0, 0]]
  let records := addresses.map fun address =>
    let addr := Soundness.Target.bitVecToWord (p := SP1Prime) (BitVec.ofNat 64 address)
    let value := Soundness.Target.bitVecToWord (p := SP1Prime) (memory.readWord address)
    [(3 : Fp), 17, addr[0], addr[1], addr[2]] ++ value.toList
  [("byte", { circuit := InitialMemoryLookup.circuit memory (2 ^ 48) (by norm_num) }, inputs),
   ("word", { circuit := InitialMemoryRead.circuit memory }, inputs),
   ("source", { circuit := SnapshotRamProvider.circuit snapshot }, inputs),
   ("target", { circuit := FinalRamValue.circuit snapshot },
     records ++ [[3, 17, 0, 1, 0, 99, 0, 0, 0], [3, 17, 65536, 0, 0, 17, 0, 0, 0]])]

theorem cases_correct :
    ["sp1.native.initial_memory", "sp1.native.target_memory"].all (fun name =>
      cases.all fun (_, requests, expected) =>
        (match generate name requests with
        | .ok witness => (description name).checkWitness SP1Prime witness
        | .error _ => false) == expected) = true := by native_decide

theorem exports_succeed : rustExports.all (fun entry => entry.2.isOk) = true := by native_decide

end SP1CleanTest.Core.RamExport
