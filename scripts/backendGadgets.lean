import SP1Clean.Circuits.Gadgets.IsZero
import SP1Clean.Circuits.Gadgets.IsZeroWord
import SP1Clean.Native.Operations.WordRangeCheck
import Clean.Backends.Circom.Compile
import Clean.Backends.Circom.R1CS
import CompPoly.Fields.BN254.Basic
import Lean.Data.Json

/-! # Native standalone backend conformance exporter

The two zero adapters witness the existing populate IR and invoke the public assertion with
gate one. Range checking invokes its public circuit unchanged. These are export harnesses,
not new operation faithfulness anchors or a proof of the backend. All constraints are retained.
-/

namespace BackendGadgets

open Circuit SP1Clean Backends.Circom Lean

abbrev prime := BN254.scalarFieldSize
abbrev F := ZMod prime

instance : Fact prime.Prime := ⟨BN254.ScalarField_is_prime⟩
instance : Fact (2 ^ 17 < prime) := ⟨by decide⟩

def zeroProgram : Circuit F Unit := do
  let a : Expression F := .var ⟨0⟩
  let cols : Var Circuits.Types.IsZeroOperation F ← witness (IsZeroOperation.populateFE (.expr a))
  assertion IsZeroOperation.circuit ⟨a, cols, 1⟩

def wordZeroProgram : Circuit F Unit := do
  let a : Var Word F := varFromOffset Word 0
  let cols : Var Circuits.Types.IsZeroWordOperation F ← witness (IsZeroWordOperation.populateFE (a.map Witgen.FExpr.expr))
  assertion IsZeroWordOperation.circuit ⟨a, cols, 1⟩

def rangeProgram : Circuit F Unit :=
  assertion WordRangeCheck.circuit (varFromOffset Word 0)

structure Sample where
  name : String
  inputs : List Nat
  accepted : Bool := true

structure Mutation where
  name : String
  cell : Nat
  value : Nat
  accepted : Bool

structure Gadget where
  name : String
  program : Circuit F Unit
  inputNames : List String
  cellNames : List String
  outputs : List Nat
  samples : List Sample
  mutations : Sample → List Mutation

def scalarSamples : List Sample :=
  [⟨"zero", [0], true⟩, ⟨"one", [1], true⟩, ⟨"two", [2], true⟩,
   ⟨"field-minus-one", [prime - 1], true⟩, ⟨"field-minus-two", [prime - 2], true⟩,
   ⟨"above-u64", [2 ^ 64], true⟩, ⟨"above-u128", [2 ^ 128], true⟩]

def wordSamples : List Sample :=
  [⟨"zero", [0, 0, 0, 0], true⟩, ⟨"all-field-max", List.replicate 4 (prime - 1), true⟩] ++
  (List.range 4).flatMap fun i =>
    [⟨s!"limb-{i}-one", (List.replicate 4 0).set i 1, true⟩,
     ⟨s!"limb-{i}-field-max", (List.replicate 4 0).set i (prime - 1), true⟩]

def rangeSamples : List Sample :=
  [⟨"zero", [0, 0, 0, 0], true⟩, ⟨"max-u16", List.replicate 4 65535, true⟩,
   ⟨"mixed", [1, 256, 32768, 65535], true⟩,
   ⟨"above-u64", [2 ^ 64, 0, 0, 0], false⟩] ++
  (List.range 4).flatMap fun i =>
    [⟨s!"limb-{i}-overflow", (List.replicate 4 0).set i 65536, false⟩,
     ⟨s!"limb-{i}-field-max", (List.replicate 4 0).set i (prime - 1), false⟩]

def gadgets : List Gadget := [
  { name := "is-zero", program := zeroProgram, inputNames := ["a"],
    cellNames := ["a", "inverse", "result"], outputs := [2], samples := scalarSamples,
    mutations := fun sample =>
      if sample.name == "zero" then
        [⟨"zero-inverse-is-free", 1, 7, true⟩, ⟨"corrupt-zero-result", 2, 0, false⟩]
      else if sample.name == "one" then
        [⟨"corrupt-nonzero-inverse", 1, 0, false⟩, ⟨"corrupt-nonzero-result", 2, 1, false⟩]
      else [] },
  { name := "is-zero-word", program := wordZeroProgram,
    inputNames := (List.range 4).map (fun i => s!"limb{i}"),
    cellNames := ((List.range 4).map (fun i => s!"limb{i}")) ++
      ((List.range 4).flatMap (fun i => [s!"limb{i}.inverse", s!"limb{i}.result"])) ++
      ["first_half", "second_half", "result"], outputs := [14], samples := wordSamples,
    mutations := fun sample =>
      if sample.name == "zero" then
        ((List.range 4).map (fun i => ⟨s!"zero-limb-{i}-inverse-is-free", 4 + 2 * i, 7, true⟩)) ++
        [⟨"corrupt-word-result", 14, 0, false⟩, ⟨"corrupt-limb-result", 5, 0, false⟩,
         ⟨"corrupt-half-result", 12, 0, false⟩]
      else if sample.name == "all-field-max" then
        (List.range 4).map fun i => ⟨s!"corrupt-limb-{i}-nonzero-inverse", 4 + 2 * i, 0, false⟩
      else [] },
  { name := "word-range-check", program := rangeProgram,
    inputNames := (List.range 4).map (fun i => s!"limb{i}"),
    cellNames := ((List.range 4).map (fun i => s!"limb{i}")) ++
      ((List.range 4).flatMap (fun i => (List.range 16).map fun j => s!"limb{i}.bit{j}")),
    outputs := [], samples := rangeSamples,
    mutations := fun sample =>
      if sample.name == "zero" then
        (List.range 4).flatMap fun i =>
          [⟨s!"nonboolean-limb-{i}-bit", 4 + 16 * i, 2, false⟩,
           ⟨s!"wrong-limb-{i}-bit", 4 + 16 * i, 1, false⟩]
      else [] }]

/-- Eligibility is checked on every flattened operation, before either artifact is written. -/
def eligible (numInputs : Nat) (ops : List (Operation F)) : Except String Unit := do
  for op in Operations.toFlat ops do
    match op with
    | .lookup _ => throw "standalone R1CS rejects lookup"
    | .interact _ => throw "standalone R1CS rejects interaction"
    | .witness _ (.native _) => throw "standalone R1CS rejects native witness"
    | _ => pure ()
  let _ ← processFlatOps (Operations.toFlat ops) (VarMap.init numInputs 4 prime) numInputs {}

def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def liftResult {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

def jsonNat (value : Nat) : Json := toJson (toString value)

def assertionsHold (flat : List (FlatOperation F)) (cells : List F) : Bool :=
  let env := Environment.fromArray cells.toArray (fun _ _ => #[])
  flat.all fun op => match op with
    | .assert expression => env expression == 0
    | .witness .. => true
    | .lookup .. | .interact .. => false

def writeJson (path : System.FilePath) (value : Json) : IO Unit :=
  IO.FS.writeFile path (value.pretty ++ "\n")

def exportGadget (directory : System.FilePath) (gadget : Gadget) : IO Json := do
  let inputs := gadget.inputNames.length
  let ops := gadget.program.operations inputs
  let flat := ops.toFlat
  let count := inputs + FlatOperation.localLength flat
  require (count == gadget.cellNames.length) s!"{gadget.name}: changed original-cell layout"
  liftResult (eligible inputs ops)
  let wasm ← liftResult (compileModule prime inputs gadget.inputNames gadget.outputs ops 4)
  let r1cs ← liftResult (compileR1CSBin prime inputs gadget.inputNames gadget.outputs ops 4)
  let r1csText ← liftResult (compileR1CS prime inputs gadget.inputNames gadget.outputs ops 4)
  let r1csJson ← liftResult (Json.parse r1csText)
  let vm := { (VarMap.init inputs 4 prime) with
    numOutputs := gadget.outputs.length, outputVars := gadget.outputs }
  let cellMap := (List.range count).map fun cell => Json.mkObj [
    ("cell", toJson cell), ("name", toJson (gadget.cellNames[cell]?.getD "")),
    ("signal", toJson (signalOfVar vm cell))]
  let path := directory / gadget.name
  IO.FS.createDirAll (path / "inputs")
  IO.FS.writeBinFile (path / "circuit.wasm") wasm
  IO.FS.writeBinFile (path / "circuit.r1cs") r1cs
  IO.FS.writeFile (path / "circuit.r1cs.json") (r1csText ++ "\n")
  writeJson (path / "layout.json") (Json.mkObj [
    ("constantSignal", toJson (0 : Nat)), ("originalCells", toJson cellMap),
    ("outputCells", toJson gadget.outputs), ("inputNames", toJson gadget.inputNames),
    ("auxiliarySignalsStart", toJson (count + 1))])
  let mut cases : List Json := []
  for sample in gadget.samples do
    require (sample.inputs.length == inputs && sample.inputs.all (· < prime))
      s!"{gadget.name}/{sample.name}: noncanonical or mis-sized input"
    let env := (gadget.program.proverEnvironment (ProverHint.empty F)
      (sample.inputs.map (fun n => (n : F)))).toEnvironment
    let cells := (List.range count).map env.get
    require (assertionsHold flat cells == sample.accepted)
      s!"{gadget.name}/{sample.name}: Lean constraints disagree with expected acceptance"
    let inputJson := Json.mkObj (gadget.inputNames.zip (sample.inputs.map jsonNat))
    writeJson (path / "inputs" / s!"{sample.name}.json") inputJson
    let mut mutations : List Json := []
    for mutation in gadget.mutations sample do
      require (mutation.cell < count && mutation.value < prime)
        s!"{gadget.name}/{mutation.name}: invalid mutation"
      require (assertionsHold flat (cells.set mutation.cell (mutation.value : F)) == mutation.accepted)
        s!"{gadget.name}/{mutation.name}: Lean mutation acceptance mismatch"
      mutations := mutations ++ [Json.mkObj [
        ("id", toJson mutation.name), ("cell", toJson mutation.cell),
        ("value", jsonNat mutation.value), ("accepted", toJson mutation.accepted)]]
    cases := cases ++ [Json.mkObj [
      ("id", toJson sample.name), ("input", inputJson), ("accepted", toJson sample.accepted),
      ("leanCells", toJson (cells.map (fun value => toString value.val))),
      ("mutations", toJson mutations)]]
  writeJson (path / "cases.json") (toJson cases)
  let getNat (key : String) : IO Nat := liftResult (r1csJson.getObjValAs? Nat key)
  pure (Json.mkObj [
    ("name", toJson gadget.name), ("inputCells", toJson inputs),
    ("witnessCells", toJson (count - inputs)),
    ("leanAssertions", toJson (flat.countP fun op => match op with | .assert _ => true | _ => false)),
    ("r1csConstraints", toJson (← getNat "nConstraints")),
    ("signals", toJson (← getNat "nVars")),
    ("wasmBytes", toJson wasm.size), ("r1csBytes", toJson r1cs.size),
    ("cases", toJson gadget.samples.length)])

def rejectionTests : IO Json := do
  let table : Table F field := { name := "reject.lookup", Contains := fun _ _ => True }
  let channel : Channel F field := { name := "reject.interaction", Guarantees := fun _ _ => True }
  let tests : List (String × List (Operation F)) := [
    ("lookup", [Operation.lookup ⟨table.toRaw, #v[0]⟩]),
    ("interaction", (channel.push (0 : Expression F)).operations 0),
    ("native", [.witness 1 (.native fun _ => #v[0])]),
    ("dataGet", [.witness 1 (.ir [] (.lit #v[.dataGet "external" 1 (.const 0) ⟨0, by decide⟩]))]),
    ("hintGet", [.witness 1 (.ir [] (.lit #v[.hintGet "external" 1 (.const 0) ⟨0, by decide⟩]))]),
    ("unbound-index", [.witness 1 (.ir [] (.lit #v[.ofU64 .idx]))])]
  let mut results : List Json := []
  for (name, ops) in tests do
    let compiled := compileR1CSBin prime 0 [] [] ops 4
    match compiled with
    | .ok _ => throw (IO.userError s!"unsupported {name} unexpectedly compiled to R1CS")
    | .error error =>
      match eligible 0 ops with
      | .ok _ => throw (IO.userError s!"eligibility accepted {name}")
      | .error _ => pure ()
      if name != "lookup" && name != "interaction" then
        match compileModule prime 0 [] [] ops 4 with
        | .ok _ => throw (IO.userError s!"unsupported {name} unexpectedly compiled to WASM")
        | .error _ => pure ()
      results := results ++ [Json.mkObj [("id", toJson name), ("r1csError", toJson error)]]
  pure (toJson results)

end BackendGadgets

/-- Record the resolved build input without maintaining another dependency pin in this driver. -/
private def cleanRevision : IO String := do
  let manifest ← BackendGadgets.liftResult (Lean.Json.parse (← IO.FS.readFile "lake-manifest.json"))
  let packages ← BackendGadgets.liftResult (manifest.getObjValAs? (Array Lean.Json) "packages")
  for package in packages do
    let name ← BackendGadgets.liftResult (package.getObjValAs? String "name")
    if name == "Clean" then
      return ← BackendGadgets.liftResult (package.getObjValAs? String "rev")
  throw (IO.userError "lake-manifest.json has no resolved Clean dependency")

def main (args : List String) : IO UInt32 := do
  match args with
  | [output] =>
    let revision ← cleanRevision
    let directory := System.FilePath.mk output
    IO.FS.createDirAll directory
    let rejected ← BackendGadgets.rejectionTests
    let mut costs : List Lean.Json := []
    for gadget in BackendGadgets.gadgets do
      costs := costs ++ [← BackendGadgets.exportGadget directory gadget]
    BackendGadgets.writeJson (directory / "manifest.json") (Lean.Json.mkObj [
      ("field", Lean.toJson "BN254 scalar field"), ("prime", BackendGadgets.jsonNat BackendGadgets.prime),
      ("cleanRevision", Lean.toJson revision),
      ("snarkjs", Lean.toJson "0.7.6"), ("numWords", Lean.toJson (4 : Nat)),
      ("claim", Lean.toJson "standalone backend conformance; not a verified backend or ensemble export"),
      ("gadgets", Lean.toJson costs), ("rejected", rejected)])
    IO.println s!"Exported {costs.length} unchanged gadget constraint systems to {output}"
    return 0
  | _ => IO.eprintln "usage: backendGadgets OUTPUT_DIRECTORY"; return 2
