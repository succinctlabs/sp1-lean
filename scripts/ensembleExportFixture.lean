import SP1CleanTest.Core.EnsembleExport
import SP1CleanTest.Core.InstructionExport
import SP1CleanTest.Core.ByteProviderExport
import SP1CleanTest.Core.SnapshotRegisterExport
import SP1CleanTest.Core.StaticProviderExport
import SP1CleanTest.Core.RamExport

/-! # Clean's built-in whole-ensemble Rust export fixture

Generated sources and Lean reference rows stay under the ignored .lake/ensemble-export tree.
The comparison script regenerates twice, checks the completion marker and compiles the output.
-/

open Lean SP1CleanTest.Core.EnsembleExport

private def physicalReference {PublicIO : TypeMap} [ProvableType PublicIO]
    {ensemble : Air.Flat.Ensemble (ZMod SP1Clean.SP1Prime) PublicIO}
    (witness : Air.Flat.EnsembleWitness ensemble) : Json :=
  Json.mkObj [
    ("tables", toJson (witness.tables.map fun table =>
      table.table.map fun row => row.map (·.val))),
    ("interactions", toJson (witness.interactions.map fun interaction => Json.mkObj [
      ("channel", toJson interaction.channel.name),
      ("message", toJson (interaction.msg.map (·.val))),
      ("multiplicity", toJson interaction.mult.val),
      ("assumeGuarantees", toJson interaction.assumeGuarantees)]))]

private def exportEnsembleFixture : IO Unit := do
  let out := System.FilePath.mk
    ((← IO.getEnv "ENSEMBLE_EXPORT_OUT").getD ".lake/ensemble-export/manual")
  IO.FS.createDirAll out
  let exported ← match rust with
    | .ok value => pure value
    | .error message => throw (IO.userError message)
  IO.FS.writeFile (out / "fixed_membership.rs") exported
  for (name, result) in SP1CleanTest.Core.InstructionExport.rustExports ++
      SP1CleanTest.Core.ByteProviderExport.rustExports ++
      SP1CleanTest.Core.SnapshotRegisterExport.rustExports ++
      SP1CleanTest.Core.SnapshotRegisterExport.Target.rustExports ++
      SP1CleanTest.Core.StaticProviderExport.rustExports ++
      SP1CleanTest.Core.RamExport.rustExports do
    let source ← match result with
      | .ok value => pure value
      | .error message => throw (IO.userError message)
    IO.FS.writeFile (out / name) source
  let cases ← ([7, 9, 8] : List Nat).mapM fun (value : Nat) => do
    let result ← match generate (Nat.cast value) with
      | .error message => pure <| Json.mkObj [
          ("publicInput", toJson value), ("accepted", toJson false), ("error", toJson message)]
      | .ok witness => do
          let accepted := description.checkWitness SP1Clean.SP1Prime witness
          unless accepted do throw (IO.userError "generated witness failed raw acceptance")
          pure <| Json.mkObj [
            ("publicInput", toJson value), ("accepted", toJson accepted),
            ("tables", toJson (witness.tables.map fun table =>
              table.table.map fun row => row.map (·.val))),
            ("interactionCount", toJson witness.interactions.length)]
    pure result
  IO.FS.writeFile (out / "fixed_membership.reference.json") ((toJson cases).compress ++ "\n")
  let registerCases ← SP1CleanTest.Core.SnapshotRegisterExport.cases.mapM
      fun (name, requests, expected) => do
    let fields := [("name", toJson name),
      ("publicInput", toJson ((toElements requests).toArray.map (·.val))),
      ("accepted", toJson expected)]
    match SP1CleanTest.Core.SnapshotRegisterExport.generate requests with
    | .error message =>
      if expected then throw (IO.userError s!"{name}: {message}")
      pure <| Json.mkObj (fields ++ [("error", toJson message)])
    | .ok witness =>
      unless expected && SP1CleanTest.Core.SnapshotRegisterExport.description.checkWitness
          SP1Clean.SP1Prime witness do
        throw (IO.userError s!"unexpected source-register acceptance: {name}")
      pure <| Json.mkObj (fields ++ [("witness", physicalReference witness)])
  let empty ← match SP1CleanTest.Core.SnapshotRegisterExport.generateEmpty with
    | .error message => throw (IO.userError message)
    | .ok witness =>
      unless SP1CleanTest.Core.SnapshotRegisterExport.emptyDescription.checkWitness
          SP1Clean.SP1Prime witness do
        throw (IO.userError "unused fixed provider failed raw acceptance")
      pure (physicalReference witness)
  IO.FS.writeFile (out / "snapshot_registers.reference.json")
    ((Json.mkObj [("cases", toJson registerCases), ("empty", empty)]).compress ++ "\n")
  let targetCases ← SP1CleanTest.Core.SnapshotRegisterExport.Target.cases.mapM
      fun (name, requests, expected) => do
    let fields := [("name", toJson name),
      ("publicInput", toJson ((toElements requests).toArray.map (·.val))),
      ("accepted", toJson expected)]
    match SP1CleanTest.Core.SnapshotRegisterExport.Target.generate requests with
    | .error message =>
      if expected then throw (IO.userError s!"{name}: {message}")
      pure <| Json.mkObj (fields ++ [("error", toJson message)])
    | .ok witness =>
      unless SP1CleanTest.Core.SnapshotRegisterExport.Target.description.checkWitness
          SP1Clean.SP1Prime witness == expected do
        throw (IO.userError s!"unexpected target-register acceptance: {name}")
      pure <| Json.mkObj (fields ++ [("witness", physicalReference witness)])
  let targetEmpty ← match SP1CleanTest.Core.SnapshotRegisterExport.Target.generateEmpty with
    | .error message => throw (IO.userError message)
    | .ok witness =>
      unless SP1CleanTest.Core.SnapshotRegisterExport.Target.emptyDescription.checkWitness
          SP1Clean.SP1Prime witness do
        throw (IO.userError "unused target provider failed raw acceptance")
      pure (physicalReference witness)
  IO.FS.writeFile (out / "target_registers.reference.json")
    ((Json.mkObj [("cases", toJson targetCases), ("empty", targetEmpty)]).compress ++ "\n")
  let staticFixtures ← SP1CleanTest.Core.StaticProviderExport.fixtures.mapM fun (name, rows) => do
    let cases ← SP1CleanTest.Core.StaticProviderExport.requests.mapM fun request => do
      let expected := rows.contains request[0] && rows.contains request[1]
      let fields := [("publicInput", toJson ((toElements request).toArray.map (·.val))),
        ("accepted", toJson expected)]
      match SP1CleanTest.Core.StaticProviderExport.generate rows request with
      | .error message =>
        if expected then throw (IO.userError s!"{name}: {message}")
        pure <| Json.mkObj (fields ++ [("error", toJson message)])
      | .ok witness =>
        unless expected && (SP1CleanTest.Core.StaticProviderExport.description rows).checkWitness
            SP1Clean.SP1Prime witness do
          throw (IO.userError s!"unexpected padded membership acceptance: {name}")
        pure <| Json.mkObj (fields ++ [("witness", physicalReference witness)])
    let unused ← match SP1CleanTest.Core.StaticProviderExport.generateEmpty rows with
      | .error message => throw (IO.userError s!"{name}: {message}")
      | .ok witness =>
        unless (SP1CleanTest.Core.StaticProviderExport.emptyDescription rows).checkWitness
            SP1Clean.SP1Prime witness do
          throw (IO.userError s!"unused padded provider failed: {name}")
        pure (physicalReference witness)
    pure <| Json.mkObj [("name", toJson name), ("cases", toJson cases), ("unused", unused)]
  IO.FS.writeFile (out / "static_membership.reference.json") ((toJson staticFixtures).compress ++ "\n")
  let ramFixtures ← ["sp1.native.initial_memory", "sp1.native.target_memory"].mapM fun name => do
    let cases ← SP1CleanTest.Core.RamExport.cases.mapM fun (label, requests, expected) => do
      let fields := [("name", toJson label),
        ("publicInput", toJson ((toElements requests).toArray.map (·.val))),
        ("accepted", toJson expected)]
      match SP1CleanTest.Core.RamExport.generate name requests with
      | .error message =>
        if expected then throw (IO.userError s!"{label}: {message}")
        pure <| Json.mkObj (fields ++ [("error", toJson message)])
      | .ok witness =>
        unless expected && (SP1CleanTest.Core.RamExport.description name).checkWitness
            SP1Clean.SP1Prime witness do
          throw (IO.userError s!"unexpected RAM membership acceptance: {label}")
        pure <| Json.mkObj (fields ++ [("witness", physicalReference witness)])
    pure (name, toJson cases)
  IO.FS.writeFile (out / "ram_membership.reference.json") ((Json.mkObj ramFixtures).compress ++ "\n")
  let ramRows := SP1CleanTest.Core.RamExport.rowCases.map fun (name, component, inputs) =>
    (name, toJson (inputs.map fun cells =>
      let input := fromElements (Vector.ofFn fun index => cells[index.val]?.getD 0)
      let row := component.buildRow input (fun _ _ => #[]) (ProverHint.empty _)
      let env := Environment.fromArray row (fun _ _ => #[])
      Json.mkObj [("input", toJson (cells.map (·.val))), ("row", toJson (row.map (·.val))),
        ("interactions", toJson (component.rowOperations.interactionValues env |>.map fun entry =>
          Json.mkObj [("channel", toJson entry.channel.name),
            ("message", toJson (entry.msg.map (·.val))),
            ("multiplicity", toJson entry.mult.val), ("assumeGuarantees", toJson entry.assumeGuarantees)]))]))
  IO.FS.writeFile (out / "ram_rows.reference.json") ((Json.mkObj ramRows).compress ++ "\n")
  IO.println "EXPORTED ensemble Rust and Lean reference cases"

#eval exportEnsembleFixture
