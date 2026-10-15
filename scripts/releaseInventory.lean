import SP1CleanTest.Alignment.Support.BranchEnsembleFixture

/-! Read the installed native assembly directly. This is inventory metadata, not AIR lowering.
Generated reports live under the ignored build tree; Rust supplies the independent release layout.
-/

open Lean Circuit Air.Flat SP1Clean.Audit.BranchEnsemble

private def releaseInventory : IO Unit := do
  let ensemble := assembly target
  let tables := ensemble.tables.mapIdx fun index component => Json.mkObj [
    ("slot", toJson index), ("name", toJson component.circuit.name),
    ("width", toJson component.width), ("inputWidth", toJson component.rowOffset),
    ("fixedWidth", toJson component.fixedWidth),
    ("lookups", toJson (component.rowOperations.lookups.map (·.table.name)))]
  IO.println <| (Json.mkObj [
    ("tables", toJson tables),
    ("publicWidth", toJson (size SP1Clean.SP1PublicIO))]).compress

#eval releaseInventory
