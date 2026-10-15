import SP1CleanTest.Alignment.Audit.BranchEnsembleRoundTrip
import Lean.Data.Json

/-! Run through `python3 scripts/check_examples.py branch`. This evaluates the compiler-derived physical
witness and its mutations. The imported theorem supplies official Sail execution; this driver
does not execute the noncomputable full Sail state. -/

open Lean Circuit Air.Flat SP1Clean
open SP1Clean.Audit.BranchEnsemble

/-- Count the actual installed component operations for its physical rows. -/
private def rowStats (position : Nat) (table : Table Fp) : Json :=
  let operations := table.component.operations
  Json.mkObj [
    ("position", toJson position),
    ("rows", toJson table.table.length),
    ("width", toJson table.component.width),
    ("assertionsPerRow", toJson operations.constraints.length),
    ("fixedLookupsPerRow", toJson operations.lookups.length),
    ("interactionsPerRow", toJson operations.interactions.length)]

/-- Print revision-tagged computed outcomes and fail on any expectation mismatch. -/
private def runBranchEnsembleExample : IO Unit := do
  let revision ← IO.getEnv "SP1_EXAMPLE_REVISION"
  let status ← IO.getEnv "SP1_EXAMPLE_STATUS"
  unless revision.isSome && (status == some "clean" || status == some "dirty") do
    throw (IO.userError "Run python3 scripts/check_examples.py branch to attach revision provenance")
  let cases := results
  let sourcePc := header.init_pc0.val + 65536 * header.init_pc1.val + 4294967296 * header.init_pc2.val
  let targetPc := header.final_pc0.val + 65536 * header.final_pc1.val + 4294967296 * header.final_pc2.val
  let sourceClock := header.init_clk_0_16.val + 65536 * header.init_clk_16_24.val +
    16777216 * header.init_clk_24_32.val + 4294967296 * header.init_clk_32_48.val
  let targetClock := header.final_clk_0_16.val + 65536 * header.final_clk_16_24.val +
    16777216 * header.final_clk_24_32.val + 4294967296 * header.final_clk_32_48.val
  let event := SP1Clean.Audit.BranchCompilerRoundTrip.event
  let tableStats := activeWitness.tables.zipIdx.map fun (table, position) => rowStats position table
  let physicalLedger := activeWitness.tables.flatMap (·.interactions activeWitness.data)
  let verifierLedger := (assembly target).verifierOperations.interactionValues
    (Environment.fromInput header activeWitness.data)
  let report := Json.mkObj [
    ("revision", toJson revision.get!), ("dirty", toJson (status == some "dirty")),
    ("assembly", toJson "SP1Clean.Soundness.HostFinalMemory.ensemble"),
    ("theorem", toJson "SP1Clean.Audit.BranchEnsemble.joined"),
    ("sailEvidence", toJson "official Sail retirement proved by imported theorem; not executed by this runner"),
    ("instruction", toJson s!"BEQ x{event.opA},x{event.opB},+{event.imm}"),
    ("instructionWord", toJson SP1Clean.Audit.BranchCompilerRoundTrip.view.word.toNat),
    ("sourcePc", toJson sourcePc), ("targetPc", toJson targetPc),
    ("sourceClock", toJson sourceClock), ("targetClock", toJson targetClock),
    ("tableCount", toJson activeWitness.tables.length),
    ("tableRows", toJson (activeWitness.tables.map (·.table.length)).sum),
    ("physicalInteractions", toJson physicalLedger.length),
    ("verifierInteractions", toJson verifierLedger.length),
    ("interactions", toJson activeWitness.interactions.length),
    ("registeredChannelOccurrences", toJson (assembly target).channels.length),
    ("uniqueChannels", toJson (channels target).length),
    ("tables", toJson tableStats),
    ("cases", toJson (cases.map fun (name, expected, actual) => Json.mkObj [
      ("id", toJson name), ("expected", toJson expected), ("actual", toJson actual)]))]
  IO.println report.pretty
  unless cases.all (fun (_, expected, actual) => expected == actual) do
    throw (IO.userError "assembled branch regression mismatch")

#eval runBranchEnsembleExample
