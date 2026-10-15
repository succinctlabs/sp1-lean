import SP1CleanTest.Alignment.Examples.LoadByteStatic

/-! Executable costs and regressions for the dedicated-provider LoadByte comparison. -/

open Lean Circuit Air.Flat SP1Clean
open SP1CleanTest.Alignment.Examples.LoadByteStatic
open SP1Clean.Soundness.LoadByteStatic

namespace SP1Clean.LoadByteStaticRunner

/-- Syntax-derived polynomial degree bound; no cancellation or backend lowering is assumed. -/
def degreeBound : Expression F → ℕ
  | .var _ => 1
  | .const _ => 0
  | .add a b => max (degreeBound a) (degreeBound b)
  | .mul a b => degreeBound a + degreeBound b

/-- Costs are evaluated on actual programs and built rows, including disabled interactions. -/
def costs (tables : List (Table F)) : Json :=
  let rows := tables.flatMap fun table => table.table.map fun row => (table.component, row)
  let constraints := rows.flatMap fun (component, _) => component.operations.constraints
  let lookups := rows.flatMap fun (component, _) => component.operations.lookups
  Json.mkObj [
    ("physicalRows", toJson rows.length),
    ("cells", toJson ((rows.map fun entry => entry.2.size).sum)),
    ("inputCells", toJson ((rows.map fun entry => entry.1.rowOffset).sum)),
    ("witnessCells", toJson ((rows.map fun entry => entry.2.size - entry.1.rowOffset).sum)),
    ("assertions", toJson constraints.length),
    ("maxConstraintDegreeBound", toJson ((constraints.map degreeBound).foldl max 0)),
    ("fixedLookupOccurrences", toJson lookups.length),
    ("maxLookupEntryDegreeBound", toJson
      ((lookups.flatMap fun lookup => lookup.entry.toList.map degreeBound).foldl max 0)),
    ("rawInteractions", toJson ((tables.flatMap (·.interactions (deriveProverData tables))).length)),
    ("rawByteInteractions", toJson (byteLedger tables).length),
    ("zeroByteInteractions", toJson ((byteLedger tables).countP fun interaction => interaction.mult == 0))]

/-- Print one deterministic report; any failed case or unsupported provider demand exits nonzero. -/
def main : IO Unit := do
  let some residual := residual? workload | throw (IO.userError "unsupported residual provider demand")
  let cases := matrix.map fun sample =>
    let signed := sample.1
    let offset := sample.2.1
    let value := sample.2.2
    (s!"{if signed then "LB" else "LBU"}/offset-{offset}/byte-{value}", true,
      caseCheck (input signed offset value))
  let cases := cases ++ [("inactive-byte-300", true, caseCheck inactive),
    ("same-key-reader-demand", true, repeatedKeyRetained)] ++
      invalidCases.map (fun (name, accepted) => (name, false, accepted))
  let old := originalAssembly workload data hint residual
  let new := replacementAssembly workload data hint residual
  let oldByteBalanced := byteBalanced old
  let newByteBalanced := byteBalanced new
  let report := Json.mkObj [
    ("scope", toJson "dedicated selected-pair providers plus identical residual providers; local constraints and Byte balance"),
    ("notClaimed", toJson "canonical inventory recount, all-channel acceptance, full-core speedup, or R1CS score"),
    ("degreeMetric", toJson "syntactic polynomial degree upper bound over actual flattened expressions"),
    ("fieldCharacteristic", toJson SP1Prime),
    ("activeRows", toJson matrix.length), ("inactiveRows", toJson (1 : ℕ)),
    ("fixedTableRows", toJson (LoadByteStaticChip.fixedByteLookup (p := SP1Prime)).rows.length),
    ("oldDedicatedProviderRows", toJson workload.length),
    ("newDedicatedProviderRows", toJson (0 : ℕ)),
    ("sharedResidualProviderRows", toJson ((residual.map fun table => table.table.length).sum)),
    ("oldConsumer", costs [originalTable workload data hint]),
    ("newConsumer", costs [replacementTable workload data hint]),
    ("oldAssembly", costs old), ("newAssembly", costs new),
    ("oldByteBalanced", toJson oldByteBalanced), ("newByteBalanced", toJson newByteBalanced),
    ("cases", toJson (cases.map fun (name, expected, actual) => Json.mkObj
      [("id", toJson name), ("expected", toJson expected), ("actual", toJson actual),
       ("passed", toJson (expected == actual))]))]
  IO.println report.pretty
  unless cases.all (fun sample => sample.2.1 == sample.2.2) &&
      tablesCheck old && tablesCheck new && oldByteBalanced && newByteBalanced do
    throw (IO.userError "LoadByte static-lookup regression failed")

end SP1Clean.LoadByteStaticRunner

#eval SP1Clean.LoadByteStaticRunner.main
