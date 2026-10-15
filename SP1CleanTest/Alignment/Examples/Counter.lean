import SP1Clean.Soundness.Examples.Counter
import ToClean.Air.FiniteLookup
import Clean.Circuit.WitnessExport

/-! # Executable checks of the complete counter example

The checks evaluate the actual physical witness, assertions, fixed lookups, and complete
State ledger. The universal acceptance equivalence lives in the production module; these
finite regression checks use the separate test/compiler trust boundary.
-/

namespace SP1CleanTest.Alignment.Examples.Counter

open Air.Flat Circuit SP1Clean.Soundness.CounterExample

/-- The fixed range table used by physical transitions. Public bounds use verifier assertions. -/
def fixedLookups : List (FiniteLookup F) :=
  [FiniteLookup.ofStatic (rangeTable 15 (by decide))]

/-- Evaluate every actual assertion and lookup against a supplied physical row. -/
def rowChecks (component : Component F) (data : ProverData F) (row : Array F) : Bool :=
  let env := Environment.fromArray row data
  component.rowOperations.toFlat.all fun operation =>
    match operation with
    | .assert expression => env expression == 0
    | .lookup lookup => fixedLookups.any fun table =>
        lookup.table.name == table.table.name && table.rows.any fun fixed =>
          fixed.toArray == (lookup.entry.map env).toArray
    | .witness .. | .interact .. => true

/-- Check the real raw witness, including channel membership and the characteristic bound. -/
def validates (witness : EnsembleWitness ensemble) : Bool :=
  let ledger := witness.interactions
  (witness.tables.all fun table =>
    table.table.all (rowChecks table.component witness.data)) &&
    decide (ledger.length < 97) &&
    ledger.all fun key =>
      (ensemble.channels.map RawChannel.name).contains key.channel.name &&
        ((ledger.filter fun entry => entry.channel.name == key.channel.name &&
          entry.msg == key.msg).map Interaction.mult).sum == 0

/-- Compile data-only increment events and check the returned physical AIR witness. -/
def compiledAccepted (initial final count : ℕ) : Bool :=
  (compile (initial, final) (List.replicate count Event.increment)).any validates

/-- Return State and complete interaction counts, including the four public-check occurrences. -/
def compiledCount (initial final count : ℕ) : Option (ℕ × ℕ) :=
  (compile (initial, final) (List.replicate count Event.increment)).map
    (fun witness =>
      let ledger := witness.interactions
      ((ledger.filter (fun interaction => interaction.channel.name == state.name)).length, ledger.length))

/-- Named positive and adversarial checks, each using the compiler or the actual AIR evaluator. -/
def results : List (String × Bool × Bool) :=
  [("compile-2-to-5", true, compiledAccepted 2 5 3),
   ("empty-0-to-0", true, compiledAccepted 0 0 0),
   ("empty-15-to-15", true, compiledAccepted 15 15 0),
   ("maximum-0-to-15", true, compiledAccepted 0 15 15),
   ("shuffled-physical-rows", true,
     validates (witnessOfRows (2, 5) [(4, 5), (2, 3), (3, 4)])),
   ("missing-transition", false, validates (witnessOfRows (2, 5) [(2, 3), (4, 5)])),
   ("duplicate-transition", false,
     validates (witnessOfRows (2, 5) [(2, 3), (3, 4), (3, 4), (4, 5)])),
   ("wrong-public-endpoint", false,
     validates (witnessOfRows (2, 6) [(2, 3), (3, 4), (4, 5)])),
   ("wrong-event-count", false, (compile (2, 5) (List.replicate 2 Event.increment)).isSome),
   ("endpoint-16", false, (compile (15, 16) [Event.increment]).isSome),
   ("raw-empty-endpoint-16", false, validates (witnessOfRows (16, 16) [])),
   ("raw-empty-endpoint-96", false, validates (witnessOfRows (96, 96) [])),
   ("decreasing-boundary", false, (compile (5, 2) []).isSome),
   ("empty-unequal-boundaries", false, (compile (2, 3) []).isSome),
   ("modular-wrap-row", false,
     rowChecks { circuit := transition } (witnessOfRows (0, 0) []).data #[96, 0])]

/-- Both successful compilation and physical mutations have the stated executable outcomes. -/
theorem casesMatch : results.all (fun (_, expected, actual) => expected == actual) = true := by
  native_decide

/-- State endpoints and all four public-check occurrences survive, even for an empty trace. -/
theorem exactCounts :
    compiledCount 2 5 3 = some (8, 12) ∧ compiledCount 0 0 0 = some (2, 6) ∧
      compiledCount 0 15 15 = some (32, 36) := by native_decide

/-- Only transition rows determine named prover data; the verifier adds no physical table. -/
theorem physicalData :
    let witness := witnessOfRows (2, 5) [(2, 3), (3, 4), (4, 5)]
    witness.tables.length = 1 ∧ witness.data "CounterTransition" 2 =
      #[#v[2, 3], #v[3, 4], #v[4, 5]] := by native_decide

/-- The wrap row satisfies the field equation but fails the actual row's fixed lookup. -/
theorem wrapNeedsLookup :
    (0 : F) = (96 : F) + 1 ∧
      rowChecks { circuit := transition } (witnessOfRows (0, 0) []).data #[96, 0] = false := by
  native_decide

/-- Print actual compiled rows and the complete positive/negative regression results. -/
def main : IO Unit := do
  IO.println "Counter over ZMod 97: executable fixture checks, not proof certificates"
  for (name, expected, actual) in results do
    IO.println s!"{if expected == actual then "PASS" else "FAIL"} {name}: expected {expected}, actual {actual}"
  unless results.all (fun (_, expected, actual) => expected == actual) do
    throw (IO.userError "Counter fixture expectation mismatch")
  match compile (2, 5) (List.replicate 3 Event.increment) with
  | none => throw (IO.userError "Valid counter example did not compile")
  | some witness =>
    let rows := witness.tables.flatMap fun table => table.table.map fun row =>
      row.toList.map ZMod.val
    let ledger := witness.interactions
    let stateCount := (ledger.filter (fun interaction => interaction.channel.name == state.name)).length
    IO.println s!"Compiled 2 -> 5: rows {reprStr rows}; State interactions {stateCount}; total interactions {ledger.length}"

/-- info: exportable ✓ (0 witness cells) -/
#guard_msgs in
#assert_exportable transition

/-- info: exportable ✓ (0 witness cells) -/
#guard_msgs in
#assert_exportable verifier

end SP1CleanTest.Alignment.Examples.Counter
