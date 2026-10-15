import SP1Clean.Soundness.HostCommitEnsemble
import SP1Clean.Proofs.Chips.HostCommitChip.Populate
import SP1Clean.Model.SP1Field
import Clean.Circuit.WitnessExport

/-! # Physical commitment-bank boundary regressions

Build the actual nine bank tables and separate public verifier. Evaluate their canonical ledger
at the data derived from the committed rows, retaining zero-multiplicity occurrences. Empty-bank
checks cover every emitted channel. Active histories check all assertions and Byte meanings, then bank-channel
balance; authenticating their HostCall inputs remains the enclosing machine's responsibility.
-/

namespace SP1CleanTest.Core.HostCommitBoundary

open Circuit Air.Flat SP1Clean SP1Clean.HostCommitChip SP1Clean.Soundness

private abbrev Fp := ZMod SP1Prime
private abbrev Ledger := List (String × List Fp × Fp)

private instance byteDecidable (op : ByteOpcode) (a b c : Fp) : Decidable (op.constrain a b c) := by
  cases op <;> unfold ByteOpcode.constrain <;> infer_instance

private def byteValid (values : List Fp) : Bool :=
  match values with
  | [opcode, a, b, c] =>
    [ByteOpcode.AND, .OR, .XOR, .U8Range, .LTU, .MSB, .Range].any fun op =>
      opcode == (op.idx : Fp) && decide (op.constrain a b c)
  | _ => false

private def checked (component : Component Fp) (data : ProverData Fp) (row : Array Fp) : Bool :=
  let env := Environment.fromArray row data
  component.rowOperations.toFlat.all fun operation =>
    match operation with
    | .assert expression => env expression == 0
    | .lookup _ => false
    | .witness .. => true
    | .interact interaction =>
      env interaction.mult == 0 || interaction.channel.name != "SP1Byte" ||
        byteValid (interaction.msg.map env).toList

private def tableChecked (data : ProverData Fp) (table : Table Fp) : Bool :=
  table.table.all (checked table.component data)

private def evaluatedWitness {PublicIO : TypeMap} [ProvableType PublicIO]
    {ensemble : Ensemble Fp PublicIO} (built : EnsembleWitness ensemble) : Bool × Ledger :=
  (built.tables.all (tableChecked built.data),
    built.interactions.map fun interaction =>
      (interaction.channel.name, interaction.msg.toList, interaction.mult))

private def balance (ledger : Ledger) : Bool :=
  ledger.length < SP1Prime && ledger.all fun key =>
    ((ledger.filter (fun item => item.1 == key.1 && item.2.1 == key.2.1)).map (·.2.2)).sum == 0

private def calls (deferred : Bool) (slot : Fin 8) : List (Inputs Fp) := Id.run do
  let make (clock value : ℕ) (previous : State Fp) := HostCommitChip.populate deferred
    ⟨0, clock, codeWord deferred, slotWord slot, Target.bitVecToWord (BitVec.ofNat 64 value), codeWord deferred, 0⟩ previous
  let first := make 1 65537 HostCommitBoundary.initial
  let second := make 265 131075 (first.next slot)
  return [first, second]

private def lastState (deferred : Bool) (slot : Fin 8) : State Fp :=
  ((calls deferred slot)[1]!).next slot

private def tableFor (deferred : Bool) (events : List (Fin 8 × Inputs Fp))
    (terminals : List (State Fp)) (index : HostCommitBank.Index) : Table Fp :=
  match index with
  | some selected => Table.build { circuit := HostCommitChip.circuit deferred selected }
      ((events.filter (fun event => event.1 == selected)).map (·.2)) (fun _ _ => #[]) (ProverHint.empty Fp)
  | none => Table.build { circuit := HostCommitBoundary.terminal deferred } terminals
      (fun _ _ => #[]) (ProverHint.empty Fp)

private def witnessFor (deferred : Bool) (source : Model.Core.HostState) (events : List (Fin 8 × Inputs Fp))
    (terminals : List (State Fp)) (publicValues : Vector (Word Fp) 8) :
    EnsembleWitness (HostCommitEnsemble.ensemble (p := SP1Prime) deferred source [] []
      (by simpa using HostCommitBank.components_unique_names (p := SP1Prime) deferred)) :=
  EnsembleWitness.ofTables _ (HostCommitBank.indices.map (tableFor deferred events terminals))
    publicValues (by
      simp only [List.map_map, HostCommitEnsemble.ensemble, HostCommitBank.components,
        HostCommitBank.views, List.append_nil, Function.comp_def]
      apply List.map_congr_left
      intro index _
      cases index <;> rfl)

private def witness (deferred : Bool) (slot : Fin 8) (active : Bool)
    (terminals : List (State Fp)) (publicValues : Vector (Word Fp) 8) :=
  witnessFor deferred {} (if active then (calls deferred slot).map (slot, ·) else []) terminals publicValues

private def evaluated (deferred : Bool) (slot : Fin 8) (active : Bool)
    (terminals : List (State Fp)) (publicValues : Vector (Word Fp) 8) : Bool × Ledger :=
  evaluatedWitness (witness deferred slot active terminals publicValues)

/-- Empty banks have one genuine terminal row, nine tables, and a balanced complete ledger. -/
theorem emptyBanks : [false, true].all (fun deferred =>
    let empty := evaluated deferred 0 false [HostCommitBoundary.initial] (Vector.replicate 8 0)
    empty.1 && balance empty.2 &&
      (witness deferred 0 false [HostCommitBoundary.initial] (Vector.replicate 8 0)).tables.length == 9) = true := by
  native_decide

/-- Physical slot grouping does not lose repeated writes; the final public bank is enforced. -/
theorem repeatedBanks : [false, true].all (fun deferred => (List.finRange 8).all fun slot =>
    let last := lastState deferred slot
    let result := evaluated deferred slot true [last] last.values
    result.1 && balance (result.2.filter fun item => item.1 == (stateChannel (p := SP1Prime) deferred).name)) = true := by
  native_decide

/-- Omitting or duplicating the terminal, forging genesis, or changing the public result fails balance. -/
theorem boundaryTampering : [false, true].all (fun deferred =>
    let last := lastState deferred 3
    [evaluated deferred 0 false [] (Vector.replicate 8 0),
     evaluated deferred 0 false [HostCommitBoundary.initial, HostCommitBoundary.initial] (Vector.replicate 8 0),
     evaluated deferred 0 false [last] last.values,
     evaluated deferred 3 true [last] (Vector.replicate 8 0)].all fun result =>
       result.1 && !balance (result.2.filter fun item => item.1 == (stateChannel (p := SP1Prime) deferred).name)) = true := by
  native_decide

private def interleaved (deferred : Bool) : List (Fin 8 × Inputs Fp) × State Fp := Id.run do
  let make (slot : Fin 8) (clock value : ℕ) (previous : State Fp) := HostCommitChip.populate deferred
    ⟨0, clock, codeWord deferred, slotWord slot, Target.bitVecToWord (BitVec.ofNat 64 value), codeWord deferred, 0⟩ previous
  let first := make 7 1 11 HostCommitBoundary.initial
  let second := make 0 265 22 (first.next 7)
  let third := make 7 529 33 (second.next 0)
  return ([(7, first), (0, second), (7, third)], third.next 7)

/-- Slot-grouped physical tables retain a history whose chronological order crosses tables. -/
theorem interleavedBanks : [false, true].all (fun deferred =>
    let (events, last) := interleaved deferred
    let built := witnessFor deferred {} events [last] last.values
    let checks := evaluatedWitness built
    checks.1 && balance (checks.2.filter fun item =>
      item.1 == (stateChannel (p := SP1Prime) deferred).name) &&
      (built.tables.flatMap (fun table => table.table.map (fun row => row[1]!))) == [265, 1, 529, 529]) = true := by
  native_decide

private def terminalChecked (deferred : Bool) (state : State Fp) : Bool :=
  tableChecked (fun _ _ => #[]) (Table.build { circuit := HostCommitBoundary.terminal deferred } [state]
    (fun _ _ => #[]) (ProverHint.empty Fp))

/-- The sentinel cannot be reused as an ordinary clock or as another terminal's predecessor. -/
theorem terminalClocks : [false, true].all (fun deferred =>
    terminalChecked deferred ⟨2 ^ 24 - 1, 2 ^ 24 - 1, Vector.replicate 8 0⟩ &&
    !(tableChecked (fun _ _ => #[]) (Table.build { circuit := HostCommitChip.circuit deferred 0 }
      [HostCommitChip.populate deferred ((calls deferred 0)[0]!).call
        (HostCommitBoundary.final (Vector.replicate 8 0))] (fun _ _ => #[]) (ProverHint.empty Fp))) &&
    [⟨2 ^ 24, 0, Vector.replicate 8 0⟩, ⟨0, 2 ^ 24, Vector.replicate 8 0⟩,
     ⟨-1, 0, Vector.replicate 8 0⟩, ⟨0, -1, Vector.replicate 8 0⟩].all
       (fun state => !terminalChecked deferred state)) = true := by native_decide

/-- info: exportable ✓ (48 witness cells) -/
#guard_msgs in
#assert_exportable (HostCommitBoundary.terminal (p := SP1Prime) false)

/-- info: exportable ✓ (48 witness cells) -/
#guard_msgs in
#assert_exportable (HostCommitBoundary.terminal (p := SP1Prime) true)

/-- info: exportable ✓ (0 witness cells) -/
#guard_msgs in
#assert_exportable (HostCommitBoundary.verifier (p := SP1Prime) false (Vector.replicate 8 0))

/-- info: exportable ✓ (0 witness cells) -/
#guard_msgs in
#assert_exportable (HostCommitBoundary.verifier (p := SP1Prime) true (Vector.replicate 8 0))

private def continuationSource : Model.Core.HostState :=
  { committed := #v[1, 65537, 3, 4, 5, 6, 7, 4294967295],
    deferred := #v[101, 102, 103, 104, 105, 106, 107, 108],
    stdout := [11, 22], stderr := [33] }

private def continuation (deferred : Bool) : List (Fin 8 × Inputs Fp) × State Fp := Id.run do
  let make (slot : Fin 8) (clock value : ℕ) (previous : State Fp) := HostCommitChip.populate deferred
    ⟨0, clock, codeWord deferred, slotWord slot, Target.bitVecToWord (BitVec.ofNat 64 value), codeWord deferred, 0⟩ previous
  let seed := HostCommitBoundary.start (HostCommitEnsemble.sourceValues deferred continuationSource)
  let first := make 7 1048577 11 seed
  let second := make 0 1048841 22 (first.next 7)
  let third := make 7 1049105 33 (second.next 0)
  return ([(7, first), (0, second), (7, third)], third.next 7)

private def bankChecked (deferred : Bool) (source : Model.Core.HostState)
    (events : List (Fin 8 × Inputs Fp)) (last : State Fp) (values : Vector (Word Fp) 8) : Bool :=
  let checks := evaluatedWitness (witnessFor deferred source events [last] values)
  checks.1 && balance (checks.2.filter fun item =>
    item.1 == (stateChannel (p := SP1Prime) deferred).name)

/-- Nonzero banks survive empty segments and repeated interleaved writes. A cut seeds the second
shard from the first result with a local clock-zero token, preserving all untouched host fields. -/
theorem continuationBanks : [false, true].all (fun deferred =>
    let seed := HostCommitBoundary.start (HostCommitEnsemble.sourceValues (p := SP1Prime) deferred continuationSource)
    let empty := evaluatedWitness (witnessFor deferred continuationSource [] [seed] seed.values)
    let (events, last) := continuation deferred
    let first := events[0]!.2.next 7
    let middle := first.apply deferred continuationSource
    let rest := events.drop 1
    let resumed := (rest[0]!.1, { rest[0]!.2 with previous := HostCommitBoundary.start first.values }) :: rest.drop 1
    empty.1 && balance empty.2 &&
      bankChecked deferred continuationSource events last last.values &&
      bankChecked deferred continuationSource (events.take 1) first first.values &&
      bankChecked deferred middle resumed last last.values &&
      decide (middle.stdout = continuationSource.stdout ∧ middle.stderr = continuationSource.stderr ∧
        (if deferred then middle.committed = continuationSource.committed
          else middle.deferred = continuationSource.deferred))) = true := by native_decide

/-- A continuation cannot reset its source, alter an untouched source slot, or forge an outgoing
slot. Changing a high word limb is rejected even when 32-bit decoding would discard that limb. -/
theorem continuationTampering : [false, true].all (fun deferred =>
    let (events, last) := continuation deferred
    let forgedSource := if deferred then { continuationSource with deferred := continuationSource.deferred.set 5 999 }
      else { continuationSource with committed := continuationSource.committed.set 5 999 }
    let forgedValues := last.values.set 5 (last.values[5].set 2 1)
    !bankChecked deferred {} events last last.values &&
      !bankChecked deferred forgedSource events last last.values &&
      !bankChecked deferred continuationSource events last forgedValues) = true := by native_decide

/-- info: exportable ✓ (0 witness cells) -/
#guard_msgs in
#assert_exportable (HostCommitBoundary.verifier (p := SP1Prime) false
  (HostCommitEnsemble.sourceValues false continuationSource))

/-- info: exportable ✓ (0 witness cells) -/
#guard_msgs in
#assert_exportable (HostCommitBoundary.verifier (p := SP1Prime) true
  (HostCommitEnsemble.sourceValues true continuationSource))

end SP1CleanTest.Core.HostCommitBoundary
