import SP1Clean.Soundness.HostHintReadPartition
import SP1Clean.Soundness.HostHintReadLocalPermissions
import SP1Clean.Soundness.HostHintReadLocalRecords
import SP1Clean.Soundness.HostHintReadLocalExecution
import SP1Clean.Soundness.HostHintReadLocalQueue
import SP1Clean.Soundness.HostHintQueueBoundary
import SP1Clean.Soundness.HostHintQueueHistory
import SP1Clean.Soundness.HostQueueCPUOrder
import SP1Clean.Soundness.HostQueueCPUReplay
import SP1Clean.Soundness.HostHintReadCPUMemory
import SP1Clean.Proofs.Chips.HostHintLengthChip.Populate
import ToClean.Air.EnsembleBuild
import SP1CleanTest.Core.HintReadFixtures
import SP1Clean.Proofs.Chips.HostHintReadChip.Populate
import ToClean.Air.TableBuild
import SP1CleanTest.Core.StaticMembership

/-! # Executed shared HINT_READ table selection

Build the actual handler and consumer tables for different nodes, lengths, destinations, and
clocks. Check their computed cells and cursor ledger, then decode each selected physical table
back to the independent padded-write inventory. Installed permission and record-source tests
check their actual whole-witness ledgers and fixed lookups. These remain subsystem regressions:
the other channels and complete mixed execution are not claimed satisfied by these fixtures.
-/

namespace SP1CleanTest.Core.HostHintReadPartition

open Circuit Air.Flat SP1Clean Model.Core HintQueue Soundness HostChecks

private abbrev Fp := ZMod SP1Prime

private def hints : List Bytes := [HintReadFixtures.bytes 16, HintReadFixtures.bytes 8, []]

private def call (head previous now address : ℕ) : HostHintReadChip.Inputs Fp :=
  let store := (ofList hints).1
  let queue := (decode? store head).getD []
  let bytes := queue.headD []
  let host : HostState := { io := ⟨queue, []⟩ }
  let context : HostReadContext :=
    ⟨fun index => if index == 5 then some 241
      else if index == 10 then some (BitVec.ofNat 64 address)
      else if index == 11 then some (BitVec.ofNat 64 bytes.length) else none, fun _ => none⟩
  let executed := (host.run ⟨{ readOnly := fun _ => false }, SP1Prime⟩ context).getD
    ⟨.hintRead, 0, 0, 0, ⟨host, none⟩⟩
  HostHintReadChip.populate store head previous now executed

private def calls : List (HostHintReadChip.Inputs Fp) :=
  [call 3 0 1 65536, call 2 1 265 131064, call 1 265 (2 ^ 24 + 1) (2 ^ 48 - 8)]

private def words (call : HostHintReadChip.Inputs Fp) : List HintReadFixtures.Row :=
  let node := (node? (ofList hints).1 (Address.toNat call.node.pointer)).getD default
  (List.range (wordCount node.bytes)).map fun index =>
    let address := Address.ofNat (p := SP1Prime) (Address.toNat call.span.start + index * 8)
    let word := WordRecord.encode (p := SP1Prime) (Address.toNat call.node.pointer) node.bytes index
    let ram := HostRamAccessChip.populate ⟨0, 0, address[0], address[1], address[2], HintReadFixtures.oldWord⟩
      call.call.clk_high (call.call.clk_low.val % 65536 : ℕ) (call.call.clk_low.val / 65536 : ℕ) word.value
    let last := decide (index + 1 = wordCount node.bytes)
    (last, HintReadWordChip.populate last ram word.pointer word.index)

private def handlers (calls : List (HostHintReadChip.Inputs Fp)) : Table Fp :=
  Table.build HostHintReadCoverage.handler calls (fun _ _ => #[]) (ProverHint.empty Fp)

private def consumers (rows : List HintReadFixtures.Row) : List (Table Fp) :=
  HintReadCoverage.variants.map fun last => Table.build (HintReadCoverage.view last).component
    ((rows.filter (fun row => row.1 == last)).map (·.2)) (fun _ _ => #[]) (ProverHint.empty Fp)

private theorem consumers_aligned (rows : List HintReadFixtures.Row) :
    List.Forall₂ (fun last table => (HintReadCoverage.view last).component = table.component)
      HintReadCoverage.variants (consumers rows) := by
  simp only [consumers, HintReadCoverage.variants, List.map_cons, List.map_nil]
  exact .cons rfl (.cons rfl .nil)

/-- Filter Clean's evaluated ledger without dropping repeats or zero multiplicities. -/
private def ledgerFor (names : List String) (interactions : List (Interaction Fp)) : Ledger :=
  interactions.filterMap fun interaction =>
    if names.contains interaction.channel.name then
      some (interaction.channel.name, interaction.msg.toList, interaction.mult) else none

private def cursorLedger := ledgerFor ["sp1.native.hint_read_state"]
private def permissionLedger := ledgerFor ["SP1WritePermission"]
private def recordLedger := ledgerFor ["sp1.native.hint_node", "sp1.native.hint_word"]
private def queueLedger := ledgerFor ["sp1.native.hint_queue_state"]
private def callLedger := ledgerFor ["sp1.native.host_call"]

private def physicalInteractions (tables : List (Table Fp)) : List (Interaction Fp) :=
  let data := deriveProverData tables
  tables.flatMap (·.interactions data)

private def checked (data : ProverData Fp) (table : Table Fp) : Bool × Ledger :=
  let operations := table.component.rowOperations.toFlat
  let assertions := table.table.all fun row =>
    let env := Environment.fromArray row data
    operations.all fun operation =>
      match operation with
      | .assert expression => env expression == 0
      | .lookup _ => false
      | _ => true
  (assertions, cursorLedger (table.interactions data))

private def shared (calls : List (HostHintReadChip.Inputs Fp)) (rows : List HintReadFixtures.Row) : Bool :=
  let tables := handlers calls :: consumers rows
  let checked := tables.map (checked (deriveProverData tables))
  checked.all (·.1) && HintReadFixtures.balanced (checked.flatMap (·.2))

private def unique (table : Table Fp) : Bool :=
  decide (((table.table.map (Environment.fromArray · (deriveProverData [table]))).map
    Soundness.HostHintReadPartition.callClock).Nodup)

/-- Interleaved calls and reversed physical rows retain complete per-call writes across clock carries. -/
theorem sharedCalls :
    let table := handlers calls
    let rows := (calls.flatMap words).reverse
    let tables := consumers rows
    let data := deriveProverData (table :: tables)
    shared calls rows = true ∧ unique table = true ∧
      (table.table.map (Environment.fromArray · data)).all (fun env =>
        let call := HostHintReadCoverage.input env
        let key := Soundness.HostHintReadPartition.callClock env
        let selected := Soundness.HostHintReadPartition.tablesFor key tables data (consumers_aligned rows)
        let actual := ((node? (ofList hints).1 (Address.toNat call.node.pointer)).getD default).bytes
        let inventory := (HintReadCoverage.variants.zip selected).flatMap fun (last, table) =>
          table.table.map fun row => HintReadWrites.produced (last, Environment.fromArray row data)
        HintReadFixtures.balanced
          ((checked data (handlers [call])).2 ++ (selected.map (checked data)).flatMap (·.2)) &&
          inventory.mergeSort (fun a b => a.1 ≤ b.1) == wordWrites (Address.toNat call.span.start) actual) = true := by
  native_decide

/-- A missing handler or consumer cannot borrow a different event's cursor endpoints. -/
theorem missingAndOrphanRows :
    let rows := calls.flatMap words
    shared (calls.drop 1) rows = false ∧ shared calls (rows.drop 1) = false ∧
      shared calls (rows ++ words (call 3 0 9 65536)) = false ∧
      ((Soundness.HostHintReadPartition.tablesFor (0, 9) (consumers rows)
        (deriveProverData (consumers rows)) (consumers_aligned rows)).map
        (fun table => table.table.length)) = [0, 0] := by native_decide

/-- Duplicating complete calls preserves cursor balance but violates the required event uniqueness. -/
theorem duplicateHandlers :
    let doubled := calls ++ calls
    shared doubled (doubled.flatMap words) = true ∧ unique (handlers doubled) = false := by native_decide

private def image : ProgramImage := ⟨[(65536, 0x73), (131072, 0x73)], 65536, []⟩

private def source : ExecutionSnapshot :=
  { sail := { registers := (Soundness.Target.configuredState 65536).regs, memory := image.initialMemory }
    host := {}, clock := 1 }

private theorem baseNames :
    ((HostLocalCore.tables (p := SP1Prime) image source
      ((HostHintReadHandoff.receiver :: HostCallReceivers.available).map (·.component) ++
        (HostHintReadHandoff.wordResources ++ []))).map (·.circuit.name)).Nodup := by
  have names := HostHintReadLocal.source_unique_names (p := SP1Prime) image source []
  rw [HostLocalCore.tables_names] at names ⊢
  simp only [List.map_append, ← List.append_assoc, List.append_nil] at names ⊢
  exact (List.nodup_append.mp names).1

private def assembly :=
  HostHintReadLocal.ensemble (p := SP1Prime) image source HostCallReceivers.available [] [] baseNames

/-- Build every physical slot, retaining unused verifier-fixed membership rows at count zero. -/
private def buildWitness (ensemble : Ensemble Fp SP1PublicIO)
    (inputs : ℕ → List (List Fp)) : EnsembleWitness ensemble :=
  EnsembleWitness.ofTables ensemble
    (StaticMembership.buildTables ensemble.tables inputs
      []
      (fun _ _ => #[]) (ProverHint.empty Fp))
    (valueFromOffset SP1PublicIO 0 (Environment.fromArray #[] (fun _ _ => #[])))
    (StaticMembership.buildTables_components ..)

private def installedInputs (calls : List (HostHintReadChip.Inputs Fp)) (rows : List HintReadFixtures.Row)
    (permissions : List (WritePermissionProvider.Inputs Fp)) (index : ℕ) : List (List Fp) :=
  if index == 61 then permissions.map (fun row => (toElements row).toList)
  else if index == 62 then calls.map (fun row => (toElements row).toList)
  else if index == 83 || index == 84 then
    (rows.filter (fun row => row.1 == (index == 84))).map (fun row => (toElements row.2).toList)
  else []

/-- A physical ensemble witness used to test cursor extraction. Other channels are deliberately
not claimed balanced: source authentication and CPU instruction construction are separate tests. -/
private def installed (calls : List (HostHintReadChip.Inputs Fp)) (rows : List HintReadFixtures.Row)
    (permissions : List (WritePermissionProvider.Inputs Fp) := []) : EnsembleWitness assembly :=
  buildWitness assembly (installedInputs calls rows permissions)

/-- The installed 85-table assembly retains exactly the handler and both physical word tables.
Its complete cursor balances with reversed multi-call rows; missing handlers, missing words,
and orphan consumers fail at the same whole-witness channel boundary. The named prover data
contains the actual handler inputs in physical order. -/
theorem installedCursor :
    let rows := (calls.flatMap words).reverse
    let witness := installed calls rows
    let handler := HostHintReadLocal.handlerTable witness
    let tables := HostHintReadLocal.wordTables witness
    let cursor := cursorLedger witness.interactions
    witness.tables.length = 85 ∧ handler.table = (handlers calls).table ∧
      witness.data "sp1.native.hint_read" (size HostHintReadChip.Inputs) =
        (calls.map toElements).toArray ∧
      tables.map (·.table) = (consumers rows).map (·.table) ∧
      (handler :: tables).all (fun table => (checked witness.data table).1) = true ∧
      cursor = (checked witness.data handler).2 ++ (tables.map (checked witness.data)).flatMap (·.2) ∧
      HintReadFixtures.balanced cursor = true ∧
      HintReadFixtures.balanced (cursorLedger (installed (calls.drop 1) rows).interactions) = false ∧
      HintReadFixtures.balanced (cursorLedger (installed calls (rows.drop 1)).interactions) = false ∧
      HintReadFixtures.balanced (cursorLedger (installed calls (rows ++ words (call 3 0 9 65536))).interactions) = false := by
  native_decide

private def permissionRows (rows : List HintReadFixtures.Row) (forge := false) :
    List (WritePermissionProvider.Inputs Fp) :=
  rows.flatMap fun row => (List.range 8).filterMap fun index =>
    let address := Address.toNat row.2.address + index
    match WritePermissionProvider.populate? (p := SP1Prime) image address with
    | some input => some input
    | none => if forge then (WritePermissionProvider.populate? (p := SP1Prime) image (address - 8)).map
        (fun input => { input with address := Address.ofNat address }) else none

private def permissionRowsChecked (rows : List (WritePermissionProvider.Inputs Fp)) : Bool :=
  rows.all fun input =>
    (HostChecks.evaluateProgram (WritePermissionProvider.main image (varFromOffset WritePermissionProvider.Inputs 0))
      (toElements input).toList none [FiniteLookup.ofStatic image.writePermissionTable]).1

/-- Installed permissions cover the padding and final native RAM cell. Dropping a permission fails
balance. Padding into ROM keeps cursor balance but lacks permissions; forged provider rows restore
that balance only by violating the fixed provider's actual assertions/lookup. -/
theorem installedPermissions :
    let permittedCalls := [call 2 1 265 131056, call 1 265 (2 ^ 24 + 1) (2 ^ 48 - 8)]
    let rows := permittedCalls.flatMap words
    let permissions := permissionRows rows
    let writable := installed permittedCalls rows permissions
    let romCalls := [call 2 1 265 131064]
    let romRows := romCalls.flatMap words
    let rom := installed romCalls romRows (permissionRows romRows)
    let forged := permissionRows romRows true
    permissionRowsChecked permissions = true ∧
      HintReadFixtures.balanced (permissionLedger writable.interactions) = true ∧
      HintReadFixtures.balanced (permissionLedger (installed permittedCalls rows (permissions.drop 1)).interactions) = false ∧
      HintReadFixtures.balanced (cursorLedger rom.interactions) = true ∧
      HintReadFixtures.balanced (permissionLedger rom.interactions) = false ∧
      HintReadFixtures.balanced (permissionLedger (installed romCalls romRows forged).interactions) = true ∧
      permissionRowsChecked forged = false := by native_decide

private def sourceInputs (calls : List (HostHintReadChip.Inputs Fp))
    (rows : List HintReadFixtures.Row) (nodes : List (NodeRecord Fp)) (records : List (WordRecord Fp))
    (index : ℕ) : List (List Fp) :=
  if index == 85 then nodes.map (fun row => (toElements row).toList)
  else if index == 86 then records.map (fun row => (toElements row).toList)
  else installedInputs calls rows [] index

private def recordSnapshot (actual : List Bytes) : ExecutionSnapshot :=
  { source with host := { source.host with io := { source.host.io with hints := actual } } }

private def sourceAssembly (actual : List Bytes) :=
  HostHintReadLocal.ensemble (p := SP1Prime) image (recordSnapshot actual) HostCallReceivers.available
    (HostHintReadLocal.sourceResources actual) []
    (HostHintReadLocal.source_unique_names image (recordSnapshot actual) actual)

private def withSources (actual : List Bytes) (calls : List (HostHintReadChip.Inputs Fp))
    (rows : List HintReadFixtures.Row) (nodes : List (NodeRecord Fp)) (records : List (WordRecord Fp)) :
    EnsembleWitness (sourceAssembly actual) :=
  buildWitness (sourceAssembly actual) (sourceInputs calls rows nodes records)

private def sourceRowsChecked (actual : List Bytes) (nodes : List (NodeRecord Fp))
    (records : List (WordRecord Fp)) : Bool :=
  nodes.all (fun node => (evaluateProgram
    (HostHintQueue.sourceMain actual (varFromOffset NodeRecord 0)) (toElements node).toList none
    [FiniteLookup.ofStatic (sourceTable actual)]).1) &&
  records.all (fun record => (evaluateProgram
    (HostHintQueue.sourceWordMain actual (varFromOffset WordRecord 0)) (toElements record).toList none
    [FiniteLookup.ofStatic (sourceWordTable actual)]).1)

/-- The installed fixed sources authenticate every handler/consumer request, with duplicate demand
and reversed physical rows. Missing providers fail balance; changing fixed bytes preserves the
claimed ledger but fails the source lookup. Other channels are outside this regression. -/
theorem installedRecords :
    let rows := (calls.flatMap words).reverse
    let nodes := calls.map (·.node)
    let records := calls.map (·.endStep.word) ++ rows.map (fun row => (row.2.step row.1).word)
    let witness := withSources hints calls rows nodes records
    let changed := [[99] ++ (HintReadFixtures.bytes 16).drop 1, HintReadFixtures.bytes 8, []]
    witness.tables.length = 89 ∧ sourceRowsChecked hints nodes records = true ∧
      HintReadFixtures.balanced (recordLedger witness.interactions) = true ∧
      HintReadFixtures.balanced (recordLedger (withSources hints calls rows (nodes.drop 1) records).interactions) = false ∧
      HintReadFixtures.balanced (recordLedger (withSources hints calls rows nodes (records.drop 1)).interactions) = false ∧
      HintReadFixtures.balanced (recordLedger (withSources changed calls rows nodes records).interactions) = true ∧
      sourceRowsChecked changed nodes records = false := by native_decide

/-- Semantic 64-bit agreement does not establish canonical field limbs. -/
theorem noncanonicalNodeLength :
    let node := (call 3 0 1 65536).node
    let forged : NodeRecord Fp := { node with length := node.length.set 3 (node.length[3] + 65536) }
    Word.toBitVec64 forged.length = Word.toBitVec64 node.length ∧
      sourceRowsChecked hints [node] [] = true ∧ sourceRowsChecked hints [forged] [] = false := by native_decide

/-- Future nodes can have identical bytes and valid source records. Complete record balance still
does not authorize their use by an earlier call: its actual cursor ledger rejects the substitution. -/
theorem futureNodeConsumers :
    let earlier := call 3 0 1 65536
    let actual := HintReadFixtures.bytes 16 :: hints
    let rows := (words earlier).map fun row => (row.1, { row.2 with pointer := Address.ofNat 4 })
    let nodes := [earlier.node]
    let records := earlier.endStep.word :: rows.map (fun row => (row.2.step row.1).word)
    node? (ofList hints).1 4 = none ∧
      node? (ofList actual).1 4 = some ⟨HintReadFixtures.bytes 16, 3⟩ ∧
      sourceRowsChecked actual nodes records = true ∧
      HintReadFixtures.balanced (recordLedger (withSources actual [earlier] rows nodes records).interactions) = true ∧
      (consumers rows).all (fun table => (checked (deriveProverData (consumers rows)) table).1) = true ∧
      shared [earlier] (words earlier) = true ∧ shared [earlier] rows = false := by native_decide

private def queueEndpoint (state : HostHintQueue.State Fp) (multiplicity : Fp) : String × List Fp × Fp :=
  ("sp1.native.hint_queue_state", (toElements state).toList, multiplicity)

/-- Active fixed-source fixtures satisfy their record subsystem but lack queue endpoints.
The explicit pair closes only that ledger; forged final heads or reset allocation frontiers fail. -/
theorem missingQueueEndpoints :
    let rows := (calls.flatMap words).reverse
    let nodes := calls.map (·.node)
    let records := calls.map (·.endStep.word) ++ rows.map (fun row => (row.2.step row.1).word)
    let witness := withSources hints calls rows nodes records
    let actual := queueLedger witness.interactions
    let initial := (call 3 0 1 65536).previous
    let final := (call 1 265 (2 ^ 24 + 1) (2 ^ 48 - 8)).next
    sourceRowsChecked hints nodes records = true ∧
      HintReadFixtures.balanced (recordLedger witness.interactions) = true ∧
      HintReadFixtures.balanced actual = false ∧
      HintReadFixtures.balanced (queueEndpoint initial 1 :: queueEndpoint final (-1) :: actual) = true ∧
      HintReadFixtures.balanced (queueEndpoint initial 1 ::
        queueEndpoint { final with head := Address.ofNat 1 } (-1) :: actual) = false ∧
      HintReadFixtures.balanced (queueEndpoint initial 1 ::
        queueEndpoint { final with allocated := Address.ofNat 0 } (-1) :: actual) = false := by native_decide

private def queueAssembly (actual : List Bytes) (final : HostHintQueue.State Fp) :=
  Soundness.HostHintQueueBoundary.ensemble image (recordSnapshot actual) final (recordSnapshot actual).host
    HostCallReceivers.available (HostHintReadLocal.sourceResources actual) []
    (HostHintReadLocal.source_unique_names image (recordSnapshot actual) actual)

private def withQueueBoundary (actual : List Bytes) (final : HostHintQueue.State Fp)
    (calls : List (HostHintReadChip.Inputs Fp)) (rows : List HintReadFixtures.Row)
    (nodes : List (NodeRecord Fp)) (records : List (WordRecord Fp)) :
    EnsembleWitness (queueAssembly actual final) :=
  buildWitness (queueAssembly actual final) (sourceInputs calls rows nodes records)

/-- The actual verifier closes queue balance exactly once. Duplicate handler chains, a forged
final head, and a reset frontier fail; zero-event identities work. Other AIR channels remain
outside this fixture, so this is not yet a full mixed-execution non-vacuity proof. -/
theorem installedQueueEndpoints :
    let rows := (calls.flatMap words).reverse
    let nodes := calls.map (·.node)
    let records := calls.map (·.endStep.word) ++ rows.map (fun row => (row.2.step row.1).word)
    let final := (call 1 265 (2 ^ 24 + 1) (2 ^ 48 - 8)).next
    let witness := withQueueBoundary hints final calls rows nodes records
    let projected := Soundness.HostHintQueueBoundary.projected witness
    let endpoints := queueLedger ((queueAssembly hints final).verifierOperations.interactionValues
      (Environment.fromInput witness.publicInput witness.data))
    witness.tables.length = 89 ∧ projected.tables.length = 89 ∧
      witness.tables.map (·.table) = projected.tables.map (·.table) ∧
      endpoints = [queueEndpoint (SP1Clean.HostHintQueueBoundary.initial hints) 1,
        queueEndpoint final (-1)] ∧
      queueLedger witness.interactions = endpoints ++ queueLedger (physicalInteractions witness.tables) ∧
      HintReadFixtures.balanced (queueLedger witness.interactions) = true ∧
      HintReadFixtures.balanced (queueLedger projected.interactions) = false ∧
      recordLedger witness.interactions = recordLedger projected.interactions ∧
      HintReadFixtures.balanced (queueLedger
        (withQueueBoundary hints final (calls ++ calls) rows nodes records).interactions) = false ∧
      HintReadFixtures.balanced (queueLedger
        (withQueueBoundary hints { final with head := Address.ofNat 1 } calls rows nodes records).interactions) = false ∧
      HintReadFixtures.balanced (queueLedger
        (withQueueBoundary hints { final with allocated := Address.ofNat 0 } calls rows nodes records).interactions) = false ∧
      HintReadFixtures.balanced (queueLedger (withQueueBoundary hints
        (SP1Clean.HostHintQueueBoundary.initial hints) [] [] [] []).interactions) = true := by native_decide

private def lengthCall (head previous now : ℕ) : HostHintLengthChip.Inputs Fp :=
  let store := (ofList hints).1
  let queue := (decode? store head).getD []
  let host : HostState := { io := ⟨queue, []⟩ }
  let context : HostReadContext :=
    ⟨fun index => if index == 5 then some 240
      else if index == 10 || index == 11 then some 0 else none, fun _ => none⟩
  let executed := (host.run ⟨{ readOnly := fun _ => false }, SP1Prime⟩ context).getD
    ⟨.hintLength, 0, 0, 0, ⟨host, none⟩⟩
  HostHintLengthChip.populate store head previous now executed

private def historyTables (forge : Bool) : List (Table Fp) :=
  let lengths := [lengthCall 3 0 1, lengthCall 2 9 273, lengthCall 1 281 545]
  let lengths := if forge then lengths.map fun row =>
      if row.call.clk_low == 273 then
        { row with
          call := { row.call with result := Soundness.Target.bitVecToWord 16 }
          node := { row.node with length := Soundness.Target.bitVecToWord 16 } }
      else row
    else lengths
  [handlers [call 1 545 553 65536, call 2 273 281 65536, call 3 1 9 65536],
   Table.build { circuit := HostHintLengthChip.circuit false } lengths.reverse (fun _ _ => #[]) (ProverHint.empty Fp),
   Table.build { circuit := HostHintLengthChip.circuit true } [lengthCall 0 553 817] (fun _ _ => #[]) (ProverHint.empty Fp)]

private def historyPath (forge : Bool) : List (HostQueueOrder.Row (p := SP1Prime)) :=
  (TransitionView.readIndexedRows HostQueueOrder.indices (historyTables forge)
    (deriveProverData (historyTables forge))).mergeSort
    (fun first second => HostQueueOrder.time (HostQueueOrder.edge first).2 ≤
      HostQueueOrder.time (HostQueueOrder.edge second).2)

/-- A queue-only verifier is evaluated separately from its physical handler tables. -/
private def closedQueueLedger (final : HostHintQueue.State Fp) (tables : List (Table Fp)) : Ledger :=
  let data := deriveProverData tables
  queueLedger ((SP1Clean.HostHintQueueBoundary.closed hints final).operations.interactionValues
    (Environment.fromArray #[] data) ++ tables.flatMap (·.interactions data))

/-- Replay consumes physically decoded observations/pops across both HINT_LEN variants.
A stale length forged in both result and metadata passes local assertions and token balance,
but fails source authentication and semantic replay. These are queue-subsystem fixtures. -/
theorem physicalQueueHistory :
    let final := (lengthCall 0 553 817).next
    let stale := lengthCall 2 9 273
    let forged := { stale.node with length := Soundness.Target.bitVecToWord 16 }
    (historyTables false).all (fun table => (checked (deriveProverData (historyTables false)) table).1) = true ∧
      (historyTables true).all (fun table => (checked (deriveProverData (historyTables true)) table).1) = true ∧
      HintReadFixtures.balanced (closedQueueLedger final (historyTables false)) = true ∧
      HintReadFixtures.balanced (closedQueueLedger final (historyTables true)) = true ∧
      sourceRowsChecked hints [stale.node] [] = true ∧ sourceRowsChecked hints [forged] [] = false ∧
      (historyPath false).length = 7 ∧
      HintQueue.replay? ((historyPath false).map HostQueueHistory.event) hints = some [] ∧
      HintQueue.replay? ((historyPath true).map HostQueueHistory.event) hints = none := by native_decide

/-- Byte replay supports new allocations and distinguishes an empty hint from an empty queue. -/
theorem queueReplayPrepends :
    HintQueue.replay? [.prepend [[99]], .length 1, .read 1, .length 16] hints = some hints ∧
      HintQueue.replay? [.prepend [[]], .length 0, .read 0, .length 16] hints = some hints ∧
      HintQueue.replay? [.length (BitVec.allOnes 64)] [] = some [] ∧
      HintQueue.replay? [.length 0] [] = none ∧
      HintQueue.replay? [.read 0] [] = none := by native_decide

private def cpuTime (index : ℕ) : ℕ := 2 ^ 24 - 263 + 264 * index

private def cpuQueueTables : List (Table Fp) :=
  [handlers [call 1 (cpuTime 6) (cpuTime 7) 65536,
      call 2 (cpuTime 3) (cpuTime 5) 65536, call 3 (cpuTime 0) (cpuTime 2) 65536],
   Table.build { circuit := HostHintLengthChip.circuit false }
     [lengthCall 1 (cpuTime 5) (cpuTime 6), lengthCall 2 (cpuTime 2) (cpuTime 3), lengthCall 3 0 (cpuTime 0)]
     (fun _ _ => #[]) (ProverHint.empty Fp),
   Table.build { circuit := HostHintLengthChip.circuit true } [lengthCall 0 (cpuTime 7) (cpuTime 8)]
     (fun _ _ => #[]) (ProverHint.empty Fp)]

private def cpuQueuePath : List (HostQueueOrder.Row (p := SP1Prime)) :=
  (TransitionView.readIndexedRows HostQueueOrder.indices cpuQueueTables (deriveProverData cpuQueueTables)).mergeSort
    (fun first second => HostQueueCPUOrder.eventTime first ≤ HostQueueCPUOrder.eventTime second)

private def enterCall (index : ℕ) : HostCallChip.Message Fp :=
  ⟨(cpuTime index / 2 ^ 24 : ℕ), (cpuTime index % 2 ^ 24 : ℕ), #v[3, 0, 0, 0], 0, 0, 0, 0⟩

private def queueInstruction (message : HostCallChip.Message Fp) : HostCallChip.Inputs Fp :=
  let code := message.code[0]
  let input : SyscallInstrsChip.Inputs Fp :=
    { state := ⟨message.clk_high, (message.clk_low.val / 65536 : ℕ),
        (message.clk_low.val % 65536 : ℕ), #v[0, 1, 0]⟩
      op_a := 5, op_a_memory := ⟨message.code, ⟨0, ((message.clk_low.val + 3) % 65536 : ℕ)⟩⟩, op_a_0 := 0
      op_b := 10, op_b_memory := ⟨message.arg1, ⟨0, ((message.clk_low.val + 2) % 65536 : ℕ)⟩⟩
      op_c := 11, op_c_memory := ⟨message.arg2, ⟨0, ((message.clk_low.val + 1) % 65536 : ℕ)⟩⟩
      next_pc := #v[4, 1, 0], is_halt := 0, op_a_value := message.result
      syscall_id_bytes := U16toU8OperationSafe.populate message.code
      is_enter_unconstrained := IsZeroOperation.populate (code - 3)
      is_hint_len := IsZeroOperation.populate (code - 240), is_halt_zero := IsZeroOperation.populate code
      is_commit := IsZeroOperation.populate (code - 16), is_commit_deferred := IsZeroOperation.populate (code - 26)
      digest_index_bits := 0, digest_word := 0, op_b_cmp := ⟨1⟩, op_c_cmp := ⟨1⟩, is_real := 1 }
  HostCallChip.populate input 0 0

private def cpuCalls : List (HostCallChip.Message Fp) :=
  ((cpuQueuePath.map HostQueueCPUOrder.call) ++ [enterCall 1, enterCall 4]).mergeSort
    (fun first second => Semantics.clkNat first.clk_high first.clk_low ≤
      Semantics.clkNat second.clk_high second.clk_low)

private def cpuInstructions (messages : List (HostCallChip.Message Fp)) : Table Fp :=
  let padding := queueInstruction (enterCall 1)
  let padding := { padding with instruction := { padding.instruction with is_real := 0 } }
  Table.build HostCallLedger.producer (padding :: (messages.map queueInstruction).reverse ++ [padding])
    (fun _ _ => #[]) (ProverHint.empty Fp)

private def cpuHandoff (messages : List (HostCallChip.Message Fp)) : Bool :=
  let enters := Table.build { circuit := HostEnterChip.circuit } [enterCall 4, enterCall 1]
    (fun _ _ => #[]) (ProverHint.empty Fp)
  HintReadFixtures.balanced (callLedger (physicalInteractions (cpuInstructions messages :: enters :: cpuQueueTables)))

/-- The physical wrapper handoff agrees with queue chronology despite reversed tables, padding,
two intervening ENTER calls, and a 24-bit clock carry. Equal clocks do not permit changing a
complete call. This fixture checks handoff/queue protocols, not complete CPU/Memory balance. -/
theorem queueCPUHandoff :
    let decoded := HostCallLedger.calls (cpuInstructions cpuCalls) (deriveProverData [cpuInstructions cpuCalls])
    let stamps := decoded.reverse.map (fun message => Semantics.clkNat message.clk_high message.clk_low)
    let queueStamps := cpuQueuePath.map HostQueueCPUOrder.eventTime
    let changed := cpuCalls.map fun message => if message.code[0] == 240 then
      { message with result := Soundness.Target.bitVecToWord 99 } else message
    let final := (lengthCall 0 (cpuTime 7) (cpuTime 8)).next
    let physicalCalls := callLedger (physicalInteractions [cpuInstructions cpuCalls])
    (cpuInstructions cpuCalls).table.length = 11 ∧ decoded.length = 9 ∧
      physicalCalls.length = 11 ∧ (physicalCalls.filter (fun entry => entry.2.2 == 0)).length = 2 ∧
      stamps = (List.range 9).map cpuTime ∧
      queueStamps = [0, 2, 3, 5, 6, 7, 8].map cpuTime ∧
      decide (queueStamps.Sublist stamps) = true ∧
      (cpuCalls.map queueInstruction).all (fun row => (evaluateProgram
        (HostCallChip.main (varFromOffset HostCallChip.Inputs 0)) (toElements row).toList).1) = true ∧
      cpuQueueTables.all (fun table => (checked (deriveProverData cpuQueueTables) table).1) = true ∧
      HintReadFixtures.balanced (closedQueueLedger final cpuQueueTables) = true ∧
      cpuHandoff cpuCalls = true ∧ cpuHandoff changed = false ∧
      HintQueue.replay? ((cpuQueuePath.filter (fun row => HostQueueCPUOrder.eventTime row < cpuTime 3)).map
        HostQueueHistory.event) hints = some (hints.drop 1) ∧
      HintQueue.replay? (cpuQueuePath.map HostQueueHistory.event) hints = some [] := by native_decide

/-- The shared semantic decoder retains every physical queue action and erases the two ENTERs.
This strengthens the handoff fixture with event contents; it still does not claim full Memory balance. -/
theorem queueCPUProjection :
    let instructions := cpuInstructions cpuCalls
    let rows := (HostCallLedger.activeRows instructions (deriveProverData [instructions])).reverse.map fun env =>
      NativeCore.ExecutionRow.syscall (HostCallLedger.input env).instruction
    let events := rows.map NativeCore.ExecutionRow.event
    events.filterMap queueEvent? = cpuQueuePath.map HostQueueHistory.event ∧
      events.all (fun event => match event with
        | .ordinary => true
        | .syscall call => call.rawCode != SyscallKind.write.code) = true ∧
      HintQueue.replay? (events.filterMap queueEvent?) hints = some [] := by
  simp only [List.map_map, Function.comp_def, NativeCore.ExecutionRow.event, syscallEventOfRow]
  native_decide

private def callWords (physical : List (HintReadCoverage.Row (p := SP1Prime)))
    (env : Environment Fp) : List (HintReadCoverage.Row (p := SP1Prime)) :=
  physical.filter (fun row => decide (HostHintReadCPU.wordClock row =
    ((HostCallLedger.call env).clk_high, (HostCallLedger.call env).clk_low)))

private theorem callWords_eq (data : ProverData Fp) (physical : List (HintReadCoverage.Row (p := SP1Prime)))
    (env : Environment Fp) :
    HostHintReadCPU.wordsAt data physical
      (.syscall (HostCallLedger.input env).instruction) = callWords physical env := rfl

/-- CPU grouping retains final padding through reversed physical tables and a clock carry.
Duplicating the word inventory doubles every group's count and exposes duplicate locations;
selection itself must never erase those occurrences. The fixture remains a protocol test. -/
theorem cpuWordGrouping :
    let instructions := cpuInstructions cpuCalls
    let rows := (HostCallLedger.activeRows instructions (deriveProverData [instructions])).reverse.map fun env =>
      NativeCore.ExecutionRow.syscall (HostCallLedger.input env).instruction
    let table := consumers (([call 3 (cpuTime 0) (cpuTime 2) 65536,
      call 2 (cpuTime 3) (cpuTime 5) 65536, call 1 (cpuTime 6) (cpuTime 7) 65536].flatMap words).reverse)
    let data := deriveProverData table
    let physical := TransitionView.readIndexedRows HintReadCoverage.variants table data
    let groups := rows.map (HostHintReadCPU.wordsAt data physical)
    let duplicates := rows.map (HostHintReadCPU.wordsAt data (physical ++ physical))
    groups.map List.length = [0, 0, 3, 0, 0, 2, 0, 1, 0] ∧
      groups.all (fun group => decide ((group.map (fun row => (HintReadWrites.produced row).1)).Nodup)) = true ∧
      duplicates.map List.length = [0, 0, 6, 0, 0, 4, 0, 2, 0] ∧
      duplicates.all (fun group => decide ((group.map (fun row => (HintReadWrites.produced row).1)).Nodup)) = false := by
  simp only [List.map_map, Function.comp_def, callWords_eq]
  native_decide

end SP1CleanTest.Core.HostHintReadPartition
