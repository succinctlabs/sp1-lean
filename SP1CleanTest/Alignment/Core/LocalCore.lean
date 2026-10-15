import SP1Clean.Soundness.LocalCoreGrounding
import SP1Clean.Soundness.ProtectedLocalCore
import SP1Clean.Soundness.ProtectedOrdinaryReceipt
import SP1Clean.Soundness.HostHintQueueBoundary
import SP1Clean.Proofs.Chips.HostCommitChip.Populate
import SP1Clean.Model.Core.HostSnapshot
import SP1Clean.Model.Core.InstructionWrite
import SP1CleanTest.Alignment.Support.LocalCoreFixture
import ToClean.Air.FiniteLookup
import Clean.Circuit.WitnessExport

/-! # Complete local-assembly constraint and ledger regression

The fixture starts at clock 9 with nonzero source registers and executes ADD. Rows are interpreted
at their actual indices in the 61-table local assembly. All assertions, fixed lookups, public
verifier interactions, channel membership, count bounds, and full-message balances are checked.
Byte/Range demands are closed by executing the actual provider circuits. An active HINT_LEN fixture
checks the wide syscall edge and all three Memory pairs, and records the unclosed host-result
binding with a concrete forged-return example. Same-register accesses and a real State clock carry
exercise the grounding interfaces; stopped-source rows are rejected while identities remain valid.
This is AIR conformance, not an execution theorem.
-/

namespace SP1CleanTest.Core.LocalCore

open Circuit Air.Flat SP1Clean SP1Clean.Model.Core SP1Clean.Soundness SP1Clean.Soundness.Target

private abbrev Fp := ZMod SP1Prime
private abbrev Row := ℕ × List Fp
private abbrev Ledger := List (String × List Fp × Fp)

open Fixture

private def evaluateRow (image : ProgramImage) (source : ExecutionSnapshot) (row : Row)
    (guarded : Bool := false) : Bool × Ledger :=
  let tables := if guarded then Soundness.ProtectedLocalCore.tables image source
    else Soundness.LocalCore.tables image source
  match tables[row.1]? with
  | none => (false, [])
  | some component =>
    let result := evaluate image source component row.2
    (component.fixedColumns.isNone && result.1, result.2)

private def check (image : ProgramImage) (source : ExecutionSnapshot) (pi : SP1PublicIO Fp) (rows : List Row)
    (guarded : Bool := false) : Bool :=
  let assembly := if guarded then Soundness.ProtectedLocalCore.ensemble (p := SP1Prime) image source
    else Soundness.LocalCore.ensemble image source
  let head := (true, assembly.verifierOperations.interactionValues
    (Environment.fromInput pi (fun _ _ => #[])) |>.map fun interaction =>
      (interaction.channel.name, interaction.msg.toList, interaction.mult))
  let initial := head :: rows.map (fun row => evaluateRow image source row guarded)
  let demands := (initial.flatMap Prod.snd).filterMap byteProvider
  let evaluated := initial ++ demands.map (fun row => evaluateRow image source row guarded)
  let consumers := evaluated.flatMap Prod.snd
  let ledger := consumers ++ StaticMembership.providerLedger source.sail.memorySnapshot.registerTable consumers ++
    StaticMembership.providerLedger
      (InitialMemoryLookup.membership source.sail.memory (2 ^ 48) "sp1.native.initial_memory") consumers
  evaluated.all Prod.fst && decide (ledger.length < SP1Prime) &&
    ledger.all fun (name, message, _) =>
      (assembly.channels.map RawChannel.name).contains name &&
        ((ledger.filter (fun entry => entry.1 == name && entry.2.1 == message)).map
          (fun entry => entry.2.2)).sum == 0

/-- info: exportable ✓ (0 witness cells) -/
#guard_msgs in
#assert_exportable (Soundness.LocalCore.verifier (p := SP1Prime) image source)

/-- The full local fixture has an active instruction, nonzero incoming registers, and no boot clock. -/
theorem activeLocalShard : check image source publicInput baseRows = true := by native_decide

/-- State endpoints are bound to the physical instruction ledger, not chosen independently. -/
theorem rejectsWrongEndpoints :
    [check image source { publicInput with init_clk_0_16 := 1 } baseRows,
     check image source { publicInput with final_clk_0_16 := 18 } baseRows,
     check image source { publicInput with final_pc0 := 8 } baseRows] = [false, false, false] := by native_decide

/-- Changing fixed incoming values or removing a register invalidates this physical witness. -/
theorem rejectsWrongSource :
    [check image { source with sail.registers := source.sail.registers.insert .x2 101 } publicInput baseRows,
     check image { source with sail.registers := source.sail.registers.erase .x2 } publicInput baseRows,
     check image { source with sail.memory := source.sail.memory.write 65536 0 } publicInput baseRows] =
      [false, false, false] := by native_decide

/-- The source's actual PC and clock cannot differ from the public incoming token. -/
theorem rejectsUnboundSource :
    [check image { source with clock := 10 } publicInput baseRows,
     check image { source with sail.registers := source.sail.registers.insert .PC 65540 } publicInput baseRows,
     check image { source with clock := 2 ^ 48 + 9 } publicInput baseRows,
     check image { source with sail.registers := source.sail.registers.insert .PC (2 ^ 48 + 65536) }
       publicInput baseRows] = [false, false, false, false] := by native_decide

/-- Platform configuration is checked even when the affected register is untouched by the row. -/
theorem rejectsInvalidPlatform :
    [check image { source with sail.registers := source.sail.registers.insert .misa 0 } publicInput baseRows,
     check image { source with sail.registers := source.sail.registers.insert .misa 4100 } publicInput baseRows,
     check image { source with sail.registers := source.sail.registers.insert .mstatus 8 } publicInput baseRows,
     check image { source with sail.registers := source.sail.registers.erase .pma_regions } publicInput baseRows] =
      [false, false, false, false] := by native_decide

/-- ROM agreement is enforced even when no source/final RAM row reads the changed code byte. -/
theorem checksUntouchedRom :
    check image source publicInput withoutRam = true ∧
      check image { source with sail.memory := source.sail.memory.write 65536 0 } publicInput withoutRam = false := by
  native_decide

/-- Missing or duplicate source records fail the actual Memory/order balances. -/
theorem rejectsBrokenInventory :
    [check image source publicInput (baseRows.drop 1),
     check image source publicInput (sourceRegister 0 1 :: baseRows),
     check image source publicInput (baseRows.filter (fun row => row.1 != 2)),
     check image source publicInput (baseRows.filter (fun row => row.1 != 4))] =
      [false, false, false, false] := by native_decide

/-- A forged final value cannot be hidden by keeping the same canonical address and clock. -/
theorem rejectsWrongFinalValue :
    check image source publicInput (baseRows.set 5 (3, finalRecord 0 1 13 124)) = false := by native_decide

/-- Fetch authentication rejects a missing ROM producer and an altered fixed lookup key. -/
theorem rejectsUnauthenticatedFetch :
    [check image source publicInput (baseRows.filter (fun row => row.1 != 6)),
     check image source publicInput (baseRows.set 10 (6, programRow.2.set 0 4))] =
      [false, false] := by native_decide

private def twoImage : ProgramImage := ⟨[(65536, 0x003100b3), (65540, 0x003100b3)], 65536, []⟩

private def twoSource : ExecutionSnapshot := { source with sail.memory := twoImage.initialMemory }

private def secondAdd : Row := (7, TraceGenTests.rTypeEventInputs
  { Audit.OneAddNativePremises.event with
    clk := 17, pc := 65540, tsA := 21, prevTsA := 13, prevA := 123,
    tsB := 20, prevTsB := 12, tsC := 19, prevTsC := 11 })

private def paddingAdd : Row := (7, List.replicate (size AddChip.Inputs) 0)

private def twoPublic : SP1PublicIO Fp :=
  { publicInput with final_clk_0_16 := 25, final_pc0 := 8 }

private def twoRows : List Row :=
  [sourceRegister 0 1, sourceRegister 2 2, sourceRegister 3 3, terminal 2 4,
    (3, finalRecord 0 1 21 123), (3, finalRecord 2 2 20 100), (3, finalRecord 3 3 19 23), terminal 5 4,
    programRow, (6, ((DecodedProgramProvider.populate? (p := SP1Prime) twoImage (65540, 0x003100b3) 1).map
      (fun input => (toElements input).toList)).getD []),
    secondAdd, paddingAdd, (7, Audit.OneAddNativePremises.inputs),
    (57, List.replicate (size HaltChip.Inputs) 0)]

/-- The physical ADD rows are reversed, with padding between them; the ledger still closes
for the two-step local segment. Duplicating an active occurrence invalidates it. -/
theorem acceptsReorderedPaddedSegment :
    check twoImage twoSource twoPublic twoRows = true ∧
      check twoImage twoSource twoPublic (secondAdd :: twoRows) = false := by native_decide

private def identityPublic : SP1PublicIO Fp :=
  { publicInput with final_clk_0_16 := 9, final_pc0 := 0 }

private def identityRows : List Row :=
  [terminal 2 0, terminal 5 0, paddingAdd, (57, List.replicate (size HaltChip.Inputs) 0)]

/-- A zero-step segment has equal State endpoints and empty touched inventories. The same
identity is accepted for a stopped host; this does not permit a semantic step after HALT. -/
theorem acceptsEmptySegments :
    check image source identityPublic identityRows = true ∧
      check image { source with host.exitCode := some 0 } identityPublic identityRows = true := by native_decide

private def aliasImage : ProgramImage := ⟨[(65536, 0x001080b3)], 65536, []⟩

private def aliasSource : ExecutionSnapshot :=
  { source with
    sail.registers := source.sail.registers.insert .x1 100
    sail.memory := aliasImage.initialMemory }

private def aliasEvent : TraceGenTests.AluEventRec :=
  { Audit.OneAddNativePremises.event with
    a := 200, c := 100, opB := 1, opC := 1, prevA := 100, prevTsA := 12, prevTsB := 11 }

private def aliasRows : List Row :=
  [(0, (toElements (OrderedSnapshotProvider.populate
    (SnapshotRegisterProvider.populate aliasSource.sail.memorySnapshot 1#5) 0 1)).toList), terminal 2 2,
    (3, finalRecord 0 1 13 200), terminal 5 2,
    (6, ((DecodedProgramProvider.populate? (p := SP1Prime) aliasImage (65536, 0x001080b3) 1).map
      (fun input => (toElements input).toList)).getD []),
    (7, TraceGenTests.rTypeEventInputs aliasEvent), (57, List.replicate (size HaltChip.Inputs) 0)]

/-- ADD x1,x1,x1 uses one source/final location and three consecutive touches within the row.
Skipping either intermediate prior record breaks the complete physical Memory ledger. -/
theorem acceptsSameRegisterTouches :
    check aliasImage aliasSource publicInput aliasRows = true ∧
      check aliasImage aliasSource publicInput
        (aliasRows.set 5 (7, TraceGenTests.rTypeEventInputs { aliasEvent with prevTsA := 0 })) = false ∧
      check aliasImage aliasSource publicInput
        (aliasRows.set 5 (7, TraceGenTests.rTypeEventInputs { aliasEvent with prevTsB := 0 })) = false := by
  native_decide

private def clockEvent (clock : ℕ) : TraceGenTests.AluEventRec :=
  { Audit.OneAddNativePremises.event with clk := clock, tsA := clock + 4, tsB := clock + 3, tsC := clock + 2 }

private def clockPublic (clock : ℕ) : SP1PublicIO Fp :=
  { publicInput with
    init_clk_0_16 := (clock % 65536 : ℕ)
    init_clk_16_24 := (clock / 65536 % 256 : ℕ)
    final_clk_0_16 := ((clock + 8) % 65536 : ℕ)
    final_clk_16_24 := ((clock + 8) / 65536 % 256 : ℕ)
    final_clk_24_32 := ((clock + 8) / 2 ^ 24 : ℕ) }

private def clockRows (clock : ℕ) : List Row :=
  [sourceRegister 0 1, sourceRegister 2 2, sourceRegister 3 3, terminal 2 4,
    (3, finalRecord 0 1 (clock + 4) 123), (3, finalRecord 2 2 (clock + 3) 100),
    (3, finalRecord 3 3 (clock + 2) 23), terminal 5 4, programRow,
    (7, TraceGenTests.rTypeEventInputs (clockEvent clock)), (57, List.replicate (size HaltChip.Inputs) 0)]

private def clockCarry : Row := (56, (toElements ({
    next_clk_32_48 := 0, next_clk_24_32 := 1, next_clk_16_24 := 0, next_clk_0_16 := 1,
    clk_high := 0, clk_low := 2 ^ 24 + 1, next_pc0 := 4, next_pc1 := 1, next_pc2 := 0,
    pc0 := 4, pc1 := 1, pc2 := 0, is_clk := 1, is_real := 1 } : StateBumpChip.Inputs Fp)).toList)

/-- A row crossing the 24-bit epoch needs the actual StateBump link to its canonical public end.
The three Memory touches still precede the carry and preserve their original timestamps. -/
theorem acceptsStateClockCarry :
    let clock := 2 ^ 24 - 7
    check image { source with clock := clock } (clockPublic clock) (clockCarry :: clockRows clock) = true ∧
      check image { source with clock := clock } (clockPublic clock) (clockRows clock) = false := by
  native_decide

/-- Source validation checks clock range, while active CPU rows additionally require SP1's
1-mod-8 clock phase. Shared semantic compiler bounds must account for this profile condition. -/
theorem clockPhaseNeedsProfile :
    checkExecutionSource image { source with clock := 10 } = true ∧
      check image { source with clock := 10 } (clockPublic 10) (clockRows 10) = false := by
  native_decide

/-- The stopped-source clock constraints reject this formerly accepted active ADD. Empty
segments at stopped sources remain valid, as checked by `acceptsEmptySegments`. -/
theorem rejectsActiveRowsAfterHalt :
    check image { source with host.exitCode := some 0 } publicInput baseRows = false := by native_decide

private def syscallImage : ProgramImage := ⟨[(65536, 0x00000073)], 65536, []⟩

private def syscallProgram : GuestProgram := syscallImage.toGuestProgram (by decide)

private def syscallPolicy : HostPolicy :=
  ⟨⟨fun address => decide (65536 ≤ address ∧ address < 65540), 65536, 2 ^ 48⟩, SP1Prime⟩

private def syscallSource : ExecutionSnapshot where
  sail := { registers := (((configuredState 65536).regs.insert .x5 240).insert .x10 7).insert .x11 9
            memory := syscallImage.initialMemory }
  host := { io := ⟨[[1, 2, 3]], []⟩ }
  clock := 9

private def syscallInput (result : ℕ) : SyscallInstrsChip.Inputs Fp :=
  { state := ⟨0, 0, 9, #v[0, 1, 0]⟩
    op_a := 5, op_a_memory := ⟨word 240, ⟨0, 12⟩⟩, op_a_0 := 0
    op_b := 10, op_b_memory := ⟨word 7, ⟨0, 11⟩⟩
    op_c := 11, op_c_memory := ⟨word 9, ⟨0, 10⟩⟩
    next_pc := #v[4, 1, 0], is_halt := 0
    op_a_value := word result, syscall_id_bytes := U16toU8OperationSafe.populate (word 240)
    is_enter_unconstrained := IsZeroOperation.populate (237 : Fp)
    is_hint_len := IsZeroOperation.populate (0 : Fp)
    is_halt_zero := IsZeroOperation.populate (240 : Fp)
    is_commit := IsZeroOperation.populate (224 : Fp)
    is_commit_deferred := IsZeroOperation.populate (214 : Fp)
    digest_index_bits := Vector.replicate 8 0, digest_word := 0
    op_b_cmp := ⟨1⟩, op_c_cmp := ⟨1⟩, is_real := 1 }

private def syscallRows (result : ℕ) : List Row :=
  let sourceRow (previous index : ℕ) : Row :=
    (0, (toElements (OrderedSnapshotProvider.populate
      (SnapshotRegisterProvider.populate syscallSource.sail.memorySnapshot (BitVec.ofNat 5 index))
      previous index)).toList)
  [sourceRow 0 5, sourceRow 6 10, sourceRow 11 11, terminal 2 12,
    (3, finalRecord 0 5 13 result), (3, finalRecord 6 10 12 7), (3, finalRecord 11 11 11 9), terminal 5 12,
    (6, ((DecodedProgramProvider.populate? (p := SP1Prime) syscallImage (65536, 0x00000073) 1).map
      (fun input => (toElements input).toList)).getD []),
    (57, List.replicate (size HaltChip.Inputs) 0), (58, (toElements (syscallInput result)).toList)]

private def syscallPublic : SP1PublicIO Fp := { publicInput with final_clk_0_16 := 273 }

private def commitSource : ExecutionSnapshot :=
  { syscallSource with
    sail.registers := (((syscallSource.sail.registers.insert .x5 16).insert .x10 0).insert .x11 65537).insert .x20 907
    sail.memory := ((syscallSource.sail.memory.write 8 19).write 80000 42).write (2 ^ 48 - 1) 55
    host := {
      committed := #v[11, 22, 33, 44, 55, 66, 77, 88],
      deferred := #v[101, 102, 103, 104, 105, 106, 107, 108],
      io.publicOutput := [41, 42], stdout := [11, 12], stderr := [13],
      requests := [.hook ⟨15, [7]⟩], replies := [⟨⟨16, [5]⟩, [[6]]⟩] } }

private def commitTarget : HostState :=
  { commitSource.host with committed := commitSource.host.committed.set 0 65537 }

private def commitInstruction : HostCallChip.Inputs Fp :=
  ⟨{ syscallInput 16 with
      op_a_memory.prev_value := word 16, op_b_memory.prev_value := word 0,
      op_c_memory.prev_value := word 65537,
      syscall_id_bytes := U16toU8OperationSafe.populate (word 16),
      is_enter_unconstrained := IsZeroOperation.populate (13 : Fp),
      is_hint_len := IsZeroOperation.populate (-224 : Fp),
      is_halt_zero := IsZeroOperation.populate (16 : Fp),
      is_commit := IsZeroOperation.populate (0 : Fp),
      is_commit_deferred := IsZeroOperation.populate (-10 : Fp),
      digest_index_bits := #v[1, 0, 0, 0, 0, 0, 0, 0], digest_word := #v[1, 0, 1, 0] },
    ⟨0, ⟨0, 0⟩⟩⟩

private def commitHandler : HostCommitChip.Inputs Fp :=
  HostCommitChip.populate false (commitInstruction.message 0)
    (HostCommitBoundary.start (HostCommitEnsemble.sourceValues false commitSource.host))

private def commitRows : List Row :=
  let sourceRow (previous index : ℕ) : Row :=
    (0, (toElements (OrderedSnapshotProvider.populate
      (SnapshotRegisterProvider.populate commitSource.sail.memorySnapshot (BitVec.ofNat 5 index))
      previous index)).toList)
  [sourceRow 0 5, sourceRow 6 10, sourceRow 11 11, terminal 2 12,
    (3, finalRecord 0 5 13 16), (3, finalRecord 6 10 12 0),
    (3, finalRecord 11 11 11 65537), terminal 5 12,
    (6, ((DecodedProgramProvider.populate? (p := SP1Prime) syscallImage (65536, 0x00000073) 1).map
      (fun input => (toElements input).toList)).getD []),
    (57, List.replicate (size HaltChip.Inputs) 0),
    (58, (toElements commitInstruction).toList), (65, (toElements commitHandler).toList),
    (87, (toElements (commitHandler.next 0)).toList),
    (88, (toElements (HostCommitBoundary.start
      (HostCommitEnsemble.sourceValues true commitSource.host))).toList)]

/-- Separate Memory balance only to identify the cause of a negative fixture. Full acceptance
below requires both checks. The first still checks every constraint, lookup and other channel. -/
private def installedChecks (source : ExecutionSnapshot) (input : SP1PublicIO Fp)
    (target : HostState) (rows : List Row) : Bool × Bool :=
  let assembly := HostHintQueueBoundary.ensemble (p := SP1Prime) syscallImage source
    (SP1Clean.HostHintQueueBoundary.initial source.host.io.hints) target HostCallReceivers.available
    (HostHintReadLocal.sourceResources source.host.io.hints) []
    (HostHintReadLocal.source_unique_names syscallImage source source.host.io.hints)
  let evaluateAt (row : Row) := match assembly.tables[row.1]? with
    | none => (false, [])
    | some component =>
      let result := evaluate syscallImage source component row.2
      (component.fixedColumns.isNone && result.1, result.2)
  let head := (true, assembly.verifierOperations.interactionValues
    (Environment.fromInput input (fun _ _ => #[])) |>.map fun interaction =>
      (interaction.channel.name, interaction.msg.toList, interaction.mult))
  let initial := head :: rows.map evaluateAt
  let demands := (initial.flatMap Prod.snd).filterMap byteProvider
  let evaluated := initial ++ demands.map evaluateAt
  let consumers := evaluated.flatMap Prod.snd
  let ledger := consumers ++ StaticMembership.providerLedger source.sail.memorySnapshot.registerTable consumers ++
    StaticMembership.providerLedger
      (InitialMemoryLookup.membership source.sail.memory (2 ^ 48) "sp1.native.initial_memory") consumers
  let balanced (entry : String × List Fp × Fp) :=
    ((ledger.filter (fun other => other.1 == entry.1 && other.2.1 == entry.2.1)).map
      (fun other => other.2.2)).sum == 0
  (evaluated.all Prod.fst && decide (ledger.length < SP1Prime) &&
    ledger.all (fun entry => (assembly.channels.map RawChannel.name).contains entry.1 &&
      (entry.1 == "SP1Memory" || balanced entry)),
    ledger.all (fun entry => entry.1 != "SP1Memory" || balanced entry))

private def commitChecks (target : HostState) (rows : List Row) : Bool × Bool :=
  installedChecks commitSource syscallPublic target rows

private def checkCommit (target : HostState) (rows : List Row) : Bool :=
  let checked := commitChecks target rows
  checked.1 && checked.2

/-- An active COMMIT closes the complete installed ledger from nonzero incoming banks,
including the actual CPU handoff, register Memory pairs, both terminals, and every Byte provider. -/
theorem activeCommitLocalShard : checkCommit commitTarget commitRows = true := by native_decide

/-- Untouched source values need no Memory rows, even below the RAM bus window and at its upper
edge. Removing a touched final record still fails after repairing the boundary ordering chain. -/
theorem untouchedCommitMemory :
    ((commitSource.hostStep? syscallPolicy syscallProgram).map (fun result =>
      (result.1.sail.registers.get? LeanRV64D.Defs.Register.x20,
        result.1.sail.memory.read 8, result.1.sail.memory.read 80000,
        result.1.sail.memory.read (2 ^ 48 - 1)))) = some (some 907, 19, 42, 55) ∧
    commitChecks commitTarget (commitRows.take 6 ++ [terminal 5 11] ++ commitRows.drop 8) = (true, false) := by
  native_decide

/-- Complete balance rejects changed outgoing words in either bank and missing or duplicate terminals. -/
theorem rejectsCommitBoundaries :
    [checkCommit commitSource.host commitRows,
     checkCommit { commitTarget with deferred := commitTarget.deferred.set 0 0 } commitRows,
     checkCommit commitTarget (commitRows.filter (fun row => row.1 != 87)),
     checkCommit commitTarget (commitRows.filter (fun row => row.1 != 88)),
     checkCommit commitTarget (commitRows ++ commitRows.filter (fun row => row.1 == 87))] =
      [false, false, false, false, false] := by native_decide

/-- The installed interaction-only public verifier contains no native witness closure. -/
theorem installedVerifier_exportable :
    Witgen.unexportableWitnesses ((HostHintQueueBoundary.ensemble (p := SP1Prime) syscallImage commitSource
      (SP1Clean.HostHintQueueBoundary.initial []) commitTarget HostCallReceivers.available
      (HostHintReadLocal.sourceResources []) []
      (HostHintReadLocal.source_unique_names syscallImage commitSource [])).verifierOperations.toFlat) = [] := by
  native_decide

/-- info: exportable ✓ (0 witness cells) -/
#guard_msgs in
#assert_exportable (HaltPaddingChip.circuit (p := SP1Prime))

/-- An active ECALL closes the actual 61-table ledger with all three nonzero source registers,
its wide State edge, the changed result, and source/final inventories. No syscall row is erased. -/
theorem activeSyscallLocalShard :
    check syscallImage syscallSource syscallPublic (syscallRows 3) = true := by native_decide

/-- Missing, duplicated, stale, or corrupted syscall read-back records fail complete AIR checks. -/
theorem rejectsBrokenSyscallLedger :
    [check syscallImage syscallSource syscallPublic ((syscallRows 3).drop 1),
     check syscallImage syscallSource syscallPublic ((syscallRows 3).set 4 (3, finalRecord 0 5 13 4)),
     check syscallImage syscallSource syscallPublic ((syscallRows 3).set 5 (3, finalRecord 6 10 11 7)),
     check syscallImage syscallSource syscallPublic ((syscallRows 3).set 6 (3, finalRecord 11 11 11 8)),
     check syscallImage syscallSource syscallPublic ((syscallRows 3) ++ [(58, (toElements (syscallInput 3)).toList)])] =
      [false, false, false, false, false] := by native_decide

private def epochRows (epoch : ℕ) : List Row :=
  let refresh (index value : ℕ) : Row :=
    let input : MemoryBumpChip.Inputs Fp :=
      { access := ⟨word value, ⟨0, 0, 0, ((epoch - 1) % 65536 : ℕ), ((epoch - 1) / 65536 : ℕ)⟩⟩
        addr := index, clk_0_16 := 0, clk_16_24 := 0, clk_24_32 := (epoch % 256 : ℕ)
        clk_32_48 := (epoch / 256 : ℕ), is_real := 1 }
    (55, (toElements input).toList)
  let input := { syscallInput 3 with state.clk_high := (epoch : Fp) }
  ((((syscallRows 3).set 4 (3, finalRecord 0 5 13 3 epoch)).set 5 (3, finalRecord 6 10 12 7 epoch)).set
    6 (3, finalRecord 11 11 11 9 epoch)).set 10 (58, (toElements input).toList) ++
      [refresh 5 240, refresh 10 7, refresh 11 9]

/-- One refresh per touched register reaches the incoming epoch, even at the largest 24-bit
high clock. The continuation does not need rows for all preceding clock epochs. -/
theorem acceptsDistantSourceEpochs : [1, 2 ^ 24 - 1].all (fun epoch =>
    check syscallImage { syscallSource with clock := epoch * 2 ^ 24 + 9 }
      { syscallPublic with
        init_clk_24_32 := (epoch % 256 : ℕ), init_clk_32_48 := (epoch / 256 : ℕ)
        final_clk_24_32 := (epoch % 256 : ℕ), final_clk_32_48 := (epoch / 256 : ℕ) }
      (epochRows epoch)) = true := by native_decide

/-- Recorded integration gap: matching a forged HINT_LEN return on both the instruction and final
record still satisfies this AIR, although finite host execution returns three. Host binding must
close this before any local execution-equivalence theorem is claimed. -/
theorem hintReturnNeedsHostBinding :
    check syscallImage syscallSource syscallPublic (syscallRows 4) = true ∧
      ((syscallSource.hostStep? syscallPolicy syscallProgram).map
        (fun output => output.1.sail.registers.get? LeanRV64D.Defs.Register.x5)) = some (some 3) := by
  native_decide

private def haltSource (exit : ℕ) : ExecutionSnapshot :=
  { syscallSource with
    sail.registers := (syscallSource.sail.registers.insert .x5 0).insert .x10 (BitVec.ofNat 64 exit) }

private def haltInput (exit : ℕ) : HaltChip.Inputs Fp :=
  { state := ⟨0, 0, 9, #v[0, 1, 0]⟩
    x5_memory := ⟨word 0, ⟨0, 12⟩⟩
    x10_memory := ⟨word exit, ⟨0, 11⟩⟩
    x11_memory := ⟨word 9, ⟨0, 10⟩⟩
    is_real := 1 }

private def haltPublic (exit : ℕ) : SP1PublicIO Fp :=
  { syscallPublic with final_pc0 := 1, final_pc1 := 0, exit_code := exit }

private def haltRows (exit : ℕ) : List Row :=
  let sourceRow (previous index : ℕ) : Row :=
    (0, (toElements (OrderedSnapshotProvider.populate
      (SnapshotRegisterProvider.populate (haltSource exit).sail.memorySnapshot (BitVec.ofNat 5 index))
      previous index)).toList)
  [sourceRow 0 5, sourceRow 6 10, sourceRow 11 11, terminal 2 12,
    (3, finalRecord 0 5 13 0), (3, finalRecord 6 10 12 exit), (3, finalRecord 11 11 11 9), terminal 5 12,
    (6, ((DecodedProgramProvider.populate? (p := SP1Prime) syscallImage (65536, 0x00000073) 1).map
      (fun input => (toElements input).toList)).getD []),
    (57, (toElements (haltInput exit)).toList)]

/-- The complete local AIR accepts HALT at a non-boot source with the largest legacy exit code. -/
theorem activeHaltLocalShard :
    check syscallImage (haltSource 65535) (haltPublic 65535) (haltRows 65535) = true := by native_decide

/-- The next exit code is valid for the concrete host but excluded by the legacy row's three
upper-zero assertions. This is a completeness restriction, not an error in host dispatch. -/
theorem legacyHaltExitRange :
    check syscallImage (haltSource 65536) (haltPublic 65536) (haltRows 65536) = false ∧
      (((haltSource 65536).host.run syscallPolicy (.ofSail (haltSource 65536).sail.realize)).map
        (fun execution => execution.effect.state.exitCode)) = some (some 65536) := by
  rw [← SailSnapshot.readContext_eq]
  native_decide

/-- HALT's actual register observations and public exit cannot be changed independently. -/
theorem rejectsForgedHalt :
    [check syscallImage { haltSource 65535 with
        sail.registers := (haltSource 65535).sail.registers.insert .x5 1 }
      (haltPublic 65535) (haltRows 65535),
     check syscallImage { haltSource 65535 with
        sail.registers := (haltSource 65535).sail.registers.insert .x11 8 }
      (haltPublic 65535) (haltRows 65535),
     check syscallImage (haltSource 65535) (haltPublic 65534) (haltRows 65535)] =
      [false, false, false] := by native_decide

private def unchangedBanks (host : HostState) : List Row :=
  [(87, (toElements (HostCommitBoundary.start (HostCommitEnsemble.sourceValues false host))).toList),
   (88, (toElements (HostCommitBoundary.start (HostCommitEnsemble.sourceValues true host))).toList)]

private def haltInstruction (exit : ℕ) : HostCallChip.Inputs Fp :=
  ⟨{ syscallInput 0 with
      op_a_memory.prev_value := word 0, op_b_memory.prev_value := word exit,
      next_pc := #v[1, 0, 0], is_halt := 1,
      syscall_id_bytes := U16toU8OperationSafe.populate (word 0),
      is_enter_unconstrained := IsZeroOperation.populate (-3 : Fp),
      is_hint_len := IsZeroOperation.populate (-240 : Fp),
      is_halt_zero := IsZeroOperation.populate (0 : Fp),
      is_commit := IsZeroOperation.populate (-16 : Fp),
      is_commit_deferred := IsZeroOperation.populate (-26 : Fp) },
    ⟨0, ⟨0, 0⟩⟩⟩

private def installedHaltRows (exit : ℕ) (legacy : Bool) : List Row :=
  (if legacy then haltRows exit else
    (haltRows exit).filter (fun row => row.1 != 57) ++
      [(58, (toElements (haltInstruction exit)).toList),
       (63, (toElements (HostHaltChip.populate ((haltInstruction exit).message 0))).toList)]) ++
    unchangedBanks (haltSource exit).host

private def checkInstalledHalt (exit publicExit : ℕ) (rows : List Row) : Bool :=
  let checked := installedChecks (haltSource exit) (haltPublic publicExit)
    { (haltSource exit).host with exitCode := some (BitVec.ofNat 32 exit) } rows
  checked.1 && checked.2

/-- The installed assembly rejects active legacy HALT and accepts canonical syscall HALT,
including a code above the legacy range, without a legacy padding companion. -/
theorem installedHaltExit :
    checkInstalledHalt 65535 65535 (installedHaltRows 65535 true) = false ∧
    checkInstalledHalt 65536 65536 (installedHaltRows 65536 false) = true ∧
    checkInstalledHalt 0 0 (installedHaltRows 0 false) = true ∧
    ((haltSource 0).hostStep? syscallPolicy syscallProgram).map (fun result => result.1.host.exitCode) =
      some (some 0) := by native_decide

/-- Wrong public values, duplicate HALT producers, and a spurious legacy padding producer are
rejected by complete acceptance, including when the genuine exit code is zero. -/
theorem rejectsInstalledExitForgery :
    [checkInstalledHalt 65536 65535 (installedHaltRows 65536 false),
     checkInstalledHalt 0 1 (installedHaltRows 0 false),
     checkInstalledHalt 0 0 (installedHaltRows 0 false ++
       (installedHaltRows 0 false).filter (fun row => row.1 == 58 || row.1 == 63)),
     checkInstalledHalt 0 0 (installedHaltRows 0 false ++
       [(57, List.replicate (size HaltChip.Inputs) 0)])] =
      [false, false, false, false] := by native_decide

/-- A real HALT-zero cannot be advertised as running or as a different exit code. -/
theorem rejectsSuppliedExitStatus :
    installedChecks (haltSource 0) (haltPublic 0)
      { (haltSource 0).host with exitCode := none } (installedHaltRows 0 false) = (false, true) ∧
    installedChecks (haltSource 0) (haltPublic 0)
      { (haltSource 0).host with exitCode := some 7 } (installedHaltRows 0 false) = (false, true) := by
  native_decide

private def checkTerminalIdentity (initial final : Option (BitVec 32)) : Bool × Bool :=
  let incoming := { haltSource 0 with host.exitCode := initial }
  installedChecks incoming identityPublic { incoming.host with exitCode := final }
    (identityRows ++ unchangedBanks incoming.host)

/-- Empty running and stopped shards retain their exact optional exit, including wide codes.
Neither a fabricated HALT-zero nor restarting a stopped host can pass the complete checks. -/
theorem terminalIdentity :
    [checkTerminalIdentity none none,
     checkTerminalIdentity (some 0) (some 0),
     checkTerminalIdentity (some 65536) (some 65536),
     checkTerminalIdentity none (some 0),
     checkTerminalIdentity (some 0) none,
     checkTerminalIdentity (some 65536) (some 0)] =
      [(true, true), (true, true), (true, true), (false, true), (false, true), (false, true)] := by
  native_decide

private def storeRomImage : ProgramImage := ⟨[(65536, 0x00110023)], 65536, []⟩

private def storeRomSource : ExecutionSnapshot :=
  { source with
    sail := { registers := ((configuredState 65536).regs.insert .x1 0).insert .x2 65536
              memory := storeRomImage.initialMemory } }

private def storeRomInput : StoreByteChip.Inputs Fp :=
  { is_real := 1, state := ⟨0, 0, 9, #v[0, 1, 0]⟩
    adapter :=
      { op_a := 1, op_a_memory := ⟨word 0, ⟨0, 12⟩⟩, op_a_0 := 0,
        op_b := 2, op_b_memory := ⟨word 65536, ⟨0, 11⟩⟩, op_c_imm := word 0 }
    memory_access :=
      { prev_value := word 0x00110023, access_timestamp := ⟨0, 0, 1, 9, 0⟩ }
    offset_bit := #v[0, 0, 0], mem_limb := 0x23, mem_limb_low_byte := 0x23
    register_low_byte := 0, increment := -(0x23 : Fp), store_value := word 0x00110000 }

private def storeRomRows : List Row :=
  let sourceRow (previous index : ℕ) : Row :=
    (0, (toElements (OrderedSnapshotProvider.populate
      (SnapshotRegisterProvider.populate storeRomSource.sail.memorySnapshot (BitVec.ofNat 5 index))
      previous index)).toList)
  [sourceRow 0 1, sourceRow 2 2,
    (1, (toElements (OrderedSnapshotProvider.populate
      (word 65536) 3 65536)).toList),
    terminal 2 65537,
    (3, finalRecord 0 1 13 0), (3, finalRecord 2 2 12 65536),
    (4, finalRecord 3 65536 10 0x00110000), terminal 5 65537,
    (6, ((DecodedProgramProvider.populate? (p := SP1Prime) storeRomImage (65536, 0x00110023) 1).map
      (fun input => (toElements input).toList)).getD []),
    (25, (toElements storeRomInput).toList), (57, List.replicate (size HaltChip.Inputs) 0)]

/-- The unguarded local AIR permits SB to overwrite its own instruction byte. Source ROM
validation and fixed Program membership alone do not enforce ROM preservation. -/
theorem unguardedStoreIntoRom :
    check storeRomImage storeRomSource publicInput storeRomRows = true ∧
      storeRomImage.readOnly 65536 = true ∧
      storeRomSource.sail.memory.read 65536 = 0x23 ∧
      Word.toBitVec64 storeRomInput.store_value = 0x00110000 := by native_decide

private def permissionRow (address : ℕ) : Row :=
  (61, ((WritePermissionProvider.populate? (p := SP1Prime) storeRomImage address).map
    (fun input => (toElements input).toList)).getD [])

private def sameValueRomSource : ExecutionSnapshot :=
  { storeRomSource with sail.registers := storeRomSource.sail.registers.insert .x1 0x23 }

private def sameValueRomInput : StoreByteChip.Inputs Fp :=
  { storeRomInput with
    adapter.op_a_memory.prev_value := word 0x23,
    register_low_byte := 0x23, increment := 0, store_value := word 0x00110023 }

private def sameValueRomRows : List Row :=
  let sourceRow (previous index : ℕ) : Row :=
    (0, (toElements (OrderedSnapshotProvider.populate
      (SnapshotRegisterProvider.populate sameValueRomSource.sail.memorySnapshot (BitVec.ofNat 5 index))
      previous index)).toList)
  [sourceRow 0 1, sourceRow 2 2,
    (1, (toElements (OrderedSnapshotProvider.populate
      (word 65536) 3 65536)).toList),
    terminal 2 65537,
    (3, finalRecord 0 1 13 0x23), (3, finalRecord 2 2 12 65536),
    (4, finalRecord 3 65536 10 0x00110023), terminal 5 65537,
    (6, ((DecodedProgramProvider.populate? (p := SP1Prime) storeRomImage (65536, 0x00110023) 1).map
      (fun input => (toElements input).toList)).getD []),
    (25, (toElements sameValueRomInput).toList), (57, List.replicate (size HaltChip.Inputs) 0)]

/-- An SB that leaves its entire RAM cell unchanged still needs code-write permission.
The unprotected AIR accepts the real row; both the protected AIR and semantic policy reject it. -/
theorem rejectsSameValueRomStore :
    check storeRomImage sameValueRomSource publicInput sameValueRomRows = true ∧
    check storeRomImage sameValueRomSource publicInput sameValueRomRows true = false ∧
    sameValueRomInput.store_value = sameValueRomInput.memory_access.prev_value ∧
    InstructionWrite.check storeRomImage.readOnly
      sameValueRomSource.sail.readContext.register (.STORE (0, .Regidx 1, .Regidx 2, 1)) = false := by
  native_decide

private def besideRomSource : ExecutionSnapshot :=
  { storeRomSource with
    sail.registers := (storeRomSource.sail.registers.insert .x1 127).insert .x2 65540 }

private def besideRomInput : StoreByteChip.Inputs Fp :=
  { storeRomInput with
    adapter.op_a_memory.prev_value := word 127
    adapter.op_b_memory.prev_value := word 65540
    offset_bit := #v[0, 0, 1], mem_limb := 0, mem_limb_low_byte := 0
    register_low_byte := 127, increment := 127, store_value := word 0x7f00110023 }

private def besideRomRows : List Row :=
  let sourceRow (previous index : ℕ) : Row :=
    (0, (toElements (OrderedSnapshotProvider.populate
      (SnapshotRegisterProvider.populate besideRomSource.sail.memorySnapshot (BitVec.ofNat 5 index))
      previous index)).toList)
  [sourceRow 0 1, sourceRow 2 2,
    (1, (toElements (OrderedSnapshotProvider.populate
      (word 65536) 3 65536)).toList),
    terminal 2 65537,
    (3, finalRecord 0 1 13 127), (3, finalRecord 2 2 12 65540),
    (4, finalRecord 3 65536 10 0x7f00110023), terminal 5 65537,
    (6, ((DecodedProgramProvider.populate? (p := SP1Prime) storeRomImage (65536, 0x00110023) 1).map
      (fun input => (toElements input).toList)).getD []),
    (25, (toElements besideRomInput).toList), (57, List.replicate (size HaltChip.Inputs) 0)]

/-- The strengthened full AIR rejects the reproduced store into its own code byte, including
an attempted provider row whose query is ROM but whose interval was selected for writable RAM. -/
theorem protectedRejectsStoreIntoRom :
    [check storeRomImage storeRomSource publicInput storeRomRows true,
     check storeRomImage storeRomSource publicInput (storeRomRows ++ [permissionRow 65540]) true,
     check storeRomImage storeRomSource publicInput (storeRomRows ++ [(61,
       ((WritePermissionProvider.populate? (p := SP1Prime) storeRomImage 65540).map
         (fun input => (toElements { input with address := Address.ofNat 65536 }).toList)).getD [])]) true] =
      [false, false, false] := by native_decide

/-- Byte-precise protection permits changing writable data in the other half of the same RAM
cell as code, while requiring a matching permission provider at the actual written address. -/
theorem protectedPartialStoreBesideRom :
    [check storeRomImage besideRomSource publicInput (besideRomRows ++ [permissionRow 65540]) true,
     check storeRomImage besideRomSource publicInput besideRomRows true,
     check storeRomImage besideRomSource publicInput (besideRomRows ++ [permissionRow 65541]) true] =
      [true, false, false] := by native_decide

private def receiptStore (source : ExecutionSnapshot) (input : StoreByteChip.Inputs Fp) :=
  evaluate storeRomImage source (ProtectedOrdinaryReceipt.component .storeByte) (toElements input).toList

private def receiptPermission (source : ExecutionSnapshot) (input : StoreByteChip.Inputs Fp)
    (permissions : List (List Fp)) : Bool :=
  let produced := receiptStore source input
  let providers := permissions.map fun row =>
    evaluate storeRomImage source { circuit := WritePermissionProvider.circuit storeRomImage } row
  let ledger := ((produced :: providers).flatMap (·.2)).filter
    (fun entry => entry.1 == (WritePermissionProvider.channel (p := SP1Prime)).name)
  produced.1 && providers.all (·.1) && ledger.all (fun key =>
    ((ledger.filter (fun item => item.2.1 == key.2.1)).map (·.2.2)).sum == 0)

/-- Publishing a receipt retains byte-precise permission enforcement. Even an unchanged code
store fails, while a writable byte beside code succeeds only with the matching provider.
This checks the actual permission subsystem; observation endpoint installation is separate. -/
theorem receiptStoreProtection :
    (receiptStore sameValueRomSource sameValueRomInput).1 = true ∧
    ((receiptStore sameValueRomSource sameValueRomInput).2.filter
      (fun entry => entry.1 == "SP1OrdinaryStateReceipt")) =
        [("SP1OrdinaryStateReceipt", [0, 17, 4, 1, 0], 1)] ∧
    [receiptPermission sameValueRomSource sameValueRomInput [],
     receiptPermission sameValueRomSource sameValueRomInput [(permissionRow 65540).2],
     receiptPermission besideRomSource besideRomInput [],
     receiptPermission besideRomSource besideRomInput [(permissionRow 65541).2],
     receiptPermission besideRomSource besideRomInput [(permissionRow 65540).2]] =
      [false, false, false, false, true] := by native_decide

/-- Adding the permission ledger preserves ordinary non-store and HALT local segments. -/
theorem protectedNonStores :
    check image source publicInput baseRows true = true ∧
      check syscallImage (haltSource 65535) (haltPublic 65535) (haltRows 65535) true = true := by native_decide

/-- Endpoint encoding includes the last native byte and excludes the first out-of-range address. -/
theorem permissionAddressWindow :
    ((WritePermissionProvider.populate? (p := SP1Prime) storeRomImage (2 ^ 48 - 1)).isSome,
      (WritePermissionProvider.populate? (p := SP1Prime) storeRomImage (2 ^ 48)).isSome) =
        (true, false) := by native_decide

/-- info: exportable ✓ (4 witness cells) -/
#guard_msgs in
#assert_exportable (ProtectedStore.byte (p := SP1Prime))

/-- info: exportable ✓ (4 witness cells) -/
#guard_msgs in
#assert_exportable (ProtectedStore.half (p := SP1Prime))

/-- info: exportable ✓ (4 witness cells) -/
#guard_msgs in
#assert_exportable (ProtectedStore.word (p := SP1Prime))

/-- info: exportable ✓ (4 witness cells) -/
#guard_msgs in
#assert_exportable (ProtectedStore.double (p := SP1Prime))

/-- info: exportable ✓ (88 witness cells) -/
#guard_msgs in
#assert_exportable (WritePermissionProvider.circuit (p := SP1Prime) storeRomImage)

/-- Padding in every store table has zero permission demand; stopped-source identities remain valid. -/
theorem protectedPaddingIdentity :
    let rows := identityRows ++
      [(25, List.replicate (size StoreByteChip.Inputs) 0),
       (26, List.replicate (size StoreHalfChip.Inputs) 0),
       (27, List.replicate (size StoreWordChip.Inputs) 0),
       (28, List.replicate (size StoreDoubleChip.Inputs) 0)]
    check image source identityPublic rows true = true ∧
      check image { source with host.exitCode := some 0 } identityPublic rows true = true := by native_decide

/-- Shared active ADD fixture for extensions of the same native physical assembly. -/
def addFixture : ProgramImage × ExecutionSnapshot × SP1PublicIO Fp × List Row :=
  (image, source, publicInput, baseRows)

/-- Execute actual row programs and fixed lookups, allowing an extension's additional fixed tables. -/
def evaluateComponent (image : ProgramImage) (source : ExecutionSnapshot) (component : Component Fp)
    (inputs : List Fp) (extraLookups : List (FiniteLookup Fp)) : Bool × Ledger :=
  evaluate image source component inputs extraLookups

/-- Construct real Byte/Range providers at their stable local-assembly positions. -/
def provideBytes := byteProvider

end SP1CleanTest.Core.LocalCore
