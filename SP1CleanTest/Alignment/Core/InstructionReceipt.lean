import SP1Clean.Soundness.OrdinaryStateReceipt
import SP1Clean.Soundness.HostOrdinaryReceipts
import SP1CleanTest.Alignment.Support.LocalCoreFixture
import SP1CleanTest.Core.NonVacuityReal
import SP1Clean.Native.Operations.OrdinaryObservation
import SP1CleanTest.Core.HostChecks
import Clean.Circuit.WitnessExport

/-! # Actual ordinary receipt programs

Existing active ADD and JAL/JALR rows exercise the receipt program, including a computed jump
target and JALR's low-bit masking. Every old assertion/lookup and ledger is preserved by the
generic theorems. These regressions inspect the added raw occurrences and reject forged
successors, missing/duplicate receipts and attempts to count a padding row as an instruction.
-/

namespace SP1CleanTest.Alignment.Core.InstructionReceipt

open Circuit Air.Flat SP1Clean SP1Clean.Soundness SP1Clean.NonVacuityRealTests

private abbrev Fp := ZMod SP1Prime
private def image := SP1CleanTest.Core.LocalCore.Fixture.image
private def source := SP1CleanTest.Core.LocalCore.Fixture.source

private def evaluate (id : InstructionChipId) (inputs : List Fp) :=
  SP1CleanTest.Core.LocalCore.Fixture.evaluate image source
    (OrdinaryStateReceipt.component id) inputs []

private def receipts (id : InstructionChipId) (inputs : List Fp) :=
  (evaluate id inputs).2.filter (fun entry => entry.1 == "SP1OrdinaryStateReceipt")

private def addInputs : List Fp := SP1Clean.Audit.OneAddNativePremises.inputs
private def paddingInputs : List Fp := addInputs.set 0 0
private def oddJalr : JalrChip.Inputs Fp :=
  { jalrInputs with adapter.op_c_imm := Target.bitVecToWord (BitVec.ofNat 64 0x11) }

/-- Active sequential and control-flow rows publish their actual successors. -/
theorem active :
    receipts .add addInputs = [("SP1OrdinaryStateReceipt", [0, 17, 4, 1, 0], 1)] ∧
    receipts .jal (toElements jalInputs).toList =
      [("SP1OrdinaryStateReceipt", [0, 17, 0x1100, 0, 0], 1)] ∧
    receipts .jalr (toElements oddJalr).toList =
      [("SP1OrdinaryStateReceipt", [0, 17, 0x2010, 0, 0], 1)] ∧
    (evaluate .add addInputs).1 = true ∧
    (evaluate .jal (toElements jalInputs).toList).1 = true ∧
    (evaluate .jalr (toElements oddJalr).toList).1 = true := by native_decide

/-- A padding row still costs one physical occurrence, with zero active multiplicity. -/
theorem padding : receipts .add paddingInputs =
    [("SP1OrdinaryStateReceipt", [0, 17, 4, 1, 0], 0)] := by native_decide

private def agrees (id : InstructionChipId) (inputs : List Fp) (claimed : List (List Fp)) : Bool :=
  let produced := (receipts id inputs).filter (fun entry => entry.2.2 != 0) |>.map (·.2.1)
  decide (produced.Perm claimed)

/-- Comparing the actual emitted multiset rejects omissions, duplicates and forged successors.
This is a ledger regression; the ordered bookkeeping consumer is a separate installation. -/
theorem mutations :
    [agrees .add addInputs [],
     agrees .add addInputs [[0, 17, 4, 1, 0], [0, 17, 4, 1, 0]],
     agrees .add addInputs [[0, 18, 4, 1, 0]],
     agrees .jal (toElements jalInputs).toList [[0, 17, 0x1004, 0, 0]],
     agrees .jalr (toElements oddJalr).toList [[0, 17, 0x2011, 0, 0]],
     agrees .add paddingInputs [[0, 17, 4, 1, 0]]] = List.replicate 6 false := by native_decide

private def consumed (message : Channels.StateMsg Fp) :=
  let input := OrdinaryObservation.populate true ⟨0, 0, 0, #v[0, 0, 0]⟩ message
  SP1CleanTest.Core.HostChecks.evaluateProgram
    (OrdinaryObservation.main true (varFromOffset OrdinaryObservation.Inputs 0))
    (toElements input).toList

private def joined (id : InstructionChipId) (inputs : List Fp)
    (messages : List (Channels.StateMsg Fp)) : Bool :=
  let consumers := messages.map consumed
  let ledger := receipts id inputs ++ ((consumers.flatMap (·.2)).filter
    (fun entry => entry.1 == "SP1OrdinaryStateReceipt"))
  (evaluate id inputs).1 && consumers.all (·.1) && ledger.all (fun key =>
    ((ledger.filter (fun item => item.2.1 == key.2.1)).map (·.2.2)).sum == 0)

/-- The actual consumer agrees with actual ADD/JALR producers. Missing, repeated and forged
messages fail real receipt balance, while inactive producer rows require no consumer. -/
theorem actualConsumer :
    joined .add addInputs [⟨0, 17, 4, 1, 0⟩] = true ∧
    joined .jalr (toElements oddJalr).toList [⟨0, 17, 0x2010, 0, 0⟩] = true ∧
    joined .add paddingInputs [] = true ∧
    [joined .add addInputs [],
     joined .add addInputs [⟨0, 17, 4, 1, 0⟩, ⟨0, 17, 4, 1, 0⟩],
     joined .add addInputs [⟨0, 18, 4, 1, 0⟩],
     joined .jalr (toElements oddJalr).toList [⟨0, 17, 0x2011, 0, 0⟩],
     joined .add paddingInputs [⟨0, 17, 4, 1, 0⟩]] = List.replicate 5 false := by native_decide

private def installed :=
    HostOrdinaryReceipts.ensemble (p := SP1Prime) image source source
      (HostHintQueueBoundary.initial []) HostCallReceivers.available
      (HostHintReadLocal.sourceResources []) []
      (HostFinalMemory.source_unique_names image source source.sail.memorySnapshot)

private def storeFixtures : List (ℕ × List Fp) :=
  [(25, (toElements storeByteInputs).toList), (26, (toElements storeHalfInputs).toList),
   (27, (toElements storeWordInputs).toList), (28, (toElements storeDoubleInputs).toList)]

private def installedStore (padding : Bool) (entry : ℕ × List Fp) :=
  match installed.tables[entry.1]? with
  | none => (false, [])
  | some component => SP1CleanTest.Core.LocalCore.Fixture.evaluate image source component
      (if padding then entry.2.set 0 0 else entry.2) []

/-- All four physical mixed-store positions retain every byte-permission request and add
exactly one receipt with the original successor. No endpoint acceptance is assumed here. -/
theorem installedStores :
    (storeFixtures.map (installedStore false)).all (·.1) = true ∧
    ((storeFixtures.map (installedStore false)).map fun result =>
      (result.2.filter (fun entry => entry.1 == "SP1OrdinaryStateReceipt"))) =
        List.replicate 4 [("SP1OrdinaryStateReceipt", [0, 17, 4100, 0, 0], 1)] ∧
    ((storeFixtures.map (installedStore false)).map fun result =>
      (result.2.filter (fun entry => entry.1 == (WritePermissionProvider.channel (p := SP1Prime)).name)).length) =
        [1, 2, 4, 8] := by native_decide

/-- Padding keeps its physical costs while both receipt and permission multiplicities vanish. -/
theorem installedStorePadding :
    (storeFixtures.map (installedStore true)).all (·.1) = true ∧
    ((storeFixtures.map (installedStore true)).flatMap (·.2) |>.filter fun entry =>
      entry.1 == "SP1OrdinaryStateReceipt" || entry.1 == (WritePermissionProvider.channel (p := SP1Prime)).name).all
        (fun entry => entry.2.2 == 0) = true := by native_decide

/-- info: exportable ✓ (4 witness cells) -/
#guard_msgs in
#assert_exportable (ProtectedOrdinaryReceipt.component (p := SP1Prime) .storeByte).circuit

/-- info: exportable ✓ (4 witness cells) -/
#guard_msgs in
#assert_exportable (ProtectedOrdinaryReceipt.component (p := SP1Prime) .storeHalf).circuit

/-- info: exportable ✓ (4 witness cells) -/
#guard_msgs in
#assert_exportable (ProtectedOrdinaryReceipt.component (p := SP1Prime) .storeWord).circuit

/-- info: exportable ✓ (4 witness cells) -/
#guard_msgs in
#assert_exportable (ProtectedOrdinaryReceipt.component (p := SP1Prime) .storeDouble).circuit

end SP1CleanTest.Alignment.Core.InstructionReceipt
