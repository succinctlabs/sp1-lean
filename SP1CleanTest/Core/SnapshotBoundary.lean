import SP1Clean.Proofs.Chips.OrderedSnapshotProvider
import SP1Clean.Model.SP1Field
import ToClean.Air.FiniteLookup
import SP1CleanTest.Core.StaticMembership
import Clean.Circuit.WitnessExport

/-! # Arbitrary source-snapshot AIR regressions

Execute the real witness programs and check all flattened assertions, concrete fixed lookups,
nonzero Byte messages, and both fixed membership ledgers. These are provider regressions, not a whole-machine balance claim.
-/

namespace SP1CleanTest.Core.SnapshotBoundary

open Circuit Air.Flat SP1Clean SP1Clean.Model.Core SP1Clean.Soundness.Target

private abbrev Fp := ZMod SP1Prime

private def snapshot : MemorySnapshot :=
  ⟨Vector.ofFn (fun index => BitVec.ofNat 64 (index.val * 0x123456789abcdef)),
    ⟨[(65536, 42), (65543, 171), (131071, 255), (2 ^ 48 - 1, 197)]⟩⟩

private instance byteDecidable (op : ByteOpcode) (a b c : Fp) : Decidable (op.constrain a b c) := by
  cases op <;> unfold ByteOpcode.constrain <;> infer_instance

private def byteValid (values : List Fp) : Bool :=
  match values with
  | [opcode, a, b, c] =>
    [ByteOpcode.AND, .OR, .XOR, .U8Range, .LTU, .MSB, .Range].any fun op =>
      opcode == (op.idx : Fp) && decide (op.constrain a b c)
  | _ => false

private def evaluate {Input : TypeMap} [ProvableType Input]
    (program : Var Input Fp → Circuit Fp (Var Channels.MemoryMsg Fp))
    (input : Input Fp) : Bool × List Fp :=
  let circuit := program (varFromOffset Input 0)
  let env := (circuit.proverEnvironment (ProverHint.empty Fp) (toElements input).toList).toEnvironment
  let operations := (circuit.operations (size Input)).toFlat
  let valid := operations.all fun operation =>
    match operation with
    | .assert expression => env expression == 0
    | .lookup .. => false
    | .interact interaction => interaction.channel.name != "SP1Byte" || env interaction.mult == 0 ||
        byteValid (interaction.msg.map env).toList
    | .witness .. => true
  let ledger := (FlatOperation.interactions operations).map fun interaction =>
    (interaction.channel.name, (interaction.msg.map env).toList, env interaction.mult)
  (valid && StaticMembership.check snapshot.registerTable ledger &&
      StaticMembership.check (InitialMemoryLookup.membership snapshot.memory (2 ^ 48) "sp1.native.initial_memory") ledger,
    (toElements (ProvableType.eval env (circuit.output (size Input)))).toList)

private def name : String := "SP1NativeSourceMemoryOrder"

/-- info: exportable ✓ (128 witness cells) -/
#guard_msgs in
#assert_exportable (OrderedSnapshotProvider.registerCircuit (p := SP1Prime) name snapshot)

/-- info: exportable ✓ (872 witness cells) -/
#guard_msgs in
#assert_exportable (OrderedSnapshotProvider.ramCircuit (p := SP1Prime) name snapshot)

/-- Every register, including x0 and multi-limb nonzero values, yields its authenticated record. -/
theorem constructedRegisters : (List.range 32).all (fun index =>
    let payload := SnapshotRegisterProvider.populate snapshot (BitVec.ofNat 5 index)
    let input := OrderedSnapshotProvider.populate payload index index
    evaluate (OrderedSnapshotProvider.registerCircuit name snapshot).main input ==
      (true, [0, 0, (index : Fp), 0, 0] ++ payload.value.toList)) = true := by native_decide

/-- Changed values in any limb, a substituted index, an invalid index, and a forged x0 all fail. -/
theorem rejectsForgedRegisters :
    let payload := SnapshotRegisterProvider.populate (p := SP1Prime) snapshot 5
    let bad := (List.range 4).map (fun limb =>
      let changed := payload.value.set! limb (payload.value[limb]! + 1)
      { payload with value := changed }) ++
      [{ payload with index := 6 }, { payload with index := 32 }, { payload with index := 0 }]
    bad.all (fun input => !(evaluate (SnapshotRegisterProvider.circuit snapshot).main input).1) = true := by
  native_decide

/-- Repeated requests share a count while all 32 physical rows and zero-count occurrences survive. -/
theorem fixedRegisterOccurrences :
    let source := snapshot.registerTable (p := SP1Prime)
    let message := (toElements (snapshot.registerRow (p := SP1Prime) 5)).toList ++ [1]
    let requests : StaticMembership.Ledger Fp :=
      [(source.channel.name, message, -1), (source.channel.name, message, -1)]
    let built := StaticMembership.table source requests
    let ledger := StaticMembership.providerLedger source requests
    built.length = 32 ∧ ledger.length = 32 ∧
      (ledger.filter (fun entry => entry.2.1 == message)).map (·.2.2) = [2] ∧
      (ledger.filter (fun entry => entry.2.2 == 0)).length = 31 ∧
      StaticMembership.check source requests = true ∧
      (StaticMembership.providerLedger source []).map (·.2.2) = List.replicate 32 0 := by
  native_decide

/-- Duplicate rows remain physical; an empty predicate has one inactive backend row. -/
theorem emptyAndDuplicateFixedRows :
    let row := snapshot.registerRow (p := SP1Prime) 5
    let duplicate := StaticTable.ofRows "duplicate" [row, row]
    let empty := StaticTable.ofRows (Row := RegisterSnapshotRow) (F := Fp) "empty" []
    let message := (toElements row).toList ++ [1]
    let requests : StaticMembership.Ledger Fp := [("duplicate", message, -1), ("duplicate", message, -1)]
    (StaticMembership.table duplicate requests).length = 2 ∧
      (StaticMembership.providerLedger duplicate requests).map (·.2.2) = [2, 0] ∧
      StaticMembership.check duplicate requests = true ∧
      (StaticMembership.table empty []).length = 1 ∧
      StaticMembership.check empty [] = true ∧
      StaticMembership.check empty [("empty", message, -1)] = false := by
  native_decide

/-- Explicit and default-zero RAM bytes are authenticated, including the last aligned word. -/
theorem constructedRam : [65536, 131064, 131072, 2 ^ 48 - 8].all (fun address =>
    ((OrderedSnapshotProvider.populateRam? 32 address).map fun input =>
      let result := evaluate (OrderedSnapshotProvider.ramCircuit name snapshot).main input
      let word := bitVecToWord (p := SP1Prime) (BitVec.ofNat 64 address)
      result == (true, [(0 : Fp), 0, word[0], word[1], word[2]] ++
        (bitVecToWord (p := SP1Prime) (snapshot.memory.readWord address)).toList)).getD false) = true := by
  native_decide

/-- A row built from different source memory cannot authenticate under this snapshot's fixed membership. -/
theorem rejectsForgedRam :
    let forged := { snapshot with memory := snapshot.memory.write 65536 99 }
    ((SnapshotRamProvider.populate? 65536).map fun input =>
      (evaluate (SnapshotRamProvider.circuit forged).main input).1) = some false := by native_decide

/-- Ordering still binds to the authenticated location; it cannot be a witness-selected key. -/
theorem rejectsUnrelatedKey :
    let input := OrderedSnapshotProvider.populate
      (SnapshotRegisterProvider.populate snapshot 5) 0 6
    (evaluate (OrderedSnapshotProvider.registerCircuit name snapshot).main input).1 = false := by native_decide

/-- Extensional comparison accepts obsolete history and explicit zero entries. -/
theorem equivalentHistories :
    let other := { snapshot with memory :=
      ⟨snapshot.memory.entries ++ [(65536, 99), (77777, 0)]⟩ }
    snapshot.equivalent other = true := by native_decide

/-- Equality includes addresses absent from a shard's provider rows, and every register. -/
theorem rejectsUntouchedMutations :
    [snapshot.equivalent { snapshot with memory := snapshot.memory.write 77777 1 },
     snapshot.equivalent { snapshot with registers := snapshot.registers.set! 31 0 },
     snapshot.equivalent { snapshot with memory := snapshot.memory.write (2 ^ 48 - 1) 0 }] =
      [false, false, false] := by native_decide

end SP1CleanTest.Core.SnapshotBoundary
