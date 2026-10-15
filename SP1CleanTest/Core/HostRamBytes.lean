import SP1Clean.Proofs.Operations.HostRamBytes
import SP1Clean.Proofs.Chips.HostRamReadChip.Populate
import SP1CleanTest.Core.HostChecks
import Clean.Circuit.WitnessExport

/-! # Host-word byte decoding and read-ledger regressions

Execute the bundled decoder and constrain its actual output. Joint provider/consumer checks
retain complete read keys and the single physical Memory pair. Span queries remain fixtures;
these tests do not claim that a host call has selected the complete buffer footprint.
-/

namespace SP1CleanTest.Core.HostRamBytes

open Circuit SP1Clean SP1Clean.Model.Core HostChecks

private abbrev Fp := ZMod SP1Prime

private def expected : Vector Fp 8 := #v[0, 255, 1, 128, 255, 0, 254, 127]

private def prior : Channels.MemoryMsg Fp :=
  ⟨0, 16777215, 0, 1, 0, #v[65280, 32769, 255, 32766]⟩

private def provider : HostRamReadChip.Inputs Fp :=
  HostRamReadChip.populate prior 1 1 0 true

private def evaluate (input : SP1Clean.HostRamBytes.Inputs Fp)
    (output : Vector Fp 8 := expected) : Bool × Ledger :=
  evaluateProgram (do
    let actual ← SP1Clean.HostRamBytes.circuit (varFromOffset SP1Clean.HostRamBytes.Inputs 0)
    assertion (Gadgets.Equality.circuit (fields 8)) ⟨actual, const output⟩)
    (toElements input).toList

private def consumer : SP1Clean.HostRamBytes.Inputs Fp :=
  SP1Clean.HostRamBytes.populate provider.message

private def produced : Bool × Ledger :=
  evaluateProgram (HostRamReadChip.main (varFromOffset HostRamReadChip.Inputs 0))
    (toElements provider).toList

private def readBalanced (ledger : Ledger) : Bool :=
  let reads := ledger.filter fun entry => entry.1 == "sp1.native.host_ram_read"
  reads.length < SP1Prime && reads.all fun (_, message, _) =>
    (reads.filterMap fun (_, other, mult) => if message == other then some mult else none).sum == 0

/-- The output uses every low/high byte, with fixed little-endian order across all four limbs. -/
theorem decodesBytes : (evaluate consumer).1 = true ∧
    (List.range 8).all (fun index =>
      !(evaluate consumer (expected.set! index (expected[index]! + 1))).1) = true := by
  native_decide

/-- Two decoders consume both shared reads while retaining only one physical RAM update. -/
theorem sharedDecoderLedger :
    let consumed := evaluate consumer
    let ledger := produced.2 ++ consumed.2 ++ consumed.2
    produced.1 = true ∧ consumed.1 = true ∧ readBalanced ledger = true ∧
    ((ledger.filter fun entry => entry.1 == "SP1Memory").map fun entry => entry.2.2) = [-1, 1] ∧
    readBalanced (produced.2 ++ consumed.2) = false ∧
    readBalanced (ledger ++ consumed.2) = false := by native_decide

/-- Byte-column changes and malformed channel guarantees fail the executable local checks. -/
theorem rejectsMalformed :
    (List.range 4).all (fun index =>
      !(evaluate { consumer with low := consumer.low.set! index (consumer.low[index]! + 1) }).1) = true ∧
    [{ consumer.read with addr0 := 1 }, { consumer.read with addr1 := 0 },
      { consumer.read with addr2 := 65536 },
      { consumer.read with value := #v[65536, 0, 0, 0] }].all
      (fun read => !(evaluate (SP1Clean.HostRamBytes.populate read)).1) = true := by native_decide

/-- Locally valid clock/address/value changes still fail matching against the original provider. -/
theorem rejectsWrongReadKey :
    [{ consumer.read with clk_high := 2 }, { consumer.read with clk_low := 9 },
      { consumer.read with addr0 := 8 }, { consumer.read with value := #v[0, 0, 0, 0] }].all
      (fun read =>
        let changed := SP1Clean.HostRamBytes.populate read
        let output := SP1Clean.HostRamBytes.bytes (256 : Fp)⁻¹ changed
        let checked := evaluate changed output
        checked.1 && !readBalanced (produced.2 ++ checked.2 ++ (evaluate consumer).2)) = true := by
  native_decide

private def context : HostReadContext where
  register _ := none
  byte address := some (BitVec.ofNat 8 address)

private def policy : HostMemoryPolicy := { readOnly := fun _ => false }

private def words (cell : ℕ) : BitVec 64 :=
  Word.bytesValue (Vector.ofFn fun index => BitVec.ofNat 8 (cell * 8 + index.val))

/-- Unaligned reads preserve exactly 32 bytes; the empty upper endpoint reads no cell. -/
theorem spanReads :
    context.readGuest? policy 65539 32 = some ((List.range 32).map fun index => BitVec.ofNat 8 (index + 3)) ∧
    context.readGuest? policy 65539 32 = some (HostReadContext.slice words 65539 32) ∧
    context.readGuest? policy (2 ^ 48) 0 = some [] ∧
    context.readGuest? policy (2 ^ 48 - 31) 32 = none ∧
    ({ context with byte := fun address => if address == 65560 then none else context.byte address } :
      HostReadContext).readGuest? policy 65539 32 = none := by native_decide

/-- info: exportable ✓ (0 witness cells) -/
#guard_msgs in
#assert_exportable (SP1Clean.HostRamBytes.circuit (p := SP1Prime))

end SP1CleanTest.Core.HostRamBytes
