import SP1CleanTest.Core.HostChecks
import Clean.Circuit.WitnessExport
import SP1Clean.Proofs.Operations.HintReadSpanPopulate
import SP1Clean.Proofs.Operations.HintReadSpanLedger
import SP1Clean.Native.Operations.HintQueueWordSource

/-! # Exact padded counts, carries, and the final native RAM cell

Run the actual span circuit and its witness program, including every Byte request. The checks
retain a mathematical one-past endpoint at `2^48` and reject omission of the padding word. The
word-request fixtures exercise source contents; the complete AIR consumer walk is still pending.
-/

namespace SP1CleanTest.Core.HintReadSpan

open Circuit Air.Flat SP1Clean Model.Core HostChecks

private abbrev Fp := ZMod SP1Prime

private def word (value : ℕ) : Word Fp := Soundness.Target.bitVecToWord (BitVec.ofNat 64 value)

private def row (address length : ℕ) : SP1Clean.HintReadSpan.Inputs Fp :=
  SP1Clean.HintReadSpan.populate (Address.ofNat address) (word length)

private def checked (input : SP1Clean.HintReadSpan.Inputs Fp) (corrupt : Option ℕ := none) : Bool × Ledger :=
  evaluateProgram (SP1Clean.HintReadSpan.main (varFromOffset SP1Clean.HintReadSpan.Inputs 0))
    (toElements input).toList corrupt

private def divisionOutput (value : Word Fp) : Bool × AddressDiv8.Output Fp :=
  let input := AddressDiv8.populate value
  let program := AddressDiv8.main (varFromOffset AddressDiv8.Inputs 0)
  let env := (program.proverEnvironment (ProverHint.empty Fp) (toElements input).toList).toEnvironment
  ((evaluateProgram (do let _ ← program; pure ()) (toElements input).toList).1,
    Eval.eval env (program.output (size AddressDiv8.Inputs)))

/-- Division is exact through both limb carries and the last 48-bit value. -/
theorem divisionCarries : [0, 1, 7, 8, 65535, 65536, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 48 - 1].all
    (fun value =>
      let (valid, result) := divisionOutput (word value)
      valid && Address.toNat result.quotient == value / 8 && result.remainder.val == value % 8 &&
        Word.toNat result.rounded == value / 8 * 8) = true := by native_decide

/-- Counts include one padding word for every length; both addition stages use only Byte pulls. -/
theorem paddedCounts : [0, 1, 7, 8, 9, 15, 16, 65535, 65536, 2 ^ 32 - 1, 2 ^ 32,
    2 ^ 48 - 65536 - 1].all (fun length =>
      let input := row 65536 length
      let result := checked input
      result.1 && Address.toNat input.count == length / 8 + 1 &&
        Address.toNat input.last == 65536 + length / 8 * 8 && result.2.length == 6 &&
        result.2.all (fun item => item.1 == "SP1Byte" && item.2.2 == -1)) = true := by native_decide

/-- A permitted final cell is retained even though its one-past address cannot fit in three limbs. -/
theorem finalCell : [(2 ^ 48 - 8, 0), (2 ^ 48 - 8, 7), (2 ^ 48 - 16, 8),
    (2 ^ 48 - 16, 15)].all (fun (address, length) =>
      let input := row address length
      (checked input).1 && Address.toNat input.last + 8 == 2 ^ 48 &&
        address + 8 * Address.toNat input.count == 2 ^ 48) = true := by native_decide

/-- An extra padding cell outside RAM, unaligned starts, and out-of-domain lengths fail closed. -/
theorem rejectsWindow :
    [row (2 ^ 48 - 8) 8, row (2 ^ 48 - 16) 16, row 65528 0, row 65537 0,
      row 65536 (2 ^ 48), row 65536 (2 ^ 64 - 1),
      { (row 65536 0) with start := #v[65536, 0, 0] }].all
      (fun input => !(checked input).1) = true := by native_decide

/-- False count/last claims and noncanonical division columns fail the composed assertions. -/
theorem rejectsForgedEndpoints :
    let input := row 65536 16
    [{ input with count := 0 }, { input with count := Address.ofNat 2 },
     { input with count := Address.ofNat 4 }, { input with count := #v[65536, 0, 0] },
     { input with last := Address.ofNat 65544 }, { input with last := Address.ofNat 65560 },
     { input with length := { input.length with quotients := #v[1, 0, 0] } },
     { input with startQuotients := #v[1, 0, 0] }].all
       (fun forged => !(checked forged).1) = true ∧
      [0, 12, 13, 15, 47, 48, 60, 61, 63, 95, 97, 99, 100, 115].all
        (fun index => !(checked input (some index)).1) = true := by native_decide

/-- The checked count requests every source word, including the actual last-cell padding value. -/
theorem sourceWordCover : (List.range 18).all (fun length =>
    let bytes : Bytes := (List.range length).map fun index => BitVec.ofNat 8 (index + 1)
    let address := 2 ^ 48 - 8 * HintQueue.wordCount bytes
    let input := row address length
    let memory := (ByteMemory.mk []).writeBytes address (hintWriteBytes bytes)
    (checked input).1 && (List.range (Address.toNat input.count)).all (fun index =>
      let record := HintQueue.WordRecord.encode (p := SP1Prime) 1 bytes index
      let source := evaluateProgram
        (HostHintQueue.sourceWordMain [bytes] (varFromOffset HintQueue.WordRecord 0))
        (toElements record).toList none [FiniteLookup.ofStatic (HintQueue.sourceWordTable [bytes])]
      source.1 && (record.isLast == 1) == (index + 1 == Address.toNat input.count) &&
        Word.toBitVec64 record.value == memory.readWord (address + index * 8))) = true := by native_decide

/-- A wrapped length word cannot authenticate the actual node end; the consumer still needs that evidence. -/
theorem lengthWordNeedsNodeEnd :
    let actualLength : ℕ := 2 ^ 64
    let input := row 65536 actualLength
    word actualLength = word 0 ∧ (checked input).1 = true ∧ Address.toNat input.count = 1 ∧
      actualLength / 8 + 1 ≠ Address.toNat input.count := by native_decide

/-- info: exportable ✓ (48 witness cells) -/
#guard_msgs in
#assert_exportable (AddressDiv8.circuit (p := SP1Prime))

/-- info: exportable ✓ (116 witness cells) -/
#guard_msgs in
#assert_exportable (SP1Clean.HintReadSpan.circuit (p := SP1Prime))

end SP1CleanTest.Core.HintReadSpan
