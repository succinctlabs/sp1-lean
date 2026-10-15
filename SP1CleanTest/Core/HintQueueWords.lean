import SP1CleanTest.Core.HostChecks
import Clean.Circuit.WitnessExport
import SP1Clean.Proofs.Operations.HintQueueWordSource
import SP1Clean.Native.Operations.HintQueueSource

/-! # Byte-authenticated source hints and complete padded requests

Evaluate actual fixed-lookup providers and fixture consumers on the node/word ledgers. These
tests expose missing words, content changes, and the need for separate length authentication.
The fixture consumer is not the full HINT_READ handler or a mixed-AIR integration claim.
-/

namespace SP1CleanTest.Core.HintQueueWords

open Circuit Air.Flat SP1Clean Model.Core HintQueue HostChecks

private abbrev Fp := ZMod SP1Prime

private def sourceWord (hints : List Bytes) (row : WordRecord Fp) : Bool × Ledger :=
  evaluateProgram (HostHintQueue.sourceWordMain hints (varFromOffset WordRecord 0))
    (toElements row).toList none [FiniteLookup.ofStatic (sourceWordTable hints)]

private def sourceNode (hints : List Bytes) (row : NodeRecord Fp) : Bool × Ledger :=
  evaluateProgram (HostHintQueue.sourceMain hints (varFromOffset NodeRecord 0))
    (toElements row).toList none [FiniteLookup.ofStatic (sourceTable hints)]

private def demand (pointer : ℕ) (bytes : Bytes) : Bool × Ledger :=
  evaluateProgram (do
    HostHintQueue.nodeChannel.pull (const (NodeRecord.encode pointer ⟨bytes, 0⟩))
    Circuit.forEach (Vector.ofFn fun index : Fin (wordCount bytes) => index.val) fun index =>
      HostHintQueue.wordChannel.pull (const (WordRecord.encode pointer bytes index))) []

private def balanced (ledger : Ledger) : Bool :=
  ledger.length < SP1Prime && ledger.all fun key =>
    ((ledger.filter (fun item => item.1 == key.1 && item.2.1 == key.2.1)).map (·.2.2)).sum == 0

private def checkWords (actual claimed : Bytes) (rows : List (WordRecord Fp)) : Bool :=
  let header := sourceNode [actual] (NodeRecord.encode 1 ⟨actual, 0⟩)
  let words := rows.map (sourceWord [actual])
  let consumed := demand 1 claimed
  header.1 && words.all (·.1) && consumed.1 &&
    balanced (header.2 ++ words.flatMap (·.2) ++ consumed.2)

private def complete (actual claimed : Bytes) : Bool :=
  checkWords actual claimed (nodeWordRows 1 actual)

private def bytes (length : ℕ) : Bytes :=
  (List.range length).map fun index => BitVec.ofNat 8 (17 * index + 1)

/-- Complete source contents and lengths balance for partial, empty, and aligned hints. -/
theorem completeRequests : (List.range 26).all (fun length => complete (bytes length) (bytes length)) = true := by
  native_decide

/-- Same-length replacement bytes cannot reuse a valid metadata header. -/
theorem changedContents :
    complete [1, 2] [8, 9] = false ∧ complete [1, 2] [2, 1] = false ∧
    complete (bytes 17) ((bytes 16) ++ [255]) = false := by native_decide

/-- Omitting the mandatory padding word fails, including for an empty or aligned hint. -/
theorem completePadding : [0, 1, 7, 8, 9, 16].all (fun length =>
    let actual := bytes length
    let rows := nodeWordRows (p := SP1Prime) 1 actual
    rows.length == length / 8 + 1 &&
      !(checkWords actual actual (rows.take (rows.length - 1))) &&
      !(checkWords actual actual (rows ++ rows.take 1))) = true := by native_decide

/-- Word values alone cannot recover length when trailing source bytes are zero. -/
theorem lengthIsRequired :
    wordValue [] 0 = wordValue [0] 0 ∧ wordCount [] = wordCount [0] ∧
      complete [] [0] = false ∧ complete [0] [] = false := by native_decide

/-- Key substitution, extra positions, malformed limbs, and forged padding fail the lookup. -/
theorem forgedWords :
    let actual := bytes 8
    let row := WordRecord.encode (p := SP1Prime) 1 actual 0
    [{ row with pointer := 0 }, { row with pointer := Address.ofNat 2 },
     { row with pointer := #v[65536, 0, 0] },
     { row with index := #v[65536, 0, 0] },
     { row with index := Address.ofNat 1 }, { row with index := Address.ofNat 2 },
     { row with value := #v[65536, 0, 0, 0] },
     { row with isLast := 1 }, { row with isLast := 2 },
     { (WordRecord.encode 1 actual 1) with isLast := 0 },
     { (WordRecord.encode 1 actual 1) with value := #v[1, 0, 0, 0] }].all
       (fun forged => !(sourceWord [actual] forged).1) = true ∧
      (sourceWord [] (WordRecord.encode 1 [] 0)).1 = false := by native_decide

/-- The fixed source lookup authenticates exactly one final word, including empty hints. -/
theorem authenticatedEnds : (List.range 26).all (fun length =>
    let actual := bytes length
    let rows := nodeWordRows (p := SP1Prime) 1 actual
    (rows.filter (fun record => record.isLast == 1)).length == 1 &&
      rows.all (fun record => (sourceWord [actual] record).1 &&
        (record.isLast == 1) == (Address.toNat record.index + 1 == wordCount actual))) = true := by
  native_decide

/-- Even a hint whose length word wraps to zero cannot authenticate its first word as final. -/
theorem wrappedLengthHasNoBoundedEnd (actual : Bytes) (length : actual.length = 2 ^ 64)
    (index : ℕ) (bound : index < 2 ^ 48) :
    (WordRecord.encode (p := SP1Prime) 1 actual index).isLast = 0 := by
  have different : index + 1 ≠ wordCount actual := by simp only [wordCount, length]; omega
  simp only [WordRecord.encode, different, ↓reduceIte]

/-- Authenticated words agree with actual sparse writes, including overwritten padding bytes. -/
theorem actualPaddedWrites : (List.range 26).all (fun length =>
    let actual := bytes length
    let memory := (ByteMemory.mk []).writeBytes 65536 (List.replicate 40 255)
    let next := memory.writeBytes 65536 (hintWriteBytes actual)
    let rows := nodeWordRows (p := SP1Prime) 1 actual
    rows.all (fun row => (sourceWord [actual] row).1 &&
      Word.toBitVec64 row.value == next.readWord (65536 + Address.toNat row.index * 8)) &&
      next.read (65536 + 8 * wordCount actual) == 255) = true := by native_decide

/-- Historical source words stay usable, but a newly allocated node needs another authorization. -/
theorem historicalAndFresh :
    let hints : List Bytes := [[1, 2], [], bytes 9]
    let (store, head) := ofList hints
    let (next, fresh) := prepend store head [[1, 2]]
    (sourceWord hints (WordRecord.encode 1 (bytes 9) 0)).1 = true ∧
    (sourceWord hints (WordRecord.encode 3 [1, 2] 0)).1 = true ∧
    (sourceWord hints (WordRecord.encode fresh [1, 2] 0)).1 = false ∧
    decode? next head = some hints ∧ decode? next fresh = some ([1, 2] :: hints) := by native_decide

/-- info: exportable ✓ (0 witness cells) -/
#guard_msgs in
#assert_exportable (HostHintQueue.sourceWord (p := SP1Prime) [[], [1, 2, 3], bytes 8])

end SP1CleanTest.Core.HintQueueWords
