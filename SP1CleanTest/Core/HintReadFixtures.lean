import SP1CleanTest.Core.HostChecks
import SP1Clean.Proofs.Chips.HintReadWordChip.Populate
import SP1Clean.Proofs.Chips.HintReadWordChip.Ledger
import SP1Clean.Native.Operations.HintQueueWordSource
import SP1Clean.Native.Operations.WritePermission

/-! # Shared executable fixtures for hint transfers

These helpers run the actual word, source, and permission circuits and compare their complete
non-Byte ledgers. Semantic Memory boundary fixtures are independent of the consumer row values.
The handler battery replaces the fixture cursor endpoints with the real handler's interactions.
-/

namespace SP1CleanTest.Core.HintReadFixtures

open Circuit Air.Flat SP1Clean Model.Core HintQueue HostChecks

abbrev Fp := ZMod SP1Prime
abbrev Row := Bool × HintReadWordChip.Inputs Fp

def image : ProgramImage := ⟨[(131072, 0x00000073)], 131072, []⟩

def bytes (length : ℕ) : Bytes := (List.range length).map fun i => BitVec.ofNat 8 (19 * i + 3)

def oldWord : Word Fp := Soundness.Target.bitVecToWord (BitVec.allOnes 64)

def row (address : ℕ) (actual : Bytes) (index : ℕ) : Row :=
  let key := Address.ofNat (p := SP1Prime) (address + 8 * index)
  let word := WordRecord.encode (p := SP1Prime) 1 actual index
  let ram := HostRamAccessChip.populate ⟨0, 0, key[0], key[1], key[2], oldWord⟩ 0 1 0 word.value
  let last := decide (index + 1 = wordCount actual)
  (last, HintReadWordChip.populate last ram word.pointer word.index)

def rows (address : ℕ) (actual : Bytes) : List Row :=
  (List.range (wordCount actual)).map (row address actual)

def checked (row : Row) (corrupt : Option ℕ := none) : Bool × Ledger :=
  evaluateProgram (HintReadWordChip.main row.1 (varFromOffset HintReadWordChip.Inputs 0))
    (toElements row.2).toList corrupt

def source (actual : Bytes) (record : WordRecord Fp) : Bool × Ledger :=
  evaluateProgram (HostHintQueue.sourceWordMain [actual] (varFromOffset WordRecord 0))
    (toElements record).toList none [FiniteLookup.ofStatic (sourceWordTable [actual])]

def permission (image : ProgramImage) (address : ℕ) : Bool × Ledger :=
  match WritePermissionProvider.populate? (p := SP1Prime) image address with
  | none => (false, [])
  | some input =>
    evaluateProgram (WritePermissionProvider.main image (varFromOffset WritePermissionProvider.Inputs 0))
      (toElements input).toList none [FiniteLookup.ofStatic image.writePermissionTable]

def balanced (ledger : Ledger) : Bool :=
  let selected := ledger.filter (fun item => item.1 != "SP1Byte")
  selected.length < SP1Prime && selected.all fun key =>
    ((selected.filter (fun item => item.1 == key.1 && item.2.1 == key.2.1)).map (·.2.2)).sum == 0

def boundaries (address : ℕ) (actual : Bytes) : Ledger :=
  let count := wordCount actual
  let memory := (ByteMemory.mk []).writeBytes address (List.replicate (8 * count) 255)
  let after := memory.writeBytes address (hintWriteBytes actual)
  (evaluateProgram (do
    HintReadWordChip.stateChannel.push (const (⟨0, 1, Address.ofNat 1, 0, Address.ofNat address⟩ : HintReadWordChip.State Fp))
    HintReadWordChip.stateChannel.pull (const (⟨0, 1, Address.ofNat 1, Address.ofNat count,
      Address.ofNat (address + 8 * (count - 1))⟩ : HintReadWordChip.State Fp))
    Circuit.forEach (Vector.ofFn fun index : Fin count => index.val) fun index => do
      let key := Address.ofNat (p := SP1Prime) (address + 8 * index)
      Channels.memoryChannel.push (const ⟨0, 0, key[0], key[1], key[2], oldWord⟩)
      Channels.memoryChannel.pull (const ⟨0, 2, key[0], key[1], key[2],
        Soundness.Target.bitVecToWord (after.readWord (address + 8 * index))⟩)) []).2

def check (image : ProgramImage) (address : ℕ) (actual : Bytes) (rows : List Row)
    (missingPermission : Option ℕ := none) : Bool :=
  let consumers := rows.map checked
  let sources := rows.map fun row => source actual (row.2.step row.1).word
  let permissions := rows.flatMap fun row => (List.range 8).filterMap fun index =>
    let target := Address.toNat row.2.address + index
    if missingPermission == some target then none else some (permission image target)
  consumers.all (·.1) && sources.all (·.1) && permissions.all (·.1) &&
    balanced (boundaries address actual ++ consumers.flatMap (·.2) ++ sources.flatMap (·.2) ++ permissions.flatMap (·.2))

end SP1CleanTest.Core.HintReadFixtures
