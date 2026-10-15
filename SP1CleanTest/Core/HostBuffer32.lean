import SP1Clean.Proofs.Operations.HostBuffer32.Populate
import SP1Clean.Proofs.Operations.HostBuffer32.Ledger
import SP1Clean.Proofs.Chips.HostRamReadChip.Populate
import SP1CleanTest.Core.HostChecks
import Clean.Circuit.WitnessExport

/-! # Complete host-buffer circuit regressions

All alignment variants execute their real assertions and read ledger. Overlapping buffers use
one physical provider per union cell. Requests remain fixtures until the call consumer is added.
-/

namespace SP1CleanTest.Core.HostBuffer32

open Circuit SP1Clean SP1Clean.Model.Core HostChecks
open SP1Clean.Soundness.Target

private abbrev Fp := ZMod SP1Prime

private def words (cell : ℕ) : Word Fp :=
  bitVecToWord (Word.bytesValue (Vector.ofFn fun index => BitVec.ofNat 8 (cell * 8 + index.val)))

private def evaluate (offset : Fin 8) (input : SP1Clean.HostBuffer32.Inputs offset Fp) : Bool × Ledger :=
  evaluateProgram (SP1Clean.HostBuffer32.main offset (varFromOffset (SP1Clean.HostBuffer32.Inputs offset) 0))
    (toElements input).toList

private def atQuery (address : ℕ) :=
  evaluate (SP1Clean.HostBuffer32.selectedOffset address) (SP1Clean.HostBuffer32.populate address 1 1 words)

private def reads (ledger : Ledger) : Ledger :=
  ledger.filter fun entry => entry.1 == "sp1.native.host_ram_read"

private def buffers (ledger : Ledger) : Ledger :=
  ledger.filter fun entry => entry.1 == "sp1.native.host_buffer32"

/-- Every alignment has the exact minimal read count and little-endian byte window. -/
theorem allAlignments : (List.range 8).all (fun offset =>
    let result := atQuery (65536 + offset)
    result.1 && (reads result.2).length == (if offset == 0 then 4 else 5) &&
      buffers result.2 == [("sp1.native.host_buffer32",
        [1, 1, (offset : Fp), 1, 0, 0] ++ (List.range 32).map (fun index => (((offset + index) % 256 : ℕ) : Fp)),
        1)]) = true := by native_decide

/-- Limb carries and the final permitted aligned/unaligned windows work; an escaping tail fails. -/
theorem windowBounds :
    [65536, 131069, 2 ^ 32 - 3, 2 ^ 48 - 33, 2 ^ 48 - 32].all (fun address => (atQuery address).1) = true ∧
    [65535, 2 ^ 48 - 31, 2 ^ 48].all (fun address => !(atQuery address).1) = true := by native_decide

private def fixture := SP1Clean.HostBuffer32.populate 65539 1 1 words

/-- Every byte is constrained, and a changed query cannot reuse the old cover or alignment. -/
theorem rejectsChangedMessage :
    (List.range 32).all (fun index =>
      !(evaluate _ { fixture with message.bytes :=
        fixture.message.bytes.set! index (fixture.message.bytes[index]! + 1) }).1) = true ∧
    [65536, 65540, 65547].all (fun address =>
      !(evaluate _ { fixture with message.address := SP1Clean.HostBuffer32.wordOffset address }).1) = true ∧
    !(evaluate _ { fixture with message.clk_high := 2 }).1 = true ∧
    !(evaluate _ { fixture with message.clk_low := 2 }).1 = true := by native_decide

/-- Replacing, moving, or duplicating any covering read is detected. -/
theorem rejectsChangedCells : (List.range 5).all (fun index =>
    let cell := fixture.cells[index]!
    [{ cell with read.clk_high := 2 }, { cell with read.clk_low := 2 },
      { cell with read.addr0 := cell.read.addr0 + 8 },
      SP1Clean.HostRamBytes.populate { cell.read with value := #v[0, 0, 0, 0] },
      fixture.cells[(index + 1) % 5]!].all (fun changed =>
        !(evaluate _ { fixture with cells := fixture.cells.set! index changed }).1)) = true := by
  native_decide

private def prior (cell : ℕ) : Channels.MemoryMsg Fp :=
  let read := SP1Clean.HostBuffer32.readAt (cell * 8) 0 16777215 (words cell)
  ⟨read.clk_high, read.clk_low, read.addr0, read.addr1, read.addr2, read.value⟩

private def providers := HostRamReadChip.populateSpans ⟨65539, 32⟩ ⟨65560, 32⟩ prior 1 1 0

private def produced : Bool × Ledger :=
  let checked := providers.map fun row =>
    evaluateProgram (HostRamReadChip.main (varFromOffset HostRamReadChip.Inputs 0)) (toElements row).toList
  (checked.all Prod.fst, checked.flatMap Prod.snd)

private def balanced (ledger : Ledger) : Bool :=
  let entries := reads ledger
  entries.length < SP1Prime && entries.all fun (_, message, _) =>
    (entries.filterMap fun (_, other, mult) => if message == other then some mult else none).sum == 0

/-- Two complete consumers balance their shared read providers with one physical access per cell. -/
theorem overlappingBuffers :
    let first := atQuery 65539
    let second := atQuery 65560
    let ledger := produced.2 ++ first.2 ++ second.2
    produced.1 = true ∧ first.1 = true ∧ second.1 = true ∧ balanced ledger = true ∧
    providers.length = 7 ∧
    (ledger.filter fun entry => entry.1 == "SP1Memory").length = 14 ∧
    (buffers ledger).length = 2 ∧
    balanced (produced.2 ++ first.2) = false ∧ balanced (ledger ++ second.2) = false := by native_decide

/-- info: exportable ✓ (0 witness cells) -/
#guard_msgs in
#assert_exportable (SP1Clean.HostBuffer32.circuit (p := SP1Prime) ⟨0, by decide⟩)

/-- info: exportable ✓ (0 witness cells) -/
#guard_msgs in
#assert_exportable (SP1Clean.HostBuffer32.circuit (p := SP1Prime) ⟨1, by decide⟩)

/-- info: exportable ✓ (0 witness cells) -/
#guard_msgs in
#assert_exportable (SP1Clean.HostBuffer32.circuit (p := SP1Prime) ⟨2, by decide⟩)

/-- info: exportable ✓ (0 witness cells) -/
#guard_msgs in
#assert_exportable (SP1Clean.HostBuffer32.circuit (p := SP1Prime) ⟨3, by decide⟩)

/-- info: exportable ✓ (0 witness cells) -/
#guard_msgs in
#assert_exportable (SP1Clean.HostBuffer32.circuit (p := SP1Prime) ⟨4, by decide⟩)

/-- info: exportable ✓ (0 witness cells) -/
#guard_msgs in
#assert_exportable (SP1Clean.HostBuffer32.circuit (p := SP1Prime) ⟨5, by decide⟩)

/-- info: exportable ✓ (0 witness cells) -/
#guard_msgs in
#assert_exportable (SP1Clean.HostBuffer32.circuit (p := SP1Prime) ⟨6, by decide⟩)

/-- info: exportable ✓ (0 witness cells) -/
#guard_msgs in
#assert_exportable (SP1Clean.HostBuffer32.circuit (p := SP1Prime) ⟨7, by decide⟩)

end SP1CleanTest.Core.HostBuffer32
