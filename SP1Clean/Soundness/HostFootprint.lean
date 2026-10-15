import SP1Clean.Model.Core.HostFootprint
import SP1Clean.Model.Core.HostSail
import SP1Clean.Math.ByteWord
import SP1Clean.Soundness.Grounding.MemoryCell
import SP1Clean.Proofs.Operations.HostRamBytes

/-! # Host execution from authenticated Memory-bus words

Whole-word observations imply agreement on every byte the native host interpreter can inspect.
The words must be present: equality of two failed optional word reads would not authenticate
their constituent bytes. A separate frame theorem proves that applying the host effect preserves
every RAM cell outside its computed footprint. These are local semantic bridges for the pending
host AIR tables, not a construction of those tables or their balanced ledger.
-/

namespace SP1Clean.Soundness

open SP1Clean.Model.Core SP1Clean.Semantics SP1Clean.Soundness.Target

/-- The exact register/RAM keys consumed by a host access ledger. -/
def hostLocations (footprint : HostFootprint) : List MemLoc :=
  footprint.registers.map MemLoc.reg ++
    footprint.ramCells.map (fun index => .ram (BitVec.ofNat 61 index))

/-- The finite inventory has canonical, distinct Memory-bus locations after address encoding. -/
theorem hostLocations_canonical_nodup {host : HostState} {policy : HostPolicy}
    {context : HostReadContext} {execution : HostExecution} {footprint : HostFootprint}
    (run : host.run policy context = some execution)
    (built : execution.footprint? context = some footprint)
    (lower : 2 ^ 16 ≤ policy.memory.lower) (upper : policy.memory.upper ≤ 2 ^ 48) :
    (∀ loc ∈ hostLocations footprint, loc.CanonicalAddress) ∧ (hostLocations footprint).Nodup := by
  have bounds := host.footprint_in_window run built lower upper
  have indexValue (index : ℕ) (member : index ∈ footprint.ramCells) :
      (BitVec.ofNat 61 index).toNat = index := by
    apply Nat.mod_eq_of_lt
    have := bounds index member
    omega
  constructor
  · intro loc member
    rcases List.mem_append.mp member with register | ram
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp register
      trivial
    · obtain ⟨index, cellMem, rfl⟩ := List.mem_map.mp ram
      simp only [MemLoc.CanonicalAddress, indexValue index cellMem]
      have := bounds index cellMem
      omega
  · have distinct := HostExecution.footprint_nodup built
    apply List.nodup_append.mpr
    refine ⟨distinct.1.map (fun _ _ equal => MemLoc.reg.inj equal), ?_, ?_⟩
    · apply List.Nodup.map_on ?_ distinct.2
      intro left leftMem right rightMem equal
      have same := congrArg BitVec.toNat (MemLoc.ram.inj equal)
      simpa only [indexValue left leftMem, indexValue right rightMem] using same
    · intro left leftMem right rightMem
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp leftMem
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp rightMem
      simp

/-- The same defined Memory-bus words are observed by both source states on the finite footprint. -/
def HostWordAgreement (footprint : HostFootprint) (left right : SailState) : Prop :=
  (∀ index ∈ footprint.registers, left.get_reg? index = right.get_reg? index) ∧
    ∀ index ∈ footprint.ramCells, ∃ word,
      locContent left (.ram (BitVec.ofNat 61 index)) = some word ∧
      locContent right (.ram (BitVec.ofNat 61 index)) = some word

/-- A decoded host read reaches the Sail-backed host byte interface after its exact Memory
word has been grounded. Canonical address bounds and alignment come from the circuit contract. -/
theorem hostRamBytes_read_of_word {p : ℕ} [Fact p.Prime]
    {input : HostRamBytes.Inputs (ZMod p)} {output : Vector (ZMod p) 8}
    (checked : HostRamBytes.Spec input output) (source : SailState)
    (observed : locContent source
      (.ram (BitVec.ofNat 61 (Word.toNat input.read.address / 8))) =
        some (Word.toBitVec64 input.read.value)) :
    (HostReadContext.ofSail source).readBytes? (Word.toNat input.read.address) 8 =
      some (output.map fun byte => BitVec.ofNat 8 byte.val).toList := by
  apply checked.readBytes
  intro index
  have read := byte_of_ramWord64?_eq_some observed index
  have address : (RamCell.baseAddr (BitVec.ofNat 61 (Word.toNat input.read.address / 8))).toNat =
      Word.toNat input.read.address := by
    have bounded := checked.1.2.2.1
    have aligned := checked.1.2.2.2.1
    rw [RamCell.baseAddr_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [address] at read
  fin_cases index <;> exact read

/-- Defined aligned words authenticate every covered byte, including byte slices spanning cells. -/
theorem hostReadContext_agrees_of_words {footprint : HostFootprint} {left right : SailState}
    (bounded : ∀ index ∈ footprint.ramCells, index < 2 ^ 61)
    (words : HostWordAgreement footprint left right) :
    footprint.Agrees (.ofSail left) (.ofSail right) := by
  refine ⟨words.1, ?_⟩
  intro address covered
  obtain ⟨word, leftRead, rightRead⟩ := words.2 (address / 8) covered
  let cell : RamCell := BitVec.ofNat 61 (address / 8)
  have cellValue : cell.toNat = address / 8 := by
    exact Nat.mod_eq_of_lt (bounded _ covered)
  let offset : Fin 8 := ⟨address % 8, Nat.mod_lt _ (by decide)⟩
  have position : cell.baseAddr.toNat + offset.val = address := by
    rw [RamCell.baseAddr_toNat, cellValue]
    dsimp only [offset]
    omega
  have leftByte := byte_of_ramWord64?_eq_some leftRead offset
  have rightByte := byte_of_ramWord64?_eq_some rightRead offset
  change left.mem.get? address = right.mem.get? address
  exact (position ▸ leftByte).trans (position ▸ rightByte).symm

/-- Replacing a source state by one with the same authenticated footprint reproduces the whole
host execution. The footprint's address bounds follow from execution and the native memory policy. -/
theorem hostRun_of_wordAgreement {host : HostState} {policy : HostPolicy} {left right : SailState}
    {execution : HostExecution} {footprint : HostFootprint}
    (run : host.run policy (.ofSail left) = some execution)
    (built : execution.footprint? (.ofSail left) = some footprint)
    (lower : 2 ^ 16 ≤ policy.memory.lower) (upper : policy.memory.upper ≤ 2 ^ 48)
    (words : HostWordAgreement footprint left right) :
    host.run policy (.ofSail right) = some execution := by
  apply host.run_congr_of_footprint run built
  apply hostReadContext_agrees_of_words ?_ words
  intro index member
  have bounds := host.footprint_in_window run built lower upper index member
  omega

/-- The actual host update leaves every RAM word outside its computed inventory unchanged. -/
theorem hostExecution_ram_frame {execution : HostExecution} {context : HostReadContext}
    {footprint : HostFootprint} (built : execution.footprint? context = some footprint)
    (source : SailState) (pc : BitVec 64) (cell : RamCell)
    (outside : cell.toNat ∉ footprint.ramCells) :
    locContent (execution.apply source pc) (.ram cell) = locContent source (.ram cell) := by
  apply locContent_ram_congr_cell
  intro index
  change (execution.effect.applyMemory source.mem).get? (cell.baseAddr.toNat + index.val) = _
  cases written : execution.effect.write with
  | none => simp only [HostEffect.applyMemory, written]
  | some write =>
      simp only [HostEffect.applyMemory, written]
      apply write.read_outside
      by_contra inside
      have bound : cell.baseAddr.toNat + index.val - write.address < write.bytes.length := by omega
      have covered := execution.write_covered built written _ bound
      have cellAddress := RamCell.baseAddr_toNat cell
      have byteBound := index.isLt
      have same : (write.address + (cell.baseAddr.toNat + index.val - write.address)) / 8 =
          cell.toNat := by omega
      exact outside (same ▸ covered)

/-- A full emitted cell is exactly the post-state Memory-bus word. This includes a HINT_READ
padding cell; none of its bytes is inherited from old memory. -/
theorem hostExecution_written_word {execution : HostExecution} {write : HostMemoryWrite}
    (written : execution.effect.write = some write) (source : SailState) (pc : BitVec 64)
    (offset : ℕ) (bound : 8 * offset + 8 ≤ write.bytes.length) (cell : RamCell)
    (address : cell.baseAddr.toNat = write.address + 8 * offset) :
    locContent (execution.apply source pc) (.ram cell) =
      some (Word.bytesValue (write.wordBytes offset bound)) := by
  have read (index : ℕ) (small : index < 8) :
      (execution.apply source pc).mem.get? (cell.baseAddr.toNat + index) =
        some write.bytes[8 * offset + index] := by
    simp only [HostExecution.apply, HostEffect.applyMemory, written, address, Nat.add_assoc]
    exact write.read_written source.mem _ (by omega)
  have first : (execution.apply source pc).mem.get? cell.baseAddr.toNat =
      some write.bytes[8 * offset] := by simpa using read 0 (by decide)
  simp only [locContent, ramWord64?, first, read 1 (by decide), read 2 (by decide),
    read 3 (by decide), read 4 (by decide), read 5 (by decide), read 6 (by decide),
    read 7 (by decide), Word.bytesValue, HostMemoryWrite.wordBytes, Vector.getElem_ofFn]
  rfl

end SP1Clean.Soundness
