import SP1Clean.Native.Operations.HostBuffer32

/-! # Address and byte assembly for complete host buffers

This argument uses only local word meanings, address additions, and byte assembly. No circuit
constraints are unpacked here. The caller supplies the already proved subcircuit contracts.
-/

namespace SP1Clean.HostBuffer32

open SP1Clean.Model.Core

variable {p : ℕ} [Fact p.Prime]

private theorem address_offset {base query : Word (ZMod p)} {amount : ℕ}
    (small : amount < 64) (baseBound : Word.isU64 base) (baseWindow : Word.toNat base < 2 ^ 48)
    (queryBound : Word.isU64 query)
    (equal : Word.toBitVec64 query = Word.toBitVec64 base + BitVec.ofNat 64 amount) :
    Word.toNat query = Word.toNat base + amount := by
  rw [← Word.toBitVec64_toNat queryBound, equal, BitVec.toNat_add,
    Word.toBitVec64_toNat baseBound, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : amount < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]

/-- Four or five adjacent bounded words and their decoded bytes determine the complete read. -/
theorem spec_of_cells (offset : Fin 8) (input : Inputs offset (ZMod p))
    (decoded : ∀ index : Fin (cellCount offset), HostRamBytes.Spec input.cells[index.val]
      (HostRamBytes.bytes (256 : ZMod p)⁻¹ input.cells[index.val]))
    (clocks : ∀ index : Fin (cellCount offset),
      input.cells[index.val].read.clk_high = input.message.clk_high ∧
      input.cells[index.val].read.clk_low = input.message.clk_low)
    (addresses : ∀ index : Fin (cellCount offset),
      Word.toBitVec64 input.cells[index.val].read.address =
        Word.toBitVec64 input.cells[(start offset).val].read.address + BitVec.ofNat 64 (8 * index.val))
    (queryBound : Word.isU64 input.message.address)
    (query : Word.toBitVec64 input.message.address =
      Word.toBitVec64 input.cells[(start offset).val].read.address + BitVec.ofNat 64 offset.val)
    (values : input.message.bytes = payload offset (256 : ZMod p)⁻¹ input.cells) : Spec input := by
  have base := (decoded (start offset)).1
  have queryPosition := address_offset (by have := offset.isLt; omega) base.1 base.2.2.1 queryBound query
  have positions (index : Fin (cellCount offset)) := address_offset
    (by have := index.isLt; have := offset.isLt; unfold cellCount at *; omega)
    base.1 base.2.2.1 (decoded index).1.1 (addresses index)
  have aligned := base.2.2.2.1
  have lower := base.2.1
  have offBound := offset.isLt
  have modulo : Word.toNat input.message.address % 8 = offset.val := by omega
  have window : Word.toNat input.message.address + 32 ≤ 2 ^ 48 := by
    let last : Fin (cellCount offset) := ⟨cellCount offset - 1, by have := cellCount_pos offset; omega⟩
    have lastWindow := (decoded last).1.2.2.1
    rw [positions last] at lastWindow
    dsimp only [last, cellCount] at lastWindow
    omega
  have bounded : ∀ index : Fin 32, input.message.bytes[index].val < 256 := by
    intro index
    rw [values]
    simp only [payload, Vector.getElem_ofFn, Fin.getElem_fin]
    exact (decoded (byteCell offset index)).2.1
      ⟨(offset.val + index.val) % 8, Nat.mod_lt _ (by decide)⟩
  refine ⟨⟨queryBound, by omega, window, bounded⟩, ⟨modulo, ?_⟩, ?_⟩
  · intro index
    refine ⟨(decoded index).1, (clocks index).1, (clocks index).2, ?_⟩
    simp only [Fin.getElem_fin]
    rw [positions index]
    omega
  · intro context observed
    rw [HostReadContext.readBytes?_eq_some_iff]
    refine ⟨by simp, ?_⟩
    intro index bound
    have small : index < 32 := by simpa using bound
    let byte : Fin 32 := ⟨index, small⟩
    let cell := byteCell offset byte
    let slot : Fin 8 := ⟨(offset.val + index) % 8, Nat.mod_lt _ (by decide)⟩
    have read := observed cell slot
    simp only [Fin.getElem_fin] at read
    rw [(decoded cell).2.2, Word.bytesValue_extract _ slot] at read
    have position : Word.toNat input.cells[cell.val].read.address + slot.val =
        Word.toNat input.message.address + index := by
      rw [positions cell]
      dsimp only [cell, byteCell, byte, slot]
      omega
    rw [position] at read
    simpa only [values, Vector.getElem_toList, Vector.getElem_map, payload, Vector.getElem_ofFn,
      cell, byteCell, byte, slot, Fin.getElem_fin] using read

/-- The circuit consumes precisely the minimal ordered cover, with no missing or extra cell. -/
theorem Spec.cell_addresses {offset : Fin 8} {input : Inputs offset (ZMod p)}
    (checked : Spec input) :
    (input.cells.toList.map fun cell => Word.toNat cell.read.address) =
      ((Model.Core.MemorySpan.mk (Word.toNat input.message.address) 32).cells.map (· * 8)) := by
  have length : (Word.toNat input.message.address + 32 - 1) / 8 + 1 -
      Word.toNat input.message.address / 8 = cellCount offset := by
    have alignment := checked.2.1.1
    unfold cellCount
    omega
  simp only [Model.Core.MemorySpan.cells, show ¬ (32 : ℕ) = 0 from by decide, if_false, length]
  apply List.ext_getElem
  · simp
  · intro index left right
    have bound : index < cellCount offset := by simpa using left
    have position := (checked.2.1.2 ⟨index, bound⟩).2.2.2
    simp only [Fin.getElem_fin] at position
    simp only [List.getElem_map, Vector.getElem_toList, List.getElem_range']
    omega

/-- Logical read addresses are distinct within a buffer. Overlap across buffers is shared by
`HostReadPlan`, which is responsible for the distinct physical inventory. -/
theorem Spec.cell_addresses_nodup {offset : Fin 8} {input : Inputs offset (ZMod p)}
    (checked : Spec input) :
    (input.cells.toList.map fun cell => Word.toNat cell.read.address).Nodup := by
  rw [checked.cell_addresses]
  exact (Model.Core.MemorySpan.nodup_cells _).map (fun _ _ same => by omega)

end SP1Clean.HostBuffer32
