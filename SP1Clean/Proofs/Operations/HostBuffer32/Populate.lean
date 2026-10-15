import SP1Clean.Proofs.Operations.HostBuffer32
import SP1Clean.Model.Core.MemoryTable

/-! # Constructing complete host buffers

The query computes its alignment variant, covering addresses, decoded low bytes, and payload.
Only canonical word values come from the supplying Memory history; no cover or byte witness is
chosen separately.
-/

namespace SP1Clean.HostBuffer32

open Circuit SP1Clean.Soundness.Target Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def selectedOffset (address : ℕ) : Fin 8 := ⟨address % 8, Nat.mod_lt _ (by decide)⟩

def readAt (address : ℕ) (clkHigh clkLow : ZMod p) (value : Word (ZMod p)) :
    HostRamReadChip.Message (ZMod p) :=
  let word := wordOffset address
  ⟨clkHigh, clkLow, word[0], word[1], word[2], value⟩

omit [Fact (2 ^ 17 < p)] in
private theorem readAt_address (address : ℕ) (clkHigh clkLow : ZMod p) (value : Word (ZMod p))
    (bound : address < 2 ^ 48) :
    (readAt address clkHigh clkLow value).address = wordOffset address := by
  have bound64 : address < 2 ^ 64 := by omega
  have last : (wordOffset (p := p) address)[3] = 0 := by
    simp only [wordOffset, bitVecToWord, circuit_norm]
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt bound64, Nat.div_eq_of_lt bound]
    simp only [Nat.zero_mod, Nat.cast_zero]
  ext index bound
  interval_cases index <;> simp only [readAt, HostRamReadChip.Message.address, circuit_norm, last]

def populate (address : ℕ) (clkHigh clkLow : ZMod p) (words : ℕ → Word (ZMod p)) :
    Inputs (selectedOffset address) (ZMod p) :=
  let cells := Vector.ofFn fun index : Fin (cellCount (selectedOffset address)) =>
    HostRamBytes.populate (readAt ((address / 8 + index.val) * 8) clkHigh clkLow
      (words (address / 8 + index.val)))
  ⟨⟨clkHigh, clkLow, wordOffset address, payload _ (256 : ZMod p)⁻¹ cells⟩, cells⟩

/-- Every in-window query with canonical covering words has a complete circuit input. -/
theorem populate_assumptions (address : ℕ) (clkHigh clkLow : ZMod p)
    (words : ℕ → Word (ZMod p)) (lower : 2 ^ 16 ≤ address) (upper : address + 32 ≤ 2 ^ 48)
    (bounded : ∀ cell ∈ (MemorySpan.mk address 32).cells, Word.isU64 (words cell)) :
    ProverAssumptions (selectedOffset address) (populate address clkHigh clkLow words) := by
  have cover (index : Fin (cellCount (selectedOffset address))) :
      address / 8 + index.val ∈ (MemorySpan.mk address 32).cells := by
    rw [MemorySpan.mem_cells]
    have := index.isLt
    simp only [cellCount, selectedOffset] at this
    dsimp only
    omega
  have window (index : Fin (cellCount (selectedOffset address))) :=
    MemorySpan.cell_in_window _ lower upper _ (cover index)
  have encoded (index : Fin (cellCount (selectedOffset address))) :
      ((populate address clkHigh clkLow words).cells[index.val]).read.address =
        wordOffset ((address / 8 + index.val) * 8) := by
    simp only [populate, Vector.getElem_ofFn, HostRamBytes.populate]
    apply readAt_address
    have := window index
    omega
  have base : Word.toBitVec64 ((populate address clkHigh clkLow words).cells[
      (start (selectedOffset address)).val]).read.address = BitVec.ofNat 64 (address / 8 * 8) := by
    rw [encoded]
    simp only [start, Nat.add_zero, wordOffset, toBitVec64_bitVecToWord]
  refine ⟨?_, isU64_bitVecToWord _, ?_, rfl⟩
  · intro index
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [populate, Vector.getElem_ofFn]
      apply HostRamBytes.populate_assumptions
      have position := readAt_address ((address / 8 + index.val) * 8) clkHigh clkLow
        (words (address / 8 + index.val)) (by have := window index; omega)
      change (readAt _ clkHigh clkLow (words _)).Valid
      change Word.isU64 _ ∧ _
      rw [show (readAt ((address / 8 + index.val) * 8) clkHigh clkLow
          (words (address / 8 + index.val))).address = _ from position]
      have natural := endpoint_toNat (p := p) ((address / 8 + index.val) * 8) (by
        have := window index
        omega)
      change Word.isU64 (wordOffset _) ∧ _
      rw [show Word.toNat (wordOffset (p := p) ((address / 8 + index.val) * 8)) = _ from natural]
      exact ⟨isU64_bitVecToWord _, (window index).1, by have := window index; omega,
        Nat.mul_mod_left _ _, bounded _ (cover index)⟩
    · simp only [populate, Vector.getElem_ofFn, HostRamBytes.populate, readAt]
    · simp only [populate, Vector.getElem_ofFn, HostRamBytes.populate, readAt]
    · rw [encoded, base]
      simp only [wordOffset, toBitVec64_bitVecToWord]
      rw [← BitVec.ofNat_add]
      congr 1
      omega
  · rw [base]
    change Word.toBitVec64 (wordOffset address) = _
    simp only [wordOffset, toBitVec64_bitVecToWord, selectedOffset]
    rw [← BitVec.ofNat_add]
    congr 1
    omega

end SP1Clean.HostBuffer32
