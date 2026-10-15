module

public import SP1Clean.Semantics.Specs.BitwiseBytes
public import SP1Clean.Semantics.Specs.U16toU8Safe
import Mathlib.Tactic.FinCases

/-! # Word-level bitwise contract

The complete byte certificate retains the operand decomposition and result bytes needed for
arbitrary-row completeness. Pure readout lemmas derive operand/result ranges and RV64 bitwise
meaning. Padding leaves all byte columns free.
-/

@[expose] public section

namespace SP1Clean.BitwiseU16Operation

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The two operand words, the (chip-owned) decomposition + result column struct, the opcode selector
(AND=0, OR=1, XOR=2), and the `is_real` gate — SP1's `eval` params verbatim. -/
structure Inputs (F : Type) where
  /-- First operand in four 16-bit limbs. -/
  b : fields 4 F
  /-- Second operand in four 16-bit limbs. -/
  c : fields 4 F
  /-- Committed byte decompositions and result bytes. -/
  cols : Columns F
  /-- AND = 0, OR = 1, XOR = 2. -/
  opcode : F
  /-- One for an active row, zero for padding. -/
  is_real : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- The eight little-endian bytes of a word given its low-byte columns: `byte[2i] = low[i]`,
`byte[2i+1] = (w[i] − low[i])·256⁻¹` (SP1's `eval_u16_to_u8_unsafe`). Reducible so it unifies with the
byte expressions `main` feeds the composed `BitwiseOperation`. -/
@[reducible] def decompBytes (w : Word (ZMod p)) (low : Circuits.Types.U16toU8Operation (ZMod p)) :
    Vector (ZMod p) 8 :=
  #v[low.low_bytes[0], (w[0] - low.low_bytes[0]) * (256 : ZMod p)⁻¹,
     low.low_bytes[1], (w[1] - low.low_bytes[1]) * (256 : ZMod p)⁻¹,
     low.low_bytes[2], (w[2] - low.low_bytes[2]) * (256 : ZMod p)⁻¹,
     low.low_bytes[3], (w[3] - low.low_bytes[3]) * (256 : ZMod p)⁻¹]

/-- Reassemble the eight result bytes into a four-limb word. -/
def resultWord (r : Vector (ZMod p) 8) : Word (ZMod p) :=
  #v[r[0] + r[1] * 256, r[2] + r[3] * 256, r[4] + r[5] * 256, r[6] + r[7] * 256]

/-- Opcode selects AND/OR/XOR and the row gate is binary. Active byte lookups establish
operand bounds; padding imposes no operand-range obligation. -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  input.opcode.val < 3 ∧
    (input.is_real = 0 ∨ input.is_real = 1)

/-- Structural contract: the composed `BitwiseOperation.Spec` on the two byte decompositions — on a
real row the eight decomposed bytes are genuine bytes and each result byte is their per-opcode bitwise
combination. Equivalent to the constraint list (so completeness holds). The whole-word semantic readout
is `result_semantic`. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  SP1Clean.BitwiseOperation.Spec
    (⟨decompBytes input.b input.cols.b_low_bytes, decompBytes input.c input.cols.c_low_bytes,
      input.cols.bitwise_operation, input.opcode, input.is_real⟩ :
      SP1Clean.BitwiseOperation.Inputs (ZMod p))

/-- A limb's value splits as its low byte plus 256× its high byte, given both are bytes. -/
lemma limb_split {w low : ZMod p} (hlo : low.val < 256)
    (hhi : ((w - low) * (256 : ZMod p)⁻¹).val < 256) :
    w.val = low.val + ((w - low) * (256 : ZMod p)⁻¹).val * 256 := by
  conv_lhs => rw [U16toU8OperationSafe.reassemble w low]
  exact val_lo_add_hi hlo hhi

/-- A limb of `w` splits as its two decomposed bytes (low + 256·high), given both are bytes. Keeps the
split in `decompBytes`-indexed form so it unifies syntactically with `toBitVec64_asm8`. -/
lemma decomp_limb_split {w : Word (ZMod p)} {low : Circuits.Types.U16toU8Operation (ZMod p)} (i : Fin 4)
    (hlo : (decompBytes w low)[2 * (i : ℕ)].val < 256)
    (hhi : (decompBytes w low)[2 * (i : ℕ) + 1].val < 256) :
    w[(i : ℕ)].val
      = (decompBytes w low)[2 * (i : ℕ)].val + (decompBytes w low)[2 * (i : ℕ) + 1].val * 256 := by
  fin_cases i <;>
    · simp only [decompBytes, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ] at hlo hhi ⊢
      exact limb_split hlo hhi

/-- Active byte certificates bound both operands, without caller-supplied word bounds. -/
theorem operands_isU64 {input : Inputs (ZMod p)} (hir : input.is_real = 1)
    (hs : Spec input) : Word.isU64 input.b ∧ Word.isU64 input.c := by
  have hbytes := (hs hir).1
  have bound (w : Word (ZMod p)) (low : Circuits.Types.U16toU8Operation (ZMod p))
      (hw : ∀ j : Fin 8, (decompBytes w low)[(j : ℕ)].val < 256) : Word.isU64 w := by
    intro i
    have hlo : (decompBytes w low)[2 * (i : ℕ)].val < 256 := hw ⟨2 * (i : ℕ), by omega⟩
    have hhi : (decompBytes w low)[2 * (i : ℕ) + 1].val < 256 := hw ⟨2 * (i : ℕ) + 1, by omega⟩
    change w[(i : ℕ)].val < 2 ^ 16
    rw [decomp_limb_split i hlo hhi]
    omega
  exact ⟨bound _ _ (fun j => (hbytes j).1), bound _ _ (fun j => (hbytes j).2)⟩

/-- **Whole-word readout.** From the structural `Spec` on a real row, the reassembled result word is
the AND/OR/XOR (as 64-bit values) of the two operands. The `BitwiseChip` soundness consumes this. -/
theorem result_semantic (input : Inputs (ZMod p))
    (hir : input.is_real = 1) (hs : Spec input) :
    (input.opcode = 0 →
      Word.toBitVec64 (resultWord input.cols.bitwise_operation.result)
        = Word.toBitVec64 input.b &&& Word.toBitVec64 input.c) ∧
    (input.opcode = 1 →
      Word.toBitVec64 (resultWord input.cols.bitwise_operation.result)
        = Word.toBitVec64 input.b ||| Word.toBitVec64 input.c) ∧
    (input.opcode = 2 →
      Word.toBitVec64 (resultWord input.cols.bitwise_operation.result)
        = Word.toBitVec64 input.b ^^^ Word.toBitVec64 input.c) := by
  set b := input.b with hb_def
  set c := input.c with hc_def
  set lb := input.cols.b_low_bytes with hlb_def
  set lc := input.cols.c_low_bytes with hlc_def
  set r := input.cols.bitwise_operation.result with hr_def
  obtain ⟨hbnd, harms⟩ := hs hir
  have bbB : ∀ i : Fin 8, (decompBytes b lb)[(i : ℕ)].val < 256 := fun i => (hbnd i).1
  have bbC : ∀ i : Fin 8, (decompBytes c lc)[(i : ℕ)].val < 256 := fun i => (hbnd i).2
  -- the two operand words, packaged as `BitVec.ofNat` of the base-256 assembly of their bytes
  have hsplitB : Word.toBitVec64 b = BitVec.ofNat 64 (asm8
      (decompBytes b lb)[0].val (decompBytes b lb)[1].val (decompBytes b lb)[2].val
      (decompBytes b lb)[3].val (decompBytes b lb)[4].val (decompBytes b lb)[5].val
      (decompBytes b lb)[6].val (decompBytes b lb)[7].val) :=
    toBitVec64_asm8 b _ _ _ _ _ _ _ _
      (decomp_limb_split 0 (bbB 0) (bbB 1)) (decomp_limb_split 1 (bbB 2) (bbB 3))
      (decomp_limb_split 2 (bbB 4) (bbB 5)) (decomp_limb_split 3 (bbB 6) (bbB 7))
  have hsplitC : Word.toBitVec64 c = BitVec.ofNat 64 (asm8
      (decompBytes c lc)[0].val (decompBytes c lc)[1].val (decompBytes c lc)[2].val
      (decompBytes c lc)[3].val (decompBytes c lc)[4].val (decompBytes c lc)[5].val
      (decompBytes c lc)[6].val (decompBytes c lc)[7].val) :=
    toBitVec64_asm8 c _ _ _ _ _ _ _ _
      (decomp_limb_split 0 (bbC 0) (bbC 1)) (decomp_limb_split 1 (bbC 2) (bbC 3))
      (decomp_limb_split 2 (bbC 4) (bbC 5)) (decomp_limb_split 3 (bbC 6) (bbC 7))
  -- per-opcode resolver: from the arm's byte equalities, run the keystone reassembly
  have core : ∀ (op : ℕ), op < 3 →
      (∀ i : Fin 8, r[(i : ℕ)].val
        = byteOp op (decompBytes b lb)[(i : ℕ)].val (decompBytes c lc)[(i : ℕ)].val) →
      Word.toBitVec64 (resultWord r) = bitOp64 op (Word.toBitVec64 b) (Word.toBitVec64 c) := by
    intro op hop hbyteop
    have hr_lt : ∀ i : Fin 8, r[(i : ℕ)].val < 256 := fun i => by
      rw [hbyteop i]; exact byteOp_lt256 _ _ _ (bbB i) (bbC i)
    have hres : Word.toBitVec64 (resultWord r) = BitVec.ofNat 64 (asm8
        r[0].val r[1].val r[2].val r[3].val r[4].val r[5].val r[6].val r[7].val) := by
      refine toBitVec64_asm8 (resultWord r) _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ <;>
        simp only [resultWord, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ]
      · exact val_lo_add_hi (hr_lt 0) (hr_lt 1)
      · exact val_lo_add_hi (hr_lt 2) (hr_lt 3)
      · exact val_lo_add_hi (hr_lt 4) (hr_lt 5)
      · exact val_lo_add_hi (hr_lt 6) (hr_lt 7)
    rw [hres, hsplitB, hsplitC]
    exact reassemble_byteOp op hop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (bbB 0) (bbB 1) (bbB 2) (bbB 3) (bbB 4) (bbB 5) (bbB 6)
      (bbC 0) (bbC 1) (bbC 2) (bbC 3) (bbC 4) (bbC 5) (bbC 6)
      (hbyteop 0) (hbyteop 1) (hbyteop 2) (hbyteop 3) (hbyteop 4) (hbyteop 5) (hbyteop 6) (hbyteop 7)
  refine ⟨fun h0 => ?_, fun h1 => ?_, fun h2 => ?_⟩
  · have := core 0 (by omega) (fun i => by rw [byteOp_zero]; exact (harms.1 h0) i)
    rwa [bitOp64_zero] at this
  · have := core 1 (by omega) (fun i => by rw [byteOp_one]; exact (harms.2.1 h1) i)
    rwa [bitOp64_one] at this
  · have := core 2 (by omega) (fun i => by rw [byteOp_two]; exact (harms.2.2 h2) i)
    rwa [bitOp64_two] at this

/-- The active result is a bounded word for each supported bitwise opcode. -/
theorem resultWord_isU64 {inp : BitwiseU16Operation.Inputs (ZMod p)}
    (hir : inp.is_real = 1) (hs : BitwiseU16Operation.Spec inp)
    (hop : inp.opcode = 0 ∨ inp.opcode = 1 ∨ inp.opcode = 2) :
    Word.isU64 (BitwiseU16Operation.resultWord inp.cols.bitwise_operation.result) := by
  obtain ⟨hbnd, harm0, harm1, harm2⟩ := hs hir
  have hr_lt : ∀ i : Fin 8, inp.cols.bitwise_operation.result[(i : ℕ)].val < 256 := fun i => by
    rcases hop with h | h | h
    · rw [show inp.cols.bitwise_operation.result[(i : ℕ)].val = _ from harm0 h i]
      exact byteOp_lt256 0 _ _ (hbnd i).1 (hbnd i).2
    · rw [show inp.cols.bitwise_operation.result[(i : ℕ)].val = _ from harm1 h i]
      exact byteOp_lt256 1 _ _ (hbnd i).1 (hbnd i).2
    · rw [show inp.cols.bitwise_operation.result[(i : ℕ)].val = _ from harm2 h i]
      exact byteOp_lt256 2 _ _ (hbnd i).1 (hbnd i).2
  have b : ∀ (i : ℕ) (hi : i < 8), inp.cols.bitwise_operation.result[i].val < 256 :=
    fun i hi => hr_lt ⟨i, hi⟩
  refine Word.isU64_of_cases ?_ ?_ ?_ ?_ <;>
    simp only [BitwiseU16Operation.resultWord, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ]
  · have h0 := b 0 (by omega); have h1 := b 1 (by omega); rw [val_lo_add_hi h0 h1]; omega
  · have h0 := b 2 (by omega); have h1 := b 3 (by omega); rw [val_lo_add_hi h0 h1]; omega
  · have h0 := b 4 (by omega); have h1 := b 5 (by omega); rw [val_lo_add_hi h0 h1]; omega
  · have h0 := b 6 (by omega); have h1 := b 7 (by omega); rw [val_lo_add_hi h0 h1]; omega

end SP1Clean.BitwiseU16Operation
