import SP1Clean.Soundness.GroundingAdapter

/-! # Aligned RAM-cell updates

SP1's Memory bus represents RAM as aligned 8-byte cells, while Sail's architectural memory is
byte-addressed.  This module is the small semantic bridge between those views:

* `cellBytesToWord` assembles one little-endian cell;
* `updatedCellBytes` applies a committed byte-range `MemWrite` to that cell;
* `RamCellUpdate` states that the resulting bytes are the word pushed on the Memory bus; and
* `ramCellPost_of_update` combines that relation with `RowEffect.mem` and the grounded prior-cell
  pull to authenticate the pushed post-state cell.

The definition is deliberately independent of any concrete load/store chip.  Subword store chips
prove `RamCellUpdate` from their existing read-modify-write equations; SD proves it from its full
word write.
-/

namespace SP1Clean.Soundness

open SP1Clean.Semantics
open SP1Clean.Soundness.Target
open SP1Clean.Channels (MemoryMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The canonical byte address of a RAM cell is exactly eight times its cell index. -/
theorem RamCell.baseAddr_toNat (cell : RamCell) :
    cell.baseAddr.toNat = cell.toNat * 8 := by
  rw [RamCell.baseAddr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have := cell.isLt
  omega

/-- Assemble eight little-endian bytes into the Memory bus's 64-bit cell value. -/
def cellBytesToWord (bytes : Vector (BitVec 8) 8) : BitVec 64 :=
  bytes[7] ++ bytes[6] ++ bytes[5] ++ bytes[4] ++
    bytes[3] ++ bytes[2] ++ bytes[1] ++ bytes[0]

/-- The eight little-endian bytes of one 64-bit Memory-bus value. -/
def wordBytes (word : BitVec 64) : Vector (BitVec 8) 8 :=
  #v[word.extractLsb' 0 8, word.extractLsb' 8 8, word.extractLsb' 16 8,
    word.extractLsb' 24 8, word.extractLsb' 32 8, word.extractLsb' 40 8,
    word.extractLsb' 48 8, word.extractLsb' 56 8]

/-- A field element decomposed into two range-checked bytes has the canonical base-256
decomposition of its representative. -/
theorem bytePair_unique {u low high : ZMod p}
    (lowBound : low.val < 256) (highBound : high.val < 256)
    (decomposed : u = low + high * 256) :
    low.val = u.val % 256 ∧ high.val = u.val / 256 := by
  have value := congrArg ZMod.val decomposed
  rw [val_lo_add_hi lowBound highBound] at value
  have division := Nat.mod_add_div u.val 256
  have remainderBound := Nat.mod_lt u.val (by omega : 0 < 256)
  constructor <;> omega

/-- The low byte of a range-checked base-256 decomposition. -/
theorem lowByte_eq {u low high : ZMod p}
    (lowBound : low.val < 256) (highBound : high.val < 256)
    (decomposed : u = low + high * 256) :
    BitVec.ofNat 8 u.val = BitVec.ofNat 8 low.val := by
  have unique := bytePair_unique lowBound highBound decomposed
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- The high byte of a range-checked base-256 decomposition. -/
theorem highByte_eq {u low high : ZMod p}
    (lowBound : low.val < 256) (highBound : high.val < 256)
    (decomposed : u = low + high * 256) :
    BitVec.ofNat 8 (u.val >>> 8) = BitVec.ofNat 8 high.val := by
  have unique := bytePair_unique lowBound highBound decomposed
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  norm_num [Nat.shiftRight_eq_div_pow]
  omega

omit [Fact (2 ^ 17 < p)] in
/-- Fixed-width closing lemma used by the eight word-byte projections below.  Keeping the
`Word.toBitVec64` conversion opaque here avoids asking elaboration or the kernel to normalize a
64-bit `ofNat` through every caller. -/
private theorem extractByte_eq_of_shift (word : Word (ZMod p))
    (bound : Word.isU64 word) (start value : ℕ)
    (shift : Word.toNat word >>> start % 256 = value % 256) :
    (Word.toBitVec64 word).extractLsb' start 8 = BitVec.ofNat 8 value := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, Word.toBitVec64_toNat bound,
    BitVec.toNat_ofNat]
  norm_num
  exact shift

omit [Fact (2 ^ 17 < p)] in
/-- Byte zero of a canonical four-limb word. -/
theorem wordBytes_zero (word : Word (ZMod p)) (bound : Word.isU64 word) :
    (wordBytes (Word.toBitVec64 word))[0] = BitVec.ofNat 8 word[0].val := by
  change (Word.toBitVec64 word).extractLsb' 0 8 = _
  apply extractByte_eq_of_shift word bound
  rw [Word.toNat_def]
  norm_num [Nat.shiftRight_eq_div_pow]
  omega

omit [Fact (2 ^ 17 < p)] in
/-- Byte one of a canonical four-limb word. -/
theorem wordBytes_one (word : Word (ZMod p)) (bound : Word.isU64 word) :
    (wordBytes (Word.toBitVec64 word))[1] =
      BitVec.ofNat 8 (word[0].val >>> 8) := by
  change (Word.toBitVec64 word).extractLsb' 8 8 = _
  apply extractByte_eq_of_shift word bound
  rw [Word.toNat_def]
  norm_num [Nat.shiftRight_eq_div_pow]
  have limbs := Word.lt_cases_of_isU64 bound
  omega

omit [Fact (2 ^ 17 < p)] in
/-- Byte two of a canonical four-limb word. -/
theorem wordBytes_two (word : Word (ZMod p)) (bound : Word.isU64 word) :
    (wordBytes (Word.toBitVec64 word))[2] = BitVec.ofNat 8 word[1].val := by
  change (Word.toBitVec64 word).extractLsb' 16 8 = _
  apply extractByte_eq_of_shift word bound
  rw [Word.toNat_def]
  norm_num [Nat.shiftRight_eq_div_pow]
  have limbs := Word.lt_cases_of_isU64 bound
  omega

omit [Fact (2 ^ 17 < p)] in
/-- Byte three of a canonical four-limb word. -/
theorem wordBytes_three (word : Word (ZMod p)) (bound : Word.isU64 word) :
    (wordBytes (Word.toBitVec64 word))[3] =
      BitVec.ofNat 8 (word[1].val >>> 8) := by
  change (Word.toBitVec64 word).extractLsb' 24 8 = _
  apply extractByte_eq_of_shift word bound
  rw [Word.toNat_def]
  norm_num [Nat.shiftRight_eq_div_pow]
  have limbs := Word.lt_cases_of_isU64 bound
  omega

omit [Fact (2 ^ 17 < p)] in
/-- Byte four of a canonical four-limb word. -/
theorem wordBytes_four (word : Word (ZMod p)) (bound : Word.isU64 word) :
    (wordBytes (Word.toBitVec64 word))[4] = BitVec.ofNat 8 word[2].val := by
  change (Word.toBitVec64 word).extractLsb' 32 8 = _
  apply extractByte_eq_of_shift word bound
  rw [Word.toNat_def]
  norm_num [Nat.shiftRight_eq_div_pow]
  have limbs := Word.lt_cases_of_isU64 bound
  omega

omit [Fact (2 ^ 17 < p)] in
/-- Byte five of a canonical four-limb word. -/
theorem wordBytes_five (word : Word (ZMod p)) (bound : Word.isU64 word) :
    (wordBytes (Word.toBitVec64 word))[5] =
      BitVec.ofNat 8 (word[2].val >>> 8) := by
  change (Word.toBitVec64 word).extractLsb' 40 8 = _
  apply extractByte_eq_of_shift word bound
  rw [Word.toNat_def]
  norm_num [Nat.shiftRight_eq_div_pow]
  have limbs := Word.lt_cases_of_isU64 bound
  omega

omit [Fact (2 ^ 17 < p)] in
/-- Byte six of a canonical four-limb word. -/
theorem wordBytes_six (word : Word (ZMod p)) (bound : Word.isU64 word) :
    (wordBytes (Word.toBitVec64 word))[6] = BitVec.ofNat 8 word[3].val := by
  change (Word.toBitVec64 word).extractLsb' 48 8 = _
  apply extractByte_eq_of_shift word bound
  rw [Word.toNat_def]
  norm_num [Nat.shiftRight_eq_div_pow]
  have limbs := Word.lt_cases_of_isU64 bound
  omega

omit [Fact (2 ^ 17 < p)] in
/-- Byte seven of a canonical four-limb word. -/
theorem wordBytes_seven (word : Word (ZMod p)) (bound : Word.isU64 word) :
    (wordBytes (Word.toBitVec64 word))[7] =
      BitVec.ofNat 8 (word[3].val >>> 8) := by
  change (Word.toBitVec64 word).extractLsb' 56 8 = _
  apply extractByte_eq_of_shift word bound
  rw [Word.toNat_def]
  norm_num [Nat.shiftRight_eq_div_pow]
  have limbs := Word.lt_cases_of_isU64 bound
  omega

omit [Fact (2 ^ 17 < p)] in
/-- Direct extraction form of `wordBytes_zero`, convenient when the surrounding vector index
carries a non-canonical proof term. -/
theorem wordByte_zero (word : Word (ZMod p)) (bound : Word.isU64 word) :
    (Word.toBitVec64 word).extractLsb' 0 8 =
      BitVec.ofNat 8 word[0].val :=
  wordBytes_zero word bound

omit [Fact (2 ^ 17 < p)] in
/-- Direct extraction form of `wordBytes_one`. -/
theorem wordByte_one (word : Word (ZMod p)) (bound : Word.isU64 word) :
    (Word.toBitVec64 word).extractLsb' 8 8 =
      BitVec.ofNat 8 (word[0].val >>> 8) :=
  wordBytes_one word bound

omit [Fact (2 ^ 17 < p)] in
/-- Direct extraction form of `wordBytes_two`. -/
theorem wordByte_two (word : Word (ZMod p)) (bound : Word.isU64 word) :
    (Word.toBitVec64 word).extractLsb' 16 8 =
      BitVec.ofNat 8 word[1].val :=
  wordBytes_two word bound

omit [Fact (2 ^ 17 < p)] in
/-- Direct extraction form of `wordBytes_three`. -/
theorem wordByte_three (word : Word (ZMod p)) (bound : Word.isU64 word) :
    (Word.toBitVec64 word).extractLsb' 24 8 =
      BitVec.ofNat 8 (word[1].val >>> 8) :=
  wordBytes_three word bound

omit [Fact (2 ^ 17 < p)] in
/-- Direct extraction form of `wordBytes_four`. -/
theorem wordByte_four (word : Word (ZMod p)) (bound : Word.isU64 word) :
    (Word.toBitVec64 word).extractLsb' 32 8 =
      BitVec.ofNat 8 word[2].val :=
  wordBytes_four word bound

omit [Fact (2 ^ 17 < p)] in
/-- Direct extraction form of `wordBytes_five`. -/
theorem wordByte_five (word : Word (ZMod p)) (bound : Word.isU64 word) :
    (Word.toBitVec64 word).extractLsb' 40 8 =
      BitVec.ofNat 8 (word[2].val >>> 8) :=
  wordBytes_five word bound

omit [Fact (2 ^ 17 < p)] in
/-- Direct extraction form of `wordBytes_six`. -/
theorem wordByte_six (word : Word (ZMod p)) (bound : Word.isU64 word) :
    (Word.toBitVec64 word).extractLsb' 48 8 =
      BitVec.ofNat 8 word[3].val :=
  wordBytes_six word bound

omit [Fact (2 ^ 17 < p)] in
/-- Direct extraction form of `wordBytes_seven`. -/
theorem wordByte_seven (word : Word (ZMod p)) (bound : Word.isU64 word) :
    (Word.toBitVec64 word).extractLsb' 56 8 =
      BitVec.ofNat 8 (word[3].val >>> 8) :=
  wordBytes_seven word bound

/-- Splitting a 64-bit word into bytes and reassembling it is the identity. -/
theorem cellBytesToWord_wordBytes (word : BitVec 64) :
    cellBytesToWord (wordBytes word) = word := by
  simp [cellBytesToWord, wordBytes]
  bv_decide

/-- Byte `i` occupies bits `[8*i, 8*i+8)` of the assembled cell. -/
theorem extractLsb_cellBytesToWord (bytes : Vector (BitVec 8) 8) (i : Fin 8) :
    (cellBytesToWord bytes).extractLsb' (8 * i.val) 8 = bytes[i] := by
  fin_cases i <;> simp only [cellBytesToWord]
  · rw [BitVec.extractLsb'_append_eq_right]
    simp
  · rw [BitVec.extractLsb'_append_eq_of_le (by omega), BitVec.extractLsb'_append_eq_right]
    simp
  · rw [BitVec.extractLsb'_append_eq_of_le (by omega),
      BitVec.extractLsb'_append_eq_of_le (by omega), BitVec.extractLsb'_append_eq_right]
    simp
  · rw [BitVec.extractLsb'_append_eq_of_le (by omega),
      BitVec.extractLsb'_append_eq_of_le (by omega), BitVec.extractLsb'_append_eq_of_le (by omega),
      BitVec.extractLsb'_append_eq_right]
    simp
  · rw [BitVec.extractLsb'_append_eq_of_le (by omega),
      BitVec.extractLsb'_append_eq_of_le (by omega), BitVec.extractLsb'_append_eq_of_le (by omega),
      BitVec.extractLsb'_append_eq_of_le (by omega), BitVec.extractLsb'_append_eq_right]
    simp
  · rw [BitVec.extractLsb'_append_eq_of_le (by omega),
      BitVec.extractLsb'_append_eq_of_le (by omega), BitVec.extractLsb'_append_eq_of_le (by omega),
      BitVec.extractLsb'_append_eq_of_le (by omega), BitVec.extractLsb'_append_eq_of_le (by omega),
      BitVec.extractLsb'_append_eq_right]
    simp
  · rw [BitVec.extractLsb'_append_eq_of_le (by omega),
      BitVec.extractLsb'_append_eq_of_le (by omega), BitVec.extractLsb'_append_eq_of_le (by omega),
      BitVec.extractLsb'_append_eq_of_le (by omega), BitVec.extractLsb'_append_eq_of_le (by omega),
      BitVec.extractLsb'_append_eq_of_le (by omega), BitVec.extractLsb'_append_eq_right]
    simp
  · rw [BitVec.extractLsb'_append_eq_of_le (by omega),
      BitVec.extractLsb'_append_eq_of_le (by omega), BitVec.extractLsb'_append_eq_of_le (by omega),
      BitVec.extractLsb'_append_eq_of_le (by omega), BitVec.extractLsb'_append_eq_of_le (by omega),
      BitVec.extractLsb'_append_eq_of_le (by omega), BitVec.extractLsb'_append_eq_of_le (by omega)]
    simp

/-- Little-endian byte assembly loses no information. -/
theorem cellBytesToWord_injective : Function.Injective cellBytesToWord := by
  intro left right assembled
  apply Vector.ext
  intro i hi
  let index : Fin 8 := ⟨i, hi⟩
  change left[index] = right[index]
  have extracted := congrArg
    (fun word : BitVec 64 => word.extractLsb' (8 * index.val) 8) assembled
  simpa only [extractLsb_cellBytesToWord] using extracted

/-- A byte vector assembling to `word` is its canonical little-endian decomposition. -/
theorem eq_wordBytes_of_cellBytesToWord_eq {bytes : Vector (BitVec 8) 8}
    {word : BitVec 64} (assembled : cellBytesToWord bytes = word) :
    bytes = wordBytes word :=
  cellBytesToWord_injective (assembled.trans (cellBytesToWord_wordBytes word).symm)

/-- Apply a byte-addressed committed write to one aligned cell's prior bytes. -/
def updatedCellBytes (mw : Trace.MemWrite (ZMod p)) (cell : RamCell)
    (old : Vector (BitVec 8) 8) : Vector (BitVec 8) 8 :=
  Vector.ofFn fun i =>
    let address := cell.baseAddr.toNat + i.val
    if mw.covers address then mw.byteAt address else old[i]

omit [Fact p.Prime] in
@[simp] theorem updatedCellBytes_getElem_val (mw : Trace.MemWrite (ZMod p)) (cell : RamCell)
    (old : Vector (BitVec 8) 8) (i : Fin 8) :
    (updatedCellBytes mw cell old)[i.val] =
      if mw.covers (cell.baseAddr.toNat + i.val) then
        mw.byteAt (cell.baseAddr.toNat + i.val) else old[i.val] := by
  simp [updatedCellBytes]

omit [Fact p.Prime] in
/-- Fin-indexed spelling retained for proofs that carry the byte position as a typed index. -/
theorem updatedCellBytes_getElem (mw : Trace.MemWrite (ZMod p)) (cell : RamCell)
    (old : Vector (BitVec 8) 8) (i : Fin 8) :
    (updatedCellBytes mw cell old)[i] =
      if mw.covers (cell.baseAddr.toNat + i.val) then
        mw.byteAt (cell.baseAddr.toNat + i.val) else old[i] := by
  change (updatedCellBytes mw cell old)[i.val] =
    if mw.covers (cell.baseAddr.toNat + i.val) then
      mw.byteAt (cell.baseAddr.toNat + i.val) else old[i.val]
  exact updatedCellBytes_getElem_val mw cell old i

/-- The canonical full-cell result of placing a contiguous store value at byte offset `offset`.
This is the fixed-width bit-vector form to which the four store chips reduce their respective
read-modify-write column equations. -/
def patchedCellBytes (old : BitVec 64) (mw : Trace.MemWrite (ZMod p))
    (offset width : ℕ) : Vector (BitVec 8) 8 :=
  Vector.ofFn fun i =>
    if offset ≤ i.val ∧ i.val < offset + width then
      (Word.toBitVec64 mw.value).extractLsb' (8 * (i.val - offset)) 8
    else
      (wordBytes old)[i]

omit [Fact (2 ^ 17 < p)] in
@[simp] theorem patchedCellBytes_getElem_val (old : BitVec 64)
    (mw : Trace.MemWrite (ZMod p)) (offset width : ℕ) (i : Fin 8) :
    (patchedCellBytes old mw offset width)[i.val] =
      if offset ≤ i.val ∧ i.val < offset + width then
        (Word.toBitVec64 mw.value).extractLsb' (8 * (i.val - offset)) 8
      else
        (wordBytes old)[i.val] := by
  simp [patchedCellBytes]

omit [Fact (2 ^ 17 < p)] in
/-- Fin-indexed spelling retained for the fixed eight-byte case splits below. -/
theorem patchedCellBytes_getElem (old : BitVec 64)
    (mw : Trace.MemWrite (ZMod p)) (offset width : ℕ) (i : Fin 8) :
    (patchedCellBytes old mw offset width)[i] =
      if offset ≤ i.val ∧ i.val < offset + width then
        (Word.toBitVec64 mw.value).extractLsb' (8 * (i.val - offset)) 8
      else
        (wordBytes old)[i] := by
  change (patchedCellBytes old mw offset width)[i.val] =
    if offset ≤ i.val ∧ i.val < offset + width then
      (Word.toBitVec64 mw.value).extractLsb' (8 * (i.val - offset)) 8
    else
      (wordBytes old)[i.val]
  exact patchedCellBytes_getElem_val old mw offset width i

omit [Fact (2 ^ 17 < p)] in
/-- Patching all eight bytes at offset zero is exactly the committed store word. -/
theorem patchedCellBytes_zero_eight (old : BitVec 64)
    (mw : Trace.MemWrite (ZMod p)) :
    patchedCellBytes old mw 0 8 = wordBytes (Word.toBitVec64 mw.value) := by
  apply Vector.ext
  intro i hi
  let index : Fin 8 := ⟨i, hi⟩
  change (patchedCellBytes old mw 0 8)[index] = (wordBytes (Word.toBitVec64 mw.value))[index]
  interval_cases i <;> simp [index, patchedCellBytes, wordBytes]

omit [Fact (2 ^ 17 < p)] in
/-- The canonical four-byte patch at offset zero, expressed by the limb equalities used by SP1's
SW read-modify-write columns. -/
theorem patchedCellBytes_zero_four
    (address : Vector (ZMod p) 3)
    (old stored new : Word (ZMod p))
    (oldBound : Word.isU64 old) (storedBound : Word.isU64 stored)
    (newBound : Word.isU64 new)
    (new0 : new[0] = stored[0]) (new1 : new[1] = stored[1])
    (new2 : new[2] = old[2]) (new3 : new[3] = old[3]) :
    cellBytesToWord
        (patchedCellBytes (Word.toBitVec64 old)
          ⟨address, stored, 4⟩ 0 4) =
      Word.toBitVec64 new := by
  rw [← cellBytesToWord_wordBytes (Word.toBitVec64 new)]
  apply congrArg cellBytesToWord
  apply Vector.ext
  intro i hi
  let index : Fin 8 := ⟨i, hi⟩
  change (patchedCellBytes (Word.toBitVec64 old) ⟨address, stored, 4⟩ 0 4)[index] =
    (wordBytes (Word.toBitVec64 new))[index]
  interval_cases i
  · dsimp only [index]
    rw [patchedCellBytes_getElem, if_pos (by change 0 ≤ 0 ∧ 0 < 0 + 4; omega)]
    norm_num
    change (Word.toBitVec64 stored).extractLsb' 0 8 = (Word.toBitVec64 new).extractLsb' 0 8
    rw [wordByte_zero stored storedBound, wordByte_zero new newBound, new0]
  · dsimp only [index]
    rw [patchedCellBytes_getElem, if_pos (by change 0 ≤ 1 ∧ 1 < 0 + 4; omega)]
    norm_num
    change (Word.toBitVec64 stored).extractLsb' 8 8 = (Word.toBitVec64 new).extractLsb' 8 8
    rw [wordByte_one stored storedBound, wordByte_one new newBound, new0]
  · dsimp only [index]
    rw [patchedCellBytes_getElem, if_pos (by change 0 ≤ 2 ∧ 2 < 0 + 4; omega)]
    norm_num
    change (Word.toBitVec64 stored).extractLsb' 16 8 = (Word.toBitVec64 new).extractLsb' 16 8
    rw [wordByte_two stored storedBound, wordByte_two new newBound, new1]
  · dsimp only [index]
    rw [patchedCellBytes_getElem, if_pos (by change 0 ≤ 3 ∧ 3 < 0 + 4; omega)]
    norm_num
    change (Word.toBitVec64 stored).extractLsb' 24 8 = (Word.toBitVec64 new).extractLsb' 24 8
    rw [wordByte_three stored storedBound, wordByte_three new newBound, new1]
  · dsimp only [index]
    rw [patchedCellBytes_getElem, if_neg (by change ¬(0 ≤ 4 ∧ 4 < 0 + 4); omega)]
    change (Word.toBitVec64 old).extractLsb' 32 8 = (Word.toBitVec64 new).extractLsb' 32 8
    rw [wordByte_four old oldBound, wordByte_four new newBound, new2]
  · dsimp only [index]
    rw [patchedCellBytes_getElem, if_neg (by change ¬(0 ≤ 5 ∧ 5 < 0 + 4); omega)]
    change (Word.toBitVec64 old).extractLsb' 40 8 = (Word.toBitVec64 new).extractLsb' 40 8
    rw [wordByte_five old oldBound, wordByte_five new newBound, new2]
  · dsimp only [index]
    rw [patchedCellBytes_getElem, if_neg (by change ¬(0 ≤ 6 ∧ 6 < 0 + 4); omega)]
    change (Word.toBitVec64 old).extractLsb' 48 8 = (Word.toBitVec64 new).extractLsb' 48 8
    rw [wordByte_six old oldBound, wordByte_six new newBound, new3]
  · dsimp only [index]
    rw [patchedCellBytes_getElem, if_neg (by change ¬(0 ≤ 7 ∧ 7 < 0 + 4); omega)]
    change (Word.toBitVec64 old).extractLsb' 56 8 = (Word.toBitVec64 new).extractLsb' 56 8
    rw [wordByte_seven old oldBound, wordByte_seven new newBound, new3]

omit [Fact (2 ^ 17 < p)] in
/-- The canonical four-byte patch at offset four, expressed by the limb equalities used by SP1's
SW read-modify-write columns. -/
theorem patchedCellBytes_four_four
    (address : Vector (ZMod p) 3)
    (old stored new : Word (ZMod p))
    (oldBound : Word.isU64 old) (storedBound : Word.isU64 stored)
    (newBound : Word.isU64 new)
    (new0 : new[0] = old[0]) (new1 : new[1] = old[1])
    (new2 : new[2] = stored[0]) (new3 : new[3] = stored[1]) :
    cellBytesToWord
        (patchedCellBytes (Word.toBitVec64 old)
          ⟨address, stored, 4⟩ 4 4) =
      Word.toBitVec64 new := by
  rw [← cellBytesToWord_wordBytes (Word.toBitVec64 new)]
  apply congrArg cellBytesToWord
  apply Vector.ext
  intro i hi
  let index : Fin 8 := ⟨i, hi⟩
  change (patchedCellBytes (Word.toBitVec64 old) ⟨address, stored, 4⟩ 4 4)[index] =
    (wordBytes (Word.toBitVec64 new))[index]
  interval_cases i
  · dsimp only [index]
    rw [patchedCellBytes_getElem, if_neg (by change ¬(4 ≤ 0 ∧ 0 < 4 + 4); omega)]
    change (Word.toBitVec64 old).extractLsb' 0 8 = (Word.toBitVec64 new).extractLsb' 0 8
    rw [wordByte_zero old oldBound, wordByte_zero new newBound, new0]
  · dsimp only [index]
    rw [patchedCellBytes_getElem, if_neg (by change ¬(4 ≤ 1 ∧ 1 < 4 + 4); omega)]
    change (Word.toBitVec64 old).extractLsb' 8 8 = (Word.toBitVec64 new).extractLsb' 8 8
    rw [wordByte_one old oldBound, wordByte_one new newBound, new0]
  · dsimp only [index]
    rw [patchedCellBytes_getElem, if_neg (by change ¬(4 ≤ 2 ∧ 2 < 4 + 4); omega)]
    change (Word.toBitVec64 old).extractLsb' 16 8 = (Word.toBitVec64 new).extractLsb' 16 8
    rw [wordByte_two old oldBound, wordByte_two new newBound, new1]
  · dsimp only [index]
    rw [patchedCellBytes_getElem, if_neg (by change ¬(4 ≤ 3 ∧ 3 < 4 + 4); omega)]
    change (Word.toBitVec64 old).extractLsb' 24 8 = (Word.toBitVec64 new).extractLsb' 24 8
    rw [wordByte_three old oldBound, wordByte_three new newBound, new1]
  · dsimp only [index]
    rw [patchedCellBytes_getElem, if_pos (by change 4 ≤ 4 ∧ 4 < 4 + 4; omega)]
    norm_num
    change (Word.toBitVec64 stored).extractLsb' 0 8 = (Word.toBitVec64 new).extractLsb' 32 8
    rw [wordByte_zero stored storedBound, wordByte_four new newBound, new2]
  · dsimp only [index]
    rw [patchedCellBytes_getElem, if_pos (by change 4 ≤ 5 ∧ 5 < 4 + 4; omega)]
    norm_num
    change (Word.toBitVec64 stored).extractLsb' 8 8 = (Word.toBitVec64 new).extractLsb' 40 8
    rw [wordByte_one stored storedBound, wordByte_five new newBound, new2]
  · dsimp only [index]
    rw [patchedCellBytes_getElem, if_pos (by change 4 ≤ 6 ∧ 6 < 4 + 4; omega)]
    norm_num
    change (Word.toBitVec64 stored).extractLsb' 16 8 = (Word.toBitVec64 new).extractLsb' 48 8
    rw [wordByte_two stored storedBound, wordByte_six new newBound, new3]
  · dsimp only [index]
    rw [patchedCellBytes_getElem, if_pos (by change 4 ≤ 7 ∧ 7 < 4 + 4; omega)]
    norm_num
    change (Word.toBitVec64 stored).extractLsb' 24 8 = (Word.toBitVec64 new).extractLsb' 56 8
    rw [wordByte_three stored storedBound, wordByte_seven new newBound, new3]

omit [Fact (2 ^ 17 < p)] in
/-- The canonical two-byte patch at any of the four halfword-aligned offsets. `selected` names the
16-bit limb replaced by the low limb of the committed store word. -/
theorem patchedCellBytes_two
    (address : Vector (ZMod p) 3)
    (old stored new : Word (ZMod p))
    (selected : Fin 4)
    (oldBound : Word.isU64 old) (storedBound : Word.isU64 stored)
    (newBound : Word.isU64 new)
    (newEq : ∀ i : Fin 4,
      new[i] = if i = selected then stored[0] else old[i]) :
    cellBytesToWord
        (patchedCellBytes (Word.toBitVec64 old)
          ⟨address, stored, 2⟩ (2 * selected.val) 2) =
      Word.toBitVec64 new := by
  have new0 := newEq 0
  have new1 := newEq 1
  have new2 := newEq 2
  have new3 := newEq 3
  rw [← cellBytesToWord_wordBytes (Word.toBitVec64 new)]
  apply congrArg cellBytesToWord
  apply Vector.ext
  intro i hi
  let index : Fin 8 := ⟨i, hi⟩
  change (patchedCellBytes (Word.toBitVec64 old) ⟨address, stored, 2⟩ (2 * selected.val) 2)[index]
    = (wordBytes (Word.toBitVec64 new))[index]
  fin_cases selected <;> interval_cases i <;>
    simp [index, patchedCellBytes, wordBytes] at new0 new1 new2 new3 ⊢
  all_goals
    first
    | rw [wordByte_zero old oldBound, wordByte_zero new newBound, new0]
    | rw [wordByte_one old oldBound, wordByte_one new newBound, new0]
    | rw [wordByte_two old oldBound, wordByte_two new newBound, new1]
    | rw [wordByte_three old oldBound, wordByte_three new newBound, new1]
    | rw [wordByte_four old oldBound, wordByte_four new newBound, new2]
    | rw [wordByte_five old oldBound, wordByte_five new newBound, new2]
    | rw [wordByte_six old oldBound, wordByte_six new newBound, new3]
    | rw [wordByte_seven old oldBound, wordByte_seven new newBound, new3]
    | rw [wordByte_zero stored storedBound, wordByte_zero new newBound, new0]
    | rw [wordByte_one stored storedBound, wordByte_one new newBound, new0]
    | rw [wordByte_zero stored storedBound, wordByte_two new newBound, new1]
    | rw [wordByte_one stored storedBound, wordByte_three new newBound, new1]
    | rw [wordByte_zero stored storedBound, wordByte_four new newBound, new2]
    | rw [wordByte_one stored storedBound, wordByte_five new newBound, new2]
    | rw [wordByte_zero stored storedBound, wordByte_six new newBound, new3]
    | rw [wordByte_one stored storedBound, wordByte_seven new newBound, new3]

/-- The quotient expression used by SP1's byte-decomposition columns reassembles the original
field element. -/
theorem byteQuotient_reassembles (u low : ZMod p) :
    u = low + (u - low) * (256 : ZMod p)⁻¹ * 256 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h256 : (256 : ZMod p)⁻¹ * 256 = 1 := inv_mul_cancel₀ val_256_ne_zero
  rw [mul_assoc, h256, mul_one]
  ring

/-- Replacing the low byte of one selected 16-bit limb gives the corresponding byte-level
description of the whole post-state cell. -/
theorem lowByteUpdateFacts
    (old stored new : Word (ZMod p))
    (limb : Fin 4)
    (registerLow registerHigh memoryLow memoryHigh : ZMod p)
    (oldBound : Word.isU64 old) (storedBound : Word.isU64 stored)
    (registerLowBound : registerLow.val < 256)
    (registerHighBound : registerHigh.val < 256)
    (memoryLowBound : memoryLow.val < 256)
    (memoryHighBound : memoryHigh.val < 256)
    (storedDecomp : stored[0] = registerLow + registerHigh * 256)
    (oldDecomp : old[limb] = memoryLow + memoryHigh * 256)
    (newEq : ∀ i : Fin 4,
      new[i] = if i = limb then registerLow + memoryHigh * 256 else old[i]) :
    ∃ selected : Fin 8,
      selected.val = 2 * limb.val ∧
      Word.isU64 new ∧
      ∀ i : Fin 8,
        (wordBytes (Word.toBitVec64 new))[i] =
          if i = selected then (wordBytes (Word.toBitVec64 stored))[0]
          else (wordBytes (Word.toBitVec64 old))[i] := by
  let selected : Fin 8 := ⟨2 * limb.val, by
    have := limb.isLt
    omega⟩
  have newBound : Word.isU64 new := by
    intro i
    rw [newEq i]
    split
    · rw [val_lo_add_hi registerLowBound memoryHighBound]
      omega
    · exact oldBound i
  refine ⟨selected, rfl, newBound, ?_⟩
  intro i
  have newSelected :
      new[limb] = registerLow + memoryHigh * 256 := by
    rw [newEq limb, if_pos rfl]
  have newLow :=
    lowByte_eq registerLowBound memoryHighBound newSelected
  have newHigh :=
    highByte_eq registerLowBound memoryHighBound newSelected
  have storedLow :=
    lowByte_eq registerLowBound registerHighBound storedDecomp
  have oldHigh :=
    highByte_eq memoryLowBound memoryHighBound oldDecomp
  have new0 := newEq 0
  have new1 := newEq 1
  have new2 := newEq 2
  have new3 := newEq 3
  fin_cases limb <;> fin_cases i <;>
    simp [selected, wordBytes] at new0 new1 new2 new3 newLow newHigh storedLow oldHigh ⊢
  all_goals
    first
    | rw [wordByte_zero new newBound, wordByte_zero stored storedBound,
        newLow, storedLow]
    | rw [wordByte_one new newBound, wordByte_one old oldBound,
        newHigh, oldHigh]
    | rw [wordByte_two new newBound, wordByte_zero stored storedBound,
        newLow, storedLow]
    | rw [wordByte_three new newBound, wordByte_three old oldBound,
        newHigh, oldHigh]
    | rw [wordByte_four new newBound, wordByte_zero stored storedBound,
        newLow, storedLow]
    | rw [wordByte_five new newBound, wordByte_five old oldBound,
        newHigh, oldHigh]
    | rw [wordByte_six new newBound, wordByte_zero stored storedBound,
        newLow, storedLow]
    | rw [wordByte_seven new newBound, wordByte_seven old oldBound,
        newHigh, oldHigh]
    | rw [wordByte_zero old oldBound, wordByte_zero new newBound, new0]
    | rw [wordByte_one old oldBound, wordByte_one new newBound, new0]
    | rw [wordByte_two old oldBound, wordByte_two new newBound, new1]
    | rw [wordByte_three old oldBound, wordByte_three new newBound, new1]
    | rw [wordByte_four old oldBound, wordByte_four new newBound, new2]
    | rw [wordByte_five old oldBound, wordByte_five new newBound, new2]
    | rw [wordByte_six old oldBound, wordByte_six new newBound, new3]
    | rw [wordByte_seven old oldBound, wordByte_seven new newBound, new3]

/-- Replacing the high byte of one selected 16-bit limb gives the corresponding byte-level
description of the whole post-state cell. -/
theorem highByteUpdateFacts
    (old stored new : Word (ZMod p))
    (limb : Fin 4)
    (registerLow registerHigh memoryLow memoryHigh : ZMod p)
    (oldBound : Word.isU64 old) (storedBound : Word.isU64 stored)
    (registerLowBound : registerLow.val < 256)
    (registerHighBound : registerHigh.val < 256)
    (memoryLowBound : memoryLow.val < 256)
    (memoryHighBound : memoryHigh.val < 256)
    (storedDecomp : stored[0] = registerLow + registerHigh * 256)
    (oldDecomp : old[limb] = memoryLow + memoryHigh * 256)
    (newEq : ∀ i : Fin 4,
      new[i] = if i = limb then memoryLow + registerLow * 256 else old[i]) :
    ∃ selected : Fin 8,
      selected.val = 2 * limb.val + 1 ∧
      Word.isU64 new ∧
      ∀ i : Fin 8,
        (wordBytes (Word.toBitVec64 new))[i] =
          if i = selected then (wordBytes (Word.toBitVec64 stored))[0]
          else (wordBytes (Word.toBitVec64 old))[i] := by
  let selected : Fin 8 := ⟨2 * limb.val + 1, by
    have := limb.isLt
    omega⟩
  have newBound : Word.isU64 new := by
    intro i
    rw [newEq i]
    split
    · rw [val_lo_add_hi memoryLowBound registerLowBound]
      omega
    · exact oldBound i
  refine ⟨selected, rfl, newBound, ?_⟩
  intro i
  have newSelected :
      new[limb] = memoryLow + registerLow * 256 := by
    rw [newEq limb, if_pos rfl]
  have newLow :=
    lowByte_eq memoryLowBound registerLowBound newSelected
  have newHigh :=
    highByte_eq memoryLowBound registerLowBound newSelected
  have storedLow :=
    lowByte_eq registerLowBound registerHighBound storedDecomp
  have oldLow :=
    lowByte_eq memoryLowBound memoryHighBound oldDecomp
  have new0 := newEq 0
  have new1 := newEq 1
  have new2 := newEq 2
  have new3 := newEq 3
  fin_cases limb <;> fin_cases i <;>
    simp [selected, wordBytes] at new0 new1 new2 new3 newLow newHigh storedLow oldLow ⊢
  all_goals
    first
    | rw [wordByte_zero new newBound, wordByte_zero old oldBound,
        newLow, oldLow]
    | rw [wordByte_one new newBound, wordByte_zero stored storedBound,
        newHigh, storedLow]
    | rw [wordByte_two new newBound, wordByte_two old oldBound,
        newLow, oldLow]
    | rw [wordByte_three new newBound, wordByte_zero stored storedBound,
        newHigh, storedLow]
    | rw [wordByte_four new newBound, wordByte_four old oldBound,
        newLow, oldLow]
    | rw [wordByte_five new newBound, wordByte_zero stored storedBound,
        newHigh, storedLow]
    | rw [wordByte_six new newBound, wordByte_six old oldBound,
        newLow, oldLow]
    | rw [wordByte_seven new newBound, wordByte_zero stored storedBound,
        newHigh, storedLow]
    | rw [wordByte_zero old oldBound, wordByte_zero new newBound, new0]
    | rw [wordByte_one old oldBound, wordByte_one new newBound, new0]
    | rw [wordByte_two old oldBound, wordByte_two new newBound, new1]
    | rw [wordByte_three old oldBound, wordByte_three new newBound, new1]
    | rw [wordByte_four old oldBound, wordByte_four new newBound, new2]
    | rw [wordByte_five old oldBound, wordByte_five new newBound, new2]
    | rw [wordByte_six old oldBound, wordByte_six new newBound, new3]
    | rw [wordByte_seven old oldBound, wordByte_seven new newBound, new3]

omit [Fact (2 ^ 17 < p)] in
/-- A byte-level description of the post-state word closes the canonical one-byte patch at any
of the cell's eight offsets. -/
theorem patchedCellBytes_one
    (address : Vector (ZMod p) 3)
    (old stored new : Word (ZMod p))
    (selected : Fin 8)
    (newBytes : ∀ i : Fin 8,
      (wordBytes (Word.toBitVec64 new))[i] =
        if i = selected then (wordBytes (Word.toBitVec64 stored))[0]
        else (wordBytes (Word.toBitVec64 old))[i]) :
    cellBytesToWord
        (patchedCellBytes (Word.toBitVec64 old)
          ⟨address, stored, 1⟩ selected.val 1) =
      Word.toBitVec64 new := by
  rw [← cellBytesToWord_wordBytes (Word.toBitVec64 new)]
  apply congrArg cellBytesToWord
  apply Vector.ext
  intro i hi
  let index : Fin 8 := ⟨i, hi⟩
  change (patchedCellBytes (Word.toBitVec64 old) ⟨address, stored, 1⟩ selected.val 1)[index] =
    (wordBytes (Word.toBitVec64 new))[index]
  rw [newBytes index, patchedCellBytes_getElem]
  by_cases selectedEq : index = selected
  · subst selected
    rw [if_pos rfl, if_pos (by omega)]
    norm_num
    rfl
  · rw [if_neg selectedEq]
    apply if_neg
    intro covered
    apply selectedEq
    apply Fin.ext
    omega

/-- A Memory-bus new value faithfully represents applying `mw` to the prior aligned cell.  This is
the common semantic statement behind SB/SH/SW's read-modify-write witnesses and SD's full-cell
write. -/
def RamCellUpdate (mw : Trace.MemWrite (ZMod p)) (cell : RamCell)
    (old new : BitVec 64) : Prop :=
  ∀ bytes : Vector (BitVec 8) 8,
    cellBytesToWord bytes = old →
      cellBytesToWord (updatedCellBytes mw cell bytes) = new

/-- A store whose byte address is `offset` bytes into `cell` implements `RamCellUpdate` as soon as
the chip's read-modify-write columns equal the canonical patched-cell word. This separates the
generic byte-address arithmetic from each chip's small selector proof. -/
theorem ramCellUpdate_of_patchedCell
    {mw : Trace.MemWrite (ZMod p)} {cell : RamCell}
    {old new : BitVec 64} {offset width : ℕ}
    (address : mw.addrNat = cell.baseAddr.toNat + offset)
    (widthEq : mw.width = width)
    (newEq : new = cellBytesToWord (patchedCellBytes old mw offset width)) :
    RamCellUpdate mw cell old new := by
  intro bytes assembled
  rw [eq_wordBytes_of_cellBytesToWord_eq assembled, newEq]
  apply congrArg cellBytesToWord
  apply Vector.ext
  intro i hi
  let index : Fin 8 := ⟨i, hi⟩
  change (updatedCellBytes mw cell (wordBytes old))[index] =
    (patchedCellBytes old mw offset width)[index]
  rw [updatedCellBytes_getElem, patchedCellBytes_getElem]
  by_cases covered : offset ≤ index.val ∧ index.val < offset + width
  · rw [if_pos covered, if_pos]
    · unfold Trace.MemWrite.byteAt
      congr 2
      omega
    · unfold Trace.MemWrite.covers
      rw [address, widthEq]
      omega
  · rw [if_neg covered, if_neg]
    unfold Trace.MemWrite.covers
    rw [address, widthEq]
    omega

/-- The committed byte range lies wholly inside one canonical RAM cell. -/
def _root_.SP1Clean.Trace.MemWrite.InCell
    (mw : Trace.MemWrite (ZMod p)) (cell : RamCell) : Prop :=
  ∀ address : ℕ, mw.covers address →
    cell.baseAddr.toNat ≤ address ∧ address < cell.baseAddr.toNat + 8

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- A contiguous store lies in its aligned cell when its starting offset and width fit in the
cell's eight-byte range. -/
theorem Trace.MemWrite.inCell_of_address_width
    {mw : Trace.MemWrite (ZMod p)} {cell : RamCell} {offset width : ℕ}
    (address : mw.addrNat = cell.baseAddr.toNat + offset)
    (widthEq : mw.width = width) (fits : offset + width ≤ 8) :
    mw.InCell cell := by
  intro byte covered
  unfold Trace.MemWrite.covers at covered
  rw [address, widthEq] at covered
  omega

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- Two different canonical cells have disjoint byte ranges. -/
theorem Trace.MemWrite.not_covers_otherCell
    {mw : Trace.MemWrite (ZMod p)} {written other : RamCell}
    (inCell : mw.InCell written) (different : other ≠ written) (i : Fin 8) :
    ¬ mw.covers (other.baseAddr.toNat + i.val) := by
  intro covered
  have range := inCell _ covered
  have indexEq : other.toNat = written.toNat := by
    rw [RamCell.baseAddr_toNat, RamCell.baseAddr_toNat] at range
    have := i.isLt
    omega
  exact different (BitVec.eq_of_toNat_eq indexEq)

/-- Pointwise equality on a cell's eight bytes is enough to preserve its assembled content. -/
theorem locContent_ram_congr_cell {state state' : SailState} (cell : RamCell)
    (frame : ∀ i : Fin 8,
      state'.mem.get? (cell.baseAddr.toNat + i.val) =
        state.mem.get? (cell.baseAddr.toNat + i.val)) :
    locContent state' (MemLoc.ram cell) = locContent state (MemLoc.ram cell) := by
  -- `frameAt` re-indexes `frame` by a raw `ℕ`, so the eight `rw`s below match the literal offsets
  -- that `ramWord64?` reads (a `Fin` numeral's `.val` does not reduce at `rw`'s transparency).
  have frameAt : ∀ (k : ℕ), k < 8 → state'.mem.get? (cell.baseAddr.toNat + k) =
      state.mem.get? (cell.baseAddr.toNat + k) := fun k hk => frame ⟨k, hk⟩
  have frame0 : state'.mem.get? cell.baseAddr.toNat =
      state.mem.get? cell.baseAddr.toNat := by simpa using frameAt 0 (by omega)
  simp only [locContent, ramWord64?]
  rw [frame0, frameAt 1 (by omega), frameAt 2 (by omega), frameAt 3 (by omega),
    frameAt 4 (by omega), frameAt 5 (by omega), frameAt 6 (by omega), frameAt 7 (by omega)]

/-- Reading a complete RAM word exposes its eight constituent bytes. -/
theorem cellBytes_of_ramWord64?_eq_some {state : SailState} {cell : RamCell}
    {word : BitVec 64}
    (read : ramWord64? state cell.baseAddr = some word) :
    ∃ bytes : Vector (BitVec 8) 8,
      (∀ i : Fin 8,
        state.mem.get? (cell.baseAddr.toNat + i.val) = some bytes[i]) ∧
      cellBytesToWord bytes = word := by
  unfold ramWord64? at read
  rcases byte0Eq : state.mem.get? cell.baseAddr.toNat with _ | byte0
  · rw [byte0Eq] at read
    contradiction
  rcases byte1Eq : state.mem.get? (cell.baseAddr.toNat + 1) with _ | byte1
  · rw [byte0Eq, byte1Eq] at read
    contradiction
  rcases byte2Eq : state.mem.get? (cell.baseAddr.toNat + 2) with _ | byte2
  · rw [byte0Eq, byte1Eq, byte2Eq] at read
    contradiction
  rcases byte3Eq : state.mem.get? (cell.baseAddr.toNat + 3) with _ | byte3
  · rw [byte0Eq, byte1Eq, byte2Eq, byte3Eq] at read
    contradiction
  rcases byte4Eq : state.mem.get? (cell.baseAddr.toNat + 4) with _ | byte4
  · rw [byte0Eq, byte1Eq, byte2Eq, byte3Eq, byte4Eq] at read
    contradiction
  rcases byte5Eq : state.mem.get? (cell.baseAddr.toNat + 5) with _ | byte5
  · rw [byte0Eq, byte1Eq, byte2Eq, byte3Eq, byte4Eq, byte5Eq] at read
    contradiction
  rcases byte6Eq : state.mem.get? (cell.baseAddr.toNat + 6) with _ | byte6
  · rw [byte0Eq, byte1Eq, byte2Eq, byte3Eq, byte4Eq, byte5Eq, byte6Eq] at read
    contradiction
  rcases byte7Eq : state.mem.get? (cell.baseAddr.toNat + 7) with _ | byte7
  · rw [byte0Eq, byte1Eq, byte2Eq, byte3Eq, byte4Eq, byte5Eq, byte6Eq, byte7Eq] at read
    contradiction
  let bytes : Vector (BitVec 8) 8 :=
    #v[byte0, byte1, byte2, byte3, byte4, byte5, byte6, byte7]
  refine ⟨bytes, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [bytes] <;> assumption
  · rw [byte0Eq, byte1Eq, byte2Eq, byte3Eq, byte4Eq, byte5Eq, byte6Eq, byte7Eq] at read
    simpa [cellBytesToWord, bytes] using read

/-- Project one canonical little-endian byte from a grounded Memory-bus cell. -/
theorem byte_of_ramWord64?_eq_some {state : SailState} {cell : RamCell}
    {word : BitVec 64} (read : ramWord64? state cell.baseAddr = some word) (i : Fin 8) :
    state.mem.get? (cell.baseAddr.toNat + i.val) = some (wordBytes word)[i] := by
  obtain ⟨bytes, byteRead, assembled⟩ := cellBytes_of_ramWord64?_eq_some read
  rw [eq_wordBytes_of_cellBytesToWord_eq assembled] at byteRead
  exact byteRead i

/-- The generic byte-addressed-to-cell bridge.  A grounded pull supplies the old cell, the
`RowEffect` supplies the architectural byte update, and `RamCellUpdate` identifies the assembled
result with the bus's new word. -/
theorem ramCellPost_of_update
    {view : Trace.RowView (ZMod p)} {rf : Semantics.RowFacts p}
    {program : GuestProgram} {state state' : SailState}
    {mw : Trace.MemWrite (ZMod p)} {cell : RamCell}
    {old new : Word (ZMod p)}
    (effect : RowEffect program view state state')
    (commit : view.commit.memWrite = some mw)
    (pulls : MemoryPullsBound rf state)
    (oldPull : ∃ mp ∈ rf.memPulls,
      MemoryMsg.locOf mp.1 = MemLoc.ram cell ∧ mp.1.value = old)
    (update : RamCellUpdate mw cell (Word.toBitVec64 old) (Word.toBitVec64 new)) :
    locContent state' (MemLoc.ram cell) = some (Word.toBitVec64 new) := by
  obtain ⟨prior, priorMem, priorLoc, priorValue⟩ := oldPull
  have priorContent := pulls prior priorMem
  rw [priorLoc, priorValue] at priorContent
  obtain ⟨bytes, byteRead, assembled⟩ :=
    cellBytes_of_ramWord64?_eq_some priorContent
  have byteWrite : ∀ i : Fin 8,
      state'.mem.get? (cell.baseAddr.toNat + i.val) =
        some (updatedCellBytes mw cell bytes)[i] := by
    intro i
    rw [updatedCellBytes_getElem]
    split_ifs with covered
    · exact (effect.mem.2 mw commit).1 _ covered
    · rw [(effect.mem.2 mw commit).2 _ covered]
      exact byteRead i
  have assembled' := update bytes assembled
  -- Re-indexed by a raw `ℕ` so the eight `rw`s match the literal offsets `ramWord64?` reads.
  have byteWriteAt : ∀ (k : ℕ) (hk : k < 8), state'.mem.get? (cell.baseAddr.toNat + k) =
      some (updatedCellBytes mw cell bytes)[k] := fun k hk => byteWrite ⟨k, hk⟩
  have byteWrite0 : state'.mem.get? cell.baseAddr.toNat =
      some (updatedCellBytes mw cell bytes)[0] := by simpa using byteWriteAt 0 (by omega)
  simp only [locContent, ramWord64?]
  rw [byteWrite0, byteWriteAt 1 (by omega), byteWriteAt 2 (by omega), byteWriteAt 3 (by omega),
    byteWriteAt 4 (by omega), byteWriteAt 5 (by omega), byteWriteAt 6 (by omega),
    byteWriteAt 7 (by omega)]
  exact congrArg some assembled'

/-- Assemble the `RowWiring.ram_frame` obligation for a store.  The written cell uses the
authenticated full-cell update; every other cell frames because canonical 8-byte cells are
disjoint. -/
theorem ramFrame_of_update
    {view : Trace.RowView (ZMod p)} {rf : Semantics.RowFacts p}
    {program : GuestProgram} {state state' : SailState}
    {mw : Trace.MemWrite (ZMod p)} {written : RamCell}
    {old new : Word (ZMod p)}
    (effect : RowEffect program view state state')
    (commit : view.commit.memWrite = some mw)
    (pulls : MemoryPullsBound rf state)
    (oldPull : ∃ mp ∈ rf.memPulls,
      MemoryMsg.locOf mp.1 = MemLoc.ram written ∧ mp.1.value = old)
    (newPush : ∃ message ∈ rf.memPushes,
      MemoryMsg.locOf message = MemLoc.ram written ∧ message.value = new)
    (inCell : mw.InCell written)
    (update : RamCellUpdate mw written (Word.toBitVec64 old) (Word.toBitVec64 new)) :
    ∀ (cell : RamCell) (value : Word (ZMod p)),
      (∀ message ∈ rf.memPushes,
        MemoryMsg.locOf message = MemLoc.ram cell → message.value = value) →
      locContent state (MemLoc.ram cell) = some (Word.toBitVec64 value) →
      locContent state' (MemLoc.ram cell) = some (Word.toBitVec64 value) := by
  intro cell value pushValues priorContent
  by_cases same : cell = written
  · subst cell
    obtain ⟨message, messageMem, messageLoc, messageValue⟩ := newPush
    have newEq : new = value := by
      rw [← messageValue]
      exact pushValues message messageMem messageLoc
    rw [← newEq]
    exact ramCellPost_of_update effect commit pulls oldPull update
  · calc
      locContent state' (MemLoc.ram cell) =
          locContent state (MemLoc.ram cell) := locContent_ram_congr_cell cell (fun i =>
            (effect.mem.2 mw commit).2 _
              (Trace.MemWrite.not_covers_otherCell inCell same i))
      _ = some (Word.toBitVec64 value) := priorContent

end SP1Clean.Soundness
