import SP1Clean.Math.Word
import SP1Clean.Native.Operations.U16MSBOperation.Populate
import SP1Clean.Native.Operations.U16CompareOperation.Populate
import SP1Clean.Native.Operations.MulOperation.Populate
import SP1Clean.Native.Operations.IsZeroWordOperation.Populate
import SP1Clean.Native.Operations.IsEqualWordOperation.Populate
import SP1Clean.Native.Operations.LtOperationUnsigned.Populate
import SP1Clean.Native.Operations.AddOperation.Populate

/-! # `DivRemChip` — native witness generation (`populate`)

SP1's `DivRemChip::generate_trace_into` (`alu/divrem/mod.rs:231-570`) ported to Lean: the honest
witness assignments for every committed column block, each a **pure function of the raw register
reads** `B`/`C` (`adapter.op_b/c_memory.prev_value`) and the eight variant flags `f` (plus the
`is_real` input `ir` where SP1 gates the populate on a real event). The flags are **not** computable
from the row inputs — the prover supplies them via the `"div_rem_flags"` `ProverHint` key, one-hot
`[div, divu, rem, remu, divw, remw, divuw, remuw]` on real rows; the key's **absence defaults to the
padding template** `is_divu = 1` (SP1's padded rows are "0 divided by 1": `is_divu = 1`,
`op_c read = Word(1)`, everything live derived from that — `mod.rs:549-569`).

The division core `quotBits`/`remBits` is the `BitVec` port of the executor's
`get_quotient_and_remainder` (`executor/src/utils.rs:73-93`): divisor-zero branched **first**
(RISC-V's `q = allOnes, r = b` — `BitVec`'s own `x/0 = 0` convention differs), then truncated
signed division (`sdiv`/`srem`, which wrap `intMin / -1` exactly like Rust's `wrapping_div/rem`),
with the W-variants operating on the low 32 bits and sign-extending the result.

Blocks SP1 populates **conditionally** are gated the same way here (zero off-gate, so the
`TraceGenTests` anchor matches SP1's `generate_trace` cell-for-cell, unmasked): the two
`MulOperation` structs (`mul_lower` on real rows; `mul_upper` only on the 64-bit variants), the
`is_overflow_b/c` `IsEqualWordOperation` structs (real rows, word-truncated forms on W-variants),
the two `AddOperation` negation words (only when the matching `abs_*_alu_event` fires), and the
`LtOperationUnsigned` block (only when the remainder-check multiplicity is `1`). `is_c_0` is
populated **ungated** (SP1 calls `is_c_0.populate` on padding rows too). -/

namespace SP1Clean.DivRemChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- The eight honest variant flags `[div, divu, rem, remu, divw, remw, divuw, remuw]` from the
`"div_rem_flags"` hint key. Falls back to the **padding template** `is_divu = 1` when the key is
absent (SP1's padded rows are `0 / 1` `DIVU` rows, not all-zero — `mod.rs:560-568`). -/
def hintFlags (h : ProverHint (ZMod p)) : Vector (ZMod p) 8 :=
  ((h "div_rem_flags" 8)[0]?).getD #v[0, 1, 0, 0, 0, 0, 0, 0]

/-- The four base-2^16 limbs of a `ℕ` (the u64 bit pattern → committed word). -/
def wordOfNat (n : ℕ) : Word (ZMod p) :=
  #v[((n % 2 ^ 16 : ℕ) : ZMod p), ((n / 2 ^ 16 % 2 ^ 16 : ℕ) : ZMod p),
     ((n / 2 ^ 32 % 2 ^ 16 : ℕ) : ZMod p), ((n / 2 ^ 48 % 2 ^ 16 : ℕ) : ZMod p)]

/-- The committed word of a 64-bit value. -/
def wordOfBits (x : BitVec 64) : Word (ZMod p) := wordOfNat x.toNat

/-- Two's-complement absolute value (Rust `unsigned_abs`: `|intMin| = intMin`'s bit pattern). -/
def bvAbs {w : ℕ} (x : BitVec w) : BitVec w := if x.msb then -x else x

/-! ## The division core (`get_quotient_and_remainder`) -/

/-- The quotient bit pattern, per variant class: the `BitVec` port of the executor's
`get_quotient_and_remainder` (first component). Divisor-zero (on the class's operand width) gives
RISC-V's `allOnes`; the W-variants divide the low 32 bits and sign-extend the result (including
`divuw` — Rust's `as i32 as i64 as u64` on the 32-bit unsigned quotient). The fall-through class is
unsigned 64-bit (`divu`/`remu`), which is also the padding default. -/
def quotBits (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) : BitVec 64 :=
  let b := Word.toBitVec64 B
  let c := Word.toBitVec64 C
  if f[4] + f[5] = 1 then
    if c.setWidth 32 = 0 then BitVec.allOnes 64
    else ((b.setWidth 32).sdiv (c.setWidth 32)).signExtend 64
  else if f[6] + f[7] = 1 then
    if c.setWidth 32 = 0 then BitVec.allOnes 64
    else ((b.setWidth 32).udiv (c.setWidth 32)).signExtend 64
  else if f[0] + f[2] = 1 then
    if c = 0 then BitVec.allOnes 64 else b.sdiv c
  else
    if c = 0 then BitVec.allOnes 64 else b.udiv c

/-- The remainder bit pattern (second `get_quotient_and_remainder` component). Divisor-zero gives
`b` (sign-extended low 32 for **both** W-variant classes — Rust's `(b as i32) as u64`); `srem` is
Rust's truncated `wrapping_rem` (sign of the dividend, `intMin % -1 = 0`). -/
def remBits (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) : BitVec 64 :=
  let b := Word.toBitVec64 B
  let c := Word.toBitVec64 C
  if f[4] + f[5] = 1 then
    if c.setWidth 32 = 0 then (b.setWidth 32).signExtend 64
    else ((b.setWidth 32).srem (c.setWidth 32)).signExtend 64
  else if f[6] + f[7] = 1 then
    if c.setWidth 32 = 0 then (b.setWidth 32).signExtend 64
    else ((b.setWidth 32).umod (c.setWidth 32)).signExtend 64
  else if f[0] + f[2] = 1 then
    if c = 0 then b else b.srem c
  else
    if c = 0 then b else b.umod c

/-- The committed `quotient` word (the RISC-V writeback form, W-variants sign-extended). -/
def populateQuotient (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) : Word (ZMod p) :=
  wordOfBits (quotBits B C f)

/-- The committed `remainder` word. -/
def populateRemainder (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) : Word (ZMod p) :=
  wordOfBits (remBits B C f)

/-- The computational quotient: the low 32 bits **zero**-extended for the unsigned W-variants
(`quotient as u32 as u64`), the writeback form otherwise. -/
def quotCompBits (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) : BitVec 64 :=
  if f[6] + f[7] = 1 then ((quotBits B C f).setWidth 32).setWidth 64 else quotBits B C f

/-- The computational remainder (as `quotCompBits`). -/
def remCompBits (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) : BitVec 64 :=
  if f[6] + f[7] = 1 then ((remBits B C f).setWidth 32).setWidth 64 else remBits B C f

/-- The committed `quotient_comp` word. -/
def populateQuotComp (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) : Word (ZMod p) :=
  wordOfBits (quotCompBits B C f)

/-- The committed `remainder_comp` word. -/
def populateRemComp (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) : Word (ZMod p) :=
  wordOfBits (remCompBits B C f)

/-- The result word `a` (the register writeback): the quotient on the `div`-family flags, the
remainder on the `rem`-family flags, zero otherwise. On the padding template (`is_divu`, `0 / 1`)
this is the zero word, matching SP1's zero-initialized padding `a`. -/
def populateA (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) : Word (ZMod p) :=
  if f[0] + f[1] + f[4] + f[6] = 1 then populateQuotient B C f
  else if f[2] + f[3] + f[5] + f[7] = 1 then populateRemainder B C f
  else #v[0, 0, 0, 0]

/-! ## The arithmetic operands `b`/`c` (extension of the raw reads) -/

/-- The committed operand `b`: the raw read for the 64-bit variants, its low 32 bits
sign-extended (signed W) / zero-extended (unsigned W) otherwise — the value E20–E47 pin. -/
def bComp (B : Word (ZMod p)) (f : Vector (ZMod p) 8) : Word (ZMod p) :=
  if f[4] + f[5] = 1 then
    let m := U16MSBOperation.populate_msb B[1]
    #v[B[0], B[1], m * 65535, m * 65535]
  else if f[6] + f[7] = 1 then #v[B[0], B[1], 0, 0]
  else B

/-- The committed operand `c` (as `bComp`). -/
def cComp (C : Word (ZMod p)) (f : Vector (ZMod p) 8) : Word (ZMod p) :=
  if f[4] + f[5] = 1 then
    let m := U16MSBOperation.populate_msb C[1]
    #v[C[0], C[1], m * 65535, m * 65535]
  else if f[6] + f[7] = 1 then #v[C[0], C[1], 0, 0]
  else C

/-! ## Sign cells and derived flags -/

/-- The shared `b_msb` witness cell: the MSB of the **raw read**'s limb 1 on the W-variants
(`event.b >> 16`), limb 3 otherwise (`b >> 48`) — one cell consumed by both the
`is_real_not_word`-gated and the word-gated `U16MSBOperation` assertions. -/
def bMsbCell (B : Word (ZMod p)) (f : Vector (ZMod p) 8) : ZMod p :=
  if f[4] + f[5] + f[6] + f[7] = 1 then U16MSBOperation.populate_msb B[1]
  else U16MSBOperation.populate_msb B[3]

/-- The shared `c_msb` witness cell (as `bMsbCell`). -/
def cMsbCell (C : Word (ZMod p)) (f : Vector (ZMod p) 8) : ZMod p :=
  if f[4] + f[5] + f[6] + f[7] = 1 then U16MSBOperation.populate_msb C[1]
  else U16MSBOperation.populate_msb C[3]

/-- The shared `rem_msb` witness cell, on the populated remainder. -/
def remMsbCell (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) : ZMod p :=
  if f[4] + f[5] + f[6] + f[7] = 1 then
    U16MSBOperation.populate_msb (populateRemainder B C f)[1]
  else U16MSBOperation.populate_msb (populateRemainder B C f)[3]

/-- The `quot_msb` witness cell: only the W-variants fill it (SP1 populates it in the
word branch only; zero elsewhere, including padding). -/
def quotMsbCell (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) : ZMod p :=
  if f[4] + f[5] + f[6] + f[7] = 1 then
    U16MSBOperation.populate_msb (populateQuotient B C f)[1]
  else 0

/-- `b_neg = b_msb · is_signed_type` (E15's defining form; zero on the unsigned variants). -/
def populateBNeg (B : Word (ZMod p)) (f : Vector (ZMod p) 8) : ZMod p :=
  (f[0] + f[2] + f[4] + f[5]) * bMsbCell B f

/-- `c_neg = c_msb · is_signed_type`. -/
def populateCNeg (C : Word (ZMod p)) (f : Vector (ZMod p) 8) : ZMod p :=
  (f[0] + f[2] + f[4] + f[5]) * cMsbCell C f

/-- `rem_neg = rem_msb · is_signed_type`. -/
def populateRemNeg (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) : ZMod p :=
  (f[0] + f[2] + f[4] + f[5]) * remMsbCell B C f

/-! ## The overflow `IsEqualWordOperation` structs -/

/-- The `is_overflow_b` struct: populated on real rows only (zero on padding), with the
word-truncated form `(b as u32, i32::MIN)` on the W-variants and `(b, i64::MIN)` otherwise. -/
def ovbWitness (ir : ZMod p) (B : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    Extracted.IsEqualWordOperation (ZMod p) :=
  if ir = 1 then
    if f[4] + f[5] + f[6] + f[7] = 1 then
      IsEqualWordOperation.populate #v[B[0], B[1], 0, 0] #v[0, 32768, 0, 0]
    else IsEqualWordOperation.populate B #v[0, 0, 0, 32768]
  else ⟨IsZeroWordOperation.zeroCols⟩

/-- The `is_overflow_c` struct: `(c as u32, -1i32)` on the W-variants, `(c, -1i64)` otherwise. -/
def ovcWitness (ir : ZMod p) (C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    Extracted.IsEqualWordOperation (ZMod p) :=
  if ir = 1 then
    if f[4] + f[5] + f[6] + f[7] = 1 then
      IsEqualWordOperation.populate #v[C[0], C[1], 0, 0] #v[65535, 65535, 0, 0]
    else IsEqualWordOperation.populate C #v[65535, 65535, 65535, 65535]
  else ⟨IsZeroWordOperation.zeroCols⟩

/-- `is_overflow = ovb.result · ovc.result · is_signed_type` — E96's defining form, stated on the
witnessed structs so the constraint is definitional at the witness. -/
def populateIsOverflow (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) : ZMod p :=
  (ovbWitness ir B f).is_diff_zero.result * (ovcWitness ir C f).is_diff_zero.result
    * (f[0] + f[2] + f[4] + f[5])

/-- The seven scalar gate/sign cells, in witness order:
`[is_overflow, b_neg, b_neg_not_overflow, b_not_neg_not_overflow, is_real_not_word, rem_neg,
c_neg]`. On the padding template all are zero except `b_not_neg_not_overflow = 1` (SP1
`mod.rs:566`). -/
def populateScal (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    Vector (ZMod p) 7 :=
  let ov := populateIsOverflow ir B C f
  let bn := populateBNeg B f
  #v[ov, bn, bn * (1 - ov), (1 - bn) * (1 - ov),
     ir * (1 - (f[4] + f[5] + f[6] + f[7])), populateRemNeg B C f, populateCNeg C f]

/-! ## Absolute values and the divide-by-zero block -/

/-- The committed `abs_c`: `|c|` (two's complement, on the computational operand) for the signed
variants, the computational operand itself for the unsigned ones. -/
def populateAbsC (C : Word (ZMod p)) (f : Vector (ZMod p) 8) : Word (ZMod p) :=
  if f[0] + f[2] + f[4] + f[5] = 1 then wordOfBits (bvAbs (Word.toBitVec64 (cComp C f)))
  else cComp C f

/-- The committed `abs_remainder`: `|remainder|` for the signed variants, `remainder_comp` for the
unsigned ones. -/
def populateAbsRem (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) : Word (ZMod p) :=
  if f[0] + f[2] + f[4] + f[5] = 1 then wordOfBits (bvAbs (remBits B C f))
  else populateRemComp B C f

/-- The committed `max_abs_c_or_1 = max(1, abs_c)`: `Word(1)` exactly when `abs_c = 0`. -/
def populateMaxAbsCOr1 (C : Word (ZMod p)) (f : Vector (ZMod p) 8) : Word (ZMod p) :=
  let ac := populateAbsC C f
  if Word.toNat ac = 0 then #v[1, 0, 0, 0] else ac

/-- The `is_c_0` struct, populated **ungated** on the computational `c` (SP1 calls
`is_c_0.populate` on padding rows too — `mod.rs:568`). -/
def isC0Witness (C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    Extracted.IsZeroWordOperation (ZMod p) :=
  IsZeroWordOperation.populate (cComp C f)

/-- The `remainder_check_multiplicity = is_real · (1 − is_c_0.result)` gate cell. -/
def ltGate (ir : ZMod p) (C : Word (ZMod p)) (f : Vector (ZMod p) 8) : ZMod p :=
  ir * (1 - (isC0Witness C f).result)

/-! ## The `MulOperation` product structs -/

/-- The `c_times_quotient_lower` struct: `MulOperation.populate` of
`(quotient_comp, c)` on real rows, the zero struct on padding (SP1 populates it only per-event;
`MulOperation.populate 0 (1,0,0,0)` would fill `c_lower_byte[0] = 1`, which SP1's padding does
not). -/
def populateMulLower (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    Extracted.MulOperation (ZMod p) :=
  if ir = 1 then MulOperation.populate (populateQuotComp B C f) (cComp C f) 0 0 0
  else MulOperation.zeroCols

/-- The `c_times_quotient_upper` struct: populated **only on the 64-bit variants** (`is_mulh` for
the signed pair, unsigned otherwise); the W-variants leave it all-zero (SP1 `mod.rs:484-503` — the
upper Mul's multiplicity is `is_real_not_word`). -/
def populateMulUpper (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    Extracted.MulOperation (ZMod p) :=
  if ir = 1 ∧ f[0] + f[1] + f[2] + f[3] = 1 then
    MulOperation.populate (populateQuotComp B C f) (cComp C f) (f[0] + f[2]) 0 0
  else MulOperation.zeroCols

/-! ## `c_times_quotient` limbs and the carry chain -/

/-- The 128-bit product `quotient_comp · c`: sign-extended multiplication for the signed variants
(`mod.rs:453-461`), zero-extended otherwise. The low 64 bits agree with Rust's wrapping product in
every class. -/
def ctqProd (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) : BitVec 128 :=
  let qc := Word.toBitVec64 (populateQuotComp B C f)
  let cc := Word.toBitVec64 (cComp C f)
  if f[0] + f[2] + f[4] + f[5] = 1 then qc.signExtend 128 * cc.signExtend 128
  else qc.setWidth 128 * cc.setWidth 128

/-- u16 limb `i` of the 128-bit product (`0 ≤ i < 8`). -/
def ctqLimbNat (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) (i : ℕ) : ℕ :=
  (ctqProd B C f).toNat / 2 ^ (16 * i) % 2 ^ 16

/-- The committed `c_times_quotient` block (8 u16 limbs of the 128-bit product). -/
def populateCtq (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) : Vector (ZMod p) 8 :=
  Vector.ofFn fun i : Fin 8 => ((ctqLimbNat B C f i.val : ℕ) : ZMod p)

/-- Addend limb `i` of `remainder` in the carry chain: `remainder_comp` on the low word,
`rem_neg · 0xFFFF` sign fill above (`mod.rs:507-511`). -/
def remAddendNat (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) (i : ℕ) : ℕ :=
  if h : i < 4 then ((populateRemComp B C f)[i]'h).val
  else (populateRemNeg B C f).val * 65535

/-- The carry recursion of `c_times_quotient + remainder` (`mod.rs:514-524`):
`carry[i] = (ctq[i] + rem[i] + carry[i-1]) / 2^16`. -/
def carryNat (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) : ℕ → ℕ
  | 0 => (ctqLimbNat B C f 0 + remAddendNat B C f 0) / 2 ^ 16
  | n + 1 => (ctqLimbNat B C f (n + 1) + remAddendNat B C f (n + 1) + carryNat B C f n) / 2 ^ 16

/-- The committed `carry` block (8 boolean carries). -/
def populateCarry (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) : Vector (ZMod p) 8 :=
  Vector.ofFn fun i : Fin 8 => ((carryNat B C f i.val : ℕ) : ZMod p)

/-! ## The negation `AddOperation` words and the remainder range-check block -/

/-- The `c_neg_operation` value word: populated only when `abs_c_alu_event = c_neg · is_real`
fires (`mod.rs:393-399`); the active value is `c + abs_c = 0`'s limb form. -/
def wCnegWitness (ir : ZMod p) (C : Word (ZMod p)) (f : Vector (ZMod p) 8) : Word (ZMod p) :=
  if populateCNeg C f * ir = 1 then AddOperation.populate (cComp C f) (populateAbsC C f)
  else #v[0, 0, 0, 0]

/-- The `rem_neg_operation` value word: populated from `remainder` (SP1 `mod.rs:400-406` — not
`remainder_comp`; they agree on the signed rows where the gate fires). -/
def wRnegWitness (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) : Word (ZMod p) :=
  if populateRemNeg B C f * ir = 1 then
    AddOperation.populate (populateRemainder B C f) (populateAbsRem B C f)
  else #v[0, 0, 0, 0]

/-- The three event/multiplicity cells, in witness order:
`[abs_c_alu_event, abs_rem_alu_event, remainder_check_multiplicity]`. -/
def populateMisc (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    Vector (ZMod p) 3 :=
  #v[populateCNeg C f * ir, populateRemNeg B C f * ir, ltGate ir C f]

/-- The `remainder_lt_operation` comparison limbs, gated by the remainder-check multiplicity
(SP1 populates the block only when the multiplicity is `1` — `mod.rs:433-440`). -/
def ltClWitness (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    Vector (ZMod p) 2 :=
  if ltGate ir C f = 1 then
    LtOperationUnsigned.comparisonLimbsWitness (populateAbsRem B C f) (populateMaxAbsCOr1 C f)
  else #v[0, 0]

/-- The gated `u16_flags` block. -/
def ltFlagsWitness (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    Vector (ZMod p) 4 :=
  if ltGate ir C f = 1 then
    LtOperationUnsigned.flagsWitness (populateAbsRem B C f) (populateMaxAbsCOr1 C f)
  else #v[0, 0, 0, 0]

/-- The gated `not_eq_inv` cell. -/
def ltNotEqInvWitness (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    Vector (ZMod p) 1 :=
  if ltGate ir C f = 1 then
    LtOperationUnsigned.notEqInvWitness (populateAbsRem B C f) (populateMaxAbsCOr1 C f)
  else #v[0]

/-- The gated `U16CompareOperation` bit. -/
def ltBitWitness (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    Vector (ZMod p) 1 :=
  if ltGate ir C f = 1 then
    #v[U16CompareOperation.populate_bit
        (ltClWitness ir B C f)[0] (ltClWitness ir B C f)[1]]
  else #v[0]

end SP1Clean.DivRemChip
