import SP1Clean.Math.Word
import Clean.Utils.Bitwise
import Clean.Utils.Field
import Mathlib.Tactic.IntervalCases

/-! # Byte-level bitwise foundations

Helpers for the Bitwise (AND/OR/XOR) chip, kept separate from `Word.lean` so that
editing them does not re-elaborate the heavy `AddOperation` carry-chain proofs.

`byteOp` is the per-byte AND/OR/XOR (AND=0, OR=1, XOR=2, matching SP1's `ByteOpcode`);
`bitOp64` is the same on `BitVec 64`. The load-bearing lemma `reassemble_byteOp` lifts
eight per-byte equalities `r_k = byteOp op b_k c_k` to the 64-bit identity
`toBitVec64 (reassembled r) = bitOp64 op (…b) (…c)` — the bitwise analog of
`AddOperation`'s carry-chain reassembly. -/

namespace SP1Clean

variable {p : ℕ}

/-! ## `256` as a field constant (`ZMod p`, `Fact (2 ^ 17 < p)`) -/

@[simp] lemma val_256_zmod_p [NeZero p] [Fact (2 ^ 17 < p)] :
    (256 : ZMod p).val = 256 := by
  have : (131072 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  exact ZMod.val_natCast_of_lt (show (256 : ℕ) < p by omega)

lemma val_256_ne_zero [NeZero p] [Fact (2 ^ 17 < p)] : (256 : ZMod p) ≠ 0 := by
  simp [← ZMod.val_eq_zero, val_256_zmod_p]

/-! ## The byte operation (AND=0, OR=1, XOR=2) -/

/-- Per-byte bitwise op, opcode-indexed (AND=0, OR=1, XOR=2). Matches SP1's
`ByteOpcode.{AND,OR,XOR}.toNat`. -/
def byteOp (op a b : ℕ) : ℕ :=
  if op = 0 then a &&& b else if op = 1 then a ||| b else a ^^^ b

/-- The byte op of two bytes is a byte. -/
lemma byteOp_lt256 (op a b : ℕ) (ha : a < 256) (hb : b < 256) :
    byteOp op a b < 256 := by
  have ha8 : a < 2 ^ 8 := by omega
  have hb8 : b < 2 ^ 8 := by omega
  unfold byteOp
  split_ifs
  · have := Nat.and_lt_two_pow (n := 8) a hb8; omega
  · have := Nat.or_lt_two_pow (n := 8) ha8 hb8; omega
  · have := Nat.xor_lt_two_pow (n := 8) ha8 hb8; omega

/-- The byte op on `BitVec 64`, opcode-indexed to match `byteOp`. -/
def bitOp64 (op : ℕ) (x y : BitVec 64) : BitVec 64 :=
  if op = 0 then x &&& y else if op = 1 then x ||| y else x ^^^ y

@[simp] lemma byteOp_zero (a b : ℕ) : byteOp 0 a b = a &&& b := rfl
@[simp] lemma byteOp_one (a b : ℕ) : byteOp 1 a b = a ||| b := rfl
@[simp] lemma byteOp_two (a b : ℕ) : byteOp 2 a b = a ^^^ b := rfl
@[simp] lemma bitOp64_zero (x y : BitVec 64) : bitOp64 0 x y = x &&& y := rfl
@[simp] lemma bitOp64_one (x y : BitVec 64) : bitOp64 1 x y = x ||| y := rfl
@[simp] lemma bitOp64_two (x y : BitVec 64) : bitOp64 2 x y = x ^^^ y := rfl

/-! ## Base-2^8 reassembly of eight bytes -/

/-- Nested little-endian base-2^8 reassembly of eight bytes. -/
def asm8 (x0 x1 x2 x3 x4 x5 x6 x7 : ℕ) : ℕ :=
  x0 + 2 ^ 8 * (x1 + 2 ^ 8 * (x2 + 2 ^ 8 * (x3 + 2 ^ 8 *
    (x4 + 2 ^ 8 * (x5 + 2 ^ 8 * (x6 + 2 ^ 8 * x7))))))

/-- One peel of `testBit` through a base-2^8 step. -/
private lemma testBit_step (a b j : ℕ) (hb : b < 2 ^ 8) :
    (b + 2 ^ 8 * a).testBit j = if j < 8 then b.testBit j else a.testBit (j - 8) := by
  rw [add_comm]; exact Nat.testBit_two_pow_mul_add a hb j

-- The top byte (`b7`/`c7`) needs no `< 2^8` bound: it is never a low part in the
-- `testBit_step` peel, only the high `a`. So the reassembly lemmas omit it.

/-- Bytewise AND reassembles: the base-2^8 assembly of the per-byte ANDs equals the
AND of the assemblies. -/
lemma asm8_and (b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 : ℕ)
    (hb0 : b0 < 2 ^ 8) (hb1 : b1 < 2 ^ 8) (hb2 : b2 < 2 ^ 8) (hb3 : b3 < 2 ^ 8)
    (hb4 : b4 < 2 ^ 8) (hb5 : b5 < 2 ^ 8) (hb6 : b6 < 2 ^ 8)
    (hc0 : c0 < 2 ^ 8) (hc1 : c1 < 2 ^ 8) (hc2 : c2 < 2 ^ 8) (hc3 : c3 < 2 ^ 8)
    (hc4 : c4 < 2 ^ 8) (hc5 : c5 < 2 ^ 8) (hc6 : c6 < 2 ^ 8) :
    asm8 (b0 &&& c0) (b1 &&& c1) (b2 &&& c2) (b3 &&& c3)
         (b4 &&& c4) (b5 &&& c5) (b6 &&& c6) (b7 &&& c7)
      = asm8 b0 b1 b2 b3 b4 b5 b6 b7 &&& asm8 c0 c1 c2 c3 c4 c5 c6 c7 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and]
  simp only [asm8, testBit_step, Nat.testBit_and,
    Nat.and_lt_two_pow _ hc0, Nat.and_lt_two_pow _ hc1, Nat.and_lt_two_pow _ hc2,
    Nat.and_lt_two_pow _ hc3, Nat.and_lt_two_pow _ hc4, Nat.and_lt_two_pow _ hc5,
    Nat.and_lt_two_pow _ hc6,
    hb0, hb1, hb2, hb3, hb4, hb5, hb6, hc0, hc1, hc2, hc3, hc4, hc5, hc6]
  split_ifs <;> simp

/-- Bytewise OR reassembles. -/
lemma asm8_or (b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 : ℕ)
    (hb0 : b0 < 2 ^ 8) (hb1 : b1 < 2 ^ 8) (hb2 : b2 < 2 ^ 8) (hb3 : b3 < 2 ^ 8)
    (hb4 : b4 < 2 ^ 8) (hb5 : b5 < 2 ^ 8) (hb6 : b6 < 2 ^ 8)
    (hc0 : c0 < 2 ^ 8) (hc1 : c1 < 2 ^ 8) (hc2 : c2 < 2 ^ 8) (hc3 : c3 < 2 ^ 8)
    (hc4 : c4 < 2 ^ 8) (hc5 : c5 < 2 ^ 8) (hc6 : c6 < 2 ^ 8) :
    asm8 (b0 ||| c0) (b1 ||| c1) (b2 ||| c2) (b3 ||| c3)
         (b4 ||| c4) (b5 ||| c5) (b6 ||| c6) (b7 ||| c7)
      = asm8 b0 b1 b2 b3 b4 b5 b6 b7 ||| asm8 c0 c1 c2 c3 c4 c5 c6 c7 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or]
  simp only [asm8, testBit_step, Nat.testBit_or,
    Nat.or_lt_two_pow hb0 hc0, Nat.or_lt_two_pow hb1 hc1, Nat.or_lt_two_pow hb2 hc2,
    Nat.or_lt_two_pow hb3 hc3, Nat.or_lt_two_pow hb4 hc4, Nat.or_lt_two_pow hb5 hc5,
    Nat.or_lt_two_pow hb6 hc6,
    hb0, hb1, hb2, hb3, hb4, hb5, hb6, hc0, hc1, hc2, hc3, hc4, hc5, hc6]
  split_ifs <;> simp

/-- Bytewise XOR reassembles. -/
lemma asm8_xor (b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 : ℕ)
    (hb0 : b0 < 2 ^ 8) (hb1 : b1 < 2 ^ 8) (hb2 : b2 < 2 ^ 8) (hb3 : b3 < 2 ^ 8)
    (hb4 : b4 < 2 ^ 8) (hb5 : b5 < 2 ^ 8) (hb6 : b6 < 2 ^ 8)
    (hc0 : c0 < 2 ^ 8) (hc1 : c1 < 2 ^ 8) (hc2 : c2 < 2 ^ 8) (hc3 : c3 < 2 ^ 8)
    (hc4 : c4 < 2 ^ 8) (hc5 : c5 < 2 ^ 8) (hc6 : c6 < 2 ^ 8) :
    asm8 (b0 ^^^ c0) (b1 ^^^ c1) (b2 ^^^ c2) (b3 ^^^ c3)
         (b4 ^^^ c4) (b5 ^^^ c5) (b6 ^^^ c6) (b7 ^^^ c7)
      = asm8 b0 b1 b2 b3 b4 b5 b6 b7 ^^^ asm8 c0 c1 c2 c3 c4 c5 c6 c7 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor]
  simp only [asm8, testBit_step, Nat.testBit_xor,
    Nat.xor_lt_two_pow hb0 hc0, Nat.xor_lt_two_pow hb1 hc1, Nat.xor_lt_two_pow hb2 hc2,
    Nat.xor_lt_two_pow hb3 hc3, Nat.xor_lt_two_pow hb4 hc4, Nat.xor_lt_two_pow hb5 hc5,
    Nat.xor_lt_two_pow hb6 hc6,
    hb0, hb1, hb2, hb3, hb4, hb5, hb6, hc0, hc1, hc2, hc3, hc4, hc5, hc6]
  split_ifs <;> simp

/-- **Keystone reassembly.** Given eight per-byte equalities `r_k = byteOp op b_k c_k`
(bytes `< 2^8`), the 64-bit `BitVec` of the assembled result equals the `bitOp64` of
the assembled operands. The bitwise analog of `AddOperation`'s carry-chain reassembly. -/
lemma reassemble_byteOp (op : ℕ) (hop : op < 3)
    (b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7
     r0 r1 r2 r3 r4 r5 r6 r7 : ℕ)
    (hb0 : b0 < 2 ^ 8) (hb1 : b1 < 2 ^ 8) (hb2 : b2 < 2 ^ 8) (hb3 : b3 < 2 ^ 8)
    (hb4 : b4 < 2 ^ 8) (hb5 : b5 < 2 ^ 8) (hb6 : b6 < 2 ^ 8)
    (hc0 : c0 < 2 ^ 8) (hc1 : c1 < 2 ^ 8) (hc2 : c2 < 2 ^ 8) (hc3 : c3 < 2 ^ 8)
    (hc4 : c4 < 2 ^ 8) (hc5 : c5 < 2 ^ 8) (hc6 : c6 < 2 ^ 8)
    (hr0 : r0 = byteOp op b0 c0) (hr1 : r1 = byteOp op b1 c1) (hr2 : r2 = byteOp op b2 c2)
    (hr3 : r3 = byteOp op b3 c3) (hr4 : r4 = byteOp op b4 c4) (hr5 : r5 = byteOp op b5 c5)
    (hr6 : r6 = byteOp op b6 c6) (hr7 : r7 = byteOp op b7 c7) :
    BitVec.ofNat 64 (asm8 r0 r1 r2 r3 r4 r5 r6 r7)
      = bitOp64 op (BitVec.ofNat 64 (asm8 b0 b1 b2 b3 b4 b5 b6 b7))
                   (BitVec.ofNat 64 (asm8 c0 c1 c2 c3 c4 c5 c6 c7)) := by
  subst hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7
  interval_cases op
  · simp only [byteOp_zero, bitOp64_zero]
    rw [asm8_and b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7
        hb0 hb1 hb2 hb3 hb4 hb5 hb6 hc0 hc1 hc2 hc3 hc4 hc5 hc6, BitVec.ofNat_and]
  · simp only [byteOp_one, bitOp64_one]
    rw [asm8_or b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7
        hb0 hb1 hb2 hb3 hb4 hb5 hb6 hc0 hc1 hc2 hc3 hc4 hc5 hc6, BitVec.ofNat_or]
  · simp only [byteOp_two, bitOp64_two]
    rw [asm8_xor b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7
        hb0 hb1 hb2 hb3 hb4 hb5 hb6 hc0 hc1 hc2 hc3 hc4 hc5 hc6, BitVec.ofNat_xor]

/-- Connector: a `Word`'s `toBitVec64` is the `BitVec.ofNat` of the base-2^8 assembly
of its bytes, given each limb's value splits as `lo + hi·256`. (The per-limb split is
supplied by the caller — in the gadget, from the witnessed low byte plus the
`(limb − low)·256⁻¹` high byte.) -/
lemma toBitVec64_asm8 [NeZero p] (w : Word (ZMod p)) (b0 b1 b2 b3 b4 b5 b6 b7 : ℕ)
    (h0 : w[0].val = b0 + b1 * 256) (h1 : w[1].val = b2 + b3 * 256)
    (h2 : w[2].val = b4 + b5 * 256) (h3 : w[3].val = b6 + b7 * 256) :
    Word.toBitVec64 w = BitVec.ofNat 64 (asm8 b0 b1 b2 b3 b4 b5 b6 b7) := by
  unfold Word.toBitVec64
  congr 1
  rw [Word.toNat_def, h0, h1, h2, h3]
  unfold asm8
  ring

/-- Value of a byte-pair limb: `(lo + hi·256).val = lo.val + hi.val·256` for bytes. -/
lemma val_lo_add_hi [NeZero p] [Fact (2 ^ 17 < p)] {lo hi : ZMod p}
    (hlo : lo.val < 256) (hhi : hi.val < 256) :
    (lo + hi * 256).val = lo.val + hi.val * 256 := by
  have hp : 2 ^ 17 < p := Fact.out
  have hmul : (hi * 256 : ZMod p).val = hi.val * 256 := by
    rw [ZMod.val_mul, val_256_zmod_p, Nat.mod_eq_of_lt (by omega)]
  rw [ZMod.val_add_of_lt (by rw [hmul]; omega), hmul]

end SP1Clean
