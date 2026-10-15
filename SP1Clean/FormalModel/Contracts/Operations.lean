module

public import SP1Clean.Math.Word
public import SP1Clean.Circuits.Types.AddOperation
public import SP1Clean.Circuits.Types.U16MSBOperation
public import SP1Clean.Circuits.Types.AddrAddOperation
public import SP1Clean.Circuits.Types.AddressOperation
import Mathlib.Data.Fin.VecNotation

/-! # Shared operation contracts

Input types, semantic relations and pure result helpers for operations awaiting feature separation.
Reader contracts and feature specifications have independent owners. Multiplication, safe byte
decomposition and bitwise operations live under `Semantics/Specs`; consumers import them directly.
Structural evidence stays with the operation implementations and proofs.
-/

@[expose] public section

namespace SP1Clean.AddrAddOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Inputs for the native 48-bit address-add gadget. -/
structure Inputs (F : Type) where
  a : Word F
  b : Word F
  cols : Circuits.Types.AddrAddOperation F
  is_real : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- Semantic contract for the 48-bit address add: on a real row (`is_real`-gated) the 3-limb result
is the low 48 bits of the integer sum `a + b`, each limb a genuine 16-bit value, and the
64-bit-truncated sum contains no bits above that 48-bit result. The final fact is forced by the
AIR's boolean high carry against zero; it is deliberately a conclusion rather than a soundness
precondition. The native input contains the result column struct as `cols`; its witnessed limbs
`input.cols.value` are threaded in by the
composing operation (via `populate`). The limb ranges + the sum uniquely pin every limb
(`value[i] = (addr / 2^16ⁱ) % 2^16`), which a composing `AddressOperation` needs to discharge its
inverse gate / offset decomposition in completeness. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  input.is_real = 1 →
    (input.cols.value[0].val + 65536 * input.cols.value[1].val +
        65536 ^ 2 * input.cols.value[2].val =
      (Word.toNat input.a + Word.toNat input.b) % 2 ^ 48) ∧
    input.cols.value[0].val < 2 ^ 16 ∧ input.cols.value[1].val < 2 ^ 16 ∧
      input.cols.value[2].val < 2 ^ 16 ∧
    (Word.toNat input.a + Word.toNat input.b) % 2 ^ 64 < 2 ^ 48

end SP1Clean.AddrAddOperation

namespace SP1Clean.AddressOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The two operand words, the three witnessed offset bits, and the row selector passed by the
composing load/store chip.  The selector is part of the operation input because upstream SP1 gates
the address-add carry chain, non-reserved-address inverse, and byte lookups by the chip's
`is_real`; only the three offset-bit boolean constraints are unconditional. -/
structure Inputs (F : Type) where
  b : fields 4 F
  cc : fields 4 F
  offset_bit0 : F
  offset_bit1 : F
  offset_bit2 : F
  is_real : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- The aligned address returned by SP1's `AddressOperation::eval`.  The operation's witnessed
columns retain the raw effective address `b + cc`; the value passed to the Memory bus clears its
low three bits by subtracting the separately constrained offset bits.  Keeping this projection on
the contract surface makes the distinction between the Sail-visible effective address and the
8-byte-aligned RAM-bus address explicit. -/
@[reducible] def alignedValue {F : Type} [Sub F] [Mul F] [OfNat F 2] [OfNat F 4]
    (input : Inputs F)
    (cols : Circuits.Types.AddressOperation F) : Vector F 3 :=
  #v[cols.addr_operation.value[0] - 4 * input.offset_bit2 - 2 * input.offset_bit1 -
      input.offset_bit0,
    cols.addr_operation.value[1], cols.addr_operation.value[2]]

/-- The output-independent address property enforced by SP1's `AddressOperation`: a 48-bit,
non-reserved effective address whose low three bits are exactly the supplied offset columns. This
is the compact semantic interface consumed by the Sail load/store bridges. -/
def ValidAddress (input : Inputs (ZMod p)) : Prop :=
  (Word.toNat input.b + Word.toNat input.cc) % 2 ^ 64 < 2 ^ 48 ∧
  2 ^ 16 ≤ (Word.toNat input.b + Word.toNat input.cc) % 2 ^ 48 ∧
  input.offset_bit0.val + 2 * input.offset_bit1.val + 4 * input.offset_bit2.val =
    (Word.toNat input.b + Word.toNat input.cc) % 2 ^ 48 % 8

/-- The effective byte address computed by SP1 and by Sail. Both additions are 64-bit wrapping
additions; the aligned RAM-bus address is a separate projection obtained by clearing the low bits. -/
def effectiveAddress (input : Inputs (ZMod p)) : BitVec 64 :=
  Word.toBitVec64 input.b + Word.toBitVec64 input.cc

omit [Fact (2 ^ 17 < p)] in
/-- `effectiveAddress` is exactly Rust's `u64::wrapping_add`, expressed through the semantic word
encoding. This is the shared bridge fact that permits negative sign-extended load/store immediates. -/
theorem effectiveAddress_toNat {input : Inputs (ZMod p)}
    (hb : Word.isU64 input.b) (hcc : Word.isU64 input.cc) :
    (effectiveAddress input).toNat =
      (Word.toNat input.b + Word.toNat input.cc) % 2 ^ 64 := by
  rw [effectiveAddress, BitVec.toNat_add, Word.toBitVec64_toNat hb, Word.toBitVec64_toNat hcc]

omit [Fact (2 ^ 17 < p)] in
/-- The compact AIR address contract, rephrased at the actual wrapped effective address consumed by
the Sail memory semantics. In particular, this does not assume that the natural-number sum of the
base and sign-extended immediate avoids 64-bit wraparound. -/
theorem effectiveAddress_facts {input : Inputs (ZMod p)}
    (hb : Word.isU64 input.b) (hcc : Word.isU64 input.cc)
    (h : ValidAddress input) :
    (effectiveAddress input).toNat < 2 ^ 48 ∧
      2 ^ 16 ≤ (effectiveAddress input).toNat ∧
      input.offset_bit0.val + 2 * input.offset_bit1.val + 4 * input.offset_bit2.val =
        (effectiveAddress input).toNat % 8 := by
  obtain ⟨hfit, hlo, hoffset⟩ := h
  have hmod :
      (Word.toNat input.b + Word.toNat input.cc) % 2 ^ 48 =
        (Word.toNat input.b + Word.toNat input.cc) % 2 ^ 64 := by
    rw [← Nat.mod_mod_of_dvd _ (by norm_num : 2 ^ 48 ∣ (2 ^ 64 : ℕ)),
      Nat.mod_eq_of_lt hfit]
  rw [effectiveAddress_toNat hb hcc]
  exact ⟨hfit, hmod ▸ hlo, by rwa [← hmod]⟩

omit [Fact (2 ^ 17 < p)] in
/-- The 48-bit address reconstructed by the AIR is the natural value of the wrapped 64-bit effective
address. This is the common reconciliation used by load/store row views: the AIR separately proves
that the wrapped result lies below `2^48`, so reducing that result modulo `2^48` is lossless. -/
theorem addressMod48_eq_effectiveAddress_toNat {input : Inputs (ZMod p)}
    (hb : Word.isU64 input.b) (hcc : Word.isU64 input.cc)
    (h : ValidAddress input) :
    (Word.toNat input.b + Word.toNat input.cc) % 2 ^ 48 =
      (effectiveAddress input).toNat := by
  have hfit := (effectiveAddress_facts hb hcc h).1
  rw [← Nat.mod_mod_of_dvd _ (by norm_num : 2 ^ 48 ∣ (2 ^ 64 : ℕ)),
    ← effectiveAddress_toNat hb hcc, Nat.mod_eq_of_lt hfit]

/-- Semantic contract: the address limbs are the low 48 bits of `b + cc`; the sum has no
64-bit-truncated bits above that address; the offset bits are boolean and exactly decompose the
address modulo eight; the address is outside SP1's reserved low-memory region; and all three
committed address limbs are genuine 16-bit limbs. Every conjunct is forced by the operation's AIR
(respectively the address-add carry chain and byte-range pulls, offset boolean gates, low-three-bit
range check, and top-two-limb inverse gate). Keeping the limb bounds on this semantic surface is
important: the machine layer interprets the three fields as one canonical 48-bit byte address. -/
def Spec (input : Inputs (ZMod p)) (cols : Circuits.Types.AddressOperation (ZMod p)) : Prop :=
  (cols.addr_operation.value[0].val + 65536 * cols.addr_operation.value[1].val +
      65536 ^ 2 * cols.addr_operation.value[2].val =
    (Word.toNat input.b + Word.toNat input.cc) % 2 ^ 48) ∧
  (input.offset_bit0 = 0 ∨ input.offset_bit0 = 1) ∧
  (input.offset_bit1 = 0 ∨ input.offset_bit1 = 1) ∧
  (input.offset_bit2 = 0 ∨ input.offset_bit2 = 1) ∧
  (Word.toNat input.b + Word.toNat input.cc) % 2 ^ 64 < 2 ^ 48 ∧
  2 ^ 16 ≤ (Word.toNat input.b + Word.toNat input.cc) % 2 ^ 48 ∧
  input.offset_bit0.val + 2 * input.offset_bit1.val + 4 * input.offset_bit2.val =
    (Word.toNat input.b + Word.toNat input.cc) % 2 ^ 48 % 8 ∧
  cols.addr_operation.value[0].val < 2 ^ 16 ∧
  cols.addr_operation.value[1].val < 2 ^ 16 ∧
  cols.addr_operation.value[2].val < 2 ^ 16

/-- Per-row semantic contract matching SP1's `AddressOperation::eval`: the three offset columns are
boolean on every row, while the address-add chain, non-reserved-address inverse, and byte lookup
only claim an effective address on a real row.  Keeping the unconditional booleans here is
important for parent load/store selector equations, which Rust also leaves ungated. -/
def RowSpec (input : Inputs (ZMod p)) (cols : Circuits.Types.AddressOperation (ZMod p)) : Prop :=
  (input.offset_bit0 = 0 ∨ input.offset_bit0 = 1) ∧
    (input.offset_bit1 = 0 ∨ input.offset_bit1 = 1) ∧
    (input.offset_bit2 = 0 ∨ input.offset_bit2 = 1) ∧
    (input.is_real = 1 → Spec input cols)

omit [Fact (2 ^ 17 < p)] in
/-- Project the compact Sail-facing address contract from the complete operation `Spec`. -/
theorem validAddress_of_spec {input : Inputs (ZMod p)}
    {cols : Circuits.Types.AddressOperation (ZMod p)} (h : Spec input cols) :
    ValidAddress input :=
  ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

omit [Fact (2 ^ 17 < p)] in
/-- The retained address-add byte pulls make the public three-limb address representation
canonical. This projection is used by the RAM-cell bridge without reopening the circuit. -/
theorem limbBounds_of_spec {input : Inputs (ZMod p)}
    {cols : Circuits.Types.AddressOperation (ZMod p)} (h : Spec input cols) :
    cols.addr_operation.value[0].val < 2 ^ 16 ∧
      cols.addr_operation.value[1].val < 2 ^ 16 ∧
      cols.addr_operation.value[2].val < 2 ^ 16 :=
  h.2.2.2.2.2.2.2

end SP1Clean.AddressOperation

namespace SP1Clean.AddOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Local addition-gadget inputs. Rust operation inputs are deliberately not an interface here. -/
structure Inputs (F : Type) where
  a : Word F
  b : Word F
  cols : Circuits.Types.AddOperation F
  is_real : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- Semantic contract (`is_real`-gated, mirroring the readers): on a real row the result is a 64-bit
value equal to the BitVec sum of the operands. On padding (`is_real = 0`) it is vacuous — the gadget's
gated carry/byte constraints impose nothing there. The result word is `input.cols.value`, witnessed by
the composing chip via `populate`; neither the input nor column layout is required to match Rust. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  input.is_real = 1 →
    Word.isU64 input.cols.value ∧
    Word.toBitVec64 input.cols.value = Word.toBitVec64 input.a + Word.toBitVec64 input.b

end SP1Clean.AddOperation

namespace SP1Clean.SubOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Proof-oriented local columns for the subtraction gadget. The assembled chip faithfulness map is
the only place that relates this shape to SP1 Rust's helper-operation columns. -/
structure Columns (F : Type) where
  value : Word F
deriving ProvableStruct
provable_struct_eval_lemmas Columns

/-- Local subtraction-gadget inputs. Rust operation inputs are deliberately not an interface here. -/
structure Inputs (F : Type) where
  a : Word F
  b : Word F
  cols : Columns F
  is_real : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- Semantic contract (`is_real`-gated): on a real row the result is a 64-bit value equal to the BitVec
difference of the operands. On padding (`is_real = 0`) it is vacuous. The result word is witnessed by
the composing chip via `populate`; neither the input nor column layout is required to match Rust. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  input.is_real = 1 →
    Word.isU64 input.cols.value ∧
    Word.toBitVec64 input.cols.value = Word.toBitVec64 input.a - Word.toBitVec64 input.b

end SP1Clean.SubOperation

namespace SP1Clean.AddwOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Proof-oriented local columns for the 32-bit add gadget: the two witnessed low result limbs
plus the composed sign-bit block (the shared `Circuits.Types.U16MSBOperation` struct, kept because the
native gadget composes `U16MSBOperation.circuit`). The assembled chip faithfulness map is the only
place that relates this shape to SP1 Rust's helper-operation columns. -/
structure Columns (F : Type) where
  value : Vector F 2
  msb : Circuits.Types.U16MSBOperation F
deriving ProvableStruct
provable_struct_eval_lemmas Columns

/-- Inputs for the native 32-bit add-with-sign-extension gadget. -/
structure Inputs (F : Type) where
  a : Word F
  b : Word F
  cols : Columns F
  is_real : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- The reconstructed 64-bit result word: the two witnessed low limbs, with the two high limbs
realised as the sign fill `msb * 0xFFFF`. -/
def resultWord (cols : Columns (ZMod p)) : Word (ZMod p) :=
  #v[cols.value[0], cols.value[1], cols.msb.msb * 65535, cols.msb.msb * 65535]

end SP1Clean.AddwOperation

namespace SP1Clean.SubwOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Proof-oriented local columns for the 32-bit subtract gadget: the two witnessed low result limbs
plus the composed sign-bit block (the shared `Circuits.Types.U16MSBOperation` struct, kept because the
native gadget composes `U16MSBOperation.circuit`). The assembled chip faithfulness map is the only
place that relates this shape to SP1 Rust's helper-operation columns. -/
structure Columns (F : Type) where
  value : Vector F 2
  msb : Circuits.Types.U16MSBOperation F
deriving ProvableStruct
provable_struct_eval_lemmas Columns

/-- Inputs for the native 32-bit subtract-with-sign-extension gadget. -/
structure Inputs (F : Type) where
  a : Word F
  b : Word F
  cols : Columns F
  is_real : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- The reconstructed 64-bit result word: the two witnessed low limbs, with the two high limbs
realised as the sign fill `msb * 0xFFFF`. -/
def resultWord (cols : Columns (ZMod p)) : Word (ZMod p) :=
  #v[cols.value[0], cols.value[1], cols.msb.msb * 65535, cols.msb.msb * 65535]

end SP1Clean.SubwOperation
