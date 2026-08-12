import SP1Clean.FormalModel.Contracts.Readers
import SP1Clean.Extracted.MulOperation
import SP1Clean.Extracted.U16CompareOperation
import SP1Clean.Extracted.U16MSBOperation
import SP1Clean.Extracted.U16toU8OperationUnsafe
import SP1Clean.Extracted.AddrAddOperation
import SP1Clean.Extracted.AddressOperation
import SP1Clean.Extracted.IsZeroOperation
import SP1Clean.Extracted.IsZeroWordOperation
import SP1Clean.Extracted.IsEqualWordOperation
import SP1Clean.Extracted.LtOperationUnsigned
import SP1Clean.Extracted.LtOperationSigned
import Mathlib.Data.Fin.VecNotation

/-! # Consolidated specs — operation gadgets

The `Inputs` structs, semantic `Spec`s, and the pure result helpers a `Spec` directly needs
(`resultWord`, and Mul's `productVal`) for the witnessed operation gadgets. Second file in the
`FormalModel/Contracts/` sequence (`Readers.lean → Operations.lean → Chips.lean`); the structural
`RawSpec`s stay in the per-operation proof files. Depends only on
`Math/` + `Model/` + `Extracted/` (+ `Contracts/Readers.lean` for sequencing). -/

namespace SP1Clean.U16MSBOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Proof-oriented inputs for the native MSB gadget. The column payload remains the exact Rust
anchor type, but the circuit interface is owned by the formal model. -/
structure Inputs (F : Type) where
  a : F
  cols : Extracted.U16MSBOperation F
  is_real : F
deriving ProvableStruct

/-- Semantic contract: `msb`'s booleanness holds **unconditionally** (SP1's `eval_msb` asserts it
ungated, so it must hold on padding too), and on a real row (`is_real`-gated) the witnessed `msb` is
the high bit of `a`. `Inputs` (the `eval` params verbatim — the result column struct nested as `cols`)
is the generated `Operations.U16MSBOperation.Extracted`; the witnessed bit is `input.cols.msb`,
threaded in by the composing operation (via `populate_msb`). -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  (input.cols.msb = 0 ∨ input.cols.msb = 1) ∧
  (input.is_real = 1 → input.cols.msb = if input.a.val ≥ 32768 then 1 else 0)

end SP1Clean.U16MSBOperation

namespace SP1Clean.U16CompareOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Proof-oriented inputs for the native 16-bit comparison gadget. -/
structure Inputs (F : Type) where
  a : F
  b : F
  cols : Extracted.U16CompareOperation F
  is_real : F
deriving ProvableStruct

/-- Semantic contract: `bit`'s booleanness holds **unconditionally** (SP1's `eval` asserts it ungated,
so it must hold on padding too), and on a real row (`is_real`-gated) the witnessed `bit` is the strict
less-than indicator of `a` vs `b`. `Inputs` (the `eval` params verbatim — the result column struct
nested as `cols`) is the generated `Operations.U16CompareOperation.Extracted`; the witnessed bit is
`input.cols.bit`, threaded in by the composing operation (via `populate_bit`). -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  (input.cols.bit = 0 ∨ input.cols.bit = 1) ∧
  (input.is_real = 1 → input.cols.bit = if input.a.val < input.b.val then 1 else 0)

end SP1Clean.U16CompareOperation

namespace SP1Clean.U16toU8OperationSafe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The four 16-bit input limbs to split, the already-`populate`d low-byte column struct, and the
`is_real` gate (the `eval` params verbatim, faithful to SP1's `U16toU8OperationSafeInput`). -/
structure Inputs (F : Type) where
  u16_values : fields 4 F
  cols : Extracted.U16toU8Operation F
  is_real : F
deriving ProvableStruct

/-- The ungated byte-decomposition content (2-arg, over explicit operand limbs + columns): for each
limb the low and high bytes are genuine bytes and reassemble the limb. Reused by composing operations
(e.g. `MulOperation`) that need the decomposition fact directly. -/
def DecompSpec (u16_values : Word (ZMod p)) (cols : Extracted.U16toU8Operation (ZMod p)) : Prop :=
  ∀ i : Fin 4,
    cols.low_bytes[i].val < 256 ∧
    ((u16_values[i] - cols.low_bytes[i]) * 256⁻¹).val < 256 ∧
    u16_values[i] = cols.low_bytes[i] + (u16_values[i] - cols.low_bytes[i]) * 256⁻¹ * 256

/-- Semantic contract (`is_real`-gated, `FormalAssertion`-style): on a real row, the eight output bytes
are the little-endian decomposition of the four limbs. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  input.is_real = 1 → DecompSpec input.u16_values input.cols

end SP1Clean.U16toU8OperationSafe

namespace SP1Clean.U16toU8OperationUnsafe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The four 16-bit input limbs to split, plus the low-byte column struct (a chip-owned input,
faithful to SP1's `eval_u16_to_u8_unsafe(_, u16_values, cols)`, which witnesses nothing). -/
structure Inputs (F : Type) where
  u16_values : fields 4 F
  cols : Extracted.U16toU8Operation F
deriving ProvableStruct

/-- Semantic contract: the low/high split reassembles each limb (the unsafe op's only content —
`256 * ((u - low) * 256⁻¹) = u - low`, so `low + 256 * high = u`). Holds unconditionally — the op
emits no constraints. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  input.u16_values[0] = input.cols.low_bytes[0] + (input.u16_values[0] - input.cols.low_bytes[0]) * 256⁻¹ * 256 ∧
  input.u16_values[1] = input.cols.low_bytes[1] + (input.u16_values[1] - input.cols.low_bytes[1]) * 256⁻¹ * 256 ∧
  input.u16_values[2] = input.cols.low_bytes[2] + (input.u16_values[2] - input.cols.low_bytes[2]) * 256⁻¹ * 256 ∧
  input.u16_values[3] = input.cols.low_bytes[3] + (input.u16_values[3] - input.cols.low_bytes[3]) * 256⁻¹ * 256

end SP1Clean.U16toU8OperationUnsafe

namespace SP1Clean.IsZeroOperation

/-- Inputs for the native field-zero test. -/
structure Inputs (F : Type) where
  a : F
  cols : Extracted.IsZeroOperation F
  is_real : F
deriving ProvableStruct

end SP1Clean.IsZeroOperation

namespace SP1Clean.IsZeroWordOperation

/-- Inputs for the native word-zero test. -/
structure Inputs (F : Type) where
  a : Word F
  cols : Extracted.IsZeroWordOperation F
  is_real : F
deriving ProvableStruct

end SP1Clean.IsZeroWordOperation

namespace SP1Clean.IsEqualWordOperation

/-- Inputs for the native word-equality test. -/
structure Inputs (F : Type) where
  a : Word F
  b : Word F
  cols : Extracted.IsEqualWordOperation F
  is_real : F
deriving ProvableStruct

end SP1Clean.IsEqualWordOperation

-- The IsZero composition chain keeps its focused semantic contracts beside its proofs; the stable
-- input interfaces live here so the native circuits no longer depend on generated circuit modules.

namespace SP1Clean.AddrAddOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Inputs for the native 48-bit address-add gadget. -/
structure Inputs (F : Type) where
  a : Word F
  b : Word F
  cols : Extracted.AddrAddOperation F
  is_real : F
deriving ProvableStruct

/-- Semantic contract for the 48-bit address add: on a real row (`is_real`-gated) the 3-limb result
is the low 48 bits of the integer sum `a + b`, each limb a genuine 16-bit value, and the
64-bit-truncated sum contains no bits above that 48-bit result. The final fact is forced by the
AIR's boolean high carry against zero; it is deliberately a conclusion rather than a soundness
precondition. `Inputs` (the `eval` params verbatim — the result column struct nested as `cols`) is the generated
`Operations.AddrAddOperation.Extracted`; the witnessed limbs `input.cols.value` are threaded in by the
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

/-- The aligned address returned by SP1's `AddressOperation::eval`.  The operation's witnessed
columns retain the raw effective address `b + cc`; the value passed to the Memory bus clears its
low three bits by subtracting the separately constrained offset bits.  Keeping this projection on
the contract surface makes the distinction between the Sail-visible effective address and the
8-byte-aligned RAM-bus address explicit. -/
@[reducible] def alignedValue {F : Type} [Sub F] [Mul F] [OfNat F 2] [OfNat F 4]
    (input : Inputs F)
    (cols : Extracted.AddressOperation F) : Vector F 3 :=
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
def Spec (input : Inputs (ZMod p)) (cols : Extracted.AddressOperation (ZMod p)) : Prop :=
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
def RowSpec (input : Inputs (ZMod p)) (cols : Extracted.AddressOperation (ZMod p)) : Prop :=
  (input.offset_bit0 = 0 ∨ input.offset_bit0 = 1) ∧
    (input.offset_bit1 = 0 ∨ input.offset_bit1 = 1) ∧
    (input.offset_bit2 = 0 ∨ input.offset_bit2 = 1) ∧
    (input.is_real = 1 → Spec input cols)

omit [Fact (2 ^ 17 < p)] in
/-- Project the compact Sail-facing address contract from the complete operation `Spec`. -/
theorem validAddress_of_spec {input : Inputs (ZMod p)}
    {cols : Extracted.AddressOperation (ZMod p)} (h : Spec input cols) :
    ValidAddress input :=
  ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

omit [Fact (2 ^ 17 < p)] in
/-- The retained address-add byte pulls make the public three-limb address representation
canonical. This projection is used by the RAM-cell bridge without reopening the circuit. -/
theorem limbBounds_of_spec {input : Inputs (ZMod p)}
    {cols : Extracted.AddressOperation (ZMod p)} (h : Spec input cols) :
    cols.addr_operation.value[0].val < 2 ^ 16 ∧
      cols.addr_operation.value[1].val < 2 ^ 16 ∧
      cols.addr_operation.value[2].val < 2 ^ 16 :=
  h.2.2.2.2.2.2.2

end SP1Clean.AddressOperation

namespace SP1Clean.AddOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Proof-oriented local columns for the addition gadget. This shape is independent of SP1 Rust's
`AddOperation` columns; the assembled chip faithfulness map is the only place that relates them. -/
structure Columns (F : Type) where
  value : Word F
deriving ProvableStruct

/-- Local addition-gadget inputs. Rust operation inputs are deliberately not an interface here. -/
structure Inputs (F : Type) where
  a : Word F
  b : Word F
  cols : Columns F
  is_real : F
deriving ProvableStruct

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

/-- Local subtraction-gadget inputs. Rust operation inputs are deliberately not an interface here. -/
structure Inputs (F : Type) where
  a : Word F
  b : Word F
  cols : Columns F
  is_real : F
deriving ProvableStruct

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
plus the composed sign-bit block (the shared `Extracted.U16MSBOperation` struct, kept because the
native gadget composes `U16MSBOperation.circuit`). The assembled chip faithfulness map is the only
place that relates this shape to SP1 Rust's helper-operation columns. -/
structure Columns (F : Type) where
  value : Vector F 2
  msb : Extracted.U16MSBOperation F
deriving ProvableStruct

/-- Inputs for the native 32-bit add-with-sign-extension gadget. -/
structure Inputs (F : Type) where
  a : Word F
  b : Word F
  cols : Columns F
  is_real : F
deriving ProvableStruct

/-- The reconstructed 64-bit result word: the two witnessed low limbs, with the two high limbs
realised as the sign fill `msb * 0xFFFF`. (`Inputs`/`Spec`/`spec_populate` live in the op's
`Formal.lean` — the composed circuit form imports `U16MSBOperation.Formal`, so its `Spec` cannot live
here without an import cycle, mirroring the IsZero* chain above.) -/
def resultWord (cols : Columns (ZMod p)) : Word (ZMod p) :=
  #v[cols.value[0], cols.value[1], cols.msb.msb * 65535, cols.msb.msb * 65535]

end SP1Clean.AddwOperation

namespace SP1Clean.SubwOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Proof-oriented local columns for the 32-bit subtract gadget: the two witnessed low result limbs
plus the composed sign-bit block (the shared `Extracted.U16MSBOperation` struct, kept because the
native gadget composes `U16MSBOperation.circuit`). The assembled chip faithfulness map is the only
place that relates this shape to SP1 Rust's helper-operation columns. -/
structure Columns (F : Type) where
  value : Vector F 2
  msb : Extracted.U16MSBOperation F
deriving ProvableStruct

/-- Inputs for the native 32-bit subtract-with-sign-extension gadget. -/
structure Inputs (F : Type) where
  a : Word F
  b : Word F
  cols : Columns F
  is_real : F
deriving ProvableStruct

/-- The reconstructed 64-bit result word: the two witnessed low limbs, with the two high limbs
realised as the sign fill `msb * 0xFFFF`. (`Inputs`/`Spec`/`spec_populate` live in the op's
`Formal.lean` — the composed circuit form imports `U16MSBOperation.Formal`, so its `Spec` cannot live
here without an import cycle, mirroring the IsZero* chain above.) -/
def resultWord (cols : Columns (ZMod p)) : Word (ZMod p) :=
  #v[cols.value[0], cols.value[1], cols.msb.msb * 65535, cols.msb.msb * 65535]

end SP1Clean.SubwOperation

namespace SP1Clean.LtOperationUnsigned

/-- Inputs for the native unsigned word comparison gadget. -/
structure Inputs (F : Type) where
  b : Word F
  cc : Word F
  cols : Extracted.LtOperationUnsigned F
  is_real : F
deriving ProvableStruct

end SP1Clean.LtOperationUnsigned

namespace SP1Clean.LtOperationSigned

/-- Inputs for the native signed/unsigned word comparison selector gadget. -/
structure Inputs (F : Type) where
  b : Word F
  cc : Word F
  cols : Extracted.LtOperationSigned F
  is_signed : F
  is_real : F
deriving ProvableStruct

end SP1Clean.LtOperationSigned

namespace SP1Clean.BitwiseOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Proof-oriented local columns for the bytewise bitwise gadget: the eight witnessed result bytes.
The assembled chip faithfulness map is the only place that relates this shape to SP1 Rust's
helper-operation columns. -/
structure Columns (F : Type) where
  result : Vector F 8
deriving ProvableStruct

/-- Inputs for the native bytewise bitwise gadget. -/
structure Inputs (F : Type) where
  a : Vector F 8
  b : Vector F 8
  cols : Columns F
  opcode : F
  is_real : F
deriving ProvableStruct

/-- Semantic, `is_real`- and opcode-gated contract: on a real row each result byte is the bitwise
AND/OR/XOR of the operand bytes (as 8-bit values), **and the operand bytes are genuine bytes** — the
byte table guarantees `a[i], b[i] < 256` for every fired send, so soundness exports those bounds and a
composing operation (e.g. `BitwiseU16Operation`) can consume them without having to range-check the
free byte columns itself. On padding (`is_real = 0`) it is vacuous — the gadget's gated byte-bus pulls
impose nothing there. `Inputs` (the `eval` params verbatim — the result column struct nested as `cols`)
is the generated `Operations.BitwiseOperation.Extracted`; the result bytes are `input.cols.result`,
threaded in by the composing operation. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  input.is_real = 1 →
    (∀ i : Fin 8, input.a[i].val < 256 ∧ input.b[i].val < 256) ∧
    (input.opcode = 0 → ∀ i : Fin 8, input.cols.result[i].val = input.a[i].val &&& input.b[i].val) ∧
    (input.opcode = 1 → ∀ i : Fin 8, input.cols.result[i].val = input.a[i].val ||| input.b[i].val) ∧
    (input.opcode = 2 → ∀ i : Fin 8, input.cols.result[i].val = input.a[i].val ^^^ input.b[i].val)

end SP1Clean.BitwiseOperation

-- `BitwiseU16Operation`'s `Inputs`/`Spec`/`resultWord`/`decompBytes` live in
-- `Operations/BitwiseU16Operation.lean`: the composed `FormalAssertion` imports `BitwiseOperation.Formal`
-- for `.circuit`, and its `Spec` is literally the composed `BitwiseOperation.Spec` on the two `U16toU8`
-- byte decompositions (same reasoning as the IsZero* / Addw chains above).

namespace SP1Clean.MulOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- The two operand words, the already-`populate`d column struct, the `is_real` gate, and the five
variant selectors (the `eval` params verbatim, faithful to SP1's `MulOperation::eval`). The result
word is **reconstructed** from the `product` columns (see `resultWord`), placed at the chip level. -/
structure Inputs (F : Type) where
  b : fields 4 F
  c : fields 4 F
  cols : Extracted.MulOperation F
  is_real : F
  is_mul : F
  is_mulh : F
  is_mulhu : F
  is_mulhsu : F
  is_mulw : F
deriving ProvableStruct

/-- Witnessed product byte `k`, `0` outside `0..15`. -/
def productVal (cols : Extracted.MulOperation (ZMod p)) (k : ℕ) : ZMod p :=
  if h : k < 16 then cols.product[k]'h else 0

/-- The 64-bit result word, read off the witnessed `product` per active variant: the low 64 bits
(bytes `0..7`) for `MUL`; the high 64 bits (bytes `8..15`) for the `MULH*` family; the
sign-extended low 32 bits for `MULW`. -/
def resultWord (input : Inputs (ZMod p)) (cols : Extracted.MulOperation (ZMod p)) : Word (ZMod p) :=
  if input.is_mulw = 1 then
    #v[productVal cols 0 + productVal cols 1 * 256, productVal cols 2 + productVal cols 3 * 256,
       cols.product_msb.msb * 65535, cols.product_msb.msb * 65535]
  else if input.is_mulh = 1 ∨ input.is_mulhu = 1 ∨ input.is_mulhsu = 1 then
    #v[productVal cols 8 + productVal cols 9 * 256, productVal cols 10 + productVal cols 11 * 256,
       productVal cols 12 + productVal cols 13 * 256, productVal cols 14 + productVal cols 15 * 256]
  else
    #v[productVal cols 0 + productVal cols 1 * 256, productVal cols 2 + productVal cols 3 * 256,
       productVal cols 4 + productVal cols 5 * 256, productVal cols 6 + productVal cols 7 * 256]

/-- The ungated semantic content (2-arg, over an explicit `cols`): the reconstructed result is the
appropriate slice of the `BitVec` product for the active variant — low 64 for `MUL`, high 64 of the
unsigned/signed 128-bit product for the `MULH*` family, sign-extended low 32 for `MULW`. The
`FormalAssertion` `Spec` (below) gates this on `is_real`. -/
def SemanticSpec (input : Inputs (ZMod p)) (cols : Extracted.MulOperation (ZMod p)) : Prop :=
  (resultWord input cols).isU64 ∧
  (input.is_mul = 1 →
    Word.toBitVec64 (resultWord input cols)
      = Word.toBitVec64 input.b * Word.toBitVec64 input.c) ∧
  (input.is_mulhu = 1 →
    Word.toBitVec64 (resultWord input cols)
      = (((Word.toBitVec64 input.b).setWidth 128 * (Word.toBitVec64 input.c).setWidth 128)
          >>> 64).setWidth 64) ∧
  (input.is_mulh = 1 →
    Word.toBitVec64 (resultWord input cols)
      = (((Word.toBitVec64 input.b).signExtend 128 * (Word.toBitVec64 input.c).signExtend 128)
          >>> 64).setWidth 64) ∧
  (input.is_mulhsu = 1 →
    Word.toBitVec64 (resultWord input cols)
      = (((Word.toBitVec64 input.b).signExtend 128 * (Word.toBitVec64 input.c).setWidth 128)
          >>> 64).setWidth 64) ∧
  (input.is_mulw = 1 →
    Word.toBitVec64 (resultWord input cols)
      = ((Word.toBitVec64 input.b * Word.toBitVec64 input.c).setWidth 32).signExtend 64)

end SP1Clean.MulOperation
