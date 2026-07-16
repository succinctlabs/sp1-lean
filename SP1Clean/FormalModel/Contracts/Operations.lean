import SP1Clean.FormalModel.Contracts.Readers
import SP1Clean.Extracted.AddwOperation
import SP1Clean.Extracted.SubwOperation
import SP1Clean.Extracted.MulOperation
import SP1Clean.Extracted.BitwiseOperation
import SP1Clean.Extracted.Circuit.BitwiseOperation
import SP1Clean.Extracted.U16CompareOperation
import SP1Clean.Extracted.Circuit.U16CompareOperation
import SP1Clean.Extracted.U16MSBOperation
import SP1Clean.Extracted.Circuit.U16MSBOperation
import SP1Clean.Extracted.U16toU8OperationUnsafe
import SP1Clean.Extracted.AddrAddOperation
import SP1Clean.Extracted.Circuit.AddrAddOperation
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
`Specs/` sequence; the structural `RawSpec`s stay in the per-operation proof files. Depends only on
`Foundations/` + `Extracted/` (+ `Specs.Reader` for sequencing). -/

namespace SP1Clean.U16MSBOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

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

-- `IsZeroOperation`, `IsZeroWordOperation`, `IsEqualWordOperation`: these three form a composition
-- chain (`IsEqualWord` composes `IsZeroWord` composes `IsZeroOperation`) using the `FormalAssertion`
-- circuit form. A composing op's `Extracted` imports the sub's `Formal` (for `.circuit`), so their
-- `Spec`s cannot live here (it would cycle: `Specs.Operation` → composer `Extracted` → sub `Formal`
-- → … → `Specs.Operation`). Each defines its `Spec` (and `spec_populate`) in its own
-- `Operations/<Op>/Formal.lean` instead.

namespace SP1Clean.AddrAddOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Semantic contract for the 48-bit address add: on a real row (`is_real`-gated) the 3-limb result
is the low 48 bits of the integer sum `a + b`, each limb a genuine 16-bit value. `Inputs` (the `eval`
params verbatim — the result column struct nested as `cols`) is the generated
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
      input.cols.value[2].val < 2 ^ 16

end SP1Clean.AddrAddOperation

namespace SP1Clean.AddressOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
local instance neZero_spec : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩

/-- The two operand words and the three witnessed offset bits. -/
structure Inputs (F : Type) where
  b : fields 4 F
  cc : fields 4 F
  offset_bit0 : F
  offset_bit1 : F
  offset_bit2 : F
deriving ProvableStruct

/-- Semantic contract: the address limbs are the low 48 bits of `b + cc` and the offset bits are
boolean. -/
def Spec (input : Inputs (ZMod p)) (cols : Extracted.AddressOperation (ZMod p)) : Prop :=
  (cols.addr_operation.value[0].val + 65536 * cols.addr_operation.value[1].val +
      65536 ^ 2 * cols.addr_operation.value[2].val =
    (Word.toNat input.b + Word.toNat input.cc) % 2 ^ 48) ∧
  (input.offset_bit0 = 0 ∨ input.offset_bit0 = 1) ∧
  (input.offset_bit1 = 0 ∨ input.offset_bit1 = 1) ∧
  (input.offset_bit2 = 0 ∨ input.offset_bit2 = 1)

end SP1Clean.AddressOperation

namespace SP1Clean.AddOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
local instance neZero_spec : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩

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
local instance neZero_spec : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩

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
local instance neZero_spec : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩

/-- The reconstructed 64-bit result word: the two witnessed low limbs, with the two high limbs
realised as the sign fill `msb * 0xFFFF`. (`Inputs`/`Spec`/`spec_populate` live in the op's
`Formal.lean` — the composed circuit form imports `U16MSBOperation.Formal`, so its `Spec` cannot live
here without an import cycle, mirroring the IsZero* chain above.) -/
def resultWord (cols : Extracted.AddwOperation (ZMod p)) : Word (ZMod p) :=
  #v[cols.value[0], cols.value[1], cols.msb.msb * 65535, cols.msb.msb * 65535]

end SP1Clean.AddwOperation

namespace SP1Clean.SubwOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
local instance neZero_spec : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩

/-- The reconstructed 64-bit result word: the two witnessed low limbs, with the two high limbs
realised as the sign fill `msb * 0xFFFF`. (`Inputs`/`Spec`/`spec_populate` live in the op's
`Formal.lean` — the composed circuit form imports `U16MSBOperation.Formal`, so its `Spec` cannot live
here without an import cycle, mirroring the IsZero* chain above.) -/
def resultWord (cols : Extracted.SubwOperation (ZMod p)) : Word (ZMod p) :=
  #v[cols.value[0], cols.value[1], cols.msb.msb * 65535, cols.msb.msb * 65535]

end SP1Clean.SubwOperation

-- `LtOperationSigned`'s `Inputs`/`Spec` live in `Operations/LtOperationSigned/`: the auto-generated
-- `Extracted.lean` owns the 5-field `Inputs` (`b`/`cc`/`cols`/`is_signed`/`is_real`), and `Formal.lean`
-- owns the structural `Spec` + the semantic `result_semantic` readout (the contract the chips consume).
-- It lives there (not here) to avoid an import cycle — the generated `main` imports the sub-ops' `.Formal`
-- for `.circuit` (same reasoning as the IsZero*/Addw/BitwiseU16 chains).

namespace SP1Clean.BitwiseOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

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
local instance neZero_spec : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩

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
