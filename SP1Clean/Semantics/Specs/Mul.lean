module

public import SP1Clean.Math.Word
public import SP1Clean.Circuits.Types.MulOperation

/-! # Multiplication operands and result interpretation

The operand interface, selector assumptions and five product interpretations are independent of
witness generation and circuit code. The complete intermediate certificate used for arbitrary-row
completeness remains in `Circuits/Gadgets/Mul/Arithmetic`, below the bundled gadget.
-/

@[expose] public section

namespace SP1Clean.MulOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- Multiplication operands, arithmetic columns, activity/variant selectors and the caller's
result word. The result remains explicit on disabled rows: SP1's product-MSB interaction reads
its second limb even when that interaction has zero multiplicity. -/
structure Inputs (F : Type) where
  /-- First operand, interpreted according to the selected variant. -/
  b : fields 4 F
  /-- Second operand, interpreted according to the selected variant. -/
  c : fields 4 F
  /-- Supplied product, carry and byte-decomposition witnesses. -/
  cols : Circuits.Types.MulOperation F
  /-- Enables arithmetic and byte-range checks. Variant selectors remain separate. -/
  is_real : F
  /-- Selects the low 64-bit product. -/
  is_mul : F
  /-- Selects the high 64 bits of the signed product. -/
  is_mulh : F
  /-- Selects the high 64 bits of the unsigned product. -/
  is_mulhu : F
  /-- Selects the high 64 bits with a signed first operand and unsigned second operand. -/
  is_mulhsu : F
  /-- Selects the sign-extended low 32-bit product. -/
  is_mulw : F
  /-- Caller result, retained in lookup messages even when their multiplicity is zero. -/
  a : fields 4 F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- Witnessed product byte `k`, `0` outside `0..15`. -/
def productVal (cols : Circuits.Types.MulOperation (ZMod p)) (k : ℕ) : ZMod p :=
  if h : k < 16 then cols.product[k]'h else 0

/-- The 64-bit result word, read off the witnessed `product` per active variant: the low 64 bits
(bytes `0..7`) for `MUL`; the high 64 bits (bytes `8..15`) for the `MULH*` family; the
sign-extended low 32 bits for `MULW`. -/
def resultWord (input : Inputs (ZMod p)) (cols : Circuits.Types.MulOperation (ZMod p)) : Word (ZMod p) :=
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
bundled gadget derives this interpretation from its product certificate on active rows. -/
def SemanticSpec (input : Inputs (ZMod p)) (cols : Circuits.Types.MulOperation (ZMod p)) : Prop :=
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

/-- The five variant selectors are boolean and **at most one** is set (the `{0,1}` sum-bound — the
chip discharges this unconditionally from the in-circuit sum gate, including on padding rows where
the sum is `0`). Operand bounds are conclusions of the two safe byte decompositions, not
composer-supplied preconditions. On an active row exactly one flag is set; `mulSemantics_of_raw`
recovers `sum = 1` per active variant via `sum_eq_one`. -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (input.is_mulw = 1 → input.is_real = 1) ∧
  (input.is_mul = 0 ∨ input.is_mul = 1) ∧ (input.is_mulh = 0 ∨ input.is_mulh = 1) ∧
  (input.is_mulhu = 0 ∨ input.is_mulhu = 1) ∧ (input.is_mulhsu = 0 ∨ input.is_mulhsu = 1) ∧
  (input.is_mulw = 0 ∨ input.is_mulw = 1) ∧
  (input.is_mul + input.is_mulh + input.is_mulhu + input.is_mulhsu + input.is_mulw = 0 ∨
    input.is_mul + input.is_mulh + input.is_mulhu + input.is_mulhsu + input.is_mulw = 1)

end SP1Clean.MulOperation
