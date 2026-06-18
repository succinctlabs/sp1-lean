import SP1Clean.Native.Operations.MulOperation.RawSpec

/-! # `MulOperation.populate` — the witness (trace generation), mirroring SP1's
`MulOperation::populate`. -/

namespace SP1Clean.MulOperation

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

def extStream (l0 l1 l2 l3 sgn : ℕ) : ℕ → ℕ := fun i =>
  [l0 % 256, l0 / 256, l1 % 256, l1 / 256, l2 % 256, l2 / 256, l3 % 256, l3 / 256,
   sgn * 255, sgn * 255, sgn * 255, sgn * 255, sgn * 255, sgn * 255, sgn * 255, sgn * 255].getD i 0

/-- Witnessed schoolbook product byte `k` of the sign/zero-extended operands. -/
def schoolProduct (b0 b1 b2 b3 c0 c1 c2 c3 bsgn csgn k : ℕ) : ℕ :=
  MulCarryChain.product (MulCarryChain.cpNat (extStream b0 b1 b2 b3 bsgn) (extStream c0 c1 c2 c3 csgn)) k

/-- Witnessed schoolbook column carry `k`. -/
def schoolCarry (b0 b1 b2 b3 c0 c1 c2 c3 bsgn csgn k : ℕ) : ℕ :=
  MulCarryChain.carry (MulCarryChain.cpNat (extStream b0 b1 b2 b3 bsgn) (extStream c0 c1 c2 c3 csgn)) k

/-- The witness assignment (trace generation), mirroring SP1's `MulOperation::populate`
(`operations/mul.rs:66-162`): the 16 schoolbook product bytes + 16 column carries (with the
sign/zero-extended byte streams), the `U16toU8` low-byte decompositions of `b`/`c`, the three MSB
witnesses, and the two sign-extend selectors. The columns depend on the operands and the signed-variant
flags (`is_mulh`/`is_mulhsu`) only — `is_mul`/`is_mulhu`/`is_mulw` affect result *placement*, not the
product columns. The composing chip calls this to fill `cols`; conformance anchors it to SP1's `populate`. -/
def populate (b c : Word (ZMod p)) (is_mulh is_mulhsu is_mulw : ZMod p) :
    Extracted.MulOperation (ZMod p) :=
  let bsgn := (is_mulh.val + is_mulhsu.val) * (b[3].val / 32768 % 2)
  let csgn := is_mulh.val * (c[3].val / 32768 % 2)
  let carry : Vector (ZMod p) 16 := Vector.ofFn (fun k : Fin 16 =>
    ((schoolCarry b[0].val b[1].val b[2].val b[3].val c[0].val c[1].val c[2].val c[3].val
      bsgn csgn k.val : ℕ) : ZMod p))
  let product : Vector (ZMod p) 16 := Vector.ofFn (fun k : Fin 16 =>
    ((schoolProduct b[0].val b[1].val b[2].val b[3].val c[0].val c[1].val c[2].val c[3].val
      bsgn csgn k.val : ℕ) : ZMod p))
  let b_msb := U16MSBOperation.populate_msb b[3]
  let c_msb := U16MSBOperation.populate_msb c[3]
  -- `product_msb` is gated on `is_mulw` (SP1 `mul.rs:80-84`: only the MULW variant fills it, the
  -- low-half high u16 `product[2] + product[3]*256` = `limbs[1]` of the signed low-32 product; else 0).
  { carry := carry, product := product,
    b_lower_byte := U16toU8OperationSafe.populate b, c_lower_byte := U16toU8OperationSafe.populate c,
    b_msb := b_msb, c_msb := c_msb,
    product_msb := ⟨if is_mulw = 1 then U16MSBOperation.populate_msb (product[2] + product[3] * 256)
      else 0⟩,
    b_sign_extend := (is_mulh + is_mulhsu) * b_msb, c_sign_extend := is_mulh * c_msb }

/-- The all-zero column struct — the witness on rows where the gadget is inactive and SP1 leaves
the struct unpopulated (`DivRemChip`'s `c_times_quotient_upper` on word rows; padding rows).
`spec_zero` (in `Formal`) discharges the composed assertion's obligation at this value. -/
def zeroCols : Extracted.MulOperation (ZMod p) :=
  { carry := .replicate 16 0, product := .replicate 16 0,
    b_lower_byte := ⟨.replicate 4 0⟩, c_lower_byte := ⟨.replicate 4 0⟩,
    b_msb := 0, c_msb := 0, product_msb := ⟨0⟩,
    b_sign_extend := 0, c_sign_extend := 0 }

end SP1Clean.MulOperation
