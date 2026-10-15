module

public import Clean.Gadgets.Bits
public import ToClean.Gadgets.LookupProjection

/-! # Bitwise byte operations without static lookup tables

Missing upstream capability: a bundled AND/OR/XOR byte gadget that lowers through Clean's
built-in AIR export. The existing byte gadgets use a legacy lookup table. This version composes
two `ToBits` circuits and constrains the result with bit polynomials, using the standard witness
IR. Move it upstream and remove this addition when Clean supplies the same interface.
-/

@[expose] public section

namespace Gadgets.BitwiseByte

open Circuit Utils.Bits

/-- The bitwise operation is fixed when constructing the circuit. -/
inductive Op where
  | and
  | or
  | xor

/-- Natural-number meaning of a bitwise operation. -/
def Op.apply : Op → ℕ → ℕ → ℕ
  | .and => (· &&& ·)
  | .or => (· ||| ·)
  | .xor => (· ^^^ ·)

/-- Polynomial implementing an operation on two boolean field elements. -/
def Op.bit {R : Type} [Add R] [Sub R] [Mul R] [OfNat R 2] : Op → R → R → R
  | .and, x, y => x * y
  | .or, x, y => x + y - x * y
  | .xor, x, y => x + y - 2 * x * y

variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

omit [Fact p.Prime] [Fact (p > 2)] in
/-- Bitwise operations preserve an unsigned width bound. -/
theorem Op.apply_lt {n x y : ℕ} (op : Op) (hx : x < 2 ^ n) (hy : y < 2 ^ n) :
    op.apply x y < 2 ^ n := by
  cases op with
  | and => exact Nat.and_lt_two_pow x hy
  | or => exact Nat.or_lt_two_pow hx hy
  | xor => exact Nat.xor_lt_two_pow hx hy

omit [Fact (p > 2)] in
/-- Evaluating the bit polynomial commutes with evaluating its operands. -/
@[circuit_norm] theorem Op.bit_eval (op : Op) (env : Environment (F p))
    (x y : Expression (F p)) :
    Expression.eval env (op.bit x y) = op.bit (Expression.eval env x) (Expression.eval env y) := by
  cases op <;> simp [Op.bit, circuit_norm]

omit [Fact (p > 2)] in
/-- Packing the bit polynomials gives the natural-number bitwise operation. -/
theorem fieldFromBits_bitwise (op : Op) (hp : 2 ^ 8 < p) (x y : F p)
    (hx : x.val < 2 ^ 8) (hy : y.val < 2 ^ 8) :
    fieldFromBits ((fieldToBits 8 x).zipWith op.bit (fieldToBits 8 y)) =
      (op.apply x.val y.val : F p) := by
  have hlt := lt_trans (op.apply_lt hx hy) hp
  have hbits : (fieldToBits 8 x).zipWith op.bit (fieldToBits 8 y) =
      fieldToBits 8 (op.apply x.val y.val : F p) := by
    ext i hi
    simp only [Vector.getElem_zipWith, fieldToBits, Utils.Bits.toBits, Vector.getElem_map,
      Vector.getElem_mapRange, ZMod.val_natCast_of_lt hlt]
    cases op <;> simp only [Op.bit, Op.apply, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor]
    all_goals cases x.val.testBit i <;> cases y.val.testBit i <;> norm_num
  rw [hbits, fieldFromBits_fieldToBits]
  rw [ZMod.val_natCast_of_lt hlt]
  exact op.apply_lt hx hy

/-- Range-check both inputs and constrain their bitwise result. -/
def main (op : Op) (hp : 2 ^ 8 < p) (input : Var fieldPair (F p)) :
    Circuit (F p) (Expression (F p)) := do
  let x ← ToBits.toBits 8 hp input.1
  let y ← ToBits.toBits 8 hp input.2
  let result ← witnessField (match op with
    | .and => (input.1.val &&& input.2.val).toField
    | .or => (input.1.val ||| input.2.val).toField
    | .xor => (input.1.val ^^^ input.2.val).toField)
  result === fieldFromBitsExpr (x.zipWith (op.bit) y)
  return result

/-- Both byte bounds and the semantic result follow from the constraints. -/
def circuit (op : Op) (hp : 2 ^ 8 < p) :
    GeneralFormalCircuit (F p) fieldPair field where
  main := main op hp
  Spec input output _ :=
    (input.1.val < 2 ^ 8 ∧ input.2.val < 2 ^ 8) ∧
      output.val = op.apply input.1.val input.2.val
  ProverAssumptions input _ _ := input.1.val < 2 ^ 8 ∧ input.2.val < 2 ^ 8
  soundness := by
    circuit_proof_start [ToBits.toBits]
    cases h_input
    obtain ⟨⟨hx, hxbits⟩, ⟨hy, hybits⟩, hr⟩ := h_holds
    refine ⟨⟨hx, hy⟩, ?_⟩
    simp only [hr, fieldFromBits_eval, Vector.map_zipWith, Op.bit_eval,
      ← Vector.zipWith_map, hxbits, hybits]
    rw [fieldFromBits_bitwise op hp _ _ hx hy,
      ZMod.val_natCast_of_lt (lt_trans (op.apply_lt hx hy) hp)]
  completeness := by
    circuit_proof_start [ToBits.toBits]
    cases h_input
    obtain ⟨hx, hy⟩ := h_assumptions
    dsimp only at hx hy
    obtain ⟨hxbits, hybits, hr⟩ := h_env
    refine ⟨hx, hy, ?_⟩
    simp only [hr, fieldFromBits_eval, Vector.map_zipWith, Op.bit_eval, ← Vector.zipWith_map,
      (hxbits hx).2, (hybits hy).2]
    rw [fieldFromBits_bitwise op hp _ _ hx hy]
    cases op <;> simp [Op.apply, circuit_norm]

omit [Fact (p > 2)] in
/-- The bitwise circuit adds no legacy lookups. -/
@[circuit_norm] theorem main_lookups (op : Op) (hp : 2 ^ 8 < p)
    (input : Var fieldPair (F p)) (offset : ℕ) :
    ((main op hp input).operations offset).lookups = [] := by
  simp [main, ToBits.toBits, circuit_norm, Gadgets.Equality.main, Operations.lookups]

end Gadgets.BitwiseByte
