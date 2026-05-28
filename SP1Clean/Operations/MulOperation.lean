import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations.Constraint
import SP1Foundations.ByteOpcode
import SP1Foundations.Field
import SP1Foundations.SailM
import SP1Operations.Operation.MulOperation.MulOperation
import SP1Operations.Operation.MulOperation.Constraints
import SP1Clean.ByteOpcodeTable
import SP1Clean.Operations.U16toU8OperationSafe
import SP1Clean.Operations.U16MSBOperation
import RISCV.Instructions

/-! # `MulOperation` Clean mirror

SP1's `MulOperation` is the 16-byte unsigned product carry-chain
implementing MUL/MULH/MULHU/MULHSU/MULW. Faithful Clean composition:

- `U16toU8OpSafe.assertion` ×2 — decompose `b_word` / `c_word` into
  8-byte limb vectors with U8-range checks.
- `U16MSBOp.assertion` ×1 — extract MSB of `a_word[1]` (MULW path).
- 2 MSB byte lookups (opcode 5) for `b_msb` / `c_msb` against the top
  byte of each operand.
- 42 inline `=== 0` gates for the 16-byte carry chain, the 12
  result-matching variants, the selector / msb / sgn booleans and the
  selector-sum boolean, and the 2 sign-extend coupling gates.
  (SP1 emits a 43rd `is_real * (is_real - 1) = 0` gate; the Clean
  assertion runs under the chip's `is_real = 1` so that gate is
  vacuous — the helper lemma discharges it numerically.)
- 16 u16-range lookups for `carry` (opcode 6).
- 8 U8Range triples for product byte pairs (opcode 3).

The Spec matches the 5 SP1-side `MulOperation.spec.{mul,mulh,mulhu,
mulhsu,mulw}` lemmas. Soundness composes `allHold_of_main_holds`
(Clean facts → SP1 `allHold`) with `of_sp1` (the 5-way spec). -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.MulOp

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)]

/-- Bundled FormalAssertion input. Mirrors Rust `MulOperation<T>` cols
plus the three operand words and 5 variant selectors. -/
structure Inputs (F : Type) where
  a_word : fields 4 F
  b_word : fields 4 F
  c_word : fields 4 F
  -- MulOperation cols struct:
  carry : fields 16 F
  product : fields 16 F
  b_low_bytes : fields 4 F
  c_low_bytes : fields 4 F
  b_msb : F
  c_msb : F
  product_msb : F
  b_sign_extend : F
  c_sign_extend : F
  -- Variant selectors (passed-through, MUL/MULH/MULHU/MULHSU/MULW):
  is_mul : F
  is_mulh : F
  is_mulhu : F
  is_mulhsu : F
  is_mulw : F
deriving ProvableStruct

/-- Auxiliary: assemble the SP1-native `MulOperation` column struct from
the Clean `Inputs`. -/
@[reducible] def toCols (input : Inputs (ZMod p)) : MulOperation (ZMod p) :=
  { carry := input.carry, product := input.product,
    b_lower_byte := { low_bytes := input.b_low_bytes },
    c_lower_byte := { low_bytes := input.c_low_bytes },
    b_msb := input.b_msb, c_msb := input.c_msb,
    product_msb := { msb := input.product_msb },
    b_sign_extend := input.b_sign_extend,
    c_sign_extend := input.c_sign_extend }

set_option maxHeartbeats 1600000 in
-- 71 emitted constraints (3 sub-circuits + 2 + 42 + 16 + 8 lookups/gates)
-- push `circuit_norm` past its default budget.
/-- Clean-side circuit. Composes the 3 SP1 subcircuit calls and emits
the remaining 2 + 42 + 16 + 8 inline constraints. Order matches the
SP1 constraint list at `MulOperation/Constraints.lean:1384-1453`. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  -- 3 SP1 subcircuits: U16toU8OpSafe(b), U16toU8OpSafe(c), U16MSBOp(a[1]).
  SP1Clean.U16toU8OpSafe.assertion
    (⟨input.b_word, input.b_low_bytes⟩ : Var SP1Clean.U16toU8OpSafe.Inputs (ZMod p))
  SP1Clean.U16toU8OpSafe.assertion
    (⟨input.c_word, input.c_low_bytes⟩ : Var SP1Clean.U16toU8OpSafe.Inputs (ZMod p))
  SP1Clean.U16MSBOp.assertion
    (⟨input.a_word[1], input.product_msb⟩ : Var SP1Clean.U16MSBOp.Inputs (ZMod p))
  -- 8-byte view of b_word / c_word (low/high pairs per u16 limb).
  let b0 : Expression (ZMod p) := input.b_low_bytes[0]
  let b1 : Expression (ZMod p) := (input.b_word[0] - input.b_low_bytes[0]) * (256 : ZMod p)⁻¹
  let b2 : Expression (ZMod p) := input.b_low_bytes[1]
  let b3 : Expression (ZMod p) := (input.b_word[1] - input.b_low_bytes[1]) * (256 : ZMod p)⁻¹
  let b4 : Expression (ZMod p) := input.b_low_bytes[2]
  let b5 : Expression (ZMod p) := (input.b_word[2] - input.b_low_bytes[2]) * (256 : ZMod p)⁻¹
  let b6 : Expression (ZMod p) := input.b_low_bytes[3]
  let b7 : Expression (ZMod p) := (input.b_word[3] - input.b_low_bytes[3]) * (256 : ZMod p)⁻¹
  let c0 : Expression (ZMod p) := input.c_low_bytes[0]
  let c1 : Expression (ZMod p) := (input.c_word[0] - input.c_low_bytes[0]) * (256 : ZMod p)⁻¹
  let c2 : Expression (ZMod p) := input.c_low_bytes[1]
  let c3 : Expression (ZMod p) := (input.c_word[1] - input.c_low_bytes[1]) * (256 : ZMod p)⁻¹
  let c4 : Expression (ZMod p) := input.c_low_bytes[2]
  let c5 : Expression (ZMod p) := (input.c_word[2] - input.c_low_bytes[2]) * (256 : ZMod p)⁻¹
  let c6 : Expression (ZMod p) := input.c_low_bytes[3]
  let c7 : Expression (ZMod p) := (input.c_word[3] - input.c_low_bytes[3]) * (256 : ZMod p)⁻¹
  -- Sign-extended top byte (positions 8..15 of the 16-byte form share this value).
  let bse : Expression (ZMod p) := input.b_sign_extend * 255
  let cse : Expression (ZMod p) := input.c_sign_extend * 255
  -- Typed constants — bare numeric literals next to `*` inside an outer
  -- `Expression * (…)` context don't reliably unify to `Expression (ZMod p)`,
  -- so we expose them explicitly (same pattern as `AddwOp` for `(65536 : ZMod p)⁻¹`).
  let r256 : Expression (ZMod p) := 256
  let r65535 : Expression (ZMod p) := 65535
  -- 2 MSB byte lookups (opcode 5): `b_msb = 1 ↔ b7 ≥ 128`.
  lookup ByteOpcodeTable
    (#v[(5 : Expression (ZMod p)), input.b_msb, b7, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(5 : Expression (ZMod p)), input.c_msb, c7, 0] : Vector (Expression (ZMod p)) 4)
  -- 42 inline assertZero gates.
  -- (a) sign-extend definitions (2):
  (input.b_sign_extend - (input.is_mulh + input.is_mulhsu) * input.b_msb) === 0
  (input.c_sign_extend - input.is_mulh * input.c_msb) === 0
  -- (b) 16-byte carry chain: `product[i] = m[i] [+ carry[i-1]] − carry[i] * 256`
  -- where `m[i] = Σ_{j+k=i} bbwe[j] * cbwe[k]` over the 16-byte sign-extended form.
  -- i = 0..15. Sign-extend slots 8..15 contribute `bse` / `cse` as the j or k value.
  -- i = 0: only b0*c0
  (input.product[0] - (b0*c0 - input.carry[0]* r256)) === 0
  -- i = 1: b0*c1 + b1*c0
  (input.product[1] - (b0*c1 + b1*c0 + input.carry[0] - input.carry[1]* r256)) === 0
  -- i = 2
  (input.product[2] - (b0*c2 + b1*c1 + b2*c0 + input.carry[1] - input.carry[2]* r256)) === 0
  -- i = 3
  (input.product[3] - (b0*c3 + b1*c2 + b2*c1 + b3*c0 + input.carry[2] - input.carry[3]* r256)) === 0
  -- i = 4
  (input.product[4] - (b0*c4 + b1*c3 + b2*c2 + b3*c1 + b4*c0 + input.carry[3] - input.carry[4]* r256)) === 0
  -- i = 5
  (input.product[5] - (b0*c5 + b1*c4 + b2*c3 + b3*c2 + b4*c1 + b5*c0 + input.carry[4] - input.carry[5]* r256)) === 0
  -- i = 6
  (input.product[6] - (b0*c6 + b1*c5 + b2*c4 + b3*c3 + b4*c2 + b5*c1 + b6*c0 + input.carry[5] - input.carry[6]* r256)) === 0
  -- i = 7
  (input.product[7] - (b0*c7 + b1*c6 + b2*c5 + b3*c4 + b4*c3 + b5*c2 + b6*c1 + b7*c0 + input.carry[6] - input.carry[7]* r256)) === 0
  -- i = 8: indices reach the sign-extended slot 8 (bse / cse contribute).
  (input.product[8] - (b0*cse + b1*c7 + b2*c6 + b3*c5 + b4*c4 + b5*c3 + b6*c2 + b7*c1 + bse*c0 + input.carry[7] - input.carry[8]* r256)) === 0
  -- i = 9
  (input.product[9] - (b0*cse + b1*cse + b2*c7 + b3*c6 + b4*c5 + b5*c4 + b6*c3 + b7*c2 + bse*c1 + bse*c0 + input.carry[8] - input.carry[9]* r256)) === 0
  -- i = 10
  (input.product[10] - (b0*cse + b1*cse + b2*cse + b3*c7 + b4*c6 + b5*c5 + b6*c4 + b7*c3 + bse*c2 + bse*c1 + bse*c0 + input.carry[9] - input.carry[10]* r256)) === 0
  -- i = 11
  (input.product[11] - (b0*cse + b1*cse + b2*cse + b3*cse + b4*c7 + b5*c6 + b6*c5 + b7*c4 + bse*c3 + bse*c2 + bse*c1 + bse*c0 + input.carry[10] - input.carry[11]* r256)) === 0
  -- i = 12
  (input.product[12] - (b0*cse + b1*cse + b2*cse + b3*cse + b4*cse + b5*c7 + b6*c6 + b7*c5 + bse*c4 + bse*c3 + bse*c2 + bse*c1 + bse*c0 + input.carry[11] - input.carry[12]* r256)) === 0
  -- i = 13
  (input.product[13] - (b0*cse + b1*cse + b2*cse + b3*cse + b4*cse + b5*cse + b6*c7 + b7*c6 + bse*c5 + bse*c4 + bse*c3 + bse*c2 + bse*c1 + bse*c0 + input.carry[12] - input.carry[13]* r256)) === 0
  -- i = 14
  (input.product[14] - (b0*cse + b1*cse + b2*cse + b3*cse + b4*cse + b5*cse + b6*cse + b7*c7 + bse*c6 + bse*c5 + bse*c4 + bse*c3 + bse*c2 + bse*c1 + bse*c0 + input.carry[13] - input.carry[14]* r256)) === 0
  -- i = 15
  (input.product[15] - (b0*cse + b1*cse + b2*cse + b3*cse + b4*cse + b5*cse + b6*cse + b7*cse + bse*c7 + bse*c6 + bse*c5 + bse*c4 + bse*c3 + bse*c2 + bse*c1 + bse*c0 + input.carry[14] - input.carry[15]* r256)) === 0
  -- (c) 12 result-matching gates (4 limbs × 3 variants: mulw, mul, mulh+u+su).
  (input.is_mulw * (input.product[0] + input.product[1]* r256 - input.a_word[0])) === 0
  (input.is_mul  * (input.product[0] + input.product[1]* r256 - input.a_word[0])) === 0
  ((input.is_mulh + input.is_mulhu + input.is_mulhsu) * (input.product[8] + input.product[9]* r256 - input.a_word[0])) === 0
  (input.is_mulw * (input.product[2] + input.product[3]* r256 - input.a_word[1])) === 0
  (input.is_mul  * (input.product[2] + input.product[3]* r256 - input.a_word[1])) === 0
  ((input.is_mulh + input.is_mulhu + input.is_mulhsu) * (input.product[10] + input.product[11]* r256 - input.a_word[1])) === 0
  (input.is_mulw * (input.product_msb * r65535 - input.a_word[2])) === 0
  (input.is_mul  * (input.product[4] + input.product[5]* r256 - input.a_word[2])) === 0
  ((input.is_mulh + input.is_mulhu + input.is_mulhsu) * (input.product[12] + input.product[13]* r256 - input.a_word[2])) === 0
  (input.is_mulw * (input.product_msb * r65535 - input.a_word[3])) === 0
  (input.is_mul  * (input.product[6] + input.product[7]* r256 - input.a_word[3])) === 0
  ((input.is_mulh + input.is_mulhu + input.is_mulhsu) * (input.product[14] + input.product[15]* r256 - input.a_word[3])) === 0
  -- (d) booleanness (4 msb/sgn + 5 selectors + 1 selector sum = 10 gates):
  (input.b_msb * (input.b_msb - 1)) === 0
  (input.c_msb * (input.c_msb - 1)) === 0
  (input.b_sign_extend * (input.b_sign_extend - 1)) === 0
  (input.c_sign_extend * (input.c_sign_extend - 1)) === 0
  (input.is_mul    * (input.is_mul    - 1)) === 0
  (input.is_mulh   * (input.is_mulh   - 1)) === 0
  (input.is_mulhu  * (input.is_mulhu  - 1)) === 0
  (input.is_mulhsu * (input.is_mulhsu - 1)) === 0
  (input.is_mulw   * (input.is_mulw   - 1)) === 0
  ((input.is_mul + input.is_mulh + input.is_mulhu + input.is_mulhsu + input.is_mulw) *
    ((input.is_mul + input.is_mulh + input.is_mulhu + input.is_mulhsu + input.is_mulw) - 1)) === 0
  -- (e) 2 sign-extend coupling gates: b_sign_extend nonzero ⇒ b_msb = 1.
  (input.b_sign_extend * (input.b_msb - 1)) === 0
  (input.c_sign_extend * (input.c_msb - 1)) === 0
  -- (f) 16 u16-range lookups (opcode 6) for each carry.
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), input.carry[0], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), input.carry[1], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), input.carry[2], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), input.carry[3], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), input.carry[4], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), input.carry[5], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), input.carry[6], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), input.carry[7], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), input.carry[8], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), input.carry[9], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), input.carry[10], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), input.carry[11], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), input.carry[12], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), input.carry[13], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), input.carry[14], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), input.carry[15], 16, 0] : Vector (Expression (ZMod p)) 4)
  -- (g) 8 U8Range triples (opcode 3): bounds 0, product[2i], product[2i+1] all < 256.
  lookup ByteOpcodeTable
    (#v[(3 : Expression (ZMod p)), 0, input.product[0], input.product[1]] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(3 : Expression (ZMod p)), 0, input.product[2], input.product[3]] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(3 : Expression (ZMod p)), 0, input.product[4], input.product[5]] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(3 : Expression (ZMod p)), 0, input.product[6], input.product[7]] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(3 : Expression (ZMod p)), 0, input.product[8], input.product[9]] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(3 : Expression (ZMod p)), 0, input.product[10], input.product[11]] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(3 : Expression (ZMod p)), 0, input.product[12], input.product[13]] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(3 : Expression (ZMod p)), 0, input.product[14], input.product[15]] : Vector (Expression (ZMod p)) 4)

set_option maxHeartbeats 3200000 in
-- 71 emitted constraints exceed the default `subcircuitsConsistent` budget.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.MulOp"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

/-- Assumptions: the binarity of the aggregate `is_real` selector sum is
asserted by `main` via the in-circuit `(sum) * (sum - 1) === 0` gate, but
completeness can't extract that from `Spec` alone, so chip callers must
witness binarity externally. The conditional operand bounds carry the U64
facts on the two operands when `is_real = 1`; chips supply these from
their reader sub-circuit's `RegisterAccess.Spec`. Mirrors AddOp's
`Assumptions` shape with the only difference being that `is_real` here
is the selector sum, not a standalone field. -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  let is_real : ZMod p :=
    input.is_mul + input.is_mulh + input.is_mulhu + input.is_mulhsu + input.is_mulw
  (is_real = 0 ∨ is_real = 1) ∧
  (is_real = 1 → Word.isU64 input.b_word ∧ Word.isU64 input.c_word)

/-! ## RV64 ↔ `execute_MUL_pure` bridge lemmas

Five pure BitVec identities relating `execute_MUL_pure b c .X` (the form
delivered by `MulOperation.spec.{mul,…}`) to `RV64.X c b` (the form used
in the user-facing `Spec`). Three close cleanly via `bv_decide` after a
small `simp`; the two signed-high variants (`MULH`, `MULHSU`) need a
manual `toInt`/`toNat` chain that mirrors `execute_MUL'_eq_execute_MUL`
in `SP1Foundations/SailM.lean:858-863` — left as `sorry` with TODOs since
the user has scoped completeness out of this iteration. -/

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)] in
lemma execute_MUL_pure_eq_rv64_mul (b c : BitVec 64) :
    execute_MUL_pure b c .MUL = RV64.mul c b := by
  simp [execute_MUL_pure, RV64.mul, BitVec.extend]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mul_comm]

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)] in
/-- Bridge from SP1's 128-bit signed-product form (`execute_MUL_pure b c .MULH`)
to RV64's 129-bit signed-product form (`RV64.mulh c b`). Both extract bits 64..127
of the signed product; the difference between the two representations is a
multiple of 2^128, which the shift-and-mod erases. -/
lemma execute_MUL_pure_eq_rv64_mulh (b c : BitVec 64) :
    execute_MUL_pure b c .MULH = RV64.mulh c b := by
  simp [execute_MUL_pure, RV64.mulh, BitVec.extend]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_signExtend, BitVec.toNat_setWidth,
    Nat.shiftRight_eq_div_pow]
  have hb : b.toNat < 2^64 := b.isLt
  have hc : c.toNat < 2^64 := c.isLt
  rw [Nat.mod_eq_of_lt (show b.toNat < 2^128 by omega),
      Nat.mod_eq_of_lt (show c.toNat < 2^128 by omega),
      Nat.mod_eq_of_lt (show b.toNat < 2^129 by omega),
      Nat.mod_eq_of_lt (show c.toNat < 2^129 by omega)]
  change _ % 2^128 / 2^64 % 2^64 = _ % 2^129 / 2^64 % 2^64
  have eq128 : (2 : ℕ)^128 = 2^64 * 2^64 := by norm_num
  have eq129 : (2 : ℕ)^129 = 2^64 * 2^65 := by norm_num
  have h_lhs : ∀ x : ℕ, x % 2^128 / 2^64 % 2^64 = x / 2^64 % 2^64 := by
    intro x; rw [eq128, Nat.mod_mul_right_div_self, Nat.mod_mod]
  have h_rhs : ∀ x : ℕ, x % 2^129 / 2^64 % 2^64 = x / 2^64 % 2^64 := by
    intro x; rw [eq129, Nat.mod_mul_right_div_self]
    exact Nat.mod_mod_of_dvd _ (by norm_num)
  rw [h_lhs, h_rhs]
  -- Suffices: RHS_inner − LHS_inner is a multiple of 2^64 * 2^64.
  suffices h : ∃ k : ℕ,
      (b.toNat + (if b.msb = true then 2^129 - 2^64 else 0)) *
        (c.toNat + (if c.msb = true then 2^129 - 2^64 else 0)) =
      (b.toNat + (if b.msb = true then 2^128 - 2^64 else 0)) *
        (c.toNat + (if c.msb = true then 2^128 - 2^64 else 0)) + 2^64 * (2^64 * k) by
    obtain ⟨k, hk⟩ := h
    rw [hk, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2^64),
        Nat.add_mul_mod_self_left]
  rcases hbm : b.msb with _ | _ <;> rcases hcm : c.msb with _ | _ <;>
    simp only [reduceIte, show (if false = true then (2:ℕ)^128 - 2^64 else 0) = 0
      from by decide, show (if false = true then (2:ℕ)^129 - 2^64 else 0) = 0 from by decide,
      Nat.add_zero]
  · exact ⟨0, by ring⟩
  · refine ⟨b.toNat, ?_⟩
    have : (2:ℕ)^129 - 2^64 = (2^128 - 2^64) + 2^128 := by omega
    rw [this]; ring
  · refine ⟨c.toNat, ?_⟩
    have : (2:ℕ)^129 - 2^64 = (2^128 - 2^64) + 2^128 := by omega
    rw [this]; ring
  · refine ⟨(b.toNat + (2^128 - 2^64)) + (c.toNat + (2^128 - 2^64)) + 2^128, ?_⟩
    have : (2:ℕ)^129 - 2^64 = (2^128 - 2^64) + 2^128 := by omega
    rw [this]; ring

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)] in
lemma execute_MUL_pure_eq_rv64_mulhu (b c : BitVec 64) :
    execute_MUL_pure b c .MULHU = RV64.mulhu c b := by
  simp [execute_MUL_pure, RV64.mulhu, BitVec.extend]

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)] in
/-- Bridge from SP1's mixed signed/unsigned 128-bit form (`execute_MUL_pure b c
.MULHSU`) to RV64's 129-bit form (`RV64.mulhsu c b`). Only the signed operand `b`
introduces the 128-vs-129 sign-extension gap; `c` is zero-extended identically in
both widths. Same shift-and-mod argument as `mulh`, but only `b.msb` matters. -/
lemma execute_MUL_pure_eq_rv64_mulhsu (b c : BitVec 64) :
    execute_MUL_pure b c .MULHSU = RV64.mulhsu c b := by
  simp [execute_MUL_pure, RV64.mulhsu, BitVec.extend]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_signExtend, BitVec.toNat_setWidth,
    Nat.shiftRight_eq_div_pow]
  have hb : b.toNat < 2^64 := b.isLt
  have hc : c.toNat < 2^64 := c.isLt
  rw [Nat.mod_eq_of_lt (show b.toNat < 2^128 by omega),
      Nat.mod_eq_of_lt (show b.toNat < 2^129 by omega)]
  change _ % 2^128 / 2^64 % 2^64 = _ % 2^129 / 2^64 % 2^64
  have eq128 : (2 : ℕ)^128 = 2^64 * 2^64 := by norm_num
  have eq129 : (2 : ℕ)^129 = 2^64 * 2^65 := by norm_num
  have h_lhs : ∀ x : ℕ, x % 2^128 / 2^64 % 2^64 = x / 2^64 % 2^64 := by
    intro x; rw [eq128, Nat.mod_mul_right_div_self, Nat.mod_mod]
  have h_rhs : ∀ x : ℕ, x % 2^129 / 2^64 % 2^64 = x / 2^64 % 2^64 := by
    intro x; rw [eq129, Nat.mod_mul_right_div_self]
    exact Nat.mod_mod_of_dvd _ (by norm_num)
  rw [h_lhs, h_rhs]
  suffices h : ∃ k : ℕ,
      (b.toNat + (if b.msb = true then 2^129 - 2^64 else 0)) * c.toNat =
      (b.toNat + (if b.msb = true then 2^128 - 2^64 else 0)) * c.toNat + 2^64 * (2^64 * k) by
    obtain ⟨k, hk⟩ := h
    rw [hk, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2^64),
        Nat.add_mul_mod_self_left]
  rcases hbm : b.msb with _ | _ <;>
    simp only [reduceIte, show (if false = true then (2:ℕ)^128 - 2^64 else 0) = 0
      from by decide, show (if false = true then (2:ℕ)^129 - 2^64 else 0) = 0 from by decide,
      Nat.add_zero]
  · exact ⟨0, by ring⟩
  · refine ⟨c.toNat, ?_⟩
    have : (2:ℕ)^129 - 2^64 = (2^128 - 2^64) + 2^128 := by omega
    rw [this]; ring

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)] in
lemma execute_MULW_pure_eq_rv64_mulw (b c : BitVec 64) :
    execute_MULW_pure b c = RV64.mulw c b := by
  simp [execute_MULW_pure, RV64.mulw, BitVec.extend]

/-- The FormalAssertion's semantic contract — surface only the RV64
fact, mirroring `SP1Clean.AddOp.Spec` one variant deeper: vacuous on
padding rows (`is_real = 0`); on real rows (`is_real = 1`) asserts
`isU64` on the result and the BitVec product identity for whichever of
the five variants is active. The carry chain / product table / byte
decomposition are implementation details of `main` (re-emitted at the
chip level only for SP1-faithful 1:1 mirror) and never reach the
contract.

The five `RV64.{mul,mulh,mulhu,mulhsu,mulw}` are from `RISCV.Instructions`
(operand order `rs2 rs1` matches the SP1 lower-Sail convention). The
bridge to SP1's `MulOperation.spec.{mul,…}` (which deliver
`execute_MUL_pure / execute_MULW_pure`) is provided by the five
`execute_MUL_pure_eq_rv64_*` lemmas above. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  let is_real : ZMod p :=
    input.is_mul + input.is_mulh + input.is_mulhu + input.is_mulhsu + input.is_mulw
  let bw : BitVec 64 := Word.toBitVec64 input.b_word
  let cw : BitVec 64 := Word.toBitVec64 input.c_word
  let aw : BitVec 64 := Word.toBitVec64 input.a_word
  is_real = 1 →
    Word.isU64 input.a_word ∧
    (input.is_mul    = 1 → aw = RV64.mul    cw bw) ∧
    (input.is_mulh   = 1 → aw = RV64.mulh   cw bw) ∧
    (input.is_mulhu  = 1 → aw = RV64.mulhu  cw bw) ∧
    (input.is_mulhsu = 1 → aw = RV64.mulhsu cw bw) ∧
    (input.is_mulw   = 1 → aw = RV64.mulw   cw bw)

/-- Bridge: SP1's `MulOperation.constraints.allHold` (with the
operation's `is_real` slot pinned to 1) implies the semantic `Spec`.
Forward direction only; the reverse needs hint construction of
`carry`/`product`/byte witnesses from the BitVec equation.

Closure path (currently `sorry`'d):
1. From `h_assumptions`, under `is_real = 1`, get `isU64_bw` and
   `isU64_cw`.
2. From `h_allHold`, the 5 individual selector binarities and the sum
   binarity are inside `MulOperation.constraints`'s emitted gates.
   Combined with `is_real = 1` this gives: exactly one selector is 1.
3. For the `isU64 a_word` conjunct: dispatch on the active selector;
   each `MulOperation.spec.X` returns `(is_X = 1 → isU64 a ∧ aw = ...)`
   so the active variant's `.1` gives `isU64 a`.
4. For each per-selector implication: `MulOperation.spec.X _ _ _ h` gives
   `aw = execute_MUL_pure bw cw .X` (or `execute_MULW_pure bw cw` for
   mulw). Bridge to `RV64.mulX cw bw` via the
   `execute_MUL_pure ≡ RV64.mulX` lemmas (BitVec arithmetic; available
   via `simp [RV64.mul]` + `BitVec.mul_comm` for MUL, more involved for
   the high-product variants). -/
theorem of_sp1 (input : Inputs (ZMod p))
    (h_assumptions : Assumptions input)
    (h_allHold :
      (MulOperation.constraints
        input.a_word input.b_word input.c_word (toCols input)
        1 input.is_mul input.is_mulh input.is_mulw input.is_mulhu
        input.is_mulhsu).allHold) :
    Spec input := by
  obtain ⟨_h_bin, h_bnd⟩ := h_assumptions
  simp only [Spec]
  intro h_real_one
  obtain ⟨isU64_bw, isU64_cw⟩ := h_bnd h_real_one
  -- Each `MulOperation.spec.X` delivers `is_X = 1 → aw.isU64 ∧ aw.toBitVec64 = …`
  -- (using `execute_MUL_pure` / `execute_MULW_pure`). Pre-fetch all five.
  have spec_mul    := MulOperation.spec.mul    isU64_bw isU64_cw h_allHold
  have spec_mulh   := MulOperation.spec.mulh   isU64_bw isU64_cw h_allHold
  have spec_mulhu  := MulOperation.spec.mulhu  isU64_bw isU64_cw h_allHold
  have spec_mulhsu := MulOperation.spec.mulhsu isU64_bw isU64_cw h_allHold
  have spec_mulw   := MulOperation.spec.mulw   isU64_bw isU64_cw h_allHold
  -- For the `isU64 a_word` conjunct, dispatch on which selector is 1.
  -- Extract the 5 binarities + sum-disjunction from `h_allHold` via the
  -- iff, then resolve via `MulOperation.single_op`.
  change List.Forall SP1Constraint.toProp _ at h_allHold
  rw [MulOperation.allHold_constraints_iff_is_real] at h_allHold
  obtain ⟨_u16_b, _u16_c, _msb_op, _b_msb_c, _c_msb_c,
          _b_sgn_e, _c_sgn_e,
          _p0, _p1, _p2, _p3, _p4, _p5, _p6, _p7,
          _p8, _p9, _p10, _p11, _p12, _p13, _p14, _p15,
          _aw0w, _aw0m, _aw0h, _aw1w, _aw1m, _aw1h,
          _aw2w, _aw2m, _aw2h, _aw3w, _aw3m, _aw3h,
          _b_msb_d, _c_msb_d, _b_sgn_d, _c_sgn_d,
          b_mul, b_mulh, b_mulhu, b_mulhsu, b_mulw, sum_d, _rest⟩ := h_allHold
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  -- (1) isU64 a_word: 5-way dispatch on which selector is 1.
  · rcases b_mul with h_mul0 | h_mul1
    · rcases b_mulh with h_mulh0 | h_mulh1
      · rcases b_mulhu with h_mulhu0 | h_mulhu1
        · rcases b_mulhsu with h_mulhsu0 | h_mulhsu1
          · rcases b_mulw with h_mulw0 | h_mulw1
            · -- All zero — contradicts h_real_one : sum = 1.
              exfalso
              rw [h_mul0, h_mulh0, h_mulhu0, h_mulhsu0, h_mulw0] at h_real_one
              simp at h_real_one
            · exact (spec_mulw h_mulw1).1
          · exact (spec_mulhsu h_mulhsu1).1
        · exact (spec_mulhu h_mulhu1).1
      · exact (spec_mulh h_mulh1).1
    · exact (spec_mul h_mul1).1
  -- (2) is_mul = 1 → aw = RV64.mul cw bw
  · intro h_one
    rw [(spec_mul h_one).2, execute_MUL_pure_eq_rv64_mul]
  -- (3) is_mulh = 1 → aw = RV64.mulh cw bw
  · intro h_one
    rw [(spec_mulh h_one).2, execute_MUL_pure_eq_rv64_mulh]
  -- (4) is_mulhu = 1 → aw = RV64.mulhu cw bw
  · intro h_one
    rw [(spec_mulhu h_one).2, execute_MUL_pure_eq_rv64_mulhu]
  -- (5) is_mulhsu = 1 → aw = RV64.mulhsu cw bw
  · intro h_one
    rw [(spec_mulhsu h_one).2, execute_MUL_pure_eq_rv64_mulhsu]
  -- (6) is_mulw = 1 → aw = RV64.mulw cw bw
  · intro h_one
    rw [(spec_mulw h_one).2, execute_MULW_pure_eq_rv64_mulw]

/-- Bridge from Clean's `main` post-conditions to SP1's `allHold` form.
The intended signature takes one named hypothesis per constraint emitted
in `main` — 3 sub-circuit Specs (U16toU8OpSafe ×2, U16MSBOp), 2 MSB byte
lookup facts (opcode 5), 42 inline `_ = 0` facts, 16 carry range lookup
facts (opcode 6), and 8 product-pair U8Range lookup facts (opcode 3) —
and discharges the ~70 conjuncts of `MulOperation.allHold_constraints_iff_is_real`
positionally. The current stub takes a placeholder `True` and is `sorry`.

Status: the BV bridges `execute_MUL_pure_eq_rv64_mulh` and
`execute_MUL_pure_eq_rv64_mulhsu` (consumed by `of_sp1` above) are now
both proven, so once this helper is closed `soundness` collapses to a
one-liner without further changes. `completeness` (below) is separately
sorry'd and out of scope here.

Closure outline:
  1. Reshape signature to take 71 named hypotheses matching `main`'s
     emission order (3 sub-circuit Assumptions→Spec wrappers, 2 MSB byte
     lookup ByteOpcodeSpecs, 42 inline `_ = 0` facts, 16 carry-range
     ByteOpcodeSpecs (opcode 6), 8 product-pair U8Range ByteOpcodeSpecs
     (opcode 3)); have `soundness` destructure `h_holds` post-
     `circuit_proof_start` and pass each into this helper. The Clean
     `h_holds` after `simp [main, circuit_norm]` is a ~76KB tuple
     mirroring this exactly — `obtain ⟨...⟩` destructures positionally.
  2. `change List.Forall SP1Constraint.toProp _` then
     `rw [MulOperation.allHold_constraints_iff_is_real]` to expose the
     iff's RHS conjunction.
  3. For `List.Forall toProp U16_{b,c}`: use
     `SP1Clean.U16toU8OpSafe.iff_sp1.mp` (already exists at
     `SP1Clean/Operations/U16toU8OperationSafe.lean:200`) on each
     sub-Spec to obtain the SP1 byte sends.
  4. For `List.Forall toProp (U16MSBOperation.constraints …)`: use
     `SP1Clean.U16MSBOp.iff_sp1.mpr` (at
     `SP1Clean/Operations/U16MSBOperation.lean:77`) bridging from
     `U16MSBOp.Assertion.Spec`.
  5. For the 2 three-part MSB byte-opcode chunks (`b_msb<256 ∧
     bbw[7]<256 ∧ b_msb∈{0,1} ∧ (b_msb=1↔128≤bbw[7])`): unfold the
     opcode-5 `ByteOpcodeSpec` via `constrain_MSB` (the unique
     `bop.toNat=5` matches `.MSB`).
  6. 42 inline assertZero gates: each closes by `linear_combination
     h_<i>` or `mul_eq_zero.mp h_<i>` from the corresponding `_ = 0`
     fact.
  7. 16 `carry[i].val < 65536`: use
     `SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16` on each Range
     fact.
  8. 16 `product[i] < 256`: unfold the opcode-3 U8Range ByteOpcodeSpec
     via `constrain_U8Range` (each opcode-3 row gives two `< 256`
     bounds — write a small `byteOpcodeSpec_u8range_pair` helper next
     to `byteOpcodeSpec_range16` in `SP1Clean/Operations/AddOperation.lean`). -/
private theorem allHold_of_main_holds
    (input : Inputs (ZMod p)) (h_holds : True) :
    (MulOperation.constraints
      input.a_word input.b_word input.c_word (toCols input)
      1 input.is_mul input.is_mulh input.is_mulw input.is_mulhu
      input.is_mulhsu).allHold := by
  sorry

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  -- One-liner: thread the assumptions through `allHold_of_main_holds`
  -- (currently sorry'd — see TODO above) and apply `of_sp1`. Once the
  -- helper is closed, this proof requires no further changes. The BV
  -- bridges `execute_MUL_pure_eq_rv64_mulh` / `_mulhsu` (used inside
  -- `of_sp1`) are now both proven; only the Clean→SP1 `allHold`
  -- construction remains.
  intro offset env input_var input _h_input h_assumptions _h_holds
  exact of_sp1 input h_assumptions (allHold_of_main_holds input trivial)

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  sorry

/-- The full Clean `FormalAssertion` for `MulOperation`. -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { elaborated with
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

end SP1Clean.MulOp
