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

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- Semantic Spec. Mirrors the conclusions of the 5 SP1-side lemmas
`MulOperation.spec.{mul,mulh,mulhu,mulhsu,mulw}` (`SP1Operations/
Operation/MulOperation/Constraints.lean:1761,1910,2021,2124,2231`):
under U64 bounds on `b_word`/`c_word`, the result word equals the
BitVec-pure `execute_MUL_pure` / `execute_MULW_pure` of the operands
whenever the matching selector is 1, and the result is itself U64. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  Word.isU64 input.b_word → Word.isU64 input.c_word →
    let bw : BitVec 64 := Word.toBitVec64 input.b_word
    let cw : BitVec 64 := Word.toBitVec64 input.c_word
    let aw : BitVec 64 := Word.toBitVec64 input.a_word
    (input.is_mul    = 1 → Word.isU64 input.a_word ∧ aw = execute_MUL_pure  bw cw .MUL)    ∧
    (input.is_mulh   = 1 → Word.isU64 input.a_word ∧ aw = execute_MUL_pure  bw cw .MULH)   ∧
    (input.is_mulhu  = 1 → Word.isU64 input.a_word ∧ aw = execute_MUL_pure  bw cw .MULHU)  ∧
    (input.is_mulhsu = 1 → Word.isU64 input.a_word ∧ aw = execute_MUL_pure  bw cw .MULHSU) ∧
    (input.is_mulw   = 1 → Word.isU64 input.a_word ∧ aw = execute_MULW_pure bw cw)

/-- Bridge: SP1's `MulOperation.constraints.allHold` (with the
operation's `is_real` slot pinned to 1) implies the semantic `Spec`.
A 5-way refine over the 5 `MulOperation.spec.<variant>` lemmas. The
reverse direction is false: the semantic Spec does not pin down the
`carry`/`product`/byte witnesses. -/
theorem of_sp1 (input : Inputs (ZMod p))
    (h_allHold :
      (MulOperation.constraints
        input.a_word input.b_word input.c_word (toCols input)
        1 input.is_mul input.is_mulh input.is_mulw input.is_mulhu
        input.is_mulhsu).allHold) :
    Spec input := by
  intro isU64_bw isU64_cw
  simp only [SP1ConstraintList.allHold] at h_allHold
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact MulOperation.spec.mul    isU64_bw isU64_cw h_allHold
  · exact MulOperation.spec.mulh   isU64_bw isU64_cw h_allHold
  · exact MulOperation.spec.mulhu  isU64_bw isU64_cw h_allHold
  · exact MulOperation.spec.mulhsu isU64_bw isU64_cw h_allHold
  · exact MulOperation.spec.mulw   isU64_bw isU64_cw h_allHold

/-- Bridge from Clean's `main` post-conditions to SP1's `allHold` form.
The intended signature takes one named hypothesis per constraint emitted
in `main` — 3 sub-circuit Specs (U16toU8OpSafe ×2, U16MSBOp), 2 MSB byte
lookup facts (opcode 5), 42 inline `_ = 0` facts, 16 carry range lookup
facts (opcode 6), and 8 product-pair U8Range lookup facts (opcode 3) —
and discharges the 60+ conjuncts of `MulOperation.allHold_constraints_iff_is_real`
positionally. The current stub takes a placeholder `True` and is `sorry`;
see TODO below for the closure plan.

Closure outline:
  1. `rw [MulOperation.allHold_constraints_iff_is_real]` to expose the
     iff's RHS conjunction.
  2. For the two `List.Forall toProp U16_{b,c}` conjuncts: unfold and
     discharge each of the 4 sends (opcode 3 = U8Range) using the
     Clean `U16toU8OpSafe.Spec` low/high val-bounds; the
     `(0 : ZMod p) < 256` part is `ZMod.val_zero` + `Fact (2^17 < p)`.
     (Alternatively, first close `SP1Clean.U16toU8OpSafe.iff_sp1`
     upstream and reuse it here.)
  3. For the `List.Forall toProp (U16MSBOperation.constraints …)`
     conjunct: use `U16MSBOperation.allHold_constraints_iff` to bridge
     from the `U16MSBOp.Assertion.Spec` Clean fact.
  4. For the 2 three-part MSB byte-opcode RHS chunks: unfold the
     ByteOpcodeSpec returned by the opcode-5 lookups using
     `constrain_MSB`.
  5. For the 16 carry-chain + 12 result-matching + 12 boolean +
     2 coupling assertZeros: each is a direct `linear_combination` /
     `mul_eq_zero` step from the corresponding `_ = 0` fact.
  6. For the 16 `carry[i] < 65536` conjuncts: use
     `SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16` on each Range
     lookup fact.
  7. For the 16 `product[i] < 256` conjuncts: unfold the U8Range
     ByteOpcodeSpec via `constrain_U8Range` and project. -/
private theorem allHold_of_main_holds
    (input : Inputs (ZMod p)) (h_holds : True) :
    (MulOperation.constraints
      input.a_word input.b_word input.c_word (toCols input)
      1 input.is_mul input.is_mulh input.is_mulw input.is_mulhu
      input.is_mulhsu).allHold := by
  sorry

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  -- Sketch: `circuit_proof_start` introduces `input` and `h_holds`; then
  -- `exact of_sp1 input (allHold_of_main_holds input h_holds)` would
  -- finish, once the helper body below is closed (the bridge from
  -- Clean's main facts to SP1 `allHold`). Leaving as `sorry` until
  -- the helper has a real proof.
  sorry

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
