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
import SP1Operations.Operation.MulOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.RTypeReader
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.RTypeReader

/-! # Chip-level `MulChip` mirror — heavy-arithmetic scaling test

The Mul chip is the heaviest non-DivRem chip in SP1's instruction set:
82 columns, a 16-limb carry chain + 16-limb product table, two
`U16toU8OperationSafe` sub-fragments for byte decomposition, a
`U16MSBOperation` for `mulw` sign handling, and five opcode selectors
(`is_mul`, `is_mulh`, `is_mulw`, `is_mulhu`, `is_mulhsu`) that fan out
to five distinct RISC-V multiplication variants.

This file is the **heavy-chip scaling probe** for the Clean DSL pilot.
Three structural unknowns it forces:

1. Can Clean's `ProvableStruct`-derived destructuring survive an 82-col
   struct without typeclass-synthesis explosion?
2. Can `ProgramTable.assertion` accept a selector-weighted opcode
   expression like `is_mul * 11 + is_mulh * 12 + is_mulw * 13
   + is_mulhsu * 14 + is_mulhu * 24` and still compile in reasonable
   time?
3. Does Clean's lookup machinery scale to the 7+ byte lookups Mul emits
   (clk bounds, carry bounds × 16, product bounds × 16, plus the
   sub-fragment lookups)?

The pilot deliberately does **not** mirror SP1's `MulOperation` as a
separate Clean operation file. The iff RHS in
`MulOperation.allHold_constraints_iff_is_real_poly` is 60+ conjuncts
spanning the full 16-limb product carry chain plus sub-fragments —
inlining it into a Clean `Spec` would be enormous and tells us nothing
new about Risk 1 beyond what the chip-level scaling test already
exposes. Instead, `mulSpec` here is a placeholder predicate; a future
iteration can either expand it inline or factor a dedicated
`SP1Clean/MulOperation.lean`.

Opcode encoding mirrors SP1 source: `is_mul * 11 + is_mulh * 12 +
is_mulw * 13 + is_mulhsu * 14 + is_mulhu * 24` (matching the SP1 RISC-V
opcode IDs).
-/

namespace SP1Clean.Mul

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct, mirroring SP1's Rust `MulCols<T>` over
82 field elements. Field order matches the `Main[k]` indexing in
`SP1Chips/Mul/Constraints.lean`. The struct groups the 16-limb carry
and product vectors into `Vector T 16` fields; the `U16toU8OperationSafe`
sub-fragments are inlined as `Vector T 4` (the SP1 struct's
`low_bytes` field). -/
structure MulCols (T : Type) where
  clk_high : T                              -- Main[0]
  clk_16_24 : T                             -- Main[1]
  clk_0_16 : T                              -- Main[2]
  pc : Vector T 3                           -- Main[3..5]
  op_a : T                                  -- Main[6]
  op_a_memory_prev_value : Vector T 4       -- Main[7..10]
  op_a_memory_prev_low : T                  -- Main[11]
  op_a_memory_diff_low : T                  -- Main[12]
  op_a_0 : T                                -- Main[13]
  op_b : T                                  -- Main[14]
  op_b_memory_prev_value : Vector T 4       -- Main[15..18]
  op_b_memory_prev_low : T                  -- Main[19]
  op_b_memory_diff_low : T                  -- Main[20]
  op_c : T                                  -- Main[21]
  op_c_memory_prev_value : Vector T 4       -- Main[22..25]
  op_c_memory_prev_low : T                  -- Main[26]
  op_c_memory_diff_low : T                  -- Main[27]
  op_a_write_value : Vector T 4             -- Main[28..31]
  carry : Vector T 16                       -- Main[32..47]
  product : Vector T 16                     -- Main[48..63]
  b_low_bytes : Vector T 4                  -- Main[64..67]
  c_low_bytes : Vector T 4                  -- Main[68..71]
  b_msb : T                                 -- Main[72]
  c_msb : T                                 -- Main[73]
  product_msb : T                           -- Main[74]
  b_sign_extend : T                         -- Main[75]
  c_sign_extend : T                         -- Main[76]
  is_mul : T                                -- Main[77]
  is_mulh : T                               -- Main[78]
  is_mulw : T                               -- Main[79]
  is_mulhsu : T                             -- Main[80]
  is_mulhu : T                              -- Main[81]
deriving ProvableStruct

/-- The aggregate is-real flag for Mul: any of the five opcode
selectors active. -/
def isRealExpr (cols : Var MulCols (ZMod p)) : Expression (ZMod p) :=
  cols.is_mul + cols.is_mulh + cols.is_mulw + cols.is_mulhsu + cols.is_mulhu

/-- The opcode field expression used in the program-bus interaction:
selector-weighted to dispatch to the five RV64IM multiplication
variants. Matches SP1's `E24 = is_mul * 11 + is_mulh * 12 + is_mulw * 13
+ is_mulhsu * 14 + is_mulhu * 24`. -/
def opcodeExpr (cols : Var MulCols (ZMod p)) : Expression (ZMod p) :=
  cols.is_mul * 11 + cols.is_mulh * 12 + cols.is_mulw * 13
    + cols.is_mulhsu * 14 + cols.is_mulhu * 24

/-- Clean-side circuit. Mirrors the SP1 source's emissions for Mul:
- CPUState lookups (clk_0_16 progression, clk_16_24 byte bound)
- 16 carry-bound lookups (each in Range(16))
- 16 product-bound lookups (each in U8Range)
- Program-bus interaction with the selector-weighted opcode
- 5 opcode-selector boolean gates + is_real-sum boolean gate
- 1 op_a_0 zero gate

The MulOperation sub-fragment (carry chain, U16toU8Safe, U16MSB) is
deliberately not emitted as a subcircuit here — the goal of this chip
is the structural-scale test, not the per-fragment correctness, which
would require a full MulOp Clean mirror (see file docstring). -/
def main (cols : Var MulCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨_clk_high, clk_16_24, clk_0_16, pc, op_a,
       _op_a_memory_prev_value, _op_a_memory_prev_low, _op_a_memory_diff_low,
       op_a_0, op_b, _op_b_memory_prev_value, _op_b_memory_prev_low,
       _op_b_memory_diff_low, op_c, _op_c_memory_prev_value,
       _op_c_memory_prev_low, _op_c_memory_diff_low, _op_a_write_value,
       carry, product, _b_low_bytes, _c_low_bytes,
       _b_msb, _c_msb, _product_msb, _b_sign_extend, _c_sign_extend,
       is_mul, is_mulh, is_mulw, is_mulhsu, is_mulhu⟩ := cols
  let is_real_e := is_mul + is_mulh + is_mulw + is_mulhsu + is_mulhu
  let opcode_e := is_mul * 11 + is_mulh * 12 + is_mulw * 13
                    + is_mulhsu * 14 + is_mulhu * 24
  -- CPUState: clk_0_16 progression and clk_16_24 byte bound.
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), (clk_0_16 - 1) * (8 : ZMod p)⁻¹, 13, 0]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(3 : Expression (ZMod p)), 0, clk_16_24, 0]
      : Vector (Expression (ZMod p)) 4)
  -- 16 carry-bound lookups (Range(16) each).
  lookup ByteOpcodeTable (#v[6, carry[0], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[6, carry[1], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[6, carry[2], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[6, carry[3], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[6, carry[4], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[6, carry[5], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[6, carry[6], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[6, carry[7], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[6, carry[8], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[6, carry[9], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[6, carry[10], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[6, carry[11], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[6, carry[12], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[6, carry[13], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[6, carry[14], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[6, carry[15], 16, 0] : Vector (Expression (ZMod p)) 4)
  -- 16 product-bound lookups (U8Range each).
  lookup ByteOpcodeTable (#v[3, 0, product[0], 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[3, 0, product[1], 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[3, 0, product[2], 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[3, 0, product[3], 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[3, 0, product[4], 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[3, 0, product[5], 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[3, 0, product[6], 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[3, 0, product[7], 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[3, 0, product[8], 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[3, 0, product[9], 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[3, 0, product[10], 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[3, 0, product[11], 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[3, 0, product[12], 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[3, 0, product[13], 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[3, 0, product[14], 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[3, 0, product[15], 0] : Vector (Expression (ZMod p)) 4)
  -- Program-bus interaction with selector-weighted opcode. R-type
  -- discipline: op_b and op_c are single-limb register indices with
  -- limbs 1..3 zero; imm_b = imm_c = 0.
  SP1Clean.ProgramTable.assertion
    (⟨pc, opcode_e, op_a, #v[op_b, 0, 0, 0], #v[op_c, 0, 0, 0],
      op_a_0, 0, 0⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  -- Boolean gates: each opcode selector ∈ {0, 1}, the aggregate
  -- is_real ∈ {0, 1}, and op_a_0 = 0.
  is_mul * (is_mul - 1) === 0
  is_mulh * (is_mulh - 1) === 0
  is_mulw * (is_mulw - 1) === 0
  is_mulhsu * (is_mulhsu - 1) === 0
  is_mulhu * (is_mulhu - 1) === 0
  is_real_e * (is_real_e - 1) === 0
  op_a_0 === 0

/-- Placeholder for the MulOperation-derivable Spec content. Currently
trivially `True`; a follow-up iteration can either inline the 60+
conjuncts of `MulOperation.allHold_constraints_iff_is_real_poly`'s RHS
or factor a dedicated `SP1Clean.MulOp.Spec` predicate.

The chip-level Spec below references this placeholder so the
trace-level OfflineMemory bridge can consume `MulCols` rows without
depending on the full MulOperation proof. -/
def mulSpec (_cols : MulCols (ZMod p)) : Prop := True

/-- The Clean-flavored Spec for `MulChip`. Composes the existing
per-fragment specs (`cpuStateSpec`) with three `memoryAccessSpec`
records (op_a write, op_b read, op_c read), the `ProgramTable.Spec`
consequence, the selector boolean gates, and the placeholder
`mulSpec`. -/
def Spec (cols : MulCols (ZMod p)) : Prop :=
  SP1Clean.CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 ∧
  SP1Clean.memoryAccessSpec
    (cols.clk_0_16 + cols.clk_16_24 * 65536) 4
    (SP1Clean.MemoryAccess.ofRegisterShared cols.op_a
      { prev_value := cols.op_a_memory_prev_value,
        access_timestamp :=
          { prev_low := cols.op_a_memory_prev_low,
            diff_low_limb := cols.op_a_memory_diff_low } }) ∧
  SP1Clean.memoryAccessSpec
    (cols.clk_0_16 + cols.clk_16_24 * 65536) 3
    (SP1Clean.MemoryAccess.ofRegisterShared cols.op_b
      { prev_value := cols.op_b_memory_prev_value,
        access_timestamp :=
          { prev_low := cols.op_b_memory_prev_low,
            diff_low_limb := cols.op_b_memory_diff_low } }) ∧
  SP1Clean.memoryAccessSpec
    (cols.clk_0_16 + cols.clk_16_24 * 65536) 2
    (SP1Clean.MemoryAccess.ofRegisterShared cols.op_c
      { prev_value := cols.op_c_memory_prev_value,
        access_timestamp :=
          { prev_low := cols.op_c_memory_prev_low,
            diff_low_limb := cols.op_c_memory_diff_low } }) ∧
  -- Program-bus consequence with the selector-weighted opcode.
  SP1Clean.ProgramTable.Spec
    { pc := cols.pc,
      opcode := cols.is_mul * 11 + cols.is_mulh * 12 + cols.is_mulw * 13
                  + cols.is_mulhsu * 14 + cols.is_mulhu * 24,
      op_a := cols.op_a,
      op_b := #v[cols.op_b, 0, 0, 0],
      op_c := #v[cols.op_c, 0, 0, 0],
      op_a_0 := cols.op_a_0, imm_b := 0, imm_c := 0 } ∧
  -- Five opcode-selector boolean gates plus the aggregate-is-real gate.
  cols.is_mul * (cols.is_mul - 1) = 0 ∧
  cols.is_mulh * (cols.is_mulh - 1) = 0 ∧
  cols.is_mulw * (cols.is_mulw - 1) = 0 ∧
  cols.is_mulhsu * (cols.is_mulhsu - 1) = 0 ∧
  cols.is_mulhu * (cols.is_mulhu - 1) = 0 ∧
  ((cols.is_mul + cols.is_mulh + cols.is_mulw
    + cols.is_mulhsu + cols.is_mulhu)
   * (cols.is_mul + cols.is_mulh + cols.is_mulw
      + cols.is_mulhsu + cols.is_mulhu - 1)) = 0 ∧
  cols.op_a_0 = 0 ∧
  mulSpec cols

end SP1Clean.Mul
