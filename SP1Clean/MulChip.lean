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
import SP1Operations.Operation.MulOperation.MulOperation
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.RTypeReader.RTypeReader
import SP1Clean.AddrAddOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.RTypeReader
import SP1Clean.Reader.OperandAccess
import SP1Chips.Mul.MulChip

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
`MulOperation.allHold_constraints_iff_is_real` is 60+ conjuncts
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
  state : CPUState T
  adapter : RTypeReader T
  op_a_write_value : Vector T 4             -- Main[28..31]
  carry : Vector T 16                       -- Main[32..47]
  product : Vector T 16                     -- Main[48..63]
  b_low_bytes : Vector T 4                  -- Main[64..67]
  c_low_bytes : Vector T 4                  -- Main[68..71]
  -- Five trailing single-cell fields collapsed into one `Vector T 5` so the
  -- new `next_pc_carry_value` keeps the struct at 29 < 33 fields, below the
  -- `deriving ProvableStruct` handler's list-literal elaboration ceiling.
  -- Cell layout preserved (depth-first flatten): mul_aux_bits[0..4] map to
  -- the old `b_msb, c_msb, product_msb, b_sign_extend, c_sign_extend` order.
  -- None of the five are referenced in `main` / `Spec` / `Assertion.main` /
  -- `FormalSpec` today — only destructured with `_` placeholders.
  mul_aux_bits : Vector T 5                 -- Main[72..76]
  -- Slot order matches upstream's `MulCols<T, M>` field declaration order in
  -- alu/mul/mod.rs (is_mul, is_mulh, is_mulhu, is_mulhsu, is_mulw). The
  -- previous Lean order put is_mulw at Main[79] and is_mulhu at Main[81] —
  -- bug: the constraint compiler emits the Rust struct order, so the Lean
  -- destructure was reading upstream's is_mulhu as is_mulw (and vice versa).
  -- Opcode mux `is_mulw * 13 + is_mulhu * 24` then dispatched the wrong
  -- variants. Fixed 2026-05-23.
  is_mul : T                                -- Main[77]
  is_mulh : T                               -- Main[78]
  is_mulhu : T                              -- Main[79]
  is_mulhsu : T                             -- Main[80]
  is_mulw : T                               -- Main[81]
  next_pc_carry_value : Vector T 3          -- Clean-only: pc + 4 carry witness
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
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, _op_a_memory, op_a_0, op_b, _op_b_memory, op_c, _op_c_memory⟩, _op_a_write_value,
       carry, product, _b_low_bytes, _c_low_bytes, _mul_aux_bits,
       is_mul, is_mulh, is_mulhu, is_mulhsu, is_mulw,
       _next_pc_carry_value⟩ := cols
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
conjuncts of `MulOperation.allHold_constraints_iff_is_real`'s RHS
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
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.memoryAccessSpec
    (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 4
    (SP1Clean.MemoryAccess.ofRegisterShared cols.adapter.op_a
      { prev_value := cols.adapter.op_a_memory.prev_value,
        access_timestamp :=
          { prev_low := cols.adapter.op_a_memory.access_timestamp.prev_low,
            diff_low_limb := cols.adapter.op_a_memory.access_timestamp.diff_low_limb } }) ∧
  SP1Clean.memoryAccessSpec
    (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 3
    (SP1Clean.MemoryAccess.ofRegisterShared cols.adapter.op_b
      { prev_value := cols.adapter.op_b_memory.prev_value,
        access_timestamp :=
          { prev_low := cols.adapter.op_b_memory.access_timestamp.prev_low,
            diff_low_limb := cols.adapter.op_b_memory.access_timestamp.diff_low_limb } }) ∧
  SP1Clean.memoryAccessSpec
    (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 2
    (SP1Clean.MemoryAccess.ofRegisterShared cols.adapter.op_c
      { prev_value := cols.adapter.op_c_memory.prev_value,
        access_timestamp :=
          { prev_low := cols.adapter.op_c_memory.access_timestamp.prev_low,
            diff_low_limb := cols.adapter.op_c_memory.access_timestamp.diff_low_limb } }) ∧
  -- Program-bus consequence with the selector-weighted opcode.
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc,
      opcode := cols.is_mul * 11 + cols.is_mulh * 12 + cols.is_mulw * 13
                  + cols.is_mulhsu * 14 + cols.is_mulhu * 24,
      op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0],
      op_c := #v[cols.adapter.op_c, 0, 0, 0],
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 0 } ∧
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
  cols.adapter.op_a_0 = 0 ∧
  mulSpec cols

/-- Project a raw SP1 row into the structured `MulCols` view.
82 columns; `carry : Vector T 16`, `product : Vector T 16`,
`b_low_bytes/c_low_bytes : Vector T 4`, `mul_aux_bits : Vector T 5`
packed from contiguous Main slots. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 82) : MulCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
      ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    Main[21],
    ⟨#v[Main[22], Main[23], Main[24], Main[25]], ⟨Main[26], Main[27]⟩⟩⟩,
   #v[Main[28], Main[29], Main[30], Main[31]],
   #v[Main[32], Main[33], Main[34], Main[35], Main[36], Main[37], Main[38],
      Main[39], Main[40], Main[41], Main[42], Main[43], Main[44], Main[45],
      Main[46], Main[47]],
   #v[Main[48], Main[49], Main[50], Main[51], Main[52], Main[53], Main[54],
      Main[55], Main[56], Main[57], Main[58], Main[59], Main[60], Main[61],
      Main[62], Main[63]],
   #v[Main[64], Main[65], Main[66], Main[67]],
   #v[Main[68], Main[69], Main[70], Main[71]],
   #v[Main[72], Main[73], Main[74], Main[75], Main[76]],
   Main[77], Main[78], Main[79], Main[80], Main[81],
   #v[0, 0, 0]⟩

/-- The chip-level half-iff bridge (Mul). **Proof body sorry'd**. -/
theorem spec_implies_allHold (Main : Vector (ZMod p) 82)
    (h_is_real : Main[77] + Main[78] + Main[79] + Main[80] + Main[81] = 1)
    (h_op_a_0 : Main[30] = 0)
    (h_spec : Spec (fromMain Main)) :
    (_root_.Mul.constraints Main).allHold := by
  sorry

/-- Clean-side `correct_mul`: 64-bit multiply (low 64 bits). -/
theorem correct_mul [Fact (2 ^ 24 < p)]
    (Main : Vector (ZMod p) 82) (s : SailState)
    (h_is_mul : Main[77] = 1)
    (h_others_zero : Main[78] = 0 ∧ Main[79] = 0 ∧ Main[80] = 0 ∧ Main[81] = 0)
    (h_op_a_0 : Main[30] = 0)
    (h_spec : Spec (fromMain Main))
    (state_cstrs : (_root_.Mul.constraints Main).initialState s) :
    let op_c := _root_.Mul.sp1_op_c Main
    let op_b := _root_.Mul.sp1_op_b Main
    let op_a := _root_.Mul.sp1_op_a Main
    (_root_.Mul.Poly.spec_mul (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.Mul.sp1_mul_chip Main).run s :=
  _root_.Mul.Poly.correct_mul Main s
    (spec_implies_allHold Main
      (by obtain ⟨h78, h79, h80, h81⟩ := h_others_zero
          rw [h_is_mul, h78, h79, h80, h81]; ring)
      h_op_a_0 h_spec)
    ⟨h_is_mul, h_op_a_0⟩ state_cstrs

/-! ## Full `FormalAssertion` promotion (Path-2)

Drops the inline CPUState byte lookups (converted to
`SP1Clean.CPUState.assertion` subcircuit) plus the 16 carry-bound and
16 product-bound lookups. `Assertion.main` keeps only the
subcircuit-and-scalar-gate surface: CPUState, ProgramTable, the 5
opcode boolean gates, the aggregate-is-real boolean, and `op_a_0 === 0`.
The MulOperation carry chain stays in legacy `Spec` via the `mulSpec`
placeholder; memory-bus consistency is deferred to OfflineMemory. -/

namespace Assertion

open Circuit

@[reducible]
def main (cols : Var MulCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c, op_c_memory⟩, _op_a_write_value,
       _carry, _product, _b_low_bytes, _c_low_bytes, _mul_aux_bits,
       is_mul, is_mulh, is_mulhu, is_mulhsu, is_mulw,
       next_pc_carry_value⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  let is_real_e := is_mul + is_mulh + is_mulw + is_mulhsu + is_mulhu
  let opcode_e := is_mul * 11 + is_mulh * 12 + is_mulw * 13
                    + is_mulhsu * 14 + is_mulhu * 24
  SP1Clean.ProgramTable.assertion
    (⟨pc, opcode_e, op_a, #v[op_b, 0, 0, 0], #v[op_c, 0, 0, 0],
      op_a_0, 0, 0⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  -- AddrAddOperation: pc + 4 carry-aware computation, stored in
  -- `next_pc_carry_value`. Constrains the new column to be the
  -- carry-aware semantic next_pc for the trace-level state bus.
  SP1Clean.AddrAddOp.assertion
    (⟨#v[pc[0], pc[1], pc[2], (0 : Expression (ZMod p))],
       #v[(4 : Expression (ZMod p)), 0, 0, 0],
       next_pc_carry_value⟩ :
      Var SP1Clean.AddrAddOp.Inputs (ZMod p))
  is_mul * (is_mul - 1) === 0
  is_mulh * (is_mulh - 1) === 0
  is_mulw * (is_mulw - 1) === 0
  is_mulhsu * (is_mulhsu - 1) === 0
  is_mulhu * (is_mulhu - 1) === 0
  is_real_e * (is_real_e - 1) === 0
  op_a_0 === 0
  -- Iter-8 sub-task E: per-operand memory-bus byte content.
  -- R-type: op_a/+4, op_b/+3, op_c/+2.
  let clk_low := clk_0_16 + clk_16_24 * 65536
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 4, op_a_memory.access_timestamp.prev_low, op_a_memory.access_timestamp.diff_low_limb,
       op_a_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 3, op_b_memory.access_timestamp.prev_low, op_b_memory.access_timestamp.diff_low_limb,
       op_b_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 2, op_c_memory.access_timestamp.prev_low, op_c_memory.access_timestamp.diff_low_limb,
       op_c_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))

set_option maxHeartbeats 800000 in
-- Higher heartbeats: 28 input fields + 4 subcircuit calls + 3 OperandAccess
-- calls pushes localLength_eq synthesis past the default 200k cap.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) MulCols unit where
  name := "SP1Clean.Mul"
  main := main
  localLength _ := 0

def Assumptions (_ : MulCols (ZMod p)) : Prop := True

def FormalSpec (cols : MulCols (ZMod p)) : Prop :=
  let is_real : ZMod p :=
    cols.is_mul + cols.is_mulh + cols.is_mulw + cols.is_mulhsu + cols.is_mulhu
  let opcode_e : ZMod p :=
    cols.is_mul * 11 + cols.is_mulh * 12 + cols.is_mulw * 13
      + cols.is_mulhsu * 14 + cols.is_mulhu * 24
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := opcode_e, op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0], op_c := #v[cols.adapter.op_c, 0, 0, 0],
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 0 } ∧
  SP1Clean.AddrAddOp.assertion.Spec
    ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
     #v[(4 : ZMod p), 0, 0, 0],
     cols.next_pc_carry_value⟩ ∧
  cols.is_mul * (cols.is_mul - 1) = 0 ∧
  cols.is_mulh * (cols.is_mulh - 1) = 0 ∧
  cols.is_mulw * (cols.is_mulw - 1) = 0 ∧
  cols.is_mulhsu * (cols.is_mulhsu - 1) = 0 ∧
  cols.is_mulhu * (cols.is_mulhu - 1) = 0 ∧
  is_real * (is_real - 1) = 0 ∧
  cols.adapter.op_a_0 = 0 ∧
  -- Iter-8 sub-task E: per-operand memory-bus byte-content consequences.
  -- R-type: op_a/+4, op_b/+3, op_c/+2.
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 4, cols.adapter.op_a_memory.access_timestamp.prev_low, cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 3, cols.adapter.op_b_memory.access_timestamp.prev_low, cols.adapter.op_b_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_b_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 2, cols.adapter.op_c_memory.access_timestamp.prev_low, cols.adapter.op_c_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_c_memory.prev_value⟩

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  -- Substitute all input-eval equations so the goal matches the subcircuit
  -- specs (which reference `Expression.eval env input_var_X` of pc/etc).
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30,
          e31, e32, e33⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu_sub, h_prog_sub, h_addr_sub, h_mul, h_mulh, h_mulw, h_mulhsu,
          h_mulhu, h_real, h_op_a_0,
          h_oa_a, h_oa_b, h_oa_c⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_prog_sub trivial
  · simp only [Vector.getElem_map]
    exact h_addr_sub trivial
  · linear_combination h_mul
  · linear_combination h_mulh
  · linear_combination h_mulw
  · linear_combination h_mulhsu
  · linear_combination h_mulhu
  · linear_combination h_real
  · exact h_op_a_0
  · exact h_oa_a trivial
  · exact h_oa_b trivial
  · exact h_oa_c trivial

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30,
          e31, e32, e33⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu, h_prog, h_addr, h_mul, h_mulh, h_mulw, h_mulhsu, h_mulhu,
          h_real, h_op_a_0,
          h_oa_a, h_oa_b, h_oa_c⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_prog⟩
  · refine ⟨trivial, ?_⟩
    simp only [Vector.getElem_map] at h_addr
    exact h_addr
  · linear_combination h_mul
  · linear_combination h_mulh
  · linear_combination h_mulw
  · linear_combination h_mulhsu
  · linear_combination h_mulhu
  · linear_combination h_real
  · exact h_op_a_0
  · exact ⟨trivial, h_oa_a⟩
  · exact ⟨trivial, h_oa_b⟩
  · exact ⟨trivial, h_oa_c⟩

end Assertion

def assertion : FormalAssertion (ZMod p) MulCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.Mul
