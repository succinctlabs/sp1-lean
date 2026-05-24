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
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.RTypeReader
import SP1Clean.Reader.OperandAccess
import SP1Chips.Mul.MulChip
import SP1Chips.Mul.Common
import SP1Chips.Soundness
import SP1Clean.TrustMode

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

set_option linter.style.setOption false
set_option linter.style.longLine false

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
  op_a_write_value : Vector T 4             -- Main[28..31] (== mul_operation.product[0..3])
  -- Phase 3c: MulOperation (45 cells) nested as a single field, replacing
  -- the previous 5 flat fields (carry:16, product:16, b_low_bytes:4,
  -- c_low_bytes:4, mul_aux_bits:5). The 5-field `mul_aux_bits` collapse
  -- (which existed to keep the struct under the 33-field ProvableStruct
  -- elaboration ceiling) is no longer needed; MulOperation's 9 nested
  -- fields naturally expose b_msb/c_msb/product_msb/b_sign_extend/c_sign_extend
  -- without flattening.
  mul_operation : MulOperation T            -- Main[32..76]
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
  adapter_cols : SP1Clean.UserModeReaderCols T
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
       mul_op,
       is_mul, is_mulh, is_mulhu, is_mulhsu, is_mulw,
       _adapter_cols⟩ := cols
  let carry := mul_op.carry
  let product := mul_op.product
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

/-- The MulOperation-derivable Spec content: exactly the chip-level
`MulOperation.constraints.allHold` with the chip's args (mult =
aggregate is-real sum; opcode selectors in the order MulOperation
expects: is_mul, is_mulh, is_mulw, is_mulhu, is_mulhsu). The bridge
to SP1 trivially threads this through the chip iff lemma. -/
def mulSpec (cols : MulCols (ZMod p)) : Prop :=
  (_root_.MulOperation.constraints
      cols.op_a_write_value
      cols.adapter.op_b_memory.prev_value
      cols.adapter.op_c_memory.prev_value
      cols.mul_operation
      (cols.is_mul + cols.is_mulh + cols.is_mulhu + cols.is_mulhsu + cols.is_mulw)
      cols.is_mul cols.is_mulh cols.is_mulw cols.is_mulhu cols.is_mulhsu).allHold

/-- The Clean-flavored Spec for `MulChip`. Composes the existing
per-fragment specs (`cpuStateSpec`) with three `memoryAccessSpec`
records (op_a write, op_b read, op_c read), the `ProgramTable.Spec`
consequence, the selector boolean gates, and the placeholder
`mulSpec`. -/
def TraceSpec (cols : MulCols (ZMod p)) : Prop :=
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
      opcode := cols.is_mul * 11 + cols.is_mulh * 12 + cols.is_mulhu * 13
                  + cols.is_mulhsu * 14 + cols.is_mulw * 24,
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
  mulSpec cols ∧
  cols.adapter_cols.is_trusted = 1

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
   ⟨#v[Main[32], Main[33], Main[34], Main[35], Main[36], Main[37], Main[38],
       Main[39], Main[40], Main[41], Main[42], Main[43], Main[44], Main[45],
       Main[46], Main[47]],
    #v[Main[48], Main[49], Main[50], Main[51], Main[52], Main[53], Main[54],
       Main[55], Main[56], Main[57], Main[58], Main[59], Main[60], Main[61],
       Main[62], Main[63]],
    ⟨#v[Main[64], Main[65], Main[66], Main[67]]⟩,
    ⟨#v[Main[68], Main[69], Main[70], Main[71]]⟩,
    Main[72], Main[73], ⟨Main[74]⟩, Main[75], Main[76]⟩,
   Main[77], Main[78], Main[79], Main[80], Main[81],
   -- `adapter_cols.is_trusted` aliases the aggregate is_real sum
   -- (`Main[77]+...+Main[81]`), matching the upstream RTypeReader receiving
   -- `E3 E3` (is_real, is_trusted) where `E3` is that sum.
   ⟨Main[77] + Main[78] + Main[79] + Main[80] + Main[81]⟩⟩

set_option maxHeartbeats 1600000 in
-- Heartbeats elevated for the 10-conjunct refine + cpuStateSpec_iff_sp1 +
-- rtypeReaderSpec_iff_sp1 + ProgramTable.Spec re-association on 82 cols.
/-- The chip-level half-iff bridge (Mul). -/
theorem traceSpec_implies_allHold (Main : Vector (ZMod p) 82)
    (h_is_real : Main[77] + Main[78] + Main[79] + Main[80] + Main[81] = 1)
    (_h_op_a_0 : Main[30] = 0)
    (h_spec : TraceSpec (fromMain Main)) :
    (_root_.Mul.constraints Main).allHold := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [TraceSpec, fromMain, mulSpec] at h_spec
  obtain ⟨h_cpu_spec, h_mem_a, h_mem_b, h_mem_c, h_program,
          h_mul_bin, h_mulh_bin, h_mulw_bin, h_mulhsu_bin, h_mulhu_bin,
          h_aggregate, h_a0, h_mul_op, _h_trusted⟩ := h_spec
  change List.Forall SP1Constraint.toProp (_root_.Mul.constraints Main)
  rw [_root_.Mul.allHold_constraints_iff]
  -- 10-tuple refine matching the iff RHS order. Order in iff is
  -- MulOp/CPUState/RTypeReader + 5 booleans (77,78,79,81,80) + aggregate +
  -- op_a_0 = 0.
  refine ⟨?_, ?_, ?_, h_mul_bin, h_mulh_bin, h_mulhu_bin, h_mulw_bin,
          h_mulhsu_bin, ?_, h_a0⟩
  -- 1: MulOperation.constraints.allHold — direct from h_mul_op.
  · exact h_mul_op
  -- 2: CPUState.constraints.allHold — bridge via cpuStateSpec_iff_sp1
  --    after rw'ing is_real_sum = 1.
  · rw [show (Main[77] + Main[78] + Main[79] + Main[80] + Main[81] : ZMod p) = 1
        from h_is_real]
    exact (SP1Clean.CPUState.cpuStateSpec_iff_sp1).mpr h_cpu_spec
  -- 3: RTypeReader.constraints.allHold — assemble rtypeReaderSpec from
  --    ProgramTable.Spec + 3 memoryAccessSpec records + h_a0 (vacuous
  --    op_a_0 ≠ 0 → write_value zeros under Main[13] = 0).
  · rw [show (Main[77] + Main[78] + Main[79] + Main[80] + Main[81] : ZMod p) = 1
        from h_is_real]
    refine (SP1Clean.RTypeReader.rtypeReaderSpec_iff_sp1).mpr ?_
    simp only [SP1Clean.ProgramTable.Spec, SP1Clean.ProgramSpec,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ] at h_program
    obtain ⟨h_ti, h_op_a_lt, ⟨h_b0, _, _, _⟩, ⟨h_c0, _, _, _⟩,
            h_a0_bin, h_a0_iff, _h_imm_b, _h_imm_c, h_pc_mod, h_pc_0, h_pc_1, h_pc_2⟩
      := h_program
    simp only [SP1Clean.memoryAccessSpec, SP1Clean.MemoryAccess.ofRegisterShared,
      SP1Clean.MemoryAccess.ofShared] at h_mem_a h_mem_b h_mem_c
    refine ⟨?_, h_op_a_lt, h_b0, h_c0, h_a0_bin, h_a0_iff,
            ⟨h_pc_mod, h_pc_0, h_pc_1, h_pc_2⟩,
            ⟨⟨h_mem_a.1, h_mem_b.1, h_mem_c.1⟩,
             ⟨h_mem_c.2.1, h_mem_b.2.1, h_mem_a.2.1⟩,
             ⟨h_mem_a.2.2, h_mem_b.2.2, h_mem_c.2.2⟩⟩,
            ?_⟩
    -- trusted_instr: matches directly after Spec opcode mapping fixed
    -- (the field-order/opcode-pair bug was the prior obstacle).
    · convert h_ti using 2
    -- op_a_0 ≠ 0 → write_value zeros: vacuous under h_a0.
    · intro h_ne
      exact absurd h_a0 h_ne
  -- aggregate boolean — Spec order is (mul,mulh,mulw,mulhsu,mulhu) but iff
  -- uses Main slot order (77,78,79,80,81 = mul,mulh,mulhu,mulhsu,mulw).
  --   They're equal by commutativity; close via linear_combination.
  · linear_combination h_aggregate * 1

/-- Clean-side `correct_mul`: 64-bit multiply (low 64 bits). -/
theorem correct_mul [Fact (2 ^ 24 < p)]
    (Main : Vector (ZMod p) 82) (s : SailState)
    (h_is_mul : Main[77] = 1)
    (h_others_zero : Main[78] = 0 ∧ Main[79] = 0 ∧ Main[80] = 0 ∧ Main[81] = 0)
    (h_op_a_0 : Main[30] = 0)
    (h_spec : TraceSpec (fromMain Main))
    (state_cstrs : (_root_.Mul.constraints Main).initialState s) :
    let op_c := _root_.Mul.sp1_op_c Main
    let op_b := _root_.Mul.sp1_op_b Main
    let op_a := _root_.Mul.sp1_op_a Main
    (_root_.Mul.Poly.spec_mul (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.Mul.sp1_mul_chip Main).run s :=
  _root_.Mul.Poly.correct_mul Main s
    (traceSpec_implies_allHold Main
      (by obtain ⟨h78, h79, h80, h81⟩ := h_others_zero
          rw [h_is_mul, h78, h79, h80, h81]; ring)
      h_op_a_0 h_spec)
    ⟨h_is_mul, h_op_a_0⟩ state_cstrs

/-! ## RawSpec / SemanticSpec POC (parallel to AddChip's POC)

Same two-layer split as in `AddChip.lean`. `RawSpec` is the iff-RHS of
`Mul.allHold_constraints_iff` (3 sub-allHolds + 7 chip-list props);
`SemanticSpec` is the trace-facing contract (cpuStateSpec + 3
memoryAccessSpec + ProgramTable.Spec + is_real_bin + per-row Sail
equivalence via `soundness_mul` — single if-then-else cascade dispatching
on the 5 opcode flags, no per-variant unfolding). `raw_to_semantic`
confines the chip-internal MulOperation arithmetic + RTypeReader bridge
to one proof. -/

/-- Structural mirror of `Mul.constraints.allHold`. Matches the RHS of
`Mul.allHold_constraints_iff` at `SP1Chips/Mul/Common.lean:235`. -/
def RawSpec (Main : Vector (ZMod p) 82) : Prop :=
  (MulOperation.constraints (F := ZMod p)
      #v[Main[28], Main[29], Main[30], Main[31]]
      #v[Main[15], Main[16], Main[17], Main[18]]
      #v[Main[22], Main[23], Main[24], Main[25]]
      { carry := #v[Main[32], Main[33], Main[34], Main[35], Main[36], Main[37],
          Main[38], Main[39], Main[40], Main[41], Main[42], Main[43], Main[44],
          Main[45], Main[46], Main[47]],
        product := #v[Main[48], Main[49], Main[50], Main[51], Main[52], Main[53],
          Main[54], Main[55], Main[56], Main[57], Main[58], Main[59], Main[60],
          Main[61], Main[62], Main[63]],
        b_lower_byte := { low_bytes := #v[Main[64], Main[65], Main[66], Main[67]] },
        c_lower_byte := { low_bytes := #v[Main[68], Main[69], Main[70], Main[71]] },
        b_msb := Main[72], c_msb := Main[73],
        product_msb := { msb := Main[74] },
        b_sign_extend := Main[75], c_sign_extend := Main[76] }
      (Main[77] + Main[78] + Main[79] + Main[80] + Main[81])
      Main[77] Main[78] Main[81] Main[79] Main[80]).allHold ∧
  (CPUState.constraints (F := ZMod p)
      { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2],
        pc := #v[Main[3], Main[4], Main[5]] }
      #v[Main[3] + 4, Main[4], Main[5]] 8
      (Main[77] + Main[78] + Main[79] + Main[80] + Main[81])).allHold ∧
  (RTypeReader.constraints (F := ZMod p)
      Main[0] (Main[2] + Main[1] * 65536) #v[Main[3], Main[4], Main[5]]
      (Main[77] * 11 + Main[78] * 12 + Main[79] * 13 + Main[80] * 14 + Main[81] * 24)
      #v[Main[28], Main[29], Main[30], Main[31]]
      { op_a := Main[6],
        op_a_memory :=
          { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
            access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } },
        op_a_0 := Main[13], op_b := Main[14],
        op_b_memory :=
          { prev_value := #v[Main[15], Main[16], Main[17], Main[18]],
            access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } },
        op_c := Main[21],
        op_c_memory :=
          { prev_value := #v[Main[22], Main[23], Main[24], Main[25]],
            access_timestamp := { prev_low := Main[26], diff_low_limb := Main[27] } } }
      (Main[77] + Main[78] + Main[79] + Main[80] + Main[81])
      (Main[77] + Main[78] + Main[79] + Main[80] + Main[81])).allHold ∧
  Main[77] * (Main[77] - 1) = 0 ∧
  Main[78] * (Main[78] - 1) = 0 ∧
  Main[79] * (Main[79] - 1) = 0 ∧
  Main[81] * (Main[81] - 1) = 0 ∧
  Main[80] * (Main[80] - 1) = 0 ∧
  (Main[77] + Main[78] + Main[79] + Main[80] + Main[81]) *
    (Main[77] + Main[78] + Main[79] + Main[80] + Main[81] - 1) = 0 ∧
  Main[13] = 0

/-- `RawSpec` is exactly `allHold`. Direct rewrite via the Phase-0 iff
`Mul.allHold_constraints_iff`. -/
theorem rawSpec_iff_allHold (Main : Vector (ZMod p) 82) :
    (_root_.Mul.constraints Main).allHold ↔ RawSpec Main := by
  change List.Forall SP1Constraint.toProp (_root_.Mul.constraints Main) ↔ _
  rw [_root_.Mul.allHold_constraints_iff]
  rfl

/-- The row's user-facing contract: trace-facing structural specs + Sail
equivalence as a Prop. The Sail-eq conjunct uses `SP1Chips.soundness_mul`'s
if-then-else cascade dispatching on the 5 opcode flags. -/
def SemanticSpec (Main : Vector (ZMod p) 82) : Prop :=
  let cols := fromMain Main
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
  SP1Clean.ProgramTable.Spec
      { pc := cols.state.pc,
        opcode := cols.is_mul * 11 + cols.is_mulh * 12 + cols.is_mulhu * 13
                  + cols.is_mulhsu * 14 + cols.is_mulw * 24,
        op_a := cols.adapter.op_a,
        op_b := #v[cols.adapter.op_b, 0, 0, 0],
        op_c := #v[cols.adapter.op_c, 0, 0, 0],
        op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 0 } ∧
  (cols.is_mul + cols.is_mulh + cols.is_mulhu + cols.is_mulhsu + cols.is_mulw) *
    (cols.is_mul + cols.is_mulh + cols.is_mulhu + cols.is_mulhsu + cols.is_mulw - 1) = 0 ∧
  -- Per-row Sail equivalence via the SP1Chips.Soundness aggregator —
  -- one if-then-else cascade dispatching on all 5 opcode flags.
  (∀ s : SailState, (_root_.Mul.constraints Main).initialState s →
    (_root_.Mul.sp1_mul_chip Main).run s =
      (if _root_.Mul.is_mul Main then
        (_root_.Mul.Poly.spec_mul (.Regidx (_root_.Mul.sp1_op_c Main))
          (.Regidx (_root_.Mul.sp1_op_b Main))
          (.Regidx (_root_.Mul.sp1_op_a Main))).run s
      else if _root_.Mul.is_mulh Main then
        (_root_.Mulh.Poly.spec_mulh (.Regidx (_root_.Mul.sp1_op_c Main))
          (.Regidx (_root_.Mul.sp1_op_b Main))
          (.Regidx (_root_.Mul.sp1_op_a Main))).run s
      else if _root_.Mul.is_mulhu Main then
        (_root_.Mulhu.Poly.spec_mulhu (.Regidx (_root_.Mul.sp1_op_c Main))
          (.Regidx (_root_.Mul.sp1_op_b Main))
          (.Regidx (_root_.Mul.sp1_op_a Main))).run s
      else if _root_.Mul.is_mulhsu Main then
        (_root_.Mulhsu.Poly.spec_mulhsu (.Regidx (_root_.Mul.sp1_op_c Main))
          (.Regidx (_root_.Mul.sp1_op_b Main))
          (.Regidx (_root_.Mul.sp1_op_a Main))).run s
      else if _root_.Mul.is_mulw Main then
        (_root_.Mulw.Poly.spec_mulw (.Regidx (_root_.Mul.sp1_op_c Main))
          (.Regidx (_root_.Mul.sp1_op_b Main))
          (.Regidx (_root_.Mul.sp1_op_a Main))).run s
      else (_root_.Mul.sp1_mul_chip Main).run s))

set_option maxHeartbeats 1600000 in
-- Heartbeats elevated for the ProgramTable.Spec assembly + soundness_mul plumbing.
/-- The bridge: `RawSpec → SemanticSpec` under `is_real_sum = 1`. Confines all
chip-internal arithmetic (MulOperation carry chain, byte ranges, Sail
equivalence via `soundness_mul`) to this one proof. The `Fact (2 ^ 24 < p)`
requirement matches `Mul.Poly.correct_mul`'s bound (inherited via
`soundness_mul`). -/
theorem raw_to_semantic [Fact (2 ^ 24 < p)] (Main : Vector (ZMod p) 82)
    (h_is_real : Main[77] + Main[78] + Main[79] + Main[80] + Main[81] = 1)
    (h_raw : RawSpec Main) : SemanticSpec Main := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h_mulop, h_cpu_raw, h_rtr_raw, _h_mul_bin, _h_mulh_bin, _h_mulhu_bin,
          _h_mulw_bin, _h_mulhsu_bin, h_aggregate, h_a0⟩ := h_raw
  have h_allHold : (_root_.Mul.constraints Main).allHold :=
    (rawSpec_iff_allHold Main).mpr ⟨h_mulop, h_cpu_raw, h_rtr_raw,
      _h_mul_bin, _h_mulh_bin, _h_mulhu_bin, _h_mulw_bin, _h_mulhsu_bin, h_aggregate, h_a0⟩
  rw [h_is_real] at h_cpu_raw h_rtr_raw
  have h_cpu_spec := SP1Clean.CPUState.cpuStateSpec_iff_sp1.mp h_cpu_raw
  have h_rtr_spec := SP1Clean.RTypeReader.rtypeReaderSpec_iff_sp1.mp h_rtr_raw
  obtain ⟨h_ti, h_op_a_lt, h_op_b_lt, h_op_c_lt, h_a0_bin, h_a0_iff,
          ⟨h_pc_mod, h_pc_0_lt, h_pc_1_lt, h_pc_2_lt⟩,
          ⟨⟨h_diff_a, h_diff_b, h_diff_c⟩,
           ⟨h_ts_c, h_ts_b, h_ts_a⟩,
           ⟨h_isU64_a, h_isU64_b, h_isU64_c⟩⟩,
          _h_a0_implies⟩ := h_rtr_spec
  have h_zero_lt : (0 : ZMod p) < (65536 : ZMod p) := by
    have h65536_lt : (65536 : ℕ) < p := by
      have := Fact.out (p := 2 ^ 17 < p); omega
    have h65536_val : (65536 : ZMod p).val = 65536 := ZMod.val_natCast_of_lt h65536_lt
    change (0 : ZMod p).val < (65536 : ZMod p).val
    rw [ZMod.val_zero, h65536_val]; omega
  refine ⟨h_cpu_spec,
          ⟨h_diff_a, h_ts_a, h_isU64_a⟩,
          ⟨h_diff_b, h_ts_b, h_isU64_b⟩,
          ⟨h_diff_c, h_ts_c, h_isU64_c⟩,
          ?_, ?_, ?_⟩
  -- ProgramTable.Spec
  · simp only [SP1Clean.ProgramTable.Spec, SP1Clean.ProgramSpec,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
    refine ⟨?_, h_op_a_lt, ⟨h_op_b_lt, h_zero_lt, h_zero_lt, h_zero_lt⟩,
            ⟨h_op_c_lt, h_zero_lt, h_zero_lt, h_zero_lt⟩,
            h_a0_bin, h_a0_iff, Or.inl trivial, Or.inl trivial,
            h_pc_mod, h_pc_0_lt, h_pc_1_lt, h_pc_2_lt⟩
    -- trusted_instr: matches after the opcode formula reduces.
    convert h_ti using 2
  -- aggregate boolean (Cols-field order vs Main-slot order via linear_combination).
  · linear_combination h_aggregate * 1
  -- Sail equivalence via soundness_mul
  · intro s state_cstrs
    exact soundness_mul Main s h_allHold state_cstrs

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
       _mul_op,
       is_mul, is_mulh, is_mulhu, is_mulhsu, is_mulw,
       _adapter_cols⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  let is_real_e := is_mul + is_mulh + is_mulw + is_mulhsu + is_mulhu
  let opcode_e := is_mul * 11 + is_mulh * 12 + is_mulw * 13
                    + is_mulhsu * 14 + is_mulhu * 24
  SP1Clean.ProgramTable.assertion
    (⟨pc, opcode_e, op_a, #v[op_b, 0, 0, 0], #v[op_c, 0, 0, 0],
      op_a_0, 0, 0⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
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
  obtain ⟨h_cpu_sub, h_prog_sub, h_mul, h_mulh, h_mulw, h_mulhsu,
          h_mulhu, h_real, h_op_a_0,
          h_oa_a, h_oa_b, h_oa_c⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_prog_sub trivial
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
  obtain ⟨h_cpu, h_prog, h_mul, h_mulh, h_mulw, h_mulhsu, h_mulhu,
          h_real, h_op_a_0,
          h_oa_a, h_oa_b, h_oa_c⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_prog⟩
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
