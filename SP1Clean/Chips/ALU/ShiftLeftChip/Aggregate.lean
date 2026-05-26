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
import SP1Operations.Operation.U16MSBOperation.U16MSBOperation
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.ALUTypeReader.ALUTypeReader
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.OperandAccess
import SP1Chips.ShiftLeft.ShiftLeftChip
import SP1Clean.TrustMode
import SP1Clean.Chips.Structs

/-! # Chip-level `ShiftLeftChip` mirror — second heavy-arithmetic scaling probe

The ShiftLeft chip bundles 4 RV64IM left-shift variants (sll/slli/sllw/slliw)
into a single 65-column trace. Distinct from `MulChip` in its mechanics:
the 64-bit shift amount is decomposed into 6 boolean bits (`Main[36..41]`)
which select between 1×, 2×, 4×, 8×, 16×, 32× multiplications via a chain
of multipliers (`Main[42..44]`). A one-hot byte-shift selector
(`Main[45..48]`) routes the shifted limbs into the appropriate write
position. The result is committed to `Main[32..35]`.

This is the **second heavy-chip data point** for Risk 1 (heavy-chip
scaling). The SP1-side proof uses `maxHeartbeats 100000000` (100M)
because of the bit-decomposition chain and the conditional `(is_sll = 0
∨ byte_selector_k = 0 ∨ ...)` clauses. The Clean structural mirror is
expected to compile much faster since it skips those proof obligations.

Same focused-pilot-mirror discipline as `MulChip`: define the column
struct, emit the structural lookups in `main` (CPUState bounds, byte
shift power lookup, ProgramTable.assertion with selector-weighted
opcode), expose the per-row Spec consequences, leave the shift-
arithmetic content to `shiftSpec` as a placeholder.

Opcode encoding mirrors SP1: `is_sll * 8 + is_sllw * 14` for the
top-level opcode field (RV64IM IDs).
-/

namespace SP1Clean.ShiftLeft

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The aggregate is-real flag: at least one of the two shift variants
active. -/
def isRealExpr (cols : Var ShiftLeftCols (ZMod p)) : Expression (ZMod p) :=
  cols.is_sll + cols.is_sllw

/-- The opcode field expression for the program-bus interaction:
`is_sll * 8 + is_sllw * 14`. Matches SP1's RV64IM opcode IDs (SLL=8,
SLLW=14). The `imm_c` flag toggles R-type (sll/sllw) vs I-type
(slli/slliw) at chip granularity. -/
def opcodeExpr (cols : Var ShiftLeftCols (ZMod p)) : Expression (ZMod p) :=
  cols.is_sll * 8 + cols.is_sllw * 14

/-- Clean-side circuit. Emits the structural lookups and asserts:
- CPUState clk bounds (via subcircuit)
- 6 boolean asserts on the bit-decomposition
- 4 boolean asserts on the byte-shift selector
- 2 boolean asserts on the opcode selectors
- Aggregate is-real boolean
- ProgramTable.assertion with selector-weighted opcode
- op_a_0 = 0

The shift-arithmetic content (bit-decomposition correctness, shift
power chain, byte-shift one-hot, limb-shift correctness) is deferred
to `shiftSpec` placeholder; see file docstring. -/
def main (cols : Var ShiftLeftCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, _op_a_memory, op_a_0, op_b, _op_b_memory, op_c, _op_c_memory, imm_c⟩,
       _result,
       c_bits, _v_01, _v_012, _v_0123, shift_u16, _lower_limb, _higher_limb,
       _limb_result, _sllw_msb, is_sll, is_sllw, _is_sllw_imm,
       _adapter_cols⟩ := cols
  -- CPUState range lookups (clk_0_16 progression + clk_16_24 U8 bound).
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  -- 6 boolean asserts on the bit decomposition.
  c_bits[0] * (c_bits[0] - 1) === 0
  c_bits[1] * (c_bits[1] - 1) === 0
  c_bits[2] * (c_bits[2] - 1) === 0
  c_bits[3] * (c_bits[3] - 1) === 0
  c_bits[4] * (c_bits[4] - 1) === 0
  c_bits[5] * (c_bits[5] - 1) === 0
  -- 4 boolean asserts on the byte-shift selector.
  shift_u16[0] * (shift_u16[0] - 1) === 0
  shift_u16[1] * (shift_u16[1] - 1) === 0
  shift_u16[2] * (shift_u16[2] - 1) === 0
  shift_u16[3] * (shift_u16[3] - 1) === 0
  -- 2 opcode-selector boolean asserts + aggregate is-real boolean.
  is_sll * (is_sll - 1) === 0
  is_sllw * (is_sllw - 1) === 0
  (is_sll + is_sllw) * (is_sll + is_sllw - 1) === 0
  -- Program-bus interaction. R-type discipline when imm_c = 0
  -- (sll/sllw); I-type when imm_c = 1 (slli/slliw). `op_c : Word T` is
  -- a 4-limb field — for R-type it's just `op_c[0]` (the register index)
  -- with limbs 1..3 zeroed by the trusted_instr check.
  SP1Clean.ProgramTable.assertion
    (⟨pc, is_sll * 8 + is_sllw * 14,
      op_a, #v[op_b, 0, 0, 0], op_c,
      op_a_0, 0, imm_c⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  -- op_a_0 forced to zero.
  op_a_0 === 0

/-- The shift-arithmetic Spec content. Bundles the iff-RHS conjuncts of
`_root_.ShiftLeft.allHold_constraints_iff` that aren't otherwise carried
by the chip-level Spec (cpuStateSpec / memoryAccessSpec / ProgramTable.Spec /
boolean gates). Includes:
  - `U16MSBOperation.constraints.allHold` for the SLLW sign-extension MSB
  - `ALUTypeReader.constraints.allHold` (raw form — assembly from factored
    Spec components is awkward due to imm_c-gated op_c)
  - The shift-exponent byte bound on `op_c[0]`
  - Byte-offset gates linking `c_bits[4..5]` to `shift_u16[0..3]`
  - Shift-power chain (`v_01`, `v_012`, `v_0123`)
  - Per-limb shift bounds/identities (Main[15..18] inputs, lower/higher limbs)
  - Per-limb output (Main[57..60] = `limb_result`)
  - 16 SLL gated output equations + 4 SLLW + 2 SLLW sign extensions
  - `is_sllw_imm` derivation
-/
def shiftSpec (cols : ShiftLeftCols (ZMod p)) : Prop :=
  (_root_.U16MSBOperation.constraints cols.result[1]
      cols.sllw_msb cols.is_sllw).allHold ∧
  (_root_.ALUTypeReader.constraints cols.state.clk_high
      (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) cols.state.pc
      (cols.is_sll * 6 + cols.is_sllw * 21)
      cols.result cols.adapter
      (cols.is_sll + cols.is_sllw) (cols.is_sll + cols.is_sllw)).allHold ∧
  -- shift-exponent bound: (op_c[0] - bit_decomp) * 64⁻¹ < 2^10
  (¬ cols.is_sll + cols.is_sllw = 0 →
    ((cols.adapter.op_c_memory.prev_value[0] - (cols.c_bits[0] + cols.c_bits[1] * 2 +
        cols.c_bits[2] * 4 + cols.c_bits[3] * 8 + cols.c_bits[4] * 16 +
        cols.c_bits[5] * 32)) * ((64 : ZMod p)⁻¹)).val < 2 ^ (10 : ZMod p).val) ∧
  -- 4 byte-offset gates: shift_u16[i] = 0 ∨ <bit decomp = i>
  (cols.shift_u16[0] = 0 ∨ cols.c_bits[4] + cols.c_bits[5] * 2 * cols.is_sll = 0) ∧
  (cols.shift_u16[1] = 0 ∨ cols.c_bits[4] + cols.c_bits[5] * 2 * cols.is_sll = 1) ∧
  (cols.shift_u16[2] = 0 ∨ cols.c_bits[4] + cols.c_bits[5] * 2 * cols.is_sll = 2) ∧
  (cols.shift_u16[3] = 0 ∨ cols.c_bits[4] + cols.c_bits[5] * 2 * cols.is_sll = 3) ∧
  -- shift_u16 one-hot under is_real
  (cols.is_sll + cols.is_sllw = 0 ∨
    cols.shift_u16[0] + cols.shift_u16[1] + cols.shift_u16[2] + cols.shift_u16[3] = 1) ∧
  -- shift-power chain
  (cols.v_01 = (cols.c_bits[0] + 1) * (cols.c_bits[1] * 3 + 1)) ∧
  (cols.v_012 = cols.v_01 * (cols.c_bits[2] * 15 + 1)) ∧
  (cols.v_0123 = cols.v_012 * (cols.c_bits[3] * 255 + 1)) ∧
  -- per-limb shift bounds + identities (4 sets for Main[15..18])
  (¬ cols.is_sll + cols.is_sllw = 0 →
    (cols.lower_limb[0]).val < 2 ^ ((16 : ZMod p) - (cols.c_bits[0] + cols.c_bits[1] * 2 +
        cols.c_bits[2] * 4 + cols.c_bits[3] * 8)).val) ∧
  (¬ cols.is_sll + cols.is_sllw = 0 →
    (cols.higher_limb[0]).val < 2 ^ (cols.c_bits[0] + cols.c_bits[1] * 2 +
        cols.c_bits[2] * 4 + cols.c_bits[3] * 8).val) ∧
  (cols.adapter.op_b_memory.prev_value[0] * cols.v_0123 =
    cols.higher_limb[0] * 65536 + cols.lower_limb[0] * cols.v_0123) ∧
  (¬ cols.is_sll + cols.is_sllw = 0 →
    (cols.lower_limb[1]).val < 2 ^ ((16 : ZMod p) - (cols.c_bits[0] + cols.c_bits[1] * 2 +
        cols.c_bits[2] * 4 + cols.c_bits[3] * 8)).val) ∧
  (¬ cols.is_sll + cols.is_sllw = 0 →
    (cols.higher_limb[1]).val < 2 ^ (cols.c_bits[0] + cols.c_bits[1] * 2 +
        cols.c_bits[2] * 4 + cols.c_bits[3] * 8).val) ∧
  (cols.adapter.op_b_memory.prev_value[1] * cols.v_0123 =
    cols.higher_limb[1] * 65536 + cols.lower_limb[1] * cols.v_0123) ∧
  (¬ cols.is_sll + cols.is_sllw = 0 →
    (cols.lower_limb[2]).val < 2 ^ ((16 : ZMod p) - (cols.c_bits[0] + cols.c_bits[1] * 2 +
        cols.c_bits[2] * 4 + cols.c_bits[3] * 8)).val) ∧
  (¬ cols.is_sll + cols.is_sllw = 0 →
    (cols.higher_limb[2]).val < 2 ^ (cols.c_bits[0] + cols.c_bits[1] * 2 +
        cols.c_bits[2] * 4 + cols.c_bits[3] * 8).val) ∧
  (cols.adapter.op_b_memory.prev_value[2] * cols.v_0123 =
    cols.higher_limb[2] * 65536 + cols.lower_limb[2] * cols.v_0123) ∧
  (¬ cols.is_sll + cols.is_sllw = 0 →
    (cols.lower_limb[3]).val < 2 ^ ((16 : ZMod p) - (cols.c_bits[0] + cols.c_bits[1] * 2 +
        cols.c_bits[2] * 4 + cols.c_bits[3] * 8)).val) ∧
  (¬ cols.is_sll + cols.is_sllw = 0 →
    (cols.higher_limb[3]).val < 2 ^ (cols.c_bits[0] + cols.c_bits[1] * 2 +
        cols.c_bits[2] * 4 + cols.c_bits[3] * 8).val) ∧
  (cols.adapter.op_b_memory.prev_value[3] * cols.v_0123 =
    cols.higher_limb[3] * 65536 + cols.lower_limb[3] * cols.v_0123) ∧
  -- limb_result equations
  (cols.limb_result[0] = cols.lower_limb[0] * cols.v_0123) ∧
  (cols.limb_result[1] = cols.lower_limb[1] * cols.v_0123 + cols.higher_limb[0]) ∧
  (cols.limb_result[2] = cols.lower_limb[2] * cols.v_0123 + cols.higher_limb[1]) ∧
  (cols.limb_result[3] = cols.lower_limb[3] * cols.v_0123 + cols.higher_limb[2]) ∧
  -- 16 SLL gated output equations (4 limbs × 4 shift_u16 cases)
  (cols.is_sll = 0 ∨ cols.shift_u16[0] = 0 ∨ cols.result[0] = cols.limb_result[0]) ∧
  (cols.is_sll = 0 ∨ cols.shift_u16[0] = 0 ∨ cols.result[1] = cols.limb_result[1]) ∧
  (cols.is_sll = 0 ∨ cols.shift_u16[0] = 0 ∨ cols.result[2] = cols.limb_result[2]) ∧
  (cols.is_sll = 0 ∨ cols.shift_u16[0] = 0 ∨ cols.result[3] = cols.limb_result[3]) ∧
  (cols.is_sll = 0 ∨ cols.shift_u16[1] = 0 ∨ cols.result[0] = 0) ∧
  (cols.is_sll = 0 ∨ cols.shift_u16[1] = 0 ∨ cols.result[1] = cols.limb_result[0]) ∧
  (cols.is_sll = 0 ∨ cols.shift_u16[1] = 0 ∨ cols.result[2] = cols.limb_result[1]) ∧
  (cols.is_sll = 0 ∨ cols.shift_u16[1] = 0 ∨ cols.result[3] = cols.limb_result[2]) ∧
  (cols.is_sll = 0 ∨ cols.shift_u16[2] = 0 ∨ cols.result[0] = 0) ∧
  (cols.is_sll = 0 ∨ cols.shift_u16[2] = 0 ∨ cols.result[1] = 0) ∧
  (cols.is_sll = 0 ∨ cols.shift_u16[2] = 0 ∨ cols.result[2] = cols.limb_result[0]) ∧
  (cols.is_sll = 0 ∨ cols.shift_u16[2] = 0 ∨ cols.result[3] = cols.limb_result[1]) ∧
  (cols.is_sll = 0 ∨ cols.shift_u16[3] = 0 ∨ cols.result[0] = 0) ∧
  (cols.is_sll = 0 ∨ cols.shift_u16[3] = 0 ∨ cols.result[1] = 0) ∧
  (cols.is_sll = 0 ∨ cols.shift_u16[3] = 0 ∨ cols.result[2] = 0) ∧
  (cols.is_sll = 0 ∨ cols.shift_u16[3] = 0 ∨ cols.result[3] = cols.limb_result[0]) ∧
  -- 4 SLLW gated output equations (shift_u16[0..1] cases × 2 low limbs)
  (cols.is_sllw = 0 ∨ cols.shift_u16[0] = 0 ∨ cols.result[0] = cols.limb_result[0]) ∧
  (cols.is_sllw = 0 ∨ cols.shift_u16[0] = 0 ∨ cols.result[1] = cols.limb_result[1]) ∧
  (cols.is_sllw = 0 ∨ cols.shift_u16[1] = 0 ∨ cols.result[0] = 0) ∧
  (cols.is_sllw = 0 ∨ cols.shift_u16[1] = 0 ∨ cols.result[1] = cols.limb_result[0]) ∧
  -- SLLW sign extension: high two limbs = sllw_msb * 0xFFFF
  (cols.is_sllw = 0 ∨ cols.sllw_msb.msb * 65535 = cols.result[2]) ∧
  (cols.is_sllw = 0 ∨ cols.sllw_msb.msb * 65535 = cols.result[3]) ∧
  -- is_sllw_imm = is_sllw * imm_c
  cols.is_sllw_imm = cols.is_sllw * cols.adapter.imm_c

/-- The Clean-flavored Spec for `ShiftLeftChip`. Composes the existing
per-fragment specs with three memory access records (op_a, op_b, op_c),
the program-bus consequence, the boolean gates, and the placeholder
shift content. -/
def TraceSpec (cols : ShiftLeftCols (ZMod p)) : Prop :=
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
    (SP1Clean.MemoryAccess.ofRegisterShared cols.adapter.op_c[0]
      { prev_value := cols.adapter.op_c_memory.prev_value,
        access_timestamp :=
          { prev_low := cols.adapter.op_c_memory.access_timestamp.prev_low,
            diff_low_limb := cols.adapter.op_c_memory.access_timestamp.diff_low_limb } }) ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc,
      opcode := cols.is_sll * 8 + cols.is_sllw * 14,
      op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0],
      op_c := cols.adapter.op_c,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := cols.adapter.imm_c } ∧
  -- 6 + 4 + 2 + 1 = 13 boolean gates.
  cols.c_bits[0] * (cols.c_bits[0] - 1) = 0 ∧
  cols.c_bits[1] * (cols.c_bits[1] - 1) = 0 ∧
  cols.c_bits[2] * (cols.c_bits[2] - 1) = 0 ∧
  cols.c_bits[3] * (cols.c_bits[3] - 1) = 0 ∧
  cols.c_bits[4] * (cols.c_bits[4] - 1) = 0 ∧
  cols.c_bits[5] * (cols.c_bits[5] - 1) = 0 ∧
  cols.shift_u16[0] * (cols.shift_u16[0] - 1) = 0 ∧
  cols.shift_u16[1] * (cols.shift_u16[1] - 1) = 0 ∧
  cols.shift_u16[2] * (cols.shift_u16[2] - 1) = 0 ∧
  cols.shift_u16[3] * (cols.shift_u16[3] - 1) = 0 ∧
  cols.is_sll * (cols.is_sll - 1) = 0 ∧
  cols.is_sllw * (cols.is_sllw - 1) = 0 ∧
  (cols.is_sll + cols.is_sllw) * (cols.is_sll + cols.is_sllw - 1) = 0 ∧
  cols.adapter.op_a_0 = 0 ∧
  shiftSpec cols ∧
  cols.adapter_cols.is_trusted = 1

set_option maxHeartbeats 2400000 in
-- Heartbeats elevated for the ~65-conjunct iff RHS refine on 65 cols.
/-- The chip-level half-iff bridge (ShiftLeft). -/
theorem traceSpec_implies_allHold (Main : Vector (ZMod p) 65)
    (h_is_real : Main[62] + Main[63] = 1)
    (h_spec : TraceSpec (fromMain Main)) :
    (_root_.ShiftLeft.constraints Main).allHold := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [TraceSpec, fromMain, shiftSpec,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ] at h_spec
  change List.Forall SP1Constraint.toProp (_root_.ShiftLeft.constraints Main)
  rw [_root_.ShiftLeft.allHold_constraints_iff]
  obtain ⟨h_cpu_spec, _h_mem_a, _h_mem_b, _h_mem_c, _h_program,
          h_cb0, h_cb1, h_cb2, h_cb3, h_cb4, h_cb5,
          h_su0, h_su1, h_su2, h_su3,
          h_sll_bin, h_sllw_bin, h_aggregate, _h_op_a_0,
          h_ss, _h_trusted⟩ := h_spec
  obtain ⟨h_u16msb, h_alu, h_exp_bound,
          h_su0g, h_su1g, h_su2g, h_su3g, h_su_one_hot,
          h_v01, h_v012, h_v0123,
          h_lo0_b, h_hi0_b, h_li0,
          h_lo1_b, h_hi1_b, h_li1,
          h_lo2_b, h_hi2_b, h_li2,
          h_lo3_b, h_hi3_b, h_li3,
          h_lr0, h_lr1, h_lr2, h_lr3,
          h_sll00, h_sll01, h_sll02, h_sll03,
          h_sll10, h_sll11, h_sll12, h_sll13,
          h_sll20, h_sll21, h_sll22, h_sll23,
          h_sll30, h_sll31, h_sll32, h_sll33,
          h_sllw00, h_sllw01, h_sllw10, h_sllw11,
          h_sllw_se0, h_sllw_se1, h_sllw_imm⟩ := h_ss
  -- Boolean conversion helper: `x * (x - 1) = 0 ↔ x = 0 ∨ x = 1`.
  have bool_of : ∀ {x : ZMod p}, x * (x - 1) = 0 → x = 0 ∨ x = 1 := fun h =>
    (mul_eq_zero.mp h).imp_right (by intro h'; linear_combination h')
  have h_cb0' := bool_of h_cb0
  have h_cb1' := bool_of h_cb1
  have h_cb2' := bool_of h_cb2
  have h_cb3' := bool_of h_cb3
  have h_cb4' := bool_of h_cb4
  have h_cb5' := bool_of h_cb5
  have h_su0' := bool_of h_su0
  have h_su1' := bool_of h_su1
  have h_su2' := bool_of h_su2
  have h_su3' := bool_of h_su3
  have h_sll' := bool_of h_sll_bin
  have h_sllw' := bool_of h_sllw_bin
  have h_aggregate' := bool_of h_aggregate
  refine ⟨h_u16msb, ?_, h_alu, h_aggregate', h_sll', h_sllw',
          h_cb0', h_cb1', h_cb2', h_cb3', h_cb4', h_cb5',
          h_exp_bound,
          h_su0g, h_su0', h_su1g, h_su1', h_su2g, h_su2', h_su3g, h_su3',
          h_su_one_hot, h_v01, h_v012, h_v0123,
          h_lo0_b, h_hi0_b, h_li0,
          h_lo1_b, h_hi1_b, h_li1,
          h_lo2_b, h_hi2_b, h_li2,
          h_lo3_b, h_hi3_b, h_li3,
          h_lr0, h_lr1, h_lr2, h_lr3,
          h_sll00, h_sll01, h_sll02, h_sll03,
          h_sll10, h_sll11, h_sll12, h_sll13,
          h_sll20, h_sll21, h_sll22, h_sll23,
          h_sll30, h_sll31, h_sll32, h_sll33,
          h_sllw00, h_sllw01, h_sllw10, h_sllw11,
          h_sllw_se0, h_sllw_se1, h_sllw_imm, _h_op_a_0⟩
  -- 2: CPUState bridge via cpuStateSpec_iff_sp1 (after rw is_real_sum = 1).
  rw [show (Main[62] + Main[63] : ZMod p) = 1 from h_is_real]
  exact (SP1Clean.CPUState.cpuStateSpec_iff_sp1).mpr h_cpu_spec

/-- Clean-side `correct_sll`: R-type left shift. -/
theorem correct_sll
    (Main : Vector (ZMod p) 65) (s : SailState)
    (h_is_sll : Main[62] = 1) (h_imm_c : Main[31] = 0)
    (h_sllw_zero : Main[63] = 0)
    (h_spec : TraceSpec (fromMain Main))
    (state_cstrs : (_root_.ShiftLeft.constraints Main).initialState s) :
    let op_c := _root_.ShiftLeft.sp1_op_c Main
    let op_b := _root_.ShiftLeft.sp1_op_b Main
    let op_a := _root_.ShiftLeft.sp1_op_a Main
    (_root_.Sll.Poly.spec_sll (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.ShiftLeft.sp1_shift_left Main).run s :=
  _root_.Sll.Poly.correct_sll Main s
    (traceSpec_implies_allHold Main (by rw [h_is_sll, h_sllw_zero]; ring) h_spec)
    ⟨h_is_sll, h_imm_c⟩ state_cstrs

/-! ## Full `FormalAssertion` promotion (Path-2 — trimmed)

`Assertion.main` drops the 10 Vector-indexed boolean gates (6 for
`c_bits`, 4 for `shift_u16`) that the chip's `main` emits. Those
gates are internal to the shift-arithmetic operation and would trip
the documented Path-1 friction (`Vector.map (eval env) input_var_X =
input_X` doesn't reduce per-element under `circuit_proof_start`). They
stay in the legacy `Spec` via `shiftSpec` placeholder and are consumed
through the chip-level pipeline, not the trace-level FormalAssertion.

Assertion.main keeps: `CPUState` + `ProgramTable` + 2 opcode boolean
gates + aggregate sum + `op_a_0 = 0` = 6 conjuncts. -/

namespace Assertion

open Circuit

@[reducible]
def main (cols : Var ShiftLeftCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c, op_c_memory, imm_c⟩,
       _result,
       _c_bits, _v_01, _v_012, _v_0123, _shift_u16, _lower_limb, _higher_limb,
       _limb_result, _sllw_msb, is_sll, is_sllw, _is_sllw_imm,
       _adapter_cols⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ProgramTable.assertion
    (⟨pc, is_sll * 8 + is_sllw * 14,
      op_a, #v[op_b, 0, 0, 0], op_c,
      op_a_0, 0, imm_c⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  is_sll * (is_sll - 1) === 0
  is_sllw * (is_sllw - 1) === 0
  (is_sll + is_sllw) * (is_sll + is_sllw - 1) === 0
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
-- Higher heartbeats: 31 input fields + 4 subcircuit calls + 3 OperandAccess
-- calls pushes localLength_eq synthesis past the default 200k cap.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) ShiftLeftCols unit where
  name := "SP1Clean.ShiftLeft"
  main := main
  localLength _ := 0

def Assumptions (_ : ShiftLeftCols (ZMod p)) : Prop := True

def FormalSpec (cols : ShiftLeftCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := cols.is_sll * 8 + cols.is_sllw * 14,
      op_a := cols.adapter.op_a, op_b := #v[cols.adapter.op_b, 0, 0, 0],
      op_c := cols.adapter.op_c,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := cols.adapter.imm_c } ∧
  cols.is_sll * (cols.is_sll - 1) = 0 ∧
  cols.is_sllw * (cols.is_sllw - 1) = 0 ∧
  (cols.is_sll + cols.is_sllw) * (cols.is_sll + cols.is_sllw - 1) = 0 ∧
  cols.adapter.op_a_0 = 0 ∧
  -- Iter-8 sub-task E: per-operand memory-bus byte-content consequences.
  -- R-type: op_a/+4, op_b/+3, op_c/+2.
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 4, cols.adapter.op_a_memory.access_timestamp.prev_low,
     cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 3, cols.adapter.op_b_memory.access_timestamp.prev_low,
     cols.adapter.op_b_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_b_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 2, cols.adapter.op_c_memory.access_timestamp.prev_low,
     cols.adapter.op_c_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_c_memory.prev_value⟩

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30,
          e31⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu_sub, h_prog_sub, h_sll, h_sllw, h_sum,
          h_op_a_0, h_oa_a, h_oa_b, h_oa_c⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_prog_sub trivial
  · linear_combination h_sll
  · linear_combination h_sllw
  · linear_combination h_sum
  · exact h_op_a_0
  · exact h_oa_a trivial
  · exact h_oa_b trivial
  · exact h_oa_c trivial

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30,
          e31⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu, h_prog, h_sll, h_sllw, h_sum, h_op_a_0,
          h_oa_a, h_oa_b, h_oa_c⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_prog⟩
  · linear_combination h_sll
  · linear_combination h_sllw
  · linear_combination h_sum
  · exact h_op_a_0
  · exact ⟨trivial, h_oa_a⟩
  · exact ⟨trivial, h_oa_b⟩
  · exact ⟨trivial, h_oa_c⟩

end Assertion

def assertion : FormalAssertion (ZMod p) ShiftLeftCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.ShiftLeft
