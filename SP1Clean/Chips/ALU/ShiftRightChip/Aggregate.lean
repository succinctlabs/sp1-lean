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
import SP1Chips.ShiftRight.ShiftRightChip
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.OperandAccess
import SP1Clean.Reader.CPUState
import SP1Clean.TrustMode
import SP1Clean.Chips.Structs
import SP1Clean.Chips.Spec

/-! # Chip-level `ShiftRightChip` mirror — bundled 4-variant right shift

The ShiftRight chip bundles four RV64IM right-shift variants
(`srl`/`sra`/`srlw`/`sraw`) into a single 69-column trace, distinguished
by selectors at `Main[64..67]`. Same structural-mirror discipline as
`ShiftLeftChip`: shift-arithmetic content (bit-decomposition correctness,
shift power chain, byte-shift one-hot, limb-shift) is captured as a
placeholder `shiftSpec` (currently `True`).

Opcode encoding: SRL=7, SRA=8, SRLW=22, SRAW=23.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.ShiftRight

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def isRealExpr (cols : Var ShiftRightCols (ZMod p)) : Expression (ZMod p) :=
  cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw

/-- Selector-weighted opcode: SRL=7, SRA=8, SRLW=22, SRAW=23. -/
def opcodeExpr (cols : Var ShiftRightCols (ZMod p)) : Expression (ZMod p) :=
  cols.is_srl * 7 + cols.is_sra * 8 + cols.is_srlw * 22 + cols.is_sraw * 23

def main (cols : Var ShiftRightCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, _op_a_memory, op_a_0, op_b, _op_b_memory, op_c, _op_c_memory, imm_c⟩,
       _op_a_write_value,
       _b_msb, _srw_msb, _c_bits, _sra_msb_v0123, _v_0123, _v_012, _v_01,
       _lower_limb, _higher_limb, _limb_result, _shift_u16,
       is_srl, is_sra, is_srlw, is_sraw, _is_w_imm,
       _adapter_cols⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  let opcode_e := is_srl * 7 + is_sra * 8 + is_srlw * 22 + is_sraw * 23
  SP1Clean.ProgramTable.assertion
    (⟨pc, opcode_e, op_a, #v[op_b, 0, 0, 0], op_c,
      op_a_0, 0, imm_c⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  is_srl * (is_srl - 1) === 0
  is_sra * (is_sra - 1) === 0
  is_srlw * (is_srlw - 1) === 0
  is_sraw * (is_sraw - 1) === 0
  let sum := is_srl + is_sra + is_srlw + is_sraw
  sum * (sum - 1) === 0
  op_a_0 === 0

/-- The shift-arithmetic Spec content for ShiftRight. Bundles the iff-RHS
conjuncts of `_root_.ShiftRight.allHold_constraints_iff` that aren't otherwise
carried by the chip-level Spec. Includes 3 `U16MSBOperation` sub-allHolds (one
each for SRA on op_b high limb, SRAW on op_b mid limb, and SRLW/SRAW on result
high limb), the raw `ALUTypeReader` sub-allHold, the is_w_imm derivation, the
c_bits and shift_u16 boolean gates (not in Spec), the shift-exponent bound,
the shift-power chain (uses `1 - c_bit_i`, the inverse-form for right-shift),
per-limb shift bounds + identities (with `(is_srl + is_sra)` factor on high
limbs for SRA propagation), 4 limb_result equations, `sra_msb_v0123`
intermediate, and 22 gated output equations (16 for srl+sra × 4 shift_u16, 6
for srlw+sraw shift_u16 arms). -/
def shiftSpec (cols : ShiftRightCols (ZMod p)) : Prop :=
  -- 3 U16MSBOperation sub-allHolds.
  (_root_.U16MSBOperation.constraints cols.adapter.op_b_memory.prev_value[3]
      cols.b_msb cols.is_sra).allHold ∧
  (_root_.U16MSBOperation.constraints cols.adapter.op_b_memory.prev_value[1]
      cols.b_msb cols.is_sraw).allHold ∧
  (_root_.U16MSBOperation.constraints cols.op_a_write_value[1]
      cols.srw_msb (cols.is_srlw + cols.is_sraw)).allHold ∧
  -- ALUTypeReader.constraints.allHold (raw form, with chip args).
  (_root_.ALUTypeReader.constraints cols.state.clk_high
      (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) cols.state.pc
      (cols.is_srl * 7 + cols.is_sra * 8 + cols.is_srlw * 22 + cols.is_sraw * 23)
      cols.op_a_write_value cols.adapter
      (cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw)
      (cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw)).allHold ∧
  -- is_w_imm = (is_srlw + is_sraw) * imm_c
  cols.is_w_imm = (cols.is_srlw + cols.is_sraw) * cols.adapter.imm_c ∧
  -- 6 c_bits booleans
  (cols.c_bits[0] = 0 ∨ cols.c_bits[0] = 1) ∧
  (cols.c_bits[1] = 0 ∨ cols.c_bits[1] = 1) ∧
  (cols.c_bits[2] = 0 ∨ cols.c_bits[2] = 1) ∧
  (cols.c_bits[3] = 0 ∨ cols.c_bits[3] = 1) ∧
  (cols.c_bits[4] = 0 ∨ cols.c_bits[4] = 1) ∧
  (cols.c_bits[5] = 0 ∨ cols.c_bits[5] = 1) ∧
  -- shift-exponent bound
  (¬ cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw = 0 →
    ((cols.adapter.op_c_memory.prev_value[0] - (cols.c_bits[0] + cols.c_bits[1] * 2 +
        cols.c_bits[2] * 4 + cols.c_bits[3] * 8 + cols.c_bits[4] * 16 +
        cols.c_bits[5] * 32)) * ((64 : ZMod p)⁻¹)).val < 2 ^ (10 : ZMod p).val) ∧
  -- 4 shift_u16 byte-offset gates + booleans (interleaved)
  (cols.shift_u16[0] = 0 ∨ cols.c_bits[4] + cols.c_bits[5] * 2 *
      (cols.is_srl + cols.is_sra) = 0) ∧
  (cols.shift_u16[0] = 0 ∨ cols.shift_u16[0] = 1) ∧
  (cols.shift_u16[1] = 0 ∨ cols.c_bits[4] + cols.c_bits[5] * 2 *
      (cols.is_srl + cols.is_sra) = 1) ∧
  (cols.shift_u16[1] = 0 ∨ cols.shift_u16[1] = 1) ∧
  (cols.shift_u16[2] = 0 ∨ cols.c_bits[4] + cols.c_bits[5] * 2 *
      (cols.is_srl + cols.is_sra) = 2) ∧
  (cols.shift_u16[2] = 0 ∨ cols.shift_u16[2] = 1) ∧
  (cols.shift_u16[3] = 0 ∨ cols.c_bits[4] + cols.c_bits[5] * 2 *
      (cols.is_srl + cols.is_sra) = 3) ∧
  (cols.shift_u16[3] = 0 ∨ cols.shift_u16[3] = 1) ∧
  -- shift_u16 one-hot under is_real
  (cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw = 0 ∨
    cols.shift_u16[0] + cols.shift_u16[1] + cols.shift_u16[2] + cols.shift_u16[3] = 1) ∧
  -- shift-power chain (inverse: uses (1 - cb_i))
  (cols.v_01 = (1 - cols.c_bits[0] + 1) * 2 * ((1 - cols.c_bits[1]) * 3 + 1)) ∧
  (cols.v_012 = cols.v_01 * ((1 - cols.c_bits[2]) * 15 + 1)) ∧
  (cols.v_0123 = cols.v_012 * ((1 - cols.c_bits[3]) * 255 + 1)) ∧
  -- per-limb shift bounds + identities (4 sets for Main[15..18])
  -- Limb 0: standard
  (¬ cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw = 0 →
    (cols.lower_limb[0]).val < 2 ^ (cols.c_bits[0] + cols.c_bits[1] * 2 +
        cols.c_bits[2] * 4 + cols.c_bits[3] * 8 : ZMod p).val) ∧
  (¬ cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw = 0 →
    (cols.higher_limb[0]).val < 2 ^ ((16 : ZMod p) - (cols.c_bits[0] +
        cols.c_bits[1] * 2 + cols.c_bits[2] * 4 + cols.c_bits[3] * 8)).val) ∧
  (cols.adapter.op_b_memory.prev_value[0] * cols.v_0123 =
    cols.higher_limb[0] * 65536 + cols.lower_limb[0] * cols.v_0123) ∧
  -- Limb 1
  (¬ cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw = 0 →
    (cols.lower_limb[1]).val < 2 ^ (cols.c_bits[0] + cols.c_bits[1] * 2 +
        cols.c_bits[2] * 4 + cols.c_bits[3] * 8 : ZMod p).val) ∧
  (¬ cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw = 0 →
    (cols.higher_limb[1]).val < 2 ^ ((16 : ZMod p) - (cols.c_bits[0] +
        cols.c_bits[1] * 2 + cols.c_bits[2] * 4 + cols.c_bits[3] * 8)).val) ∧
  (cols.adapter.op_b_memory.prev_value[1] * cols.v_0123 =
    cols.higher_limb[1] * 65536 + cols.lower_limb[1] * cols.v_0123) ∧
  -- Limb 2: gated by (is_srl + is_sra) — for SRA-style: high limb propagates
  (¬ cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw = 0 →
    (cols.lower_limb[2]).val < 2 ^ (cols.c_bits[0] + cols.c_bits[1] * 2 +
        cols.c_bits[2] * 4 + cols.c_bits[3] * 8 : ZMod p).val) ∧
  (¬ cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw = 0 →
    (cols.higher_limb[2]).val < 2 ^ ((16 : ZMod p) - (cols.c_bits[0] +
        cols.c_bits[1] * 2 + cols.c_bits[2] * 4 + cols.c_bits[3] * 8)).val) ∧
  (cols.adapter.op_b_memory.prev_value[2] * cols.v_0123 * (cols.is_srl + cols.is_sra) =
    cols.higher_limb[2] * 65536 + cols.lower_limb[2] * cols.v_0123) ∧
  -- Limb 3
  (¬ cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw = 0 →
    (cols.lower_limb[3]).val < 2 ^ (cols.c_bits[0] + cols.c_bits[1] * 2 +
        cols.c_bits[2] * 4 + cols.c_bits[3] * 8 : ZMod p).val) ∧
  (¬ cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw = 0 →
    (cols.higher_limb[3]).val < 2 ^ ((16 : ZMod p) - (cols.c_bits[0] +
        cols.c_bits[1] * 2 + cols.c_bits[2] * 4 + cols.c_bits[3] * 8)).val) ∧
  (cols.adapter.op_b_memory.prev_value[3] * cols.v_0123 * (cols.is_srl + cols.is_sra) =
    cols.higher_limb[3] * 65536 + cols.lower_limb[3] * cols.v_0123) ∧
  -- 4 limb_result equations
  (cols.limb_result[0] = cols.higher_limb[0] + cols.lower_limb[1] * cols.v_0123) ∧
  (cols.limb_result[1] = cols.higher_limb[1] + cols.lower_limb[2] * cols.v_0123) ∧
  (cols.limb_result[2] = cols.higher_limb[2] + cols.lower_limb[3] * cols.v_0123) ∧
  (cols.limb_result[3] = cols.higher_limb[3]) ∧
  -- b_msb gating: srl + srlw → b_msb = 0 (no sign extension)
  (cols.is_srl + cols.is_srlw = 0 ∨ cols.b_msb.msb = 0) ∧
  -- sra_msb_v0123 = b_msb * v_0123
  (cols.sra_msb_v0123 = cols.b_msb.msb * cols.v_0123) ∧
  -- srw_msb gating: not (srlw + sraw) → srw_msb = 0  (lit form: srlw+sraw = 1 ∨ srw_msb = 0)
  (cols.is_srlw + cols.is_sraw = 1 ∨ cols.srw_msb.msb = 0) ∧
  -- 16 SR (srl/sra) gated output equations: gated by (is_srl + is_sra) × shift_u16
  (cols.is_srl + cols.is_sra = 0 ∨ cols.shift_u16[0] = 0 ∨
    cols.op_a_write_value[0] = cols.limb_result[0]) ∧
  (cols.is_srl + cols.is_sra = 0 ∨ cols.shift_u16[0] = 0 ∨
    cols.op_a_write_value[1] = cols.limb_result[1]) ∧
  (cols.is_srl + cols.is_sra = 0 ∨ cols.shift_u16[0] = 0 ∨
    cols.op_a_write_value[2] = cols.limb_result[2]) ∧
  (cols.is_srl + cols.is_sra = 0 ∨ cols.shift_u16[0] = 0 ∨
    cols.op_a_write_value[3] = cols.limb_result[3] +
      (cols.b_msb.msb * 65536 - cols.sra_msb_v0123)) ∧
  (cols.is_srl + cols.is_sra = 0 ∨ cols.shift_u16[1] = 0 ∨
    cols.op_a_write_value[0] = cols.limb_result[1]) ∧
  (cols.is_srl + cols.is_sra = 0 ∨ cols.shift_u16[1] = 0 ∨
    cols.op_a_write_value[1] = cols.limb_result[2]) ∧
  (cols.is_srl + cols.is_sra = 0 ∨ cols.shift_u16[1] = 0 ∨
    cols.op_a_write_value[2] = cols.limb_result[3] +
      (cols.b_msb.msb * 65536 - cols.sra_msb_v0123)) ∧
  (cols.is_srl + cols.is_sra = 0 ∨ cols.shift_u16[1] = 0 ∨
    cols.op_a_write_value[3] = cols.b_msb.msb * 65535) ∧
  (cols.is_srl + cols.is_sra = 0 ∨ cols.shift_u16[2] = 0 ∨
    cols.op_a_write_value[0] = cols.limb_result[2]) ∧
  (cols.is_srl + cols.is_sra = 0 ∨ cols.shift_u16[2] = 0 ∨
    cols.op_a_write_value[1] = cols.limb_result[3] +
      (cols.b_msb.msb * 65536 - cols.sra_msb_v0123)) ∧
  (cols.is_srl + cols.is_sra = 0 ∨ cols.shift_u16[2] = 0 ∨
    cols.op_a_write_value[2] = cols.b_msb.msb * 65535) ∧
  (cols.is_srl + cols.is_sra = 0 ∨ cols.shift_u16[2] = 0 ∨
    cols.op_a_write_value[3] = cols.b_msb.msb * 65535) ∧
  (cols.is_srl + cols.is_sra = 0 ∨ cols.shift_u16[3] = 0 ∨
    cols.op_a_write_value[0] = cols.limb_result[3] +
      (cols.b_msb.msb * 65536 - cols.sra_msb_v0123)) ∧
  (cols.is_srl + cols.is_sra = 0 ∨ cols.shift_u16[3] = 0 ∨
    cols.op_a_write_value[1] = cols.b_msb.msb * 65535) ∧
  (cols.is_srl + cols.is_sra = 0 ∨ cols.shift_u16[3] = 0 ∨
    cols.op_a_write_value[2] = cols.b_msb.msb * 65535) ∧
  (cols.is_srl + cols.is_sra = 0 ∨ cols.shift_u16[3] = 0 ∨
    cols.op_a_write_value[3] = cols.b_msb.msb * 65535) ∧
  -- 6 srlw/sraw gated output equations
  (cols.is_srlw + cols.is_sraw = 0 ∨ cols.shift_u16[0] = 0 ∨
    cols.op_a_write_value[0] = cols.limb_result[0]) ∧
  (cols.is_srlw + cols.is_sraw = 0 ∨ cols.shift_u16[0] = 0 ∨
    cols.op_a_write_value[1] = cols.limb_result[1] +
      (cols.b_msb.msb * 65536 - cols.sra_msb_v0123)) ∧
  (cols.is_srlw + cols.is_sraw = 0 ∨ cols.shift_u16[1] = 0 ∨
    cols.op_a_write_value[0] = cols.limb_result[1] +
      (cols.b_msb.msb * 65536 - cols.sra_msb_v0123)) ∧
  (cols.is_srlw + cols.is_sraw = 0 ∨ cols.shift_u16[1] = 0 ∨
    cols.op_a_write_value[1] = cols.b_msb.msb * 65535) ∧
  (cols.is_srlw + cols.is_sraw = 0 ∨ cols.op_a_write_value[2] = cols.srw_msb.msb * 65535) ∧
  (cols.is_srlw + cols.is_sraw = 0 ∨ cols.op_a_write_value[3] = cols.srw_msb.msb * 65535)

def TraceSpec (cols : ShiftRightCols (ZMod p)) : Prop :=
  let is_real : ZMod p :=
    cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw
  let opcode_e : ZMod p :=
    cols.is_srl * 7 + cols.is_sra * 8 + cols.is_srlw * 22 + cols.is_sraw * 23
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
    { pc := cols.state.pc, opcode := opcode_e,
      op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0],
      op_c := cols.adapter.op_c,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := cols.adapter.imm_c } ∧
  cols.is_srl * (cols.is_srl - 1) = 0 ∧
  cols.is_sra * (cols.is_sra - 1) = 0 ∧
  cols.is_srlw * (cols.is_srlw - 1) = 0 ∧
  cols.is_sraw * (cols.is_sraw - 1) = 0 ∧
  is_real * (is_real - 1) = 0 ∧
  cols.adapter.op_a_0 = 0 ∧
  shiftSpec cols ∧
  cols.adapter_cols.is_trusted = 1

set_option maxHeartbeats 4000000 in
-- Heartbeats elevated for the ~75-conjunct iff RHS refine on 69 cols.
/-- The chip-level half-iff bridge (ShiftRight). -/
theorem traceSpec_implies_allHold (Main : Vector (ZMod p) 69)
    (h_is_real : Main[64] + Main[65] + Main[66] + Main[67] = 1)
    (h_spec : TraceSpec (fromMain Main)) :
    (_root_.ShiftRight.constraints Main).allHold := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [TraceSpec, fromMain, shiftSpec,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ] at h_spec
  obtain ⟨h_cpu_spec, _h_mem_a, _h_mem_b, _h_mem_c, _h_program,
          h_srl_bin, h_sra_bin, h_srlw_bin, h_sraw_bin, h_aggregate,
          _h_a0, h_ss, _h_trusted⟩ := h_spec
  obtain ⟨h_u16a, h_u16b, h_u16c, h_alu, h_iswi,
          h_cb0, h_cb1, h_cb2, h_cb3, h_cb4, h_cb5,
          h_exp_bound,
          h_su0g, h_su0, h_su1g, h_su1, h_su2g, h_su2, h_su3g, h_su3,
          h_su_one_hot,
          h_v01, h_v012, h_v0123,
          h_lo0_b, h_hi0_b, h_li0,
          h_lo1_b, h_hi1_b, h_li1,
          h_lo2_b, h_hi2_b, h_li2,
          h_lo3_b, h_hi3_b, h_li3,
          h_lr0, h_lr1, h_lr2, h_lr3,
          h_bmsb_gate, h_sra_msb_eq, h_srwmsb_gate,
          h_srl_sra00, h_srl_sra01, h_srl_sra02, h_srl_sra03,
          h_srl_sra10, h_srl_sra11, h_srl_sra12, h_srl_sra13,
          h_srl_sra20, h_srl_sra21, h_srl_sra22, h_srl_sra23,
          h_srl_sra30, h_srl_sra31, h_srl_sra32, h_srl_sra33,
          h_srlw_sraw00, h_srlw_sraw01,
          h_srlw_sraw10, h_srlw_sraw11,
          h_srlw_sraw_high2, h_srlw_sraw_high3⟩ := h_ss
  change List.Forall SP1Constraint.toProp (_root_.ShiftRight.constraints Main)
  rw [_root_.ShiftRight.allHold_constraints_iff]
  -- Boolean conversion helper
  have bool_of : ∀ {x : ZMod p}, x * (x - 1) = 0 → x = 0 ∨ x = 1 := fun h =>
    (mul_eq_zero.mp h).imp_right (by intro h'; linear_combination h')
  -- iff RHS order: 3 U16MSB + CPUState + ALUTypeReader + 4 opcode bool + aggregate bool
  -- + is_w_imm + 6 c_bits bool + exp_bound + 8 shift_u16 (gate+bool interleaved) + one_hot
  -- + 3 shift-power + 12 per-limb + 4 limb_result + 4 special (b_msb_gate, sra_msb_eq, srw_gate)
  -- + 16 srl/sra gated + 6 srlw/sraw gated + Main[13] = 0
  refine ⟨h_u16a, h_u16b, h_u16c, ?_, h_alu,
          bool_of h_srl_bin, bool_of h_sra_bin, bool_of h_srlw_bin, bool_of h_sraw_bin,
          bool_of h_aggregate, h_iswi,
          h_cb0, h_cb1, h_cb2, h_cb3, h_cb4, h_cb5,
          h_exp_bound,
          h_su0g, h_su0, h_su1g, h_su1, h_su2g, h_su2, h_su3g, h_su3, h_su_one_hot,
          h_v01, h_v012, h_v0123,
          h_lo0_b, h_hi0_b, h_li0,
          h_lo1_b, h_hi1_b, h_li1,
          h_lo2_b, h_hi2_b, h_li2,
          h_lo3_b, h_hi3_b, h_li3,
          h_lr0, h_lr1, h_lr2, h_lr3,
          h_bmsb_gate, h_sra_msb_eq, h_srwmsb_gate,
          h_srl_sra00, h_srl_sra01, h_srl_sra02, h_srl_sra03,
          h_srl_sra10, h_srl_sra11, h_srl_sra12, h_srl_sra13,
          h_srl_sra20, h_srl_sra21, h_srl_sra22, h_srl_sra23,
          h_srl_sra30, h_srl_sra31, h_srl_sra32, h_srl_sra33,
          h_srlw_sraw00, h_srlw_sraw01,
          h_srlw_sraw10, h_srlw_sraw11,
          h_srlw_sraw_high2, h_srlw_sraw_high3, _h_a0⟩
  -- CPUState bridge via cpuStateSpec_iff_sp1
  rw [show (Main[64] + Main[65] + Main[66] + Main[67] : ZMod p) = 1 from h_is_real]
  exact (SP1Clean.CPUState.cpuStateSpec_iff_sp1).mpr h_cpu_spec

/-- Clean-side `correct_srl`: R-type logical right shift. -/
theorem correct_srl
    (Main : Vector (ZMod p) 69) (s : SailState)
    (h_is_srl : Main[64] = 1) (h_imm_c : Main[31] = 0)
    (h_others_zero : Main[65] = 0 ∧ Main[66] = 0 ∧ Main[67] = 0)
    (h_spec : TraceSpec (fromMain Main))
    (state_cstrs : (_root_.ShiftRight.constraints Main).initialState s) :
    let op_c := _root_.ShiftRight.sp1_op_c Main
    let op_b := _root_.ShiftRight.sp1_op_b Main
    let op_a := _root_.ShiftRight.sp1_op_a Main
    (_root_.Srl.Poly.spec_srl (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.ShiftRight.sp1_shift_right Main).run s :=
  _root_.Srl.Poly.correct_srl Main s
    (traceSpec_implies_allHold Main
      (by obtain ⟨h65, h66, h67⟩ := h_others_zero
          rw [h_is_srl, h65, h66, h67]; ring)
      h_spec)
    ⟨h_is_srl, h_imm_c⟩ state_cstrs

/-! ## Full `FormalAssertion` promotion (Path-2)

`Assertion.main` is identical to the chip's `main` (no byte lookups to
drop here — `ShiftRight`'s `main` already only emits `CPUState`,
`ProgramTable`, and scalar boolean gates). The shift-arithmetic content
in `intermediates_aux` stays in legacy `Spec` (via `shiftSpec`
placeholder) and is deferred to the trace-level OfflineMemory bridge.
Memory-bus consistency is similarly deferred. -/

namespace Assertion

open Circuit

@[reducible]
def main (cols : Var ShiftRightCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c, op_c_memory, imm_c⟩,
       _op_a_write_value,
       _b_msb, _srw_msb, _c_bits, _sra_msb_v0123, _v_0123, _v_012, _v_01,
       _lower_limb, _higher_limb, _limb_result, _shift_u16,
       is_srl, is_sra, is_srlw, is_sraw, _is_w_imm,
       _adapter_cols⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  let opcode_e := is_srl * 7 + is_sra * 8 + is_srlw * 22 + is_sraw * 23
  SP1Clean.ProgramTable.assertion
    (⟨pc, opcode_e, op_a, #v[op_b, 0, 0, 0], op_c,
      op_a_0, 0, imm_c⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  is_srl * (is_srl - 1) === 0
  is_sra * (is_sra - 1) === 0
  is_srlw * (is_srlw - 1) === 0
  is_sraw * (is_sraw - 1) === 0
  let sum := is_srl + is_sra + is_srlw + is_sraw
  sum * (sum - 1) === 0
  op_a_0 === 0
  -- Iter-8 sub-task E: per-operand memory-bus byte content.
  -- R-type-shaped: op_a/+4, op_b/+3, op_c/+2.
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
-- Higher heartbeats: 26 input fields + 4 subcircuit calls + 3 OperandAccess
-- calls pushes localLength_eq synthesis past the default 200k cap.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) ShiftRightCols unit where
  name := "SP1Clean.ShiftRight"
  main := main
  localLength _ := 0

def Assumptions (_ : ShiftRightCols (ZMod p)) : Prop := True

-- TODO(Spec-canonical-2026-05-26): `FormalSpec` was rewritten to the
-- canonical (a) shape (CPUState.Gated + ALUTypeReader.Gated + scalar
-- gates + RV64.srl/sra/srlw/sraw semantic dispatch). The prior
-- 11-conjunct `refine` shape no longer matches the new Spec —
-- reconstruct via `CPUState.Gated.Assertion.Spec_iff_sp1` +
-- `ALUTypeReader.Gated.Assertion.Spec_iff_sp1` + the chip's 54-gate
-- inline shift correctness lemma (see `AddChip/Lemmas.lean` for the
-- canonical template).
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec :=
  sorry

-- TODO(Spec-canonical-2026-05-26): see `soundness` above.
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec :=
  sorry

end Assertion

def assertion : FormalAssertion (ZMod p) ShiftRightCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.ShiftRight
