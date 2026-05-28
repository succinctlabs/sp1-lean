import SP1Clean.Chips.ALU.ShiftLeftChip.Lemmas
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import SP1Foundations.ByteOpcode
import SP1Clean.ByteOpcodeTable
import SP1Clean.SP1Lookup
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ALUTypeReader
import SP1Clean.Operations.U16MSBOperation
import SP1Clean.MemoryAccess
import RISCV.Instructions

/-! # `ShiftLeftChip` Clean circuit + `FormalAssertion`

Path-2 main lifted from `Aggregate.lean`. Soundness/completeness
sorry'd pending an operation-level bridge (Shift operation is
inline-only — no separate module). -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.ShiftLeft

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

@[reducible]
def main (cols : Var ShiftLeftCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩, adapter, result,
       c_bits, v_01, v_012, v_0123, shift_u16,
       lower_limb, higher_limb, limb_result, sllw_msb,
       is_sll, is_sllw, is_sllw_imm, adapter_cols⟩ := cols
  -- Bind vector elements to named locals (lets the binop elaborator coerce
  -- numeral literals to `Expression (ZMod p)` — it does not anchor through `getElem`).
  let cb0 := c_bits[0]; let cb1 := c_bits[1]; let cb2 := c_bits[2]
  let cb3 := c_bits[3]; let cb4 := c_bits[4]; let cb5 := c_bits[5]
  let r0 := result[0]; let r1 := result[1]; let r2 := result[2]; let r3 := result[3]
  let s0 := shift_u16[0]; let s1 := shift_u16[1]; let s2 := shift_u16[2]; let s3 := shift_u16[3]
  let ll0 := lower_limb[0]; let ll1 := lower_limb[1]
  let ll2 := lower_limb[2]; let ll3 := lower_limb[3]
  let hl0 := higher_limb[0]; let hl1 := higher_limb[1]
  let hl2 := higher_limb[2]; let hl3 := higher_limb[3]
  let lr0 := limb_result[0]; let lr1 := limb_result[1]
  let lr2 := limb_result[2]; let lr3 := limb_result[3]
  let ob0 := adapter.op_b_memory.prev_value[0]; let ob1 := adapter.op_b_memory.prev_value[1]
  let ob2 := adapter.op_b_memory.prev_value[2]; let ob3 := adapter.op_b_memory.prev_value[3]
  let oc0 := adapter.op_c_memory.prev_value[0]
  let msb := sllw_msb.msb
  let sum : Expression (ZMod p) := is_sll + is_sllw
  let opcode_e : Expression (ZMod p) := is_sll * 6 + is_sllw * 21
  let clk_low : Expression (ZMod p) := clk_0_16 + clk_16_24 * 65536
  let c6 : Expression (ZMod p) := cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32
  let c4 : Expression (ZMod p) := cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8
  let sel : Expression (ZMod p) := cb4 + cb5 * 2 * is_sll
  -- U16MSB (inline faithful): unconditional msb-binary + gated Range-16.
  msb * (msb - 1) === 0
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), 2 * r1 - msb * 65536, 16, 0], is_sllw⟩ :
     Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  -- CPUState + ALUTypeReader (gated readers).
  SP1Clean.CPUState.Gated.assertion
    (⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩, #v[pc[0] + 4, pc[1], pc[2]], 8, sum⟩ :
      Var SP1Clean.CPUState.Gated.Inputs (ZMod p))
  SP1Clean.ALUTypeReader.Gated.assertion
    (⟨clk_high, clk_low, opcode_e, pc, result, adapter, sum, adapter_cols.is_trusted⟩ :
      Var SP1Clean.ALUTypeReader.Gated.Inputs (ZMod p))
  -- Selector binaries.
  sum * (sum - 1) === 0
  is_sll * (is_sll - 1) === 0
  is_sllw * (is_sllw - 1) === 0
  -- 6-bit shift decomposition binaries.
  cb0 * (cb0 - 1) === 0
  cb1 * (cb1 - 1) === 0
  cb2 * (cb2 - 1) === 0
  cb3 * (cb3 - 1) === 0
  cb4 * (cb4 - 1) === 0
  cb5 * (cb5 - 1) === 0
  -- Within-shift bound: (c - low6)·64⁻¹ < 2^10 (gated Range).
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), (oc0 - c6) * Expression.const (64 : ZMod p)⁻¹, 10, 0], sum⟩ :
     Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  -- 4-way byte-shift one-hot selector (product gates) + binaries + sum.
  s0 * sel === 0
  s0 * (s0 - 1) === 0
  s1 * (sel - 1) === 0
  s1 * (s1 - 1) === 0
  s2 * (sel - 2) === 0
  s2 * (s2 - 1) === 0
  s3 * (sel - 3) === 0
  s3 * (s3 - 1) === 0
  sum * (s0 + s1 + s2 + s3 - 1) === 0
  -- Shift-power chain.
  (v_01 - (cb0 + 1) * (cb1 * 3 + 1)) === 0
  (v_012 - v_01 * (cb2 * 15 + 1)) === 0
  (v_0123 - v_012 * (cb3 * 255 + 1)) === 0
  -- Per-limb shift decompositions + bounds (gated Range).
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), ll0, 16 - c4, 0], sum⟩ : Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), hl0, c4, 0], sum⟩ : Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  (ob0 * v_0123 - (hl0 * 65536 + ll0 * v_0123)) === 0
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), ll1, 16 - c4, 0], sum⟩ : Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), hl1, c4, 0], sum⟩ : Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  (ob1 * v_0123 - (hl1 * 65536 + ll1 * v_0123)) === 0
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), ll2, 16 - c4, 0], sum⟩ : Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), hl2, c4, 0], sum⟩ : Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  (ob2 * v_0123 - (hl2 * 65536 + ll2 * v_0123)) === 0
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), ll3, 16 - c4, 0], sum⟩ : Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), hl3, c4, 0], sum⟩ : Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  (ob3 * v_0123 - (hl3 * 65536 + ll3 * v_0123)) === 0
  -- limb_result wiring.
  (lr0 - ll0 * v_0123) === 0
  (lr1 - (ll1 * v_0123 + hl0)) === 0
  (lr2 - (ll2 * v_0123 + hl1)) === 0
  (lr3 - (ll3 * v_0123 + hl2)) === 0
  -- SLL output equations (16, gated by is_sll · shift_u16[k]).
  is_sll * (s0 * (r0 - lr0)) === 0
  is_sll * (s0 * (r1 - lr1)) === 0
  is_sll * (s0 * (r2 - lr2)) === 0
  is_sll * (s0 * (r3 - lr3)) === 0
  is_sll * (s1 * r0) === 0
  is_sll * (s1 * (r1 - lr0)) === 0
  is_sll * (s1 * (r2 - lr1)) === 0
  is_sll * (s1 * (r3 - lr2)) === 0
  is_sll * (s2 * r0) === 0
  is_sll * (s2 * r1) === 0
  is_sll * (s2 * (r2 - lr0)) === 0
  is_sll * (s2 * (r3 - lr1)) === 0
  is_sll * (s3 * r0) === 0
  is_sll * (s3 * r1) === 0
  is_sll * (s3 * r2) === 0
  is_sll * (s3 * (r3 - lr0)) === 0
  -- SLLW output equations (6, gated by is_sllw · shift_u16[k]; sign-extend high limbs).
  is_sllw * (s0 * (r0 - lr0)) === 0
  is_sllw * (s0 * (r1 - lr1)) === 0
  is_sllw * (s1 * r0) === 0
  is_sllw * (s1 * (r1 - lr0)) === 0
  is_sllw * (msb * 65535 - r2) === 0
  is_sllw * (msb * 65535 - r3) === 0
  -- is_sllw_imm bridge + op_a_0.
  (is_sllw_imm - is_sllw * adapter.imm_c) === 0
  adapter.op_a_0 === 0

set_option maxHeartbeats 1600000 in
-- ~60 inline gates + 2 readers + 11 gated lookups; consistency synthesis
-- exceeds default cap (precedent: LtChip / MulChip / Multiplicity scaffold).
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) ShiftLeftCols unit where
  name := "SP1Clean.ShiftLeft"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]
  subcircuitsConsistent input offset := by
    simp +arith only [main, circuit_norm]

def Assumptions (cols : ShiftLeftCols (ZMod p)) : Prop :=
  cols.adapter_cols.is_trusted = cols.is_sll + cols.is_sllw ∧
  cols.is_sll + cols.is_sllw = 1

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e_ckh, e_c1624, e_c016, e_pc⟩,
      ⟨e_opa, ⟨e_opapv, e_opapl, e_opadll⟩, e_opa0, e_opb,
        ⟨e_opbpv, e_opbpl, e_opbdll⟩, e_opc, ⟨e_opcpv, e_opcpl, e_opcdll⟩, e_immc⟩,
      e_result, e_cbits, e_v01, e_v012, e_v0123, e_shiftu16, e_lower, e_higher,
      e_limbresult, e_sllwmsb, e_issll, e_issllw, e_issllwimm, e_istrusted⟩ := h_input
  subst_eqs
  obtain ⟨h_trusted, h_sum⟩ := h_assumptions
  simp only [FormalSpec, Vector.getElem_map]
  sorry

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

end Assertion

def assertion : FormalAssertion (ZMod p) ShiftLeftCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.ShiftLeft
