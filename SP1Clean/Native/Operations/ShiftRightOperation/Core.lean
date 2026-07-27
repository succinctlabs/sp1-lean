import SP1Clean.FormalModel.Contracts.Chips
import Clean.Circuit.Basic
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # `ShiftRightCore` — the ShiftRight chip's inline assertion cluster

This zero-witness `FormalAssertion` boundary emits the 53-assert tail represented by
`ShiftRightChip.CoreSpec`.  The parent deliberately keeps the preceding four flag booleans and
combined boolean gate at chip level: Clean's shallow channel-law proof needs to see that combined
gate.  This is a proof-oriented gadget over the whole committed `ShiftRightChip.Columns` row, not a claim
that upstream SP1 has a corresponding Rust operation.  Virtual subcircuit elaboration preserves the
original operation order.
-/

namespace SP1Clean.ShiftRightCore

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Emit the folded tail of the chip-local ShiftRight assertion list over the committed row.  The
circuit witnesses nothing and has no channel activity. -/
def main (cols : Var ShiftRightChip.Columns (ZMod p)) : Circuit (ZMod p) Unit := do
  let srl := cols.is_srl
  let sra := cols.is_sra
  let srlw := cols.is_srlw
  let sraw := cols.is_sraw
  let e14 := srl + sra
  let e13 := srlw + sraw
  let sum := srl + sra + srlw + sraw
  let b0 := cols.c_bits[0]
  let b1 := cols.c_bits[1]
  let b2 := cols.c_bits[2]
  let b3 := cols.c_bits[3]
  let b4 := cols.c_bits[4]
  let b5 := cols.c_bits[5]
  let s0 := cols.shift_u16[0]
  let s1 := cols.shift_u16[1]
  let s2 := cols.shift_u16[2]
  let s3 := cols.shift_u16[3]
  let byteShift : Expression (ZMod p) := b4 + b5 * 2 * e14
  let bmsb := cols.b_msb.msb
  let srwmsb := cols.srw_msb.msb
  let c65536 : Expression (ZMod p) := 65536
  let c65535 : Expression (ZMod p) := 65535
  let sraFill : Expression (ZMod p) := bmsb * c65536 - cols.sra_msb_v0123
  let bmsbFill : Expression (ZMod p) := bmsb * c65535
  let srwFill : Expression (ZMod p) := srwmsb * c65535
  -- Immediate consistency; the five preceding gate constraints stay in the parent chip.
  cols.is_w_imm - e13 * cols.adapter.imm_c === 0
  -- Shift-amount bits and the selected 16-bit limb shift.
  b0 * (b0 - 1) === 0
  b1 * (b1 - 1) === 0
  b2 * (b2 - 1) === 0
  b3 * (b3 - 1) === 0
  b4 * (b4 - 1) === 0
  b5 * (b5 - 1) === 0
  s0 * (byteShift - 0) === 0
  s0 * (s0 - 1) === 0
  s1 * (byteShift - 1) === 0
  s1 * (s1 - 1) === 0
  s2 * (byteShift - 2) === 0
  s2 * (s2 - 1) === 0
  s3 * (byteShift - 3) === 0
  s3 * (s3 - 1) === 0
  sum * ((s0 + s1 + s2 + s3) - 1) === 0
  -- Inverted within-limb powers and the four source-limb splits.
  cols.v_01 - (((1 - b0) + 1) * 2) * ((1 - b1) * 3 + 1) === 0
  cols.v_012 - cols.v_01 * ((1 - b2) * 15 + 1) === 0
  cols.v_0123 - cols.v_012 * ((1 - b3) * 255 + 1) === 0
  cols.adapter.op_b_memory.prev_value[0] * cols.v_0123
    - (cols.higher_limb[0] * c65536 + cols.lower_limb[0] * cols.v_0123) === 0
  cols.adapter.op_b_memory.prev_value[1] * cols.v_0123
    - (cols.higher_limb[1] * c65536 + cols.lower_limb[1] * cols.v_0123) === 0
  (cols.adapter.op_b_memory.prev_value[2] * cols.v_0123) * e14
    - (cols.higher_limb[2] * c65536 + cols.lower_limb[2] * cols.v_0123) === 0
  (cols.adapter.op_b_memory.prev_value[3] * cols.v_0123) * e14
    - (cols.higher_limb[3] * c65536 + cols.lower_limb[3] * cols.v_0123) === 0
  -- Reassemble shifted limbs and constrain the sign witnesses.
  cols.limb_result[0] - (cols.higher_limb[0] + cols.lower_limb[1] * cols.v_0123) === 0
  cols.limb_result[1] - (cols.higher_limb[1] + cols.lower_limb[2] * cols.v_0123) === 0
  cols.limb_result[2] - (cols.higher_limb[2] + cols.lower_limb[3] * cols.v_0123) === 0
  cols.limb_result[3] - cols.higher_limb[3] === 0
  (srl + srlw) * bmsb === 0
  cols.sra_msb_v0123 - bmsb * cols.v_0123 === 0
  (e13 - 1) * srwmsb === 0
  -- Full-width result placement.
  e14 * (s0 * (cols.a[0] - cols.limb_result[0])) === 0
  e14 * (s0 * (cols.a[1] - cols.limb_result[1])) === 0
  e14 * (s0 * (cols.a[2] - cols.limb_result[2])) === 0
  e14 * (s0 * (cols.a[3] - (cols.limb_result[3] + sraFill))) === 0
  e14 * (s1 * (cols.a[0] - cols.limb_result[1])) === 0
  e14 * (s1 * (cols.a[1] - cols.limb_result[2])) === 0
  e14 * (s1 * (cols.a[2] - (cols.limb_result[3] + sraFill))) === 0
  e14 * (s1 * (cols.a[3] - bmsbFill)) === 0
  e14 * (s2 * (cols.a[0] - cols.limb_result[2])) === 0
  e14 * (s2 * (cols.a[1] - (cols.limb_result[3] + sraFill))) === 0
  e14 * (s2 * (cols.a[2] - bmsbFill)) === 0
  e14 * (s2 * (cols.a[3] - bmsbFill)) === 0
  e14 * (s3 * (cols.a[0] - (cols.limb_result[3] + sraFill))) === 0
  e14 * (s3 * (cols.a[1] - bmsbFill)) === 0
  e14 * (s3 * (cols.a[2] - bmsbFill)) === 0
  e14 * (s3 * (cols.a[3] - bmsbFill)) === 0
  -- Word-result placement and destination-zero flag.
  e13 * (s0 * (cols.a[0] - cols.limb_result[0])) === 0
  e13 * (s0 * (cols.a[1] - (cols.limb_result[1] + sraFill))) === 0
  e13 * (s1 * (cols.a[0] - (cols.limb_result[1] + sraFill))) === 0
  e13 * (s1 * (cols.a[1] - bmsbFill)) === 0
  e13 * (cols.a[2] - srwFill) === 0
  e13 * (cols.a[3] - srwFill) === 0
  cols.adapter.op_a_0 === 0

/-- The assertion cluster has no witnesses, outputs, subcircuits, or channel interactions. -/
instance elaborated : ElaboratedCircuit (ZMod p) ShiftRightChip.Columns unit main := by
  elaborate_circuit

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p))) = [] := rfl

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (cols : Var ShiftRightChip.Columns (ZMod p)) :
    (elaborated (p := p)).localLength cols = 0 := rfl

end SP1Clean.ShiftRightCore
