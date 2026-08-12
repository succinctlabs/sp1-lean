import SP1Clean.FormalModel.Contracts.Chips
import Clean.Circuit.Basic
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # `ShiftLeftCore` — the ShiftLeft chip's assertion cluster

This zero-witness `FormalAssertion` boundary emits the tail represented by
`ShiftLeftChip.CoreSpec`. The parent keeps the two flag booleans and their combined boolean gate at
chip level so Clean's shallow channel-law proof can see the byte-interaction selector. This is a
proof-oriented gadget over the whole committed row, not a claimed upstream Rust operation.
-/

namespace SP1Clean.ShiftLeftCore

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Emit the folded tail of the chip-local ShiftLeft assertion list. The circuit witnesses nothing
and has no channel activity. -/
def main (cols : Var ShiftLeftChip.Columns (ZMod p)) : Circuit (ZMod p) Unit := do
  let sll := cols.is_sll
  let sllw := cols.is_sllw
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
  let byteShift := b4 + b5 * 2 * sll
  let c65536 : Expression (ZMod p) := 65536
  let c65535 : Expression (ZMod p) := 65535
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
  (sll + sllw) * ((s0 + s1 + s2 + s3) - 1) === 0
  cols.v_01 - (b0 + 1) * (b1 * 3 + 1) === 0
  cols.v_012 - cols.v_01 * (b2 * 15 + 1) === 0
  cols.v_0123 - cols.v_012 * (b3 * 255 + 1) === 0
  cols.adapter.op_b_memory.prev_value[0] * cols.v_0123
    - (cols.higher_limb[0] * c65536 + cols.lower_limb[0] * cols.v_0123) === 0
  cols.adapter.op_b_memory.prev_value[1] * cols.v_0123
    - (cols.higher_limb[1] * c65536 + cols.lower_limb[1] * cols.v_0123) === 0
  cols.adapter.op_b_memory.prev_value[2] * cols.v_0123
    - (cols.higher_limb[2] * c65536 + cols.lower_limb[2] * cols.v_0123) === 0
  cols.adapter.op_b_memory.prev_value[3] * cols.v_0123
    - (cols.higher_limb[3] * c65536 + cols.lower_limb[3] * cols.v_0123) === 0
  cols.limb_result[0] - cols.lower_limb[0] * cols.v_0123 === 0
  cols.limb_result[1] - (cols.lower_limb[1] * cols.v_0123 + cols.higher_limb[0]) === 0
  cols.limb_result[2] - (cols.lower_limb[2] * cols.v_0123 + cols.higher_limb[1]) === 0
  cols.limb_result[3] - (cols.lower_limb[3] * cols.v_0123 + cols.higher_limb[2]) === 0
  sll * (s0 * (cols.a[0] - cols.limb_result[0])) === 0
  sll * (s0 * (cols.a[1] - cols.limb_result[1])) === 0
  sll * (s0 * (cols.a[2] - cols.limb_result[2])) === 0
  sll * (s0 * (cols.a[3] - cols.limb_result[3])) === 0
  sll * (s1 * cols.a[0]) === 0
  sll * (s1 * (cols.a[1] - cols.limb_result[0])) === 0
  sll * (s1 * (cols.a[2] - cols.limb_result[1])) === 0
  sll * (s1 * (cols.a[3] - cols.limb_result[2])) === 0
  sll * (s2 * cols.a[0]) === 0
  sll * (s2 * cols.a[1]) === 0
  sll * (s2 * (cols.a[2] - cols.limb_result[0])) === 0
  sll * (s2 * (cols.a[3] - cols.limb_result[1])) === 0
  sll * (s3 * cols.a[0]) === 0
  sll * (s3 * cols.a[1]) === 0
  sll * (s3 * cols.a[2]) === 0
  sll * (s3 * (cols.a[3] - cols.limb_result[0])) === 0
  sllw * (s0 * (cols.a[0] - cols.limb_result[0])) === 0
  sllw * (s0 * (cols.a[1] - cols.limb_result[1])) === 0
  sllw * (s1 * cols.a[0]) === 0
  sllw * (s1 * (cols.a[1] - cols.limb_result[0])) === 0
  sllw * (cols.sllw_msb.msb * c65535 - cols.a[2]) === 0
  sllw * (cols.sllw_msb.msb * c65535 - cols.a[3]) === 0
  cols.is_sllw_imm - sllw * cols.adapter.imm_c === 0
  cols.adapter.op_a_0 === 0

/-- The assertion cluster has no witnesses, outputs, subcircuits, or channel interactions. -/
instance elaborated : ElaboratedCircuit (ZMod p) ShiftLeftChip.Columns unit main := by
  elaborate_circuit

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p))) = [] := rfl

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (cols : Var ShiftLeftChip.Columns (ZMod p)) :
    (elaborated (p := p)).localLength cols = 0 := rfl

end SP1Clean.ShiftLeftCore
