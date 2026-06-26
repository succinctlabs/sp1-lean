import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Proofs.Operations.U16MSBOperation.Formal
import SP1Clean.Proofs.Chips.ShiftRightChip.Core
import SP1Clean.Proofs.Chips.ShiftRightChip.Populate
import SP1Clean.Proofs.Chips.ShiftRightChip.Dispatch
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.ALUTypeReader
import SP1Clean.Model.Channels
import SP1Clean.Extracted.ShiftRightChip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The `ShiftRight` chip row as a `GeneralFormalCircuit`

`SRL`/`SRA`/`SRLW`/`SRAW`: as with `ShiftLeftChip`, no operation-level extraction — the inverted-`v`
power encodings, the `b_msb`/`srw_msb` sign-extension MSB gadgets, the `lower/higher_limb` bit-split,
the `limb_result` reassembly, and the four-variant output placement are inlined into
`Extracted/ShiftRightChip.lean`.

`AssertSpec` / `InteractSpec` capture the structural meaning of SP1's two extracted constraint lists;
the semantic flag-gated RV64 `srl`/`sra`/`srlw`/`sraw` `Spec` is in `Specs/Chip.lean`.
`Faithful/ShiftRightChip.lean` anchors both structural specs.

`main` composes the readers + three `U16MSBOperation` gadgets + the witnessed column block + the
`is_real` gate. Soundness and completeness are proven (honest `Populate` witness closures). -/

namespace SP1Clean.ShiftRightChip

open Circuit
open Extracted (ShiftRightCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- The register-read operands the chip decomposes are 64-bit values (received facts from the offline
memory: the writer range-checked them). These are the `rs1`/`rs2` the `Spec` shifts. Lives here (not in
`Formal`) so the per-op `Soundness/<Op>.lean` split files can import it without a cycle through `Formal`. -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.adapter.op_b_memory.prev_value ∧ Word.isU64 input.adapter.op_c_memory.prev_value

/-- **Assertion half** — the literal meaning of SP1's `ShiftRightCols.asserts` *own* (inline) assertZero
list. `E14 = is_srl + is_sra` (the 64-bit-shift indicator) and `E13 = is_srlw + is_sraw` (the
word-shift indicator) gate the two output-placement blocks; the `v_*` powers are the **inverted**
right-shift form `2^(16 - bitShift)`. In order: the four variant booleans + sum-bound, the
immediate-consistency `is_w_imm`, the six `c_bits` booleans, the four `shift_u16` byte-selectors +
booleans + one-hot, the three inverted `v_*` encodings, the four `lower/higher_limb` splits (limbs 2,3
gated by `E14`), the four `limb_result` reassemblies, the `b_msb`/`srw_msb` sign witnesses, the
SRL/SRA output placement (gated `E14`), the SRLW/SRAW output placement (gated `E13`), and `op_a_0`. -/
def AssertSpec (cols : ShiftRightCols (ZMod p)) : Prop :=
  let srl := cols.is_srl; let sra := cols.is_sra; let srlw := cols.is_srlw; let sraw := cols.is_sraw
  let e14 := srl + sra; let e13 := srlw + sraw; let sum := srl + sra + srlw + sraw
  let b0 := cols.c_bits[0]; let b1 := cols.c_bits[1]; let b2 := cols.c_bits[2]
  let b3 := cols.c_bits[3]; let b4 := cols.c_bits[4]; let b5 := cols.c_bits[5]
  let s0 := cols.shift_u16[0]; let s1 := cols.shift_u16[1]
  let s2 := cols.shift_u16[2]; let s3 := cols.shift_u16[3]
  let byteShift := b4 + b5 * 2 * e14
  let bmsb := cols.b_msb.msb; let srwmsb := cols.srw_msb.msb
  let sraFill := cols.b_msb.msb * 65536 - cols.sra_msb_v0123
  -- variant flags + sum-bound + immediate consistency
  srl * (srl - 1) = 0 ∧ sra * (sra - 1) = 0 ∧ srlw * (srlw - 1) = 0 ∧ sraw * (sraw - 1) = 0 ∧
  sum * (sum - 1) = 0 ∧
  cols.is_w_imm - e13 * cols.adapter.imm_c = 0 ∧
  -- c_bits booleans
  b0 * (b0 - 1) = 0 ∧ b1 * (b1 - 1) = 0 ∧ b2 * (b2 - 1) = 0 ∧
  b3 * (b3 - 1) = 0 ∧ b4 * (b4 - 1) = 0 ∧ b5 * (b5 - 1) = 0 ∧
  -- shift_u16 byte-shift selectors + booleans
  s0 * (byteShift - 0) = 0 ∧ s0 * (s0 - 1) = 0 ∧
  s1 * (byteShift - 1) = 0 ∧ s1 * (s1 - 1) = 0 ∧
  s2 * (byteShift - 2) = 0 ∧ s2 * (s2 - 1) = 0 ∧
  s3 * (byteShift - 3) = 0 ∧ s3 * (s3 - 1) = 0 ∧
  sum * ((s0 + s1 + s2 + s3) - 1) = 0 ∧
  -- inverted v_* power encodings
  cols.v_01 - (((1 - b0) + 1) * 2) * ((1 - b1) * 3 + 1) = 0 ∧
  cols.v_012 - cols.v_01 * ((1 - b2) * 15 + 1) = 0 ∧
  cols.v_0123 - cols.v_012 * ((1 - b3) * 255 + 1) = 0 ∧
  -- lower/higher limb split (limbs 2,3 carry the E14 factor)
  cols.adapter.op_b_memory.prev_value[0] * cols.v_0123
    - (cols.higher_limb[0] * 65536 + cols.lower_limb[0] * cols.v_0123) = 0 ∧
  cols.adapter.op_b_memory.prev_value[1] * cols.v_0123
    - (cols.higher_limb[1] * 65536 + cols.lower_limb[1] * cols.v_0123) = 0 ∧
  (cols.adapter.op_b_memory.prev_value[2] * cols.v_0123) * e14
    - (cols.higher_limb[2] * 65536 + cols.lower_limb[2] * cols.v_0123) = 0 ∧
  (cols.adapter.op_b_memory.prev_value[3] * cols.v_0123) * e14
    - (cols.higher_limb[3] * 65536 + cols.lower_limb[3] * cols.v_0123) = 0 ∧
  -- limb_result reassembly (higher_limb[i] + lower_limb[i+1] * v_0123)
  cols.limb_result[0] - (cols.higher_limb[0] + cols.lower_limb[1] * cols.v_0123) = 0 ∧
  cols.limb_result[1] - (cols.higher_limb[1] + cols.lower_limb[2] * cols.v_0123) = 0 ∧
  cols.limb_result[2] - (cols.higher_limb[2] + cols.lower_limb[3] * cols.v_0123) = 0 ∧
  cols.limb_result[3] - cols.higher_limb[3] = 0 ∧
  -- MSB sign witnesses
  (srl + srlw) * bmsb = 0 ∧
  cols.sra_msb_v0123 - bmsb * cols.v_0123 = 0 ∧
  (e13 - 1) * srwmsb = 0 ∧
  -- SRL/SRA output placement (gated e14)
  e14 * (s0 * (cols.a[0] - cols.limb_result[0])) = 0 ∧
  e14 * (s0 * (cols.a[1] - cols.limb_result[1])) = 0 ∧
  e14 * (s0 * (cols.a[2] - cols.limb_result[2])) = 0 ∧
  e14 * (s0 * (cols.a[3] - (cols.limb_result[3] + sraFill))) = 0 ∧
  e14 * (s1 * (cols.a[0] - cols.limb_result[1])) = 0 ∧
  e14 * (s1 * (cols.a[1] - cols.limb_result[2])) = 0 ∧
  e14 * (s1 * (cols.a[2] - (cols.limb_result[3] + sraFill))) = 0 ∧
  e14 * (s1 * (cols.a[3] - bmsb * 65535)) = 0 ∧
  e14 * (s2 * (cols.a[0] - cols.limb_result[2])) = 0 ∧
  e14 * (s2 * (cols.a[1] - (cols.limb_result[3] + sraFill))) = 0 ∧
  e14 * (s2 * (cols.a[2] - bmsb * 65535)) = 0 ∧
  e14 * (s2 * (cols.a[3] - bmsb * 65535)) = 0 ∧
  e14 * (s3 * (cols.a[0] - (cols.limb_result[3] + sraFill))) = 0 ∧
  e14 * (s3 * (cols.a[1] - bmsb * 65535)) = 0 ∧
  e14 * (s3 * (cols.a[2] - bmsb * 65535)) = 0 ∧
  e14 * (s3 * (cols.a[3] - bmsb * 65535)) = 0 ∧
  -- SRLW/SRAW output placement (gated e13)
  e13 * (s0 * (cols.a[0] - cols.limb_result[0])) = 0 ∧
  e13 * (s0 * (cols.a[1] - (cols.limb_result[1] + sraFill))) = 0 ∧
  e13 * (s1 * (cols.a[0] - (cols.limb_result[1] + sraFill))) = 0 ∧
  e13 * (s1 * (cols.a[1] - bmsb * 65535)) = 0 ∧
  e13 * (cols.a[2] - srwmsb * 65535) = 0 ∧
  e13 * (cols.a[3] - srwmsb * 65535) = 0 ∧
  -- op_a_0 zeroing flag
  cols.adapter.op_a_0 = 0

/-- **Interaction half** — SP1's `ShiftRightCols.interactions` byte-range sends (gated by
`gate = is_srl + is_sra + is_srlw + is_sraw`): the shift-amount high bits `< 2^10`, and, per limb, the
`lower_limb` `< 2^bitShift` and `higher_limb` `< 2^(16 - bitShift)` ranges. (Note the lower/higher
widths are swapped versus `ShiftLeftChip`, as the right shift keeps the high bits.) -/
def InteractSpec (cols : ShiftRightCols (ZMod p)) : Prop :=
  let b0 := cols.c_bits[0]; let b1 := cols.c_bits[1]; let b2 := cols.c_bits[2]
  let b3 := cols.c_bits[3]; let b4 := cols.c_bits[4]; let b5 := cols.c_bits[5]
  let bitShift : ZMod p := b0 * 1 + b1 * 2 + b2 * 4 + b3 * 8
  let shamt : ZMod p := bitShift + b4 * 16 + b5 * 32
  let e84 : ZMod p := (cols.adapter.op_c_memory.prev_value[0] - shamt) * (64 : ZMod p)⁻¹
  let gate : ZMod p := cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw
  (gate ≠ 0 → e84.val < 2 ^ (10 : ZMod p).val) ∧
  (gate ≠ 0 → cols.lower_limb[0].val < 2 ^ bitShift.val) ∧
  (gate ≠ 0 → cols.higher_limb[0].val < 2 ^ (16 - bitShift).val) ∧
  (gate ≠ 0 → cols.lower_limb[1].val < 2 ^ bitShift.val) ∧
  (gate ≠ 0 → cols.higher_limb[1].val < 2 ^ (16 - bitShift).val) ∧
  (gate ≠ 0 → cols.lower_limb[2].val < 2 ^ bitShift.val) ∧
  (gate ≠ 0 → cols.higher_limb[2].val < 2 ^ (16 - bitShift).val) ∧
  (gate ≠ 0 → cols.lower_limb[3].val < 2 ^ bitShift.val) ∧
  (gate ≠ 0 → cols.higher_limb[3].val < 2 ^ (16 - bitShift).val)

set_option maxHeartbeats 4000000 in
/-- Compose the threaded `CPUState`/`ALUTypeReader` reader blocks and the **three** `U16MSBOperation`
gadgets (`b_msb` on `op_b` limb 3 gated `is_sra` and limb 1 gated `is_sraw`; `srw_msb` on `a[1]` gated
`is_srlw + is_sraw`), witness the shift column block, gate `is_real`, emit the ~58 inline shift
assertions (`AssertSpec`) and the nine byte-range pulls (`InteractSpec`), and assemble the extracted
`ShiftRightCols` struct. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var ShiftRightCols (ZMod p)) := do
  assertion Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  let a ← witnessVector 4 (fun env =>
    populateA
      #v[env input.adapter.op_b_memory.prev_value[0], env input.adapter.op_b_memory.prev_value[1],
         env input.adapter.op_b_memory.prev_value[2], env input.adapter.op_b_memory.prev_value[3]]
      (env input.adapter.op_c_memory.prev_value[0]) (hintFlags env.hint))
  let b_msb ← witnessVector 1 (fun env =>
    #v[bMsb
      #v[env input.adapter.op_b_memory.prev_value[0], env input.adapter.op_b_memory.prev_value[1],
         env input.adapter.op_b_memory.prev_value[2], env input.adapter.op_b_memory.prev_value[3]]
      (hintFlags env.hint)])
  let srw_msb ← witnessVector 1 (fun env =>
    #v[srwMsb
      #v[env input.adapter.op_b_memory.prev_value[0], env input.adapter.op_b_memory.prev_value[1],
         env input.adapter.op_b_memory.prev_value[2], env input.adapter.op_b_memory.prev_value[3]]
      (env input.adapter.op_c_memory.prev_value[0]) (hintFlags env.hint)])
  let c_bits ← witnessVector 6 (fun env =>
    ShiftLeftChip.cBits (env input.adapter.op_c_memory.prev_value[0]))
  let sra_msb_v0123 ← witnessVector 1 (fun env =>
    #v[sraMsbV0123
      #v[env input.adapter.op_b_memory.prev_value[0], env input.adapter.op_b_memory.prev_value[1],
         env input.adapter.op_b_memory.prev_value[2], env input.adapter.op_b_memory.prev_value[3]]
      (env input.adapter.op_c_memory.prev_value[0]) (hintFlags env.hint)])
  let v ← witnessVector 3 (fun env => vPowersInv (env input.adapter.op_c_memory.prev_value[0]))
  let lower_limb ← witnessVector 4 (fun env =>
    lowerLimb
      #v[env input.adapter.op_b_memory.prev_value[0], env input.adapter.op_b_memory.prev_value[1],
         env input.adapter.op_b_memory.prev_value[2], env input.adapter.op_b_memory.prev_value[3]]
      (env input.adapter.op_c_memory.prev_value[0]) (hintFlags env.hint))
  let higher_limb ← witnessVector 4 (fun env =>
    higherLimb
      #v[env input.adapter.op_b_memory.prev_value[0], env input.adapter.op_b_memory.prev_value[1],
         env input.adapter.op_b_memory.prev_value[2], env input.adapter.op_b_memory.prev_value[3]]
      (env input.adapter.op_c_memory.prev_value[0]) (hintFlags env.hint))
  let limb_result ← witnessVector 4 (fun env =>
    limbResult
      #v[env input.adapter.op_b_memory.prev_value[0], env input.adapter.op_b_memory.prev_value[1],
         env input.adapter.op_b_memory.prev_value[2], env input.adapter.op_b_memory.prev_value[3]]
      (env input.adapter.op_c_memory.prev_value[0]) (hintFlags env.hint))
  let shift_u16 ← witnessVector 4 (fun env =>
    shiftU16 (env input.adapter.op_c_memory.prev_value[0]) (hintFlags env.hint))
  let flags ← witnessVector 5 (fun env =>
    #v[(hintFlags env.hint)[0], (hintFlags env.hint)[1], (hintFlags env.hint)[2],
       (hintFlags env.hint)[3],
       ((hintFlags env.hint)[2] + (hintFlags env.hint)[3]) * env input.adapter.imm_c])
  let is_srl := flags[0]; let is_sra := flags[1]; let is_srlw := flags[2]
  let is_sraw := flags[3]; let is_w_imm := flags[4]
  assertion U16MSBOperation.circuit ⟨input.adapter.op_b_memory.prev_value[3], ⟨b_msb[0]⟩, is_sra⟩
  assertion U16MSBOperation.circuit ⟨input.adapter.op_b_memory.prev_value[1], ⟨b_msb[0]⟩, is_sraw⟩
  assertion U16MSBOperation.circuit ⟨a[1], ⟨srw_msb[0]⟩, is_srlw + is_sraw⟩
  assertion Readers.ALUTypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
     is_srl * 7 + is_sra * 8 + is_srlw * 22 + is_sraw * 23, a[0], a[1], a[2], a[3]⟩
  input.is_real * (input.is_real - 1) === 0
  -- The inline shift assertZeros (`AssertSpec`), emitted in the same order as `AssertSpec`/Extracted.
  let e14 := is_srl + is_sra
  let e13 := is_srlw + is_sraw
  let sum := is_srl + is_sra + is_srlw + is_sraw
  let b0 := c_bits[0]; let b1 := c_bits[1]; let b2 := c_bits[2]
  let b3 := c_bits[3]; let b4 := c_bits[4]; let b5 := c_bits[5]
  let s0 := shift_u16[0]; let s1 := shift_u16[1]; let s2 := shift_u16[2]; let s3 := shift_u16[3]
  let byteShift : Expression (ZMod p) := b4 + b5 * 2 * e14
  let v_0123 := v[0]; let v_012 := v[1]; let v_01 := v[2]
  let bmsb := b_msb[0]; let srwmsb := srw_msb[0]
  let c65536 : Expression (ZMod p) := 65536
  let c65535 : Expression (ZMod p) := 65535
  let sraFill : Expression (ZMod p) := bmsb * c65536 - sra_msb_v0123[0]
  let bmsbFill : Expression (ZMod p) := bmsb * c65535
  let srwFill : Expression (ZMod p) := srwmsb * c65535
  -- variant flags + sum-bound + immediate consistency
  is_srl * (is_srl - 1) === 0
  is_sra * (is_sra - 1) === 0
  is_srlw * (is_srlw - 1) === 0
  is_sraw * (is_sraw - 1) === 0
  sum * (sum - 1) === 0
  is_w_imm - e13 * input.adapter.imm_c === 0
  -- c_bits booleans
  b0 * (b0 - 1) === 0
  b1 * (b1 - 1) === 0
  b2 * (b2 - 1) === 0
  b3 * (b3 - 1) === 0
  b4 * (b4 - 1) === 0
  b5 * (b5 - 1) === 0
  -- shift_u16 byte-shift selectors + booleans
  s0 * (byteShift - 0) === 0
  s0 * (s0 - 1) === 0
  s1 * (byteShift - 1) === 0
  s1 * (s1 - 1) === 0
  s2 * (byteShift - 2) === 0
  s2 * (s2 - 1) === 0
  s3 * (byteShift - 3) === 0
  s3 * (s3 - 1) === 0
  sum * ((s0 + s1 + s2 + s3) - 1) === 0
  -- inverted v_* power encodings
  v_01 - (((1 - b0) + 1) * 2) * ((1 - b1) * 3 + 1) === 0
  v_012 - v_01 * ((1 - b2) * 15 + 1) === 0
  v_0123 - v_012 * ((1 - b3) * 255 + 1) === 0
  -- lower/higher limb split (limbs 2,3 carry the E14 factor)
  input.adapter.op_b_memory.prev_value[0] * v_0123
    - (higher_limb[0] * c65536 + lower_limb[0] * v_0123) === 0
  input.adapter.op_b_memory.prev_value[1] * v_0123
    - (higher_limb[1] * c65536 + lower_limb[1] * v_0123) === 0
  (input.adapter.op_b_memory.prev_value[2] * v_0123) * e14
    - (higher_limb[2] * c65536 + lower_limb[2] * v_0123) === 0
  (input.adapter.op_b_memory.prev_value[3] * v_0123) * e14
    - (higher_limb[3] * c65536 + lower_limb[3] * v_0123) === 0
  -- limb_result reassembly (higher_limb[i] + lower_limb[i+1] * v_0123)
  limb_result[0] - (higher_limb[0] + lower_limb[1] * v_0123) === 0
  limb_result[1] - (higher_limb[1] + lower_limb[2] * v_0123) === 0
  limb_result[2] - (higher_limb[2] + lower_limb[3] * v_0123) === 0
  limb_result[3] - higher_limb[3] === 0
  -- MSB sign witnesses
  (is_srl + is_srlw) * bmsb === 0
  sra_msb_v0123[0] - bmsb * v_0123 === 0
  (e13 - 1) * srwmsb === 0
  -- SRL/SRA output placement (gated e14)
  e14 * (s0 * (a[0] - limb_result[0])) === 0
  e14 * (s0 * (a[1] - limb_result[1])) === 0
  e14 * (s0 * (a[2] - limb_result[2])) === 0
  e14 * (s0 * (a[3] - (limb_result[3] + sraFill))) === 0
  e14 * (s1 * (a[0] - limb_result[1])) === 0
  e14 * (s1 * (a[1] - limb_result[2])) === 0
  e14 * (s1 * (a[2] - (limb_result[3] + sraFill))) === 0
  e14 * (s1 * (a[3] - bmsbFill)) === 0
  e14 * (s2 * (a[0] - limb_result[2])) === 0
  e14 * (s2 * (a[1] - (limb_result[3] + sraFill))) === 0
  e14 * (s2 * (a[2] - bmsbFill)) === 0
  e14 * (s2 * (a[3] - bmsbFill)) === 0
  e14 * (s3 * (a[0] - (limb_result[3] + sraFill))) === 0
  e14 * (s3 * (a[1] - bmsbFill)) === 0
  e14 * (s3 * (a[2] - bmsbFill)) === 0
  e14 * (s3 * (a[3] - bmsbFill)) === 0
  -- SRLW/SRAW output placement (gated e13)
  e13 * (s0 * (a[0] - limb_result[0])) === 0
  e13 * (s0 * (a[1] - (limb_result[1] + sraFill))) === 0
  e13 * (s1 * (a[0] - (limb_result[1] + sraFill))) === 0
  e13 * (s1 * (a[1] - bmsbFill)) === 0
  e13 * (a[2] - srwFill) === 0
  e13 * (a[3] - srwFill) === 0
  -- op_a_0 zeroing flag
  input.adapter.op_a_0 === 0
  -- The byte-range pulls (`InteractSpec`), gated by `gate = is_srl+is_sra+is_srlw+is_sraw`.
  let gate := sum
  let bitShift : Expression (ZMod p) := b0 * 1 + b1 * 2 + b2 * 4 + b3 * 8
  let shamt : Expression (ZMod p) := bitShift + b4 * 16 + b5 * 32
  let e84 : Expression (ZMod p) := (input.adapter.op_c_memory.prev_value[0] - shamt) * (64 : ZMod p)⁻¹
  byteChannel.pullIf gate
    (⟨6, e84, Expression.const ((10 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf gate
    (⟨6, lower_limb[0], bitShift, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf gate
    (⟨6, higher_limb[0], 16 - bitShift, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf gate
    (⟨6, lower_limb[1], bitShift, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf gate
    (⟨6, higher_limb[1], 16 - bitShift, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf gate
    (⟨6, lower_limb[2], bitShift, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf gate
    (⟨6, higher_limb[2], 16 - bitShift, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf gate
    (⟨6, lower_limb[3], bitShift, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf gate
    (⟨6, higher_limb[3], 16 - bitShift, 0⟩ : ByteRow (Expression (ZMod p)))
  return ⟨input.state, input.adapter, a, ⟨b_msb[0]⟩, ⟨srw_msb[0]⟩, c_bits, sra_msb_v0123[0],
    v[0], v[1], v[2], lower_limb, higher_limb, limb_result, shift_u16,
    is_srl, is_sra, is_srlw, is_sraw, is_w_imm⟩

set_option maxHeartbeats 4000000 in
instance elaborated : ElaboratedCircuit (ZMod p) Inputs ShiftRightCols main where
  -- witnesses: a(4) + b_msb(1) + srw_msb(1) + c_bits(6) + sra_msb_v0123(1) + v(3) + lower(4)
  -- + higher(4) + limb_result(4) + shift_u16(4) + flags(5) = 37.
  localLength _ := 37
  localLength_eq := by simp +arith [circuit_norm, main, Readers.ALUTypeReader.circuit, Readers.CPUState.circuit, U16MSBOperation.circuit]
  subcircuitsConsistent := by simp only [circuit_norm, main, Readers.ALUTypeReader.circuit, Readers.CPUState.circuit, U16MSBOperation.circuit]; try omega
  channelsWithGuarantees := [byteChannel.toRaw]
  channelsLawful := by simp [circuit_norm, main, Readers.ALUTypeReader.circuit, Readers.CPUState.circuit, U16MSBOperation.circuit]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [byteChannel.toRaw] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 37 := rfl

end SP1Clean.ShiftRightChip
