import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Proofs.Operations.U16MSBOperation.Formal
import SP1Clean.Proofs.Chips.ShiftRightChip.Core
import SP1Clean.Proofs.Chips.ShiftRightChip.Populate
import SP1Clean.Proofs.Chips.ShiftRightChip.Dispatch
import SP1Clean.Proofs.Chips.ShiftRightChip.Math
import SP1Clean.Proofs.Chips.ShiftRightChip.Flags
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.ALUTypeReader
import SP1Clean.Native.Readers.RegisterWrite
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
  let _ ← Readers.CPUState.circuit
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
  -- `ALUTypeReader` is now a `GeneralFormalCircuit` (SC Phase 2pre) — composed via the GFC `CoeFun`
  -- (`subcircuitWithAssertion`), discarding its `unit` output. Its `Spec` (Contracts) is unchanged.
  let _ ← Readers.ALUTypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
     is_srl * 7 + is_sra * 8 + is_srlw * 22 + is_sraw * 23, a[0], a[1], a[2], a[3]⟩
  -- Option B: the op_a (`rd`) write Memory **push** is composed here (factored OUT of the reader), *after*
  -- the shift placement, so `isU64 a` (the result range-check, `isU64_sound`) discharges its requirement.
  -- The write access clock is the recombined low clock `+ 4` (matching the reader's op_a `RegisterAccessCols`).
  -- **Gate = the variant flag-sum** `is_srl + is_sra + is_srlw + is_sraw` (= SP1's `is_real`, `sr/mod.rs:335`:
  -- "All interactions are done with multiplicity `is_real`", their sum): the result `a` is range-checked only
  -- when a variant fires (`sum = 1`), so the write's `isU64 a` requirement is sound exactly on those rows.
  assertion Readers.RegisterWrite.circuit
    ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
     input.adapter.op_a, a, is_srl + is_sra + is_srlw + is_sraw⟩
  -- `is_real` boolean gate emitted **inline** (`assertZero`, not `=== 0`) so the `enabled = is_real`
  -- selector is visible to `ConstraintsHold.Shallow` — required for the chip to be a `VmTables` table.
  assertZero (input.is_real * (input.is_real - 1))
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
  -- The combined selector `sum` (= the byte-pull gate) is boolean-gated **inline** (`assertZero`, not
  -- `=== 0`) so it is visible to `ConstraintsHold.Shallow`, discharging the off-gate byte-pull
  -- `Requirements` without keeping `byteChannel` in `channelsWithRequirements`.
  assertZero (sum * (sum - 1))
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
  localLength_eq := by simp +arith [circuit_norm, main, Readers.ALUTypeReader.circuit, Readers.CPUState.circuit, U16MSBOperation.circuit, Readers.RegisterWrite.circuit]
  subcircuitsConsistent := by simp only [circuit_norm, main, Readers.ALUTypeReader.circuit, Readers.CPUState.circuit, U16MSBOperation.circuit, Readers.RegisterWrite.circuit]; try omega
  -- `programChannel` joins the byte guarantee propagated up from `ALUTypeReader`'s program **pull** (W11 flip);
  -- `memoryChannel` joins from `ALUTypeReader`'s memory read **pulls** (W11 memory flip). The `RegisterWrite`
  -- op_a write push owes a memory requirement (declared in `circuit.channelsWithRequirements`), not a guarantee.
  channelsWithGuarantees := [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]
  channelsLawful := by simp [circuit_norm, main, Readers.ALUTypeReader.circuit, Readers.CPUState.circuit, U16MSBOperation.circuit, Readers.RegisterWrite.circuit]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 37 := rfl

/-! ## Pure-field result-word range (`isU64 a`) helpers for the op_a `RegisterWrite` push

The W11 Option-B memory flip composes `RegisterWrite` *after* the shift placement; its push owes
`isU64` of the placed result word `a`. These pure-field lemmas range-check the placed limbs from the
`e14`/`e13`-gated placement asserts and the per-limb atomic bounds (each `a_i` is `0`, a `limb_result`
entry, a sign-fill, or `msb·65535`). Shared by `isU64_sound` and all four `Soundness/<Op>.lean` tails. -/

set_option linter.unusedSectionVars false in
/-- **SRL/SRA result range** (`e14 = is_srl + is_sra = 1`). From the one-hot byte-shift selectors
(`su_k` boolean, `Σ su_k = 1`), the 16 `e14`-gated placement asserts, and the per-limb atomic bounds
(`lr0`/`lr1`/`lr2`, the sign-fill `lr3f = limb_result[3] + sraFill`, and `bmsbFill`), every result limb
is a `u16`. -/
lemma srl_sra_a_isU64 {e14 a0 a1 a2 a3 su0 su1 su2 su3 lr0 lr1 lr2 lr3f bmsbFill : ZMod p}
    (he14 : e14 = 1)
    (hsu0b : su0 = 0 ∨ su0 = 1) (hsu1b : su1 = 0 ∨ su1 = 1) (hsu2b : su2 = 0 ∨ su2 = 1)
    (hsum : su0 + su1 + su2 + su3 = 1)
    (hb0 : lr0.val < 2 ^ 16) (hb1 : lr1.val < 2 ^ 16) (hb2 : lr2.val < 2 ^ 16)
    (hbf : lr3f.val < 2 ^ 16) (hbm : bmsbFill.val < 2 ^ 16)
    (h0 : e14 * (su0 * (a0 - lr0)) = 0) (h1 : e14 * (su0 * (a1 - lr1)) = 0)
    (h2 : e14 * (su0 * (a2 - lr2)) = 0) (h3 : e14 * (su0 * (a3 - lr3f)) = 0)
    (h4 : e14 * (su1 * (a0 - lr1)) = 0) (h5 : e14 * (su1 * (a1 - lr2)) = 0)
    (h6 : e14 * (su1 * (a2 - lr3f)) = 0) (h7 : e14 * (su1 * (a3 - bmsbFill)) = 0)
    (h8 : e14 * (su2 * (a0 - lr2)) = 0) (h9 : e14 * (su2 * (a1 - lr3f)) = 0)
    (h10 : e14 * (su2 * (a2 - bmsbFill)) = 0) (h11 : e14 * (su2 * (a3 - bmsbFill)) = 0)
    (h12 : e14 * (su3 * (a0 - lr3f)) = 0) (h13 : e14 * (su3 * (a1 - bmsbFill)) = 0)
    (h14 : e14 * (su3 * (a2 - bmsbFill)) = 0) (h15 : e14 * (su3 * (a3 - bmsbFill)) = 0) :
    a0.val < 2 ^ 16 ∧ a1.val < 2 ^ 16 ∧ a2.val < 2 ^ 16 ∧ a3.val < 2 ^ 16 := by
  subst he14
  simp only [one_mul] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  rcases hsu0b with e0 | e0
  · rcases hsu1b with e1 | e1
    · rcases hsu2b with e2 | e2
      · have e3 : su3 = 1 := by rw [e0, e1, e2] at hsum; linear_combination hsum
        rw [e3, one_mul] at h12 h13 h14 h15
        exact ⟨by rw [sub_eq_zero.mp h12]; exact hbf, by rw [sub_eq_zero.mp h13]; exact hbm,
          by rw [sub_eq_zero.mp h14]; exact hbm, by rw [sub_eq_zero.mp h15]; exact hbm⟩
      · rw [e2, one_mul] at h8 h9 h10 h11
        exact ⟨by rw [sub_eq_zero.mp h8]; exact hb2, by rw [sub_eq_zero.mp h9]; exact hbf,
          by rw [sub_eq_zero.mp h10]; exact hbm, by rw [sub_eq_zero.mp h11]; exact hbm⟩
    · rw [e1, one_mul] at h4 h5 h6 h7
      exact ⟨by rw [sub_eq_zero.mp h4]; exact hb1, by rw [sub_eq_zero.mp h5]; exact hb2,
        by rw [sub_eq_zero.mp h6]; exact hbf, by rw [sub_eq_zero.mp h7]; exact hbm⟩
  · rw [e0, one_mul] at h0 h1 h2 h3
    exact ⟨by rw [sub_eq_zero.mp h0]; exact hb0, by rw [sub_eq_zero.mp h1]; exact hb1,
      by rw [sub_eq_zero.mp h2]; exact hb2, by rw [sub_eq_zero.mp h3]; exact hbf⟩

set_option linter.unusedSectionVars false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- **SRLW/SRAW result range** (`e13 = is_srlw + is_sraw = 1`). The byte shift is `cb4 ∈ {0,1}` (so only
`su0`/`su1` are hot); `a0`/`a1` come from the low-two placement asserts (`lr0`, the sign-fill `lr1f`,
`bmsbFill`); `a2 = a3 = srwmsb·65535` (the de-gated word sign fill). The `srw_msb` bit is supplied by
`hsrw_of` (the `U16MSB` gadget, which needs the just-derived `a1 < 2^16`). Every result limb is a `u16`. -/
lemma srlw_sraw_a_isU64 {e13 cb4 a0 a1 a2 a3 su0 su1 su2 su3 lr0 lr1f bmsbFill srwmsb : ZMod p}
    (he13 : e13 = 1) (hcb4 : cb4 = 0 ∨ cb4 = 1)
    (hs0sel : su0 * (cb4 - 0) = 0) (hs1sel : su1 * (cb4 - 1) = 0)
    (hs2sel : su2 * (cb4 - 2) = 0) (hs3sel : su3 * (cb4 - 3) = 0)
    (hsum : su0 + su1 + su2 + su3 = 1)
    (hb0 : lr0.val < 2 ^ 16) (hb1f : lr1f.val < 2 ^ 16) (hbm : bmsbFill.val < 2 ^ 16)
    (hsrw_of : a1.val < 2 ^ 16 → srwmsb = 0 ∨ srwmsb = 1)
    (hw0 : e13 * (su0 * (a0 - lr0)) = 0) (hw1 : e13 * (su0 * (a1 - lr1f)) = 0)
    (hw2 : e13 * (su1 * (a0 - lr1f)) = 0) (hw3 : e13 * (su1 * (a1 - bmsbFill)) = 0)
    (hw4 : e13 * (a2 - srwmsb * 65535) = 0) (hw5 : e13 * (a3 - srwmsb * 65535) = 0) :
    a0.val < 2 ^ 16 ∧ a1.val < 2 ^ 16 ∧ a2.val < 2 ^ 16 ∧ a3.val < 2 ^ 16 := by
  subst he13
  simp only [one_mul] at hw0 hw1 hw2 hw3 hw4 hw5
  have ha2 : a2 = srwmsb * 65535 := sub_eq_zero.mp hw4
  have ha3 : a3 = srwmsb * 65535 := sub_eq_zero.mp hw5
  have hp : 2 ^ 17 < p := Fact.out
  have hv2 : (2 : ZMod p).val = 2 := val_2_zmod_p
  have hv3 : (3 : ZMod p).val = 3 := by
    rw [show (3 : ZMod p) = ((3 : ℕ) : ZMod p) from by push_cast; rfl]
    exact ZMod.val_natCast_of_lt (by omega)
  have n2 : (2 : ZMod p) ≠ 0 := fun h => by rw [h, ZMod.val_zero] at hv2; omega
  have n3 : (3 : ZMod p) ≠ 0 := fun h => by rw [h, ZMod.val_zero] at hv3; omega
  have key : a0.val < 2 ^ 16 ∧ a1.val < 2 ^ 16 := by
    rcases hcb4 with h4 | h4
    · rw [h4] at hs1sel hs2sel hs3sel
      have hs1 : su1 = 0 := by
        have hh := hs1sel; simp at hh; first | exact hh | exact hh.resolve_right (by norm_num [n2])
      have hs2 : su2 = 0 := by
        have hh := hs2sel; simp at hh; first | exact hh | exact hh.resolve_right (by norm_num [n2])
      have hs3 : su3 = 0 := by
        have hh := hs3sel; simp at hh; first | exact hh | exact hh.resolve_right (by norm_num [n3])
      have hs0 : su0 = 1 := by rw [hs1, hs2, hs3] at hsum; linear_combination hsum
      rw [hs0, one_mul] at hw0 hw1
      exact ⟨by rw [sub_eq_zero.mp hw0]; exact hb0, by rw [sub_eq_zero.mp hw1]; exact hb1f⟩
    · rw [h4] at hs0sel hs2sel hs3sel
      have hs0 : su0 = 0 := by
        have hh := hs0sel; simp at hh; first | exact hh | exact hh.resolve_right (by norm_num [n2])
      have hs2 : su2 = 0 := by
        have hh := hs2sel; simp at hh; first | exact hh | exact hh.resolve_right (by norm_num [n2])
      have hs3 : su3 = 0 := by
        have hh := hs3sel; simp at hh; first | exact hh | exact hh.resolve_right (by norm_num [n2])
      have hs1 : su1 = 1 := by rw [hs0, hs2, hs3] at hsum; linear_combination hsum
      rw [hs1, one_mul] at hw2 hw3
      exact ⟨by rw [sub_eq_zero.mp hw2]; exact hb1f, by rw [sub_eq_zero.mp hw3]; exact hbm⟩
  obtain ⟨ha0, ha1⟩ := key
  have hsrwfill : (srwmsb * 65535).val < 2 ^ 16 := by
    rcases hsrw_of ha1 with h | h <;> rw [h]
    · rw [zero_mul, ZMod.val_zero]; norm_num
    · rw [one_mul, show ((65535 : ZMod p)) = ((65535 : ℕ) : ZMod p) from by push_cast; rfl,
        ZMod.val_natCast_of_lt (by omega)]; norm_num
  exact ⟨ha0, ha1, by rw [ha2]; exact hsrwfill, by rw [ha3]; exact hsrwfill⟩

/-- **Result range-check.** On a variant-active row (`sum = is_srl + is_sra + is_srlw + is_sraw = 1`, SP1's
`is_real`, `sr/mod.rs:335`) the committed result word `cols.a` is `U64`. This is the obligation the op_a
write `RegisterWrite` push owes (Option B memory flip): the shift result is range-checked exactly when a
variant fires, so the push's `isU64 a` requirement is sound on those rows. Proved as a standalone
`Soundness` (over the same `main`) so the four split per-variant `Soundness/<Op>.lean` files can each
discharge their `RegisterWrite` requirement via `(isU64_sound …).1` without re-deriving the bound. -/
def IsU64Spec (_ : Inputs (ZMod p)) (cols : ShiftRightCols (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw = 1 → Word.isU64 cols.a

set_option maxHeartbeats 16000000 in
/-- **Result range-check (callable lemma).** On a variant-active row
(`is_srl + is_sra + is_srlw + is_sraw = 1`, SP1's `is_real`) the committed result word `cols.a` is `U64`
— the obligation the op_a write `RegisterWrite` push owes (W11 Option B memory flip). Packaged as a plain
lemma over the destructured `h_holds` hypotheses so each split per-variant `Soundness/<Op>.lean` can
discharge its `RegisterWrite` requirement by applying it, mirroring green `ShiftLeftChip`'s `sll_a_isU64`. -/
lemma resultA_isU64
    (i₀ : ℕ) (env : Environment (ZMod p))
    {input_var_adapter_op_b_memory_prev_value : Word (Expression (ZMod p))}
    {input_adapter_op_b_memory_prev_value : Word (ZMod p)}
    (h_obmap : Vector.map (Expression.eval env) input_var_adapter_op_b_memory_prev_value = input_adapter_op_b_memory_prev_value)
    (h_rs1U : input_adapter_op_b_memory_prev_value.isU64)
    (h_msb1 : U16MSBOperation.circuit.Assumptions { a := Expression.eval env input_var_adapter_op_b_memory_prev_value[3], cols := { msb := env.get (i₀ + 4) }, is_real := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) } → U16MSBOperation.circuit.Spec { a := Expression.eval env input_var_adapter_op_b_memory_prev_value[3], cols := { msb := env.get (i₀ + 4) }, is_real := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) })
    (h_msb3 : U16MSBOperation.circuit.Assumptions { a := env.get (i₀ + 1), cols := { msb := env.get (i₀ + 4 + 1) }, is_real := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3) } → U16MSBOperation.circuit.Spec { a := env.get (i₀ + 1), cols := { msb := env.get (i₀ + 4 + 1) }, is_real := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3) })
    (h_srl_b : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + -1) = 0)
    (h_sra_b : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) + -1) = 0)
    (h_srlw_b : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + -1) = 0)
    (h_sraw_b : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3) + -1) = 0)
    (h_sum_b : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3) + -1) = 0)
    (h_b0 : env.get (i₀ + 4 + 1 + 1) * (env.get (i₀ + 4 + 1 + 1) + -1) = 0)
    (h_b1 : env.get (i₀ + 4 + 1 + 1 + 1) * (env.get (i₀ + 4 + 1 + 1 + 1) + -1) = 0)
    (h_b2 : env.get (i₀ + 4 + 1 + 1 + 2) * (env.get (i₀ + 4 + 1 + 1 + 2) + -1) = 0)
    (h_b3 : env.get (i₀ + 4 + 1 + 1 + 3) * (env.get (i₀ + 4 + 1 + 1 + 3) + -1) = 0)
    (h_b4 : env.get (i₀ + 4 + 1 + 1 + 4) * (env.get (i₀ + 4 + 1 + 1 + 4) + -1) = 0)
    (h_s0w : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4) * (env.get (i₀ + 4 + 1 + 1 + 4) + env.get (i₀ + 4 + 1 + 1 + 5) * 2 * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1))) = 0)
    (h_s0b : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4) + -1) = 0)
    (h_s1w : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 1) * (env.get (i₀ + 4 + 1 + 1 + 4) + env.get (i₀ + 4 + 1 + 1 + 5) * 2 * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) + -1) = 0)
    (h_s1b : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 1) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 1) + -1) = 0)
    (h_s2w : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 2) * (env.get (i₀ + 4 + 1 + 1 + 4) + env.get (i₀ + 4 + 1 + 1 + 5) * 2 * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) + -2) = 0)
    (h_s2b : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 2) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 2) + -1) = 0)
    (h_s3w : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 3) * (env.get (i₀ + 4 + 1 + 1 + 4) + env.get (i₀ + 4 + 1 + 1 + 5) * 2 * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) + -3) = 0)
    (h_onehot : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 1) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 3) + -1) = 0)
    (h_v01 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 2) + -((1 + -env.get (i₀ + 4 + 1 + 1) + 1) * 2 * ((1 + -env.get (i₀ + 4 + 1 + 1 + 1)) * 3 + 1)) = 0)
    (h_v012 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 1) + -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 2) * ((1 + -env.get (i₀ + 4 + 1 + 1 + 2)) * 15 + 1)) = 0)
    (h_v0123 : env.get (i₀ + 4 + 1 + 1 + 6 + 1) + -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 1) * ((1 + -env.get (i₀ + 4 + 1 + 1 + 3)) * 255 + 1)) = 0)
    (h_split2 : Expression.eval env input_var_adapter_op_b_memory_prev_value[2] * env.get (i₀ + 4 + 1 + 1 + 6 + 1) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) + -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 2) * 65536 + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 2) * env.get (i₀ + 4 + 1 + 1 + 6 + 1)) = 0)
    (h_lr0 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4) + -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 1) * env.get (i₀ + 4 + 1 + 1 + 6 + 1)) = 0)
    (h_lr1 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 1) + -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 1) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 2) * env.get (i₀ + 4 + 1 + 1 + 6 + 1)) = 0)
    (h_lr2 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 2) + -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 3) * env.get (i₀ + 4 + 1 + 1 + 6 + 1)) = 0)
    (h_lr3 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 3) + -env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 3) = 0)
    (h_smv : env.get (i₀ + 4 + 1 + 1 + 6) + -(env.get (i₀ + 4) * env.get (i₀ + 4 + 1 + 1 + 6 + 1)) = 0)
    (h_o0 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4) * (env.get i₀ + -env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4))) = 0)
    (h_o1 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4) * (env.get (i₀ + 1) + -env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 1))) = 0)
    (h_o2 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4) * (env.get (i₀ + 2) + -env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 2))) = 0)
    (h_o3 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4) * (env.get (i₀ + 3) + -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 3) + (env.get (i₀ + 4) * 65536 + -env.get (i₀ + 4 + 1 + 1 + 6))))) = 0)
    (h_o4 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 1) * (env.get i₀ + -env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 1))) = 0)
    (h_o5 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 1) * (env.get (i₀ + 1) + -env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 2))) = 0)
    (h_o6 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 1) * (env.get (i₀ + 2) + -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 3) + (env.get (i₀ + 4) * 65536 + -env.get (i₀ + 4 + 1 + 1 + 6))))) = 0)
    (h_o7 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 1) * (env.get (i₀ + 3) + -(env.get (i₀ + 4) * 65535))) = 0)
    (h_o8 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 2) * (env.get i₀ + -env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 2))) = 0)
    (h_o9 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 2) * (env.get (i₀ + 1) + -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 3) + (env.get (i₀ + 4) * 65536 + -env.get (i₀ + 4 + 1 + 1 + 6))))) = 0)
    (h_o10 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 2) * (env.get (i₀ + 2) + -(env.get (i₀ + 4) * 65535))) = 0)
    (h_o11 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 2) * (env.get (i₀ + 3) + -(env.get (i₀ + 4) * 65535))) = 0)
    (h_o12 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 3) * (env.get i₀ + -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 3) + (env.get (i₀ + 4) * 65536 + -env.get (i₀ + 4 + 1 + 1 + 6))))) = 0)
    (h_o13 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 3) * (env.get (i₀ + 1) + -(env.get (i₀ + 4) * 65535))) = 0)
    (h_o14 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 3) * (env.get (i₀ + 2) + -(env.get (i₀ + 4) * 65535))) = 0)
    (h_o15 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 3) * (env.get (i₀ + 3) + -(env.get (i₀ + 4) * 65535))) = 0)
    (h_w0 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4) * (env.get i₀ + -env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4))) = 0)
    (h_w1 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4) * (env.get (i₀ + 1) + -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 1) + (env.get (i₀ + 4) * 65536 + -env.get (i₀ + 4 + 1 + 1 + 6))))) = 0)
    (h_w2 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 1) * (env.get i₀ + -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 1) + (env.get (i₀ + 4) * 65536 + -env.get (i₀ + 4 + 1 + 1 + 6))))) = 0)
    (h_w3 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 1) * (env.get (i₀ + 1) + -(env.get (i₀ + 4) * 65535))) = 0)
    (h_w4 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) * (env.get (i₀ + 2) + -(env.get (i₀ + 4 + 1) * 65535)) = 0)
    (h_w5 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) * (env.get (i₀ + 3) + -(env.get (i₀ + 4 + 1) * 65535)) = 0)
    (h_byte1 : -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) = -1 → byteChannel.Guarantees { opcode := 6, a := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3), b := env.get (i₀ + 4 + 1 + 1) * 1 + env.get (i₀ + 4 + 1 + 1 + 1) * 2 + env.get (i₀ + 4 + 1 + 1 + 2) * 4 + env.get (i₀ + 4 + 1 + 1 + 3) * 8, c := 0 } env.data)
    (h_byte2 : -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) = -1 → byteChannel.Guarantees { opcode := 6, a := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4), b := 16 + -(env.get (i₀ + 4 + 1 + 1) * 1 + env.get (i₀ + 4 + 1 + 1 + 1) * 2 + env.get (i₀ + 4 + 1 + 1 + 2) * 4 + env.get (i₀ + 4 + 1 + 1 + 3) * 8), c := 0 } env.data)
    (h_byte3 : -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) = -1 → byteChannel.Guarantees { opcode := 6, a := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 1), b := env.get (i₀ + 4 + 1 + 1) * 1 + env.get (i₀ + 4 + 1 + 1 + 1) * 2 + env.get (i₀ + 4 + 1 + 1 + 2) * 4 + env.get (i₀ + 4 + 1 + 1 + 3) * 8, c := 0 } env.data)
    (h_byte4 : -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) = -1 → byteChannel.Guarantees { opcode := 6, a := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 1), b := 16 + -(env.get (i₀ + 4 + 1 + 1) * 1 + env.get (i₀ + 4 + 1 + 1 + 1) * 2 + env.get (i₀ + 4 + 1 + 1 + 2) * 4 + env.get (i₀ + 4 + 1 + 1 + 3) * 8), c := 0 } env.data)
    (h_byte5 : -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) = -1 → byteChannel.Guarantees { opcode := 6, a := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 2), b := env.get (i₀ + 4 + 1 + 1) * 1 + env.get (i₀ + 4 + 1 + 1 + 1) * 2 + env.get (i₀ + 4 + 1 + 1 + 2) * 4 + env.get (i₀ + 4 + 1 + 1 + 3) * 8, c := 0 } env.data)
    (h_byte6 : -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) = -1 → byteChannel.Guarantees { opcode := 6, a := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 2), b := 16 + -(env.get (i₀ + 4 + 1 + 1) * 1 + env.get (i₀ + 4 + 1 + 1 + 1) * 2 + env.get (i₀ + 4 + 1 + 1 + 2) * 4 + env.get (i₀ + 4 + 1 + 1 + 3) * 8), c := 0 } env.data)
    (h_byte7 : -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) = -1 → byteChannel.Guarantees { opcode := 6, a := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 3), b := env.get (i₀ + 4 + 1 + 1) * 1 + env.get (i₀ + 4 + 1 + 1 + 1) * 2 + env.get (i₀ + 4 + 1 + 1 + 2) * 4 + env.get (i₀ + 4 + 1 + 1 + 3) * 8, c := 0 } env.data)
    (h_byte8 : -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) = -1 → byteChannel.Guarantees { opcode := 6, a := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 3), b := 16 + -(env.get (i₀ + 4 + 1 + 1) * 1 + env.get (i₀ + 4 + 1 + 1 + 1) * 2 + env.get (i₀ + 4 + 1 + 1 + 2) * 4 + env.get (i₀ + 4 + 1 + 1 + 3) * 8), c := 0 } env.data)
    :
    env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3) = 1 →
      Word.isU64 (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + i }) : Word (ZMod p)) := by
  -- Reduce the committed result column `cols.a` to its four `env.get`s.
  have hcolsa : (Vector.map (Expression.eval env)
        (Vector.mapRange 4 fun i => var { index := i₀ + i }) : Word (ZMod p))
      = #v[env.get i₀, env.get (i₀ + 1), env.get (i₀ + 2), env.get (i₀ + 3)] := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    interval_cases i <;> rfl
  -- **The result range-check.** On a variant-active row the four output limbs are each `< 2^16`. Proved
  -- once here; `spec`/`regwriteA` lift it to `isU64 cols.a` and `msb3A` reads off the `a[1]` bound.
  have hbounds :
      env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) +
            env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) +
            env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) +
          env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3) = 1 →
        (env.get i₀).val < 2 ^ 16 ∧ (env.get (i₀ + 1)).val < 2 ^ 16 ∧
          (env.get (i₀ + 2)).val < 2 ^ 16 ∧ (env.get (i₀ + 3)).val < 2 ^ 16 := by
    intro hsum1
    have hp17 : 2 ^ 17 < p := Fact.out
    -- The variant flag-sum is 1, so the nine byte-pull guarantees fire (gated by `-(flag-sum) = -1`).
    have hsumneg : -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) +
          env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) +
          env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) +
        env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) = -1 := by rw [hsum1]
    have hbyte_fact : ∀ {v w : ZMod p},
        (-(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) +
            env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) +
            env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) +
            env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) = -1 →
          byteChannel.Guarantees (⟨6, v, w, 0⟩ : ByteRow (ZMod p)) env.data) → v.val < 2 ^ w.val := by
      intro v w hb
      exact byteRowSpec_range_val (hb hsumneg)
    have lt_ll0 := hbyte_fact h_byte1
    have lt_lh0 := hbyte_fact h_byte2
    have lt_ll1 := hbyte_fact h_byte3
    have lt_lh1 := hbyte_fact h_byte4
    have lt_ll2 := hbyte_fact h_byte5
    have lt_lh2 := hbyte_fact h_byte6
    have lt_ll3 := hbyte_fact h_byte7
    have lt_lh3 := hbyte_fact h_byte8
    have b_cb0 := bool_of_mul_pred h_b0
    have b_cb1 := bool_of_mul_pred h_b1
    have b_cb2 := bool_of_mul_pred h_b2
    have b_cb3 := bool_of_mul_pred h_b3
    -- The three inverted `v_*` power encodings, in `limb_result_lt`'s form.
    have eq_v01 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 2)
        = (1 + -env.get (i₀ + 4 + 1 + 1) + 1) * 2 * ((1 + -env.get (i₀ + 4 + 1 + 1 + 1)) * 3 + 1) := by
      linear_combination h_v01
    have eq_v012 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 1)
        = env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 2) * ((1 + -env.get (i₀ + 4 + 1 + 1 + 2)) * 15 + 1) := by
      linear_combination h_v012
    have eq_v0123 : env.get (i₀ + 4 + 1 + 1 + 6 + 1)
        = env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 1) * ((1 + -env.get (i₀ + 4 + 1 + 1 + 3)) * 255 + 1) := by
      linear_combination h_v0123
    -- Bridge the byte-pull range facts to the `limb_result_lt`/`sign_fill_lt` exponent form.
    rw [cb4sum_natCast] at lt_ll0 lt_ll1 lt_ll2 lt_ll3
    rw [cb4sum_sub_natCast] at lt_lh0 lt_lh1 lt_lh2 lt_lh3
    -- limb_result reassemblies + `sra_msb_v0123` witness.
    have eq_lr0 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4)
        = env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4)
          + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 1) * env.get (i₀ + 4 + 1 + 1 + 6 + 1) := by
      linear_combination h_lr0
    have eq_lr1 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 1)
        = env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 1)
          + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 2) * env.get (i₀ + 4 + 1 + 1 + 6 + 1) := by
      linear_combination h_lr1
    have eq_lr2 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 2)
        = env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 2)
          + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 3) * env.get (i₀ + 4 + 1 + 1 + 6 + 1) := by
      linear_combination h_lr2
    have eq_lr3 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 3)
        = env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 3) := by linear_combination h_lr3
    have eq_smv : env.get (i₀ + 4 + 1 + 1 + 6)
        = env.get (i₀ + 4) * env.get (i₀ + 4 + 1 + 1 + 6 + 1) := by linear_combination h_smv
    -- The byte-shift one-hot of the `shift_u16` selectors.
    have honehot1 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4) +
          env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 1) +
          env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 2) +
        env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 3) = 1 := by
      have hh := h_onehot; rw [hsum1] at hh; linear_combination hh
    -- `b_msb ∈ {0,1}` unconditionally (the `U16MSBOperation` gadget's ungated booleanness).
    have hb3e : Expression.eval env input_var_adapter_op_b_memory_prev_value[3]
        = input_adapter_op_b_memory_prev_value[3] := by rw [← h_obmap]; simp only [Vector.getElem_map]
    have hb2e : Expression.eval env input_var_adapter_op_b_memory_prev_value[2]
        = input_adapter_op_b_memory_prev_value[2] := by rw [← h_obmap]; simp only [Vector.getElem_map]
    have hbmsb_bool : env.get (i₀ + 4) = 0 ∨ env.get (i₀ + 4) = 1 :=
      (h_msb1 ⟨fun _ => by rw [hb3e]; exact h_rs1U 3, bool_of_mul_pred h_sra_b⟩).1
    -- The four `limb_result` atomic `u16` bounds (`lr0`/`lr1`/`lr2` via `limb_result_lt`; the bare high
    -- limbs `hl1`/`hl3` via the `ll = 0` specialisation).
    have B_hl1 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 1)).val < 2 ^ 16 := by
      have h := ShiftRightMath.limb_result_lt (hl := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 1))
        (ll := 0) b_cb0 b_cb1 b_cb2 b_cb3 eq_v01 eq_v012 eq_v0123 lt_lh1 (by rw [ZMod.val_zero]; positivity)
      rw [show (2 : ℕ) ^ 16 = 65536 from by norm_num]; simpa using h
    have B_hl3 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 3)).val < 2 ^ 16 := by
      have h := ShiftRightMath.limb_result_lt (hl := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 3))
        (ll := 0) b_cb0 b_cb1 b_cb2 b_cb3 eq_v01 eq_v012 eq_v0123 lt_lh3 (by rw [ZMod.val_zero]; positivity)
      rw [show (2 : ℕ) ^ 16 = 65536 from by norm_num]; simpa using h
    have B_lr0 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4)).val < 2 ^ 16 := by
      rw [show (2 : ℕ) ^ 16 = 65536 from by norm_num, eq_lr0]
      exact ShiftRightMath.limb_result_lt b_cb0 b_cb1 b_cb2 b_cb3 eq_v01 eq_v012 eq_v0123 lt_lh0 lt_ll1
    have B_lr1 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 1)).val < 2 ^ 16 := by
      rw [show (2 : ℕ) ^ 16 = 65536 from by norm_num, eq_lr1]
      exact ShiftRightMath.limb_result_lt b_cb0 b_cb1 b_cb2 b_cb3 eq_v01 eq_v012 eq_v0123 lt_lh1 lt_ll2
    have B_lr2 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 2)).val < 2 ^ 16 := by
      rw [show (2 : ℕ) ^ 16 = 65536 from by norm_num, eq_lr2]
      exact ShiftRightMath.limb_result_lt b_cb0 b_cb1 b_cb2 b_cb3 eq_v01 eq_v012 eq_v0123 lt_lh2 lt_ll3
    have B_bmsbFill : (env.get (i₀ + 4) * 65535).val < 2 ^ 16 := by
      rcases hbmsb_bool with h | h <;> rw [h]
      · rw [zero_mul, ZMod.val_zero]; norm_num
      · rw [one_mul, show ((65535 : ZMod p)) = ((65535 : ℕ) : ZMod p) from by push_cast; rfl,
          ZMod.val_natCast_of_lt (by omega)]; norm_num
    -- The sign-fill `lr3 + (b_msb·65536 - sra_msb_v0123)` is `u16` (`lr3 = hl3`; `b_msb = 0 ⇒ hl3`,
    -- `b_msb = 1 ⇒ hl3 + (65536 - v0123)` via `sign_fill_lt`).
    have B_lr3_fill : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 3)
        + (env.get (i₀ + 4) * 65536 - env.get (i₀ + 4 + 1 + 1 + 6))).val < 2 ^ 16 := by
      rcases hbmsb_bool with h0 | h1
      · rw [eq_lr3, h0, show env.get (i₀ + 4 + 1 + 1 + 6) = 0 from by rw [eq_smv, h0, zero_mul]]
        simp only [zero_mul, sub_zero, add_zero]; exact B_hl3
      · rw [eq_lr3, h1, show env.get (i₀ + 4 + 1 + 1 + 6) = env.get (i₀ + 4 + 1 + 1 + 6 + 1) from by
            rw [eq_smv, h1, one_mul],
          show (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 3) + ((1 : ZMod p) * 65536
                - env.get (i₀ + 4 + 1 + 1 + 6 + 1)))
              = (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 3)
                + (((65536 : ℕ) : ZMod p) - env.get (i₀ + 4 + 1 + 1 + 6 + 1))) from by push_cast; ring,
          show (2 : ℕ) ^ 16 = 65536 from by norm_num]
        exact ShiftRightMath.sign_fill_lt b_cb0 b_cb1 b_cb2 b_cb3 eq_v01 eq_v012 eq_v0123 lt_lh3
    -- Dispatch on `e13 = is_srlw + is_sraw ∈ {0,1}`; `e14 = 1` (SRL/SRA) or `e13 = 1` (SRLW/SRAW).
    rcases pair_flag (bool_of_mul_pred h_srl_b) (bool_of_mul_pred h_sra_b) (bool_of_mul_pred h_srlw_b)
      (bool_of_mul_pred h_sraw_b) (bool_of_mul_pred h_sum_b) with he13 | he13
    · -- `e13 = 0 ⇒ e14 = 1` (SRL/SRA): the 16 `e14`-gated placement asserts + atomic bounds.
      have he14 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4)
          + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) = 1 := by
        linear_combination hsum1 - he13
      simp only [← sub_eq_add_neg] at h_o0 h_o1 h_o2 h_o3 h_o4 h_o5 h_o6 h_o7 h_o8 h_o9 h_o10 h_o11 h_o12 h_o13 h_o14 h_o15
      exact srl_sra_a_isU64 he14 (bool_of_mul_pred h_s0b) (bool_of_mul_pred h_s1b)
        (bool_of_mul_pred h_s2b) honehot1 B_lr0 B_lr1 B_lr2 B_lr3_fill B_bmsbFill
        h_o0 h_o1 h_o2 h_o3 h_o4 h_o5 h_o6 h_o7 h_o8 h_o9 h_o10 h_o11 h_o12 h_o13 h_o14 h_o15
    · -- `e13 = 1` (SRLW/SRAW): the low-two placement + the de-gated `a2 = a3 = srw_msb·65535`.
      have he14_0 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4)
          + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) = 0 := by
        linear_combination hsum1 - he13
      -- On a word row the limb-2 split is de-gated (`e14 = 0`), forcing `ll2 = 0`.
      have h_split2_dec : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 2) * 65536
          + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 2) * env.get (i₀ + 4 + 1 + 1 + 6 + 1) = 0 := by
        have h := h_split2; rw [hb2e, he14_0] at h; linear_combination -h
      obtain ⟨-, h_ll2_0⟩ := ShiftRightMath.higher_lower_zero b_cb0 b_cb1 b_cb2 b_cb3 eq_v01 eq_v012
        eq_v0123 lt_lh2 lt_ll2 h_split2_dec
      -- The sign-fill `lr1 + (b_msb·65536 - sra_msb_v0123)` (with `ll2 = 0`, so `lr1 = hl1`) is `u16`.
      have B_lr1_fill : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 1)
          + (env.get (i₀ + 4) * 65536 - env.get (i₀ + 4 + 1 + 1 + 6))).val < 2 ^ 16 := by
        rw [eq_lr1, h_ll2_0, zero_mul, add_zero]
        rcases hbmsb_bool with h0 | h1
        · rw [h0, show env.get (i₀ + 4 + 1 + 1 + 6) = 0 from by rw [eq_smv, h0, zero_mul]]
          simp only [zero_mul, sub_zero, add_zero]; exact B_hl1
        · rw [h1, show env.get (i₀ + 4 + 1 + 1 + 6) = env.get (i₀ + 4 + 1 + 1 + 6 + 1) from by
              rw [eq_smv, h1, one_mul],
            show (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 1) + ((1 : ZMod p) * 65536
                  - env.get (i₀ + 4 + 1 + 1 + 6 + 1)))
                = (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 1)
                  + (((65536 : ℕ) : ZMod p) - env.get (i₀ + 4 + 1 + 1 + 6 + 1))) from by push_cast; ring,
            show (2 : ℕ) ^ 16 = 65536 from by norm_num]
          exact ShiftRightMath.sign_fill_lt b_cb0 b_cb1 b_cb2 b_cb3 eq_v01 eq_v012 eq_v0123 lt_lh1
      -- `srw_msb ∈ {0,1}` from the `srw_msb` gadget once `a[1] < 2^16` is in hand (supplied by the lemma).
      have hsrw_of : (env.get (i₀ + 1)).val < 2 ^ 16 → env.get (i₀ + 4 + 1) = 0 ∨ env.get (i₀ + 4 + 1) = 1 :=
        fun ha1 => (h_msb3 ⟨fun _ => by show (env.get (i₀ + 1)).val < 2 ^ 16; exact ha1, Or.inr he13⟩).1
      -- The `cb4` byte-shift selectors, de-gated to `e14 = 0`.
      have hs0sel : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4) * (env.get (i₀ + 4 + 1 + 1 + 4) - 0) = 0 := by
        have h := h_s0w; rw [he14_0] at h; linear_combination h
      have hs1sel : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 1) * (env.get (i₀ + 4 + 1 + 1 + 4) - 1) = 0 := by
        have h := h_s1w; rw [he14_0] at h; linear_combination h
      have hs2sel : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 2) * (env.get (i₀ + 4 + 1 + 1 + 4) - 2) = 0 := by
        have h := h_s2w; rw [he14_0] at h; linear_combination h
      have hs3sel : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 3) * (env.get (i₀ + 4 + 1 + 1 + 4) - 3) = 0 := by
        have h := h_s3w; rw [he14_0] at h; linear_combination h
      simp only [← sub_eq_add_neg] at h_w0 h_w1 h_w2 h_w3 h_w4 h_w5
      exact srlw_sraw_a_isU64 he13 (bool_of_mul_pred h_b4) hs0sel hs1sel hs2sel hs3sel honehot1
        B_lr0 B_lr1_fill B_bmsbFill hsrw_of h_w0 h_w1 h_w2 h_w3 h_w4 h_w5
  intro hsum1
  obtain ⟨c0, c1, c2, c3⟩ := hbounds hsum1
  rw [hcolsa]
  exact Word.isU64_of_cases c0 c1 c2 c3

end SP1Clean.ShiftRightChip
