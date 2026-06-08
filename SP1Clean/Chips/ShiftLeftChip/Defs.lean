import SP1Clean.Specs.Chip
import SP1Clean.Chips.ShiftLeftChip.Core
import SP1Clean.Operations.U16MSBOperation.Formal
import SP1Clean.Readers.CPUState
import SP1Clean.Readers.ALUTypeReader
import SP1Clean.Foundations.Channels
import SP1Clean.Extracted.ShiftLeftChip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The `ShiftLeft` chip row as a `GeneralFormalCircuit`

`SLL`/`SLLW`: SP1's shift logic (the six shift-amount bits `c_bits`, the `v_01/v_012/v_0123` power
encodings, the `shift_u16` byte-shift one-hot selector, the `lower_limb`/`higher_limb` bit-split, the
`limb_result` reassembly, and the SLLW MSB sign-extension) is inlined into
`Extracted/ShiftLeftChip.lean`'s `asserts`/`interactions` — no separate operation-level extraction.

`AssertSpec` / `InteractSpec` capture the structural meaning of SP1's two extracted constraint lists;
the semantic, flag-gated `Spec` (RV64 `sll`/`sllw` identity) is in `Specs/Chip.lean`.
`Faithful/ShiftLeftChip.lean` anchors both structural specs to SP1's extracted lists.

`main` composes `CPUState`/`ALUTypeReader`/`U16MSBOperation` sub-circuits, witnesses the shift column
block, and gates `is_real`. Soundness is proved; completeness is a deferred `sorry`. -/

namespace SP1Clean.ShiftLeftChip

open Circuit
open Extracted (ShiftLeftCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- The operands are 64-bit values, and equal to the offline-memory register readbacks. Lives here (not in
`Formal`) so the per-op `Soundness/<Op>.lean` split files can import it without a cycle through `Formal`. -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val ∧
  input.op_b_val = input.adapter.op_b_memory.prev_value ∧
  input.op_c_val = input.adapter.op_c_memory.prev_value

/-- **Assertion half** — the literal meaning of SP1's `ShiftLeftCols.asserts` *own* (inline) assertZero
list (everything past the composed `U16MSBOperation`/`CPUState`/`ALUTypeReader` sub-lists), stated as a
conjunction of `… = 0` field constraints over the committed columns. In order: the variant-flag
booleans + their sum-bound, the six `c_bits` booleans, the four `shift_u16` byte-selectors + booleans +
one-hot sum, the three `v_*` power encodings, the four `lower/higher_limb` bit-split equations, the four
`limb_result` reassembly equations, the SLL output-placement products, the SLLW output + `sllw_msb`
sign-fill, the immediate-consistency `is_sllw_imm` equation, and the `op_a_0` zeroing flag. -/
def AssertSpec (cols : ShiftLeftCols (ZMod p)) : Prop :=
  let sll := cols.is_sll; let sllw := cols.is_sllw
  let b0 := cols.c_bits[0]; let b1 := cols.c_bits[1]; let b2 := cols.c_bits[2]
  let b3 := cols.c_bits[3]; let b4 := cols.c_bits[4]; let b5 := cols.c_bits[5]
  let s0 := cols.shift_u16[0]; let s1 := cols.shift_u16[1]
  let s2 := cols.shift_u16[2]; let s3 := cols.shift_u16[3]
  let byteShift := b4 + b5 * 2 * sll
  -- variant flags
  (sll + sllw) * ((sll + sllw) - 1) = 0 ∧ sll * (sll - 1) = 0 ∧ sllw * (sllw - 1) = 0 ∧
  -- c_bits booleans
  b0 * (b0 - 1) = 0 ∧ b1 * (b1 - 1) = 0 ∧ b2 * (b2 - 1) = 0 ∧
  b3 * (b3 - 1) = 0 ∧ b4 * (b4 - 1) = 0 ∧ b5 * (b5 - 1) = 0 ∧
  -- shift_u16 byte-shift selectors + booleans
  s0 * (byteShift - 0) = 0 ∧ s0 * (s0 - 1) = 0 ∧
  s1 * (byteShift - 1) = 0 ∧ s1 * (s1 - 1) = 0 ∧
  s2 * (byteShift - 2) = 0 ∧ s2 * (s2 - 1) = 0 ∧
  s3 * (byteShift - 3) = 0 ∧ s3 * (s3 - 1) = 0 ∧
  (sll + sllw) * ((s0 + s1 + s2 + s3) - 1) = 0 ∧
  -- v_* power encodings
  cols.v_01 - (b0 + 1) * (b1 * 3 + 1) = 0 ∧
  cols.v_012 - cols.v_01 * (b2 * 15 + 1) = 0 ∧
  cols.v_0123 - cols.v_012 * (b3 * 255 + 1) = 0 ∧
  -- lower/higher limb bit-split
  cols.adapter.op_b_memory.prev_value[0] * cols.v_0123
    - (cols.higher_limb[0] * 65536 + cols.lower_limb[0] * cols.v_0123) = 0 ∧
  cols.adapter.op_b_memory.prev_value[1] * cols.v_0123
    - (cols.higher_limb[1] * 65536 + cols.lower_limb[1] * cols.v_0123) = 0 ∧
  cols.adapter.op_b_memory.prev_value[2] * cols.v_0123
    - (cols.higher_limb[2] * 65536 + cols.lower_limb[2] * cols.v_0123) = 0 ∧
  cols.adapter.op_b_memory.prev_value[3] * cols.v_0123
    - (cols.higher_limb[3] * 65536 + cols.lower_limb[3] * cols.v_0123) = 0 ∧
  -- limb_result reassembly
  cols.limb_result[0] - cols.lower_limb[0] * cols.v_0123 = 0 ∧
  cols.limb_result[1] - (cols.lower_limb[1] * cols.v_0123 + cols.higher_limb[0]) = 0 ∧
  cols.limb_result[2] - (cols.lower_limb[2] * cols.v_0123 + cols.higher_limb[1]) = 0 ∧
  cols.limb_result[3] - (cols.lower_limb[3] * cols.v_0123 + cols.higher_limb[2]) = 0 ∧
  -- SLL output placement (per byte-shift selector)
  sll * (s0 * (cols.a[0] - cols.limb_result[0])) = 0 ∧
  sll * (s0 * (cols.a[1] - cols.limb_result[1])) = 0 ∧
  sll * (s0 * (cols.a[2] - cols.limb_result[2])) = 0 ∧
  sll * (s0 * (cols.a[3] - cols.limb_result[3])) = 0 ∧
  sll * (s1 * cols.a[0]) = 0 ∧
  sll * (s1 * (cols.a[1] - cols.limb_result[0])) = 0 ∧
  sll * (s1 * (cols.a[2] - cols.limb_result[1])) = 0 ∧
  sll * (s1 * (cols.a[3] - cols.limb_result[2])) = 0 ∧
  sll * (s2 * cols.a[0]) = 0 ∧
  sll * (s2 * cols.a[1]) = 0 ∧
  sll * (s2 * (cols.a[2] - cols.limb_result[0])) = 0 ∧
  sll * (s2 * (cols.a[3] - cols.limb_result[1])) = 0 ∧
  sll * (s3 * cols.a[0]) = 0 ∧
  sll * (s3 * cols.a[1]) = 0 ∧
  sll * (s3 * cols.a[2]) = 0 ∧
  sll * (s3 * (cols.a[3] - cols.limb_result[0])) = 0 ∧
  -- SLLW output placement + MSB sign-fill
  sllw * (s0 * (cols.a[0] - cols.limb_result[0])) = 0 ∧
  sllw * (s0 * (cols.a[1] - cols.limb_result[1])) = 0 ∧
  sllw * (s1 * cols.a[0]) = 0 ∧
  sllw * (s1 * (cols.a[1] - cols.limb_result[0])) = 0 ∧
  sllw * (cols.sllw_msb.msb * 65535 - cols.a[2]) = 0 ∧
  sllw * (cols.sllw_msb.msb * 65535 - cols.a[3]) = 0 ∧
  -- immediate consistency + op_a_0 zeroing flag
  cols.is_sllw_imm - sllw * cols.adapter.imm_c = 0 ∧
  cols.adapter.op_a_0 = 0

/-- **Interaction half** — the literal meaning of SP1's `ShiftLeftCols.interactions` *own* byte-range
sends (gated by `gate = is_sll + is_sllw`): the shift-amount high bits `< 2^10`, and, per limb, the
`lower_limb` `< 2^(16 - bitShift)` and `higher_limb` `< 2^bitShift` ranges (`bitShift` = low four
shift-amount bits). Each send's meaning is `gate ≠ 0 → value.val < 2 ^ width.val` (`Range.constrain`). -/
def InteractSpec (cols : ShiftLeftCols (ZMod p)) : Prop :=
  let b0 := cols.c_bits[0]; let b1 := cols.c_bits[1]; let b2 := cols.c_bits[2]
  let b3 := cols.c_bits[3]; let b4 := cols.c_bits[4]; let b5 := cols.c_bits[5]
  let bitShift : ZMod p := b0 * 1 + b1 * 2 + b2 * 4 + b3 * 8
  let shamt : ZMod p := bitShift + b4 * 16 + b5 * 32
  let e32 : ZMod p := (cols.adapter.op_c_memory.prev_value[0] - shamt) * (64 : ZMod p)⁻¹
  let gate : ZMod p := cols.is_sll + cols.is_sllw
  (gate ≠ 0 → e32.val < 2 ^ (10 : ZMod p).val) ∧
  (gate ≠ 0 → cols.lower_limb[0].val < 2 ^ (16 - bitShift).val) ∧
  (gate ≠ 0 → cols.higher_limb[0].val < 2 ^ bitShift.val) ∧
  (gate ≠ 0 → cols.lower_limb[1].val < 2 ^ (16 - bitShift).val) ∧
  (gate ≠ 0 → cols.higher_limb[1].val < 2 ^ bitShift.val) ∧
  (gate ≠ 0 → cols.lower_limb[2].val < 2 ^ (16 - bitShift).val) ∧
  (gate ≠ 0 → cols.higher_limb[2].val < 2 ^ bitShift.val) ∧
  (gate ≠ 0 → cols.lower_limb[3].val < 2 ^ (16 - bitShift).val) ∧
  (gate ≠ 0 → cols.higher_limb[3].val < 2 ^ bitShift.val)

set_option maxHeartbeats 4000000 in
/-- Compose the threaded `CPUState`/`ALUTypeReader` reader blocks and the `U16MSBOperation` (`sllw_msb`)
gadget as Clean sub-assertions, **witness** the shift column block (the result `a`, the `c_bits`, the
`v_*` powers, the `shift_u16` selector, the `lower/higher_limb`/`limb_result` words, the `sllw_msb`),
thread the variant flags from `Inputs`, gate `is_real` (`= is_sll + is_sllw`), emit the inline shift
assertZero constraints (`AssertSpec`) and the nine `gate`-gated byte-range pulls (`InteractSpec`), and
assemble the extracted `ShiftLeftCols` struct. (The witness generators are still placeholder zeros — a
faithful `populate` is only needed for completeness, which is deferred; soundness ranges over every
satisfying assignment regardless of the generators.) -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var ShiftLeftCols (ZMod p)) := do
  let is_sll := input.is_sll; let is_sllw := input.is_sllw; let is_sllw_imm := input.is_sllw_imm
  let gate := is_sll + is_sllw
  assertion Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, gate⟩
  -- Honest-prover witness generators (`ShiftLeftCore.pop*`, SP1 `event_to_row`): every column is computed
  -- from the register read-backs `op_b_memory.prev_value` / `op_c_memory.prev_value`.
  let bw : ProverEnvironment (ZMod p) → Word (ZMod p) := fun env =>
    #v[env input.adapter.op_b_memory.prev_value[0], env input.adapter.op_b_memory.prev_value[1],
       env input.adapter.op_b_memory.prev_value[2], env input.adapter.op_b_memory.prev_value[3]]
  let cw : ProverEnvironment (ZMod p) → Word (ZMod p) := fun env =>
    #v[env input.adapter.op_c_memory.prev_value[0], env input.adapter.op_c_memory.prev_value[1],
       env input.adapter.op_c_memory.prev_value[2], env input.adapter.op_c_memory.prev_value[3]]
  let a ← witnessVector 4 (fun env => ShiftLeftCore.popA (bw env) (cw env) (env is_sll) (env is_sllw))
  let c_bits ← witnessVector 6 (fun env => ShiftLeftCore.popCbits (cw env))
  let v ← witnessVector 3 (fun env => ShiftLeftCore.popV (cw env))
  let shift_u16 ← witnessVector 4 (fun env => ShiftLeftCore.popShiftU16 (cw env) (env is_sll))
  let lower_limb ← witnessVector 4 (fun env => ShiftLeftCore.popLower (bw env) (cw env))
  let higher_limb ← witnessVector 4 (fun env => ShiftLeftCore.popHigher (bw env) (cw env))
  let limb_result ← witnessVector 4 (fun env => ShiftLeftCore.popLimbResult (bw env) (cw env))
  let sllw_msb ← witnessVector 1 (fun env => #v[ShiftLeftCore.popMsb (bw env) (cw env) (env is_sllw)])
  assertion U16MSBOperation.circuit ⟨a[1], ⟨sllw_msb[0]⟩, is_sllw⟩
  assertion Readers.ALUTypeReader.circuit
    ⟨input.adapter, gate, gate, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
     is_sll * 6 + is_sllw * 21, a[0], a[1], a[2], a[3]⟩
  input.is_real * (input.is_real - 1) === 0
  input.is_real - (is_sll + is_sllw) === 0
  -- shorthands for the committed column expressions (pure lets — no operations emitted)
  let b0 := c_bits[0]; let b1 := c_bits[1]; let b2 := c_bits[2]
  let b3 := c_bits[3]; let b4 := c_bits[4]; let b5 := c_bits[5]
  let s0 := shift_u16[0]; let s1 := shift_u16[1]; let s2 := shift_u16[2]; let s3 := shift_u16[3]
  let v01 := v[0]; let v012 := v[1]; let v0123 := v[2]
  let byteShift := b4 + b5 * 2 * is_sll
  let bitShift := b0 * 1 + b1 * 2 + b2 * 4 + b3 * 8
  let shamt := bitShift + b4 * 16 + b5 * 32
  let e32 := (input.adapter.op_c_memory.prev_value[0] - shamt) * Expression.const ((64 : ZMod p)⁻¹)
  -- ## The inline shift assertZero constraints (in `Extracted/ShiftLeftChip.lean` `asserts` order)
  -- variant flags
  (is_sll + is_sllw) * ((is_sll + is_sllw) - 1) === 0
  is_sll * (is_sll - 1) === 0
  is_sllw * (is_sllw - 1) === 0
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
  (is_sll + is_sllw) * ((s0 + s1 + s2 + s3) - 1) === 0
  -- v_* power encodings
  v01 - (b0 + 1) * (b1 * 3 + 1) === 0
  v012 - v01 * (b2 * 15 + 1) === 0
  v0123 - v012 * (b3 * 255 + 1) === 0
  -- lower/higher limb bit-split
  input.adapter.op_b_memory.prev_value[0] * v0123 - (higher_limb[0] * (65536 : Expression (ZMod p)) + lower_limb[0] * v0123) === 0
  input.adapter.op_b_memory.prev_value[1] * v0123 - (higher_limb[1] * (65536 : Expression (ZMod p)) + lower_limb[1] * v0123) === 0
  input.adapter.op_b_memory.prev_value[2] * v0123 - (higher_limb[2] * (65536 : Expression (ZMod p)) + lower_limb[2] * v0123) === 0
  input.adapter.op_b_memory.prev_value[3] * v0123 - (higher_limb[3] * (65536 : Expression (ZMod p)) + lower_limb[3] * v0123) === 0
  -- limb_result reassembly
  limb_result[0] - lower_limb[0] * v0123 === 0
  limb_result[1] - (lower_limb[1] * v0123 + higher_limb[0]) === 0
  limb_result[2] - (lower_limb[2] * v0123 + higher_limb[1]) === 0
  limb_result[3] - (lower_limb[3] * v0123 + higher_limb[2]) === 0
  -- SLL output placement (per byte-shift selector)
  is_sll * (s0 * (a[0] - limb_result[0])) === 0
  is_sll * (s0 * (a[1] - limb_result[1])) === 0
  is_sll * (s0 * (a[2] - limb_result[2])) === 0
  is_sll * (s0 * (a[3] - limb_result[3])) === 0
  is_sll * (s1 * a[0]) === 0
  is_sll * (s1 * (a[1] - limb_result[0])) === 0
  is_sll * (s1 * (a[2] - limb_result[1])) === 0
  is_sll * (s1 * (a[3] - limb_result[2])) === 0
  is_sll * (s2 * a[0]) === 0
  is_sll * (s2 * a[1]) === 0
  is_sll * (s2 * (a[2] - limb_result[0])) === 0
  is_sll * (s2 * (a[3] - limb_result[1])) === 0
  is_sll * (s3 * a[0]) === 0
  is_sll * (s3 * a[1]) === 0
  is_sll * (s3 * a[2]) === 0
  is_sll * (s3 * (a[3] - limb_result[0])) === 0
  -- SLLW output placement + MSB sign-fill
  is_sllw * (s0 * (a[0] - limb_result[0])) === 0
  is_sllw * (s0 * (a[1] - limb_result[1])) === 0
  is_sllw * (s1 * a[0]) === 0
  is_sllw * (s1 * (a[1] - limb_result[0])) === 0
  is_sllw * (sllw_msb[0] * (65535 : Expression (ZMod p)) - a[2]) === 0
  is_sllw * (sllw_msb[0] * (65535 : Expression (ZMod p)) - a[3]) === 0
  -- immediate consistency + op_a_0 zeroing flag
  is_sllw_imm - is_sllw * input.adapter.imm_c === 0
  input.adapter.op_a_0 === 0
  -- ## The nine byte-range pulls (gated by `gate = is_sll + is_sllw`); **raw** value (`toRawGated`)
  byteChannel.gatedReceive gate
    (⟨6, e32, Expression.const ((10 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.gatedReceive gate
    (⟨6, lower_limb[0], 16 - bitShift, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.gatedReceive gate
    (⟨6, higher_limb[0], bitShift, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.gatedReceive gate
    (⟨6, lower_limb[1], 16 - bitShift, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.gatedReceive gate
    (⟨6, higher_limb[1], bitShift, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.gatedReceive gate
    (⟨6, lower_limb[2], 16 - bitShift, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.gatedReceive gate
    (⟨6, higher_limb[2], bitShift, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.gatedReceive gate
    (⟨6, lower_limb[3], 16 - bitShift, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.gatedReceive gate
    (⟨6, higher_limb[3], bitShift, 0⟩ : ByteRow (Expression (ZMod p)))
  return ⟨input.state, input.adapter, a, c_bits, v[0], v[1], v[2], shift_u16,
    lower_limb, higher_limb, limb_result, ⟨sllw_msb[0]⟩, is_sll, is_sllw, is_sllw_imm⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs ShiftLeftCols main where
  -- witnesses the shift column block: a(4) + c_bits(6) + v(3) + shift_u16(4) + lower(4) + higher(4)
  -- + limb_result(4) + sllw_msb(1) = 30; the variant flags are threaded from `Inputs`, and the three
  -- sub-assertions add no witnesses.
  localLength _ := 30
  localLength_eq := by simp +arith [circuit_norm, main, Readers.ALUTypeReader.circuit, Readers.CPUState.circuit, U16MSBOperation.circuit]
  subcircuitsConsistent := by simp only [circuit_norm, main, Readers.ALUTypeReader.circuit, Readers.CPUState.circuit, U16MSBOperation.circuit]; try omega
  channelsWithGuarantees := [byteChannel.toRawGated]
  channelsWithRequirements :=
    [byteChannel.toRawGated, stateChannel.toRawGated, memoryChannel.toRaw, programChannel.toRaw]
  channelsLawful := by simp [circuit_norm, main, Readers.ALUTypeReader.circuit, Readers.CPUState.circuit, U16MSBOperation.circuit]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [byteChannel.toRawGated] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithRequirements_eq :
    ((elaborated (p := p)).channelsWithRequirements : List (RawChannel (ZMod p)))
      = [byteChannel.toRawGated, stateChannel.toRawGated, memoryChannel.toRaw, programChannel.toRaw] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 30 := rfl

end SP1Clean.ShiftLeftChip
