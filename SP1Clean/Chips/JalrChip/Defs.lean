import SP1Clean.Specs.Chip
import SP1Clean.Operations.AddOperation.Formal
import SP1Clean.Readers.CPUState
import SP1Clean.Readers.ITypeReader
import SP1Clean.Foundations.Channels
import SP1Clean.Foundations.ByteTable
import SP1Clean.Extracted.JalrChip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The JALR chip row as a `GeneralFormalCircuit` — register-indirect control flow

The sibling of `JalChip` for **JALR** (opcode 47, `rd ← pc + 4`, `pc ← (rs1 + imm) & ~1`). Like JAL its
committed `next_pc` is *computed data*, but the jump base is the **rs1 register value**
(`adapter.op_b_memory.prev_value`) rather than the program counter, and the target's low bit is **cleared**
before the jump. Composes, as true Clean subcircuits (mirroring SP1's `Jalr` `air.rs:eval`,
`Extracted/JalrChip.lean`):

- the `Readers.CPUState` adapter, fed the **LSB-cleared** `next_pc = #v[add_operation.value[0] - lsb,
  value[1], value[2]]` (RISC-V's `(rs1 + imm) & ~1`) and `clk_inc = 8`;
- **two** `AddOperation` gadgets — `rs1 + op_c_imm = add_operation.value` (the raw jump target, gated
  `is_real`) and `pc + 4 = op_a_operation.value` (the return/link address, gated *additively* by
  `is_real - op_a_0`, so it is not enforced when `rd = x0`);
- a committed `lsb` witness with the `lsb` binary gate, the low bit removed from the next_pc low limb;
- the `Readers.ITypeReader` adapter (program fetch at opcode 47, the rs1 read + rd write memory accesses,
  the `op_a_0` binary + zeroing gates);
- the 4-byte **alignment** range check on the cleared target (`Range((add_operation.value[0] - lsb)/4, 14)`);
- the `is_real` binary gate.

The chip `Spec` is the I-type reader sub-`Spec` + the proven `is_real`/`lsb` binary + the `is_real`-gated
jump (`add_operation.value = rs1 + op_c_imm`) and link (`op_a_0 = 0 → op_a_operation.value = pc + 4`)
identities. The buses' cross-row meaning lives at the trace level (`Soundness/{State,Memory}Consistency`). -/

namespace SP1Clean.JalrChip

open Circuit
open Extracted (JalrColumns)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

omit [Fact p.Prime] in
/-- `14 < p`, so the alignment `Range` byte-row width column `14` round-trips through `byteRowSpec_range`. -/
lemma h14p : (14 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega

/-- The rs1 register value (the `op_b` source read's prior value) as a 4-limb word. -/
def rs1WordI (input : Inputs (ZMod p)) : Word (ZMod p) :=
  #v[input.adapter.op_b_memory.prev_value[0], input.adapter.op_b_memory.prev_value[1],
     input.adapter.op_b_memory.prev_value[2], input.adapter.op_b_memory.prev_value[3]]

/-- The jump-target word the chip witnesses for `add_operation.value` (`rs1 + op_c_imm`, base-2^16). -/
def jumpTargetWord (input : Inputs (ZMod p)) : Word (ZMod p) :=
  AddOperation.populate (rs1WordI input) input.adapter.op_c_imm

/-- The link-address word the chip witnesses for `op_a_operation.value` (`pc + 4`, base-2^16). -/
def linkTargetWord (input : Inputs (ZMod p)) : Word (ZMod p) :=
  AddOperation.populate
    #v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] #v[4, 0, 0, 0]

/-- The committed `lsb` witness: the low bit of the jump target's low limb. -/
def lsbBit (input : Inputs (ZMod p)) : ZMod p :=
  (((jumpTargetWord input)[0].val % 2 : ℕ) : ZMod p)

/-- Compose the JALR row. Witnesses the two add results (`add_operation.value` = `rs1 + imm`,
`op_a_operation.value` = `pc + 4`) via `AddOperation.populate`, plus the `lsb` low bit of the target's
low limb; composes the demoted `AddOperation` gadget as a Clean `assertion` over each whole column struct.
The `CPUState` reader is fed the **LSB-cleared** `next_pc`; the second add's gate is `is_real - op_a_0`. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var JalrColumns (ZMod p)) := do
  let add_value ← witnessVector 4 (fun env =>
    AddOperation.populate
      #v[env input.adapter.op_b_memory.prev_value[0], env input.adapter.op_b_memory.prev_value[1],
         env input.adapter.op_b_memory.prev_value[2], env input.adapter.op_b_memory.prev_value[3]]
      #v[env input.adapter.op_c_imm[0], env input.adapter.op_c_imm[1],
         env input.adapter.op_c_imm[2], env input.adapter.op_c_imm[3]])
  let op_a_value ← witnessVector 4 (fun env =>
    AddOperation.populate
      #v[env input.state.pc[0], env input.state.pc[1], env input.state.pc[2], 0]
      #v[4, 0, 0, 0])
  let lsb ← witnessField (fun env => (((env add_value[0]).val % 2 : ℕ) : ZMod p))
  let rs1WordV : Word (Expression (ZMod p)) :=
    #v[input.adapter.op_b_memory.prev_value[0], input.adapter.op_b_memory.prev_value[1],
       input.adapter.op_b_memory.prev_value[2], input.adapter.op_b_memory.prev_value[3]]
  let pcWordV : Word (Expression (ZMod p)) :=
    #v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0]
  -- lsb binary gate.
  lsb * (lsb - 1) === 0
  -- CPUState with the **LSB-cleared** next_pc = add_operation.value & ~1.
  assertion Readers.CPUState.circuit
    ⟨input.state, #v[add_value[0] - lsb, add_value[1], add_value[2]], 8, input.is_real⟩
  -- add_operation: rs1 + op_c_imm = jump target, gated `is_real`.
  assertion AddOperation.circuit ⟨rs1WordV, input.adapter.op_c_imm, { value := add_value }, input.is_real⟩
  add_value[3] === 0
  -- op_a_operation: pc + 4 = link address, gated additively by `is_real - op_a_0`.
  assertion AddOperation.circuit
    ⟨pcWordV, #v[4, 0, 0, 0], { value := op_a_value }, input.is_real - input.adapter.op_a_0⟩
  op_a_value[3] === 0
  -- ITypeReader: program fetch (opcode 47), op_a write + op_b read, op_a_0 binary + zeroing gates.
  assertion Readers.ITypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 47,
     op_a_value[0], op_a_value[1], op_a_value[2], op_a_value[3]⟩
  -- next_pc 4-byte alignment: Range((add_operation.value[0] - lsb) / 4, 14).
  byteChannel.gatedReceive input.is_real
    (⟨6, ((add_value[0] - lsb) * (4 : ZMod p)⁻¹),
      Expression.const ((14 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))
  input.is_real * (input.is_real - 1) === 0
  return ⟨input.state, input.adapter, input.is_real, ⟨add_value⟩, ⟨op_a_value⟩, lsb⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs JalrColumns main where
  channelsLawful := by simp [circuit_norm, main, AddOperation.circuit, Readers.CPUState.circuit, Readers.ITypeReader.circuit]
  -- Two add results (8 limbs) + the `lsb` scalar.
  localLength _ := 9
  channelsWithGuarantees := [byteChannel.toRawGated]
  channelsWithRequirements :=
    [byteChannel.toRawGated, stateChannel.toRawGated, memoryChannel.toRaw, programChannel.toRaw]

end SP1Clean.JalrChip
