import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Proofs.Operations.AddOperation.Formal
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.ITypeReader
import SP1Clean.Native.Readers.RegisterWrite
import SP1Clean.Model.Channels
import SP1Clean.Model.ByteTable
import ToClean.Circuit.WitnessCombinator
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The JALR chip row as a `GeneralFormalCircuit`

JALR (opcode 47): `rd ← pc + 4`, `pc ← (rs1 + imm) & ~1`. Like JAL, `next_pc` is computed data, but
the jump base is the rs1 register value and the low bit is cleared before the jump (committed `lsb`
witness + binary gate). Composes two `AddOperation` gadgets (jump `rs1 + op_c_imm` + link `pc + 4`),
`CPUState` (LSB-cleared `next_pc`), `ITypeReader`, and a 4-byte alignment range check. Implements
SP1's `Jalr` `air.rs:eval`. -/

namespace SP1Clean.JalrChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

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

/-- Witness the two add results (`add_operation.value` = `rs1 + imm`, `op_a_operation.value` = `pc + 4`)
and the `lsb` scalar via the witness IR, then compose as Clean `assertion`s. `CPUState` is fed the LSB-cleared
`next_pc`; the link add's gate is `is_real - op_a_0`. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var Columns (ZMod p)) := do
  let add_value ← witnessVectorIR 4 (AddOperation.populateIR
    input.adapter.op_b_memory.prev_value input.adapter.op_c_imm)
  let op_a_value ← witnessVectorIR 4 (AddOperation.populateIR
    #v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0]
    #v[4, 0, 0, 0])
  -- The one witness here that reads an *earlier witnessed cell* rather than an input column:
  -- `add_value[0]` sits below this offset, so honest witness generation still sees it.
  let lsb ← witnessField ((add_value[0].val % 2).toField)
  let rs1WordV : Word (Expression (ZMod p)) :=
    #v[input.adapter.op_b_memory.prev_value[0], input.adapter.op_b_memory.prev_value[1],
       input.adapter.op_b_memory.prev_value[2], input.adapter.op_b_memory.prev_value[3]]
  let pcWordV : Word (Expression (ZMod p)) :=
    #v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0]
  lsb * (lsb - 1) === 0
  let _ ← Readers.CPUState.circuit
    ⟨input.state, #v[add_value[0] - lsb, add_value[1], add_value[2]], 8, input.is_real⟩
  assertion AddOperation.circuit ⟨rs1WordV, input.adapter.op_c_imm, { value := add_value }, input.is_real⟩
  add_value[3] === 0
  assertion AddOperation.circuit
    ⟨pcWordV, #v[4, 0, 0, 0], { value := op_a_value }, input.is_real - input.adapter.op_a_0⟩
  op_a_value[3] === 0
  -- `ITypeReader` is now a `GeneralFormalCircuit` (SC Phase 2pre) — composed via the GFC `CoeFun`
  -- (`subcircuitWithAssertion`), discarding its `unit` output. Its `Spec` (Contracts) is unchanged.
  let _ ← Readers.ITypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 47,
     op_a_value[0], op_a_value[1], op_a_value[2], op_a_value[3]⟩
  -- Option B: the op_a (`rd`) write Memory **push** is composed here (factored OUT of the reader), *after*
  -- the link `AddOperation`, so `isU64 op_a_value` (the link result / zeroing-gate range-check) discharges its
  -- requirement. The write access clock is the recombined low clock `+ 4` (matching the reader).
  assertion Readers.RegisterWrite.circuit
    ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
     input.adapter.op_a, op_a_value, input.is_real⟩
  byteChannel.pullIf input.is_real
    (⟨6, ((add_value[0] - lsb) * (4 : ZMod p)⁻¹),
      Expression.const ((14 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))
  -- Pinned Rust: `when_not(is_real).assert_zero(op_a_0)`.
  assertZero ((input.is_real - 1) * input.adapter.op_a_0)
  assertZero (input.is_real * (input.is_real - 1))
  return ⟨input.is_real, input.state, input.adapter, ⟨add_value⟩, ⟨op_a_value⟩, lsb⟩

/-- Derive the nine witness cells and the complete four-channel interface structurally from `main`. -/
instance elaborated : ElaboratedCircuit (ZMod p) Inputs Columns main := by
  elaborate_circuit

/-- Folded completed-row layout used by the whole-chip Rust AIR codec. -/
@[circuit_norm] lemma directOutput_eq
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (elaborated (p := p)).output input offset =
      (⟨input.is_real, input.state, input.adapter,
        ⟨Vector.mapRange 4 fun i =>
          var { index := offset + i }⟩,
        ⟨Vector.mapRange 4 fun i =>
          var { index := offset + 4 + i }⟩,
        var { index := offset + 8 }⟩ :
        Var Columns (ZMod p)) := rfl

/-- Component-wise evaluation of the independent JALR input prefix. -/
@[circuit_norm] theorem eval_inputs {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    Eval.eval env input =
      ({ is_real := Eval.eval env input.is_real,
         state := Eval.eval env input.state,
         adapter := Eval.eval env input.adapter } :
        Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl

/-- Component-wise evaluation of the completed JALR row. -/
@[circuit_norm] theorem eval_columns {F : Type} [FiniteField F]
    (env : Environment F) (cols : Columns (Expression F)) :
    Eval.eval env cols =
      ({ is_real := Eval.eval env cols.is_real,
         state := Eval.eval env cols.state,
         adapter := Eval.eval env cols.adapter,
         add_operation := Eval.eval env cols.add_operation,
         op_a_operation := Eval.eval env cols.op_a_operation,
         lsb := Eval.eval env cols.lsb } :
        Columns F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl

end SP1Clean.JalrChip
