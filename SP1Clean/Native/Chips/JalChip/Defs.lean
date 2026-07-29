import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Proofs.Operations.AddOperation.Formal
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.JTypeReader
import SP1Clean.Native.Readers.RegisterWrite
import SP1Clean.Model.Channels
import SP1Clean.Model.ByteTable
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The JAL chip row as a `GeneralFormalCircuit`

`next_pc` is computed data (the jump target `add_operation.value`), not `pc + 4`. Composes two
`AddOperation` gadgets (jump target `pc + op_b_imm` + link address `pc + 4`), `CPUState`, `JTypeReader`,
and a 4-byte alignment range check (`Range(add_operation.value[0] / 4, 14)`). The link-address gate is
`is_real - op_a_0` (not enforced when `rd = x0`). Implements SP1's `Jal` `air.rs:eval`. -/

namespace SP1Clean.JalChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

omit [Fact p.Prime] in
/-- `14 < p`, so the alignment `Range` byte-row width column `14` round-trips through `byteRowSpec_range`. -/
lemma h14p : (14 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega

/-- Witness the two add results (`add_operation.value` = jump target, `op_a_operation.value` = link
address) via `AddOperation.populate`, then compose as Clean `assertion`s. The `CPUState` reader is fed
the data-dependent `next_pc = add_operation.value`; the link add's gate is `is_real - op_a_0`. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var Columns (ZMod p)) := do
  let add_value ← witnessVectorNative 4 (fun env =>
    AddOperation.populate
      #v[env input.state.pc[0], env input.state.pc[1], env input.state.pc[2], 0]
      #v[env input.adapter.op_b_imm[0], env input.adapter.op_b_imm[1],
         env input.adapter.op_b_imm[2], env input.adapter.op_b_imm[3]])
  let op_a_value ← witnessVectorNative 4 (fun env =>
    AddOperation.populate
      #v[env input.state.pc[0], env input.state.pc[1], env input.state.pc[2], 0]
      #v[4, 0, 0, 0])
  let pcWordV : Word (Expression (ZMod p)) :=
    #v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0]
  let _ ← Readers.CPUState.circuit
    ⟨input.state, #v[add_value[0], add_value[1], add_value[2]], 8, input.is_real⟩
  assertion AddOperation.circuit ⟨pcWordV, input.adapter.op_b_imm, { value := add_value }, input.is_real⟩
  add_value[3] === 0
  assertion AddOperation.circuit
    ⟨pcWordV, #v[4, 0, 0, 0], { value := op_a_value }, input.is_real - input.adapter.op_a_0⟩
  op_a_value[3] === 0
  -- `JTypeReader` is now a `GeneralFormalCircuit` (SC Phase 2pre) — composed via the GFC `CoeFun`
  -- (`subcircuitWithAssertion`), discarding its `unit` output. Its `Spec` (Contracts) is unchanged.
  let _ ← Readers.JTypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 46,
     op_a_value[0], op_a_value[1], op_a_value[2], op_a_value[3]⟩
  -- Option B: the op_a (`rd`) write Memory **push** is composed here (factored OUT of the reader), *after*
  -- the link `AddOperation`, so `isU64 op_a_value` (the link result `pc + 4` / zeroing-gate range-check)
  -- discharges its requirement. The write access clock is the recombined low clock `+ 4` (matching the reader).
  assertion Readers.RegisterWrite.circuit
    ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
     input.adapter.op_a, op_a_value, input.is_real⟩
  byteChannel.pullIf input.is_real
    (⟨6, (add_value[0] * (4 : ZMod p)⁻¹), Expression.const ((14 : ℕ) : ZMod p), 0⟩ :
      ByteRow (Expression (ZMod p)))
  -- Pinned Rust: `when_not(is_real).assert_zero(op_a_0)`. This keeps the
  -- link-add gate faithful on padding rows and makes its booleanity derivable
  -- from the AIR rather than a verifier-side convention.
  assertZero ((input.is_real - 1) * input.adapter.op_a_0)
  assertZero (input.is_real * (input.is_real - 1))
  return ⟨input.is_real, input.state, input.adapter, ⟨add_value⟩, ⟨op_a_value⟩⟩

/-- Derive the eight witness cells and the complete four-channel interface structurally from `main`. -/
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
          var { index := offset + 4 + i }⟩⟩ :
        Var Columns (ZMod p)) := rfl

/-- Component-wise evaluation of the independent JAL input prefix. -/
@[circuit_norm] theorem eval_inputs {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    Eval.eval env input =
      ({ is_real := Eval.eval env input.is_real,
         state := Eval.eval env input.state,
         adapter := Eval.eval env input.adapter } :
        Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl

/-- Component-wise evaluation of the completed JAL row. -/
@[circuit_norm] theorem eval_columns {F : Type} [FiniteField F]
    (env : Environment F) (cols : Columns (Expression F)) :
    Eval.eval env cols =
      ({ is_real := Eval.eval env cols.is_real,
         state := Eval.eval env cols.state,
         adapter := Eval.eval env cols.adapter,
         add_operation := Eval.eval env cols.add_operation,
         op_a_operation := Eval.eval env cols.op_a_operation } :
        Columns F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl

end SP1Clean.JalChip
