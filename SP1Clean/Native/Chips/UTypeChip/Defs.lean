import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Proofs.Operations.AddOperation.Formal
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.JTypeReader
import SP1Clean.Native.Readers.RegisterWrite
import SP1Clean.Model.Channels
import ToClean.Circuit.WitnessCombinator
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The U-type chip row (`LUI` / `AUIPC`) as a `GeneralFormalCircuit`

Witnesses the addend (`is_auipc · pc`, 0 for LUI) and the add result; composes `CPUState` (straight-line
`next_pc = pc + 4`), `AddOperation` (gate `is_real - op_a_0`), and `JTypeReader` (opcode
`is_auipc·48 + (1-is_auipc)·49`). The addend is pinned per-limb by `addend[i] = is_auipc * pc[i]`.
Implements SP1's `UType` `eval` (`crates/core/machine/src/utype/mod.rs`). -/

namespace SP1Clean.UTypeChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Witness the addend (3 limbs = `is_auipc * pc`) and add result (4 limbs), then compose `CPUState`,
`AddOperation` (gate `is_real - op_a_0`), and `JTypeReader`. Pin the addend per-limb with
`addend[i] = is_auipc * pc[i]` gates. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var Columns (ZMod p)) := do
  -- The addend is pure field arithmetic over the input row, so it needs no `populate` companion:
  -- the three products go straight into the witness IR as literal expressions.
  let addend ← witnessVector 3 (.lit
    #v[input.is_auipc * input.state.pc[0],
       input.is_auipc * input.state.pc[1],
       input.is_auipc * input.state.pc[2]])
  let add_value ← witnessVectorIR 4 (AddOperation.populateIR
    #v[input.is_auipc * input.state.pc[0],
       input.is_auipc * input.state.pc[1],
       input.is_auipc * input.state.pc[2], 0]
    input.adapter.op_b_imm)
  let addendV : Word (Expression (ZMod p)) := #v[addend[0], addend[1], addend[2], 0]
  let _ ← Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  assertion AddOperation.circuit
    ⟨addendV, input.adapter.op_b_imm, { value := add_value }, input.is_real - input.adapter.op_a_0⟩
  -- `JTypeReader` is now a `GeneralFormalCircuit` (SC Phase 2pre) — composed via the GFC `CoeFun`
  -- (`subcircuitWithAssertion`), discarding its `unit` output. Its `Spec` (Contracts) is unchanged.
  let _ ← Readers.JTypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
     input.is_auipc * 48 + (1 - input.is_auipc) * 49,
     add_value[0], add_value[1], add_value[2], add_value[3]⟩
  -- Option B: the op_a (`rd`) write Memory **push** is composed here (factored OUT of the reader), *after*
  -- `AddOperation`, so `isU64 add_value` (the LUI/AUIPC result / zeroing-gate range-check) discharges its
  -- requirement. The write access clock is the recombined low clock `+ 4` (matching the reader).
  assertion Readers.RegisterWrite.circuit
    ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
     input.adapter.op_a, add_value, input.is_real⟩
  addend[0] - input.is_auipc * input.state.pc[0] === 0
  addend[1] - input.is_auipc * input.state.pc[1] === 0
  addend[2] - input.is_auipc * input.state.pc[2] === 0
  input.is_auipc * (input.is_auipc - 1) === 0
  -- Upstream's `when_not(is_real).assert_zero(op_a_0)`.  Besides matching the
  -- Rust AIR on padding rows, this makes the add gate `is_real - op_a_0`
  -- boolean without assuming a prover-side padding convention.
  assertZero ((input.is_real - 1) * input.adapter.op_a_0)
  -- Inline `assertZero` (not `=== 0`) so the `is_real` booleanity is visible to
  -- `ConstraintsHold.Shallow` as a chip-owned constraint (the `VmTables` re-base that motivated
  -- this was investigated and deferred — roadmap W11).
  assertZero (input.is_real * (input.is_real - 1))
  return ⟨input.is_real, input.state, input.adapter, addend, ⟨add_value⟩, input.is_auipc⟩

/-- The explicit-circuit elaborator computes the seven witness cells and the four-channel interface
from `main`, and reuses its structural certificates instead of reducing the full operation list. -/
instance elaborated : ElaboratedCircuit (ZMod p) Inputs Columns main := by
  elaborate_circuit

/-- The explicit completed row, kept folded for whole-chip row codecs and faithfulness proofs. -/
@[circuit_norm] lemma directOutput_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (elaborated (p := p)).output input offset =
      (⟨input.is_real, input.state, input.adapter,
        #v[var ⟨offset⟩, var ⟨offset + 1⟩, var ⟨offset + 2⟩],
        ⟨Vector.mapRange 4 fun i => var { index := offset + 3 + i }⟩,
        input.is_auipc⟩ :
        Var Columns (ZMod p)) := rfl

/-- Component-wise evaluation of UType's independent input row. -/
@[circuit_norm] theorem eval_inputs {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    Eval.eval env input =
      ({ is_real := Eval.eval env input.is_real, state := Eval.eval env input.state,
         adapter := Eval.eval env input.adapter,
         is_auipc := Eval.eval env input.is_auipc } : Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl

/-- Component-wise evaluation of UType's completed output row. -/
@[circuit_norm] theorem eval_columns {F : Type} [FiniteField F]
    (env : Environment F) (cols : Columns (Expression F)) :
    Eval.eval env cols =
      ({ is_real := Eval.eval env cols.is_real,
         state := Eval.eval env cols.state, adapter := Eval.eval env cols.adapter,
         addend := Eval.eval env cols.addend,
         add_operation := Eval.eval env cols.add_operation,
         is_auipc := Eval.eval env cols.is_auipc } : Columns F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl

end SP1Clean.UTypeChip
