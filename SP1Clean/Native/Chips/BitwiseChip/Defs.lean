import SP1Clean.Semantics.Specs.Chips.Bitwise
import SP1Clean.Circuits.Gadgets.Bitwise
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.ALUTypeReader
import SP1Clean.Native.Readers.RegisterWrite
import SP1Clean.Model.Channels
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Native Bitwise circuit

The three input selectors determine the byte operation, fetched opcode and activity. Clean's
witness IR constructs the sixteen byte columns; bundled CPU, ALU and register-write readers
supply the State, Memory and Program interactions. The public RV64 contract lives in
`Semantics/Specs/Chips/Bitwise`.
-/

namespace SP1Clean.BitwiseChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Build a Bitwise row from committed selectors and reader inputs. Only the sixteen byte
columns are witnessed; activity has no independent cell or external hint. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var Columns (ZMod p)) := do
  let _ ← Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  let is_xor := input.isXor; let is_or := input.isOr; let is_and := input.isAnd
  let byteOpcode : Expression (ZMod p) := is_xor * 2 + is_or * 1 + is_and * 0
  -- The chip witnesses the `BitwiseU16Operation` column struct (the two `U16toU8` low-byte blocks +
  -- the eight result bytes) via the witness-IR twin `populateFE` (`populateFE_eval` ties it to
  -- `populate`), then composes `BitwiseU16Operation.circuit` as a Clean `assertion` (it is a
  -- `FormalAssertion`, witnessing nothing of its own).
  let bw_cols ← witness (var := Var BitwiseU16Operation.Columns)
    (BitwiseU16Operation.populateFE input.op_b_val input.op_c_val byteOpcode)
  assertion BitwiseU16Operation.circuit
    ⟨input.op_b_val, input.op_c_val, bw_cols, byteOpcode, input.is_real⟩
  let r := bw_cols.bitwise_operation.result
  -- `ALUTypeReader` is now a `GeneralFormalCircuit` (SC Phase 2pre) — composed via the GFC `CoeFun`
  -- (`subcircuitWithAssertion`), discarding its `unit` output. Its `Spec` (Contracts) is unchanged.
  let _ ← Readers.ALUTypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
     is_xor * 3 + is_or * 4 + is_and * 5,
     r[0] + r[1] * 256, r[2] + r[3] * 256, r[4] + r[5] * 256, r[6] + r[7] * 256⟩
  -- Option B: the op_a (`rd`) write Memory **push** is composed here (factored OUT of the reader), *after*
  -- `BitwiseU16Operation`, so `isU64 (resultWord)` (the reassembled result word, each byte range-checked by
  -- the bitwise byte-bus pulls) discharges its requirement. The written value is the four-limb result word
  -- `#v[r[0]+r[1]*256, …]`; the write access clock is the recombined low clock `+ 4`.
  assertion Readers.RegisterWrite.circuit
    ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
     input.adapter.op_a, #v[r[0] + r[1] * 256, r[2] + r[3] * 256, r[4] + r[5] * 256, r[6] + r[7] * 256],
     input.is_real⟩
  is_xor * (is_xor - 1) === 0
  is_or * (is_or - 1) === 0
  is_and * (is_and - 1) === 0
  assertZero (input.is_real * (input.is_real - 1))
  input.adapter.op_a_0 === 0
  return ⟨input.state, input.adapter, bw_cols, is_xor, is_or, is_and⟩

-- Measured (W3/r2/b2): this instance clears 40000 heartbeats, so the former 1M ceiling was ~25x
-- over its floor and the plain default carries >=5x headroom.
instance elaborated : ElaboratedCircuit (ZMod p) Inputs Columns main where
  output input offset :=
    ⟨input.state, input.adapter,
      varFromOffset BitwiseU16Operation.Columns offset,
      input.isXor, input.isOr, input.isAnd⟩
  channelsLawful := by
    preserve_tactic_target
    simp only [Inputs.is_real, circuit_norm, main, BitwiseU16Operation.circuit, Readers.ALUTypeReader.circuit,
      Readers.CPUState.circuit, Readers.RegisterWrite.circuit]
  -- Four low bytes per operand and eight result bytes; readers witness no cells.
  localLength _ := 16
  -- `programChannel` joins the structural `RowSpec` propagated from `ALUTypeReader`'s program **pull** (W11 flip);
  -- `memoryChannel` joins from `ALUTypeReader`'s memory read **pulls** (W11 memory flip). The `RegisterWrite`
  -- op_a write push owes a memory requirement (declared in `circuit.channelsWithRequirements`), not a guarantee.
  channelsWithGuarantees := [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]

/-- The completed Bitwise row, exposed as a folded value for chip-boundary proofs. -/
@[circuit_norm] lemma directOutput_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (elaborated (p := p)).output input offset =
      (⟨input.state, input.adapter,
        varFromOffset BitwiseU16Operation.Columns offset,
        input.isXor, input.isOr, input.isAnd⟩ :
        Var Columns (ZMod p)) := rfl

/-! ### Operand words, in `circuit_norm`'s own orientation (the `AddChip/Defs.lean` pattern) —
the `ComputableWitnesses` proof projects the struct-level input agreement onto these. -/

@[circuit_norm] theorem eval_opBVal {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (ProvableStruct.eval env input).op_b_val
      = Vector.map (Expression.eval env) input.op_b_val := by
  rw [← ProvableStruct.eval_eq_eval]
  simp only [Inputs.op_b_val, eval_inputs, Readers.ALUTypeReader.eval_cols,
    Readers.ALUTypeReader.eval_accessCols]
  exact ProvableType.eval_fields env _

@[circuit_norm] theorem eval_opCVal {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (ProvableStruct.eval env input).op_c_val
      = Vector.map (Expression.eval env) input.op_c_val := by
  rw [← ProvableStruct.eval_eq_eval]
  simp only [Inputs.op_c_val, eval_inputs, Readers.ALUTypeReader.eval_cols,
    Readers.ALUTypeReader.eval_accessCols]
  exact ProvableType.eval_fields env _

end SP1Clean.BitwiseChip
