import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Native.Operations.BitwiseU16Operation
import SP1Clean.Native.Witgen.HintFlags
import ToClean.Circuit.WitnessCombinator
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.ALUTypeReader
import SP1Clean.Native.Readers.RegisterWrite
import SP1Clean.Model.Channels
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The native Bitwise chip row (AND/OR/XOR) as a `GeneralFormalCircuit`

Composes `CPUState`/`BitwiseU16Operation`/`ALUTypeReader` as Clean subcircuits/assertions (emitting all
four buses), witnesses the three variant flags, threads `byte_opcode` (`is_xor·2 + is_or·1`)
into the gadget and `cpu_opcode` (`is_xor·3 + is_or·4 + is_and·5`) into the reader, gates `is_real`, and
assembles the native `Columns` struct. Operands are projected from the adapter's
`op_b_memory`/`op_c_memory` register reads (not separate columns). Semantic `Spec` in `Formal.lean`. -/

namespace SP1Clean.BitwiseChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The `is_real` selector and the threaded committed reader column blocks `state`/`adapter` (the latter
an immediate-capable `ALUTypeReader`). The `rs1`/`rs2` operands are projected from the adapter (the
Memory-bus register reads) — see `Inputs.op_b_val`/`op_c_val` below — rather than carried as separate
committed columns. -/
structure Inputs (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.ALUTypeReader F
deriving ProvableStruct

/-- Native Bitwise-chip row (Rust field order — the chip has no separate `is_real` column; the
real-row selector is the flag sum). The reader blocks reuse the project substrate; only the composed
u16 bitwise block is owned by the local Lean gadget. `Faithful.BitwiseChip.bitwiseChipReconfigure` is
the sole bridge to Rust's separately generated whole-chip row. -/
structure Columns (F : Type) where
  state : Extracted.CPUState F
  adapter : Extracted.ALUTypeReader F
  bitwise_operation : BitwiseU16Operation.Columns F
  is_xor : F
  is_or : F
  is_and : F
deriving ProvableStruct

/-- `rs1` operand = the `op_b` register read (`op_b_memory.prev_value`); `rs2` operand = the `op_c`
register read (`op_c_memory.prev_value`). Both feed the bitwise gadget exactly as in the extraction. -/
@[reducible] def Inputs.op_b_val {F} (i : Inputs F) : Word F := i.adapter.op_b_memory.prev_value
@[reducible] def Inputs.op_c_val {F} (i : Inputs F) : Word F := i.adapter.op_c_memory.prev_value

/-- The reassembled bitwise result word the reader writes for `rd`: the eight result bytes packed into
four 16-bit limbs (`BitwiseU16Operation.resultWord`). -/
def resultWord (cols : Columns (ZMod p)) : Word (ZMod p) :=
  BitwiseU16Operation.resultWord cols.bitwise_operation.bitwise_operation.result

/-- **Assertion half** — the literal meaning of SP1's `BitwiseCols.asserts` *own* (inline) assertZero
tail (everything past the composed `BitwiseU16Operation`/`CPUState`/`ALUTypeReader` sub-lists), in
extracted order (the generated oracle: `E3,E5,E7,E9, op_a_0`): the three opcode-flag booleans
(`is_xor`, `is_or`, `is_and`), the sum-bound boolean on `E1 = is_xor + is_or + is_and`, and the
`op_a_0` zeroing flag. The byte-level bitwise arithmetic is *not* here — it is the composed
`BitwiseU16Operation` sub-list. -/
def AssertSpec (cols : Columns (ZMod p)) : Prop :=
  let x := cols.is_xor; let o := cols.is_or; let a := cols.is_and
  let sum := x + o + a
  x * (x - 1) = 0 ∧
  o * (o - 1) = 0 ∧
  a * (a - 1) = 0 ∧
  sum * (sum - 1) = 0 ∧
  cols.adapter.op_a_0 = 0

/-- **Interaction half** — SP1's `BitwiseCols.interactions` *own* tail is **empty**
(the generated oracle ends `… ++ [ ]`): every byte-range pull for the bitwise op lives inside
the composed `BitwiseU16Operation` sub-list, anchored at the operation level. So the chip's own
interaction meaning is trivial. -/
def InteractSpec (_cols : Columns (ZMod p)) : Prop := True

/-- The three honest variant flags (`is_xor`, `is_or`, `is_and`) the prover supplies via the
`"bitwise_flags"` hint key (one-hot for the active variant, all-zero on padding). -/
def hintFlags (h : ProverHint (ZMod p)) : Vector (ZMod p) 3 :=
  ((h "bitwise_flags" 3)[0]?).getD #v[0, 0, 0]

omit [Fact (2 ^ 17 < p)] in
/-- The accessor is literally the `hintFlagsIR` evaluation: `hintGet`'s zero default IS the
`.getD #v[0, 0, 0]` fallback. Stated in the `Witgen.eval` normal form the completeness seam's
witness obligations arrive in. -/
lemma hintFlags_eval_ir (env : ProverEnvironment (ZMod p)) :
    Witgen.eval (M := fields 3) { env := env } (hintFlagsIR (ZMod p) "bitwise_flags" 3)
      = hintFlags env.hint := by
  have hdefault : (default : Vector (ZMod p) 3) = #v[0, 0, 0] := rfl
  rw [hintFlags, ← hdefault]
  apply Vector.ext
  intro i hi
  rw [Witgen.eval_fields', Vector.getElem_map]
  interval_cases i <;> simp only [hintFlagsIR, Vector.getElem_ofFn, circuit_norm]

/-- Compose `Readers.CPUState.circuit` (forms `next_pc = [pc[0]+4, …]`, `clk_inc = 8`), **witness** the
three variant flags `is_xor`/`is_or`/`is_and` (from the `"bitwise_flags"` `ProverHint`), compose the
witnessed `BitwiseU16Operation` gadget (`subcircuit`, fed the SP1
`byte_opcode = is_xor·2 + is_or·1 + is_and·0`), and `Readers.ALUTypeReader.circuit`
(`cpu_opcode = is_xor·3 + is_or·4 + is_and·5`; the `rd` write value is the reassembled result word's four
limbs), gate `is_real`, emit the three flag booleans + their sum-bound + the `op_a_0` zeroing (`AssertSpec`,
SP1's `builder.assert_zero(op_a_0)`), and assemble the native `Columns` struct. The `b_low_bytes`/
`c_low_bytes` column blocks are witnessed (the gadget enforces the decomposition on its own internal
copies; these struct fields are not read by the `Spec`). -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var Columns (ZMod p)) := do
  let _ ← Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  let flags ← witnessVectorIR 3 (.ofFExprs (hintFlagsIR (ZMod p) "bitwise_flags" 3))
  let is_xor := flags[0]; let is_or := flags[1]; let is_and := flags[2]
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
  -- SP1 has no independent `is_real` column for this chip: the real-row selector is exactly the
  -- sum of the three opcode flags (`alu/bitwise/mod.rs`). `Inputs.is_real` is the native circuit's
  -- explicit bus gate, so identify it with that Rust selector in the verifier constraints.
  assertZero (input.is_real * (input.is_real - 1))
  assertZero (input.is_real - (is_xor + is_or + is_and))
  is_xor * (is_xor - 1) === 0
  is_or * (is_or - 1) === 0
  is_and * (is_and - 1) === 0
  (is_xor + is_or + is_and) * ((is_xor + is_or + is_and) - 1) === 0
  input.adapter.op_a_0 === 0
  return ⟨input.state, input.adapter, bw_cols, is_xor, is_or, is_and⟩

-- Measured (W3/r2/b2): this instance clears 40000 heartbeats, so the former 1M ceiling was ~25x
-- over its floor and the plain default carries >=5x headroom.
instance elaborated : ElaboratedCircuit (ZMod p) Inputs Columns main where
  output input offset :=
    ⟨input.state, input.adapter,
      varFromOffset BitwiseU16Operation.Columns (offset + 3),
      var { index := offset }, var { index := offset + 1 }, var { index := offset + 2 }⟩
  channelsLawful := by
    simp only [circuit_norm, main, BitwiseU16Operation.circuit, Readers.ALUTypeReader.circuit,
      Readers.CPUState.circuit, Readers.RegisterWrite.circuit]
  -- witnesses the three flags (3) + the `BitwiseU16Operation` column struct (`b_low_bytes` 4 +
  -- `c_low_bytes` 4 + `bitwise_operation.result` 8 = 16); `BitwiseU16Operation`, the two readers and
  -- `RegisterWrite` are `assertion`s (`localLength 0`). 3 + 16 = 19.
  localLength _ := 19
  -- `programChannel` joins the structural `RowSpec` propagated from `ALUTypeReader`'s program **pull** (W11 flip);
  -- `memoryChannel` joins from `ALUTypeReader`'s memory read **pulls** (W11 memory flip). The `RegisterWrite`
  -- op_a write push owes a memory requirement (declared in `circuit.channelsWithRequirements`), not a guarantee.
  channelsWithGuarantees := [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]

/-- The completed Bitwise row, exposed as a folded value for chip-boundary proofs. -/
@[circuit_norm] lemma directOutput_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (elaborated (p := p)).output input offset =
      (⟨input.state, input.adapter,
        varFromOffset BitwiseU16Operation.Columns (offset + 3),
        var { index := offset }, var { index := offset + 1 }, var { index := offset + 2 }⟩ :
        Var Columns (ZMod p)) := rfl

@[circuit_norm] theorem eval_inputs {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    Eval.eval env input =
      ({ is_real := Eval.eval env input.is_real, state := Eval.eval env input.state,
         adapter := Eval.eval env input.adapter } : Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl

@[circuit_norm] theorem eval_columns {F : Type} [FiniteField F]
    (env : Environment F) (cols : Columns (Expression F)) :
    Eval.eval env cols =
      ({ state := Eval.eval env cols.state, adapter := Eval.eval env cols.adapter,
         bitwise_operation := Eval.eval env cols.bitwise_operation,
         is_xor := Eval.eval env cols.is_xor, is_or := Eval.eval env cols.is_or,
         is_and := Eval.eval env cols.is_and } : Columns F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl

@[circuit_norm] theorem eval_inputAdapter {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (Eval.eval env input).adapter = Eval.eval env input.adapter := by
  rw [eval_inputs]

@[circuit_norm] theorem eval_inputIsReal {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (Eval.eval env input).is_real = Expression.eval env input.is_real := by
  simpa only [CircuitType.eval_expr] using
    congrArg (fun value : Inputs F => value.is_real) (eval_inputs env input)

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
