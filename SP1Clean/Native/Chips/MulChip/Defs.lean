import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Native.Operations.MulOperation
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.RTypeReader
import SP1Clean.Native.Readers.RegisterWrite
import SP1Clean.Model.Channels
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The `Mul` chip row as a `GeneralFormalCircuit`

`MUL`/`MULH`/`MULHU`/`MULHSU`/`MULW`: witnesses the `MulOperation` column struct via
`MulOperation.populate` and composes `MulOperation.circuit` (a `FormalAssertion`) as a Clean `assertion`,
gated by the flag-sum `is_real = is_mul + … + is_mulw` (`alu/mul/mod.rs:234`). The semantic, flag-gated
`Spec` (RV64 `mul`/`mulh`/`mulhu`/`mulhsu`/`mulw` identities on `cols.a`) is in `FormalModel/Contracts/Chips.lean`.

The chip's own `AssertSpec` tail is the five variant-flag booleans, their sum-bound, and `op_a_0 = 0`;
`InteractSpec` is `True` — all byte-range pulls live inside `MulOperation`. Carries `Fact (2^24 < p)`
(the `MulOperation` column-sum bound). Soundness and completeness are proven. -/

namespace SP1Clean.MulChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- The five honest variant flags (`is_mul`, `is_mulh`, `is_mulhu`, `is_mulhsu`, `is_mulw`) the
prover supplies via the `"mul_flags"` hint key (one-hot for the active variant, all-zero on
padding). Falls back to all-zero when the key is absent. -/
def hintFlags (h : ProverHint (ZMod p)) : Vector (ZMod p) 5 :=
  ((h "mul_flags" 5)[0]?).getD #v[0, 0, 0, 0, 0]

/-- The literal meaning of SP1's `MulCols.asserts` own (inline) assertZero tail
(`Extracted/ChipOracle/Mul.lean` `E5,E7,E9,E11,E13,E15,op_a_0`): the five variant-flag booleans (in SP1's
extraction order), the flag-sum boolean, and `op_a_0 = 0`. The schoolbook arithmetic belongs to
`MulOperation`, not here. -/
def AssertSpec (cols : Columns (ZMod p)) : Prop :=
  let m := cols.is_mul; let mh := cols.is_mulh; let mhu := cols.is_mulhu
  let mhsu := cols.is_mulhsu; let mw := cols.is_mulw
  let sum := m + mh + mhu + mhsu + mw
  m * (m - 1) = 0 ∧
  mh * (mh - 1) = 0 ∧
  mhu * (mhu - 1) = 0 ∧
  mw * (mw - 1) = 0 ∧
  mhsu * (mhsu - 1) = 0 ∧
  sum * (sum - 1) = 0 ∧
  cols.adapter.op_a_0 = 0

/-- SP1's `MulCols.interactions` own tail is empty: every byte-range pull lives inside `MulOperation`. -/
def InteractSpec (_cols : Columns (ZMod p)) : Prop := True

/-- Compose the `CPUState`/`RTypeReader` readers and the witnessed `MulOperation` as Clean sub-circuits.
Witnesses result word `a` and the five variant flags; gates `is_real`; assembles `Columns`.
`RTypeReader` carries the flag-weighted opcode (`E16–E23`). -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var Columns (ZMod p)) := do
  let _ ← Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  let flags ← witnessVectorNative 5 (fun env => hintFlags env.hint)
  let is_mul := flags[0]; let is_mulh := flags[1]; let is_mulhu := flags[2]
  let is_mulhsu := flags[3]; let is_mulw := flags[4]
  -- The chip witnesses the `MulOperation` column struct via `populate` (conformance-checked in
  -- `WitnessTests/MulOperationWitness.lean`), then composes `MulOperation.circuit` as a Clean
  -- `assertion`. `populate` takes `(b, c, is_mulh, is_mulhsu, is_mulw)`.
  let cols ← witnessNative (var := Var Extracted.MulOperation) (fun env =>
    MulOperation.populate
      #v[env input.op_b_val[0], env input.op_b_val[1], env input.op_b_val[2], env input.op_b_val[3]]
      #v[env input.op_c_val[0], env input.op_c_val[1], env input.op_c_val[2], env input.op_c_val[3]]
      (env is_mulh) (env is_mulhsu) (env is_mulw))
  -- Gate `MulOperation` by the flag-sum (`alu/mul/mod.rs:234`): `is_mulw = 1 → sum = 1`.
  assertion MulOperation.circuit
    ⟨input.op_b_val, input.op_c_val, cols, is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw,
      is_mul, is_mulh, is_mulhu, is_mulhsu, is_mulw⟩
  -- `a`↔`resultWord` linkage (`MulOperation.aSelector`): the register-write word is the flag-weighted
  -- product slice — `MUL`/`MULW` low bytes, `MULH*` bytes 8..15, `MULW` upper limbs sign-filled `* 65535`.
  -- Soundness uses `aSelector_eq_resultWord`; matches SP1's `MulOperation.asserts` product→`a` tie.
  let c256 : Expression (ZMod p) := 256
  let c65535 : Expression (ZMod p) := 65535
  let s0 : Expression (ZMod p) := is_mul * (cols.product[0] + cols.product[1] * c256)
    + (is_mulh + is_mulhu + is_mulhsu) * (cols.product[8] + cols.product[9] * c256)
    + is_mulw * (cols.product[0] + cols.product[1] * c256)
  let s1 : Expression (ZMod p) := is_mul * (cols.product[2] + cols.product[3] * c256)
    + (is_mulh + is_mulhu + is_mulhsu) * (cols.product[10] + cols.product[11] * c256)
    + is_mulw * (cols.product[2] + cols.product[3] * c256)
  let s2 : Expression (ZMod p) := is_mul * (cols.product[4] + cols.product[5] * c256)
    + (is_mulh + is_mulhu + is_mulhsu) * (cols.product[12] + cols.product[13] * c256)
    + is_mulw * (cols.product_msb.msb * c65535)
  let s3 : Expression (ZMod p) := is_mul * (cols.product[6] + cols.product[7] * c256)
    + (is_mulh + is_mulhu + is_mulhsu) * (cols.product[14] + cols.product[15] * c256)
    + is_mulw * (cols.product_msb.msb * c65535)
  let a ← witnessVectorNative 4 (fun env => #v[env s0, env s1, env s2, env s3])
  -- Rust gates each result-placement equation by an opcode selector.  Since `is_real` is the
  -- one-hot selector sum, gating the four combined equations by `is_real` is extensionally
  -- equivalent on active rows and, critically, leaves `a` unconstrained on padding rows just as
  -- the pinned AIR does.
  assertZero (input.is_real * (a[0] - s0))
  assertZero (input.is_real * (a[1] - s1))
  assertZero (input.is_real * (a[2] - s2))
  assertZero (input.is_real * (a[3] - s3))
  assertZero (is_mul * (is_mul - 1))
  assertZero (is_mulh * (is_mulh - 1))
  assertZero (is_mulhu * (is_mulhu - 1))
  assertZero (is_mulhsu * (is_mulhsu - 1))
  assertZero (is_mulw * (is_mulw - 1))
  assertZero ((is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw)
    * ((is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw) - 1))
  assertZero input.adapter.op_a_0
  -- `RTypeReader` is now a `GeneralFormalCircuit` (SC Phase 2pre) — composed via the GFC `CoeFun`
  -- (`subcircuitWithAssertion`), discarding its `unit` output. Its `Spec` (Contracts) is unchanged.
  let _ ← Readers.RTypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
     is_mul * 11 + is_mulh * 12 + is_mulhu * 13 + is_mulhsu * 14 + is_mulw * 24,
     a[0], a[1], a[2], a[3]⟩
  -- Pin `is_real` to the one-hot flag-sum (SP1 has no separate `is_real`: it gates the whole row by this
  -- sum `E3`, used uniformly for `CPUState`/`RTypeReader`/`MulOperation`). Making it explicit lets soundness
  -- bridge the reader (gated `is_real`) and the operation (gated by the sum) — the Option-B operand `isU64`
  -- the reader derives on real rows now also discharges `MulOperation`'s `sum = 1 → isU64` precondition.
  assertZero (input.is_real - (is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw))
  -- Option B: the op_a (`rd`) write Memory **push** is composed here (factored OUT of the reader), *after*
  -- `MulOperation`, so `isU64 a` (the result word range) discharges its requirement. Clock `+ 4`.
  assertion Readers.RegisterWrite.circuit
    ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
     input.adapter.op_a, a, input.is_real⟩
  -- Inline `assertZero` (not `=== 0`) so the `is_real` booleanity is visible to
  -- `ConstraintsHold.Shallow` — required for the chip to be a `VmTables` table (A2).
  assertZero (input.is_real * (input.is_real - 1))
  return ⟨input.state, input.adapter, a, cols, is_mul, is_mulh, is_mulhu, is_mulhsu, is_mulw⟩

-- Measured (W3/r2/b2): this derivation clears 40000 heartbeats, so the former 4M ceiling was ~100x
-- over its floor and the plain default carries >=5x headroom. Elaboration-bound, not LCNF-bound.
@[implicit_reducible] private def derivedElaborated :
    ElaboratedCircuit (ZMod p) Inputs Columns main := by
  elaborate_circuit_with {
    channelsWithGuarantees :=
      [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]
  }

/-- Clean derives the output layout and all structural proofs from `main`; this public record forwards
that compact result while keeping the declared channel order visible at the chip boundary. -/
instance elaborated : ElaboratedCircuit (ZMod p) Inputs Columns main where
  output := derivedElaborated.output
  output_eq := derivedElaborated.output_eq
  localLength := derivedElaborated.localLength
  localLength_eq := derivedElaborated.localLength_eq
  subcircuitsConsistent := derivedElaborated.subcircuitsConsistent
  channelsWithGuarantees :=
    [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]
  channelsLawful := derivedElaborated.channelsLawful

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 54 := rfl

/-- Explicit MUL row layout: five selector witnesses, the 45-cell multiplication block, then the
four-limb result word.  This is a symbolic normalization boundary for grounding and faithfulness. -/
@[circuit_norm] lemma directOutput_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (elaborated (p := p)).output input offset =
      (⟨input.state, input.adapter,
        Vector.mapRange 4 fun i => var { index := offset + 50 + i },
        varFromOffset Extracted.MulOperation (offset + 5),
        var { index := offset }, var { index := offset + 1 },
        var { index := offset + 2 }, var { index := offset + 3 },
        var { index := offset + 4 }⟩ : Var Columns (ZMod p)) := rfl

/-- The exact R-type reader input retained after MUL's 54 local cells.  Naming this value keeps
downstream timestamp and structural proofs independent of the multiplication witness internals. -/
def rTypeReaderInput (input : Var Inputs (ZMod p)) (offset : ℕ) :
    Var Readers.RTypeReader.Inputs (ZMod p) :=
  let flags : Vector (Expression (ZMod p)) 5 :=
    Vector.mapRange 5 fun i => var { index := offset + i }
  let value : Word (Expression (ZMod p)) :=
    Vector.mapRange 4 fun i => var { index := offset + 50 + i }
  let opcode : Expression (ZMod p) :=
    flags[0] * Expression.const (11 : ZMod p) +
      flags[1] * Expression.const (12 : ZMod p) +
      flags[2] * Expression.const (13 : ZMod p) +
      flags[3] * Expression.const (14 : ZMod p) +
      flags[4] * Expression.const (24 : ZMod p)
  ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
    opcode, value[0], value[1], value[2], value[3]⟩

/-- Component-wise evaluation of MUL's independent input row. -/
@[circuit_norm] theorem eval_inputs {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    Eval.eval env input =
      ({ is_real := Eval.eval env input.is_real, state := Eval.eval env input.state,
         adapter := Eval.eval env input.adapter } : Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl

/-- Component-wise evaluation of a completed Mul row. -/
@[circuit_norm] theorem eval_columns {F : Type} [FiniteField F]
    (env : Environment F) (cols : Columns (Expression F)) :
    Eval.eval env cols =
      ({ state := Eval.eval env cols.state
         adapter := Eval.eval env cols.adapter
         a := Eval.eval env cols.a
         mul_operation := Eval.eval env cols.mul_operation
         is_mul := Eval.eval env cols.is_mul
         is_mulh := Eval.eval env cols.is_mulh
         is_mulhu := Eval.eval env cols.is_mulhu
         is_mulhsu := Eval.eval env cols.is_mulhsu
         is_mulw := Eval.eval env cols.is_mulw } :
        Columns F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl

end SP1Clean.MulChip
