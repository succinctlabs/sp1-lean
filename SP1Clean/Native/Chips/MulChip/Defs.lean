import SP1Clean.Semantics.Specs.Chips.Mul
import SP1Clean.Circuits.Gadgets.Mul
import ToClean.Circuit.WitnessCombinator
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.RTypeReader
import SP1Clean.Native.Readers.RegisterWrite
import SP1Clean.Model.Channels
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel

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
Witnesses result word `a`; derives activity from the input selectors and assembles `Columns`.
`RTypeReader` carries the flag-weighted opcode (`E16–E23`). -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var Columns (ZMod p)) := do
  let _ ← Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  let is_mul := input.isMul; let is_mulh := input.isMulh; let is_mulhu := input.isMulhu
  let is_mulhsu := input.isMulhsu; let is_mulw := input.isMulw
  -- Clean's witness IR computes the arithmetic block; `populateFE_eval` relates it to `populate`.
  let cols ← witness (var := Var Circuits.Types.MulOperation)
    (MulOperation.populateFE input.op_b_val input.op_c_val is_mulh is_mulhsu is_mulw)
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
  let a ← witnessVectorIR 4 (.ofExprs #v[s0, s1, s2, s3])
  -- Gate `MulOperation` by the flag-sum (`alu/mul/mod.rs:234`): `is_mulw = 1 → sum = 1`.
  assertion MulOperation.circuit
    ⟨input.op_b_val, input.op_c_val, cols, is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw,
      is_mul, is_mulh, is_mulhu, is_mulhsu, is_mulw, a⟩
  assertZero (is_mul * (is_mul - 1))
  assertZero (is_mulh * (is_mulh - 1))
  assertZero (is_mulhu * (is_mulhu - 1))
  assertZero (is_mulhsu * (is_mulhsu - 1))
  assertZero (is_mulw * (is_mulw - 1))
  assertZero ((is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw)
    * ((is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw) - 1))
  assertZero input.adapter.op_a_0
  -- The reader authenticates the flag-weighted opcode and the source operands.
  let _ ← Readers.RTypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
     is_mul * 11 + is_mulh * 12 + is_mulhu * 13 + is_mulhsu * 14 + is_mulw * 24,
     a[0], a[1], a[2], a[3]⟩
  -- Write the completed result at clock + 4; `MulOperation` supplies its word-range guarantee.
  assertion Readers.RegisterWrite.circuit
    ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
     input.adapter.op_a, a, input.is_real⟩
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
-- `↓` (pre-order): the instance forwards `derivedElaborated`'s fields, and since Lean 4.33 `simp`
-- reduces `elaborated.output`/`.localLength` to the private forwarded projection before any
-- post-order lemma can see it; a pre-order lemma fires on the public form first.
@[circuit_norm ↓] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 49 := rfl

/-- Explicit MUL witness layout: the 45-cell multiplication block and four-limb result word.
The selectors are retained from the input row.  This is a symbolic normalization boundary for grounding and faithfulness. -/
@[circuit_norm ↓] lemma directOutput_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (elaborated (p := p)).output input offset =
      (⟨input.state, input.adapter,
        Vector.mapRange 4 fun i => var { index := offset + 45 + i },
        varFromOffset Circuits.Types.MulOperation offset,
        input.isMul, input.isMulh, input.isMulhu, input.isMulhsu, input.isMulw⟩ : Var Columns (ZMod p)) := rfl

-- The same facts on the forwarded private derivation, for a goal in which `simp` has already
-- reduced the public instance's projection.
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma derivedLocalLength_eq (x : Var Inputs (ZMod p)) :
    (derivedElaborated (p := p)).localLength x = 49 := rfl

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma derivedOutput_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (derivedElaborated (p := p)).output input offset =
      (⟨input.state, input.adapter,
        Vector.mapRange 4 fun i => var { index := offset + 45 + i },
        varFromOffset Circuits.Types.MulOperation offset,
        input.isMul, input.isMulh, input.isMulhu, input.isMulhsu, input.isMulw⟩ : Var Columns (ZMod p)) := rfl

/-- The exact R-type reader input retained after MUL's 49 local cells.  Naming this value keeps
downstream timestamp and structural proofs independent of the multiplication witness internals. -/
def rTypeReaderInput (input : Var Inputs (ZMod p)) (offset : ℕ) :
    Var Readers.RTypeReader.Inputs (ZMod p) :=
  let value : Word (Expression (ZMod p)) :=
    Vector.mapRange 4 fun i => var { index := offset + 45 + i }
  let opcode : Expression (ZMod p) :=
    input.isMul * Expression.const (11 : ZMod p) +
      input.isMulh * Expression.const (12 : ZMod p) +
      input.isMulhu * Expression.const (13 : ZMod p) +
      input.isMulhsu * Expression.const (14 : ZMod p) +
      input.isMulw * Expression.const (24 : ZMod p)
  ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
    opcode, value[0], value[1], value[2], value[3]⟩

/-! ### Operand words, in `circuit_norm`'s own orientation (the `AddChip/Defs.lean` pattern) —
the `ComputableWitnesses` proof projects the struct-level input agreement onto these. -/

@[circuit_norm] theorem eval_opBVal {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (ProvableStruct.eval env input).op_b_val
      = Vector.map (Expression.eval env) input.op_b_val := by
  rw [← ProvableStruct.eval_eq_eval]
  simp only [Inputs.op_b_val, eval_inputs, Readers.RTypeReader.eval_cols,
    Readers.RTypeReader.eval_registerAccessCols]
  exact ProvableType.eval_fields env _

@[circuit_norm] theorem eval_opCVal {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (ProvableStruct.eval env input).op_c_val
      = Vector.map (Expression.eval env) input.op_c_val := by
  rw [← ProvableStruct.eval_eq_eval]
  simp only [Inputs.op_c_val, eval_inputs, Readers.RTypeReader.eval_cols,
    Readers.RTypeReader.eval_registerAccessCols]
  exact ProvableType.eval_fields env _

end SP1Clean.MulChip
