import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Native.Operations.MulOperation
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.RTypeReader
import SP1Clean.Model.Channels
import SP1Clean.Extracted.MulChip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The `Mul` chip row as a `GeneralFormalCircuit`

`MUL`/`MULH`/`MULHU`/`MULHSU`/`MULW`: witnesses the `MulOperation` column struct via
`MulOperation.populate` and composes `MulOperation.circuit` (a `FormalAssertion`) as a Clean `assertion`,
gated by the flag-sum `is_real = is_mul + … + is_mulw` (`alu/mul/mod.rs:234`). The semantic, flag-gated
`Spec` (RV64 `mul`/`mulh`/`mulhu`/`mulhsu`/`mulw` identities on `cols.a`) is in `Specs/Chip.lean`.

The chip's own `AssertSpec` tail is the five variant-flag booleans, their sum-bound, and `op_a_0 = 0`;
`InteractSpec` is `True` — all byte-range pulls live inside `MulOperation`. Carries `Fact (2^24 < p)`
(the `MulOperation` column-sum bound). Soundness and completeness are proven. -/

namespace SP1Clean.MulChip

open Circuit
open Extracted (MulCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- The five honest variant flags (`is_mul`, `is_mulh`, `is_mulhu`, `is_mulhsu`, `is_mulw`) the
prover supplies via the `"mul_flags"` hint key (one-hot for the active variant, all-zero on
padding). Falls back to all-zero when the key is absent. -/
def hintFlags (h : ProverHint (ZMod p)) : Vector (ZMod p) 5 :=
  ((h "mul_flags" 5)[0]?).getD #v[0, 0, 0, 0, 0]

/-- The literal meaning of SP1's `MulCols.asserts` own (inline) assertZero tail
(`Extracted/MulChip.lean` `E5,E7,E9,E11,E13,E15,op_a_0`): the five variant-flag booleans (in SP1's
extraction order), the flag-sum boolean, and `op_a_0 = 0`. The schoolbook arithmetic belongs to
`MulOperation`, not here. -/
def AssertSpec (cols : MulCols (ZMod p)) : Prop :=
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
def InteractSpec (_cols : MulCols (ZMod p)) : Prop := True

/-- Compose the `CPUState`/`RTypeReader` readers and the witnessed `MulOperation` as Clean sub-circuits.
Witnesses result word `a` and the five variant flags; gates `is_real`; assembles `MulCols`.
`RTypeReader` carries the flag-weighted opcode (`E16–E23`). -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var MulCols (ZMod p)) := do
  assertion Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  let flags ← witnessVector 5 (fun env => hintFlags env.hint)
  let is_mul := flags[0]; let is_mulh := flags[1]; let is_mulhu := flags[2]
  let is_mulhsu := flags[3]; let is_mulw := flags[4]
  -- The chip witnesses the `MulOperation` column struct via `populate` (conformance-checked in
  -- `WitnessTests/MulOperationWitness.lean`), then composes `MulOperation.circuit` as a Clean
  -- `assertion`. `populate` takes `(b, c, is_mulh, is_mulhsu, is_mulw)`.
  let cols ← ProvableType.witness (fun env =>
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
  let a ← witnessVector 4 (fun env => #v[env s0, env s1, env s2, env s3])
  a[0] === s0
  a[1] === s1
  a[2] === s2
  a[3] === s3
  is_mul * (is_mul - 1) === 0
  is_mulh * (is_mulh - 1) === 0
  is_mulhu * (is_mulhu - 1) === 0
  is_mulhsu * (is_mulhsu - 1) === 0
  is_mulw * (is_mulw - 1) === 0
  (is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw)
    * ((is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw) - 1) === 0
  input.adapter.op_a_0 === 0
  assertion Readers.RTypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
     is_mul * 11 + is_mulh * 12 + is_mulhu * 13 + is_mulhsu * 14 + is_mulw * 24,
     a[0], a[1], a[2], a[3]⟩
  input.is_real * (input.is_real - 1) === 0
  return ⟨input.state, input.adapter, a, cols, is_mul, is_mulh, is_mulhu, is_mulhsu, is_mulw⟩

set_option maxHeartbeats 4000000 in
instance elaborated : ElaboratedCircuit (ZMod p) Inputs MulCols main where
  -- flags(5) + MulOperation cols(45) + a(4) = 54; MulOperation is a FormalAssertion (0 witnesses).
  localLength _ := 54
  localLength_eq := by simp +arith [circuit_norm, main, MulOperation.circuit, Readers.CPUState.circuit, Readers.RTypeReader.circuit]
  subcircuitsConsistent := by simp only [circuit_norm, main, MulOperation.circuit, Readers.CPUState.circuit, Readers.RTypeReader.circuit]; try omega
  -- `programChannel` joins the byte guarantee propagated up from `RTypeReader`'s program **pull** (W11 flip).
  channelsWithGuarantees := [byteChannel.toRaw, programChannel.toRaw]
  channelsLawful := by simp [circuit_norm, main, MulOperation.circuit, Readers.CPUState.circuit, Readers.RTypeReader.circuit]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [byteChannel.toRaw, programChannel.toRaw] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 54 := rfl

end SP1Clean.MulChip
