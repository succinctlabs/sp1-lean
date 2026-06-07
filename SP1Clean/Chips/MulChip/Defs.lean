import SP1Clean.Specs.Chip
import SP1Clean.Operations.MulOperation
import SP1Clean.Readers.CPUState
import SP1Clean.Readers.RTypeReader
import SP1Clean.Foundations.Channels
import SP1Clean.Extracted.MulChip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Skeleton — the `Mul` chip row as a `GeneralFormalCircuit` (spec surface)

The RISC-V multiply family (`MUL`/`MULH`/`MULHU`/`MULHSU`/`MULW`) ported as a chip-level
`GeneralFormalCircuit`. Unlike the shift chips — whose arithmetic is inlined into the extracted chip —
`Mul` has a **real operation-level extraction**: `Operations/MulOperation.lean` is a `FormalAssertion`
(SP1's `MulOperation::eval` — the 16-column schoolbook product, the `U16toU8`/`U16MSB` byte/sign
sub-gadgets, the `is_real`-gated byte-bus range checks). Accordingly this chip **witnesses the
`MulOperation` column struct via `MulOperation.populate` and composes `MulOperation.circuit` as a Clean
`assertion`** (à la `AddChip` composing `AddOperation` + `RTypeReader`), gated by the **flag-sum** as SP1
(`alu/mul/mod.rs:234`: `is_real = is_mul + … + is_mulw`), rather than re-deriving the product constraints.

Per `Extracted/MulChip.lean` the chip's *own* asserts (everything past the composed
`MulOperation`/`CPUState`/`RTypeReader` sublists) reduce to just the five variant-flag booleans, their
sum-bound, and `op_a_0 = 0` (`AssertSpec`); the chip's *own* interactions tail is **empty** — all
byte-range pulls live inside `MulOperation` — so `InteractSpec := True`. The semantic, `is_real`/
flag-gated `Spec` (the RV64 `mul`/`mulh`/`mulhu`/`mulhsu`/`mulw` identities on the result column `cols.a`)
lives in `Specs/Chip.lean`. `Faithful/MulChip.lean` anchors the two structural specs to SP1's extracted
lists.

Skeleton status: `AssertSpec`/`InteractSpec`/`Spec`/`main`/`elaborated`/`circuit` are real and build; the
`main` body composes the `CPUState`/`MulOperation`/`RTypeReader` sub-circuits, witnesses the result word
`a` and the five variant flags, and gates `is_real` — the six booleans + `op_a_0` (captured in
`AssertSpec`) and the soundness/completeness proofs are deferred (`sorry`). `Mul` carries the `2^24 < p`
field bound (the `MulOperation` column-sum bound), unlike the `2^17` of the other chips. -/

namespace SP1Clean.MulChip

open Circuit
open Extracted (MulCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- **Assertion half** — the literal meaning of SP1's `MulCols.asserts` *own* (inline) assertZero tail
(everything past the composed `MulOperation`/`CPUState`/`RTypeReader` sub-lists), in extracted order
(`Extracted/MulChip.lean`: `E5,E7,E9,E11,E13,E15, op_a_0`): the five variant-flag booleans (`is_mul`,
`is_mulh`, `is_mulhu`, `is_mulw`, `is_mulhsu` — note SP1's extraction order), the sum-bound boolean on
`E3 = is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw`, and the `op_a_0` zeroing flag. The heavy
schoolbook arithmetic is *not* here — it is the composed `MulOperation` sub-list. -/
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

/-- **Interaction half** — SP1's `MulCols.interactions` *own* tail is **empty** (`Extracted/MulChip.lean`
ends `… ++ [ ]`): every byte-range pull for the multiply lives inside the composed `MulOperation`
sub-list (the `U16toU8` decompositions, the product/carry byte checks), anchored at the operation level.
So the chip's own interaction meaning is trivial. -/
def InteractSpec (_cols : MulCols (ZMod p)) : Prop := True

/-- Compose the threaded `CPUState`/`RTypeReader` reader blocks and the witnessed `MulOperation` gadget
as Clean sub-circuits, **witness** the result word `a` and the five variant flags, gate `is_real`, and
assemble the extracted `MulCols` struct. The `RTypeReader` carries `Mul`'s opcode
`is_mul·11 + is_mulh·12 + is_mulhu·13 + is_mulhsu·14 + is_mulw·24` (`Extracted/MulChip.lean` E16–E23) and
the `op_a_write_value` limbs `a[0..3]`.

Skeleton note: the six booleans + `op_a_0` (`AssertSpec`) are **not yet emitted** in `main` — the
witnessed `a`/flags are currently unconstrained beyond the composed sub-circuits. The **`a = MulOperation.resultWord`
linkage** is also deferred: the native `MulOperation.circuit` reconstructs `resultWord` internally (it
does *not* take `a` as input), whereas SP1's `MulOperation.asserts` takes `a_word` and ties product→`a`;
the eventual soundness proof must add that per-variant link. Filling these in (and a faithful `populate`
for the witnesses) is the deferred proof-fill step; the byte channel is already carried by the
`MulOperation` sub-circuit. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var MulCols (ZMod p)) := do
  assertion Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  let flags ← witnessVector 5 (fun _ => (#v[0, 0, 0, 0, 0] : Vector (ZMod p) 5))
  let is_mul := flags[0]; let is_mulh := flags[1]; let is_mulhu := flags[2]
  let is_mulhsu := flags[3]; let is_mulw := flags[4]
  -- The chip **witnesses the whole `MulOperation` column struct** via the operation's `populate`
  -- (anchored to SP1's real `populate` by `WitnessTests/MulOperationWitness.lean`), then composes the
  -- demoted `MulOperation` gadget as a Clean `assertion` over `⟨b, c, cols, is_real, flags…⟩` (SP1's
  -- `MulOperation::eval`). `populate` takes `(b, c, is_mulh, is_mulhsu, is_mulw)`. Mirrors SP1's chip =
  -- row-populate (calls the operation populate) + eval (calls the operation eval).
  let cols ← ProvableType.witness (fun env =>
    MulOperation.populate
      #v[env input.op_b_val[0], env input.op_b_val[1], env input.op_b_val[2], env input.op_b_val[3]]
      #v[env input.op_c_val[0], env input.op_c_val[1], env input.op_c_val[2], env input.op_c_val[3]]
      (env is_mulh) (env is_mulhsu) (env is_mulw))
  -- gate `MulOperation` by the **flag-sum** (`is_mul + … + is_mulw`), exactly as SP1
  -- (`alu/mul/mod.rs:234`: `let is_real = local.is_mul + … + local.is_mulw`). This is what makes the
  -- operation's `is_mulw → is_real` precondition discharge (`is_mulw = 1 → sum = 1`).
  assertion MulOperation.circuit
    ⟨input.op_b_val, input.op_c_val, cols, is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw,
      is_mul, is_mulh, is_mulhu, is_mulhsu, is_mulw⟩
  -- **`a`↔`resultWord` linkage** (`MulOperation.aSelector`, inlined over the witnessed `cols` product
  -- columns): the register-write word `a` is the flag-weighted product slice — `MUL`/`MULW` low bytes,
  -- the `MULH*` family bytes 8..15, `MULW`'s upper limbs the product sign bit `* 65535`. Witnessed and
  -- gated so soundness ties `cols.a = resultWord` (via `aSelector_eq_resultWord`) and completeness
  -- populates it directly. Mirrors SP1's `MulOperation.asserts` product→`a` tie (lifted to the chip).
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
  -- witnesses flags(5) + the `MulOperation` column struct `cols`(45) + a(4) = 54; the composed
  -- `MulOperation` is now a `FormalAssertion` (0 witnesses — `cols` is an input), and the
  -- `CPUState`/`RTypeReader` assertions add no witnesses. 5 + 45 + 4 = 54.
  localLength _ := 54
  localLength_eq := by simp +arith [circuit_norm, main, MulOperation.circuit, Readers.CPUState.circuit, Readers.RTypeReader.circuit]
  subcircuitsConsistent := by simp only [circuit_norm, main, MulOperation.circuit, Readers.CPUState.circuit, Readers.RTypeReader.circuit]; try omega
  channelsWithGuarantees := [byteChannel.toRawGated]
  channelsWithRequirements :=
    [byteChannel.toRawGated, stateChannel.toRawGated, memoryChannel.toRaw, programChannel.toRaw]
  channelsLawful := by simp [circuit_norm, main, MulOperation.circuit, Readers.CPUState.circuit, Readers.RTypeReader.circuit]

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
    (elaborated (p := p)).localLength x = 54 := rfl

end SP1Clean.MulChip
