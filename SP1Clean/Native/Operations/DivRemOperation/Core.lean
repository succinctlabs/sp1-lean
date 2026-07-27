import SP1Clean.Native.Operations.MulOperation
import SP1Clean.Native.Operations.DivRemOperation.OwnAsserts
import SP1Clean.Native.Operations.DivRemOperation.AssertZeros
import SP1Clean.FormalModel.Contracts.DivRemColumns
import SP1Clean.Model.Channels
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # `DivRemCore` — the DivRem chip's product/own-assert/byte-range assertion cluster

The structural twin of `DivRemCompare` (`Compare.lean`): the DivRem chip `main`'s remaining
non-reader constraint content, as a standalone Clean `FormalAssertion` over the **whole committed
row** (`DivRemChip.Columns`). Like the comparison cluster it witnesses nothing — every column it
constrains is a field of the input `cols` — so its `localLength` is `0`. It carries:

* `MulOperation` ×2 — the two `c_times_quotient = quotient_comp · c` product structs: `lower`
  (low 64 bits, gate + `is_mul` = `is_real`) and `upper` (high 64 bits, gate = `is_real_not_word`,
  `is_mulh = is_div + is_rem` signed / `is_mulhu = is_divu + is_remu` unsigned);
* the 8 inline product-glue `assertZero`s tying the `c_times_quotient` u16 limbs to the Mul
  gadgets' product bytes — limbs 0–3 to `lower`'s bytes 0–7 under `is_real`, limbs 4–7 to
  `upper`'s bytes 8–15 gated by the 64-bit flag sum `g64 = is_div + is_divu + is_rem + is_remu`;
* the chip's own assertZero tail `assertZeros (ownAsserts cols)` (the `[E13…E367, op_a_0]` list);
* the 32 `byteChannel` u16 `Range` pulls: the 8 carry-chain limbs (`E123…E151`, rebuilt over the
  committed columns with the `rn = rem_neg · 65535` sign-fill addend) and the
  `abs_c`/`abs_remainder`/`quotient`/`remainder`/`c_times_quotient` limbs, all gated `is_real`.
  The word-gated `remainder[1]`/`quotient[1]` pulls belong to the two corresponding
  `U16MSBOperation` subcircuits in `DivRemCompare`; they are not duplicated here.

The emission order and every argument are verbatim from `Proofs/Chips/DivRemChip/Defs.lean` `main`
(lines 258–282, 406–456), with each witnessed local replaced by the corresponding `DivRemChip.Columns`
field per the chip's cols assembly. The semantic contract is `DivRemCore.CoreSpec`
(`FormalModel/Contracts/DivRem.lean`); the `FormalAssertion` bundle is
`Proofs/Operations/DivRemOperation/Core.lean`. -/

namespace SP1Clean.DivRemCore

open Circuit
open SP1Clean.Channels (byteChannel)
open SP1Clean.DivRemChip (ownAsserts assertZeros)

-- The cluster composes `MulOperation` (schoolbook product column sums ≈ 2^24 before the ZMod→ℕ
-- lift), so it carries the `Fact (2 ^ 24 < p)` field bound — subsuming the project-wide `2 ^ 17`.
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- Emit the DivRem row's product cluster (`MulOperation` ×2 + the 8 glue asserts), the chip's own
assertZero tail (`ownAsserts`), and the 32 byte-range pulls, each applied to the committed `cols`
fields. No witnesses — the only fresh state is the composed `MulOperation` assertions' channel
activity plus the cluster's own byte pulls. -/
def main (cols : Var DivRemChip.Columns (ZMod p)) : Circuit (ZMod p) Unit := do
  -- (1,2) The two `c_times_quotient` product structs (`divrem/mod.rs:721`): `lower` = low product,
  -- gate + `is_mul` = `is_real`; `upper` = high product, gate = `is_real_not_word`,
  -- `is_mulh = is_div + is_rem`, `is_mulhu = is_divu + is_remu`. Both have `is_mulw = 0`.
  assertion MulOperation.circuit
    ⟨cols.quotient_comp, cols.c, cols.c_times_quotient_lower,
     cols.is_real, cols.is_real, 0, 0, 0, 0⟩
  assertion MulOperation.circuit
    ⟨cols.quotient_comp, cols.c, cols.c_times_quotient_upper,
     cols.is_real_not_word, 0, cols.is_div + cols.is_rem, cols.is_divu + cols.is_remu, 0, 0⟩
  -- Link `c_times_quotient` to the two Mul gadgets' product bytes. SP1 gates the low result
  -- placement by `is_mul = is_real`; retaining that gate is essential on adversarial padding
  -- rows. The high 64 (limbs 4..7) is gated by the 64-bit flag sum (on word rows `upper` is
  -- all-zero while `c_times_quotient[4..7]` carries the 128-bit product's sign-extension limbs,
  -- so an unconditional tie would be unsatisfiable by the honest witness).
  let c256 : Expression (ZMod p) := 256
  let g64 := cols.is_div + cols.is_divu + cols.is_rem + cols.is_remu
  cols.is_real * (cols.c_times_quotient[0] -
    (cols.c_times_quotient_lower.product[0] +
      cols.c_times_quotient_lower.product[1] * c256)) === 0
  cols.is_real * (cols.c_times_quotient[1] -
    (cols.c_times_quotient_lower.product[2] +
      cols.c_times_quotient_lower.product[3] * c256)) === 0
  cols.is_real * (cols.c_times_quotient[2] -
    (cols.c_times_quotient_lower.product[4] +
      cols.c_times_quotient_lower.product[5] * c256)) === 0
  cols.is_real * (cols.c_times_quotient[3] -
    (cols.c_times_quotient_lower.product[6] +
      cols.c_times_quotient_lower.product[7] * c256)) === 0
  g64 * (cols.c_times_quotient[4] -
    (cols.c_times_quotient_upper.product[8] + cols.c_times_quotient_upper.product[9] * c256)) === 0
  g64 * (cols.c_times_quotient[5] -
    (cols.c_times_quotient_upper.product[10] + cols.c_times_quotient_upper.product[11] * c256)) === 0
  g64 * (cols.c_times_quotient[6] -
    (cols.c_times_quotient_upper.product[12] + cols.c_times_quotient_upper.product[13] * c256)) === 0
  g64 * (cols.c_times_quotient[7] -
    (cols.c_times_quotient_upper.product[14] + cols.c_times_quotient_upper.product[15] * c256)) === 0
  -- The chip's own assertZero constraints (`E13…E367`, `op_a_0`, incl. the binary gates like
  -- `is_real·(is_real-1)` = E355) via `ownAsserts`.
  assertZeros (ownAsserts cols)
  -- Byte-range tail (opcode `Range` = 6, all gated `is_real`): the 8 carry-chain u16 limbs
  -- (`E123…E151`) and `abs_c`/`abs_remainder`/`quotient`/`remainder`/`c_times_quotient` limbs.
  -- `rn := rem_neg·65535` (`E120`) is the high-limb addend.
  let rn : Expression (ZMod p) := cols.rem_neg * (65535 : Expression (ZMod p))
  let e123 : Expression (ZMod p) :=
    cols.c_times_quotient[0] + cols.remainder_comp[0] - cols.carry[0] * (65536 : Expression (ZMod p))
  let e127 : Expression (ZMod p) :=
    cols.c_times_quotient[1] + cols.remainder_comp[1] - cols.carry[1] * (65536 : Expression (ZMod p))
      + cols.carry[0]
  let e131 : Expression (ZMod p) :=
    cols.c_times_quotient[2] + cols.remainder_comp[2] - cols.carry[2] * (65536 : Expression (ZMod p))
      + cols.carry[1]
  let e135 : Expression (ZMod p) :=
    cols.c_times_quotient[3] + cols.remainder_comp[3] - cols.carry[3] * (65536 : Expression (ZMod p))
      + cols.carry[2]
  let e139 : Expression (ZMod p) :=
    cols.c_times_quotient[4] + rn - cols.carry[4] * (65536 : Expression (ZMod p)) + cols.carry[3]
  let e143 : Expression (ZMod p) :=
    cols.c_times_quotient[5] + rn - cols.carry[5] * (65536 : Expression (ZMod p)) + cols.carry[4]
  let e147 : Expression (ZMod p) :=
    cols.c_times_quotient[6] + rn - cols.carry[6] * (65536 : Expression (ZMod p)) + cols.carry[5]
  let e151 : Expression (ZMod p) :=
    cols.c_times_quotient[7] + rn - cols.carry[7] * (65536 : Expression (ZMod p)) + cols.carry[6]
  let g := cols.is_real
  byteChannel.pullIf g (⟨6, e123, 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, e127, 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, e131, 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, e135, 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, e139, 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, e143, 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, e147, 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, e151, 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, cols.abs_c[0], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, cols.abs_c[1], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, cols.abs_c[2], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, cols.abs_c[3], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, cols.abs_remainder[0], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, cols.abs_remainder[1], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, cols.abs_remainder[2], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, cols.abs_remainder[3], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, cols.quotient[0], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, cols.quotient[1], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, cols.quotient[2], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, cols.quotient[3], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, cols.remainder[0], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, cols.remainder[1], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, cols.remainder[2], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, cols.remainder[3], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, cols.c_times_quotient[0], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, cols.c_times_quotient[1], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, cols.c_times_quotient[2], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, cols.c_times_quotient[3], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, cols.c_times_quotient[4], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, cols.c_times_quotient[5], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, cols.c_times_quotient[6], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, cols.c_times_quotient[7], 16, 0⟩ : ByteRow (Expression (ZMod p)))

set_option maxHeartbeats 4000000 in
/-- Clean derives the structural metadata; the cluster contributes no fresh witnesses
(`localLength = 0`) and exposes only the byte-channel guarantees (its own pulls + the composed
`MulOperation`s'). -/
instance elaborated : ElaboratedCircuit (ZMod p) DivRemChip.Columns unit main := by
  elaborate_circuit_with {
    channelsWithGuarantees := [byteChannel.toRaw]
  }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [byteChannel.toRaw] := rfl

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var DivRemChip.Columns (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

end SP1Clean.DivRemCore
