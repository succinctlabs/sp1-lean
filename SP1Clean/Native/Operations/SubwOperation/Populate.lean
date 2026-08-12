import SP1Clean.Math.Word
import SP1Clean.FormalModel.Contracts.Operations

/-! # `SubwOperation` — `populate` (the witness generator, borrow-form analog of `AddwOperation`)

SP1's `SubwOperation::populate` ported natively: the low two u16 limbs of `(a-b) mod 2^32` in
two's-complement borrow form (`subwValueWitness`, carry init `1`, complement `65535 - b[i]`) and bit 15
of the high result limb (`subwMsbWitness`), packaged into the native `Columns` struct.
The composing `SubwChip` witnesses the columns with this; `spec_populate` lives in `Formal`. -/

namespace SP1Clean.SubwOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Native witness function ported from SP1's `SubwOperation::populate`: the low two u16 limbs of
`(a-b) mod 2^32` in two's-complement borrow form (carry init `1`). -/
def subwValueWitness (a b : Word (ZMod p)) : Vector (ZMod p) 2 :=
  let s0 := a[0].val + (65535 - b[0].val) + 1
  let s1 := a[1].val + (65535 - b[1].val) + s0 / 65536
  #v[((s0 % 65536 : ℕ) : ZMod p), ((s1 % 65536 : ℕ) : ZMod p)]

/-- The `msb` column SP1's `populate` writes: bit 15 of `value[1]`. -/
def subwMsbWitness (a b : Word (ZMod p)) : ZMod p :=
  (((subwValueWitness a b)[1].val / 32768 : ℕ) : ZMod p)

/-- The witnessed column struct: the two low result limbs `value` and the sign bit `msb`. -/
def populate (a b : Word (ZMod p)) : Columns (ZMod p) :=
  ⟨subwValueWitness a b, ⟨subwMsbWitness a b⟩⟩

end SP1Clean.SubwOperation
