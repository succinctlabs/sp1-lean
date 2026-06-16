import SP1Clean.Math.Word
import SP1Clean.Extracted.AddwOperation

/-! # `AddwOperation` — `populate` (the witness generator)

SP1's `AddwOperation::populate` ported natively: the low two u16 limbs of `(a+b) mod 2^32`
(`addwValueWitness`) and bit 15 of the high result limb (`addwMsbWitness`, via the nested
`U16MSBOperation::populate_msb`), packaged into the `Extracted.AddwOperation` column struct. The
composing `AddwChip` witnesses the columns with this. `spec_populate` lives in `Formal` (it references
`Spec`, which — to avoid an import cycle through the composed `U16MSBOperation.Formal` — also lives in
`Formal`). Only `a[0..1]`/`b[0..1]` are read; the high limbs are ignored, matching ADDW. -/

namespace SP1Clean.AddwOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Native witness function ported from SP1's `AddwOperation::populate`: the low two u16 limbs of
`(a+b) mod 2^32`. (Only `a[0..1]`/`b[0..1]` are read; the high limbs are ignored, matching ADDW.) -/
def addwValueWitness (a b : Word (ZMod p)) : Vector (ZMod p) 2 :=
  let s0 := a[0].val + b[0].val
  let s1 := a[1].val + b[1].val + s0 / 65536
  #v[((s0 % 65536 : ℕ) : ZMod p), ((s1 % 65536 : ℕ) : ZMod p)]

/-- The `msb` column SP1's `populate` writes: bit 15 of the high result limb `value[1]`
(`= value[1].val / 2^15`), via the nested `U16MSBOperation::populate_msb`. -/
def addwMsbWitness (a b : Word (ZMod p)) : ZMod p :=
  (((addwValueWitness a b)[1].val / 32768 : ℕ) : ZMod p)

/-- The witnessed column struct: the two low result limbs `value` and the sign bit `msb`. The
composing `AddwChip` witnesses the columns with this. -/
def populate (a b : Word (ZMod p)) : Extracted.AddwOperation (ZMod p) :=
  ⟨addwValueWitness a b, ⟨addwMsbWitness a b⟩⟩

end SP1Clean.AddwOperation
