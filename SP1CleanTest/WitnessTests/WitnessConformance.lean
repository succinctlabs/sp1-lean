import SP1Clean.Math.Word
import Mathlib.Tactic.NormNum.Prime

/-! # Shared scaffolding for witness-generation conformance anchors.

Each `WitnessTests/<Op>Witness.lean` checks that the native Lean witness function — the one the gadget's
`main` actually uses — reproduces, on every vector dumped from SP1's **real** `<Op>::populate`
(`WitnessTests/Vectors/<Op>.lean`; the namespace is `<Op>WitnessVectors`), the exact column values
`populate` wrote.

The witness functions are field-generic over `ZMod p` (uniform with the chips); conformance is
checked here at SP1's **concrete field** (KoalaBear), which is where SP1's prover actually runs — so
"conforms at KoalaBear" is the meaningful statement, and any field-specific witness data (e.g. the
`not_eq_inv = (b-c)⁻¹` inverse column in the comparison ops) is checked at a definite value that has
no ℕ analogue. The concrete-prime evaluation stays isolated to this conformance layer — the chips
never see it.

This is a *conformance* tie, not an all-inputs proof: `populate` is native imperative code that
cannot be symbolically extracted like `eval`, so we pin agreement on a fixed input battery (edge
cases + a seeded LCG). It is a completeness/liveness property — it catches silent drift between the
Lean witness and SP1's trace generator; soundness lives entirely on the constraint side. Each anchor
proves its `…Conforms`-fold `= true` by `native_decide`, which adds generated
`._native.native_decide.ax_*` compiler-trust constants — deliberately confined to these files so
the gadget soundness theorems stay
`[propext, Classical.choice, Quot.sound]`. Corrupting any vector fails the build. -/

namespace SP1Clean.WitnessTests

open SP1Clean

/-- SP1's field is KoalaBear, the prime `2^31 - 2^24 + 1`. SP1's prover runs here, so witness
conformance is checked at this concrete field. The gadgets' `Fact p.Prime` (which the witness
functions share) is discharged here once, at the concrete prime. -/
abbrev SP1Prime : ℕ := 2130706433

instance instFactSP1Prime : Fact (Nat.Prime SP1Prime) := ⟨by native_decide⟩

/-- Cast a vector of ℕ values (dumped canonical limbs/bytes/columns) into a field vector over SP1's
field — works at any width (operand words, comparison limbs, flag vectors). -/
def toFieldVec {n : ℕ} (w : Vector ℕ n) : Vector (ZMod SP1Prime) n :=
  w.map (fun x : ℕ => (x : ZMod SP1Prime))

/-- Cast a vector of ℕ limbs into a `Word` over SP1's field (the width-4 specialisation). -/
def toWord (w : Vector ℕ 4) : Word (ZMod SP1Prime) := toFieldVec w

/-- Cast a single ℕ (a dumped canonical field value, e.g. an inverse column) into SP1's field. -/
def toField (n : ℕ) : ZMod SP1Prime := (n : ZMod SP1Prime)

end SP1Clean.WitnessTests
