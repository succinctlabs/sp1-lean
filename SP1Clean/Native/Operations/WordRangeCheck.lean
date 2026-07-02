import SP1Clean.Math.Word
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Bits
import Clean.Utils.Tactics

/-! # `WordRangeCheck` — the whole-`Word` 16-bit range check as a Clean `FormalAssertion`

Asserts that all four limbs of a `Word` are genuine 16-bit values, by composing
`Gadgets.ToBits.rangeCheck 16` (a real bit-decomposition, not a lookup — it owes nothing to a bus)
per limb. Proved **once** over the whole word, so the composed `Spec` is the single semantic fact
`Word.isU64 w` — a consumer (the memory-boundary provider's `memoryChannel.pushIf`,
`Proofs/Chips/MemoryProviderChip.lean`) gets `isU64` directly from the subcircuit's `Spec` instead of
re-assembling four per-limb bounds via `Word.isU64_of_cases`.

`Assumptions` is `True` (not `Word.isU64`): a composed `FormalAssertion`'s soundness payload is
`Assumptions → Spec` (`ConstraintsHold.Soundness`), so a non-trivial precondition here would collapse
the payload to the tautology `isU64 → isU64` and starve the consumer. Completeness still has the limb
bounds — a `FormalAssertion`'s completeness receives the `Spec` (the prover must satisfy
`Assumptions ∧ Spec` to use an assertion), which is exactly `Word.isU64 w`. -/

namespace SP1Clean.WordRangeCheck

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- `p > 2`, needed by `Gadgets.ToBits.rangeCheck`'s `Fact (p > 2)`. `local` so it does not leak. -/
local instance : Fact (p > 2) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

omit [Fact p.Prime] in
/-- `2 ^ 16 < p` — the width bound `rangeCheck 16` needs for the limbs. -/
lemma two_pow_sixteen_lt : (2 : ℕ) ^ 16 < p := by
  have h := Fact.out (p := 2 ^ 17 < p)
  have h2 : (2 : ℕ) ^ 16 < 2 ^ 17 := by norm_num
  omega

/-- Range-check each of the four limbs of `w` to 16 bits (four genuine bit-decomposition
`assertion`s — no witnesses of its own beyond the sub-gadgets' bit columns, no interactions). -/
def main (w : Var Word (ZMod p)) : Circuit (ZMod p) Unit := do
  assertion (Gadgets.ToBits.rangeCheck 16 two_pow_sixteen_lt) w[0]
  assertion (Gadgets.ToBits.rangeCheck 16 two_pow_sixteen_lt) w[1]
  assertion (Gadgets.ToBits.rangeCheck 16 two_pow_sixteen_lt) w[2]
  assertion (Gadgets.ToBits.rangeCheck 16 two_pow_sixteen_lt) w[3]

instance elaborated : ElaboratedCircuit (ZMod p) Word unit main where
  -- 4 limbs × 16 bit-decomposition witnesses each.
  localLength _ := 64
  output _ _ := ()
  channelsWithGuarantees := []

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p))) = [] := rfl

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Word (ZMod p)) :
    (elaborated (p := p)).localLength x = 64 := rfl

/-- No preconditions: the four bit decompositions prove the limb bounds unconditionally. (The bounds a
prover needs for completeness flow in through `Spec` — see the module doc-comment.) -/
def Assumptions (_ : Word (ZMod p)) : Prop := True

/-- The whole-`Word` 16-bit range check: every limb `< 2^16`, as the single fact `Word.isU64`. -/
def Spec (w : Word (ZMod p)) : Prop := Word.isU64 w

theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start [Gadgets.ToBits.rangeCheck, Spec]
  obtain ⟨h0, h1, h2, h3⟩ := h_holds
  subst h_input
  exact Word.isU64_of_cases (by simpa using h0) (by simpa using h1)
    (by simpa using h2) (by simpa using h3)

theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start [Gadgets.ToBits.rangeCheck, Spec]
  subst h_input
  exact ⟨by simpa using h_spec 0, by simpa using h_spec 1,
    by simpa using h_spec 2, by simpa using h_spec 3⟩

/-- The whole-`Word` 16-bit range check as a Clean `FormalAssertion`: four per-limb
`rangeCheck 16` bit decompositions, exposed as the single semantic `Spec` `Word.isU64 w`. -/
def circuit : FormalAssertion (ZMod p) Word :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    soundness := soundness, completeness := completeness }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Word (ZMod p)) :
    circuit.localLength x = 64 := rfl

end SP1Clean.WordRangeCheck
