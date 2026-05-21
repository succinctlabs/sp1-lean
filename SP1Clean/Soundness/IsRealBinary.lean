import SP1Clean.Soundness.StateConsistency

/-! # Surfacing `is_real ∈ {0, 1}` per chip row

Every SP1Clean chip's `Spec` carries a clause of the form
`is_real * (is_real - 1) = 0` (sometimes written on the sub-opcode
sum for chips without an explicit `is_real` column — Branch, Mul,
Lt, ShiftLeft, ShiftRight, LoadX0, LoadByte, LoadHalf, LoadWord).

This file provides:

- A generic field-level `binary_of_assertZero` lemma deriving
  `x ∈ {0, 1}` from `x * (x - 1) = 0`.
- A trace-level predicate `TraceIsRealBinary` asserting that the
  `is_real` projection of every chip row's `stateAccess` is in
  `{0, 1}`.

The discharge of `TraceIsRealBinary` from each chip's `Spec` is a
deferred per-chip case analysis (20 chips × one-conjunct
projection), structurally analogous to the `TraceClkValid` and
`TraceStateValid` bundled hypotheses in
`MemoryConsistencyClock.lean` and `StateConsistency.lean`.

`TraceIsRealBinary` is the hook by which Phase C's multiplicity-
gating lemmas (`SP1Clean.Multiplicity`) fire at the trace level — any
per-row `send`/`receive` with `mult = (stateAccess row).is_real` can
be turned into a stateless-table membership claim. -/

namespace SP1Clean.Soundness

open SP1Clean

variable {p : ℕ} [Fact p.Prime]

/-- Generic field-level binarity: in a `ZMod p` for prime `p`,
`x * (x - 1) = 0` gives `x = 0 ∨ x = 1`. -/
theorem binary_of_assertZero (x : ZMod p) (h : x * (x - 1) = 0) :
    x = 0 ∨ x = 1 := by
  rcases mul_eq_zero.mp h with hx | hxm1
  · exact Or.inl hx
  · exact Or.inr (by linear_combination hxm1)

variable [Fact (2 ^ 17 < p)]

/-- Trace-level `is_real` binarity: every row's `stateAccess.is_real`
projection is in `{0, 1}`.

Deferred discharge: this is implied by `∀ row ∈ rows, row.Spec`
(every chip's `Spec` contains the corresponding `is_real * (is_real -
1) = 0` clause), via per-chip case analysis that selects the right
conjunct. Pending that case analysis, `TraceIsRealBinary` is supplied
by the verifier as part of the trace-shape bundle. -/
def TraceIsRealBinary (rows : List (ChipRow p)) : Prop :=
  ∀ row ∈ rows, (ChipRow.stateAccess row).is_real = 0 ∨
                (ChipRow.stateAccess row).is_real = 1

end SP1Clean.Soundness
