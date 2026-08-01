import SP1Clean.Native.Operations.IsZeroWordOperation.RawSpec
import SP1Clean.Native.Operations.IsZeroWordOperation.Populate
import SP1Clean.Native.Operations.IsZeroWordOperation.Defs

/-! # `IsZeroWordOperation` — the `FormalAssertion` (Spec / soundness / completeness / contract)

SP1's `IsZeroWordOperation::eval` as a Clean `FormalAssertion`. Composes `IsZeroOperation` on each
limb; the `Spec` references the four per-limb `IsZeroOperation.Spec`s by direct field application
plus the ungated booleanness/half-product clauses and the gated AND-tree. `spec_populate` lets the
composing operation discharge its `assertion`-side obligation; `result_semantic` exposes the semantic
readout. `Spec`/`spec_populate` live here (not in `Specs.Operation`) to avoid an import cycle. -/

namespace SP1Clean.IsZeroWordOperation

open Circuit

-- Nothing in the gadget itself needs a magnitude fact; it is reintroduced at the bottom for
-- `circuit_localLength`, whose signature carries the binder.
variable {p : ℕ} [Fact p.Prime]

/-- `is_real` is binary (discharged by the composing op's gate). No operand precondition. -/
def Assumptions (input : Inputs (ZMod p)) : Prop := input.is_real = 0 ∨ input.is_real = 1

/-- Faithful semantic contract (equivalent to the constraints). `result` booleanness and the two
half-product gluings are ungated (hold on padding too); the four per-limb `IsZeroOperation.Spec`s
are referenced by direct field application; the AND-tree `result = first·second` is `is_real`-gated.
The semantic `result = (a = 0)` is recovered by `result_semantic`. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  (input.cols.result = 0 ∨ input.cols.result = 1) ∧
  (input.cols.is_zero_first_half =
      input.cols.is_zero_limb_0.result * input.cols.is_zero_limb_1.result) ∧
  (input.cols.is_zero_second_half =
      input.cols.is_zero_limb_2.result * input.cols.is_zero_limb_3.result) ∧
  IsZeroOperation.Spec ⟨input.a[0], input.cols.is_zero_limb_0, input.is_real⟩ ∧
  IsZeroOperation.Spec ⟨input.a[1], input.cols.is_zero_limb_1, input.is_real⟩ ∧
  IsZeroOperation.Spec ⟨input.a[2], input.cols.is_zero_limb_2, input.is_real⟩ ∧
  IsZeroOperation.Spec ⟨input.a[3], input.cols.is_zero_limb_3, input.is_real⟩ ∧
  (input.is_real = 1 →
      input.cols.result = input.cols.is_zero_first_half * input.cols.is_zero_second_half)

theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hs0, hs1, hs2, hs3, _hbreal, hbres, hf, hsec, hg⟩ := h_holds
  obtain ⟨hia, -⟩ := h_input
  have ea : ∀ i (hi : i < 4), Expression.eval env input_var_a[i] = input_a[i] := by
    intro i hi; rw [← hia]; simp only [Vector.getElem_map]
  simp only [ea] at hs0 hs1 hs2 hs3
  refine ⟨⟨bool_of_mul_pred (by simpa only [sub_eq_add_neg] using hbres),
      eq_of_sub_eq_zero hf, eq_of_sub_eq_zero hsec, hs0 h_assumptions, hs1 h_assumptions,
      hs2 h_assumptions, hs3 h_assumptions, ?_⟩, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro hr1
  rw [hr1, one_mul] at hg
  exact eq_of_sub_eq_zero hg

theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hbres, hf, hsec, hS0, hS1, hS2, hS3, hg⟩ := h_spec
  obtain ⟨hia, -⟩ := h_input
  have ea : ∀ i (hi : i < 4), Expression.eval env.toEnvironment input_var_a[i] = input_a[i] := by
    intro i hi; rw [← hia]; simp only [Vector.getElem_map]
  simp only [ea]
  refine ⟨⟨h_assumptions, hS0⟩, ⟨h_assumptions, hS1⟩, ⟨h_assumptions, hS2⟩,
    ⟨h_assumptions, hS3⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rcases h_assumptions with h | h <;> simp [h]
  · rcases hbres with h | h <;> simp [h]
  · simp [hf]
  · simp [hsec]
  · rcases h_assumptions with h | h
    · simp [h]
    · rw [h, one_mul, hg h]; simp

/-- The populated `result` is boolean for **any** source word (a product of per-limb `0/1`
indicators) — the ungated structural fact `spec_populate_offGate` needs. -/
theorem populate_result_bool (w : Word (ZMod p)) :
    (populate w).result = 0 ∨ (populate w).result = 1 := by
  simp only [populate, IsZeroOperation.populate]
  by_cases h0 : w[0] = 0 <;> by_cases h1 : w[1] = 0 <;> by_cases h2 : w[2] = 0 <;>
    by_cases h3 : w[3] = 0 <;> simp [h0, h1, h2, h3]

/-- The witnessed columns `populate a` satisfy the gadget `Spec` for any `is_real`. The composing op
(`IsEqualWord`) / top-level chip uses this to discharge the `assertion IsZeroWordOperation.circuit`
prover obligation. -/
theorem spec_populate (a : Word (ZMod p)) (is_real : ZMod p) :
    Spec (⟨a, populate a, is_real⟩ : Inputs (ZMod p)) :=
  ⟨populate_result_bool a, rfl, rfl, IsZeroOperation.spec_populate a[0] is_real,
    IsZeroOperation.spec_populate a[1] is_real, IsZeroOperation.spec_populate a[2] is_real,
    IsZeroOperation.spec_populate a[3] is_real, fun _ => rfl⟩

/-- Semantic exposure: on a real row the `Spec` forces `result` to be the word zero-indicator. -/
theorem result_semantic {input : Inputs (ZMod p)} (h : Spec input) (hr : input.is_real = 1) :
    input.cols.result =
      if (input.a[0] = 0 ∧ input.a[1] = 0 ∧ input.a[2] = 0 ∧ input.a[3] = 0) then 1 else 0 := by
  obtain ⟨_, hf, hs, hS0, hS1, hS2, hS3, hg⟩ := h
  exact result_collapse (hS0 hr).1 (hS1 hr).1 (hS2 hr).1 (hS3 hr).1 hf hs (hg hr)

/-- `Spec` with the gate off (`is_real = 0`) holds at the populate of **any** word `w` — not just
the operand `a`. A composing chip can share one witnessed struct between two differently-gated
assertions with different operand words (`DivRemChip`'s `is_overflow_b/c`: full-word @
`is_real_not_word` vs truncated @ the word-variant gate); the off-gate assertion only needs the
ungated structural conjuncts, which `populate` satisfies regardless of its source word. -/
theorem spec_populate_offGate (a w : Word (ZMod p)) {is_real : ZMod p} (hr : is_real = 0) :
    Spec (⟨a, populate w, is_real⟩ : Inputs (ZMod p)) :=
  ⟨populate_result_bool w, rfl, rfl,
    fun h1 => absurd (hr.symm.trans h1) zero_ne_one,
    fun h1 => absurd (hr.symm.trans h1) zero_ne_one,
    fun h1 => absurd (hr.symm.trans h1) zero_ne_one,
    fun h1 => absurd (hr.symm.trans h1) zero_ne_one,
    fun h1 => absurd (hr.symm.trans h1) zero_ne_one⟩

/-- `Spec` at the all-zero column struct with the gate off (`is_real = 0`) — the inactive-row
discharge for composing chips whose populate leaves the struct zero. The operand is arbitrary. -/
theorem spec_zero (a : Word (ZMod p)) {is_real : ZMod p} (hr : is_real = 0) :
    Spec (⟨a, zeroCols, is_real⟩ : Inputs (ZMod p)) :=
  ⟨Or.inl rfl, (mul_zero 0).symm, (mul_zero 0).symm,
    fun h1 => absurd (hr.symm.trans h1) zero_ne_one,
    fun h1 => absurd (hr.symm.trans h1) zero_ne_one,
    fun h1 => absurd (hr.symm.trans h1) zero_ne_one,
    fun h1 => absurd (hr.symm.trans h1) zero_ne_one,
    fun h1 => absurd (hr.symm.trans h1) zero_ne_one⟩

/-- SP1's `IsZeroWordOperation::eval` as a Clean-native `FormalAssertion`. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

section LocalLength
variable [Fact (2 ^ 17 < p)]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end LocalLength

end SP1Clean.IsZeroWordOperation
