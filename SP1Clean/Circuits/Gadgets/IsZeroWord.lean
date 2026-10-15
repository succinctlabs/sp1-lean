module

public import SP1Clean.Semantics.Specs.IsZeroWord
public import SP1Clean.Circuits.Gadgets.IsZero
import Mathlib.Tactic.IntervalCases
import Clean.Utils.Tactics.CircuitProofStart

/-! # Word zero-test gadget

The typed and Clean-IR witnesses, circuit and bundled correctness proofs share this module.
The pure contract is in `Semantics/Specs/IsZeroWord`. `AssertSpec` supports the
transitional comparison with independently extracted Rust assertions.
-/

@[expose] public section

namespace SP1Clean.IsZeroWordOperation

open Circuit

variable {p : ℕ} [Fact p.Prime]

/-- The witnessed column struct: per-limb `IsZeroOperation.populate`, the two half-products, and
`result = first_half * second_half`. -/
def populate (a : Word (ZMod p)) : Circuits.Types.IsZeroWordOperation (ZMod p) :=
  let l0 := IsZeroOperation.populate a[0]
  let l1 := IsZeroOperation.populate a[1]
  let l2 := IsZeroOperation.populate a[2]
  let l3 := IsZeroOperation.populate a[3]
  let fh := l0.result * l1.result
  let sh := l2.result * l3.result
  ⟨l0, l1, l2, l3, fh, sh, fh * sh⟩

/-- The all-zero column struct — the witness on rows where the gadget is inactive and SP1 leaves
the struct unpopulated (gated `IsZeroWord`/`IsEqualWord` composition on padding rows). `spec_zero`
discharges the composed assertion's obligation at this value. -/
def zeroCols : Circuits.Types.IsZeroWordOperation (ZMod p) :=
  ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, 0, 0, 0⟩

section FE

/-- The witness-IR twin of `populate`: per-limb `IsZeroOperation.populateFE`, the two half
products, and the result product — over computed word cells. -/
def populateFE (a : Vector (Witgen.FExpr (ZMod p)) 4) :
    Circuits.Types.IsZeroWordOperation (Witgen.FExpr (ZMod p)) :=
  let l0 := IsZeroOperation.populateFE a[0]
  let l1 := IsZeroOperation.populateFE a[1]
  let l2 := IsZeroOperation.populateFE a[2]
  let l3 := IsZeroOperation.populateFE a[3]
  let fh := l0.result * l1.result
  let sh := l2.result * l3.result
  ⟨l0, l1, l2, l3, fh, sh, fh * sh⟩

/-- Evaluating the twin is `populate` on the evaluated word. -/
theorem populateFE_eval (env : ProverEnvironment (ZMod p))
    (a : Vector (Witgen.FExpr (ZMod p)) 4) (va : Word (ZMod p))
    (hA : ∀ (i : ℕ) (_ : i < 4), Witgen.FExpr.eval { env := env } a[i] = va[i]) :
    Witgen.eval { env := env } (populateFE a) = populate va := by
  have h0 := hA 0 (by omega); have h1 := hA 1 (by omega)
  have h2 := hA 2 (by omega); have h3 := hA 3 (by omega)
  by_cases hv0 : va[0] = 0 <;> by_cases hv1 : va[1] = 0 <;>
    by_cases hv2 : va[2] = 0 <;> by_cases hv3 : va[3] = 0 <;>
    simp [populateFE, populate, IsZeroOperation.populateFE, IsZeroOperation.populate,
      circuit_norm, explicit_provable_type, h0, h1, h2, h3, hv0, hv1, hv2, hv3,
      Witgen.StructEval.eval.go, ProvableStruct.toComponents, ProvableStruct.fromComponents]

/-- Environment-locality of the twin. -/
theorem populateFE_congr (env env' : ProverEnvironment (ZMod p))
    (a : Vector (Witgen.FExpr (ZMod p)) 4)
    (hA : ∀ (i : ℕ) (_ : i < 4),
      Witgen.FExpr.eval { env := env } a[i] = Witgen.FExpr.eval { env := env' } a[i]) :
    Witgen.eval { env := env } (populateFE a) = Witgen.eval { env := env' } (populateFE a) := by
  simp [populateFE, IsZeroOperation.populateFE, circuit_norm, explicit_provable_type,
    hA 0 (by omega), hA 1 (by omega), hA 2 (by omega), hA 3 (by omega),
    Witgen.StructEval.eval.go, ProvableStruct.toComponents, ProvableStruct.fromComponents]

end FE

/-- Flatten the typed columns using Clean's public structure decomposition. -/
private lemma toElements_columns {F : Type} (s : Circuits.Types.IsZeroWordOperation F) :
    toElements s = #v[s.is_zero_limb_0.inverse, s.is_zero_limb_0.result,
      s.is_zero_limb_1.inverse, s.is_zero_limb_1.result,
      s.is_zero_limb_2.inverse, s.is_zero_limb_2.result,
      s.is_zero_limb_3.inverse, s.is_zero_limb_3.result,
      s.is_zero_first_half, s.is_zero_second_half, s.result] := by
  apply Vector.ext
  intro i hi
  have hi' : i < 11 := hi
  obtain ⟨⟨i0, r0⟩, ⟨i1, r1⟩, ⟨i2, r2⟩, ⟨i3, r3⟩, fh, sh, r⟩ := s
  interval_cases i <;>
    simp only [circuit_norm, explicit_provable_type, ProvableStruct.toComponents,
      ProvableStruct.componentsToElements]
  all_goals
    repeat' first
    | exact Vector.getElem_append_left (by decide)
    | refine (Vector.getElem_append_right (by decide) (by decide)).trans ?_

/-- The result occupies the final flattened cell. -/
lemma result_eq_toElements {F : Type} (s : Circuits.Types.IsZeroWordOperation F) :
    s.result = (toElements s)[10]'(by
      have h : size Circuits.Types.IsZeroWordOperation = 11 := rfl
      omega) := by
  rw [toElements_columns]
  rfl

/-- Every flattened cell of the inactive witness is zero. -/
lemma zc_cell (i : ℕ) (hi : i < size Circuits.Types.IsZeroWordOperation) :
    (toElements (zeroCols : Circuits.Types.IsZeroWordOperation (ZMod p)))[i] = 0 := by
  have flattened : toElements (zeroCols : Circuits.Types.IsZeroWordOperation (ZMod p)) =
      Vector.replicate (size Circuits.Types.IsZeroWordOperation) 0 := by
    rw [toElements_columns]
    rfl
  rw [flattened, Vector.getElem_replicate]

/-- Decoding zero cells gives the typed inactive witness. -/
lemma fromElements_zero :
    (fromElements (Vector.replicate (size Circuits.Types.IsZeroWordOperation) 0)
      : Circuits.Types.IsZeroWordOperation (ZMod p)) = zeroCols := by
  rw [ProvableType.ext_iff]
  intro i hi
  rw [ProvableType.toElements_fromElements, Vector.getElem_replicate]
  exact (zc_cell i hi).symm

/-- Literal meaning of SP1's `IsZeroWordOperation` constraint list at `is_real = 1`: the four
per-limb `IsZeroOperation.AssertSpec`s, `result` boolean, and the half-product gluing equalities. -/
def AssertSpec (a : Word (ZMod p)) (cols : Circuits.Types.IsZeroWordOperation (ZMod p)) : Prop :=
  IsZeroOperation.AssertSpec a[0] cols.is_zero_limb_0 ∧
  IsZeroOperation.AssertSpec a[1] cols.is_zero_limb_1 ∧
  IsZeroOperation.AssertSpec a[2] cols.is_zero_limb_2 ∧
  IsZeroOperation.AssertSpec a[3] cols.is_zero_limb_3 ∧
  (cols.result = 0 ∨ cols.result = 1) ∧
  (cols.is_zero_first_half - cols.is_zero_limb_0.result * cols.is_zero_limb_1.result = 0) ∧
  (cols.is_zero_second_half - cols.is_zero_limb_2.result * cols.is_zero_limb_3.result = 0) ∧
  (cols.result - cols.is_zero_first_half * cols.is_zero_second_half = 0)

/-- Soundness core: the per-limb `IsZeroOperation.AssertSpec`s + AND-tree gluing force the word
zero-indicator. -/
theorem isZeroWord_of_assert {a : Word (ZMod p)} {cols : Circuits.Types.IsZeroWordOperation (ZMod p)}
    (h_raw : AssertSpec a cols) :
    cols.result = if (a[0] = 0 ∧ a[1] = 0 ∧ a[2] = 0 ∧ a[3] = 0) then 1 else 0 := by
  obtain ⟨r0, r1, r2, r3, _, hf, hs, hr⟩ := h_raw
  exact result_collapse (IsZeroOperation.isZero_of_assert r0) (IsZeroOperation.isZero_of_assert r1)
    (IsZeroOperation.isZero_of_assert r2) (IsZeroOperation.isZero_of_assert r3)
    (eq_of_sub_eq_zero hf) (eq_of_sub_eq_zero hs) (eq_of_sub_eq_zero hr)

/-- Compose the zero-test assertions and enforce the activity/result gates. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let a := input.a
  let cols := input.cols
  let is_real := input.is_real
  assertion IsZeroOperation.circuit ⟨a[0], cols.is_zero_limb_0, is_real⟩
  assertion IsZeroOperation.circuit ⟨a[1], cols.is_zero_limb_1, is_real⟩
  assertion IsZeroOperation.circuit ⟨a[2], cols.is_zero_limb_2, is_real⟩
  assertion IsZeroOperation.circuit ⟨a[3], cols.is_zero_limb_3, is_real⟩
  is_real * (is_real - 1) === 0
  cols.result * (cols.result - 1) === 0
  cols.is_zero_first_half - cols.is_zero_limb_0.result * cols.is_zero_limb_1.result === 0
  cols.is_zero_second_half - cols.is_zero_limb_2.result * cols.is_zero_limb_3.result === 0
  is_real * (cols.result - cols.is_zero_first_half * cols.is_zero_second_half) === 0

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main := by
  elaborate_circuit_with {
    channelsWithGuarantees := []
  }

@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [] := rfl
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

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

@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl


end SP1Clean.IsZeroWordOperation
