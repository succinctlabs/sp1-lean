module

public import SP1Clean.Semantics.Specs.IsEqualWord
public import SP1Clean.Circuits.Gadgets.IsZeroWord
import Mathlib.Tactic.IntervalCases
import Clean.Utils.Tactics.CircuitProofStart

/-! # Word equality gadget

The typed and Clean-IR witnesses, circuit and bundled correctness proofs share this module.
The pure contract is in `Semantics/Specs/IsEqualWord`. `AssertSpec` supports the
transitional comparison with independently extracted Rust assertions.
-/

@[expose] public section

namespace SP1Clean.IsEqualWordOperation

open Circuit

variable {p : ℕ} [Fact p.Prime]

/-- The witnessed column struct: `IsZeroWordOperation.populate` on the limb-wise difference `a - b`. -/
def populate (a b : Word (ZMod p)) : Circuits.Types.IsEqualWordOperation (ZMod p) :=
  ⟨IsZeroWordOperation.populate #v[a[0] - b[0], a[1] - b[1], a[2] - b[2], a[3] - b[3]]⟩

section FE

/-- The witness-IR twin of `populate`: `IsZeroWordOperation.populateFE` on the limb-wise
difference (the IR's derived `sub` sugar). -/
def populateFE (a b : Vector (Witgen.FExpr (ZMod p)) 4) :
    Circuits.Types.IsEqualWordOperation (Witgen.FExpr (ZMod p)) :=
  ⟨IsZeroWordOperation.populateFE #v[a[0] - b[0], a[1] - b[1], a[2] - b[2], a[3] - b[3]]⟩

/-- Evaluating the twin is `populate` on the evaluated words. -/
theorem populateFE_eval (env : ProverEnvironment (ZMod p))
    (a b : Vector (Witgen.FExpr (ZMod p)) 4) (va vb : Word (ZMod p))
    (hA : ∀ (i : ℕ) (_ : i < 4), Witgen.FExpr.eval { env := env } a[i] = va[i])
    (hB : ∀ (i : ℕ) (_ : i < 4), Witgen.FExpr.eval { env := env } b[i] = vb[i]) :
    Witgen.eval { env := env } (populateFE a b) = populate va vb := by
  have hdiff : ∀ (i : ℕ) (_ : i < 4), Witgen.FExpr.eval { env := env }
      (#v[a[0] - b[0], a[1] - b[1], a[2] - b[2], a[3] - b[3]] :
        Vector (Witgen.FExpr (ZMod p)) 4)[i]
      = (#v[va[0] - vb[0], va[1] - vb[1], va[2] - vb[2], va[3] - vb[3]] : Word (ZMod p))[i] := by
    intro i hi
    interval_cases i <;>
      (simp only [circuit_norm, Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ,
        hA 0 (by omega), hA 1 (by omega), hA 2 (by omega), hA 3 (by omega),
        hB 0 (by omega), hB 1 (by omega), hB 2 (by omega), hB 3 (by omega)]
       try ring)
  have h := IsZeroWordOperation.populateFE_eval env
    (#v[a[0] - b[0], a[1] - b[1], a[2] - b[2], a[3] - b[3]])
    (#v[va[0] - vb[0], va[1] - vb[1], va[2] - vb[2], va[3] - vb[3]]) hdiff
  rw [Witgen.StructEval.eval_eq_eval]
  show (⟨Witgen.eval { env := env }
      (IsZeroWordOperation.populateFE #v[a[0] - b[0], a[1] - b[1], a[2] - b[2], a[3] - b[3]])⟩ :
    Circuits.Types.IsEqualWordOperation (ZMod p)) = populate va vb
  rw [h]
  rfl

/-- Environment-locality of the twin. -/
theorem populateFE_congr (env env' : ProverEnvironment (ZMod p))
    (a b : Vector (Witgen.FExpr (ZMod p)) 4)
    (hA : ∀ (i : ℕ) (_ : i < 4),
      Witgen.FExpr.eval { env := env } a[i] = Witgen.FExpr.eval { env := env' } a[i])
    (hB : ∀ (i : ℕ) (_ : i < 4),
      Witgen.FExpr.eval { env := env } b[i] = Witgen.FExpr.eval { env := env' } b[i]) :
    Witgen.eval { env := env } (populateFE a b) = Witgen.eval { env := env' } (populateFE a b) := by
  have hdiff : ∀ (i : ℕ) (_ : i < 4), Witgen.FExpr.eval { env := env }
      (#v[a[0] - b[0], a[1] - b[1], a[2] - b[2], a[3] - b[3]] :
        Vector (Witgen.FExpr (ZMod p)) 4)[i]
      = Witgen.FExpr.eval { env := env' }
        (#v[a[0] - b[0], a[1] - b[1], a[2] - b[2], a[3] - b[3]] :
          Vector (Witgen.FExpr (ZMod p)) 4)[i] := by
    intro i hi
    interval_cases i <;>
      simp only [circuit_norm, -Witgen.u64Wrap, Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ,
        hA 0 (by omega), hA 1 (by omega), hA 2 (by omega), hA 3 (by omega),
        hB 0 (by omega), hB 1 (by omega), hB 2 (by omega), hB 3 (by omega)]
  have h := IsZeroWordOperation.populateFE_congr env env'
    (#v[a[0] - b[0], a[1] - b[1], a[2] - b[2], a[3] - b[3]]) hdiff
  rw [Witgen.StructEval.eval_eq_eval, Witgen.StructEval.eval_eq_eval]
  show (⟨Witgen.eval { env := env }
      (IsZeroWordOperation.populateFE #v[a[0] - b[0], a[1] - b[1], a[2] - b[2], a[3] - b[3]])⟩ :
    Circuits.Types.IsEqualWordOperation (ZMod p))
    = ⟨Witgen.eval { env := env' }
        (IsZeroWordOperation.populateFE #v[a[0] - b[0], a[1] - b[1], a[2] - b[2], a[3] - b[3]])⟩
  rw [h]

end FE

section Flatten

/-- The equality wrapper has the same cells as its nested zero-test columns. -/
lemma toElements_mk {F : Type} (s : Circuits.Types.IsZeroWordOperation F) :
    toElements (⟨s⟩ : Circuits.Types.IsEqualWordOperation F)
      = (toElements s).cast (by rfl) := by
  change ProvableStruct.structToElements (⟨s⟩ : Circuits.Types.IsEqualWordOperation F) = _
  rw [ProvableStruct.structToElements_eq]
  simp only [ProvableStruct.toComponents, components, ProvableStruct.componentsToElements]
  ext i hi
  simp only [Vector.getElem_cast]
  exact Vector.getElem_append_left _

/-- The nested result field is flattened cell `10` (for composing chips that read the
overflow-result cell of a struct payload). -/
lemma result_eq_toElements {F : Type} (s : Circuits.Types.IsEqualWordOperation F) :
    s.is_diff_zero.result = (toElements s)[10]'(by
      have h : size Circuits.Types.IsEqualWordOperation = 11 := rfl
      omega) := by
  obtain ⟨z⟩ := s
  rw [toElements_mk, Vector.getElem_cast]
  exact IsZeroWordOperation.result_eq_toElements z

/-- Every flattened cell of the zero struct is zero. -/
lemma zc_cell (i : ℕ) (hi : i < size Circuits.Types.IsEqualWordOperation) :
    (toElements (⟨IsZeroWordOperation.zeroCols⟩ :
        Circuits.Types.IsEqualWordOperation (ZMod p)))[i] = 0 := by
  rw [toElements_mk, Vector.getElem_cast, IsZeroWordOperation.zc_cell]

/-- The flattened zero struct, as a `fromElements` of zeros (the shape `Witgen.eval_gateFE`'s
else branch produces). -/
lemma fromElements_zero :
    (fromElements (Vector.replicate (size Circuits.Types.IsEqualWordOperation) 0)
      : Circuits.Types.IsEqualWordOperation (ZMod p)) = ⟨IsZeroWordOperation.zeroCols⟩ := by
  rw [ProvableType.ext_iff]
  intro i hi
  rw [ProvableType.toElements_fromElements, Vector.getElem_replicate]
  exact (zc_cell i hi).symm

end Flatten

/-- Literal meaning of SP1's `IsEqualWordOperation` constraint list at `is_real = 1`: the
`IsZeroWordOperation.AssertSpec` on the limb-wise difference `a - b`. -/
def AssertSpec (a b : Word (ZMod p)) (cols : Circuits.Types.IsEqualWordOperation (ZMod p)) : Prop :=
  IsZeroWordOperation.AssertSpec #v[a[0] - b[0], a[1] - b[1], a[2] - b[2], a[3] - b[3]]
    cols.is_diff_zero

/-- Soundness core: the `IsZeroWordOperation` zero-test on the limb-wise difference, plus
`aᵢ - bᵢ = 0 ↔ aᵢ = bᵢ`, gives the equality indicator. -/
theorem isEqualWord_of_assert {a b : Word (ZMod p)} {cols : Circuits.Types.IsEqualWordOperation (ZMod p)}
    (h_raw : AssertSpec a b cols) :
    cols.is_diff_zero.result =
      if (a[0] = b[0] ∧ a[1] = b[1] ∧ a[2] = b[2] ∧ a[3] = b[3]) then 1 else 0 := by
  simpa only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, sub_eq_zero] using IsZeroWordOperation.isZeroWord_of_assert h_raw

/-- Compose the zero-test assertions and enforce the activity/result gates. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let a := input.a
  let b := input.b
  let is_real := input.is_real
  assertion IsZeroWordOperation.circuit
    ⟨#v[a[0] - b[0], a[1] - b[1], a[2] - b[2], a[3] - b[3]], input.cols.is_diff_zero, is_real⟩
  is_real * (is_real - 1) === 0

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
  obtain ⟨hsub, _hbool⟩ := h_holds
  obtain ⟨hia, hib, -⟩ := h_input
  have S := hsub h_assumptions
  change IsZeroWordOperation.Spec _ at S
  refine ⟨?_, Or.inl rfl⟩
  simpa only [diff, ← hia, ← hib, Vector.getElem_map, sub_eq_add_neg] using S

theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hia, hib, -⟩ := h_input
  refine ⟨⟨h_assumptions, ?_⟩, ?_⟩
  · have hs := h_spec
    simp only [diff] at hs
    change IsZeroWordOperation.Spec _
    simpa only [← hia, ← hib, Vector.getElem_map] using hs
  · rcases h_assumptions with h | h <;> simp [h]

/-- The witnessed columns `populate a b` satisfy the gadget `Spec` for any `is_real` — it delegates to
`IsZeroWordOperation.spec_populate` on the difference word. -/
theorem spec_populate (a b : Word (ZMod p)) (is_real : ZMod p) :
    Spec (⟨a, b, populate a b, is_real⟩ : Inputs (ZMod p)) :=
  IsZeroWordOperation.spec_populate _ is_real

/-- `Spec` at the all-zero column struct with the gate off (`is_real = 0`) — the inactive-row
discharge for composing chips whose populate leaves the struct zero (`DivRemChip`'s
`is_overflow_b`/`is_overflow_c` on padding rows). The operands are arbitrary. -/
theorem spec_zero (a b : Word (ZMod p)) {is_real : ZMod p} (hr : is_real = 0) :
    Spec (⟨a, b, ⟨IsZeroWordOperation.zeroCols⟩, is_real⟩ : Inputs (ZMod p)) :=
  IsZeroWordOperation.spec_zero _ hr

/-- `Spec` with the gate off (`is_real = 0`) holds at the populate of **any** word pair — the
shared-struct discharge for a composing chip whose one witnessed struct serves two
differently-gated assertions with different operand words (`DivRemChip`'s `is_overflow_b/c`:
full-word @ `is_real_not_word` vs truncated @ the word-variant gate). -/
theorem spec_populate_offGate (a b w w' : Word (ZMod p)) {is_real : ZMod p} (hr : is_real = 0) :
    Spec (⟨a, b, populate w w', is_real⟩ : Inputs (ZMod p)) :=
  IsZeroWordOperation.spec_populate_offGate _ _ hr

/-- SP1's `IsEqualWordOperation::eval` as a Clean-native `FormalAssertion`. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl


end SP1Clean.IsEqualWordOperation
