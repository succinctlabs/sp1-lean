import SP1Clean.Native.Operations.DivRemOperation.Compare
import SP1Clean.FormalModel.Contracts.DivRem
import SP1Clean.Proofs.CircuitProofStart

/-! # `DivRemCompare` — the `FormalAssertion` bundle (soundness / completeness / contract)

The DivRem comparison/sign assertion cluster as a Clean `FormalAssertion` over its explicit
committed-row view. The circuit (`Native/Operations/DivRemOperation/Compare.lean`)
witnesses nothing, so both directions are pure repackaging at the input level: soundness maps each
composed `assertion`'s `Assumptions → Spec` implication to the matching `CompareSpec` conjunct, and
completeness feeds each subcircuit its `Assumptions ∧ Spec` prover obligation from
`Assumptions`/`CompareSpec`. The external assumptions provide the independently available gate
facts and operand ranges. For the remainder comparison they provide only the generated gate
equation: this bundle first proves the `IsZero` result boolean, then derives the comparison
multiplicity's booleanness internally.

Both directions used to carry a 4000000-heartbeat ceiling. Measured 2026-07-28 (control at one
heartbeat, then a distinct-rung pass): `completeness` cleared 39999 as found; `soundness` failed at
40000 inside `hbin_rcm`'s `simp_all` and clears it once that closer is narrowed to a targeted
`rw`/`simp`. Both ceilings were therefore removed — the plain default carries ≥5× headroom. -/

namespace SP1Clean.DivRemCompare

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Composer-supplied preconditions: the independent gates are binary (`is_real`,
`is_real_not_word`, the word-variant sum `e2`, and the two negation-event flags), the
`AddOperation`/`LtOperationUnsigned` operand words are `isU64` on their gates, and the seven
`U16MSBOperation` operand limbs are 16-bit on theirs. This is the de-duplicated union of the
composed sub-operations' preconditions, except that the remainder-check multiplicity is derived
inside the bundle from `RemainderCheckGateSpec` and the `IsZeroWordOperation` result. -/
def Assumptions (cols : Inputs (ZMod p)) : Prop :=
  let bpv := cols.op_b_prev_value
  let cpv := cols.op_c_prev_value
  let irnw := cols.is_real_not_word
  let e2 := cols.is_divw + cols.is_remw + cols.is_divuw + cols.is_remuw
  (cols.is_real = 0 ∨ cols.is_real = 1) ∧
  (irnw = 0 ∨ irnw = 1) ∧
  (e2 = 0 ∨ e2 = 1) ∧
  (cols.abs_c_alu_event = 0 ∨ cols.abs_c_alu_event = 1) ∧
  (cols.abs_rem_alu_event = 0 ∨ cols.abs_rem_alu_event = 1) ∧
  RemainderCheckGateSpec cols ∧
  (cols.abs_c_alu_event = 1 → Word.isU64 cols.c ∧ Word.isU64 cols.abs_c) ∧
  (cols.abs_rem_alu_event = 1 → Word.isU64 cols.remainder_comp ∧ Word.isU64 cols.abs_remainder) ∧
  (cols.remainder_check_multiplicity = 1 →
    Word.isU64 cols.abs_remainder ∧ Word.isU64 cols.max_abs_c_or_1) ∧
  (irnw = 1 → bpv[3].val < 2 ^ 16 ∧ cpv[3].val < 2 ^ 16 ∧ cols.remainder[3].val < 2 ^ 16) ∧
  (e2 = 1 → bpv[1].val < 2 ^ 16 ∧ cpv[1].val < 2 ^ 16 ∧ cols.remainder[1].val < 2 ^ 16 ∧
    cols.quotient[1].val < 2 ^ 16)

omit [Fact (2 ^ 17 < p)] in
/-- Element-level reading of a whole-vector `h_input` eval equation: the assertion arguments read
`bpv/cpv/remainder/quotient` through `getElem`, which the vector-shaped `h_input` rules miss. -/
private lemma eval_getElem {n : ℕ} {env : Environment (ZMod p)}
    {vs : Vector (Expression (ZMod p)) n} {ws : Vector (ZMod p) n}
    (h : Vector.map (Expression.eval env) vs = ws) (i : ℕ) (_ : i < n) :
    Expression.eval env vs[i] = ws[i] := by
  rw [← h]; simp only [Vector.getElem_map]

theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions CompareSpec := by
  circuit_proof_start [CompareSpec]
  obtain ⟨hbin_ir, hbin_irnw, hbin_e2, hbin_ace, hbin_are, hrcmGate,
    hU_ac, hU_ar, hU_lt, hR3, hR1⟩ := h_assumptions
  have hb := eval_getElem h_input.1
  have hc := eval_getElem h_input.2.1
  have hr := eval_getElem h_input.2.2.2.2.2.1
  have hq := eval_getElem h_input.2.2.2.1
  simp only [hb, hc, hr, hq] at h_holds
  obtain ⟨hovb_full, hovc_full, hovb_low, hovc_low, hisc0, hadd_c, hadd_r, hlt,
    hmsb_b3, hmsb_c3, hmsb_r3, hmsb_b1, hmsb_c1, hmsb_r1, hmsb_q1⟩ := h_holds
  have hisc0Spec := hisc0 hbin_ir
  have hzbin : input_is_c_0_result = 0 ∨ input_is_c_0_result = 1 := by
    simpa only using hisc0Spec.1
  have hbin_rcm : input_remainder_check_multiplicity = 0 ∨
      input_remainder_check_multiplicity = 1 := by
    simp only [RemainderCheckGateSpec] at hrcmGate
    rcases hzbin with hz | hz <;> rcases hbin_ir with hv | hv <;>
      rw [hrcmGate, hz, hv] <;> simp
  refine ⟨⟨hovb_full hbin_irnw, hovc_full hbin_irnw, hovb_low hbin_e2, hovc_low hbin_e2,
    hisc0Spec,
    hadd_c ⟨hU_ac, hbin_ace⟩, hadd_r ⟨hU_ar, hbin_are⟩, hlt ⟨hU_lt, hbin_rcm⟩,
    hmsb_b3 ⟨fun h => (hR3 h).1, hbin_irnw⟩, hmsb_c3 ⟨fun h => (hR3 h).2.1, hbin_irnw⟩,
    hmsb_r3 ⟨fun h => (hR3 h).2.2, hbin_irnw⟩,
    hmsb_b1 ⟨fun h => (hR1 h).1, hbin_e2⟩, hmsb_c1 ⟨fun h => (hR1 h).2.1, hbin_e2⟩,
    hmsb_r1 ⟨fun h => (hR1 h).2.2.1, hbin_e2⟩, hmsb_q1 ⟨fun h => (hR1 h).2.2.2, hbin_e2⟩⟩, ?_⟩
  and_intros <;> exact Or.inl rfl

theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions CompareSpec := by
  circuit_proof_start [CompareSpec]
  obtain ⟨hbin_ir, hbin_irnw, hbin_e2, hbin_ace, hbin_are, hrcmGate,
    hU_ac, hU_ar, hU_lt, hR3, hR1⟩ := h_assumptions
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15⟩ :=
    h_spec
  have hb := eval_getElem h_input.1
  have hc := eval_getElem h_input.2.1
  have hr := eval_getElem h_input.2.2.2.2.2.1
  have hq := eval_getElem h_input.2.2.2.1
  simp only [hb, hc, hr, hq]
  have hzbin : input_is_c_0_result = 0 ∨ input_is_c_0_result = 1 := by
    simpa only using hs5.1
  have hbin_rcm : input_remainder_check_multiplicity = 0 ∨
      input_remainder_check_multiplicity = 1 := by
    simp only [RemainderCheckGateSpec] at hrcmGate
    rcases hzbin with hz | hz <;> rcases hbin_ir with hv | hv <;>
      rw [hrcmGate, hz, hv] <;> simp
  exact ⟨⟨hbin_irnw, hs1⟩, ⟨hbin_irnw, hs2⟩, ⟨hbin_e2, hs3⟩, ⟨hbin_e2, hs4⟩, ⟨hbin_ir, hs5⟩,
    ⟨⟨hU_ac, hbin_ace⟩, hs6⟩, ⟨⟨hU_ar, hbin_are⟩, hs7⟩, ⟨⟨hU_lt, hbin_rcm⟩, hs8⟩,
    ⟨⟨fun h => (hR3 h).1, hbin_irnw⟩, hs9⟩, ⟨⟨fun h => (hR3 h).2.1, hbin_irnw⟩, hs10⟩,
    ⟨⟨fun h => (hR3 h).2.2, hbin_irnw⟩, hs11⟩,
    ⟨⟨fun h => (hR1 h).1, hbin_e2⟩, hs12⟩, ⟨⟨fun h => (hR1 h).2.1, hbin_e2⟩, hs13⟩,
    ⟨⟨fun h => (hR1 h).2.2.1, hbin_e2⟩, hs14⟩, ⟨⟨fun h => (hR1 h).2.2.2, hbin_e2⟩, hs15⟩⟩

/-- The DivRem comparison/sign assertion cluster as a Clean-native `FormalAssertion`: fifteen
composed sub-operation assertions over the committed row, no fresh witnesses, semantic contract
`DivRemCompare.CompareSpec`. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := CompareSpec,
    soundness := soundness,
    completeness := completeness,
    channelsWithRequirements := [] }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithRequirements_eq :
    (circuit (p := p)).channelsWithRequirements = [] := rfl

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.DivRemCompare
