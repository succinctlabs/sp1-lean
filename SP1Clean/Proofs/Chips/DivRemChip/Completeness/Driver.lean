import SP1Clean.Proofs.Chips.DivRemChip.Defs
import SP1Clean.Proofs.Chips.DivRemChip.Populate.Bounds
import SP1Clean.Proofs.Chips.DivRemChip.Populate.Glue
import SP1Clean.Proofs.Chips.DivRemChip.Populate.Shapes
import SP1Clean.Proofs.Chips.DivRemChip.Populate.Euclid
import SP1Clean.Proofs.Chips.DivRemChip.Soundness
import SP1Clean.Proofs.Chips.DivRemChip.Assembly
import SP1Clean.Proofs.Chips.DivRemChip.Completeness.OwnComplete
import SP1Clean.Proofs.Chips.DivRemChip.Completeness.CompareComplete
import SP1Clean.Proofs.Chips.DivRemChip.Completeness.CoreComplete
import SP1Clean.Math.EvalVec
import SP1Clean.Proofs.Chips.DivRemChip.Completeness.BytePulls
import SP1Clean.Proofs.Chips.DivRemChip.Completeness.SubSpecs

/-! # `DivRemChip` — completeness driver (relocated from `Formal.lean`)

The `completeness` proof: `main`'s honest `Populate` witness closures (flags from the
`"div_rem_flags"` hint) satisfy every constraint under `ProverAssumptions`. Relocated here (as
`completeness`, reused by `Formal.circuit`) so `Formal.lean` stays a thin contract file; the
preamble runs after `circuit_proof_start` (where the witness-agreement `h_env` is cheap), then a
five-case `refine` discharges the folded CPU/RType/Compare/Core/RegisterWrite boundaries, each
delegating to a `CompareComplete` / `CoreComplete` / `SubSpecs` helper.

**The 13 `IsEqualWord`/`IsZero` cols pins** (`eqb/eqc/eqb2/eqc2/isc0`) each need
`(toElements cols)[i] = env.get (off+i)` for the witnessed sub-op cols. The wall used to be that
`circuit_proof_start`'s goal simp **decomposes** the *nested* `IsEqualWord`/`IsZeroWord` cols
(`is_diff_zero → 4× is_zero_limb → {inverse, result}`) into a deeply-nested record whose `toElements`
is intractable (a `circuit_norm` fixed point that can't be re-folded). The fix: the chip is the only
caller that passes these cols as an explicit `fromElements w` (Mul uses a `witness` result; Add/Lt/
U16MSB use struct literals), so bumping `ProvableType.eval_fromElements` to top `circuit_norm` priority
(below) intercepts `eval (fromElements w)` and rewrites it to the **flat** `fromElements (w.map env)`
*before* `eval_eq_eval` (`@[circuit_norm ↓ high]`) can decompose it — selectively, touching only these
five cols. Each pin then closes by `simp only [toElements_fromElements, getElem_map/mapRange,
circuit_norm]`. No struct flattening, no brute force, no faithfulness impact. -/

namespace SP1Clean.DivRemChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

-- `2 ^ 24` (subsuming `2 ^ 17`): the chip composes `MulOperation` — see `Defs`.
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]


-- Keep the IsEqualWord/IsZeroWord sub-op cols (the only ones `main` passes as explicit `fromElements`)
-- FOLDED through `circuit_proof_start`'s goal simp: `eval_fromElements` rewrites `eval (fromElements w)`
-- → `fromElements (w.map env)` (flat) BEFORE `eval_eq_eval` (`@[circuit_norm ↓ high]`) decomposes it into
-- the intractable nested record. Selective: Mul uses a `witness` result, Add/Lt/U16MSB use struct literals,
-- so none of them match `fromElements`. Lets the 13 `eqb/eqc/eqb2/eqc2/isc0` cols pins close fast.
attribute [local circuit_norm ↓ 100000] ProvableType.eval_fromElements


/-- Completeness: `main`'s honest `Populate` witness closures (flags from the `"div_rem_flags"`
hint) satisfy every constraint under `ProverAssumptions`. -/
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start_core
  let inputExpr := input_var
  rw [show main input_var = populateRow input_var >>= constrainRow input_var from rfl,
    Circuit.ConstraintsHold.bind_usesLocalWitnesses] at h_env
  replace h_env := h_env.1
  refine ⟨?_, trivial⟩
  simp +instances only [circuit_norm] at h_input
  provable_struct_simp
  dsimp only [ProverAssumptions] at h_assumptions
  have hbU := h_assumptions.1
  have hcU := h_assumptions.2.1
  have ha_prev := h_assumptions.2.2.1
  have hbin := h_assumptions.2.2.2.1
  have hf0 := h_assumptions.2.2.2.2.1
  have hf1 := h_assumptions.2.2.2.2.2.1
  have hf2 := h_assumptions.2.2.2.2.2.2.1
  have hf3 := h_assumptions.2.2.2.2.2.2.2.1
  have hf4 := h_assumptions.2.2.2.2.2.2.2.2.1
  have hf5 := h_assumptions.2.2.2.2.2.2.2.2.2.1
  have hf6 := h_assumptions.2.2.2.2.2.2.2.2.2.2.1
  have hf7 := h_assumptions.2.2.2.2.2.2.2.2.2.2.2.1
  have hsum := h_assumptions.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hpad := h_assumptions.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hop_a_0 := h_assumptions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h_cpu := h_assumptions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hrac_a := h_assumptions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hrac_b := h_assumptions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hrac_c := h_assumptions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hdec := h_assumptions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hprevclk := h_assumptions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear h_assumptions
  have h_env_flags := h_env.1
  have h_env_qc := h_env.2.1
  have h_env_a := h_env.2.2.1
  have h_env_b := h_env.2.2.2.1
  have h_env_c := h_env.2.2.2.2.1
  have h_env_mullo := h_env.2.2.2.2.2.1
  have h_env_mulhi := h_env.2.2.2.2.2.2.1
  have h_env_scal := h_env.2.2.2.2.2.2.2.1
  have h_env_ctq := h_env.2.2.2.2.2.2.2.2.1
  have h_env_carry := h_env.2.2.2.2.2.2.2.2.2.1
  have h_env_ovb := h_env.2.2.2.2.2.2.2.2.2.2.1
  have h_env_ovc := h_env.2.2.2.2.2.2.2.2.2.2.2.1
  have h_env_isc0 := h_env.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h_env_absc := h_env.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h_env_absr := h_env.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h_env_rc := h_env.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h_env_max := h_env.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h_env_wcneg := h_env.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h_env_wrneg := h_env.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h_env_misc := h_env.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h_env_cl := h_env.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h_env_f := h_env.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h_env_nei := h_env.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h_env_bit := h_env.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h_env_rem := h_env.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h_env_quot := h_env.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h_env_bmsb := h_env.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h_env_cmsb := h_env.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h_env_remmsb := h_env.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h_env_quotmsb :=
    h_env.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear h_env
  simp only [Witgen.WitgenIR.eval_native_apply] at h_env_flags h_env_qc h_env_a h_env_b h_env_c
  simp only [Witgen.WitgenIR.eval_native_apply] at h_env_mullo h_env_mulhi h_env_scal h_env_ctq h_env_carry
  simp only [Witgen.WitgenIR.eval_native_apply] at h_env_ovb h_env_ovc h_env_isc0 h_env_absc h_env_absr
  simp only [Witgen.WitgenIR.eval_native_apply] at h_env_rc h_env_max h_env_wcneg h_env_wrneg h_env_misc
  simp only [Witgen.WitgenIR.eval_native_apply] at h_env_cl h_env_f h_env_nei h_env_bit h_env_rem h_env_quot
  simp only [Witgen.WitgenIR.eval_native_apply] at h_env_bmsb h_env_cmsb h_env_remmsb h_env_quotmsb
  -- project (not destructure — `rcases` on `h_input` disturbs the bound `h_env_*` hypotheses)
  have hpc : Vector.map (Expression.eval env.toEnvironment) input_var_state_pc = input_state_pc := by
    rw [← CircuitType.eval_var_fields]
    exact h_input.2.1.2.2.2
  have hbpv : Vector.map (Expression.eval env.toEnvironment)
      input_var_adapter_op_b_memory_prev_value = input_adapter_op_b_memory_prev_value := by
    rw [← CircuitType.eval_var_fields]
    exact h_input.2.2.2.2.2.2.1.1
  have hapv : Vector.map (Expression.eval env.toEnvironment)
      input_var_adapter_op_a_memory_prev_value = input_adapter_op_a_memory_prev_value := by
    rw [← CircuitType.eval_var_fields]
    exact h_input.2.2.2.1.1
  have hcpv : Vector.map (Expression.eval env.toEnvironment)
      input_var_adapter_op_c_memory_prev_value = input_adapter_op_c_memory_prev_value := by
    rw [← CircuitType.eval_var_fields]
    exact h_input.2.2.2.2.2.2.2.2.1
  have hir : Expression.eval env.toEnvironment input_var_is_real = input_is_real := h_input.1
  haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  -- reduce the reducible operand projections, then abbreviate the operands and flags
  simp only [Inputs.op_b_val, Inputs.op_c_val] at hbU hcU
  set B := input_adapter_op_b_memory_prev_value with hBdef
  set C := input_adapter_op_c_memory_prev_value with hCdef
  -- `set F := hintFlags env.hint` `kabstract`s the 30× `hintFlags env.hint` occurrences buried in the
  -- heavy `h_env_*` pins (it is 0× in the goal) and stalls for minutes. `F` is consumed only via defeq
  -- (the pins close by `exact`/`simpa`), so introduce it as a defeq `let` and abstract it just in the
  -- small flag hypotheses the `rw`-based `have`s actually need.
  let F := hintFlags env.hint
  have hFdef : F = hintFlags env.hint := rfl
  have hFlags : hintFlags env.hint = F := hFdef.symm
  rw [← hFdef] at hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum
  -- per-element eval facts for input vectors
  have epc0 : Expression.eval env.toEnvironment input_var_state_pc[0] = input_state_pc[0] := by
    rw [← hpc, Vector.getElem_map]
  have epc1 : Expression.eval env.toEnvironment input_var_state_pc[1] = input_state_pc[1] := by
    rw [← hpc, Vector.getElem_map]
  have epc2 : Expression.eval env.toEnvironment input_var_state_pc[2] = input_state_pc[2] := by
    rw [← hpc, Vector.getElem_map]
  have hz : ∀ w : ZMod p, input_adapter_op_a_0 * w = 0 := fun w => by rw [hop_a_0, zero_mul]
  -- one-hot machinery
  have he2sum := (flagSums_bool hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum).1
  -- the padding template
  have hpadvals : input_is_real = 0 →
      B = #v[0, 0, 0, 0] ∧ C = #v[1, 0, 0, 0] ∧ F = #v[0, 1, 0, 0, 0, 0, 0, 0] := by
    intro h0
    obtain ⟨hb', hc', hf'⟩ := hpad h0
    simp only [Inputs.op_b_val, Inputs.op_c_val] at hb' hc'
    exact ⟨hb', hc', hFdef.trans hf'⟩
  -- flag pins
  have hfl0 : env.get i₀ = F[0] := by simpa using h_env_flags 0
  have hfl1 : env.get (i₀ + 1) = F[1] := by simpa using h_env_flags 1
  have hfl2 : env.get (i₀ + 2) = F[2] := by simpa using h_env_flags 2
  have hfl3 : env.get (i₀ + 3) = F[3] := by simpa using h_env_flags 3
  have hfl4 : env.get (i₀ + 4) = F[4] := by simpa using h_env_flags 4
  have hfl5 : env.get (i₀ + 5) = F[5] := by simpa using h_env_flags 5
  have hfl6 : env.get (i₀ + 6) = F[6] := by simpa using h_env_flags 6
  have hfl7 : env.get (i₀ + 7) = F[7] := by simpa using h_env_flags 7
  -- scalar witness pins (each `env.get` atom in goal form = its populate value)
  have hSC4 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 4)
      = input_is_real * (1 - (F[4] + F[5] + F[6] + F[7])) := by
    have h := h_env_scal 4
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hir, hFlags] at h
    simpa [populateScal_4] using h
  -- `rem_neg` scalar pin (scal slot 5) for the high-half chain rows
  have hREMNEG : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 5) = populateRemNeg B C F := by
    have h := h_env_scal 5
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hir, hFlags] at h
    simpa [populateScal_5] using h
  have hMISC0 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
        + 4 + 4 + 4 + 4 + 4 + 4)
      = populateCNeg C F * input_is_real := by
    have h := h_env_misc 0
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hir, hFlags] at h
    simpa [populateMisc_0] using h
  have hMISC1 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
        + 4 + 4 + 4 + 4 + 4 + 4 + 1)
      = populateRemNeg B C F * input_is_real := by
    have h := h_env_misc 1
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hir, hFlags] at h
    simpa [populateMisc_1] using h
  have hMISC2 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
        + 4 + 4 + 4 + 4 + 4 + 4 + 2)
      = ltGate input_is_real C F := by
    have h := h_env_misc 2
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hir, hFlags] at h
    simpa [populateMisc_2] using h
  have hNEI : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
        + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4)
      = (ltNotEqInvWitness input_is_real B C F)[0] := by
    have h := h_env_nei 0
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hir, hFlags] at h; exact h
  have hBIT : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
        + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1)
      = (ltBitWitness input_is_real B C F)[0] := by
    have h := h_env_bit 0
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hir, hFlags] at h; exact h
  have hBM : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
        + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 4)
      = bMsbCell B F := by
    have h := h_env_bmsb
    simp only [circuit_norm, vec4_eval, hbpv, hFlags] at h; exact h
  have hCM : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
        + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 4 + 1)
      = cMsbCell C F := by
    have h := h_env_cmsb
    simp only [circuit_norm, vec4_eval, hcpv, hFlags] at h; exact h
  have hRM : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
        + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 4 + 1 + 1)
      = remMsbCell B C F := by
    have h := h_env_remmsb
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h; exact h
  have hQM : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
        + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 4 + 1 + 1 + 1)
      = quotMsbCell B C F := by
    have h := h_env_quotmsb
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h; exact h
  -- vector pins: each witnessed operand vector (as it appears in the goal) = its populate word
  have hQCvec : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var { index := i₀ + 8 + i }) : Word (ZMod p))
      = populateQuotComp B C F := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    have h := h_env_qc ⟨i, hi⟩
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h; exact h
  have hCvec : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var { index := i₀ + 8 + 4 + 4 + 4 + i }) : Word (ZMod p))
      = cComp C F := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    have h := h_env_c ⟨i, hi⟩
    simp only [circuit_norm, vec4_eval, hcpv, hFlags] at h; exact h
  have hABSCvec : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i =>
          var { index := i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + i })
        : Word (ZMod p))
      = populateAbsC C F := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    have h := h_env_absc ⟨i, hi⟩
    simp only [circuit_norm, vec4_eval, hcpv, hFlags] at h; exact h
  have hABSRvec : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i =>
          var { index := i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 4 + i })
        : Word (ZMod p))
      = populateAbsRem B C F := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    have h := h_env_absr ⟨i, hi⟩
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h; exact h
  have hRCvec : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i =>
          var { index := i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
            + 4 + 4 + i }) : Word (ZMod p))
      = populateRemComp B C F := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    have h := h_env_rc ⟨i, hi⟩
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h; exact h
  have hMAXvec : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i =>
          var { index := i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
            + 4 + 4 + 4 + i }) : Word (ZMod p))
      = populateMaxAbsCOr1 C F := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    have h := h_env_max ⟨i, hi⟩
    simp only [circuit_norm, vec4_eval, hcpv, hFlags] at h; exact h
  have hWCNEGvec : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i =>
          var { index := i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
            + 4 + 4 + 4 + 4 + i }) : Word (ZMod p))
      = wCnegWitness input_is_real C F := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    have h := h_env_wcneg ⟨i, hi⟩
    simp only [circuit_norm, vec4_eval, hcpv, hir, hFlags] at h; exact h
  have hWRNEGvec : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i =>
          var { index := i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
            + 4 + 4 + 4 + 4 + 4 + i }) : Word (ZMod p))
      = wRnegWitness input_is_real B C F := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    have h := h_env_wrneg ⟨i, hi⟩
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hir, hFlags] at h; exact h
  have hLTCLvec : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 2 fun i =>
          var { index := i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
            + 4 + 4 + 4 + 4 + 4 + 4 + 3 + i }) : Vector (ZMod p) 2)
      = ltClWitness input_is_real B C F := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    have h := h_env_cl ⟨i, hi⟩
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hir, hFlags] at h; exact h
  have hLTFvec : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i =>
          var { index := i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
            + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + i }) : Vector (ZMod p) 4)
      = ltFlagsWitness input_is_real B C F := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    have h := h_env_f ⟨i, hi⟩
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hir, hFlags] at h; exact h
  -- the two Mul struct blocks, as quantified toElements pins + fromElements struct pins
  -- `hMULLO`/`hMULHI`: same nativeValue-blowup as the Bitwise `hc` bridge (`docs/agents/proof-patterns.md`)
  -- — `exact h` after folding needs the *expensive* `combinedSize'`-based isDefEq against
  -- `(toElements (populateMulLower/Upper …))[i]` for the 45-element `MulOperation` struct. Bridge via a
  -- definitional `have` ascribed at `h_env_mullo`'s own (unfolded) type, fold the operands via the cheap
  -- `rw`, then close through `getElem_toElements_eval_varFromOffset` (the CHEAP `env.get`-level identity)
  -- instead of the eager `exact`.
  have hMULLO : ∀ i : Fin 45, env.get (i₀ + 8 + 4 + 4 + 4 + 4 + ↑i)
      = (SubSpecs.mulWitnessElements (populateMulLower input_is_real B C F)).get i := by
    intro i
    have hc : env.toEnvironment.get (i₀ + 8 + 4 + 4 + 4 + 4 + ↑i)
        = (toElements (populateMulLower (Expression.eval env.toEnvironment input_var_is_real)
            (#v[Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[0],
                Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[1],
                Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[2],
                Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[3]])
            (#v[Expression.eval env.toEnvironment input_var_adapter_op_c_memory_prev_value[0],
                Expression.eval env.toEnvironment input_var_adapter_op_c_memory_prev_value[1],
                Expression.eval env.toEnvironment input_var_adapter_op_c_memory_prev_value[2],
                Expression.eval env.toEnvironment input_var_adapter_op_c_memory_prev_value[3]])
            (hintFlags env.hint)))[↑i] := h_env_mullo i
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hir, hFlags] at hc
    exact hc.trans
      (SubSpecs.mulWitnessElements_get (populateMulLower input_is_real B C F) i).symm
  have hMULHI : ∀ i : Fin 45, env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + ↑i)
      = (SubSpecs.mulWitnessElements (populateMulUpper input_is_real B C F)).get i := by
    intro i
    have hc : env.toEnvironment.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + ↑i)
        = (toElements (populateMulUpper (Expression.eval env.toEnvironment input_var_is_real)
            (#v[Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[0],
                Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[1],
                Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[2],
                Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[3]])
            (#v[Expression.eval env.toEnvironment input_var_adapter_op_c_memory_prev_value[0],
                Expression.eval env.toEnvironment input_var_adapter_op_c_memory_prev_value[1],
                Expression.eval env.toEnvironment input_var_adapter_op_c_memory_prev_value[2],
                Expression.eval env.toEnvironment input_var_adapter_op_c_memory_prev_value[3]])
            (hintFlags env.hint)))[↑i] := h_env_mulhi i
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hir, hFlags] at hc
    exact hc.trans
      (SubSpecs.mulWitnessElements_get (populateMulUpper input_is_real B C F) i).symm
  have hOVB : ∀ i : Fin 11, env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + ↑i)
      = (SubSpecs.eqWordWitnessElements (ovbWitness input_is_real B F)).get i := by
    intro i
    have h := h_env_ovb i
    simp only [circuit_norm, vec4_eval, hbpv, hir, hFlags] at h
    exact h.trans (SubSpecs.eqWordWitnessElements_get (ovbWitness input_is_real B F) i).symm
  have hOVC : ∀ i : Fin 11, env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + ↑i)
      = (SubSpecs.eqWordWitnessElements (ovcWitness input_is_real C F)).get i := by
    intro i
    have h := h_env_ovc i
    simp only [circuit_norm, vec4_eval, hcpv, hir, hFlags] at h
    exact h.trans (SubSpecs.eqWordWitnessElements_get (ovcWitness input_is_real C F) i).symm
  let isc0Witness : Extracted.IsZeroWordOperation (ZMod p) := isC0Witness C F
  have hISC0 : ∀ i : Fin 11,
      env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + ↑i) =
        (SubSpecs.isZeroWitnessElements (p := p) isc0Witness).get i := by
    intro i
    have h := h_env_isc0 i
    simp only [circuit_norm, vec4_eval, hcpv, hFlags] at h
    exact h.trans (SubSpecs.isZeroWitnessElements_get isc0Witness i).symm
  -- derived gate facts
  have hirnwbin : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 4) = 0
      ∨ env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 4) = 1 := by
    rw [hSC4]
    rcases hbin with h | h
    · left; rw [h, zero_mul]
    · rcases he2sum with h2 | h2
      · right; rw [h, h2]; ring
      · left; rw [h, h2]; ring
  -- folds for the own-asserts bundle (`CoreComplete.evaluatedPopulatedOwnAssertsComplete`): the five
  -- `scal` slots, the whole-vector operand/witness blocks, and the prev-value bridges that the cases
  -- above don't already build. All clone the `hSC4` / `hCvec` patterns.
  have hOV : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45) = populateIsOverflow input_is_real B C F := by
    have h := h_env_scal 0
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hir, hFlags] at h
    simpa [populateScal_0] using h
  have hBN : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 1) = populateBNeg B F := by
    have h := h_env_scal 1
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hir, hFlags] at h
    simpa [populateScal_1] using h
  have hBNNO : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 2)
      = populateBNeg B F * (1 - populateIsOverflow input_is_real B C F) := by
    have h := h_env_scal 2
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hir, hFlags] at h
    simpa [populateScal_2] using h
  have hBNNNO : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 3)
      = (1 - populateBNeg B F) * (1 - populateIsOverflow input_is_real B C F) := by
    have h := h_env_scal 3
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hir, hFlags] at h
    simpa [populateScal_3] using h
  have hCN : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 6) = populateCNeg C F := by
    have h := h_env_scal 6
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hir, hFlags] at h
    simpa [populateScal_6] using h
  have hBvec : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var { index := i₀ + 8 + 4 + 4 + i }) : Word (ZMod p))
      = bComp B F := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    have h := h_env_b ⟨i, hi⟩
    simp only [circuit_norm, vec4_eval, hbpv, hFlags] at h; exact h
  have hAvec : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var { index := i₀ + 8 + 4 + i }) : Word (ZMod p))
      = populateA B C F := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    have h := h_env_a ⟨i, hi⟩
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h; exact h
  have hQvec : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var { index :=
          i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2
            + 4 + 1 + 1 + 4 + i }) : Word (ZMod p))
      = populateQuotient B C F := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    have h := h_env_quot ⟨i, hi⟩
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h; exact h
  have hRvec : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var { index :=
          i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2
            + 4 + 1 + 1 + i }) : Word (ZMod p))
      = populateRemainder B C F := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    have h := h_env_rem ⟨i, hi⟩
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h; exact h
  have hCTQvecW : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 8 fun i => var { index := i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + i })
        : Vector (ZMod p) 8)
      = populateCtq B C F := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    have h := h_env_ctq ⟨i, hi⟩
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h; exact h
  have hCARRYvecW : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 8 fun i => var { index := i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + i })
        : Vector (ZMod p) 8)
      = populateCarry B C F := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    have h := h_env_carry ⟨i, hi⟩
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h; exact h
  -- a signed-class row is real (the divu-padding template `F = #v[0,1,0,…]` has signed sum `0`)
  have hsr : F[0] + F[2] + F[4] + F[5] = 1 → input_is_real = 1 := by
    intro hsig'
    rcases hbin with h | h
    · exfalso
      obtain ⟨-, -, hF⟩ := hpadvals h
      rw [hF] at hsig'
      norm_num at hsig'
    · exact h
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec h_cpu
  -- Split the witness-only prefix from the five folded proof boundaries in `constrainRow`.
  -- This is definitional factoring only: the flat operation order remains the Rust row order.
  simp only [main, ConstraintsHold.Completeness, Circuit.bind_forAllNoOffset]
  refine ⟨by
    simp only [populateRow, Circuit.bind_forAllNoOffset, witnessVectorNative,
      CircuitNormalization.witnessNative_apply_eq, Circuit.pure_def, Circuit.operations,
      Operations.forAllNoOffset, and_true], ?_⟩
  -- Expose the five folded constraint boundaries after the witness-only prefix.
  rw [populateRow_output_eq]
  simp only [constrainRow, Circuit.bind_forAllNoOffset,
    subcircuitWithAssertion, assertion, Circuit.pure_def, Circuit.operations,
    Operations.forAllNoOffset, GeneralFormalCircuit.toSubcircuit_completeness,
    FormalAssertion.toSubcircuit_completeness, and_true]
  refine ⟨?cpu, ?rtype, ?compare, ?core, ?regwrite⟩
  case cpu =>
    simp +instances only [circuit_norm, h_input]
    exact ⟨hbin, by rw [← epc0, ← epc1, ← epc2] at h_cpu; exact h_cpu⟩
  case rtype =>
    simp +instances only [Readers.RTypeReader.circuit, Readers.RTypeReader.ProverAssumptionsD,
      Readers.RTypeReader.Assumptions, Readers.RTypeReader.Spec, populatedRowAt, circuit_norm, h_input,
      epc0, epc1, epc2, hapv, hbpv, hcpv]
    exact ⟨⟨hbin, hbin, h_clk⟩, ⟨⟨hz _, hz _, hz _, hz _⟩, Or.inl hop_a_0, hrac_a, hrac_b,
      hrac_c, hdec, fun hr => ⟨ha_prev hr, hbU, hcU, (hprevclk hr).1, (hprevclk hr).2.1,
        (hprevclk hr).2.2⟩⟩⟩
  case compare =>
    have hCompareInputs := CompareComplete.evaluatedInputs_eq env inputExpr i₀
      input_is_real B C F hir hbpv hcpv hfl4 hfl5 hfl6 hfl7 hSC4 hCvec
      hABSCvec hABSRvec hRCvec hMAXvec hWCNEGvec hWRNEGvec hLTCLvec hLTFvec
      hNEI hBIT hRvec hQvec hBM hCM hRM hQM hMISC0 hMISC1 hMISC2 hOVB hOVC
      (by simpa only [isc0Witness] using hISC0)
    refine ⟨?_, ?_⟩
    · simp only [DivRemCompare.circuit]
      rw [hCompareInputs]
      exact CompareComplete.honestAssumptions input_is_real B C F hbU hcU hbin
        hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum
    · simp only [DivRemCompare.circuit]
      rw [hCompareInputs]
      exact CompareComplete.honestSpec input_is_real B C F hbU hcU hbin
        hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum hpadvals
  case core =>
    refine ⟨?_, ?_⟩
    · simp only [DivRemCore.circuit, DivRemCore.Assumptions]
    · simp only [DivRemCore.circuit, DivRemCore.CoreSpec]
      refine ⟨CoreComplete.evaluatedProductSpec env inputExpr i₀ input_is_real B C F
        hQCvec hCvec hCTQvecW hMULLO hMULHI hir hSC4 hfl0 hfl1 hfl2 hfl3 hcU hbin
        hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum hpadvals, ?_,
        ⟨CoreComplete.evaluatedSelectionEvidenceSpec env inputExpr i₀ input_is_real F
          hir hSC4 hfl0 hfl1 hfl2 hfl3 hfl4 hfl5 hfl6 hfl7 hbin
          (by rw [← hSC4]; exact hirnwbin) hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum,
        CoreComplete.evaluatedRangeSpec env inputExpr i₀ B C F hcU hCTQvecW
          hCARRYvecW hRCvec hABSCvec hABSRvec hQvec hRvec hREMNEG⟩⟩
      exact CoreComplete.evaluatedPopulatedOwnAssertsComplete env inputExpr i₀
        input_is_real B C F hbU hcU hbin hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum hsr
        hfl0 hfl1 hfl2 hfl3 hfl4 hfl5 hfl6 hfl7 hir
        hSC4 hOV hBN hBNNO hBNNNO hREMNEG hCN hMISC0 hMISC1 hMISC2
        hBM hCM hRM hQM
        hBvec hCvec hQvec hQCvec hRvec hRCvec hAvec hABSCvec hABSRvec hMAXvec
        hCTQvecW hCARRYvecW hWCNEGvec hWRNEGvec hbpv hcpv
        hOVB hOVC (by simpa only [isc0Witness] using hISC0)
        hBIT ((h_input.2.2.2.2.1).trans hop_a_0)
  case regwrite =>
    simp +instances only [Readers.RegisterWrite.circuit, Readers.RegisterWrite.Assumptions,
      Readers.RegisterWrite.Spec, populatedRowAt_a_eq, circuit_norm, h_input]
    exact ⟨hbin, fun _ => by rw [hAvec]; exact populateA_isU64 B C F, h_clk.at_four⟩

end SP1Clean.DivRemChip
