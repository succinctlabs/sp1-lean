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
preamble runs after `circuit_proof_start` (where the witness-agreement `h_env` is cheap), then the
62-case `refine` discharges each constraint. Mul/glue/ctq/Add/Lt/U16MSB/`own`/byte-pull cases are all
real (the sub-circuit `Spec` cases delegate to the `SubSpecs.subSpec_*` helpers).

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
open Extracted (DivRemCols)
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
  obtain ⟨hbU0, hbU1, hbU2, hbU3⟩ := Word.lt_cases_of_isU64 hbU
  obtain ⟨hcU0, hcU1, hcU2, hcU3⟩ := Word.lt_cases_of_isU64 hcU
  -- per-element eval facts for input vectors
  have epc0 : Expression.eval env.toEnvironment input_var_state_pc[0] = input_state_pc[0] := by
    rw [← hpc, Vector.getElem_map]
  have epc1 : Expression.eval env.toEnvironment input_var_state_pc[1] = input_state_pc[1] := by
    rw [← hpc, Vector.getElem_map]
  have epc2 : Expression.eval env.toEnvironment input_var_state_pc[2] = input_state_pc[2] := by
    rw [← hpc, Vector.getElem_map]
  have heb0 : Expression.eval env.toEnvironment
      input_var_adapter_op_b_memory_prev_value[0] = B[0] := by
    rw [← hbpv, Vector.getElem_map]
  have heb1 : Expression.eval env.toEnvironment
      input_var_adapter_op_b_memory_prev_value[1] = B[1] := by
    rw [← hbpv, Vector.getElem_map]
  have heb3 : Expression.eval env.toEnvironment
      input_var_adapter_op_b_memory_prev_value[3] = B[3] := by
    rw [← hbpv, Vector.getElem_map]
  have hec0 : Expression.eval env.toEnvironment
      input_var_adapter_op_c_memory_prev_value[0] = C[0] := by
    rw [← hcpv, Vector.getElem_map]
  have hec1 : Expression.eval env.toEnvironment
      input_var_adapter_op_c_memory_prev_value[1] = C[1] := by
    rw [← hcpv, Vector.getElem_map]
  have hec3 : Expression.eval env.toEnvironment
      input_var_adapter_op_c_memory_prev_value[3] = C[3] := by
    rw [← hcpv, Vector.getElem_map]
  have hz : ∀ w : ZMod p, input_adapter_op_a_0 * w = 0 := fun w => by rw [hop_a_0, zero_mul]
  -- one-hot machinery
  have hsums := flagSums_bool hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum
  have he2sum := hsums.1
  have hsig := hsums.2.1
  have hg64 := hsums.2.2.1
  have hd_r := hsums.2.2.2.1
  have hdu_r := hsums.2.2.2.2
  clear hsums
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
  have hCTQ0 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7) = (populateCtq B C F)[0] := by
    have h := h_env_ctq 0
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hCTQ1 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 1) = (populateCtq B C F)[1] := by
    have h := h_env_ctq 1
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hCTQ2 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 2) = (populateCtq B C F)[2] := by
    have h := h_env_ctq 2
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hCTQ3 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 3) = (populateCtq B C F)[3] := by
    have h := h_env_ctq 3
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hCTQ4 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 4) = (populateCtq B C F)[4] := by
    have h := h_env_ctq 4
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hCTQ5 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 5) = (populateCtq B C F)[5] := by
    have h := h_env_ctq 5
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hCTQ6 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 6) = (populateCtq B C F)[6] := by
    have h := h_env_ctq 6
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hCTQ7 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 7) = (populateCtq B C F)[7] := by
    have h := h_env_ctq 7
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  -- carry-block element pins (for the `pe1xx` chain-residue cases)
  have hCARRY0 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8) = (populateCarry B C F)[0] := by
    have h := h_env_carry 0
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hCARRY1 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 1) = (populateCarry B C F)[1] := by
    have h := h_env_carry 1
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hCARRY2 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 2) = (populateCarry B C F)[2] := by
    have h := h_env_carry 2
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hCARRY3 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 3) = (populateCarry B C F)[3] := by
    have h := h_env_carry 3
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hCARRY4 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 4) = (populateCarry B C F)[4] := by
    have h := h_env_carry 4
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hCARRY5 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 5) = (populateCarry B C F)[5] := by
    have h := h_env_carry 5
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hCARRY6 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 6) = (populateCarry B C F)[6] := by
    have h := h_env_carry 6
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hCARRY7 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 7) = (populateCarry B C F)[7] := by
    have h := h_env_carry 7
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  -- `rem_neg` scalar pin (scal slot 5) for the high-half chain rows
  have hREMNEG : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 5) = populateRemNeg B C F := by
    have h := h_env_scal 5
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hir, hFlags] at h
    simpa [populateScal_5] using h
  -- `remainder_comp` element pins (for the low-half chain rows)
  have hRC0 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4)
      = (populateRemComp B C F)[0] := by
    have h := h_env_rc 0
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hRC1 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1)
      = (populateRemComp B C F)[1] := by
    have h := h_env_rc 1
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hRC2 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2)
      = (populateRemComp B C F)[2] := by
    have h := h_env_rc 2
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hRC3 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)
      = (populateRemComp B C F)[3] := by
    have h := h_env_rc 3
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hABSC0 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11)
      = (populateAbsC C F)[0] := by
    have h := h_env_absc 0
    simp only [circuit_norm, vec4_eval, hcpv, hFlags] at h
    exact h
  have hABSC1 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 1)
      = (populateAbsC C F)[1] := by
    have h := h_env_absc 1
    simp only [circuit_norm, vec4_eval, hcpv, hFlags] at h
    exact h
  have hABSC2 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 2)
      = (populateAbsC C F)[2] := by
    have h := h_env_absc 2
    simp only [circuit_norm, vec4_eval, hcpv, hFlags] at h
    exact h
  have hABSC3 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 3)
      = (populateAbsC C F)[3] := by
    have h := h_env_absc 3
    simp only [circuit_norm, vec4_eval, hcpv, hFlags] at h
    exact h
  have hABSR0 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 4)
      = (populateAbsRem B C F)[0] := by
    have h := h_env_absr 0
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hABSR1 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 1)
      = (populateAbsRem B C F)[1] := by
    have h := h_env_absr 1
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hABSR2 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 2)
      = (populateAbsRem B C F)[2] := by
    have h := h_env_absr 2
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hABSR3 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 3)
      = (populateAbsRem B C F)[3] := by
    have h := h_env_absr 3
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
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
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hir, hFlags] at h
    exact h
  have hBIT : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
        + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1)
      = (ltBitWitness input_is_real B C F)[0] := by
    have h := h_env_bit 0
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hir, hFlags] at h
    exact h
  have hREM0 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
        + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1)
      = (populateRemainder B C F)[0] := by
    have h := h_env_rem 0
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hREM1 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
        + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 1)
      = (populateRemainder B C F)[1] := by
    have h := h_env_rem 1
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hREM2 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
        + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 2)
      = (populateRemainder B C F)[2] := by
    have h := h_env_rem 2
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hREM3 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
        + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 3)
      = (populateRemainder B C F)[3] := by
    have h := h_env_rem 3
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hQUOT0 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
        + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4)
      = (populateQuotient B C F)[0] := by
    have h := h_env_quot 0
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hQUOT1 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
        + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 1)
      = (populateQuotient B C F)[1] := by
    have h := h_env_quot 1
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hQUOT2 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
        + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 2)
      = (populateQuotient B C F)[2] := by
    have h := h_env_quot 2
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hQUOT3 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
        + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 3)
      = (populateQuotient B C F)[3] := by
    have h := h_env_quot 3
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hBM : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
        + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 4)
      = bMsbCell B F := by
    have h := h_env_bmsb
    simp only [circuit_norm, vec4_eval, hbpv, hFlags] at h
    exact h
  have hCM : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
        + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 4 + 1)
      = cMsbCell C F := by
    have h := h_env_cmsb
    simp only [circuit_norm, vec4_eval, hcpv, hFlags] at h
    exact h
  have hRM : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
        + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 4 + 1 + 1)
      = remMsbCell B C F := by
    have h := h_env_remmsb
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hQM : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
        + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 4 + 1 + 1 + 1)
      = quotMsbCell B C F := by
    have h := h_env_quotmsb
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  -- vector pins: each witnessed operand vector (as it appears in the goal) = its populate word
  have hQCvec : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var { index := i₀ + 8 + i }) : Word (ZMod p))
      = populateQuotComp B C F := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    have h := h_env_qc ⟨i, hi⟩
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hCvec : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var { index := i₀ + 8 + 4 + 4 + 4 + i }) : Word (ZMod p))
      = cComp C F := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    have h := h_env_c ⟨i, hi⟩
    simp only [circuit_norm, vec4_eval, hcpv, hFlags] at h
    exact h
  have hABSCvec : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i =>
          var { index := i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + i })
        : Word (ZMod p))
      = populateAbsC C F := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    have h := h_env_absc ⟨i, hi⟩
    simp only [circuit_norm, vec4_eval, hcpv, hFlags] at h
    exact h
  have hABSRvec : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i =>
          var { index := i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 4 + i })
        : Word (ZMod p))
      = populateAbsRem B C F := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    have h := h_env_absr ⟨i, hi⟩
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hRCvec : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i =>
          var { index := i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
            + 4 + 4 + i }) : Word (ZMod p))
      = populateRemComp B C F := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    have h := h_env_rc ⟨i, hi⟩
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hMAXvec : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i =>
          var { index := i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
            + 4 + 4 + 4 + i }) : Word (ZMod p))
      = populateMaxAbsCOr1 C F := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    have h := h_env_max ⟨i, hi⟩
    simp only [circuit_norm, vec4_eval, hcpv, hFlags] at h
    exact h
  have hWCNEGvec : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i =>
          var { index := i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
            + 4 + 4 + 4 + 4 + i }) : Word (ZMod p))
      = wCnegWitness input_is_real C F := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    have h := h_env_wcneg ⟨i, hi⟩
    simp only [circuit_norm, vec4_eval, hcpv, hir, hFlags] at h
    exact h
  have hWRNEGvec : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i =>
          var { index := i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
            + 4 + 4 + 4 + 4 + 4 + i }) : Word (ZMod p))
      = wRnegWitness input_is_real B C F := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    have h := h_env_wrneg ⟨i, hi⟩
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hir, hFlags] at h
    exact h
  have hLTCLvec : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 2 fun i =>
          var { index := i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
            + 4 + 4 + 4 + 4 + 4 + 4 + 3 + i }) : Vector (ZMod p) 2)
      = ltClWitness input_is_real B C F := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    have h := h_env_cl ⟨i, hi⟩
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hir, hFlags] at h
    exact h
  have hLTFvec : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i =>
          var { index := i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
            + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + i }) : Vector (ZMod p) 4)
      = ltFlagsWitness input_is_real B C F := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    have h := h_env_f ⟨i, hi⟩
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hir, hFlags] at h
    exact h
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
  -- Product byte pins, projected through the small opaque layout lemma in `SubSpecs`.
  have hPL16 := SubSpecs.mulProduct_pins env.get (i₀ + 8 + 4 + 4 + 4 + 4)
    (populateMulLower input_is_real B C F) hMULLO
  have hPU16 := SubSpecs.mulProduct_pins env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45)
    (populateMulUpper input_is_real B C F) hMULHI
  have hPL0 := hPL16 ⟨0, by norm_num⟩
  have hPL1 := hPL16 ⟨1, by norm_num⟩
  have hPL2 := hPL16 ⟨2, by norm_num⟩
  have hPL3 := hPL16 ⟨3, by norm_num⟩
  have hPL4 := hPL16 ⟨4, by norm_num⟩
  have hPL5 := hPL16 ⟨5, by norm_num⟩
  have hPL6 := hPL16 ⟨6, by norm_num⟩
  have hPL7 := hPL16 ⟨7, by norm_num⟩
  have hPU8 := hPU16 ⟨8, by norm_num⟩
  have hPU9 := hPU16 ⟨9, by norm_num⟩
  have hPU10 := hPU16 ⟨10, by norm_num⟩
  have hPU11 := hPU16 ⟨11, by norm_num⟩
  have hPU12 := hPU16 ⟨12, by norm_num⟩
  have hPU13 := hPU16 ⟨13, by norm_num⟩
  have hPU14 := hPU16 ⟨14, by norm_num⟩
  have hPU15 := hPU16 ⟨15, by norm_num⟩
  -- derived gate facts
  have hirnwbin : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 4) = 0
      ∨ env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 4) = 1 := by
    rw [hSC4]
    rcases hbin with h | h
    · left; rw [h, zero_mul]
    · rcases he2sum with h2 | h2
      · right; rw [h, h2]; ring
      · left; rw [h, h2]; ring
  have hirnw_cases : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 4) = 1 →
      input_is_real = 1 ∧ F[4] + F[5] + F[6] + F[7] = 0 := by
    intro hx
    rw [hSC4] at hx
    rcases hbin with h | h
    · rw [h, zero_mul] at hx
      exact absurd hx zero_ne_one
    · rcases he2sum with h2 | h2
      · exact ⟨h, h2⟩
      · rw [h, h2] at hx
        exact absurd hx (by simp)
  have hE2bin : env.get (i₀ + 4) + env.get (i₀ + 5) + env.get (i₀ + 6) + env.get (i₀ + 7) = 0
      ∨ env.get (i₀ + 4) + env.get (i₀ + 5) + env.get (i₀ + 6) + env.get (i₀ + 7) = 1 := by
    rw [hfl4, hfl5, hfl6, hfl7]
    exact he2sum
  have hE2_one : env.get (i₀ + 4) + env.get (i₀ + 5) + env.get (i₀ + 6) + env.get (i₀ + 7) = 1 →
      F[4] + F[5] + F[6] + F[7] = 1 := by
    intro h
    rw [hfl4, hfl5, hfl6, hfl7] at h
    exact h
  have hgcneg : populateCNeg C F * input_is_real = 0
      ∨ populateCNeg C F * input_is_real = 1 := by
    rcases hbin with h | h
    · left; rw [h, mul_zero]
    · rw [h, mul_one]
      exact populateCNeg_bool hcU hsig
  have hgrneg : populateRemNeg B C F * input_is_real = 0
      ∨ populateRemNeg B C F * input_is_real = 1 := by
    rcases hbin with h | h
    · left; rw [h, mul_zero]
    · rw [h, mul_one]
      exact populateRemNeg_bool B C hsig
  have hltgbool : ltGate input_is_real C F = 0 ∨ ltGate input_is_real C F = 1 :=
    ltGate_bool C F hbin
  -- byte bounds at the populate values
  obtain ⟨hACb0, hACb1, hACb2, hACb3⟩ := Word.lt_cases_of_isU64 (populateAbsC_isU64 hcU F)
  obtain ⟨hARb0, hARb1, hARb2, hARb3⟩ := Word.lt_cases_of_isU64 (populateAbsRem_isU64 B C F)
  obtain ⟨hQb0, hQb1, hQb2, hQb3⟩ := Word.lt_cases_of_isU64 (populateQuotient_isU64 B C F)
  obtain ⟨hRb0, hRb1, hRb2, hRb3⟩ := Word.lt_cases_of_isU64 (populateRemainder_isU64 B C F)
  -- the ctq glue value bundles
  have hctqPad : input_is_real = 0 → ∀ (k : ℕ) (hk : k < 8), (populateCtq B C F)[k]'hk = 0 :=
    populateCtq_padding_of_template hpadvals
  have hctqLoReal := populateMulLower_product_pair B C F input_is_real hcU
  have hctqHiReal := populateMulUpper_product_pair B C F input_is_real hcU
    hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum
  -- folds for the `own` case (`ownAsserts_complete`): the five `scal` slots, the six whole-vector
  -- operand/witness blocks, and the prev-value bridges that the case bodies above don't already build.
  -- All clone the `hSC4` / `hCvec` patterns. (The three `IsEqual`/`IsZero` struct-result pins reference
  -- `colsV`, so they are derived inside `case own`.)
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
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    have h := h_env_b ⟨i, hi⟩
    simp only [circuit_norm, vec4_eval, hbpv, hFlags] at h
    exact h
  have hAvec : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var { index := i₀ + 8 + 4 + i }) : Word (ZMod p))
      = populateA B C F := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    have h := h_env_a ⟨i, hi⟩
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hQvec : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var { index :=
          i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2
            + 4 + 1 + 1 + 4 + i }) : Word (ZMod p))
      = populateQuotient B C F := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    have h := h_env_quot ⟨i, hi⟩
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hRvec : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var { index :=
          i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2
            + 4 + 1 + 1 + i }) : Word (ZMod p))
      = populateRemainder B C F := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    have h := h_env_rem ⟨i, hi⟩
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hCTQvecW : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 8 fun i => var { index := i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + i })
        : Vector (ZMod p) 8)
      = populateCtq B C F := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    have h := h_env_ctq ⟨i, hi⟩
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
  have hCARRYvecW : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 8 fun i => var { index := i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + i })
        : Vector (ZMod p) 8)
      = populateCarry B C F := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    have h := h_env_carry ⟨i, hi⟩
    simp only [circuit_norm, vec4_eval, hbpv, hcpv, hFlags] at h
    exact h
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
      /-
      let actual : DivRemCompare.Inputs (ZMod p) :=
        Eval.eval env (DivRemCompare.Inputs.ofCols (populatedRowAt inputExpr i₀))
      have hHonest := CompareComplete.honestSpec input_is_real B C F hbU hcU hbin
        hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum hpadvals
      unfold DivRemCompare.CompareSpec at hHonest
      dsimp only [CompareComplete.honestInputs] at hHonest
      obtain ⟨hEqBFull, hEqCFull, hEqBLow, hEqCLow, hZero, hAddC, hAddR, hLt,
        hBHigh, hCHigh, hRHigh, hBLow, hCLow, hRLow, hQLow⟩ := hHonest
      have hEqBFullActual : IsEqualWordOperation.Spec
          ⟨#v[actual.op_b_prev_value[0], actual.op_b_prev_value[1],
              actual.op_b_prev_value[2], actual.op_b_prev_value[3]],
            #v[0, 0, 0, 32768], actual.is_overflow_b, actual.is_real_not_word⟩ := by
        dsimp only [actual]
        simp +instances only [inputExpr, DivRemCompare.Inputs.ofCols, populatedRowAt,
          circuit_norm, h_input]
        rw [hbpv, hSC4]
        refine SubSpecs.subSpec_eqWord env.toEnvironment
          (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8) _ _ _ _
          (ovbWitness input_is_real B F) ?_ hOVB hEqBFull
        intro i hi
        simp only [ProvableType.toElements_fromElements, Vector.getElem_map,
          Vector.getElem_mapRange, circuit_norm]
      have hEqCFullActual : IsEqualWordOperation.Spec
          ⟨#v[actual.op_c_prev_value[0], actual.op_c_prev_value[1],
              actual.op_c_prev_value[2], actual.op_c_prev_value[3]],
            #v[65535, 65535, 65535, 65535], actual.is_overflow_c,
            actual.is_real_not_word⟩ := by
        dsimp only [actual]
        simp +instances only [inputExpr, DivRemCompare.Inputs.ofCols, populatedRowAt,
          circuit_norm, h_input]
        rw [hcpv, hSC4]
        refine SubSpecs.subSpec_eqWord env.toEnvironment
          (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11) _ _ _ _
          (ovcWitness input_is_real C F) ?_ hOVC hEqCFull
        intro i hi
        simp only [ProvableType.toElements_fromElements, Vector.getElem_map,
          Vector.getElem_mapRange, circuit_norm]
      have hEqBLowActual : IsEqualWordOperation.Spec
          ⟨#v[actual.op_b_prev_value[0], actual.op_b_prev_value[1], 0, 0],
            #v[0, 32768, 0, 0], actual.is_overflow_b,
            actual.is_divw + actual.is_remw + actual.is_divuw + actual.is_remuw⟩ := by
        dsimp only [actual]
        simp +instances only [inputExpr, DivRemCompare.Inputs.ofCols, populatedRowAt,
          circuit_norm, h_input]
        rw [hbpv, hfl4, hfl5, hfl6, hfl7]
        refine SubSpecs.subSpec_eqWord env.toEnvironment
          (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8) _ _ _ _
          (ovbWitness input_is_real B F) ?_ hOVB hEqBLow
        intro i hi
        simp only [ProvableType.toElements_fromElements, Vector.getElem_map,
          Vector.getElem_mapRange, circuit_norm]
      have hEqCLowActual : IsEqualWordOperation.Spec
          ⟨#v[actual.op_c_prev_value[0], actual.op_c_prev_value[1], 0, 0],
            #v[65535, 65535, 0, 0], actual.is_overflow_c,
            actual.is_divw + actual.is_remw + actual.is_divuw + actual.is_remuw⟩ := by
        dsimp only [actual]
        simp +instances only [inputExpr, DivRemCompare.Inputs.ofCols, populatedRowAt,
          circuit_norm, h_input]
        rw [hcpv, hfl4, hfl5, hfl6, hfl7]
        refine SubSpecs.subSpec_eqWord env.toEnvironment
          (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11) _ _ _ _
          (ovcWitness input_is_real C F) ?_ hOVC hEqCLow
        intro i hi
        simp only [ProvableType.toElements_fromElements, Vector.getElem_map,
          Vector.getElem_mapRange, circuit_norm]
      have hZeroActual : IsZeroWordOperation.Spec
          ⟨actual.c, actual.is_c_0, actual.is_real⟩ := by
        dsimp only [actual]
        simp +instances only [inputExpr, DivRemCompare.Inputs.ofCols, populatedRowAt,
          circuit_norm, h_input]
        rw [hCvec]
        refine SubSpecs.subSpec_isZero env.toEnvironment
          (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11) _ _ _
          isc0Witness ?_ hISC0 (by simpa only [isc0Witness] using hZero)
        intro i hi
        simp only [ProvableType.toElements_fromElements, Vector.getElem_map,
          Vector.getElem_mapRange, circuit_norm]
      have hAddCActual : AddOperation.Spec
          ⟨actual.c, actual.abs_c, ⟨actual.c_neg_operation.value⟩,
            actual.abs_c_alu_event⟩ := by
        dsimp only [actual]
        simp +instances only [inputExpr, DivRemCompare.Inputs.ofCols, populatedRowAt,
          circuit_norm, h_input]
        rw [hCvec, hABSCvec, hWCNEGvec, hMISC0]
        exact hAddC
      have hAddRActual : AddOperation.Spec
          ⟨actual.remainder_comp, actual.abs_remainder,
            ⟨actual.rem_neg_operation.value⟩, actual.abs_rem_alu_event⟩ := by
        dsimp only [actual]
        simp +instances only [inputExpr, DivRemCompare.Inputs.ofCols, populatedRowAt,
          circuit_norm, h_input]
        rw [hRCvec, hABSRvec, hWRNEGvec, hMISC1]
        exact hAddR
      have hLtActual : LtOperationUnsigned.Spec
          ⟨actual.abs_remainder, actual.max_abs_c_or_1,
            actual.remainder_lt_operation, actual.remainder_check_multiplicity⟩ := by
        dsimp only [actual]
        simp +instances only [inputExpr, DivRemCompare.Inputs.ofCols, populatedRowAt,
          circuit_norm, h_input]
        rw [hABSRvec, hMAXvec, hLTFvec, hLTCLvec, hNEI, hBIT, hMISC2]
        exact hLt
      have hBHighActual : U16MSBOperation.Spec
          ⟨actual.op_b_prev_value[3], actual.b_msb, actual.is_real_not_word⟩ := by
        dsimp only [actual]
        simp +instances only [inputExpr, DivRemCompare.Inputs.ofCols, populatedRowAt,
          circuit_norm, h_input]
        rw [hbpv, hBM, hSC4]
        exact hBHigh
      have hCHighActual : U16MSBOperation.Spec
          ⟨actual.op_c_prev_value[3], actual.c_msb, actual.is_real_not_word⟩ := by
        dsimp only [actual]
        simp +instances only [inputExpr, DivRemCompare.Inputs.ofCols, populatedRowAt,
          circuit_norm, h_input]
        rw [hcpv, hCM, hSC4]
        exact hCHigh
      have hRHighActual : U16MSBOperation.Spec
          ⟨actual.remainder[3], actual.rem_msb, actual.is_real_not_word⟩ := by
        dsimp only [actual]
        simp +instances only [inputExpr, DivRemCompare.Inputs.ofCols, populatedRowAt,
          circuit_norm, h_input]
        rw [hRvec, hRM, hSC4]
        exact hRHigh
      have hBLowActual : U16MSBOperation.Spec
          ⟨actual.op_b_prev_value[1], actual.b_msb,
            actual.is_divw + actual.is_remw + actual.is_divuw + actual.is_remuw⟩ := by
        dsimp only [actual]
        simp +instances only [inputExpr, DivRemCompare.Inputs.ofCols, populatedRowAt,
          circuit_norm, h_input]
        rw [hbpv, hBM, hfl4, hfl5, hfl6, hfl7]
        exact hBLow
      have hCLowActual : U16MSBOperation.Spec
          ⟨actual.op_c_prev_value[1], actual.c_msb,
            actual.is_divw + actual.is_remw + actual.is_divuw + actual.is_remuw⟩ := by
        dsimp only [actual]
        simp +instances only [inputExpr, DivRemCompare.Inputs.ofCols, populatedRowAt,
          circuit_norm, h_input]
        rw [hcpv, hCM, hfl4, hfl5, hfl6, hfl7]
        exact hCLow
      have hRLowActual : U16MSBOperation.Spec
          ⟨actual.remainder[1], actual.rem_msb,
            actual.is_divw + actual.is_remw + actual.is_divuw + actual.is_remuw⟩ := by
        dsimp only [actual]
        simp +instances only [inputExpr, DivRemCompare.Inputs.ofCols, populatedRowAt,
          circuit_norm, h_input]
        rw [hRvec, hRM, hfl4, hfl5, hfl6, hfl7]
        exact hRLow
      have hQLowActual : U16MSBOperation.Spec
          ⟨actual.quotient[1], actual.quot_msb,
            actual.is_divw + actual.is_remw + actual.is_divuw + actual.is_remuw⟩ := by
        dsimp only [actual]
        simp +instances only [inputExpr, DivRemCompare.Inputs.ofCols, populatedRowAt,
          circuit_norm, h_input]
        rw [hQvec, hQM, hfl4, hfl5, hfl6, hfl7]
        exact hQLow
      change DivRemCompare.CompareSpec actual
      unfold DivRemCompare.CompareSpec
      exact ⟨hEqBFullActual, hEqCFullActual, hEqBLowActual, hEqCLowActual, hZeroActual,
        hAddCActual, hAddRActual, hLtActual, hBHighActual, hCHighActual, hRHighActual,
        hBLowActual, hCLowActual, hRLowActual, hQLowActual⟩
      -/
      /-
      simp +instances only [DivRemCompare.Inputs.ofCols, populatedRowAt, circuit_norm, h_input]
      simp only [DivRemCompare.CompareSpec]
      and_intros
      · rw [hbpv]
        rcases hbin with h0 | h1
        · have hg0 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 4) = 0 := by
            rw [hSC4, h0, zero_mul]
          rw [hg0]
          refine SubSpecs.subSpec_eqWord env.toEnvironment
            (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8) _ _ _ _
            (ovbWitness input_is_real B F) ?_ hOVB (by
              rw [ovbWitness, if_neg (fun hx => absurd (h0.symm.trans hx) zero_ne_one)]
              exact IsEqualWordOperation.spec_zero B #v[0, 0, 0, 32768]
                (rfl : (0 : ZMod p) = 0))
          intro i hi
          simp only [ProvableType.toElements_fromElements, Vector.getElem_map,
            Vector.getElem_mapRange, circuit_norm]
        · rcases he2sum with hw0 | hw1
          · have hg1 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 4) = 1 := by
              rw [hSC4, h1, hw0]
              norm_num
            rw [hg1]
            refine SubSpecs.subSpec_eqWord env.toEnvironment
              (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8) _ _ _ _
              (ovbWitness input_is_real B F) ?_ hOVB (by
                rw [ovbWitness, if_pos h1,
                  if_neg (fun hx => absurd (hw0.symm.trans hx) zero_ne_one)]
                exact IsEqualWordOperation.spec_populate B #v[0, 0, 0, 32768] 1)
            intro i hi
            simp only [ProvableType.toElements_fromElements, Vector.getElem_map,
              Vector.getElem_mapRange, circuit_norm]
          · have hg0 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 4) = 0 := by
              rw [hSC4, h1, hw1]
              norm_num
            rw [hg0]
            refine SubSpecs.subSpec_eqWord env.toEnvironment
              (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8) _ _ _ _
              (ovbWitness input_is_real B F) ?_ hOVB (by
                rw [ovbWitness, if_pos h1, if_pos hw1]
                exact IsEqualWordOperation.spec_populate_offGate B #v[0, 0, 0, 32768]
                  #v[B[0], B[1], 0, 0] #v[0, 32768, 0, 0] (rfl : (0 : ZMod p) = 0))
            intro i hi
            simp only [ProvableType.toElements_fromElements, Vector.getElem_map,
              Vector.getElem_mapRange, circuit_norm]
      · rw [hcpv]
        rcases hbin with h0 | h1
        · have hg0 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 4) = 0 := by
            rw [hSC4, h0, zero_mul]
          rw [hg0]
          refine SubSpecs.subSpec_eqWord env.toEnvironment
            (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11) _ _ _ _
            (ovcWitness input_is_real C F) ?_ hOVC (by
              rw [ovcWitness, if_neg (fun hx => absurd (h0.symm.trans hx) zero_ne_one)]
              exact IsEqualWordOperation.spec_zero C #v[65535, 65535, 65535, 65535]
                (rfl : (0 : ZMod p) = 0))
          intro i hi
          simp only [ProvableType.toElements_fromElements, Vector.getElem_map,
            Vector.getElem_mapRange, circuit_norm]
        · rcases he2sum with hw0 | hw1
          · have hg1 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 4) = 1 := by
              rw [hSC4, h1, hw0]
              norm_num
            rw [hg1]
            refine SubSpecs.subSpec_eqWord env.toEnvironment
              (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11) _ _ _ _
              (ovcWitness input_is_real C F) ?_ hOVC (by
                rw [ovcWitness, if_pos h1,
                  if_neg (fun hx => absurd (hw0.symm.trans hx) zero_ne_one)]
                exact IsEqualWordOperation.spec_populate C #v[65535, 65535, 65535, 65535] 1)
            intro i hi
            simp only [ProvableType.toElements_fromElements, Vector.getElem_map,
              Vector.getElem_mapRange, circuit_norm]
          · have hg0 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 4) = 0 := by
              rw [hSC4, h1, hw1]
              norm_num
            rw [hg0]
            refine SubSpecs.subSpec_eqWord env.toEnvironment
              (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11) _ _ _ _
              (ovcWitness input_is_real C F) ?_ hOVC (by
                rw [ovcWitness, if_pos h1, if_pos hw1]
                exact IsEqualWordOperation.spec_populate_offGate C
                  #v[65535, 65535, 65535, 65535] #v[C[0], C[1], 0, 0]
                  #v[65535, 65535, 0, 0] (rfl : (0 : ZMod p) = 0))
            intro i hi
            simp only [ProvableType.toElements_fromElements, Vector.getElem_map,
              Vector.getElem_mapRange, circuit_norm]
      · rw [hbpv, hfl4, hfl5, hfl6, hfl7]
        rcases he2sum with hw0 | hw1
        · rw [hw0]
          rcases hbin with h0 | h1
          · refine SubSpecs.subSpec_eqWord env.toEnvironment
              (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8) _ _ _ _
              (ovbWitness input_is_real B F) ?_ hOVB (by
                rw [ovbWitness, if_neg (fun hx => absurd (h0.symm.trans hx) zero_ne_one)]
                exact IsEqualWordOperation.spec_zero (#v[B[0], B[1], 0, 0] : Word (ZMod p))
                  #v[0, 32768, 0, 0] (rfl : (0 : ZMod p) = 0))
            intro i hi
            simp only [ProvableType.toElements_fromElements, Vector.getElem_map,
              Vector.getElem_mapRange, circuit_norm]
          · refine SubSpecs.subSpec_eqWord env.toEnvironment
              (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8) _ _ _ _
              (ovbWitness input_is_real B F) ?_ hOVB (by
                rw [ovbWitness, if_pos h1,
                  if_neg (fun hx => absurd (hw0.symm.trans hx) zero_ne_one)]
                exact IsEqualWordOperation.spec_populate_offGate
                  (#v[B[0], B[1], 0, 0] : Word (ZMod p)) #v[0, 32768, 0, 0]
                  B #v[0, 0, 0, 32768] (rfl : (0 : ZMod p) = 0))
            intro i hi
            simp only [ProvableType.toElements_fromElements, Vector.getElem_map,
              Vector.getElem_mapRange, circuit_norm]
        · have h1 : input_is_real = 1 := by
            rcases hbin with h0 | h1
            · obtain ⟨-, -, hF0⟩ := hpadvals h0
              rw [hF0] at hw1
              simp at hw1
            · exact h1
          rw [hw1]
          refine SubSpecs.subSpec_eqWord env.toEnvironment
            (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8) _ _ _ _
            (ovbWitness input_is_real B F) ?_ hOVB (by
              rw [ovbWitness, if_pos h1, if_pos hw1]
              exact IsEqualWordOperation.spec_populate (#v[B[0], B[1], 0, 0] : Word (ZMod p))
                #v[0, 32768, 0, 0] 1)
          intro i hi
          simp only [ProvableType.toElements_fromElements, Vector.getElem_map,
            Vector.getElem_mapRange, circuit_norm]
      · rw [hcpv, hfl4, hfl5, hfl6, hfl7]
        rcases he2sum with hw0 | hw1
        · rw [hw0]
          rcases hbin with h0 | h1
          · refine SubSpecs.subSpec_eqWord env.toEnvironment
              (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11) _ _ _ _
              (ovcWitness input_is_real C F) ?_ hOVC (by
                rw [ovcWitness, if_neg (fun hx => absurd (h0.symm.trans hx) zero_ne_one)]
                exact IsEqualWordOperation.spec_zero (#v[C[0], C[1], 0, 0] : Word (ZMod p))
                  #v[65535, 65535, 0, 0] (rfl : (0 : ZMod p) = 0))
            intro i hi
            simp only [ProvableType.toElements_fromElements, Vector.getElem_map,
              Vector.getElem_mapRange, circuit_norm]
          · refine SubSpecs.subSpec_eqWord env.toEnvironment
              (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11) _ _ _ _
              (ovcWitness input_is_real C F) ?_ hOVC (by
                rw [ovcWitness, if_pos h1,
                  if_neg (fun hx => absurd (hw0.symm.trans hx) zero_ne_one)]
                exact IsEqualWordOperation.spec_populate_offGate
                  (#v[C[0], C[1], 0, 0] : Word (ZMod p)) #v[65535, 65535, 0, 0]
                  C #v[65535, 65535, 65535, 65535] (rfl : (0 : ZMod p) = 0))
            intro i hi
            simp only [ProvableType.toElements_fromElements, Vector.getElem_map,
              Vector.getElem_mapRange, circuit_norm]
        · have h1 : input_is_real = 1 := by
            rcases hbin with h0 | h1
            · obtain ⟨-, -, hF0⟩ := hpadvals h0
              rw [hF0] at hw1
              simp at hw1
            · exact h1
          rw [hw1]
          refine SubSpecs.subSpec_eqWord env.toEnvironment
            (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11) _ _ _ _
            (ovcWitness input_is_real C F) ?_ hOVC (by
              rw [ovcWitness, if_pos h1, if_pos hw1]
              exact IsEqualWordOperation.spec_populate (#v[C[0], C[1], 0, 0] : Word (ZMod p))
                #v[65535, 65535, 0, 0] 1)
          intro i hi
          simp only [ProvableType.toElements_fromElements, Vector.getElem_map,
            Vector.getElem_mapRange, circuit_norm]
      · rw [hCvec]
        refine SubSpecs.subSpec_isZero env.toEnvironment
          (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11) _ _ _
          isc0Witness ?_ hISC0 (by
            simp only [isc0Witness, isC0Witness]
            exact IsZeroWordOperation.spec_populate (cComp C F) input_is_real)
        intro i hi
        simp only [ProvableType.toElements_fromElements, Vector.getElem_map,
          Vector.getElem_mapRange, circuit_norm]
      · rw [hCvec, hABSCvec, hWCNEGvec, hMISC0]
        rcases hgcneg with hg0 | hg1
        · rw [hg0]
          exact fun hx => absurd hx zero_ne_one
        · rw [hg1, show wCnegWitness input_is_real C F =
              AddOperation.populate (cComp C F) (populateAbsC C F) from by
              rw [wCnegWitness, if_pos hg1]]
          exact AddOperation.spec_populate (cComp_isU64 hcU F)
            (populateAbsC_isU64 hcU F) 1
      · rw [hRCvec, hABSRvec, hWRNEGvec, hMISC1]
        rcases hgrneg with hg0 | hg1
        · rw [hg0]
          exact fun hx => absurd hx zero_ne_one
        · rw [hg1]
          have h67 := flags67_eq_zero_of_remNeg_mul_eq_one B C input_is_real
            hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum hg1
          have hRCR : populateRemComp B C F = populateRemainder B C F := by
            unfold populateRemComp remCompBits populateRemainder
            rw [if_neg (fun hx => absurd (h67.symm.trans hx) zero_ne_one)]
          rw [hRCR, show wRnegWitness input_is_real B C F =
              AddOperation.populate (populateRemainder B C F) (populateAbsRem B C F) from by
              rw [wRnegWitness, if_pos hg1]]
          exact AddOperation.spec_populate (populateRemainder_isU64 B C F)
            (populateAbsRem_isU64 B C F) 1
      · rw [hABSRvec, hMAXvec, hLTFvec, hLTCLvec, hNEI, hBIT, hMISC2]
        rcases hltgbool with hg0 | hg1
        · rw [hg0, show ltFlagsWitness input_is_real B C F =
              (#v[0, 0, 0, 0] : Vector (ZMod p) 4) from by
              rw [ltFlagsWitness, if_neg (fun hx => absurd (hg0.symm.trans hx) zero_ne_one)],
            show ltClWitness input_is_real B C F = (#v[0, 0] : Vector (ZMod p) 2) from by
              rw [ltClWitness, if_neg (fun hx => absurd (hg0.symm.trans hx) zero_ne_one)],
            show (ltNotEqInvWitness input_is_real B C F)[0] = 0 from by
              rw [ltNotEqInvWitness, if_neg (fun hx => absurd (hg0.symm.trans hx) zero_ne_one)]
              rfl,
            show (ltBitWitness input_is_real B C F)[0] = 0 from by
              rw [ltBitWitness, if_neg (fun hx => absurd (hg0.symm.trans hx) zero_ne_one)]
              rfl]
          exact LtOperationUnsigned.spec_zero (populateAbsRem B C F)
            (populateMaxAbsCOr1 C F) rfl
        · rw [hg1, show ltClWitness input_is_real B C F =
              LtOperationUnsigned.comparisonLimbsWitness (populateAbsRem B C F)
                (populateMaxAbsCOr1 C F) from by rw [ltClWitness, if_pos hg1],
            show ltFlagsWitness input_is_real B C F =
              LtOperationUnsigned.flagsWitness (populateAbsRem B C F)
                (populateMaxAbsCOr1 C F) from by rw [ltFlagsWitness, if_pos hg1],
            show (ltNotEqInvWitness input_is_real B C F)[0] =
              (LtOperationUnsigned.notEqInvWitness (populateAbsRem B C F)
                (populateMaxAbsCOr1 C F))[0] from by rw [ltNotEqInvWitness, if_pos hg1],
            show (ltBitWitness input_is_real B C F)[0] =
              U16CompareOperation.populate_bit
                (LtOperationUnsigned.comparisonLimbsWitness (populateAbsRem B C F)
                  (populateMaxAbsCOr1 C F))[0]
                (LtOperationUnsigned.comparisonLimbsWitness (populateAbsRem B C F)
                  (populateMaxAbsCOr1 C F))[1] from by
              rw [ltBitWitness, if_pos hg1, ltClWitness, if_pos hg1]
              rfl]
          exact LtOperationUnsigned.spec_populate
      · exact ⟨by rw [hBM]; exact bMsbCell_bool hbU F, fun hg => by
          obtain ⟨_, hw0⟩ := hirnw_cases hg
          rw [hBM, heb3, bMsbCell, if_neg (fun hx => absurd (hw0.symm.trans hx) zero_ne_one)]
          exact (U16MSBOperation.spec_populate hbU3 1).2 rfl⟩
      · exact ⟨by rw [hCM]; exact cMsbCell_bool hcU F, fun hg => by
          obtain ⟨_, hw0⟩ := hirnw_cases hg
          rw [hCM, hec3, cMsbCell, if_neg (fun hx => absurd (hw0.symm.trans hx) zero_ne_one)]
          exact (U16MSBOperation.spec_populate hcU3 1).2 rfl⟩
      · exact ⟨by rw [hRM]; exact remMsbCell_bool B C F, fun hg => by
          obtain ⟨_, hw0⟩ := hirnw_cases hg
          rw [hRM, hREM3, remMsbCell,
            if_neg (fun hx => absurd (hw0.symm.trans hx) zero_ne_one)]
          exact (U16MSBOperation.spec_populate hRb3 1).2 rfl⟩
      · exact ⟨by rw [hBM]; exact bMsbCell_bool hbU F, fun hg => by
          have hw1 := hE2_one hg
          rw [hBM, heb1, bMsbCell, if_pos hw1]
          exact (U16MSBOperation.spec_populate hbU1 1).2 rfl⟩
      · exact ⟨by rw [hCM]; exact cMsbCell_bool hcU F, fun hg => by
          have hw1 := hE2_one hg
          rw [hCM, hec1, cMsbCell, if_pos hw1]
          exact (U16MSBOperation.spec_populate hcU1 1).2 rfl⟩
      · exact ⟨by rw [hRM]; exact remMsbCell_bool B C F, fun hg => by
          have hw1 := hE2_one hg
          rw [hRM, hREM1, remMsbCell, if_pos hw1]
          exact (U16MSBOperation.spec_populate hRb1 1).2 rfl⟩
      · exact ⟨by rw [hQM]; exact quotMsbCell_bool B C F, fun hg => by
          have hw1 := hE2_one hg
          rw [hQM, hQUOT1, quotMsbCell, if_pos hw1]
          exact (U16MSBOperation.spec_populate hQb1 1).2 rfl⟩
      -/
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
  /- Legacy flattened child proof, retained temporarily while its cases are regrouped above.
  refine ⟨?mulLo, ?mulHi, ?ctq0, ?ctq1, ?ctq2, ?ctq3, ?ctq4, ?ctq5, ?ctq6, ?ctq7,
    ?eqb, ?eqc, ?eqb2, ?eqc2, ?isc0, ?addc, ?addr, ?lt,
    ?msb0, ?msb1, ?msb2, ?msb3, ?msb4, ?msb5, ?msb6, ?cpu, ?rtype, ?own,
    ?pe123, ?pe127, ?pe131, ?pe135, ?pe139, ?pe143, ?pe147, ?pe151,
    ?pabsc0, ?pabsc1, ?pabsc2, ?pabsc3, ?pabsr0, ?pabsr1, ?pabsr2, ?pabsr3,
    ?pq0, ?pq1, ?pq2, ?pq3, ?pr0, ?pr1, ?pr2, ?pr3,
    ?pctq0, ?pctq1, ?pctq2, ?pctq3, ?pctq4, ?pctq5, ?pctq6, ?pctq7,
    ?pe2r1, ?pe2q1, ?regwrite⟩
  case cpu => exact ⟨hbin, by rw [← epc0, ← epc1, ← epc2] at h_cpu; exact h_cpu⟩
  case regwrite =>
    -- RegisterWrite's op_a write push: `is_real` binary + the witnessed result `a = populateA B C F`
    -- (`hAvec`), whose `isU64` is unconditional (`populateA_isU64`).
    exact ⟨⟨hbin, fun _ => by rw [hAvec]; exact populateA_isU64 B C F⟩, trivial⟩
  case rtype =>
    -- (W11 flip) the reader's `Assumptions` is now the pair `⟨is_real binary, is_trusted binary⟩` (both
    -- `is_real` here), and its `Spec` gained the trailing decode conjunct `hdec` (provided by completeness).
    exact ⟨⟨hbin, hbin⟩, ⟨⟨hz _, hz _, hz _, hz _⟩, Or.inl hop_a_0, hrac_a, hrac_b, hrac_c, hdec,
      fun hr => ⟨ha_prev hr, hbU, hcU⟩⟩⟩
  case mulLo =>
    rw [hQCvec, hCvec]
    have hsumArgLo : input_is_real + 0 + 0 + 0 + 0 = 0
        ∨ input_is_real + 0 + 0 + 0 + 0 = 1 := by
      rcases hbin with h | h
      · left; rw [h]; norm_num
      · right; rw [h]; norm_num
    refine ⟨⟨fun _ => ⟨populateQuotComp_isU64 B C F, cComp_isU64 hcU F⟩, hbin,
      fun hx => absurd hx zero_ne_one, hbin, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl,
      hsumArgLo⟩, ?_⟩
    rcases hbin with h0 | h1
    · refine SubSpecs.subSpec_mul env.toEnvironment (i₀ + 8 + 4 + 4 + 4 + 4)
        _ _ _ _ _ _ _ _ _ (populateMulLower input_is_real B C F) ?_ hMULLO
        (by
          rw [populateMulLower, if_neg (fun hx => absurd (h0.symm.trans hx) zero_ne_one)]
          exact MulOperation.spec_zero (populateQuotComp B C F) (cComp C F)
            input_is_real 0 0 0 0 h0)
      intro i hi
      refine Eq.trans ?_ (getElem_toElements_eval_varFromOffset env.toEnvironment
        (i₀ + 8 + 4 + 4 + 4 + 4) i hi)
      simp [circuit_norm]
    · refine SubSpecs.subSpec_mul env.toEnvironment (i₀ + 8 + 4 + 4 + 4 + 4)
        _ _ _ _ _ _ _ _ _ (populateMulLower input_is_real B C F) ?_ hMULLO
        (by
          rw [populateMulLower, if_pos h1]
          exact MulOperation.spec_populate (populateQuotComp_isU64 B C F) (cComp_isU64 hcU F)
            input_is_real 0 0 0 0 input_is_real (Or.inr h1) (Or.inl rfl) (Or.inl rfl)
            (Or.inl rfl) (Or.inl rfl) hsumArgLo)
      intro i hi
      refine Eq.trans ?_ (getElem_toElements_eval_varFromOffset env.toEnvironment
        (i₀ + 8 + 4 + 4 + 4 + 4) i hi)
      simp [circuit_norm]
  case mulHi =>
    rw [hQCvec, hCvec, hfl0, hfl1, hfl2, hfl3]
    have hsumArg : (0 : ZMod p) + (F[0] + F[2]) + (F[1] + F[3]) + 0 + 0 = 0
        ∨ (0 : ZMod p) + (F[0] + F[2]) + (F[1] + F[3]) + 0 + 0 = 1 := by
      rcases hg64 with h | h
      · left; linear_combination h
      · right; linear_combination h
    refine ⟨⟨fun _ => ⟨populateQuotComp_isU64 B C F, cComp_isU64 hcU F⟩, hirnwbin,
      fun hx => absurd hx zero_ne_one, Or.inl rfl, hd_r, hdu_r, Or.inl rfl, Or.inl rfl,
      hsumArg⟩, ?_⟩
    by_cases hcond : input_is_real = 1 ∧ F[0] + F[1] + F[2] + F[3] = 1
    · refine SubSpecs.subSpec_mul env.toEnvironment (i₀ + 8 + 4 + 4 + 4 + 4 + 45)
        _ _ _ _ _ _ _ _ _ (populateMulUpper input_is_real B C F) ?_ hMULHI
        (by
          rw [populateMulUpper, if_pos hcond]
          exact MulOperation.spec_populate (populateQuotComp_isU64 B C F) (cComp_isU64 hcU F)
            0 (F[0] + F[2]) (F[1] + F[3]) 0 0 (env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 4))
            (Or.inl rfl) hd_r hdu_r (Or.inl rfl) (Or.inl rfl) hsumArg)
      intro i hi
      refine Eq.trans ?_ (getElem_toElements_eval_varFromOffset env.toEnvironment
        (i₀ + 8 + 4 + 4 + 4 + 4 + 45) i hi)
      simp [circuit_norm]
    · have hg0 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 4) = 0 := by
        rw [hSC4]
        rcases hbin with h | h
        · rw [h, zero_mul]
        · rcases he2sum with h2 | h2
          · exact absurd ⟨h, by linear_combination hsum - h2⟩ hcond
          · rw [h, h2]; ring
      refine SubSpecs.subSpec_mul env.toEnvironment (i₀ + 8 + 4 + 4 + 4 + 4 + 45)
        _ _ _ _ _ _ _ _ _ (populateMulUpper input_is_real B C F) ?_ hMULHI
        (by
          rw [populateMulUpper, if_neg hcond]
          exact MulOperation.spec_zero (populateQuotComp B C F) (cComp C F)
            0 (F[0] + F[2]) (F[1] + F[3]) 0 0 hg0)
      intro i hi
      refine Eq.trans ?_ (getElem_toElements_eval_varFromOffset env.toEnvironment
        (i₀ + 8 + 4 + 4 + 4 + 4 + 45) i hi)
      simp [circuit_norm]
  case ctq0 =>
    rw [hCTQ0, hPL0, hPL1]
    rcases hbin with h0 | h1
    · rw [hctqPad h0 0 (by norm_num), populateMulLower,
        if_neg (fun hx => absurd (h0.symm.trans hx) zero_ne_one)]
      simp [MulOperation.zeroCols]
    · simpa using hctqLoReal h1 0 (by norm_num)
  case ctq1 =>
    rw [hCTQ1, hPL2, hPL3]
    rcases hbin with h0 | h1
    · rw [hctqPad h0 1 (by norm_num), populateMulLower,
        if_neg (fun hx => absurd (h0.symm.trans hx) zero_ne_one)]
      simp [MulOperation.zeroCols]
    · simpa using hctqLoReal h1 1 (by norm_num)
  case ctq2 =>
    rw [hCTQ2, hPL4, hPL5]
    rcases hbin with h0 | h1
    · rw [hctqPad h0 2 (by norm_num), populateMulLower,
        if_neg (fun hx => absurd (h0.symm.trans hx) zero_ne_one)]
      simp [MulOperation.zeroCols]
    · simpa using hctqLoReal h1 2 (by norm_num)
  case ctq3 =>
    rw [hCTQ3, hPL6, hPL7]
    rcases hbin with h0 | h1
    · rw [hctqPad h0 3 (by norm_num), populateMulLower,
        if_neg (fun hx => absurd (h0.symm.trans hx) zero_ne_one)]
      simp [MulOperation.zeroCols]
    · simpa using hctqLoReal h1 3 (by norm_num)
  case ctq4 =>
    rw [hfl0, hfl1, hfl2, hfl3, hCTQ4, hPU8, hPU9]
    rcases hg64 with hg | hg
    · rw [hg, zero_mul]
    · rw [hg, one_mul]
      rcases hbin with h0 | h1
      · rw [hctqPad h0 4 (by norm_num), populateMulUpper,
          if_neg (fun hx => absurd (h0.symm.trans hx.1) zero_ne_one)]
        simp [MulOperation.zeroCols]
      · have h := hctqHiReal h1 hg 0 (by norm_num)
        norm_num at h
        rw [h]
        exact add_neg_cancel (_ : ZMod p)
  case ctq5 =>
    rw [hfl0, hfl1, hfl2, hfl3, hCTQ5, hPU10, hPU11]
    rcases hg64 with hg | hg
    · rw [hg, zero_mul]
    · rw [hg, one_mul]
      rcases hbin with h0 | h1
      · rw [hctqPad h0 5 (by norm_num), populateMulUpper,
          if_neg (fun hx => absurd (h0.symm.trans hx.1) zero_ne_one)]
        simp [MulOperation.zeroCols]
      · have h := hctqHiReal h1 hg 1 (by norm_num)
        norm_num at h
        rw [h]
        exact add_neg_cancel (_ : ZMod p)
  case ctq6 =>
    rw [hfl0, hfl1, hfl2, hfl3, hCTQ6, hPU12, hPU13]
    rcases hg64 with hg | hg
    · rw [hg, zero_mul]
    · rw [hg, one_mul]
      rcases hbin with h0 | h1
      · rw [hctqPad h0 6 (by norm_num), populateMulUpper,
          if_neg (fun hx => absurd (h0.symm.trans hx.1) zero_ne_one)]
        simp [MulOperation.zeroCols]
      · have h := hctqHiReal h1 hg 2 (by norm_num)
        norm_num at h
        rw [h]
        exact add_neg_cancel (_ : ZMod p)
  case ctq7 =>
    rw [hfl0, hfl1, hfl2, hfl3, hCTQ7, hPU14, hPU15]
    rcases hg64 with hg | hg
    · rw [hg, zero_mul]
    · rw [hg, one_mul]
      rcases hbin with h0 | h1
      · rw [hctqPad h0 7 (by norm_num), populateMulUpper,
          if_neg (fun hx => absurd (h0.symm.trans hx.1) zero_ne_one)]
        simp [MulOperation.zeroCols]
      · have h := hctqHiReal h1 hg 3 (by norm_num)
        norm_num at h
        rw [h]
        exact add_neg_cancel (_ : ZMod p)
  case eqb =>
    rw [vec4_eval, hbpv]
    rcases hbin with h0 | h1
    · have hg0 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 4) = 0 := by
        rw [hSC4, h0, zero_mul]
      rw [hg0]
      refine ⟨Or.inl rfl, ?_⟩
      refine SubSpecs.subSpec_eqWord env.toEnvironment
        (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8) _ _ _ _
        (ovbWitness input_is_real B F) ?_ hOVB
        (by
          rw [ovbWitness, if_neg (fun hx => absurd (h0.symm.trans hx) zero_ne_one)]
          exact IsEqualWordOperation.spec_zero B #v[0, 0, 0, 32768] (rfl : (0 : ZMod p) = 0))
      intro i hi
      simp only [ProvableType.toElements_fromElements, Vector.getElem_map, Vector.getElem_mapRange,
        circuit_norm]
    · rcases he2sum with hw0 | hw1
      · have hg1 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 4) = 1 := by
          rw [hSC4, h1, hw0]; norm_num
        rw [hg1]
        refine ⟨Or.inr rfl, ?_⟩
        refine SubSpecs.subSpec_eqWord env.toEnvironment
          (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8) _ _ _ _
          (ovbWitness input_is_real B F) ?_ hOVB
          (by
            rw [ovbWitness, if_pos h1, if_neg (fun hx => absurd (hw0.symm.trans hx) zero_ne_one)]
            exact IsEqualWordOperation.spec_populate B #v[0, 0, 0, 32768] 1)
        intro i hi
        simp only [ProvableType.toElements_fromElements, Vector.getElem_map, Vector.getElem_mapRange,
        circuit_norm]
      · have hg0 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 4) = 0 := by
          rw [hSC4, h1, hw1]; norm_num
        rw [hg0]
        refine ⟨Or.inl rfl, ?_⟩
        refine SubSpecs.subSpec_eqWord env.toEnvironment
          (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8) _ _ _ _
          (ovbWitness input_is_real B F) ?_ hOVB
          (by
            rw [ovbWitness, if_pos h1, if_pos hw1]
            exact IsEqualWordOperation.spec_populate_offGate B #v[0, 0, 0, 32768]
              #v[B[0], B[1], 0, 0] #v[0, 32768, 0, 0] (rfl : (0 : ZMod p) = 0))
        intro i hi
        simp only [ProvableType.toElements_fromElements, Vector.getElem_map, Vector.getElem_mapRange,
        circuit_norm]
  case eqc =>
    rw [vec4_eval, hcpv]
    rcases hbin with h0 | h1
    · have hg0 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 4) = 0 := by
        rw [hSC4, h0, zero_mul]
      rw [hg0]
      refine ⟨Or.inl rfl, ?_⟩
      refine SubSpecs.subSpec_eqWord env.toEnvironment
        (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11) _ _ _ _
        (ovcWitness input_is_real C F) ?_ hOVC
        (by
          rw [ovcWitness, if_neg (fun hx => absurd (h0.symm.trans hx) zero_ne_one)]
          exact IsEqualWordOperation.spec_zero C #v[65535, 65535, 65535, 65535]
            (rfl : (0 : ZMod p) = 0))
      intro i hi
      simp only [ProvableType.toElements_fromElements, Vector.getElem_map, Vector.getElem_mapRange,
        circuit_norm]
    · rcases he2sum with hw0 | hw1
      · have hg1 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 4) = 1 := by
          rw [hSC4, h1, hw0]; norm_num
        rw [hg1]
        refine ⟨Or.inr rfl, ?_⟩
        refine SubSpecs.subSpec_eqWord env.toEnvironment
          (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11) _ _ _ _
          (ovcWitness input_is_real C F) ?_ hOVC
          (by
            rw [ovcWitness, if_pos h1, if_neg (fun hx => absurd (hw0.symm.trans hx) zero_ne_one)]
            exact IsEqualWordOperation.spec_populate C #v[65535, 65535, 65535, 65535] 1)
        intro i hi
        simp only [ProvableType.toElements_fromElements, Vector.getElem_map, Vector.getElem_mapRange,
        circuit_norm]
      · have hg0 : env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 4) = 0 := by
          rw [hSC4, h1, hw1]; norm_num
        rw [hg0]
        refine ⟨Or.inl rfl, ?_⟩
        refine SubSpecs.subSpec_eqWord env.toEnvironment
          (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11) _ _ _ _
          (ovcWitness input_is_real C F) ?_ hOVC
          (by
            rw [ovcWitness, if_pos h1, if_pos hw1]
            exact IsEqualWordOperation.spec_populate_offGate C #v[65535, 65535, 65535, 65535]
              #v[C[0], C[1], 0, 0] #v[65535, 65535, 0, 0] (rfl : (0 : ZMod p) = 0))
        intro i hi
        simp only [ProvableType.toElements_fromElements, Vector.getElem_map, Vector.getElem_mapRange,
        circuit_norm]
  case eqb2 =>
    simp only [heb0, heb1, hfl4, hfl5, hfl6, hfl7]
    rcases he2sum with hw0 | hw1
    · rw [hw0]
      refine ⟨Or.inl rfl, ?_⟩
      rcases hbin with h0 | h1
      · refine SubSpecs.subSpec_eqWord env.toEnvironment
          (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8) _ _ _ _
          (ovbWitness input_is_real B F) ?_ hOVB
          (by
            rw [ovbWitness, if_neg (fun hx => absurd (h0.symm.trans hx) zero_ne_one)]
            exact IsEqualWordOperation.spec_zero (#v[B[0], B[1], 0, 0] : Word (ZMod p))
              #v[0, 32768, 0, 0] (rfl : (0 : ZMod p) = 0))
        intro i hi
        simp only [ProvableType.toElements_fromElements, Vector.getElem_map, Vector.getElem_mapRange,
        circuit_norm]
      · refine SubSpecs.subSpec_eqWord env.toEnvironment
          (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8) _ _ _ _
          (ovbWitness input_is_real B F) ?_ hOVB
          (by
            rw [ovbWitness, if_pos h1, if_neg (fun hx => absurd (hw0.symm.trans hx) zero_ne_one)]
            exact IsEqualWordOperation.spec_populate_offGate
              (#v[B[0], B[1], 0, 0] : Word (ZMod p)) #v[0, 32768, 0, 0]
              B #v[0, 0, 0, 32768] (rfl : (0 : ZMod p) = 0))
        intro i hi
        simp only [ProvableType.toElements_fromElements, Vector.getElem_map, Vector.getElem_mapRange,
        circuit_norm]
    · have h1 : input_is_real = 1 := by
        rcases hbin with h0 | h1
        · obtain ⟨-, -, hF0⟩ := hpadvals h0
          rw [hF0] at hw1
          simp at hw1
        · exact h1
      rw [hw1]
      refine ⟨Or.inr rfl, ?_⟩
      refine SubSpecs.subSpec_eqWord env.toEnvironment
        (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8) _ _ _ _
        (ovbWitness input_is_real B F) ?_ hOVB
        (by
          rw [ovbWitness, if_pos h1, if_pos hw1]
          exact IsEqualWordOperation.spec_populate (#v[B[0], B[1], 0, 0] : Word (ZMod p))
            #v[0, 32768, 0, 0] 1)
      intro i hi
      simp only [ProvableType.toElements_fromElements, Vector.getElem_map, Vector.getElem_mapRange,
        circuit_norm]
  case eqc2 =>
    simp only [hec0, hec1, hfl4, hfl5, hfl6, hfl7]
    rcases he2sum with hw0 | hw1
    · rw [hw0]
      refine ⟨Or.inl rfl, ?_⟩
      rcases hbin with h0 | h1
      · refine SubSpecs.subSpec_eqWord env.toEnvironment
          (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11) _ _ _ _
          (ovcWitness input_is_real C F) ?_ hOVC
          (by
            rw [ovcWitness, if_neg (fun hx => absurd (h0.symm.trans hx) zero_ne_one)]
            exact IsEqualWordOperation.spec_zero (#v[C[0], C[1], 0, 0] : Word (ZMod p))
              #v[65535, 65535, 0, 0] (rfl : (0 : ZMod p) = 0))
        intro i hi
        simp only [ProvableType.toElements_fromElements, Vector.getElem_map, Vector.getElem_mapRange,
        circuit_norm]
      · refine SubSpecs.subSpec_eqWord env.toEnvironment
          (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11) _ _ _ _
          (ovcWitness input_is_real C F) ?_ hOVC
          (by
            rw [ovcWitness, if_pos h1, if_neg (fun hx => absurd (hw0.symm.trans hx) zero_ne_one)]
            exact IsEqualWordOperation.spec_populate_offGate
              (#v[C[0], C[1], 0, 0] : Word (ZMod p)) #v[65535, 65535, 0, 0]
              C #v[65535, 65535, 65535, 65535] (rfl : (0 : ZMod p) = 0))
        intro i hi
        simp only [ProvableType.toElements_fromElements, Vector.getElem_map, Vector.getElem_mapRange,
        circuit_norm]
    · have h1 : input_is_real = 1 := by
        rcases hbin with h0 | h1
        · obtain ⟨-, -, hF0⟩ := hpadvals h0
          rw [hF0] at hw1
          simp at hw1
        · exact h1
      rw [hw1]
      refine ⟨Or.inr rfl, ?_⟩
      refine SubSpecs.subSpec_eqWord env.toEnvironment
        (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11) _ _ _ _
        (ovcWitness input_is_real C F) ?_ hOVC
        (by
          rw [ovcWitness, if_pos h1, if_pos hw1]
          exact IsEqualWordOperation.spec_populate (#v[C[0], C[1], 0, 0] : Word (ZMod p))
            #v[65535, 65535, 0, 0] 1)
      intro i hi
      simp only [ProvableType.toElements_fromElements, Vector.getElem_map, Vector.getElem_mapRange,
        circuit_norm]
  case isc0 =>
    rw [hCvec]
    refine ⟨hbin, ?_⟩
    refine SubSpecs.subSpec_isZero env.toEnvironment
      (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11) _ _ _
      isc0Witness ?_ hISC0
      (by
        simp only [isc0Witness, isC0Witness]
        exact IsZeroWordOperation.spec_populate (cComp C F) input_is_real)
    intro i hi
    simp only [ProvableType.toElements_fromElements, Vector.getElem_map, Vector.getElem_mapRange,
        circuit_norm]
  case addc =>
    rw [hCvec, hABSCvec, hWCNEGvec, hMISC0]
    rcases hgcneg with hg0 | hg1
    · rw [hg0]
      exact ⟨⟨fun hx => absurd hx zero_ne_one, Or.inl rfl⟩, fun hx => absurd hx zero_ne_one⟩
    · rw [hg1]
      refine ⟨⟨fun _ => ⟨cComp_isU64 hcU F, populateAbsC_isU64 hcU F⟩, Or.inr rfl⟩, ?_⟩
      rw [show wCnegWitness input_is_real C F
          = AddOperation.populate (cComp C F) (populateAbsC C F) from by
        rw [wCnegWitness, if_pos hg1]]
      exact AddOperation.spec_populate (cComp_isU64 hcU F) (populateAbsC_isU64 hcU F) 1
  case addr =>
    rw [hRCvec, hABSRvec, hWRNEGvec, hMISC1]
    rcases hgrneg with hg0 | hg1
    · rw [hg0]
      exact ⟨⟨fun hx => absurd hx zero_ne_one, Or.inl rfl⟩, fun hx => absurd hx zero_ne_one⟩
    · rw [hg1]
      have h67 := flags67_eq_zero_of_remNeg_mul_eq_one B C input_is_real
        hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum hg1
      have hRCR : populateRemComp B C F = populateRemainder B C F := by
        unfold populateRemComp remCompBits populateRemainder
        rw [if_neg (fun hx => absurd (h67.symm.trans hx) zero_ne_one)]
      rw [hRCR]
      refine ⟨⟨fun _ => ⟨populateRemainder_isU64 B C F, populateAbsRem_isU64 B C F⟩,
        Or.inr rfl⟩, ?_⟩
      rw [show wRnegWitness input_is_real B C F
          = AddOperation.populate (populateRemainder B C F) (populateAbsRem B C F) from by
        rw [wRnegWitness, if_pos hg1]]
      exact AddOperation.spec_populate (populateRemainder_isU64 B C F)
        (populateAbsRem_isU64 B C F) 1
  case lt =>
    rw [hABSRvec, hMAXvec, hLTFvec, hLTCLvec, hNEI, hBIT, hMISC2]
    rcases hltgbool with hg0 | hg1
    · rw [hg0]
      refine ⟨⟨fun hx => absurd hx zero_ne_one, Or.inl rfl⟩, ?_⟩
      rw [show ltFlagsWitness input_is_real B C F = (#v[0, 0, 0, 0] : Vector (ZMod p) 4) from by
          rw [ltFlagsWitness, if_neg (fun hx => absurd (hg0.symm.trans hx) zero_ne_one)],
        show ltClWitness input_is_real B C F = (#v[0, 0] : Vector (ZMod p) 2) from by
          rw [ltClWitness, if_neg (fun hx => absurd (hg0.symm.trans hx) zero_ne_one)],
        show (ltNotEqInvWitness input_is_real B C F)[0] = 0 from by
          rw [ltNotEqInvWitness, if_neg (fun hx => absurd (hg0.symm.trans hx) zero_ne_one)]
          rfl,
        show (ltBitWitness input_is_real B C F)[0] = 0 from by
          rw [ltBitWitness, if_neg (fun hx => absurd (hg0.symm.trans hx) zero_ne_one)]
          rfl]
      exact LtOperationUnsigned.spec_zero (populateAbsRem B C F) (populateMaxAbsCOr1 C F) rfl
    · rw [hg1]
      refine ⟨⟨fun _ => ⟨populateAbsRem_isU64 B C F, populateMaxAbsCOr1_isU64 hcU F⟩,
        Or.inr rfl⟩, ?_⟩
      rw [show ltClWitness input_is_real B C F
          = LtOperationUnsigned.comparisonLimbsWitness (populateAbsRem B C F)
              (populateMaxAbsCOr1 C F) from by
          rw [ltClWitness, if_pos hg1],
        show ltFlagsWitness input_is_real B C F
          = LtOperationUnsigned.flagsWitness (populateAbsRem B C F)
              (populateMaxAbsCOr1 C F) from by
          rw [ltFlagsWitness, if_pos hg1],
        show (ltNotEqInvWitness input_is_real B C F)[0]
          = (LtOperationUnsigned.notEqInvWitness (populateAbsRem B C F)
              (populateMaxAbsCOr1 C F))[0] from by
          rw [ltNotEqInvWitness, if_pos hg1],
        show (ltBitWitness input_is_real B C F)[0]
          = U16CompareOperation.populate_bit
              (LtOperationUnsigned.comparisonLimbsWitness (populateAbsRem B C F)
                (populateMaxAbsCOr1 C F))[0]
              (LtOperationUnsigned.comparisonLimbsWitness (populateAbsRem B C F)
                (populateMaxAbsCOr1 C F))[1] from by
          rw [ltBitWitness, if_pos hg1, ltClWitness, if_pos hg1]
          rfl]
      exact LtOperationUnsigned.spec_populate
  case msb0 =>
    exact ⟨⟨fun _ => by rw [heb3]; exact hbU3, hirnwbin⟩,
      by rw [hBM]; exact bMsbCell_bool hbU F,
      fun hg => by
        obtain ⟨h1, hw0⟩ := hirnw_cases hg
        rw [hBM, heb3, bMsbCell, if_neg (fun hx => absurd (hw0.symm.trans hx) zero_ne_one)]
        exact (U16MSBOperation.spec_populate hbU3 1).2 rfl⟩
  case msb1 =>
    exact ⟨⟨fun _ => by rw [hec3]; exact hcU3, hirnwbin⟩,
      by rw [hCM]; exact cMsbCell_bool hcU F,
      fun hg => by
        obtain ⟨h1, hw0⟩ := hirnw_cases hg
        rw [hCM, hec3, cMsbCell, if_neg (fun hx => absurd (hw0.symm.trans hx) zero_ne_one)]
        exact (U16MSBOperation.spec_populate hcU3 1).2 rfl⟩
  case msb2 =>
    exact ⟨⟨fun _ => by rw [hREM3]; exact hRb3, hirnwbin⟩,
      by rw [hRM]; exact remMsbCell_bool B C F,
      fun hg => by
        obtain ⟨h1, hw0⟩ := hirnw_cases hg
        rw [hRM, hREM3, remMsbCell, if_neg (fun hx => absurd (hw0.symm.trans hx) zero_ne_one)]
        exact (U16MSBOperation.spec_populate hRb3 1).2 rfl⟩
  case msb3 =>
    exact ⟨⟨fun _ => by rw [heb1]; exact hbU1, hE2bin⟩,
      by rw [hBM]; exact bMsbCell_bool hbU F,
      fun hg => by
        have hw1 := hE2_one hg
        rw [hBM, heb1, bMsbCell, if_pos hw1]
        exact (U16MSBOperation.spec_populate hbU1 1).2 rfl⟩
  case msb4 =>
    exact ⟨⟨fun _ => by rw [hec1]; exact hcU1, hE2bin⟩,
      by rw [hCM]; exact cMsbCell_bool hcU F,
      fun hg => by
        have hw1 := hE2_one hg
        rw [hCM, hec1, cMsbCell, if_pos hw1]
        exact (U16MSBOperation.spec_populate hcU1 1).2 rfl⟩
  case msb5 =>
    exact ⟨⟨fun _ => by rw [hREM1]; exact hRb1, hE2bin⟩,
      by rw [hRM]; exact remMsbCell_bool B C F,
      fun hg => by
        have hw1 := hE2_one hg
        rw [hRM, hREM1, remMsbCell, if_pos hw1]
        exact (U16MSBOperation.spec_populate hRb1 1).2 rfl⟩
  case msb6 =>
    exact ⟨⟨fun _ => by rw [hQUOT1]; exact hQb1, hE2bin⟩,
      by rw [hQM]; exact quotMsbCell_bool B C F,
      fun hg => by
        have hw1 := hE2_one hg
        rw [hQM, hQUOT1, quotMsbCell, if_pos hw1]
        exact (U16MSBOperation.spec_populate hQb1 1).2 rfl⟩
  case pabsc0 => exact BytePulls.bytePullSimple hABSC0 hACb0
  case pabsc1 => exact BytePulls.bytePullSimple hABSC1 hACb1
  case pabsc2 => exact BytePulls.bytePullSimple hABSC2 hACb2
  case pabsc3 => exact BytePulls.bytePullSimple hABSC3 hACb3
  case pabsr0 => exact BytePulls.bytePullSimple hABSR0 hARb0
  case pabsr1 => exact BytePulls.bytePullSimple hABSR1 hARb1
  case pabsr2 => exact BytePulls.bytePullSimple hABSR2 hARb2
  case pabsr3 => exact BytePulls.bytePullSimple hABSR3 hARb3
  case pq0 => exact BytePulls.bytePullSimple hQUOT0 hQb0
  case pq1 => exact BytePulls.bytePullSimple hQUOT1 hQb1
  case pq2 => exact BytePulls.bytePullSimple hQUOT2 hQb2
  case pq3 => exact BytePulls.bytePullSimple hQUOT3 hQb3
  case pr0 => exact BytePulls.bytePullSimple hREM0 hRb0
  case pr1 => exact BytePulls.bytePullSimple hREM1 hRb1
  case pr2 => exact BytePulls.bytePullSimple hREM2 hRb2
  case pr3 => exact BytePulls.bytePullSimple hREM3 hRb3
  case pctq0 => exact BytePulls.bytePullSimple hCTQ0 (populateCtq_val_lt B C F 0 (by norm_num))
  case pctq1 => exact BytePulls.bytePullSimple hCTQ1 (populateCtq_val_lt B C F 1 (by norm_num))
  case pctq2 => exact BytePulls.bytePullSimple hCTQ2 (populateCtq_val_lt B C F 2 (by norm_num))
  case pctq3 => exact BytePulls.bytePullSimple hCTQ3 (populateCtq_val_lt B C F 3 (by norm_num))
  case pctq4 => exact BytePulls.bytePullSimple hCTQ4 (populateCtq_val_lt B C F 4 (by norm_num))
  case pctq5 => exact BytePulls.bytePullSimple hCTQ5 (populateCtq_val_lt B C F 5 (by norm_num))
  case pctq6 => exact BytePulls.bytePullSimple hCTQ6 (populateCtq_val_lt B C F 6 (by norm_num))
  case pctq7 => exact BytePulls.bytePullSimple hCTQ7 (populateCtq_val_lt B C F 7 (by norm_num))
  case pe2r1 => exact BytePulls.bytePullSimple hREM1 hRb1
  case pe2q1 => exact BytePulls.bytePullSimple hQUOT1 hQb1
  case own =>
    -- the three `IsEqual`/`IsZero` struct-result pins (eOVBR/eOVCR/eISC0): rebuild each sub-op `cols`
    -- block from its `toElements` pin (`hOVB`/`hOVC`/`hISC0`) via `fromElements`, then project the
    -- result field (the `hSML`→`hPL0` recipe). Supplied inline so the goal provides the column struct.
    simp only [assertZeros, forAllNoOffset_map_assert]
    exact ownAsserts_complete env.toEnvironment _ input_is_real B C F
      hbU hcU hbin hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum hsr
      hfl0 hfl1 hfl2 hfl3 hfl4 hfl5 hfl6 hfl7
      h_input.1 hSC4 hOV hBN hBNNO hBNNNO hREMNEG hCN hMISC0 hMISC1 hMISC2
      hBM hCM hRM hQM
      hBvec hCvec hQvec hQCvec hRvec hRCvec hAvec hABSCvec hABSRvec hMAXvec hCTQvecW hCARRYvecW
      hWCNEGvec hWRNEGvec hbpv hcpv
      (by
        have hS : (ProvableType.fromElements (M := Extracted.IsEqualWordOperation)
              (Vector.mapRange 11 fun j =>
                env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + j)))
            = ovbWitness input_is_real B F := by
          refine (ProvableType.ext_iff _ _).mpr fun i hi => ?_
          rw [ProvableType.toElements_fromElements]
          exact (Vector.getElem_mapRange i hi).trans (hOVB ⟨i, hi⟩)
        rw [← hS]
        simp only [iseqword_result_proj, circuit_norm])
      (by
        have hS : (ProvableType.fromElements (M := Extracted.IsEqualWordOperation)
              (Vector.mapRange 11 fun j =>
                env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + j)))
            = ovcWitness input_is_real C F := by
          refine (ProvableType.ext_iff _ _).mpr fun i hi => ?_
          rw [ProvableType.toElements_fromElements]
          exact (Vector.getElem_mapRange i hi).trans (hOVC ⟨i, hi⟩)
        rw [← hS]
        simp only [iseqword_result_proj, circuit_norm])
      (by
        have hS : (ProvableType.fromElements (M := Extracted.IsZeroWordOperation)
              (Vector.mapRange 11 fun j =>
                env.get (i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + j)))
            = isc0Witness := by
          refine (ProvableType.ext_iff _ _).mpr fun i hi => ?_
          rw [ProvableType.toElements_fromElements]
          have hi' : i < 11 := by simpa only [circuit_norm] using hi
          simpa only [Vector.getElem_cast] using
            (Vector.getElem_mapRange i hi).trans (hISC0 ⟨i, hi'⟩)
        rw [← hS]
        simp only [isc0Witness, iszeroword_result_proj, circuit_norm])
      hBIT
      ((h_input.2.2.2.2.1).trans hop_a_0)
  case pe123 =>
    refine fun _ => ?_
    have hcr := chain_residue_field_0 B C F
    try push_cast at hcr
    rw [hCTQ0, hRC0, hCARRY0, ← sub_eq_add_neg, hcr]
    convert byteRow_range16 (chainResidue_field_val_lt B C F 0) using 2
  case pe127 =>
    refine fun _ => ?_
    have hcr := chain_residue_field_1 B C F
    try push_cast at hcr
    rw [hCTQ1, hRC1, hCARRY1, hCARRY0, ← sub_eq_add_neg, hcr]
    convert byteRow_range16 (chainResidue_field_val_lt B C F 1) using 2
  case pe131 =>
    refine fun _ => ?_
    have hcr := chain_residue_field_2 B C F
    try push_cast at hcr
    rw [hCTQ2, hRC2, hCARRY2, hCARRY1, ← sub_eq_add_neg, hcr]
    convert byteRow_range16 (chainResidue_field_val_lt B C F 2) using 2
  case pe135 =>
    refine fun _ => ?_
    have hcr := chain_residue_field_3 B C F
    try push_cast at hcr
    rw [hCTQ3, hRC3, hCARRY3, hCARRY2, ← sub_eq_add_neg, hcr]
    convert byteRow_range16 (chainResidue_field_val_lt B C F 3) using 2
  case pe139 =>
    refine fun _ => ?_
    have hcr := chain_residue_field_4 B C F
    try push_cast at hcr
    rw [hCTQ4, hREMNEG, hCARRY4, hCARRY3, ← sub_eq_add_neg, hcr]
    convert byteRow_range16 (chainResidue_field_val_lt B C F 4) using 2
  case pe143 =>
    refine fun _ => ?_
    have hcr := chain_residue_field_5 B C F
    try push_cast at hcr
    rw [hCTQ5, hREMNEG, hCARRY5, hCARRY4, ← sub_eq_add_neg, hcr]
    convert byteRow_range16 (chainResidue_field_val_lt B C F 5) using 2
  case pe147 =>
    refine fun _ => ?_
    have hcr := chain_residue_field_6 B C F
    try push_cast at hcr
    rw [hCTQ6, hREMNEG, hCARRY6, hCARRY5, ← sub_eq_add_neg, hcr]
    convert byteRow_range16 (chainResidue_field_val_lt B C F 6) using 2
  case pe151 =>
    refine fun _ => ?_
    have hcr := chain_residue_field_7 B C F
    try push_cast at hcr
    rw [hCTQ7, hREMNEG, hCARRY7, hCARRY6, ← sub_eq_add_neg, hcr]
    convert byteRow_range16 (chainResidue_field_val_lt B C F 7) using 2
  -/

end SP1Clean.DivRemChip
