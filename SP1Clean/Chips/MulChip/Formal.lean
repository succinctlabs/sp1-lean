import SP1Clean.Chips.MulChip.Defs

/-! # `SP1Clean.MulChip` — `Assumptions` / soundness / completeness / `circuit` -/

namespace SP1Clean.MulChip

open Circuit
open Extracted (MulCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- Operands are 64-bit values (true on real and zero-padded rows). -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val

/-- Prover-side row well-formedness, with the reader column blocks as *threaded inputs* (mirrors
`AddChip.ProverAssumptions`): the operand `isU64`s, the `is_real` binary selector, the `op_a_0 = 0`
flag, and the `is_real`-gated CPUState clock bounds + per-operand register-access timestamp bounds
(the verifier commits a well-formed clock/timestamp row). Soundness never assumes these. -/
def ProverAssumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p))
    (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  input.adapter.op_a_0 = 0 ∧
  Readers.CPUState.Spec
    { cols := input.state, next_pc := #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
      clk_inc := 8, is_real := input.is_real } ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_a_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_b_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 3⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_c_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 2⟩

theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hbU, hcU⟩ := h_assumptions
  obtain ⟨_hcpu, h_mulop, ha0, ha1, ha2, ha3, gb_mul, gb_mulh, gb_mulhu, gb_mulhsu, gb_mulw,
    gb_sum, hopa0, hadapter, h_gate⟩ := h_holds
  have bmul := bool_of_mul_pred gb_mul
  have bmulh := bool_of_mul_pred gb_mulh
  have bmulhu := bool_of_mul_pred gb_mulhu
  have bmulhsu := bool_of_mul_pred gb_mulhsu
  have bmulw := bool_of_mul_pred gb_mulw
  have bsum := bool_of_mul_pred gb_sum
  have h_bin := bool_of_mul_pred h_gate
  -- `is_mulw = 1 → is_real = 1` (gate = flag-sum, SP1 `alu/mul/mod.rs:234`): one-hot via `sum_eq_one`.
  -- Required precondition for `MulOperation`.
  have h_mw := fun (hmw : (env.get (i₀ + 4) : ZMod p) = 1) =>
    MulOperation.sum_eq_one bmul bmulh bmulhu bmulhsu bmulw bsum (Or.inr (Or.inr (Or.inr (Or.inr hmw))))
  -- `MulOperation.Assumptions` (operands `isU64` when active; flag binaries; `is_mulw → is_real`; sum-bound).
  have h_spec := h_mulop ⟨fun _ => ⟨hbU, hcU⟩, bsum, h_mw, bmul, bmulh, bmulhu, bmulhsu, bmulw, bsum⟩
  refine ⟨⟨hadapter h_bin, h_bin, fun hr => ⟨?_, ?_, ?_, ?_, ?_⟩⟩, Or.inr h_bin,
    Or.inr ⟨fun _ => ⟨hbU, hcU⟩, bsum, h_mw, bmul, bmulh, bmulhu, bmulhsu, bmulw, bsum⟩, Or.inr h_bin⟩
  · intro h1
    have hsum1 := MulOperation.sum_eq_one bmul bmulh bmulhu bmulhsu bmulw bsum (Or.inl h1)
    obtain ⟨_hisU64, hmul, _hmulhu, _hmulh, _hmulhsu, _hmulw⟩ :=
      MulOperation.result_semantic ⟨fun _ => ⟨hbU, hcU⟩, bsum, h_mw, bmul, bmulh, bmulhu, bmulhsu, bmulw, bsum⟩ h_spec hsum1
    rw [rv64_mul_eq, ← hmul h1]; congr 1
    rw [← MulOperation.aSelector_eq_resultWord _ _ bmul bmulh bmulhu bmulhsu bmulw hsum1]
    apply Vector.ext; intro k hk; interval_cases k <;>
      simp only [MulOperation.aSelector, MulOperation.productVal, Vector.getElem_map,
        Vector.getElem_mapRange, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, Nat.reduceLT, dif_pos] <;>
      first | exact ha0 | exact ha1 | exact ha2 | exact ha3
  · intro h1
    have hsum1 := MulOperation.sum_eq_one bmul bmulh bmulhu bmulhsu bmulw bsum (Or.inr (Or.inl h1))
    obtain ⟨_hisU64, _hmul, _hmulhu, hmulh, _hmulhsu, _hmulw⟩ :=
      MulOperation.result_semantic ⟨fun _ => ⟨hbU, hcU⟩, bsum, h_mw, bmul, bmulh, bmulhu, bmulhsu, bmulw, bsum⟩ h_spec hsum1
    rw [rv64_mulh_eq, ← hmulh h1]; congr 1
    rw [← MulOperation.aSelector_eq_resultWord _ _ bmul bmulh bmulhu bmulhsu bmulw hsum1]
    apply Vector.ext; intro k hk; interval_cases k <;>
      simp only [MulOperation.aSelector, MulOperation.productVal, Vector.getElem_map,
        Vector.getElem_mapRange, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, Nat.reduceLT, dif_pos] <;>
      first | exact ha0 | exact ha1 | exact ha2 | exact ha3
  · intro h1
    have hsum1 := MulOperation.sum_eq_one bmul bmulh bmulhu bmulhsu bmulw bsum (Or.inr (Or.inr (Or.inl h1)))
    obtain ⟨_hisU64, _hmul, hmulhu, _hmulh, _hmulhsu, _hmulw⟩ :=
      MulOperation.result_semantic ⟨fun _ => ⟨hbU, hcU⟩, bsum, h_mw, bmul, bmulh, bmulhu, bmulhsu, bmulw, bsum⟩ h_spec hsum1
    rw [rv64_mulhu_eq, ← hmulhu h1]; congr 1
    rw [← MulOperation.aSelector_eq_resultWord _ _ bmul bmulh bmulhu bmulhsu bmulw hsum1]
    apply Vector.ext; intro k hk; interval_cases k <;>
      simp only [MulOperation.aSelector, MulOperation.productVal, Vector.getElem_map,
        Vector.getElem_mapRange, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, Nat.reduceLT, dif_pos] <;>
      first | exact ha0 | exact ha1 | exact ha2 | exact ha3
  · intro h1
    have hsum1 := MulOperation.sum_eq_one bmul bmulh bmulhu bmulhsu bmulw bsum (Or.inr (Or.inr (Or.inr (Or.inl h1))))
    obtain ⟨_hisU64, _hmul, _hmulhu, _hmulh, hmulhsu, _hmulw⟩ :=
      MulOperation.result_semantic ⟨fun _ => ⟨hbU, hcU⟩, bsum, h_mw, bmul, bmulh, bmulhu, bmulhsu, bmulw, bsum⟩ h_spec hsum1
    rw [rv64_mulhsu_eq, ← hmulhsu h1]; congr 1
    rw [← MulOperation.aSelector_eq_resultWord _ _ bmul bmulh bmulhu bmulhsu bmulw hsum1]
    apply Vector.ext; intro k hk; interval_cases k <;>
      simp only [MulOperation.aSelector, MulOperation.productVal, Vector.getElem_map,
        Vector.getElem_mapRange, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, Nat.reduceLT, dif_pos] <;>
      first | exact ha0 | exact ha1 | exact ha2 | exact ha3
  · intro h1
    have hsum1 := MulOperation.sum_eq_one bmul bmulh bmulhu bmulhsu bmulw bsum (Or.inr (Or.inr (Or.inr (Or.inr h1))))
    obtain ⟨_hisU64, _hmul, _hmulhu, _hmulh, _hmulhsu, hmulw⟩ :=
      MulOperation.result_semantic ⟨fun _ => ⟨hbU, hcU⟩, bsum, h_mw, bmul, bmulh, bmulhu, bmulhsu, bmulw, bsum⟩ h_spec hsum1
    rw [rv64_mulw_eq, ← hmulw h1]; congr 1
    rw [← MulOperation.aSelector_eq_resultWord _ _ bmul bmulh bmulhu bmulhsu bmulw hsum1]
    apply Vector.ext; intro k hk; interval_cases k <;>
      simp only [MulOperation.aSelector, MulOperation.productVal, Vector.getElem_map,
        Vector.getElem_mapRange, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, Nat.reduceLT, dif_pos] <;>
      first | exact ha0 | exact ha1 | exact ha2 | exact ha3

set_option linter.unusedSectionVars false in
/-- A length-4 `#v` of pointwise evaluations is the `Vector.map` of the evaluator (folds the witness
hint's `populate` operands, written `#v[env op_*_val[k]]` by the generator, back to `Vector.map`;
mirrors `LtChip.vec4_eval`). -/
private lemma vec4_eval (e : Environment (ZMod p)) (v : Vector (Expression (ZMod p)) 4) :
    (#v[Expression.eval e v[0], Expression.eval e v[1], Expression.eval e v[2],
        Expression.eval e v[3]] : Vector (ZMod p) 4) = Vector.map (Expression.eval e) v := by
  ext k hk
  interval_cases k <;> simp [Vector.getElem_map]

set_option maxHeartbeats 40000000 in
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨hbU, hcU, hbin, hop_a_0, h_cpu, hrac_a, hrac_b, hrac_c⟩ := h_assumptions
  obtain ⟨h_env_flags, h_env_cols, h_env_a⟩ := h_env
  obtain ⟨-, ⟨-, -, -, hpc⟩, -, -, -, -, ⟨hob, -, -⟩, -, hoc, -, -⟩ := h_input
  -- the five variant flags are witnessed `0` (padding-default hint)
  have hflag0 : env.get i₀ = 0 := by simpa using h_env_flags 0
  have hflag1 : env.get (i₀ + 1) = 0 := by simpa using h_env_flags 1
  have hflag2 : env.get (i₀ + 2) = 0 := by simpa using h_env_flags 2
  have hflag3 : env.get (i₀ + 3) = 0 := by simpa using h_env_flags 3
  have hflag4 : env.get (i₀ + 4) = 0 := by simpa using h_env_flags 4
  have hsum0 : env.get i₀ + env.get (i₀ + 1) + env.get (i₀ + 2) + env.get (i₀ + 3)
      + env.get (i₀ + 4) = 0 := by
    rw [hflag0, hflag1, hflag2, hflag3, hflag4]; simp
  have epc0 : Expression.eval env.toEnvironment input_var_state_pc[0] = input_state_pc[0] := by
    rw [← hpc, Vector.getElem_map]
  have epc1 : Expression.eval env.toEnvironment input_var_state_pc[1] = input_state_pc[1] := by
    rw [← hpc, Vector.getElem_map]
  have epc2 : Expression.eval env.toEnvironment input_var_state_pc[2] = input_state_pc[2] := by
    rw [← hpc, Vector.getElem_map]
  have hz : ∀ w : ZMod p, input_adapter_op_a_0 * w = 0 := fun w => by rw [hop_a_0, zero_mul]
  -- fold the witness hint's `populate` operands to the evaluated input words
  simp only [Inputs.op_b_val, Inputs.op_c_val, vec4_eval, hob, hoc] at h_env_cols
  refine ⟨⟨hbin, by rw [← epc0, ← epc1, ← epc2] at h_cpu; exact h_cpu⟩,
    ⟨⟨fun _ => ⟨hbU, hcU⟩, Or.inl hsum0,
      fun h => absurd (hflag4.symm.trans h) zero_ne_one,
      Or.inl hflag0, Or.inl hflag1, Or.inl hflag2, Or.inl hflag3, Or.inl hflag4, Or.inl hsum0⟩, ?_⟩,
    by simpa using h_env_a 0, by simpa using h_env_a 1,
    by simpa using h_env_a 2, by simpa using h_env_a 3,
    by rw [hflag0]; simp, by rw [hflag1]; simp, by rw [hflag2]; simp, by rw [hflag3]; simp,
    by rw [hflag4]; simp, by rw [hsum0]; simp, hop_a_0,
    ⟨hbin, ⟨hz _, hz _, hz _, hz _⟩, Or.inl hop_a_0, hrac_a, hrac_b, hrac_c⟩, ?_⟩
  · -- the composed `MulOperation` `FormalAssertion`'s `Spec` at the witnessed `populate`d columns:
    -- `spec_populate` once the witnessed column struct equals `populate …` (each cell is
    -- `env.get (i₀+5+k)`, pinned by the normalised witness hint to `(toElements (populate …))[k]`).
    convert MulOperation.spec_populate (b := input_adapter_op_b_memory_prev_value)
      (c := input_adapter_op_c_memory_prev_value) hbU hcU
      (env.get i₀) (env.get (i₀ + 1)) (env.get (i₀ + 2)) (env.get (i₀ + 3)) (env.get (i₀ + 4))
      (env.get i₀ + env.get (i₀ + 1) + env.get (i₀ + 2) + env.get (i₀ + 3) + env.get (i₀ + 4))
      (Or.inl hflag0) (Or.inl hflag1) (Or.inl hflag2) (Or.inl hflag3) (Or.inl hflag4)
      (Or.inl hsum0) using 2
    refine (ProvableType.ext_iff _ _).mpr (fun i hi => ?_)
    refine Eq.trans ?_
      ((getElem_toElements_eval_varFromOffset env.toEnvironment (i₀ + 5) i hi).trans
        (h_env_cols ⟨i, hi⟩))
    simp [circuit_norm]
  · rcases hbin with h | h <;> rw [h] <;> simp

/-- The `Mul` chip row as a `GeneralFormalCircuit`: flag-gated RV64 `mul`/`mulh`/`mulhu`/`mulhsu`/`mulw`
semantic contract; output is the extracted `MulCols` column struct. Soundness/completeness are proven
and axiom-clean (completeness via `MulOperation.spec_populate` on the witnessed columns). -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs MulCols :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness }

end SP1Clean.MulChip
