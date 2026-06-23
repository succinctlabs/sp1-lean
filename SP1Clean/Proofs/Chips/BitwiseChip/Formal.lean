import SP1Clean.Native.Chips.BitwiseChip.Defs

/-! # `SP1Clean.BitwiseChip` — contract: `Assumptions` / soundness / completeness / `circuit`

Semantic `Spec` (binary ∧ flag-gated `RV64.and`/`or`/`xor`), soundness (keyed on `one_hot3`
selector lemma — each opcode branch is a self-contained local argument), completeness, and the
bundled `circuit`. -/

namespace SP1Clean.BitwiseChip

open Circuit
open Extracted (BitwiseCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Operands are 64-bit values; `is_real`-binary is proven from the in-circuit gate (so it lives in
`Spec`), not assumed. The operands resolve via the adapter projections (`Inputs.op_b_val`/`op_c_val`). -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val

/-- Prover-side row well-formedness: operand `isU64`s, `is_real` binary, the honest
`"bitwise_flags"` hint (each flag binary, one-hot, the sum = `is_real`), `op_a_0 = 0`,
`imm_c = 0` (register-register ops), CPUState clock bounds, three timestamp `Spec`s
(op_c gated by `is_real - imm_c`). -/
def ProverAssumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) : Prop :=
  let f := hintFlags hint
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (f[0] = 0 ∨ f[0] = 1) ∧ (f[1] = 0 ∨ f[1] = 1) ∧ (f[2] = 0 ∨ f[2] = 1) ∧
  input.is_real = f[0] + f[1] + f[2] ∧
  (f[0] = 1 → f[1] = 0 ∧ f[2] = 0) ∧
  (f[1] = 1 → f[0] = 0 ∧ f[2] = 0) ∧
  (f[2] = 1 → f[0] = 0 ∧ f[1] = 0) ∧
  input.adapter.op_a_0 = 0 ∧ input.adapter.imm_c = 0 ∧
  Readers.CPUState.Spec
    { cols := input.state, next_pc := #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
      clk_inc := 8, is_real := input.is_real } ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_a_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_b_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 3⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_c_memory, input.is_real - input.adapter.imm_c,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 2⟩

/-- Proven `is_real`-binary + `is_real`/flag-gated RV64 identity on the result word. Vacuous on
padding. Cross-row bus guarantees live at the trace level and are not re-exposed here. -/
def Spec (input : Inputs (ZMod p)) (cols : BitwiseCols (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (input.is_real = 1 →
    (cols.is_and = 1 →
      Word.toBitVec64 (resultWord cols)
        = RV64.and (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)) ∧
    (cols.is_or = 1 →
      Word.toBitVec64 (resultWord cols)
        = RV64.or (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)) ∧
    (cols.is_xor = 1 →
      Word.toBitVec64 (resultWord cols)
        = RV64.xor (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)))

/-- One-hot lemma for the three opcode selectors: given each selector is binary and their sum is binary
(`E1 = is_xor + is_or + is_and` with `E9 = E1·(E1-1) = 0`), whichever selector is `1` forces the other
two to `0`. The sum-bound rules out two-or-three-hot via `2 ≠ 0` / `6 ≠ 0` in `ZMod p` (`p > 2^17`). -/
private lemma one_hot3 {x o a : ZMod p}
    (hx : x = 0 ∨ x = 1) (ho : o = 0 ∨ o = 1) (ha : a = 0 ∨ a = 1)
    (hsum : (x + o + a) * (x + o + a + -1) = 0) :
    (x = 1 → o = 0 ∧ a = 0) ∧ (o = 1 → x = 0 ∧ a = 0) ∧ (a = 1 → x = 0 ∧ o = 0) := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : Fact (1 < p) := ⟨by omega⟩
  have hne : ∀ k : ℕ, 0 < k → k < p → ((k : ℕ) : ZMod p) ≠ 0 := fun k hk hkp => by
    rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]; intro hd
    exact absurd (Nat.le_of_dvd hk hd) (by omega)
  have h2 : (2 : ZMod p) ≠ 0 := by simpa using hne 2 (by norm_num) (by omega)
  have h6 : (6 : ZMod p) ≠ 0 := by simpa using hne 6 (by norm_num) (by omega)
  rcases hx with rfl | rfl <;> rcases ho with rfl | rfl <;> rcases ha with rfl | rfl <;>
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    first
      | exact ⟨rfl, rfl⟩
      | exact absurd h.symm one_ne_zero
      | (exfalso; apply h2; linear_combination hsum)
      | (exfalso; apply h6; linear_combination hsum)

/-- The byte opcode `is_xor·2 + is_or·1 + is_and·0` lands in `{0,1,2}` (one-hot), so its `val < 3` —
the operand-range part of the composed `BitwiseU16Operation.circuit`'s `Assumptions`. -/
private lemma val_lt_three {x : ZMod p} (h : x = 0 ∨ x = 1 ∨ x = 2) : x.val < 3 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  rcases h with rfl | rfl | rfl
  · simp
  · rw [ZMod.val_one]; omega
  · rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_cast, ZMod.val_natCast_of_lt hp]; omega

set_option maxHeartbeats 2000000 in
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start [Spec]
  haveI hF1 : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨ha, hb⟩ := h_assumptions
  obtain ⟨_h_cpu, h_bw, _h_adapter, h_gate, h_xor_bin, h_or_bin, h_and_bin, h_sum, _h_opa0⟩ := h_holds
  have h_bin := bool_of_mul_pred h_gate
  have h_xor_bool := bool_of_mul_pred h_xor_bin
  have h_or_bool := bool_of_mul_pred h_or_bin
  have h_and_bool := bool_of_mul_pred h_and_bin
  have hoh := one_hot3 h_xor_bool h_or_bool h_and_bool h_sum
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hop3 : (env.get i₀ * 2 + env.get (i₀ + 1) * 1 + env.get (i₀ + 2) * 0).val < 3 :=
    val_lt_three <| by
      rcases h_xor_bool with hx | hx
      · rcases h_or_bool with ho | ho
        · exact Or.inl (by rw [hx, ho]; ring)
        · exact Or.inr (Or.inl (by rw [hx, ho]; ring))
      · obtain ⟨ho, _⟩ := hoh.1 hx
        exact Or.inr (Or.inr (by rw [hx, ho]; ring))
  -- once the active flag forces the others to 0, the byte opcode reduces to a literal
  refine ⟨⟨h_bin, fun hr => ⟨fun hand => ?_, fun hor => ?_, fun hxor => ?_⟩⟩,
    Or.inr h_bin, Or.inr ⟨ha, hb, hop3, h_bin⟩, Or.inr h_bin⟩
  · obtain ⟨hx0, ho0⟩ := hoh.2.2 hand
    have hopc : env.get i₀ * 2 + env.get (i₀ + 1) * 1 + env.get (i₀ + 2) * 0 = 0 := by
      rw [hx0, ho0]; ring
    exact (BitwiseU16Operation.result_semantic _ hr
      (h_bw ⟨ha, hb, by rw [hopc, ZMod.val_zero]; omega, h_bin⟩)).1 hopc
  · obtain ⟨hx0, _ha0⟩ := hoh.2.1 hor
    have hopc : env.get i₀ * 2 + env.get (i₀ + 1) * 1 + env.get (i₀ + 2) * 0 = 1 := by
      rw [hx0, hor]; ring
    exact (BitwiseU16Operation.result_semantic _ hr
      (h_bw ⟨ha, hb, by rw [hopc, ZMod.val_one]; omega, h_bin⟩)).2.1 hopc
  · obtain ⟨ho0, _ha0⟩ := hoh.1 hxor
    have hopc : env.get i₀ * 2 + env.get (i₀ + 1) * 1 + env.get (i₀ + 2) * 0 = 2 := by
      rw [hxor, ho0]; ring
    exact (BitwiseU16Operation.result_semantic _ hr
      (h_bw ⟨ha, hb, by rw [hopc]; exact val_lt_three (Or.inr (Or.inr rfl)), h_bin⟩)).2.2 hopc

set_option linter.unusedSectionVars false in
/-- A length-4 `#v` of pointwise evaluations is the `Vector.map` of the evaluator — lets the witness
hint's `populate` operands (written `#v[env op_b_val[k]]` by the generator) be rewritten to the
`Vector.map eval …` form that `h_input` provides. -/
private lemma vec4_eval (e : Environment (ZMod p)) (v : Vector (Expression (ZMod p)) 4) :
    (#v[Expression.eval e v[0], Expression.eval e v[1], Expression.eval e v[2],
        Expression.eval e v[3]] : Vector (ZMod p) 4) = Vector.map (Expression.eval e) v := by
  ext k hk
  interval_cases k <;> simp [Vector.getElem_map]

set_option maxHeartbeats 8000000 in
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨ha, hb, hbin, hf0, hf1, hf2, hsum, hone0, hone1, hone2, hop_a_0, himm, h_cpu,
    hrac_a, hrac_b, hrac_c⟩ := h_assumptions
  obtain ⟨h_env_flags, h_env_cols⟩ := h_env
  have hflag0 : env.get i₀ = (hintFlags env.hint)[0] := by simpa using h_env_flags 0
  have hflag1 : env.get (i₀ + 1) = (hintFlags env.hint)[1] := by simpa using h_env_flags 1
  have hflag2 : env.get (i₀ + 2) = (hintFlags env.hint)[2] := by simpa using h_env_flags 2
  have hf0' : env.get i₀ = 0 ∨ env.get i₀ = 1 := by rw [hflag0]; exact hf0
  have hf1' : env.get (i₀ + 1) = 0 ∨ env.get (i₀ + 1) = 1 := by rw [hflag1]; exact hf1
  have hf2' : env.get (i₀ + 2) = 0 ∨ env.get (i₀ + 2) = 1 := by rw [hflag2]; exact hf2
  have hsumc : env.get i₀ + env.get (i₀ + 1) + env.get (i₀ + 2) = input_is_real := by
    rw [hflag0, hflag1, hflag2]; exact hsum.symm
  have hsum01' : env.get i₀ + env.get (i₀ + 1) + env.get (i₀ + 2) = 0
      ∨ env.get i₀ + env.get (i₀ + 1) + env.get (i₀ + 2) = 1 := by
    rw [hsumc]; exact hbin
  have hbool : ∀ x : ZMod p, x = 0 ∨ x = 1 → x * (x + -1) = 0 := by
    rintro x (h | h) <;> rw [h] <;> simp
  have hz : ∀ w : ZMod p, input_adapter_op_a_0 * w = 0 := fun w => by rw [hop_a_0, zero_mul]
  -- The witness hint computed `populate` at the *eval-of-var* operands; `h_input` identifies those with
  -- the value-form operands, normalising the hint's `populate` to match `spec_populate`.
  have hpvb : Vector.map (Expression.eval env.toEnvironment) input_var_adapter_op_b_memory_prev_value
      = input_adapter_op_b_memory_prev_value := h_input.2.2.2.2.2.2.1.1
  have hpvc : Vector.map (Expression.eval env.toEnvironment) input_var_adapter_op_c_memory_prev_value
      = input_adapter_op_c_memory_prev_value := h_input.2.2.2.2.2.2.2.2.1.1
  simp only [Inputs.op_b_val, Inputs.op_c_val, vec4_eval, hpvb, hpvc] at h_env_cols
  have hop3 : (env.get i₀ * 2 + env.get (i₀ + 1) * 1 + env.get (i₀ + 2) * 0).val < 3 :=
    val_lt_three <| by
      rw [hflag0, hflag1, hflag2]
      rcases hf0 with hx | hx
      · rcases hf1 with ho | ho
        · exact Or.inl (by rw [hx, ho]; ring)
        · exact Or.inr (Or.inl (by rw [hx, ho]; ring))
      · obtain ⟨ho, -⟩ := hone0 hx
        exact Or.inr (Or.inr (by rw [hx, ho]; ring))
  refine ⟨⟨hbin, h_cpu⟩,
    ⟨⟨ha, hb, hop3, hbin⟩,
      ?_⟩,
    ⟨hbin, ⟨hz _, hz _, hz _, hz _⟩, Or.inl hop_a_0,
      by rw [himm, mul_zero], by rw [himm, sub_zero]; exact hbin,
      ⟨by rw [himm, zero_mul], by rw [himm, zero_mul], by rw [himm, zero_mul], by rw [himm, zero_mul]⟩,
      hrac_a, hrac_b, hrac_c⟩,
    by rcases hbin with h | h <;> rw [h] <;> simp,
    hbool _ hf0',
    hbool _ hf1',
    hbool _ hf2',
    hbool _ hsum01',
    hop_a_0⟩
  -- The composed `BitwiseU16Operation` `FormalAssertion`'s `Spec` at the witnessed `populate`d columns:
  -- `spec_populate` once the witnessed column struct equals `populate …`. Each of its 16 cells is
  -- `env.get (i₀+3+k)`, which the (normalised) witness hint pins to `(toElements (populate …))[k]`.
  convert BitwiseU16Operation.spec_populate (b := input_adapter_op_b_memory_prev_value)
    (c := input_adapter_op_c_memory_prev_value)
    (opcode := env.get i₀ * 2 + env.get (i₀ + 1) * 1 + env.get (i₀ + 2) * 0) ha hb hop3 input_is_real
    using 2
  refine (ProvableType.ext_iff _ _).mpr (fun i hi => ?_)
  refine Eq.trans ?_
    ((getElem_toElements_eval_varFromOffset env.toEnvironment (i₀ + 3) i hi).trans (h_env_cols ⟨i, hi⟩))
  -- `W` and `eval (ProvableStruct.varFromOffset …)` both circuit_norm-normalise to the same per-field
  -- struct, so the two `toElements` getElems coincide.
  simp [circuit_norm]

/-- The Bitwise chip row as a `GeneralFormalCircuit`: flag-gated RV64 `and`/`or`/`xor` semantic contract,
composing the witnessed `BitwiseU16Operation` gadget and the immediate-capable register reader; output is
the extracted `BitwiseCols` column struct. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs BitwiseCols :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness }

end SP1Clean.BitwiseChip
