import Clean.Air.FlatComponent
import ToClean.Circuit.SubcircuitProjection
import SP1Clean.Native.Chips.BitwiseChip.Defs
import SP1Clean.Math.EvalVec
import Clean.Air.Circuit
import ToClean.Circuit.WitgenEval

/-! # `SP1Clean.BitwiseChip` — contract: `Assumptions` / soundness / completeness / `circuit`

Semantic `Spec` (binary ∧ flag-gated `RV64.and`/`or`/`xor`), soundness (keyed on `one_hot3`
selector lemma — each opcode branch is a self-contained local argument), completeness, and the
bundled `circuit`. -/

namespace SP1Clean.BitwiseChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Byte-channel guarantees establish operand ranges; the chip needs no caller precondition. -/
def Assumptions (_input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop := True

/-- Honest bounded operands, boolean selectors/activity, register or immediate row form,
CPU clock bounds and prior-access timestamps. No external selector hint is needed. -/
def ProverAssumptions (input : Inputs (ZMod p)) (_data : ProverData (ZMod p))
    (_hint : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val ∧
  (input.is_real = 1 → Word.isU64 input.adapter.op_a_memory.prev_value) ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (input.isXor = 0 ∨ input.isXor = 1) ∧
  (input.isOr = 0 ∨ input.isOr = 1) ∧
  (input.isAnd = 0 ∨ input.isAnd = 1) ∧
  input.adapter.op_a_0 = 0 ∧
  (input.adapter.imm_c = 0 ∨ (input.is_real = 1 ∧ input.adapter.imm_c = 1)) ∧
  (input.adapter.imm_c *
      (input.adapter.op_c_memory.prev_value[0] - input.adapter.op_c[0]) = 0 ∧
    input.adapter.imm_c *
      (input.adapter.op_c_memory.prev_value[1] - input.adapter.op_c[1]) = 0 ∧
    input.adapter.imm_c *
      (input.adapter.op_c_memory.prev_value[2] - input.adapter.op_c[2]) = 0 ∧
    input.adapter.imm_c *
      (input.adapter.op_c_memory.prev_value[3] - input.adapter.op_c[3]) = 0) ∧
  Readers.CPUState.Spec
    { cols := input.state, next_pc := #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
      clk_inc := 8, is_real := input.is_real } ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_a_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_b_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 3⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_c_memory, input.is_real - input.adapter.imm_c,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 2⟩ ∧
  (input.is_real = 1 → input.adapter.op_a.val < 32 ∧
    input.state.pc[0].val < 2 ^ 16 ∧ input.state.pc[1].val < 2 ^ 16 ∧ input.state.pc[2].val < 2 ^ 16) ∧
  -- G1: the three pulled prior records' 24-bit access clocks (`Channels.MemoryMsg.ClkBound`, the clock
  -- half of the memory channel's `Guarantees`). A pull's completeness must exhibit the guarantee it
  -- consumes; in a real trace each prior access sits at a genuine `< 2^24` timestamp. The op_c
  -- component is harmlessly stronger than its access gate on immediate rows (the honest builder puts
  -- literal zero there). Soundness does *not* assume these — they are derived from the pulls.
  (input.is_real = 1 →
    input.adapter.op_a_memory.access_timestamp.prev_low.val < 2 ^ 24 ∧
    input.adapter.op_b_memory.access_timestamp.prev_low.val < 2 ^ 24 ∧
    input.adapter.op_c_memory.access_timestamp.prev_low.val < 2 ^ 24)

/-- One-hot lemma for the three opcode selectors: given each selector is binary and their sum is binary
(`E1 = is_xor + is_or + is_and` with `E9 = E1·(E1-1) = 0`), whichever selector is `1` forces the other
two to `0`. The sum-bound rules out two-or-three-hot via `2 ≠ 0` / `6 ≠ 0` in `ZMod p` (`p > 2^17`). -/
private lemma one_hot3 {x o a : ZMod p}
    (hx : x = 0 ∨ x = 1) (ho : o = 0 ∨ o = 1) (ha : a = 0 ∨ a = 1)
    (hsum : (x + o + a) * (x + o + a - 1) = 0) :
    (x = 1 → o = 0 ∧ a = 0) ∧ (o = 1 → x = 0 ∧ a = 0) ∧ (a = 1 → x = 0 ∧ o = 0) := by
  have h2 : (2 : ZMod p) ≠ 0 := by simp [← ZMod.val_eq_zero, val_2_zmod_p]
  have h6 : (6 : ZMod p) ≠ 0 := by simp [← ZMod.val_eq_zero, val_6_zmod_p]
  rcases hx with rfl | rfl <;> rcases ho with rfl | rfl <;> rcases ha with rfl | rfl <;>
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    first
      | exact ⟨rfl, rfl⟩
      | exact absurd h.symm one_ne_zero
      | (exfalso; apply h2; linear_combination hsum)
      | (exfalso; apply h6; linear_combination hsum)

/-- The byte opcode `is_xor·2 + is_or·1 + is_and·0` lands in `{0,1,2}` (one-hot), so its `val < 3` —
the opcode-range part of the composed `BitwiseU16Operation.circuit`'s `Assumptions`. -/
private lemma val_lt_three {x : ZMod p} (h : x = 0 ∨ x = 1 ∨ x = 2) : x.val < 3 := by
  rcases h with rfl | rfl | rfl
  · simp
  · rw [ZMod.val_one]; omega
  · rw [val_2_zmod_p]; omega

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- Structural `toElements` projection: cell `8 + k` of a `BitwiseU16Operation` column struct (after the
two 4-byte `U16toU8` low-byte blocks) is the `k`-th result byte. Destructuring `s` exposes the
constructor so `circuit_norm` routes the `toElements` append without evaluating any byte contents — the
completeness `populate` bridge applies it symbolically. -/
private lemma toElements_result_byte (s : BitwiseU16Operation.Columns (ZMod p)) (k : Fin 8) :
    (toElements s)[8 + (k : ℕ)]'(by simp only [circuit_norm]; omega)
      = s.bitwise_operation.result[(k : ℕ)] := by
  obtain ⟨⟨a⟩, ⟨b⟩, ⟨c⟩⟩ := s
  fin_cases k <;>
    (simp only [circuit_norm, explicit_provable_type, ProvableStruct.toComponents,
       ProvableStruct.componentsToElements];
     refine (Vector.getElem_append_right ?_ ?_).trans
       ((Vector.getElem_append_right ?_ ?_).trans
         ((Vector.getElem_append_left ?_).trans
           ((Vector.getElem_cast ?_).trans (Vector.getElem_append_left ?_)))) <;> decide)

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- Witness-pin transport for the eight result bytes: from the 16 cell-level `toElements` pins to the
per-byte projections of the column struct.

Stating this over an **opaque** `s` is the load-bearing part. `BitwiseU16Operation.populate` is a
`let`-bundle ending in `BitwiseOperation.populate (decompBytes …) (decompBytes …) opcode`, so writing
`(populate b c opcode).bitwise_operation.result[k]` in a *type* makes the elaborator `whnf` straight
through both `let`s, `decompBytes`, and the eight-fold `byteOp` result vector. With `s` abstract the
projection is inert, and the completeness proof instantiates it by application (pattern-matching only,
nothing unfolds). -/
private theorem result_byte_pin {env : ProverEnvironment (ZMod p)} {i₀ : ℕ}
    {s : BitwiseU16Operation.Columns (ZMod p)}
    (h : ∀ j : Fin 16, env.get (i₀ + (j : ℕ))
      = (toElements s)[(j : ℕ)]'(by
          have : size BitwiseU16Operation.Columns = 16 := rfl; have := j.isLt; omega))
    (k : Fin 8) :
    env.get (i₀ + 4 + 4 + (k : ℕ)) = s.bitwise_operation.result[(k : ℕ)] := by
  rw [show i₀ + 4 + 4 + (k : ℕ) = i₀ + (8 + (k : ℕ)) by ring]
  exact (h ⟨8 + (k : ℕ), by omega⟩).trans (toElements_result_byte s k)

-- Runs at the plain default: the former 2000000 ceiling was ~50x over; measured floor <= 40000.
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start [Inputs.is_real]
  obtain ⟨h_cpu, h_bw, _h_adapter, _h_regwrite,
    h_xor_bin, h_or_bin, h_and_bin, h_sum, _h_opa0⟩ := h_holds
  have h_bin := bool_of_mul_pred h_sum
  -- G1: the CPUState sub-`Spec`'s two clock byte bounds discharge the *push* side of the memory
  -- channel's new `MemoryMsg.ClkBound` guarantee — `ALUTypeReader`'s two read-back pushes
  -- (`clk_low + 3` / `+ 2`) and `RegisterWrite`'s op_a write push (`clk_low + 4`). The offset is left
  -- to unification, so this line never names the destructured state columns.
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec (h_cpu h_bin)
  have h_xor_bool := bool_of_mul_pred h_xor_bin
  have h_or_bool := bool_of_mul_pred h_or_bin
  have h_and_bool := bool_of_mul_pred h_and_bin
  have hoh := one_hot3 h_xor_bool h_or_bool h_and_bool h_sum
  have hop_cases : input_isXor * 2 + input_isOr * 1 + input_isAnd * 0 = 0
      ∨ input_isXor * 2 + input_isOr * 1 + input_isAnd * 0 = 1
      ∨ input_isXor * 2 + input_isOr * 1 + input_isAnd * 0 = 2 := by
    rcases h_xor_bool with hx | hx
    · rcases h_or_bool with ho | ho
      · exact Or.inl (by rw [hx, ho]; ring)
      · exact Or.inr (Or.inl (by rw [hx, ho]; ring))
    · obtain ⟨ho, _⟩ := hoh.1 hx
      exact Or.inr (Or.inr (by rw [hx, ho]; ring))
  have hop3 : (input_isXor * 2 + input_isOr * 1 + input_isAnd * 0).val < 3 :=
    val_lt_three hop_cases
  -- once the active flag forces the others to 0, the byte opcode reduces to a literal
  refine ⟨⟨h_bin, fun hr => ⟨fun hand => ?_, fun hor => ?_, fun hxor => ?_⟩,
    ⟨h_and_bool, h_or_bool, h_xor_bool, hoh.2.2, hoh.2.1, hoh.1⟩⟩, ?_⟩
  · obtain ⟨hx0, ho0⟩ := hoh.2.2 hand
    have hopc : input_isXor * 2 + input_isOr * 1 + input_isAnd * 0 = 0 := by
      rw [hx0, ho0]; ring
    exact (BitwiseU16Operation.result_semantic _ hr
      (h_bw ⟨by rw [hopc, ZMod.val_zero]; omega, h_bin⟩)).1 hopc
  · obtain ⟨hx0, _ha0⟩ := hoh.2.1 hor
    have hopc : input_isXor * 2 + input_isOr * 1 + input_isAnd * 0 = 1 := by
      rw [hx0, hor]; ring
    exact (BitwiseU16Operation.result_semantic _ hr
      (h_bw ⟨by rw [hopc, ZMod.val_one]; omega, h_bin⟩)).2.1 hopc
  · obtain ⟨ho0, _ha0⟩ := hoh.1 hxor
    have hopc : input_isXor * 2 + input_isOr * 1 + input_isAnd * 0 = 2 := by
      rw [hxor, ho0]; ring
    exact (BitwiseU16Operation.result_semantic _ hr
      (h_bw ⟨by rw [hopc]; exact val_lt_three (Or.inr (Or.inr rfl)), h_bin⟩)).2.2 hopc
  -- The per-emitter channel-requirement tail: the bare `CPUState` `Assumptions` (the binary gate), the
  -- composed `BitwiseU16Operation`/`ALUTypeReader` requirements (bare or `[] ∨ Assumptions` disjuncts).
  · and_intros <;>
      first | exact h_bin | exact ⟨hop3, h_bin⟩ | exact Or.inl rfl
            | exact Or.inr h_bin
            | exact Or.inr ⟨h_bin, h_bin, h_clk⟩
            | exact Or.inr ⟨h_bin, (fun hr => by
                have hisu := BitwiseU16Operation.resultWord_isU64 hr (h_bw ⟨hop3, h_bin⟩) hop_cases
                simp only [BitwiseU16Operation.resultWord, Vector.getElem_map,
                  circuit_norm] at hisu ⊢
                exact hisu), h_clk.at_four⟩

-- Keep the populated byte columns folded when transporting witness pins.
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start [Inputs.is_real]
  obtain ⟨ha, hb, ha_prev, hbin, hf0, hf1, hf2, hop_a_0, himm,
    himm_copy, h_cpu, hrac_a, hrac_b, hrac_c, hdec, hprevclk⟩ := h_assumptions
  -- G1: the *push* side clock bounds, from the prover-supplied CPUState clock byte bounds.
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec h_cpu
  obtain ⟨-, h_env_cols, -⟩ := h_env
  have hflag0 : Expression.eval env.toEnvironment input_var_isXor = input_isXor := h_input.2.2.1
  have hflag1 : Expression.eval env.toEnvironment input_var_isOr = input_isOr := h_input.2.2.2.1
  have hflag2 : Expression.eval env.toEnvironment input_var_isAnd = input_isAnd := h_input.2.2.2.2
  have hbool : ∀ x : ZMod p, x = 0 ∨ x = 1 → x * (x - 1) = 0 := by
    rintro x (h | h) <;> rw [h] <;> simp
  have hone := one_hot3 hf0 hf1 hf2 (hbool _ hbin)
  have hz : ∀ w : ZMod p, input_adapter_op_a_0 * w = 0 := fun w => by rw [hop_a_0, zero_mul]
  -- The witness hint computed `populate` at the *eval-of-var* operands; `h_input` identifies those with
  -- the value-form operands, normalising the hint's `populate` to match `spec_populate`.
  have hpvb : Vector.map (Expression.eval env.toEnvironment) input_var_adapter_op_b_memory_prev_value
      = input_adapter_op_b_memory_prev_value := h_input.2.1.2.2.2.2.1.1
  have hpvc : Vector.map (Expression.eval env.toEnvironment) input_var_adapter_op_c_memory_prev_value
      = input_adapter_op_c_memory_prev_value := h_input.2.1.2.2.2.2.2.2.1.1
  simp only [Inputs.op_b_val, Inputs.op_c_val] at h_env_cols
  -- `circuit_norm` states the witness condition as one struct equation; read it cell by cell.
  replace h_env_cols := fun j : Fin 16 =>
    (ProvableStruct.get_of_eval_varFromOffset_eq (α := BitwiseU16Operation.Columns) env.toEnvironment i₀ _
      (by simpa only [circuit_norm] using h_env_cols) j (by
        have h : size BitwiseU16Operation.Columns = 16 := rfl
        have := j.isLt
        omega)).trans (Witgen.getElem_eval_toElements _ _ j (by
      have h : size BitwiseU16Operation.Columns = 16 := rfl
      have := j.isLt
      omega)).symm
  -- The witness stream is the `populateFE` IR; `populateFE_eval_cell` evaluates each pinned cell to
  -- the value-level `populate` at the evaluated operands (the operands folded through `vec4_eval` +
  -- `h_input`, the opcode expression evaluated to its `env.get` form).
  have hopc : Expression.eval env.toEnvironment
      (input_var_isXor * 2 + input_var_isOr * 1 + input_var_isAnd * 0)
      = input_isXor * 2 + input_isOr * 1 + input_isAnd * 0 := by
    simp only [circuit_norm, hflag0, hflag1, hflag2]
  have hcolsPop : ∀ j : Fin 16, env.get (i₀ + (j : ℕ))
      = (toElements (BitwiseU16Operation.populate input_adapter_op_b_memory_prev_value
          input_adapter_op_c_memory_prev_value
          (input_isXor * 2 + input_isOr * 1 + input_isAnd * 0)))[(j : ℕ)]'(by
        have : size BitwiseU16Operation.Columns = 16 := rfl
        have := j.isLt
        omega) := by
    intro j
    refine (h_env_cols j).trans ?_
    have hcell := BitwiseU16Operation.populateFE_eval_cell env
      input_var_adapter_op_b_memory_prev_value input_var_adapter_op_c_memory_prev_value
      (input_var_isXor * 2 + input_var_isOr * 1 + input_var_isAnd * 0)
      input_adapter_op_b_memory_prev_value input_adapter_op_c_memory_prev_value
      ((vec4_eval env.toEnvironment _).trans hpvb) ((vec4_eval env.toEnvironment _).trans hpvc)
      ha hb (j : ℕ) j.isLt
    rw [hopc] at hcell
    exact hcell
  have hop_cases : input_isXor * 2 + input_isOr * 1 + input_isAnd * 0 = 0
      ∨ input_isXor * 2 + input_isOr * 1 + input_isAnd * 0 = 1
      ∨ input_isXor * 2 + input_isOr * 1 + input_isAnd * 0 = 2 := by
    rcases hf0 with hx | hx
    · rcases hf1 with ho | ho
      · exact Or.inl (by rw [hx, ho]; ring)
      · exact Or.inr (Or.inl (by rw [hx, ho]; ring))
    · obtain ⟨ho, -⟩ := hone.1 hx
      exact Or.inr (Or.inr (by rw [hx, ho]; ring))
  have hop3 : (input_isXor * 2 + input_isOr * 1 + input_isAnd * 0).val < 3 :=
    val_lt_three hop_cases
  have himm_pad : ((input_isXor + input_isOr + input_isAnd) - 1) * input_adapter_imm_c = 0 := by
    rcases himm with h0 | ⟨hr, h1⟩
    · rw [h0, mul_zero]
    · rw [hr, h1]
      simp
  have hcbin : (input_isXor + input_isOr + input_isAnd) - input_adapter_imm_c = 0 ∨
      (input_isXor + input_isOr + input_isAnd) - input_adapter_imm_c = 1 := by
    rcases himm with h0 | ⟨hr, h1⟩
    · rw [h0, sub_zero]
      exact hbin
    · rw [hr, h1]
      simp
  have hreal_of_c (hc : (input_isXor + input_isOr + input_isAnd) - input_adapter_imm_c = 1) : (input_isXor + input_isOr + input_isAnd) = 1 := by
    rcases himm with h0 | ⟨hr, h1⟩
    · rwa [h0, sub_zero] at hc
    · exact hr
  refine ⟨⟨hbin, h_cpu⟩,
    ⟨⟨hop3, hbin⟩,
      ?_⟩,
    ⟨⟨hbin, hbin, h_clk⟩,
      ⟨⟨hz _, hz _, hz _, hz _⟩, Or.inl hop_a_0,
      himm_pad, hcbin, himm_copy,
      hrac_a, hrac_b, hrac_c, hdec,
      (fun hr => ⟨ha_prev hr, ha, (hprevclk hr).1, (hprevclk hr).2.1⟩),
      fun hc => ⟨hb, (hprevclk (hreal_of_c hc)).2.2⟩⟩⟩,
    ⟨⟨hbin, ?_, h_clk.at_four⟩, trivial⟩,
    hbool _ hf0,
    hbool _ hf1,
    hbool _ hf2,
    hbool _ hbin,
    hop_a_0⟩
  · -- The composed `BitwiseU16Operation` `FormalAssertion`'s `Spec` at the witnessed `populate`d columns:
    -- `spec_populate` once the witnessed column struct equals `populate …`. Each of its 16 cells is
    -- `env.get (i₀+k)`, which the (normalised) witness hint pins to `(toElements (populate …))[k]`.
    convert BitwiseU16Operation.spec_populate (b := input_adapter_op_b_memory_prev_value)
      (c := input_adapter_op_c_memory_prev_value)
      (opcode := input_isXor * 2 + input_isOr * 1 + input_isAnd * 0) ha hb hop3 (input_isXor + input_isOr + input_isAnd)
      using 2
    -- 4.32: `convert … using 2` now leaves only the `cols` equality. The former `rfl` step closed a
    -- separate `circuit.Spec = Spec` goal that the congruence no longer emits (Clean `088a9287`).
    -- Per cell: the varFromOffset read is the pinned witness cell (`hcolsPop`), already in the
    -- value-level `populate` form.
    refine (ProvableType.ext_iff (α := BitwiseU16Operation.Columns) _ _).mpr (fun i hi => ?_)
    refine Eq.trans ?_
      ((getElem_toElements_eval_varFromOffset env.toEnvironment i₀ i hi).trans
        (hcolsPop ⟨i, hi⟩))
    simp only [circuit_norm]
  · -- RegisterWrite's `isU64 value` (the op_a write push): the witnessed result word's `isU64` from
    -- the pure bitwise result-range lemma at the populated columns (`spec_populate`), transported
    -- to the chip's explicit `#v[r[0]+r[1]*256, …]` through per-byte witness pins.
    intro hr
    have hisu := BitwiseU16Operation.resultWord_isU64 hr
      (BitwiseU16Operation.spec_populate ha hb hop3 (input_isXor + input_isOr + input_isAnd)) hop_cases
    -- Transport the value-level pins (`hcolsPop`) to the per-byte projections through
    -- `result_byte_pin` — whose `s` stays abstract, so `populate` is never unfolded.
    have key := result_byte_pin hcolsPop
    convert hisu using 2
    simp only [BitwiseU16Operation.resultWord, Inputs.op_b_val, Inputs.op_c_val]
    simp only [show env.get (i₀ + 4 + 4) = _ from key 0,
               show env.get (i₀ + 4 + 4 + 1) = _ from key 1,
               show env.get (i₀ + 4 + 4 + 2) = _ from key 2,
               show env.get (i₀ + 4 + 4 + 3) = _ from key 3,
               show env.get (i₀ + 4 + 4 + 4) = _ from key 4,
               show env.get (i₀ + 4 + 4 + 5) = _ from key 5,
               show env.get (i₀ + 4 + 4 + 6) = _ from key 6,
               show env.get (i₀ + 4 + 4 + 7) = _ from key 7]
    rfl

/-- Exact State-channel pair emitted by the composed CPU-state reader. -/
def exposedStateInteractions (input : Var Inputs (ZMod p)) :
    List (ChannelInteraction (stateChannel (p := p))) :=
  [ stateChannel.pulledIf input.is_real
      ⟨input.state.clk_high,
       input.state.clk_0_16 + input.state.clk_16_24 * 65536,
       input.state.pc[0], input.state.pc[1], input.state.pc[2]⟩,
    stateChannel.pushedIf input.is_real
      ⟨input.state.clk_high,
       input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 8,
       input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]⟩ ]

/-- Byte operation selected by the input flags: AND = 0, OR = 1, XOR = 2. -/
def exposedByteOpcode (input : Var Inputs (ZMod p)) : Expression (ZMod p) :=
  input.isXor * 2 + input.isOr * 1 + input.isAnd * 0

/-- The eight source-B bytes supplied to the bytewise operation: four witnessed low bytes
interleaved with the four derived high bytes. -/
def exposedBBytes (input : Var Inputs (ZMod p)) (offset : ℕ) :
    Vector (Expression (ZMod p)) 8 :=
  #v[
    var ⟨offset⟩,
    (input.op_b_val[0] - var ⟨offset⟩) *
      Expression.const ((256 : ZMod p)⁻¹),
    var ⟨offset + 1⟩,
    (input.op_b_val[1] - var ⟨offset + 1⟩) *
      Expression.const ((256 : ZMod p)⁻¹),
    var ⟨offset + 2⟩,
    (input.op_b_val[2] - var ⟨offset + 2⟩) *
      Expression.const ((256 : ZMod p)⁻¹),
    var ⟨offset + 3⟩,
    (input.op_b_val[3] - var ⟨offset + 3⟩) *
      Expression.const ((256 : ZMod p)⁻¹)]

/-- The eight source-C bytes supplied to the bytewise operation: four witnessed low bytes
interleaved with the four derived high bytes. -/
def exposedCBytes (input : Var Inputs (ZMod p)) (offset : ℕ) :
    Vector (Expression (ZMod p)) 8 :=
  #v[
    var ⟨offset + 4⟩,
    (input.op_c_val[0] - var ⟨offset + 4⟩) *
      Expression.const ((256 : ZMod p)⁻¹),
    var ⟨offset + 5⟩,
    (input.op_c_val[1] - var ⟨offset + 5⟩) *
      Expression.const ((256 : ZMod p)⁻¹),
    var ⟨offset + 6⟩,
    (input.op_c_val[2] - var ⟨offset + 6⟩) *
      Expression.const ((256 : ZMod p)⁻¹),
    var ⟨offset + 7⟩,
    (input.op_c_val[3] - var ⟨offset + 7⟩) *
      Expression.const ((256 : ZMod p)⁻¹)]

/-- The eight witnessed bytewise result cells. -/
def exposedResultBytes (offset : ℕ) : Vector (Expression (ZMod p)) 8 :=
  #v[var ⟨offset + 8⟩, var ⟨offset + 9⟩,
    var ⟨offset + 10⟩, var ⟨offset + 11⟩,
    var ⟨offset + 12⟩, var ⟨offset + 13⟩,
    var ⟨offset + 14⟩, var ⟨offset + 15⟩]

/-- Exact Byte-channel list emitted by Bitwise: two CPU clock checks, eight raw-opcode
bitwise rows, and the ALU reader's six register-timestamp checks. -/
def exposedByteInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  let clkLow := input.state.clk_0_16 + input.state.clk_16_24 * 65536
  let opCGate := input.is_real - input.adapter.imm_c
  let opcode := exposedByteOpcode input
  let b := exposedBBytes input offset
  let c := exposedCBytes input offset
  let r := exposedResultBytes (p := p) offset
  [ byteChannel.pulledIf input.is_real
      ⟨6, (input.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹,
       Expression.const ((13 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf input.is_real ⟨3, 0, input.state.clk_16_24, 0⟩,
    byteChannel.pulledIf input.is_real ⟨opcode, r[0], b[0], c[0]⟩,
    byteChannel.pulledIf input.is_real ⟨opcode, r[1], b[1], c[1]⟩,
    byteChannel.pulledIf input.is_real ⟨opcode, r[2], b[2], c[2]⟩,
    byteChannel.pulledIf input.is_real ⟨opcode, r[3], b[3], c[3]⟩,
    byteChannel.pulledIf input.is_real ⟨opcode, r[4], b[4], c[4]⟩,
    byteChannel.pulledIf input.is_real ⟨opcode, r[5], b[5], c[5]⟩,
    byteChannel.pulledIf input.is_real ⟨opcode, r[6], b[6], c[6]⟩,
    byteChannel.pulledIf input.is_real ⟨opcode, r[7], b[7], c[7]⟩,
    byteChannel.pulledIf input.is_real
      ⟨6, input.adapter.op_a_memory.access_timestamp.diff_low_limb,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨3, 0,
       (clkLow + 4 - input.adapter.op_a_memory.access_timestamp.prev_low - 1 -
          input.adapter.op_a_memory.access_timestamp.diff_low_limb) *
            (65536 : ZMod p)⁻¹,
       0⟩,
    byteChannel.pulledIf input.is_real
      ⟨6, input.adapter.op_b_memory.access_timestamp.diff_low_limb,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨3, 0,
       (clkLow + 3 - input.adapter.op_b_memory.access_timestamp.prev_low - 1 -
          input.adapter.op_b_memory.access_timestamp.diff_low_limb) *
            (65536 : ZMod p)⁻¹,
       0⟩,
    byteChannel.pulledIf opCGate
      ⟨6, input.adapter.op_c_memory.access_timestamp.diff_low_limb,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf opCGate
      ⟨3, 0,
       (clkLow + 2 - input.adapter.op_c_memory.access_timestamp.prev_low - 1 -
          input.adapter.op_c_memory.access_timestamp.diff_low_limb) *
            (65536 : ZMod p)⁻¹,
       0⟩ ]

/-- Bitwise's exact Memory-channel interaction list (ALU-type: the op_c register pull/read-back pair
is gated by **`is_real - imm_c`** — an immediate does no register read — and addressed by the low limb
`op_c[0]`).  The op_a write push carries the byte-packed result word `[r0+r1·256, …, r6+r7·256]` from
the witnessed result bytes (cells `offset+8..15` — after the two 4-byte
`U16toU8` low-byte blocks).  Keeping this list beside `circuit` makes Clean's exposure interface the
single structural source consumed by both faithfulness and semantic grounding. -/
def exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (memoryChannel (p := p))) :=
  [ memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_a_memory.access_timestamp.prev_low,
       input.adapter.op_a, 0, 0, input.adapter.op_a_memory.prev_value⟩,
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩,
    memoryChannel.pushedIf input.is_real
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 3,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩,
    memoryChannel.pulledIf (input.is_real - input.adapter.imm_c)
      ⟨input.state.clk_high, input.adapter.op_c_memory.access_timestamp.prev_low,
       input.adapter.op_c[0], 0, 0, input.adapter.op_c_memory.prev_value⟩,
    memoryChannel.pushedIf (input.is_real - input.adapter.imm_c)
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 2,
       input.adapter.op_c[0], 0, 0, input.adapter.op_c_memory.prev_value⟩,
    memoryChannel.pushedIf input.is_real
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
       input.adapter.op_a, 0, 0,
       #v[var { index := offset + 8 } + var { index := offset + 9 } * 256,
          var { index := offset + 10 } + var { index := offset + 11 } * 256,
          var { index := offset + 12 } + var { index := offset + 13 } * 256,
          var { index := offset + 14 } + var { index := offset + 15 } * 256]⟩ ]

omit [Fact (2 ^ 17 < p)] in
/-- The exact source-B pull occupies its declared slot in Bitwise's exposed Memory list. -/
theorem opBPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

omit [Fact (2 ^ 17 < p)] in
/-- The exact (`is_real - imm_c`)-gated source-C pull occupies its declared slot in Bitwise's exposed
Memory list. -/
theorem opCPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf (input.is_real - input.adapter.imm_c)
      ⟨input.state.clk_high, input.adapter.op_c_memory.access_timestamp.prev_low,
       input.adapter.op_c[0], 0, 0, input.adapter.op_c_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

/-- Program opcode selected by the input flags: XOR = 3, OR = 4, AND = 5. -/
def exposedOpcode (input : Var Inputs (ZMod p)) : Expression (ZMod p) :=
  input.isXor * 3 + input.isOr * 4 + input.isAnd * 5

/-- Exact Program fetch emitted by the ALU adapter, with the instruction opcode reconstructed from
the three chip-owned variant flags. -/
def exposedProgramInteractions (input : Var Inputs (ZMod p)) :
    List (ChannelInteraction (programChannel (p := p))) :=
  [ programChannel.pulledIf input.is_real
      ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], exposedOpcode input,
       input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c,
       input.adapter.op_a_0, 0, input.adapter.imm_c⟩ ]

/-- The Bitwise chip row as a `GeneralFormalCircuit`: flag-gated RV64 `and`/`or`/`xor` semantic contract,
composing the witnessed `BitwiseU16Operation` gadget and the immediate-capable register reader; output is
the native `Columns` row. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs Columns :=
  { name := "sp1.native.bitwise", main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness,
    channelsWithRequirements :=
      [stateChannel.toRaw, memoryChannel.toRaw],
    -- W11 (A2): expose the State-bus `[pulledIf is_real cur, pushedIf is_real next]` pair (pc+4, clk+8)
    -- as chip-owned interactions (the Clean `VmTables` re-base that motivated the shape was investigated
    -- and deferred — roadmap W11); descends to the composed `CPUState` subcircuit's lone pull+push.
    exposedChannels := fun input offset =>
      expose stateChannel (exposedStateInteractions input) ++
      expose memoryChannel (exposedMemoryInteractions input offset) ++
      -- The Program-bus instruction fetch (descended from the composed `ALUTypeReader`, gate
      -- `is_trusted = is_real`, opcode = the committed one-hot flag encoding), consumed by
      -- `Soundness/TypedProgram.lean`.
      expose programChannel (exposedProgramInteractions input),
    exposedChannels_eq := by
      preserve_tactic_target
      intro input offset
      have h_byte := Channels.byteChannel_toRaw_ne_stateChannel (p := p)
      have h_program := Channels.programChannel_toRaw_ne_stateChannel (p := p)
      have h_memory := Channels.memoryChannel_toRaw_ne_stateChannel (p := p)
      unfold Operations.ExposedChannelsLawful
      intro exposed exposedMem
      simp only [expose, exposedStateInteractions, exposedProgramInteractions,
        List.mem_append, List.mem_singleton] at exposedMem
      rcases exposedMem with (rfl | rfl) | rfl
      · simp only [main, Readers.CPUState.circuit, Readers.CPUState.main,
          Readers.ALUTypeReader.circuit, Readers.ALUTypeReader.main,
          Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
          Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
          Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
          SP1Clean.BitwiseU16Operation.circuit, SP1Clean.BitwiseU16Operation.main,
          SP1Clean.BitwiseOperation.circuit, SP1Clean.BitwiseOperation.main,
          circuit_norm, FormalAssertion.toSubcircuit_interactions,
          GeneralFormalCircuit.toSubcircuit_interactions]
        simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
          h_byte, h_program, h_memory, decide_false, decide_true, Bool.false_eq_true,
          List.nil_append]
      · simp only [main, Readers.CPUState.circuit, Readers.CPUState.main,
          Readers.ALUTypeReader.circuit, Readers.ALUTypeReader.main,
          Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
          Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
          Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
          SP1Clean.BitwiseU16Operation.circuit, SP1Clean.BitwiseU16Operation.main,
          SP1Clean.BitwiseOperation.circuit, SP1Clean.BitwiseOperation.main,
          circuit_norm, FormalAssertion.toSubcircuit_interactions,
          GeneralFormalCircuit.toSubcircuit_interactions]
        simp [circuit_norm, Gadgets.Equality.main, exposedMemoryInteractions]
      · -- Program branch: compositional — the reader subcircuit keeps its fetch via the
        -- reader-local `_subcircuit` lemma; every other child is nil on the Program channel.
        simp only [main, Circuit.operations, Circuit.bind_def,
          Circuit.pure_def, subcircuitWithAssertion, assertion,
          HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength]
        simp only [Operations.interactionsWith_append,
          InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil,
          InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
          Soundness.aluTypeReader_programInteractions_subcircuit,
          Readers.CPUState.circuit, Readers.CPUState.channelsWithGuarantees_eq,
          Readers.RegisterWrite.circuit, Readers.RegisterWrite.channelsWithGuarantees_eq,
          SP1Clean.BitwiseU16Operation.circuit, SP1Clean.BitwiseU16Operation.elaborated,
          FormalCircuitBase.channelsWithGuarantees_def, List.mem_cons, List.not_mem_nil, or_false,
          Channels.programChannel_eq_byteChannel_false,
          Channels.programChannel_eq_stateChannel_false,
          Channels.programChannel_eq_memoryChannel_false,
          not_false_eq_true,
          Operations.interactionsWith_nil, List.map_cons, List.map_nil, List.nil_append,
          List.append_nil, Soundness.aluTypeProgramMessage, exposedOpcode]
        simp only [Operations.interactionsWith_subcircuit,
          FormalAssertion.toSubcircuit_interactions, Gadgets.Equality.main, circuit_norm,
          List.filter_nil, List.nil_append] }

@[circuit_norm] theorem circuit_main_eq : (circuit (p := p)).main = main := rfl

@[circuit_norm] theorem circuit_localLength_eq (input : Var Inputs (ZMod p)) :
    (circuit (p := p)).localLength input = 16 := rfl

@[circuit_norm] theorem circuit_size_eq :
    (circuit (p := p)).size = size Inputs + 16 := by
  rw [GeneralFormalCircuit.size_eq, circuit_localLength_eq]

/-- The completed Bitwise circuit exposes exactly its State interaction pair. -/
theorem interactionsWith_state_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith stateChannel.toRaw =
      (exposedStateInteractions input).map ChannelInteraction.toRaw := by
  exact circuit.interactionsWith_eq_of_mem_exposedChannels input offset
    ⟨stateChannel.toRaw, (exposedStateInteractions input).map ChannelInteraction.toRaw⟩
    (by simp [circuit, expose])

/-- The completed Bitwise circuit emits exactly the sixteen Byte interactions above.
Runs at the plain default: the former 4000000 ceiling was ~100x over; measured floor <= 40000. -/
theorem interactionsWith_byte_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith byteChannel.toRaw =
      (exposedByteInteractions input offset).map ChannelInteraction.toRaw := by
  simp [main, exposedByteInteractions, exposedByteOpcode, exposedBBytes,
    exposedCBytes, exposedResultBytes,
    Readers.CPUState.circuit, Readers.CPUState.main,
    Readers.ALUTypeReader.circuit, Readers.ALUTypeReader.main,
    Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    SP1Clean.BitwiseU16Operation.circuit, SP1Clean.BitwiseU16Operation.main,
    SP1Clean.BitwiseOperation.circuit, SP1Clean.BitwiseOperation.main,
    Gadgets.Equality.main, FormalAssertion.toSubcircuit_interactions,
    GeneralFormalCircuit.toSubcircuit_interactions, circuit_norm, Nat.add_assoc]

/-- The completed Bitwise circuit exposes exactly the Memory interaction list above. -/
theorem interactionsWith_memory_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw := by
  exact circuit.interactionsWith_eq_of_mem_exposedChannels input offset
    ⟨memoryChannel.toRaw, (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw⟩
    (by simp [circuit, expose])

/-- The completed Bitwise circuit exposes exactly its Program fetch. -/
theorem interactionsWith_program_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith programChannel.toRaw =
      (exposedProgramInteractions input).map ChannelInteraction.toRaw := by
  exact circuit.interactionsWith_eq_of_mem_exposedChannels input offset
    ⟨programChannel.toRaw,
      (exposedProgramInteractions input).map ChannelInteraction.toRaw⟩
    (by simp [circuit, expose])

/-- The row contains no Clean lookup operations; cross-table checks use channels. -/
theorem lookups_empty :
    ({ circuit := BitwiseChip.circuit (p := p) } :
      Air.Flat.Component (ZMod p)).operations.lookups = [] := by
  rw [Air.Flat.Component.lookups_eq, Air.Flat.Component.rowOperations_mk,
    BitwiseChip.circuit_main_eq]
  simp [BitwiseChip.main, Readers.CPUState.circuit, Readers.CPUState.main,
    Readers.ALUTypeReader.circuit, Readers.ALUTypeReader.main,
    Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    BitwiseU16Operation.circuit, BitwiseU16Operation.main,
    BitwiseOperation.circuit, BitwiseOperation.main,
    Gadgets.Equality.main, circuit_norm]

end SP1Clean.BitwiseChip
