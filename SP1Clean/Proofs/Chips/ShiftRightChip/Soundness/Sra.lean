import SP1Clean.Proofs.Chips.ShiftRightChip.Defs
import SP1Clean.Proofs.Chips.ShiftRightChip.Math
import SP1Clean.Proofs.Chips.ShiftRightChip.Flags

/-! # `ShiftRightChip` — sra conjunct soundness (split for parallel compilation)

Arithmetic right-shift (SRA) conjunct, proved as a standalone `GeneralFormalCircuit.Soundness`
over a single-conjunct local `Spec`. -/

namespace SP1Clean.ShiftRightChip.SoundSra

open Circuit
open Extracted (ShiftRightCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- The `sra` conjunct of `ShiftRightChip.Spec`, as a standalone single-conjunct spec. -/
def Spec (input : Inputs (ZMod p)) (cols : ShiftRightCols (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  input.is_real = 1 →
    (cols.is_sra = 1 →
      Word.toBitVec64 cols.a = RV64.sra (Word.toBitVec64 input.adapter.op_c_memory.prev_value)
        (Word.toBitVec64 input.adapter.op_b_memory.prev_value))

set_option linter.unusedVariables false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option maxHeartbeats 16000000 in
/-- Soundness of the `sra` conjunct (verbatim slice of the monolithic proof + the shared tail). -/
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_cpu, h_msb1, h_msb2, h_msb3, h_alu, h_realgate,
    h_srl_b, h_sra_b, h_srlw_b, h_sraw_b, h_sum_b, h_wimm,
    h_b0, h_b1, h_b2, h_b3, h_b4, h_b5,
    h_s0w, h_s0b, h_s1w, h_s1b, h_s2w, h_s2b, h_s3w, h_s3b, h_onehot,
    h_v01, h_v012, h_v0123,
    h_split0, h_split1, h_split2, h_split3,
    h_lr0, h_lr1, h_lr2, h_lr3,
    h_msbz, h_smv, h_srwz,
    h_o0, h_o1, h_o2, h_o3, h_o4, h_o5, h_o6, h_o7,
    h_o8, h_o9, h_o10, h_o11, h_o12, h_o13, h_o14, h_o15,
    h_w0, h_w1, h_w2, h_w3, h_w4, h_w5,
    h_opa0,
    h_byte0, h_byte1, h_byte2, h_byte3, h_byte4, h_byte5, h_byte6, h_byte7, h_byte8⟩ := h_holds
  -- post-#398 the nine byte receives owe no padding requirement.
  refine ⟨?spec, ?cpuA, ?msb1A, ?msb2A, ?msb3A, ?aluA,
    fun h1 h0 => off_gate_vacuous (bool_of_mul_pred h_sum_b) h1 h0,
    fun h1 h0 => off_gate_vacuous (bool_of_mul_pred h_sum_b) h1 h0,
    fun h1 h0 => off_gate_vacuous (bool_of_mul_pred h_sum_b) h1 h0,
    fun h1 h0 => off_gate_vacuous (bool_of_mul_pred h_sum_b) h1 h0,
    fun h1 h0 => off_gate_vacuous (bool_of_mul_pred h_sum_b) h1 h0,
    fun h1 h0 => off_gate_vacuous (bool_of_mul_pred h_sum_b) h1 h0,
    fun h1 h0 => off_gate_vacuous (bool_of_mul_pred h_sum_b) h1 h0,
    fun h1 h0 => off_gate_vacuous (bool_of_mul_pred h_sum_b) h1 h0,
    fun h1 h0 => off_gate_vacuous (bool_of_mul_pred h_sum_b) h1 h0⟩
  case spec =>
      intro hreal hsra
      -- `is_sra = 1` forces the other three variant flags to 0 (single-op selection).
      obtain ⟨h_srl0, h_srlw0, h_sraw0⟩ :=
        single_flag hsra (bool_of_mul_pred h_srl_b) (bool_of_mul_pred h_srlw_b)
          (bool_of_mul_pred h_sraw_b)
          (by rcases bool_of_mul_pred h_sum_b with h | h
              · exact Or.inl (by linear_combination h)
              · exact Or.inr (by linear_combination h))
      -- Reduce the committed result column `cols.a` to its four `env.get`s.
      have hcolsa : (Vector.map (Expression.eval env)
            (Vector.mapRange 4 fun i => var { index := i₀ + i }) : Word (ZMod p))
          = #v[env.get i₀, env.get (i₀ + 1), env.get (i₀ + 2), env.get (i₀ + 3)] := by
        apply Vector.ext; intro i hi
        simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
        interval_cases i <;> rfl
      obtain ⟨h_rs1U, h_rs2U⟩ := h_assumptions
      -- Alias the committed columns (exact `env.get` index forms — Lean does not reduce the `i₀+4+1+…`).
      set cb0 := env.get (i₀ + 4 + 1 + 1) with hcb0_def
      set cb1 := env.get (i₀ + 4 + 1 + 1 + 1) with hcb1_def
      set cb2 := env.get (i₀ + 4 + 1 + 1 + 2) with hcb2_def
      set cb3 := env.get (i₀ + 4 + 1 + 1 + 3) with hcb3_def
      set cb4 := env.get (i₀ + 4 + 1 + 1 + 4) with hcb4_def
      set cb5 := env.get (i₀ + 4 + 1 + 1 + 5) with hcb5_def
      set ll0 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3) with hll0_def
      set ll1 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 1) with hll1_def
      set ll2 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 2) with hll2_def
      set ll3 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 3) with hll3_def
      set hl0 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4) with hhl0_def
      set hl1 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 1) with hhl1_def
      set hl2 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 2) with hhl2_def
      set hl3 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 3) with hhl3_def
      -- The variant flag-sum is 1 on the real SRL row, so the byte-pull guarantees fire.
      have hsum1 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4)
          + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)
          + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2)
          + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3) = 1 := by
        rw [h_srl0, hsra, h_srlw0, h_sraw0]; ring
      have hsumneg : -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4)
          + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)
          + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2)
          + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) = -1 := by rw [hsum1]
      -- Generic byte-fact extractor: fold `sum * v → v` and read off the `Range` bound.
      have hbyte_fact : ∀ {v w : ZMod p},
          (-(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4)
              + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)
              + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2)
              + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) = -1 →
            byteChannel.Guarantees (⟨6, v, w, 0⟩
              : ByteRow (ZMod p)) env.data) → v.val < 2 ^ w.val := by
        intro v w hb
        exact byteRowSpec_range_val (hb hsumneg)
      -- The eight limb range facts (still in the byte-pull width form).
      have lt_ll0 := hbyte_fact h_byte1
      have lt_lh0 := hbyte_fact h_byte2
      have lt_ll1 := hbyte_fact h_byte3
      have lt_lh1 := hbyte_fact h_byte4
      have lt_ll2 := hbyte_fact h_byte5
      have lt_lh2 := hbyte_fact h_byte6
      have lt_ll3 := hbyte_fact h_byte7
      have lt_lh3 := hbyte_fact h_byte8
      -- The six `c_bits` booleans.
      have b_cb0 := bool_of_mul_pred h_b0
      have b_cb1 := bool_of_mul_pred h_b1
      have b_cb2 := bool_of_mul_pred h_b2
      have b_cb3 := bool_of_mul_pred h_b3
      have b_cb4 := bool_of_mul_pred h_b4
      have b_cb5 := bool_of_mul_pred h_b5
      set v0123 := env.get (i₀ + 4 + 1 + 1 + 6 + 1) with hv0123_def
      set v012 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 1) with hv012_def
      set v01 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 2) with hv01_def
      -- Forget the `let`-bodies (keep the `*_def` equations): `set`'s `let`-bindings otherwise wrap the
      -- carrier as `id (ZMod p)`, which blocks `linear_combination`/`ring`'s instance synthesis.
      clear_value cb0 cb1 cb2 cb3 cb4 cb5 ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 v0123 v012 v01
      -- Eval-of-input bridges for the `op_b`/`op_c` register reads (from `h_input`).
      obtain ⟨-, -, -, -, -, -, ⟨h_obmap, -, -⟩, -, ⟨h_ocmap, -, -⟩, -⟩ := h_input
      have hb0e : Expression.eval env input_var_adapter_op_b_memory_prev_value[0]
          = input_adapter_op_b_memory_prev_value[0] := by rw [← h_obmap]; simp only [Vector.getElem_map]
      have hb1e : Expression.eval env input_var_adapter_op_b_memory_prev_value[1]
          = input_adapter_op_b_memory_prev_value[1] := by rw [← h_obmap]; simp only [Vector.getElem_map]
      have hb2e : Expression.eval env input_var_adapter_op_b_memory_prev_value[2]
          = input_adapter_op_b_memory_prev_value[2] := by rw [← h_obmap]; simp only [Vector.getElem_map]
      have hb3e : Expression.eval env input_var_adapter_op_b_memory_prev_value[3]
          = input_adapter_op_b_memory_prev_value[3] := by rw [← h_obmap]; simp only [Vector.getElem_map]
      have hc0e : Expression.eval env input_var_adapter_op_c_memory_prev_value[0]
          = input_adapter_op_c_memory_prev_value[0] := by rw [← h_ocmap]; simp only [Vector.getElem_map]
      -- The three inverted-`v` encodings, as equations (`v0123 = v012 * (…)`, etc.). `simp [id_eq]`
      -- strips Clean's `id`-wrapped field elements so `linear_combination`/`ring` can synthesize.
      have eq_v01 : v01 = (1 + -cb0 + 1) * 2 * ((1 + -cb1) * 3 + 1) := by
        simp only [id_eq] at h_v01 ⊢; linear_combination h_v01
      have eq_v012 : v012 = v01 * ((1 + -cb2) * 15 + 1) := by
        simp only [id_eq] at h_v012 ⊢; linear_combination h_v012
      have eq_v0123 : v0123 = v012 * ((1 + -cb3) * 255 + 1) := by
        simp only [id_eq] at h_v0123 ⊢; linear_combination h_v0123
      -- The four limb-split decompositions `b_j * v0123 = hl_j * 65536 + ll_j * v0123` (limbs 2,3 de-gated
      -- by `e14 = is_srl + is_sra = 1`), bridged to the `((65536:ℕ):ZMod p)` form the close lemmas want.
      have h_b0_dec : input_adapter_op_b_memory_prev_value[0] * v0123
          = hl0 * ((65536 : ℕ) : ZMod p) + ll0 * v0123 := by
        have h := h_split0; rw [hb0e] at h; simp only [id_eq] at h ⊢; push_cast; linear_combination h
      have h_b1_dec : input_adapter_op_b_memory_prev_value[1] * v0123
          = hl1 * ((65536 : ℕ) : ZMod p) + ll1 * v0123 := by
        have h := h_split1; rw [hb1e] at h; simp only [id_eq] at h ⊢; push_cast; linear_combination h
      have h_b2_dec : input_adapter_op_b_memory_prev_value[2] * v0123
          = hl2 * ((65536 : ℕ) : ZMod p) + ll2 * v0123 := by
        have h := h_split2; rw [hb2e, h_srl0, hsra] at h; simp only [id_eq] at h ⊢
        push_cast; linear_combination h
      have h_b3_dec : input_adapter_op_b_memory_prev_value[3] * v0123
          = hl3 * ((65536 : ℕ) : ZMod p) + ll3 * v0123 := by
        have h := h_split3; rw [hb3e, h_srl0, hsra] at h; simp only [id_eq] at h ⊢
        push_cast; linear_combination h
      -- Normalise the goal's shift count `c0.val % 64` to the `c_bits` sum (`is_mod_64`).
      have h_cbsum_lt := cbsum_val_lt_64 b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
      have h_c0mod : input_adapter_op_c_memory_prev_value[0].val % 64
          = (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32 : ZMod p).val := by
        refine ShiftRightMath.is_mod_64 h_cbsum_lt (by simpa using h_rs2U 0) ?_
        have he := hbyte_fact h_byte0
        rw [hc0e] at he
        have h10v : ((10 : ZMod p)).val = 10 := by
          rw [show (10 : ZMod p) = ((10 : ℕ) : ZMod p) by push_cast; rfl]
          exact ZMod.val_natCast_of_lt (by have := Fact.out (p := 2 ^ 17 < p); omega)
        rw [h10v, show (2 : ℕ) ^ 10 = 1024 by norm_num] at he
        rw [c0mod_inv_bridge]; exact he
      -- Bridge the byte-pull range facts to the `srl_close_su16_*_case` exponent form.
      rw [cb4sum_natCast] at lt_ll0 lt_ll1 lt_ll2 lt_ll3
      rw [cb4sum_sub_natCast] at lt_lh0 lt_lh1 lt_lh2 lt_lh3
      have hp17 : 2 ^ 17 < p := Fact.out
      have hne2 : (2 : ZMod p) ≠ 0 := by
        intro h; have := val_2_zmod_p (p := p); rw [h, ZMod.val_zero] at this; exact absurd this (by norm_num)
      have hne3 : (3 : ZMod p) ≠ 0 := by
        intro h; have h3 : (3 : ZMod p).val = 3 := by
          rw [show (3 : ZMod p) = ((3 : ℕ) : ZMod p) by push_cast; rfl]
          exact ZMod.val_natCast_of_lt (by omega)
        rw [h, ZMod.val_zero] at h3; exact absurd h3 (by norm_num)
      -- Alias the shift-result columns.
      set su0 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4) with hsu0_def
      set su1 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 1) with hsu1_def
      set su2 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 2) with hsu2_def
      set su3 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 3) with hsu3_def
      set lr0 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4) with hlr0_def
      set lr1 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 1) with hlr1_def
      set lr2 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 2) with hlr2_def
      set lr3 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 3) with hlr3_def
      set smv := env.get (i₀ + 4 + 1 + 1 + 6) with hsmv_def
      clear_value su0 su1 su2 su3 lr0 lr1 lr2 lr3 smv
      -- One-hot of the byte-shift selectors; the limb_result decompositions; `sra_msb_v0123 = 0`.
      have honehot1 : su0 + su1 + su2 + su3 = 1 := by
        have hh := h_onehot; rw [hsum1] at hh; simp only [id_eq] at hh ⊢; linear_combination hh
      have eq_lr0 : lr0 = hl0 + ll1 * v0123 := by
        simp only [id_eq] at h_lr0 ⊢; linear_combination h_lr0
      have eq_lr1 : lr1 = hl1 + ll2 * v0123 := by
        simp only [id_eq] at h_lr1 ⊢; linear_combination h_lr1
      have eq_lr2 : lr2 = hl2 + ll3 * v0123 := by
        simp only [id_eq] at h_lr2 ⊢; linear_combination h_lr2
      have eq_lr3 : lr3 = hl3 := by simp only [id_eq] at h_lr3 ⊢; linear_combination h_lr3
      have eq_smv : smv = env.get (i₀ + 4) * v0123 := by
        have hh := h_smv; simp only [id_eq] at hh ⊢; linear_combination hh
      -- `rs1` eta, so the goal's `rs1.toBitVec64` matches the close lemma's `#v[rs1[0],…]`.
      have hrs1eta : (input_adapter_op_b_memory_prev_value : Word (ZMod p))
          = #v[input_adapter_op_b_memory_prev_value[0], input_adapter_op_b_memory_prev_value[1],
              input_adapter_op_b_memory_prev_value[2], input_adapter_op_b_memory_prev_value[3]] := by
        apply Vector.ext; intro i hi; interval_cases i <;> rfl
      -- Derive `b_msb = if op_b[3] ≥ 2^15 then 1 else 0` from the `U16MSBOperation` gadget `Spec`.
      have h_msb_eq : env.get (i₀ + 4)
          = if input_adapter_op_b_memory_prev_value[3].val ≥ 32768 then 1 else 0 := by
        have hsp := (h_msb1 ⟨fun _ => by rw [hb3e]; exact h_rs1U 3, bool_of_mul_pred h_sra_b⟩).2 hsra
        rwa [hb3e] at hsp
      have h_bvmsb : (Word.toBitVec64 input_adapter_op_b_memory_prev_value).msb
          = decide (input_adapter_op_b_memory_prev_value[3].val ≥ 32768) :=
        ShiftRightMath.toBitVec64_msb_eq_b3_ge h_rs1U
      by_cases hb3 : input_adapter_op_b_memory_prev_value[3].val ≥ 32768
      · -- b_msb = 1 (negative): sign-extended arithmetic shift.
        have hbmsb1 : env.get (i₀ + 4) = 1 := by rw [h_msb_eq, if_pos hb3]
        have hmsbtrue : (Word.toBitVec64 input_adapter_op_b_memory_prev_value).msb = true := by
          rw [h_bvmsb]; simp [hb3]
        have eq_smv1 : smv = v0123 := by rw [eq_smv, hbmsb1, one_mul]
        refine sra_div_to_bitvec_true _ _ _ h_rs2U hmsbtrue ?_
        rw [hcolsa, hrs1eta, h_c0mod]
        rcases b_cb5 with hcb5 | hcb5 <;> rcases b_cb4 with hcb4 | hcb4
        · -- byte_shift = 0: su0 = 1, sign-extended.
          have su1z : su1 = 0 := by
            have hh := h_s1w; rw [hcb4, hcb5] at hh; simp at hh
            first
              | exact hh
              | exact hh.resolve_right (by norm_num [hne2, hne3])
          have su2z : su2 = 0 := by
            have hh := h_s2w; rw [hcb4, hcb5] at hh; simp at hh
            first
              | exact hh
              | exact hh.resolve_right (by norm_num [hne2, hne3])
          have su3z : su3 = 0 := by
            have hh := h_s3w; rw [hcb4, hcb5] at hh; simp at hh
            first
              | exact hh
              | exact hh.resolve_right (by norm_num [hne2, hne3])
          have su0o : su0 = 1 := by
            have hh := honehot1; rw [su1z, su2z, su3z] at hh; simpa using hh
          have a0e : env.get i₀ = lr0 := by
            have hh := h_o0; rw [h_srl0, hsra, su0o] at hh; simp only [id_eq] at hh ⊢
            linear_combination hh
          have a1e : env.get (i₀ + 1) = lr1 := by
            have hh := h_o1; rw [h_srl0, hsra, su0o] at hh; simp only [id_eq] at hh ⊢
            linear_combination hh
          have a2e : env.get (i₀ + 2) = lr2 := by
            have hh := h_o2; rw [h_srl0, hsra, su0o] at hh; simp only [id_eq] at hh ⊢
            linear_combination hh
          have a3e : env.get (i₀ + 3) = lr3 + (((65536 : ℕ) : ZMod p) - v0123) := by
            have hh := h_o3; rw [h_srl0, hsra, su0o, hbmsb1, eq_smv1] at hh
            simp only [id_eq] at hh ⊢; push_cast; linear_combination hh
          rw [a0e, a1e, a2e, a3e, eq_lr0, eq_lr1, eq_lr2, eq_lr3]
          exact ShiftRightMath.sra_dispatch_0_msb1 b_cb0 b_cb1 b_cb2 b_cb3 hcb4 hcb5 eq_v01 eq_v012 eq_v0123
            lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3 h_b0_dec h_b1_dec h_b2_dec h_b3_dec
        · -- byte_shift = 1: su1 = 1, sign-extended.
          have su0z : su0 = 0 := by
            have hh := h_s0w; rw [hcb4, hcb5] at hh; simp at hh
            first
              | exact hh
              | exact hh.resolve_right (by norm_num [hne2, hne3])
          have su2z : su2 = 0 := by
            have hh := h_s2w; rw [hcb4, hcb5] at hh; simp at hh
            first
              | exact hh
              | exact hh.resolve_right (by norm_num [hne2, hne3])
          have su3z : su3 = 0 := by
            have hh := h_s3w; rw [hcb4, hcb5] at hh; simp at hh
            first
              | exact hh
              | exact hh.resolve_right (by norm_num [hne2, hne3])
          have su1o : su1 = 1 := by
            have hh := honehot1; rw [su0z, su2z, su3z] at hh; simpa using hh
          have a0e : env.get i₀ = lr1 := by
            have hh := h_o4; rw [h_srl0, hsra, su1o] at hh; simp only [id_eq] at hh ⊢
            linear_combination hh
          have a1e : env.get (i₀ + 1) = lr2 := by
            have hh := h_o5; rw [h_srl0, hsra, su1o] at hh; simp only [id_eq] at hh ⊢
            linear_combination hh
          have a2e : env.get (i₀ + 2) = lr3 + (((65536 : ℕ) : ZMod p) - v0123) := by
            have hh := h_o6; rw [h_srl0, hsra, su1o, hbmsb1, eq_smv1] at hh
            simp only [id_eq] at hh ⊢; push_cast; linear_combination hh
          have a3e : env.get (i₀ + 3) = ((65535 : ℕ) : ZMod p) := by
            have hh := h_o7; rw [h_srl0, hsra, su1o, hbmsb1] at hh
            simp only [id_eq] at hh ⊢; push_cast; linear_combination hh
          rw [a0e, a1e, a2e, a3e, eq_lr1, eq_lr2, eq_lr3]
          exact ShiftRightMath.sra_dispatch_1_msb1 b_cb0 b_cb1 b_cb2 b_cb3 hcb4 hcb5 eq_v01 eq_v012 eq_v0123
            lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3 h_b0_dec h_b1_dec h_b2_dec h_b3_dec
        · -- byte_shift = 2: su2 = 1, sign-extended.
          have su0z : su0 = 0 := by
            have hh := h_s0w; rw [hcb4, hcb5, h_srl0, hsra] at hh; simp at hh
            first
              | exact hh
              | exact hh.resolve_right (by norm_num [hne2, hne3])
          have su1z : su1 = 0 := by
            have hh := h_s1w; rw [hcb4, hcb5, h_srl0, hsra] at hh; simp at hh
            first
              | exact hh
              | exact hh.resolve_right (by norm_num [hne2, hne3])
          have su3z : su3 = 0 := by
            have hh := h_s3w; rw [hcb4, hcb5, h_srl0, hsra] at hh; simp at hh
            first
              | exact hh
              | exact hh.resolve_right (by norm_num [hne2, hne3])
          have su2o : su2 = 1 := by
            have hh := honehot1; rw [su0z, su1z, su3z] at hh; simpa using hh
          have a0e : env.get i₀ = lr2 := by
            have hh := h_o8; rw [h_srl0, hsra, su2o] at hh; simp only [id_eq] at hh ⊢
            linear_combination hh
          have a1e : env.get (i₀ + 1) = lr3 + (((65536 : ℕ) : ZMod p) - v0123) := by
            have hh := h_o9; rw [h_srl0, hsra, su2o, hbmsb1, eq_smv1] at hh
            simp only [id_eq] at hh ⊢; push_cast; linear_combination hh
          have a2e : env.get (i₀ + 2) = ((65535 : ℕ) : ZMod p) := by
            have hh := h_o10; rw [h_srl0, hsra, su2o, hbmsb1] at hh
            simp only [id_eq] at hh ⊢; push_cast; linear_combination hh
          have a3e : env.get (i₀ + 3) = ((65535 : ℕ) : ZMod p) := by
            have hh := h_o11; rw [h_srl0, hsra, su2o, hbmsb1] at hh
            simp only [id_eq] at hh ⊢; push_cast; linear_combination hh
          rw [a0e, a1e, a2e, a3e, eq_lr2, eq_lr3]
          exact ShiftRightMath.sra_dispatch_2_msb1 b_cb0 b_cb1 b_cb2 b_cb3 hcb4 hcb5 eq_v01 eq_v012 eq_v0123
            lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3 h_b0_dec h_b1_dec h_b2_dec h_b3_dec
        · -- byte_shift = 3: su3 = 1, sign-extended.
          have su0z : su0 = 0 := by
            have hh := h_s0w; rw [hcb4, hcb5, h_srl0, hsra] at hh; simp at hh
            first
              | exact hh
              | exact hh.resolve_right (by norm_num [hne2, hne3])
          have su1z : su1 = 0 := by
            have hh := h_s1w; rw [hcb4, hcb5, h_srl0, hsra] at hh; simp at hh
            first
              | exact hh
              | exact hh.resolve_right (by norm_num [hne2, hne3])
          have su2z : su2 = 0 := by
            have hh := h_s2w; rw [hcb4, hcb5, h_srl0, hsra] at hh; simp at hh
            first
              | exact hh
              | exact hh.resolve_right (by norm_num [hne2, hne3])
          have su3o : su3 = 1 := by
            have hh := honehot1; rw [su0z, su1z, su2z] at hh; simpa using hh
          have a0e : env.get i₀ = lr3 + (((65536 : ℕ) : ZMod p) - v0123) := by
            have hh := h_o12; rw [h_srl0, hsra, su3o, hbmsb1, eq_smv1] at hh
            simp only [id_eq] at hh ⊢; push_cast; linear_combination hh
          have a1e : env.get (i₀ + 1) = ((65535 : ℕ) : ZMod p) := by
            have hh := h_o13; rw [h_srl0, hsra, su3o, hbmsb1] at hh
            simp only [id_eq] at hh ⊢; push_cast; linear_combination hh
          have a2e : env.get (i₀ + 2) = ((65535 : ℕ) : ZMod p) := by
            have hh := h_o14; rw [h_srl0, hsra, su3o, hbmsb1] at hh
            simp only [id_eq] at hh ⊢; push_cast; linear_combination hh
          have a3e : env.get (i₀ + 3) = ((65535 : ℕ) : ZMod p) := by
            have hh := h_o15; rw [h_srl0, hsra, su3o, hbmsb1] at hh
            simp only [id_eq] at hh ⊢; push_cast; linear_combination hh
          rw [a0e, a1e, a2e, a3e, eq_lr3]
          exact ShiftRightMath.sra_dispatch_3_msb1 b_cb0 b_cb1 b_cb2 b_cb3 hcb4 hcb5 eq_v01 eq_v012 eq_v0123
            lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3 h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · -- b_msb = 0 (non-negative): arithmetic shift = logical shift (the SRL dispatch verbatim).
        have h_bmsb0 : env.get (i₀ + 4) = 0 := by rw [h_msb_eq, if_neg hb3]
        have hsmv0 : smv = 0 := by rw [eq_smv, h_bmsb0, zero_mul]
        have hmsbfalse : (Word.toBitVec64 input_adapter_op_b_memory_prev_value).msb = false := by
          rw [h_bvmsb]; simp [hb3]
        refine sra_div_to_bitvec_false _ _ _ h_rs2U hmsbfalse ?_
        rw [hcolsa, hrs1eta, h_c0mod]
        rcases b_cb5 with hcb5 | hcb5 <;> rcases b_cb4 with hcb4 | hcb4
        · -- byte_shift = 0 (cb4 = cb5 = 0): su0 = 1, the result is the within-byte limb_result word.
          have su1z : su1 = 0 := by have hh := h_s1w; rw [hcb4, hcb5] at hh; simpa using hh
          have su2z : su2 = 0 := by
            have hh := h_s2w; rw [hcb4, hcb5] at hh; simp at hh; exact hh.resolve_right hne2
          have su3z : su3 = 0 := by
            have hh := h_s3w; rw [hcb4, hcb5] at hh; simp at hh; exact hh.resolve_right hne3
          have su0o : su0 = 1 := by
            have hh := honehot1; rw [su1z, su2z, su3z] at hh; simpa using hh
          have a0lr : env.get i₀ = lr0 := by
            have hh := h_o0; rw [h_srl0, hsra, su0o] at hh; simp only [id_eq] at hh ⊢
            linear_combination hh
          have a1lr : env.get (i₀ + 1) = lr1 := by
            have hh := h_o1; rw [h_srl0, hsra, su0o] at hh; simp only [id_eq] at hh ⊢
            linear_combination hh
          have a2lr : env.get (i₀ + 2) = lr2 := by
            have hh := h_o2; rw [h_srl0, hsra, su0o] at hh; simp only [id_eq] at hh ⊢
            linear_combination hh
          have a3lr : env.get (i₀ + 3) = lr3 := by
            have hh := h_o3; rw [h_srl0, hsra, su0o, h_bmsb0, hsmv0] at hh
            simp only [id_eq] at hh ⊢; linear_combination hh
          rw [a0lr, a1lr, a2lr, a3lr, eq_lr0, eq_lr1, eq_lr2, eq_lr3]
          exact ShiftRightMath.srl_dispatch_0 b_cb0 b_cb1 b_cb2 b_cb3 hcb4 hcb5 eq_v01 eq_v012 eq_v0123
            lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3 h_b0_dec h_b1_dec h_b2_dec h_b3_dec
        · -- byte_shift = 1 (cb4 = 1, cb5 = 0): su1 = 1, result shifted down one limb.
          have su0z : su0 = 0 := by
            have hh := h_s0w; rw [hcb4, hcb5] at hh; simp at hh
            first
              | exact hh
              | exact hh.resolve_right (by norm_num [hne2, hne3])
          have su2z : su2 = 0 := by
            have hh := h_s2w; rw [hcb4, hcb5] at hh; simp at hh
            first
              | exact hh
              | exact hh.resolve_right (by norm_num [hne2, hne3])
          have su3z : su3 = 0 := by
            have hh := h_s3w; rw [hcb4, hcb5] at hh; simp at hh
            first
              | exact hh
              | exact hh.resolve_right (by norm_num [hne2, hne3])
          have su1o : su1 = 1 := by
            have hh := honehot1; rw [su0z, su2z, su3z] at hh; simpa using hh
          have a0lr : env.get i₀ = lr1 := by
            have hh := h_o4; rw [h_srl0, hsra, su1o] at hh; simp only [id_eq] at hh ⊢
            linear_combination hh
          have a1lr : env.get (i₀ + 1) = lr2 := by
            have hh := h_o5; rw [h_srl0, hsra, su1o] at hh; simp only [id_eq] at hh ⊢
            linear_combination hh
          have a2lr : env.get (i₀ + 2) = lr3 := by
            have hh := h_o6; rw [h_srl0, hsra, su1o, h_bmsb0, hsmv0] at hh; simp only [id_eq] at hh ⊢
            linear_combination hh
          have a3z : env.get (i₀ + 3) = 0 := by
            have hh := h_o7; rw [h_srl0, hsra, su1o, h_bmsb0] at hh; simp only [id_eq] at hh ⊢
            linear_combination hh
          rw [a0lr, a1lr, a2lr, a3z, eq_lr1, eq_lr2, eq_lr3]
          exact ShiftRightMath.srl_dispatch_1 b_cb0 b_cb1 b_cb2 b_cb3 hcb4 hcb5 eq_v01 eq_v012 eq_v0123
            lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3 h_b0_dec h_b1_dec h_b2_dec h_b3_dec
        · -- byte_shift = 2 (cb4 = 0, cb5 = 1): su2 = 1, result shifted down two limbs.
          have su0z : su0 = 0 := by
            have hh := h_s0w; rw [hcb4, hcb5, h_srl0, hsra] at hh; simp at hh
            first
              | exact hh
              | exact hh.resolve_right (by norm_num [hne2, hne3])
          have su1z : su1 = 0 := by
            have hh := h_s1w; rw [hcb4, hcb5, h_srl0, hsra] at hh; simp at hh
            first
              | exact hh
              | exact hh.resolve_right (by norm_num [hne2, hne3])
          have su3z : su3 = 0 := by
            have hh := h_s3w; rw [hcb4, hcb5, h_srl0, hsra] at hh; simp at hh
            first
              | exact hh
              | exact hh.resolve_right (by norm_num [hne2, hne3])
          have su2o : su2 = 1 := by
            have hh := honehot1; rw [su0z, su1z, su3z] at hh; simpa using hh
          have a0lr : env.get i₀ = lr2 := by
            have hh := h_o8; rw [h_srl0, hsra, su2o] at hh; simp only [id_eq] at hh ⊢
            linear_combination hh
          have a1lr : env.get (i₀ + 1) = lr3 := by
            have hh := h_o9; rw [h_srl0, hsra, su2o, h_bmsb0, hsmv0] at hh; simp only [id_eq] at hh ⊢
            linear_combination hh
          have a2z : env.get (i₀ + 2) = 0 := by
            have hh := h_o10; rw [h_srl0, hsra, su2o, h_bmsb0] at hh; simp only [id_eq] at hh ⊢
            linear_combination hh
          have a3z : env.get (i₀ + 3) = 0 := by
            have hh := h_o11; rw [h_srl0, hsra, su2o, h_bmsb0] at hh; simp only [id_eq] at hh ⊢
            linear_combination hh
          rw [a0lr, a1lr, a2z, a3z, eq_lr2, eq_lr3]
          exact ShiftRightMath.srl_dispatch_2 b_cb0 b_cb1 b_cb2 b_cb3 hcb4 hcb5 eq_v01 eq_v012 eq_v0123
            lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3 h_b0_dec h_b1_dec h_b2_dec h_b3_dec
        · -- byte_shift = 3 (cb4 = 1, cb5 = 1): su3 = 1, result shifted down three limbs.
          have su0z : su0 = 0 := by
            have hh := h_s0w; rw [hcb4, hcb5, h_srl0, hsra] at hh; simp at hh
            first
              | exact hh
              | exact hh.resolve_right (by norm_num [hne2, hne3])
          have su1z : su1 = 0 := by
            have hh := h_s1w; rw [hcb4, hcb5, h_srl0, hsra] at hh; simp at hh
            first
              | exact hh
              | exact hh.resolve_right (by norm_num [hne2, hne3])
          have su2z : su2 = 0 := by
            have hh := h_s2w; rw [hcb4, hcb5, h_srl0, hsra] at hh; simp at hh
            first
              | exact hh
              | exact hh.resolve_right (by norm_num [hne2, hne3])
          have su3o : su3 = 1 := by
            have hh := honehot1; rw [su0z, su1z, su2z] at hh; simpa using hh
          have a0lr : env.get i₀ = lr3 := by
            have hh := h_o12; rw [h_srl0, hsra, su3o, h_bmsb0, hsmv0] at hh; simp only [id_eq] at hh ⊢
            linear_combination hh
          have a1z : env.get (i₀ + 1) = 0 := by
            have hh := h_o13; rw [h_srl0, hsra, su3o, h_bmsb0] at hh; simp only [id_eq] at hh ⊢
            linear_combination hh
          have a2z : env.get (i₀ + 2) = 0 := by
            have hh := h_o14; rw [h_srl0, hsra, su3o, h_bmsb0] at hh; simp only [id_eq] at hh ⊢
            linear_combination hh
          have a3z : env.get (i₀ + 3) = 0 := by
            have hh := h_o15; rw [h_srl0, hsra, su3o, h_bmsb0] at hh; simp only [id_eq] at hh ⊢
            linear_combination hh
          rw [a0lr, a1z, a2z, a3z, eq_lr3]
          exact ShiftRightMath.srl_dispatch_3 b_cb0 b_cb1 b_cb2 b_cb3 hcb4 hcb5 eq_v01 eq_v012 eq_v0123
            lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3 h_b0_dec h_b1_dec h_b2_dec h_b3_dec
  -- CPUState / ALUTypeReader only assume `is_real` binary (from the in-circuit gate).
  case cpuA => exact bool_of_mul_pred h_realgate
  case aluA => exact Or.inr (bool_of_mul_pred h_realgate)
  -- The three `U16MSBOperation` assumptions need `a.val < 2^16` on real sub-rows. For `msb1`/`msb2`
  -- (the `op_b[3]`/`op_b[1]` sign reads) this is `isU64 op_b`; for `msb3` (the result limb `a[1]`) it is
  -- the output bound, re-derived in `case msb3A` from the gate-active byte pulls (see that block).
  case msb1A =>
    obtain ⟨h_rs1U, -⟩ := h_assumptions
    obtain ⟨-, -, -, -, -, -, ⟨h_obmap, -, -⟩, -, -, -⟩ := h_input
    exact Or.inr ⟨fun _ => by
        rw [show Expression.eval env input_var_adapter_op_b_memory_prev_value[3]
              = input_adapter_op_b_memory_prev_value[3] by rw [← h_obmap]; simp only [Vector.getElem_map]]
        exact h_rs1U 3,
      bool_of_mul_pred h_sra_b⟩
  case msb2A =>
    obtain ⟨h_rs1U, -⟩ := h_assumptions
    obtain ⟨-, -, -, -, -, -, ⟨h_obmap, -, -⟩, -, -, -⟩ := h_input
    exact Or.inr ⟨fun _ => by
        rw [show Expression.eval env input_var_adapter_op_b_memory_prev_value[1]
              = input_adapter_op_b_memory_prev_value[1] by rw [← h_obmap]; simp only [Vector.getElem_map]]
        exact h_rs1U 1,
      bool_of_mul_pred h_sraw_b⟩
  case msb3A =>
    -- The `srw_msb` gadget reads the result limb `a[1]` (gate `is_srlw + is_sraw`). Its `Assumptions`
    -- need `a[1] < 2^16` on a real word-variant row — the output bound, re-derived here without the
    -- active-flag `Spec` context: the gate forces `is_srl = is_sra = 0` (so the byte pulls fire), then
    -- a SRLW/SRAW split reads `a[1]` off the (gate-active) output asserts and closes via the limb bounds.
    refine Or.inr ⟨fun hgate => ?_, pair_flag (bool_of_mul_pred h_srl_b) (bool_of_mul_pred h_sra_b)
      (bool_of_mul_pred h_srlw_b) (bool_of_mul_pred h_sraw_b) (bool_of_mul_pred h_sum_b)⟩
    obtain ⟨h_srl0, h_sra0, hsum1⟩ := srlw_sraw_gate (bool_of_mul_pred h_srl_b)
      (bool_of_mul_pred h_sra_b) (bool_of_mul_pred h_srlw_b) (bool_of_mul_pred h_sraw_b)
      (bool_of_mul_pred h_sum_b) hgate
    obtain ⟨h_rs1U, -⟩ := h_assumptions
    -- === Stage A (variant-agnostic given `is_srl = is_sra = 0`): byte ranges + limb reassembly. ===
    set cb0 := env.get (i₀ + 4 + 1 + 1) with hcb0_def
    set cb1 := env.get (i₀ + 4 + 1 + 1 + 1) with hcb1_def
    set cb2 := env.get (i₀ + 4 + 1 + 1 + 2) with hcb2_def
    set cb3 := env.get (i₀ + 4 + 1 + 1 + 3) with hcb3_def
    set cb4 := env.get (i₀ + 4 + 1 + 1 + 4) with hcb4_def
    set cb5 := env.get (i₀ + 4 + 1 + 1 + 5) with hcb5_def
    set ll0 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3) with hll0_def
    set ll1 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 1) with hll1_def
    set ll2 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 2) with hll2_def
    set ll3 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 3) with hll3_def
    set hl0 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4) with hhl0_def
    set hl1 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 1) with hhl1_def
    set hl2 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 2) with hhl2_def
    set hl3 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 3) with hhl3_def
    have hsumneg : -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4)
        + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)
        + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2)
        + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) = -1 := by rw [hsum1]
    have hbyte_fact : ∀ {v w : ZMod p},
        (-(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4)
            + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)
            + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2)
            + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) = -1 →
          byteChannel.Guarantees (⟨6, v, w, 0⟩ : ByteRow (ZMod p)) env.data) → v.val < 2 ^ w.val := by
      intro v w hb
      exact byteRowSpec_range_val (hb hsumneg)
    have lt_ll0 := hbyte_fact h_byte1
    have lt_lh0 := hbyte_fact h_byte2
    have lt_ll1 := hbyte_fact h_byte3
    have lt_lh1 := hbyte_fact h_byte4
    have lt_ll2 := hbyte_fact h_byte5
    have lt_lh2 := hbyte_fact h_byte6
    have lt_ll3 := hbyte_fact h_byte7
    have lt_lh3 := hbyte_fact h_byte8
    have b_cb0 := bool_of_mul_pred h_b0
    have b_cb1 := bool_of_mul_pred h_b1
    have b_cb2 := bool_of_mul_pred h_b2
    have b_cb3 := bool_of_mul_pred h_b3
    have b_cb4 := bool_of_mul_pred h_b4
    have b_cb5 := bool_of_mul_pred h_b5
    set v0123 := env.get (i₀ + 4 + 1 + 1 + 6 + 1) with hv0123_def
    set v012 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 1) with hv012_def
    set v01 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 2) with hv01_def
    clear_value cb0 cb1 cb2 cb3 cb4 cb5 ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 v0123 v012 v01
    obtain ⟨-, -, -, -, -, -, ⟨h_obmap, -, -⟩, -, -, -⟩ := h_input
    have hb1e : Expression.eval env input_var_adapter_op_b_memory_prev_value[1]
        = input_adapter_op_b_memory_prev_value[1] := by rw [← h_obmap]; simp [Vector.getElem_map]
    have hb2e : Expression.eval env input_var_adapter_op_b_memory_prev_value[2]
        = input_adapter_op_b_memory_prev_value[2] := by rw [← h_obmap]; simp [Vector.getElem_map]
    have eq_v01 : v01 = (1 + -cb0 + 1) * 2 * ((1 + -cb1) * 3 + 1) := by
      simp only [id_eq] at h_v01 ⊢; linear_combination h_v01
    have eq_v012 : v012 = v01 * ((1 + -cb2) * 15 + 1) := by
      simp only [id_eq] at h_v012 ⊢; linear_combination h_v012
    have eq_v0123 : v0123 = v012 * ((1 + -cb3) * 255 + 1) := by
      simp only [id_eq] at h_v0123 ⊢; linear_combination h_v0123
    have h_split2_dec : hl2 * 65536 + ll2 * v0123 = 0 := by
      have h := h_split2; rw [hb2e, h_srl0, h_sra0] at h; simp only [id_eq] at h ⊢
      linear_combination -h
    rw [cb4sum_natCast] at lt_ll0 lt_ll1 lt_ll2 lt_ll3
    rw [cb4sum_sub_natCast] at lt_lh0 lt_lh1 lt_lh2 lt_lh3
    have hp17 : 2 ^ 17 < p := Fact.out
    have hne2 : (2 : ZMod p) ≠ 0 := by
      intro h; have := val_2_zmod_p (p := p); rw [h, ZMod.val_zero] at this; exact absurd this (by norm_num)
    have hne3 : (3 : ZMod p) ≠ 0 := by
      intro h; have h3 : (3 : ZMod p).val = 3 := by
        rw [show (3 : ZMod p) = ((3 : ℕ) : ZMod p) by push_cast; rfl]
        exact ZMod.val_natCast_of_lt (by omega)
      rw [h, ZMod.val_zero] at h3; exact absurd h3 (by norm_num)
    obtain ⟨-, h_ll2_0⟩ := ShiftRightMath.higher_lower_zero b_cb0 b_cb1 b_cb2 b_cb3
      eq_v01 eq_v012 eq_v0123 lt_lh2 lt_ll2 h_split2_dec
    set su0 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4) with hsu0_def
    set su1 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 1) with hsu1_def
    set su2 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 2) with hsu2_def
    set su3 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 3) with hsu3_def
    set lr1 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 1) with hlr1_def
    set smv := env.get (i₀ + 4 + 1 + 1 + 6) with hsmv_def
    clear_value su0 su1 su2 su3 lr1 smv
    have honehot1 : su0 + su1 + su2 + su3 = 1 := by
      have hh := h_onehot; rw [hsum1] at hh; simp only [id_eq] at hh ⊢; linear_combination hh
    have eq_lr1 : lr1 = hl1 + ll2 * v0123 := by
      simp only [id_eq] at h_lr1 ⊢; linear_combination h_lr1
    -- === Variant split: read `a[1]` off the (gate-active) output asserts `h_w*`. ===
    rcases bool_of_mul_pred h_srlw_b with h_srlw0 | hsrlw
    · -- SRAW (`is_srlw = 0 ⇒ is_sraw = 1`): arithmetic word shift; `b_msb` = the low-32 sign bit.
      have hsraw : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3) = 1 := by
        rw [h_srlw0] at hgate; linear_combination hgate
      have h_msb_eq2 : env.get (i₀ + 4)
          = if input_adapter_op_b_memory_prev_value[1].val ≥ 32768 then 1 else 0 := by
        have hsp := (h_msb2 ⟨fun _ => by rw [hb1e]; exact h_rs1U 1, bool_of_mul_pred h_sraw_b⟩).2 hsraw
        rwa [hb1e] at hsp
      have eq_smv : smv = env.get (i₀ + 4) * v0123 := by
        have hh := h_smv; simp only [id_eq] at hh ⊢; linear_combination hh
      by_cases hb1 : input_adapter_op_b_memory_prev_value[1].val ≥ 32768
      · -- low-32 negative: `a[1] = limb_result[1] + sraFill` (bs0) or `65535` (bs1).
        have hbmsb1 : env.get (i₀ + 4) = 1 := by rw [h_msb_eq2, if_pos hb1]
        have eq_smv1 : smv = v0123 := by rw [eq_smv, hbmsb1, one_mul]
        rcases b_cb4 with hcb4 | hcb4
        · have su1z : su1 = 0 := by
            have hh := h_s1w; rw [hcb4, h_srl0, h_sra0] at hh; simp at hh
            first | exact hh | exact hh.resolve_right (by norm_num [hne2, hne3])
          have su2z : su2 = 0 := by
            have hh := h_s2w; rw [hcb4, h_srl0, h_sra0] at hh; simp at hh
            first | exact hh | exact hh.resolve_right (by norm_num [hne2, hne3])
          have su3z : su3 = 0 := by
            have hh := h_s3w; rw [hcb4, h_srl0, h_sra0] at hh; simp at hh
            first | exact hh | exact hh.resolve_right (by norm_num [hne2, hne3])
          have su0o : su0 = 1 := by
            have hh := honehot1; rw [su1z, su2z, su3z] at hh; simpa using hh
          have ha1 : env.get (i₀ + 1) = lr1 + (((65536 : ℕ) : ZMod p) - v0123) := by
            have hh := h_w1; rw [hsraw, h_srlw0, su0o, hbmsb1, eq_smv1] at hh
            simp only [id_eq] at hh ⊢; push_cast; linear_combination hh
          rw [ha1, eq_lr1, h_ll2_0, zero_mul, add_zero]
          exact ShiftRightMath.sign_fill_lt b_cb0 b_cb1 b_cb2 b_cb3 eq_v01 eq_v012 eq_v0123 lt_lh1
        · have su0z : su0 = 0 := by
            have hh := h_s0w; rw [hcb4, h_srl0, h_sra0] at hh; simp at hh
            first | exact hh | exact hh.resolve_right (by norm_num [hne2, hne3])
          have su2z : su2 = 0 := by
            have hh := h_s2w; rw [hcb4, h_srl0, h_sra0] at hh; simp at hh
            first | exact hh | exact hh.resolve_right (by norm_num [hne2, hne3])
          have su3z : su3 = 0 := by
            have hh := h_s3w; rw [hcb4, h_srl0, h_sra0] at hh; simp at hh
            first | exact hh | exact hh.resolve_right (by norm_num [hne2, hne3])
          have su1o : su1 = 1 := by
            have hh := honehot1; rw [su0z, su2z, su3z] at hh; simpa using hh
          have ha1 : env.get (i₀ + 1) = ((65535 : ℕ) : ZMod p) := by
            have hh := h_w3; rw [hsraw, h_srlw0, su1o, hbmsb1] at hh
            simp only [id_eq] at hh ⊢; push_cast; linear_combination hh
          rw [ha1, ZMod.val_natCast_of_lt (by omega : (65535 : ℕ) < p)]; omega
      · -- low-32 non-negative: identical to SRLW (`a[1] = limb_result[1]` (bs0) or `0` (bs1)).
        have hbmsb0 : env.get (i₀ + 4) = 0 := by rw [h_msb_eq2, if_neg hb1]
        have hsmv0 : smv = 0 := by rw [eq_smv, hbmsb0, zero_mul]
        rcases b_cb4 with hcb4 | hcb4
        · have su1z : su1 = 0 := by
            have hh := h_s1w; rw [hcb4, h_srl0, h_sra0] at hh; simp at hh
            first | exact hh | exact hh.resolve_right (by norm_num [hne2, hne3])
          have su2z : su2 = 0 := by
            have hh := h_s2w; rw [hcb4, h_srl0, h_sra0] at hh; simp at hh
            first | exact hh | exact hh.resolve_right (by norm_num [hne2, hne3])
          have su3z : su3 = 0 := by
            have hh := h_s3w; rw [hcb4, h_srl0, h_sra0] at hh; simp at hh
            first | exact hh | exact hh.resolve_right (by norm_num [hne2, hne3])
          have su0o : su0 = 1 := by
            have hh := honehot1; rw [su1z, su2z, su3z] at hh; simpa using hh
          have ha1 : env.get (i₀ + 1) = lr1 := by
            have hh := h_w1; rw [hsraw, h_srlw0, su0o, hbmsb0, hsmv0] at hh
            simp only [id_eq] at hh ⊢; linear_combination hh
          rw [ha1, eq_lr1]
          exact ShiftRightMath.limb_result_lt b_cb0 b_cb1 b_cb2 b_cb3 eq_v01 eq_v012 eq_v0123 lt_lh1 lt_ll2
        · have su0z : su0 = 0 := by
            have hh := h_s0w; rw [hcb4, h_srl0, h_sra0] at hh; simp at hh
            first | exact hh | exact hh.resolve_right (by norm_num [hne2, hne3])
          have su2z : su2 = 0 := by
            have hh := h_s2w; rw [hcb4, h_srl0, h_sra0] at hh; simp at hh
            first | exact hh | exact hh.resolve_right (by norm_num [hne2, hne3])
          have su3z : su3 = 0 := by
            have hh := h_s3w; rw [hcb4, h_srl0, h_sra0] at hh; simp at hh
            first | exact hh | exact hh.resolve_right (by norm_num [hne2, hne3])
          have su1o : su1 = 1 := by
            have hh := honehot1; rw [su0z, su2z, su3z] at hh; simpa using hh
          have ha1 : env.get (i₀ + 1) = 0 := by
            have hh := h_w3; rw [hsraw, h_srlw0, su1o, hbmsb0] at hh
            simp only [id_eq] at hh ⊢; linear_combination hh
          rw [ha1, ZMod.val_zero]; omega
    · -- SRLW (`is_srlw = 1 ⇒ is_sraw = 0`): logical word shift, `b_msb = 0` (no sign fill).
      have h_sraw0 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3) = 0 := by
        rw [hsrlw] at hgate; linear_combination hgate
      have h_bmsb0 : env.get (i₀ + 4) = 0 := by
        have hh := h_msbz; rw [h_srl0, hsrlw] at hh; simpa using hh
      have eq_smv : smv = env.get (i₀ + 4) * v0123 := by
        have hh := h_smv; simp only [id_eq] at hh ⊢; linear_combination hh
      have hsmv0 : smv = 0 := by rw [eq_smv, h_bmsb0, zero_mul]
      rcases b_cb4 with hcb4 | hcb4
      · have su1z : su1 = 0 := by
          have hh := h_s1w; rw [hcb4, h_srl0, h_sra0] at hh; simp at hh
          first | exact hh | exact hh.resolve_right (by norm_num [hne2, hne3])
        have su2z : su2 = 0 := by
          have hh := h_s2w; rw [hcb4, h_srl0, h_sra0] at hh; simp at hh
          first | exact hh | exact hh.resolve_right (by norm_num [hne2, hne3])
        have su3z : su3 = 0 := by
          have hh := h_s3w; rw [hcb4, h_srl0, h_sra0] at hh; simp at hh
          first | exact hh | exact hh.resolve_right (by norm_num [hne2, hne3])
        have su0o : su0 = 1 := by
          have hh := honehot1; rw [su1z, su2z, su3z] at hh; simpa using hh
        have ha1 : env.get (i₀ + 1) = lr1 := by
          have hh := h_w1; rw [hsrlw, h_sraw0, su0o, h_bmsb0, hsmv0] at hh
          simp only [id_eq] at hh ⊢; linear_combination hh
        rw [ha1, eq_lr1]
        exact ShiftRightMath.limb_result_lt b_cb0 b_cb1 b_cb2 b_cb3 eq_v01 eq_v012 eq_v0123 lt_lh1 lt_ll2
      · have su0z : su0 = 0 := by
          have hh := h_s0w; rw [hcb4, h_srl0, h_sra0] at hh; simp at hh
          first | exact hh | exact hh.resolve_right (by norm_num [hne2, hne3])
        have su2z : su2 = 0 := by
          have hh := h_s2w; rw [hcb4, h_srl0, h_sra0] at hh; simp at hh
          first | exact hh | exact hh.resolve_right (by norm_num [hne2, hne3])
        have su3z : su3 = 0 := by
          have hh := h_s3w; rw [hcb4, h_srl0, h_sra0] at hh; simp at hh
          first | exact hh | exact hh.resolve_right (by norm_num [hne2, hne3])
        have su1o : su1 = 1 := by
          have hh := honehot1; rw [su0z, su2z, su3z] at hh; simpa using hh
        have ha1 : env.get (i₀ + 1) = 0 := by
          have hh := h_w3; rw [hsrlw, h_sraw0, su1o, h_bmsb0] at hh
          simp only [id_eq] at hh ⊢; linear_combination hh
        rw [ha1, ZMod.val_zero]; omega

end SP1Clean.ShiftRightChip.SoundSra
