import Lean
import SP1Clean.Proofs.Chips.DivRemChip.Defs
import SP1Clean.Proofs.Chips.DivRemChip.Soundness
import SP1Clean.Proofs.Chips.DivRemChip.Assembly

/-! # `DivRemChip` — the shared `Operations.Requirements` tail (extracted once)

The `?_tail` half of every `DivRemChip` soundness conjunct (the `Operations.Requirements`
obligation) is **byte-identical** across all nine `Soundness/<Op>.lean` files: it is
`Spec`-independent, depending only on `main`/`Assumptions`/`h_holds`. It was being re-elaborated
nine times at 128M heartbeats. Here it is proved **once**, as the `Requirements` half of a
trivial-spec (`fun _ _ _ => True`) `GeneralFormalCircuit.Soundness`, so `circuit_proof_start` sets
up the identical context. Each conjunct now discharges its `?_tail` by projecting
`(requirements_holds …).2`. -/

namespace SP1Clean.DivRemChip

open Circuit
open Extracted (DivRemCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

set_option maxHeartbeats 128000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
/-- The shared `Operations.Requirements` tail of the `DivRemChip` soundness conjuncts, proved once
(the `Spec`-independent second component). `circuit_proof_start` collapses the trivial `True` spec
via `true_and ∈ circuit_norm`, leaving exactly the `Requirements` goal the per-conjunct tail proves. -/
lemma requirements_holds :
    GeneralFormalCircuit.Soundness (ZMod p) main Assumptions
      (fun _ _ _ => True : Inputs (ZMod p) → DivRemCols (ZMod p) → ProverData (ZMod p) → Prop) := by
  circuit_proof_start
  have hbU := h_assumptions.1
  have hcU := h_assumptions.2
  obtain ⟨h_mul_lo, h_mul_hi,
    h_ctq0, h_ctq1, h_ctq2, h_ctq3, h_ctq4, h_ctq5, h_ctq6, h_ctq7,
    h_eqb, h_eqc, h_eqb2, h_eqc2, h_isc0, h_addc, h_addr, h_lt,
    h_msb0, h_msb1, h_msb2, h_msb3, h_msb4, h_msb5, h_msb6, h_cpu, h_rtype, h_own,
    hb_e123, hb_e127, hb_e131, hb_e135, hb_e139, hb_e143, hb_e147, hb_e151,
    hb_absc0, hb_absc1, hb_absc2, hb_absc3, hb_absr0, hb_absr1, hb_absr2, hb_absr3,
    hb_q0, hb_q1, hb_q2, hb_q3, hb_r0, hb_r1, hb_r2, hb_r3,
    hb_ctq0, hb_ctq1, hb_ctq2, hb_ctq3, hb_ctq4, hb_ctq5, hb_ctq6, hb_ctq7,
    hb_e2r1, hb_e2q1⟩ := h_holds
  simp only [ownAsserts] at h_own
  obtain ⟨e13, e15, e17, e19, e20, e21, e22, e23, e29, e35, e41, e47, e48, e49, e51, e54, e57, e59,
    e61, e64, e67, e69, e70, e71, e73, e76, e79, e81, e83, e86, e89, e91, e96, e99, e103, e105, e107,
    e109, e111, e113, e115, e117, e119, e154, e157, e160, e163, e167, e171, e175, e179, e184, e189,
    e194, e199, e204, e209, e214, e219, e225, e228, e230, e232, e234, e236, e238, e240, e242, e244,
    e247, e250, e253, e256, e259, e262, e265, e268, e270, e272, e274, e276, e278, e280, e282, e284,
    e286, e288, e299, e300, e301, e302, e305, e307, e309, e311, e313, e315, e317, e319, e321, e323,
    e325, e327, e329, e331, e333, e335, e337, e339, e341, e343, e345, e347, e349, e351, e353, e355,
    e357, e359, e367, eopa0⟩ := h_own
  · obtain ⟨h_oir, -, -, -, -, -, ⟨h_ob, -, -⟩, -, ⟨h_oc, -, -⟩⟩ := h_input
    set B := i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 with hBdef
    -- the arithmetic operand `c` (witnessed column at `i₀+20..23`), distinct from the read; the IsZeroWord
    -- gadget tests *this* for the divide-by-zero split.
    set cop : Word (ZMod p) :=
        Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 8 + 4 + 4 + 4 + i })
      with hcop
    have hbin : input_is_real = 0 ∨ input_is_real = 1 := by
      have h := e355; simp only [circuit_norm] at h; rw [h_oir] at h; exact bool_of_mul_pred h
    simp only [circuit_norm] at e325 e327 e329 e331 e333 e335 e337 e339 e367
    have bd := bool_of_mul_pred e325; have bdu := bool_of_mul_pred e327
    have br := bool_of_mul_pred e329; have bru := bool_of_mul_pred e331
    have bdw := bool_of_mul_pred e333; have brw := bool_of_mul_pred e335
    have bduw := bool_of_mul_pred e337; have bruw := bool_of_mul_pred e339
    have hvs := flags_val_sum bd bdu br bru bdw brw bduw bruw (by linear_combination -e367)
    have he2 : env.get (i₀ + 4) + env.get (i₀ + 5) + env.get (i₀ + 6) + env.get (i₀ + 7) = 0 ∨
        env.get (i₀ + 4) + env.get (i₀ + 5) + env.get (i₀ + 6) + env.get (i₀ + 7) = 1 :=
      group_binary4 bdw brw bduw bruw (by omega)
    have hsel5 := group_binary4 bdu bru bd br (by omega)
    have hsel6 := group_binary2 bdw brw (by omega)
    have hsel7 := group_binary2 bduw bruw (by omega)
    have hsum567 : env.get (i₀ + 1) + env.get (i₀ + 3) + env.get i₀ + env.get (i₀ + 2)
        + (env.get (i₀ + 4) + env.get (i₀ + 5)) + (env.get (i₀ + 6) + env.get (i₀ + 7)) = 1 := by
      linear_combination -e367
    have hms6 := h_msb6 ⟨fun he2g => isU16_of_byteRowSpec (hb_e2q1 (by linear_combination -he2g)), he2⟩
    have hms5 := h_msb5 ⟨fun he2g => isU16_of_byteRowSpec (hb_e2r1 (by linear_combination -he2g)), he2⟩
    have hquotmsb := hms6.1
    have hremmsb := hms5.1
    have hqcU : input_is_real = 1 → Word.isU64 (Vector.map (Expression.eval env)
        (Vector.mapRange 4 fun i => var { index := i₀ + 8 + i }) : Word (ZMod p)) := by
      intro hr
      have hrneg' : -input_is_real = -1 := by rw [hr]
      simp only [circuit_norm] at e48 e49 e51 e54 e59 e61 e64 e69
      apply Word.isU64_of_cases <;> simp only [circuit_norm, Nat.add_zero]
      · rw [show env.get (i₀ + 8) = env.get (B + 7+8+8+11+11+11+4+4+4+4+4+4+3+2+4+1+1+4)
            from by linear_combination e48]
        exact isU16_of_byteRowSpec (hb_q0 hrneg')
      · rw [show env.get (i₀ + 8 + 1) = env.get (B + 7+8+8+11+11+11+4+4+4+4+4+4+3+2+4+1+1+4+1)
            from by linear_combination e49]
        exact isU16_of_byteRowSpec (hb_q1 hrneg')
      · exact comp_limb_isU16 hsel5 hsel6 hsel7 hsum567 e59 e54 e51
          hquotmsb (isU16_of_byteRowSpec (hb_q2 hrneg'))
      · exact comp_limb_isU16 hsel5 hsel6 hsel7 hsum567 e69 e64 e61
          hquotmsb (isU16_of_byteRowSpec (hb_q3 hrneg'))
    have hrcU : input_is_real = 1 → Word.isU64 (Vector.map (Expression.eval env)
        (Vector.mapRange 4 fun i => var { index := B + 7+8+8+11+11+11+4+4 + i }) : Word (ZMod p)) := by
      intro hr
      have hrneg' : -input_is_real = -1 := by rw [hr]
      simp only [circuit_norm] at e70 e71 e73 e76 e81 e83 e86 e91
      apply Word.isU64_of_cases <;> simp only [circuit_norm, Nat.add_zero]
      · rw [show env.get (B + 7+8+8+11+11+11+4+4)
            = env.get (B + 7+8+8+11+11+11+4+4+4+4+4+4+3+2+4+1+1) from by linear_combination e70]
        exact isU16_of_byteRowSpec (hb_r0 hrneg')
      · rw [show env.get (B + 7+8+8+11+11+11+4+4+1)
            = env.get (B + 7+8+8+11+11+11+4+4+4+4+4+4+3+2+4+1+1+1) from by linear_combination e71]
        exact isU16_of_byteRowSpec (hb_r1 hrneg')
      · exact comp_limb_isU16 hsel5 hsel6 hsel7 hsum567 e81 e76 e73
          hremmsb (isU16_of_byteRowSpec (hb_r2 hrneg'))
      · exact comp_limb_isU16 hsel5 hsel6 hsel7 hsum567 e91 e86 e83
          hremmsb (isU16_of_byteRowSpec (hb_r3 hrneg'))
    have habscU : input_is_real = 1 → Word.isU64 (Vector.map (Expression.eval env)
        (Vector.mapRange 4 fun i => var { index := B + 7+8+8+11+11+11 + i }) : Word (ZMod p)) := by
      intro hr
      have hrneg' : -input_is_real = -1 := by rw [hr]
      apply Word.isU64_of_cases <;> simp only [circuit_norm, Nat.add_zero]
      exacts [isU16_of_byteRowSpec (hb_absc0 hrneg'), isU16_of_byteRowSpec (hb_absc1 hrneg'),
        isU16_of_byteRowSpec (hb_absc2 hrneg'), isU16_of_byteRowSpec (hb_absc3 hrneg')]
    have habsrU : input_is_real = 1 → Word.isU64 (Vector.map (Expression.eval env)
        (Vector.mapRange 4 fun i => var { index := B + 7+8+8+11+11+11+4 + i }) : Word (ZMod p)) := by
      intro hr
      have hrneg' : -input_is_real = -1 := by rw [hr]
      apply Word.isU64_of_cases <;> simp only [circuit_norm, Nat.add_zero]
      exacts [isU16_of_byteRowSpec (hb_absr0 hrneg'), isU16_of_byteRowSpec (hb_absr1 hrneg'),
        isU16_of_byteRowSpec (hb_absr2 hrneg'), isU16_of_byteRowSpec (hb_absr3 hrneg')]
    have hbb1 : Expression.eval env input_var_adapter_op_b_memory_prev_value[1]
        = input_adapter_op_b_memory_prev_value[1] := by rw [← h_ob]; simp [Vector.getElem_map]
    have hcc1 : Expression.eval env input_var_adapter_op_c_memory_prev_value[1]
        = input_adapter_op_c_memory_prev_value[1] := by rw [← h_oc]; simp [Vector.getElem_map]
    have hbb3 : Expression.eval env input_var_adapter_op_b_memory_prev_value[3]
        = input_adapter_op_b_memory_prev_value[3] := by rw [← h_ob]; simp [Vector.getElem_map]
    have hcc3 : Expression.eval env input_var_adapter_op_c_memory_prev_value[3]
        = input_adapter_op_c_memory_prev_value[3] := by rw [← h_oc]; simp [Vector.getElem_map]
    -- `is_real_not_word` (E13 = `is_real * (1 - e2)`): binary, and `= 1 → is_real = 1 ∧ e2 = 0`.
    have h13t := e13; simp only [circuit_norm] at h13t; rw [h_oir] at h13t
    have hirnw : env.get (B + 4) = 0 ∨ env.get (B + 4) = 1 := by
      rcases hbin with h | h
      · left; rw [h] at h13t; linear_combination h13t
      · rcases he2 with h2 | h2
        · right; rw [h, h2] at h13t; linear_combination h13t
        · left; rw [h, h2] at h13t; linear_combination h13t
    have hirnw_imp : env.get (B + 4) = 1 →
        input_is_real = 1 ∧
          env.get (i₀ + 4) + env.get (i₀ + 5) + env.get (i₀ + 6) + env.get (i₀ + 7) = 0 := by
      intro hir
      rcases hbin with h | h
      · exfalso; rw [h, hir] at h13t; exact one_ne_zero (by linear_combination h13t)
      · rcases he2 with h2 | h2
        · exact ⟨h, h2⟩
        · exfalso; rw [h, h2, hir] at h13t; exact one_ne_zero (by linear_combination h13t)
    -- `max_abs_c_or_1` is `isU64`: `is_c_0 = 1 → #v[1,0,0,0]` (c = 0 branch), else `= abs_c` (E299-302).
    have hmaxU : input_is_real = 1 → Word.isU64 (Vector.map (Expression.eval env)
        (Vector.mapRange 4 fun i => var { index := B + 7+8+8+11+11+11+4+4+4 + i }) : Word (ZMod p)) := by
      intro hr
      have hrneg' : -input_is_real = -1 := by rw [hr]
      have hsem := IsZeroWordOperation.result_semantic (h_isc0 (Or.inr hr)) hr
      have h299 := e299; have h300 := e300; have h301 := e301; have h302 := e302
      simp only [circuit_norm] at h299 h300 h301 h302
      rw [iszeroword_result_proj] at h299 h300 h301 h302
      simp only [Vector.getElem_mapRange, circuit_norm] at h299 h300 h301 h302
      by_cases hcz : cop[0] = 0 ∧ cop[1] = 0 ∧ cop[2] = 0
          ∧ cop[3] = 0
      · rw [if_pos hcz] at hsem; dsimp only at hsem; rw [field_fromElements_one] at hsem
        simp only [Vector.getElem_cast, Vector.getElem_take, Vector.getElem_drop,
          Vector.getElem_mapRange, Nat.reduceAdd, circuit_norm] at hsem
        rw [hsem] at h299 h300 h301 h302
        apply Word.isU64_of_cases <;> simp only [circuit_norm, Nat.add_zero]
        · haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
          rw [show env.get (B + 7+8+8+11+11+11+4+4+4) = 1 from by linear_combination h299,
            ZMod.val_one]; norm_num
        · rw [show env.get (B + 7+8+8+11+11+11+4+4+4 + 1) = 0 from by linear_combination h300]; simp
        · rw [show env.get (B + 7+8+8+11+11+11+4+4+4 + 2) = 0 from by linear_combination h301]; simp
        · rw [show env.get (B + 7+8+8+11+11+11+4+4+4 + 3) = 0 from by linear_combination h302]; simp
      · rw [if_neg hcz] at hsem; dsimp only at hsem; rw [field_fromElements_one] at hsem
        simp only [Vector.getElem_cast, Vector.getElem_take, Vector.getElem_drop,
          Vector.getElem_mapRange, Nat.reduceAdd, circuit_norm] at hsem
        rw [hsem] at h299 h300 h301 h302
        apply Word.isU64_of_cases <;> simp only [circuit_norm, Nat.add_zero]
        · rw [show env.get (B + 7+8+8+11+11+11+4+4+4) = env.get (B + 7+8+8+11+11+11)
              from by linear_combination h299]
          exact isU16_of_byteRowSpec (hb_absc0 hrneg')
        · rw [show env.get (B + 7+8+8+11+11+11+4+4+4 + 1) = env.get (B + 7+8+8+11+11+11 + 1)
              from by linear_combination h300]
          exact isU16_of_byteRowSpec (hb_absc1 hrneg')
        · rw [show env.get (B + 7+8+8+11+11+11+4+4+4 + 2) = env.get (B + 7+8+8+11+11+11 + 2)
              from by linear_combination h301]
          exact isU16_of_byteRowSpec (hb_absc2 hrneg')
        · rw [show env.get (B + 7+8+8+11+11+11+4+4+4 + 3) = env.get (B + 7+8+8+11+11+11 + 3)
              from by linear_combination h302]
          exact isU16_of_byteRowSpec (hb_absc3 hrneg')
    -- `isU64` of the operand `c` (= `cop`), distinct from `isU64` of the read (`hcU`), feeding the
    -- `MulOperation`/`AddOperation` Assumptions (`mulLo`/`mulHi`/`addc`). Low limbs equal the read (E21/E23,
    -- bounded by `hcU`); high limbs are `read·(1-E2) + c_neg·E2·65535` (E35/E47) — closed by the verified
    -- `operand_isU64` helper (`Extract.lean`) given `he2` + `c_neg` binary (E19: `c_neg = c_msb·E10`, the
    -- `U16MSB` gadget binary, `E10` from the mutually-exclusive flags). TODO: discharge via `operand_isU64`.
    have hcU_op : Word.isU64 cop := by
      obtain ⟨hcr0, hcr1, hcr2, hcr3⟩ := Word.lt_cases_of_isU64 hcU
      have hcc0 : Expression.eval env input_var_adapter_op_c_memory_prev_value[0]
          = input_adapter_op_c_memory_prev_value[0] := by rw [← h_oc]; simp [Vector.getElem_map]
      have hcc2 : Expression.eval env input_var_adapter_op_c_memory_prev_value[2]
          = input_adapter_op_c_memory_prev_value[2] := by rw [← h_oc]; simp [Vector.getElem_map]
      simp only [circuit_norm] at e21 e23 e35 e47
      refine operand_isU64
        (e2 := env.get (i₀ + 4) + env.get (i₀ + 5) + env.get (i₀ + 6) + env.get (i₀ + 7))
        (s := env.get (B + 6)) ?_ ?_ ?_ ?_ hcr0 hcr1 hcr2 hcr3 he2 ?_
      · simp only [hcop, Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
        rw [← hcc0]; linear_combination -e21
      · simp only [hcop, Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
        rw [← hcc1]; linear_combination -e23
      · simp only [hcop, Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
        rw [← hcc2]; linear_combination e35
      · simp only [hcop, Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
        rw [← hcc3]; linear_combination e47
      · -- `c_neg = c_msb.msb * E10` (E19) binary: `c_msb` binary from the `U16MSB` gadget (@ `irnw`,
        -- via `hirnw` — unconditional), `E10 = is_div+is_rem+is_divw+is_remw ∈ {0,1}` (disjoint flags).
        have hcmsb := (h_msb1 ⟨fun _ => by rw [hcc3]; exact (Word.lt_cases_of_isU64 hcU).2.2.2,
          hirnw⟩).1
        simp only [circuit_norm] at hcmsb
        have hE10 := group_binary4 bd br bdw brw (by omega)
        have h19 := e19; simp only [circuit_norm] at h19
        rcases hcmsb with hm | hm <;> rcases hE10 with hE | hE <;>
          simp only [hm, hE, mul_zero, zero_mul, mul_one, one_mul, sub_zero] at h19 <;>
          first
            | exact Or.inl (by linear_combination -h19)
            | exact Or.inr (by linear_combination -h19)
    -- The trailing 34 `byteChannel.pullIf` off-gate `Requirements` conjuncts (32 gated by `is_real`, the
    -- last two by `e2`) — vacuous under the respective binary gate (`hbin`/`he2`, `off_gate_vacuous`).
    refine ⟨?mulLo, ?mulHi, ?eqb, ?eqc, ?eqb2, ?eqc2, ?isc0, ?addc, ?addr, ?lt,
      ?msb0, ?msb1, ?msb2, ?msb3, ?msb4, ?msb5, ?msb6, ?cpu, ?rtype, ?own,
      fun h1 h0 => off_gate_vacuous hbin h1 h0, fun h1 h0 => off_gate_vacuous hbin h1 h0,
      fun h1 h0 => off_gate_vacuous hbin h1 h0, fun h1 h0 => off_gate_vacuous hbin h1 h0,
      fun h1 h0 => off_gate_vacuous hbin h1 h0, fun h1 h0 => off_gate_vacuous hbin h1 h0,
      fun h1 h0 => off_gate_vacuous hbin h1 h0, fun h1 h0 => off_gate_vacuous hbin h1 h0,
      fun h1 h0 => off_gate_vacuous hbin h1 h0, fun h1 h0 => off_gate_vacuous hbin h1 h0,
      fun h1 h0 => off_gate_vacuous hbin h1 h0, fun h1 h0 => off_gate_vacuous hbin h1 h0,
      fun h1 h0 => off_gate_vacuous hbin h1 h0, fun h1 h0 => off_gate_vacuous hbin h1 h0,
      fun h1 h0 => off_gate_vacuous hbin h1 h0, fun h1 h0 => off_gate_vacuous hbin h1 h0,
      fun h1 h0 => off_gate_vacuous hbin h1 h0, fun h1 h0 => off_gate_vacuous hbin h1 h0,
      fun h1 h0 => off_gate_vacuous hbin h1 h0, fun h1 h0 => off_gate_vacuous hbin h1 h0,
      fun h1 h0 => off_gate_vacuous hbin h1 h0, fun h1 h0 => off_gate_vacuous hbin h1 h0,
      fun h1 h0 => off_gate_vacuous hbin h1 h0, fun h1 h0 => off_gate_vacuous hbin h1 h0,
      fun h1 h0 => off_gate_vacuous hbin h1 h0, fun h1 h0 => off_gate_vacuous hbin h1 h0,
      fun h1 h0 => off_gate_vacuous hbin h1 h0, fun h1 h0 => off_gate_vacuous hbin h1 h0,
      fun h1 h0 => off_gate_vacuous hbin h1 h0, fun h1 h0 => off_gate_vacuous hbin h1 h0,
      fun h1 h0 => off_gate_vacuous hbin h1 h0, fun h1 h0 => off_gate_vacuous hbin h1 h0,
      fun h1 h0 => off_gate_vacuous he2 h1 h0, fun h1 h0 => off_gate_vacuous he2 h1 h0⟩
    case own => simp only [circuit_norm, assertZeros, forAllNoOffset_map_assert]
    case eqb => exact Or.inl rfl
    case eqc => exact Or.inl rfl
    case eqb2 => exact Or.inl rfl
    case eqc2 => exact Or.inl rfl
    case isc0 => exact Or.inl rfl
    case cpu => exact hbin
    case rtype => exact Or.inr ⟨hbin, hbin⟩
    case mulLo =>
      exact Or.inr ⟨fun hr => ⟨hqcU hr, hcU_op⟩, hbin, fun h => (zero_ne_one h).elim, hbin,
        Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, by rcases hbin with h | h <;> simp [h]⟩
    case mulHi =>
      refine Or.inr ⟨fun hr => ⟨hqcU (hirnw_imp hr).1, hcU_op⟩, hirnw,
        fun h => (zero_ne_one h).elim, Or.inl rfl,
        group_binary2 bd br (by omega), group_binary2 bdu bru (by omega), Or.inl rfl, Or.inl rfl, ?_⟩
      rcases group_binary4 bd br bdu bru (by omega) with h | h
      · exact Or.inl (by linear_combination h)
      · exact Or.inr (by linear_combination h)
    case addc =>
      refine Or.inr ⟨fun hace => ?_, ?_⟩
      · have h286 := e286; simp only [circuit_norm] at h286
        have hr : input_is_real = 1 := by
          rcases hbin with h | h
          · exfalso; rw [h_oir, h, mul_zero, neg_zero, add_zero] at h286
            exact zero_ne_one (h286.symm.trans hace)
          · exact h
        exact ⟨hcU_op, habscU hr⟩
      · have h := e357; simp only [circuit_norm] at h; exact bool_of_mul_pred h
    case addr =>
      refine Or.inr ⟨fun hrae => ?_, ?_⟩
      · have h288 := e288; simp only [circuit_norm] at h288
        have hr : input_is_real = 1 := by
          rcases hbin with h | h
          · exfalso; rw [h_oir, h, mul_zero, neg_zero, add_zero] at h288
            exact zero_ne_one (h288.symm.trans hrae)
          · exact h
        exact ⟨hrcU hr, habsrU hr⟩
      · have h := e359; simp only [circuit_norm] at h; exact bool_of_mul_pred h
    case lt =>
      -- E305: `remainder_check_multiplicity = (1 - is_c_0.result) * is_real`.
      have h305 := e305; simp only [circuit_norm] at h305
      rw [iszeroword_result_proj] at h305
      simp only [Vector.getElem_mapRange, circuit_norm] at h305
      rw [h_oir] at h305
      refine Or.inr ⟨fun hrcm => ?_, ?_⟩
      · -- rcm = 1 → is_real = 1, then `abs_remainder`/`max_abs_c_or_1` are `isU64`.
        have hr : input_is_real = 1 := by
          rcases hbin with h | h
          · exfalso; rw [h] at h305; exact one_ne_zero (by linear_combination -h305 - hrcm)
          · exact h
        exact ⟨habsrU hr, hmaxU hr⟩
      · -- rcm binary: `(1 - is_c_0) * is_real` with `is_real`/`is_c_0` binary.
        rcases hbin with h | h
        · left; rw [h] at h305; linear_combination -h305
        · have hsem := IsZeroWordOperation.result_semantic (h_isc0 (Or.inr h)) h
          by_cases hcz : cop[0] = 0 ∧ cop[1] = 0 ∧ cop[2] = 0
              ∧ cop[3] = 0
          · left
            rw [if_pos hcz] at hsem; dsimp only at hsem; rw [field_fromElements_one] at hsem
            simp only [Vector.getElem_cast, Vector.getElem_take, Vector.getElem_drop,
              Vector.getElem_mapRange, Nat.reduceAdd, circuit_norm] at hsem
            rw [h, hsem] at h305; linear_combination -h305
          · right
            rw [if_neg hcz] at hsem; dsimp only at hsem; rw [field_fromElements_one] at hsem
            simp only [Vector.getElem_cast, Vector.getElem_take, Vector.getElem_drop,
              Vector.getElem_mapRange, Nat.reduceAdd, circuit_norm] at hsem
            rw [h, hsem] at h305; linear_combination -h305
    case msb0 =>
      -- the U16MSB gadget tests the raw read `bpv[3]`, bounded directly by `isU64 (read)`.
      refine Or.inr ⟨fun _ => ?_, hirnw⟩
      rw [hbb3]; exact (Word.lt_cases_of_isU64 hbU).2.2.2
    case msb1 =>
      refine Or.inr ⟨fun _ => ?_, hirnw⟩
      rw [hcc3]; exact (Word.lt_cases_of_isU64 hcU).2.2.2
    case msb2 =>
      refine Or.inr ⟨fun hirnwg => ?_, hirnw⟩
      obtain ⟨hr, -⟩ := hirnw_imp hirnwg
      have hrneg' : -input_is_real = -1 := by rw [hr]
      exact isU16_of_byteRowSpec (hb_r3 hrneg')
    case msb3 =>
      refine Or.inr ⟨fun _ => ?_, he2⟩
      rw [hbb1]; exact (Word.lt_cases_of_isU64 hbU).2.1
    case msb4 =>
      refine Or.inr ⟨fun _ => ?_, he2⟩
      rw [hcc1]; exact (Word.lt_cases_of_isU64 hcU).2.1
    case msb5 =>
      exact Or.inr ⟨fun he2g => isU16_of_byteRowSpec (hb_e2r1 (by linear_combination -he2g)), he2⟩
    case msb6 =>
      exact Or.inr ⟨fun he2g => isU16_of_byteRowSpec (hb_e2q1 (by linear_combination -he2g)), he2⟩

/-- The `Spec`-only obligation: the soundness goal *minus* the shared `Operations.Requirements` tail.
Each conjunct proves this (its own `Spec`); the tail is supplied once by `requirements_holds`. -/
def SpecObligation (Spec : Inputs (ZMod p) → DivRemCols (ZMod p) → ProverData (ZMod p) → Prop) : Prop :=
  ∀ (i₀ : ℕ) (env : Environment (ZMod p)) (input_var : Var Inputs (ZMod p)) (input : Inputs (ZMod p)),
    eval env input_var = input → Assumptions input env.data →
    ConstraintsHold.Soundness env (main input_var |>.operations i₀) →
    Spec input (eval env (ElaboratedCircuit.output main input_var i₀)) env.data

/-- Reassemble a full `GeneralFormalCircuit.Soundness` from the per-conjunct `SpecObligation` and the
shared `requirements_holds` tail — the binders are still **raw** here (no `circuit_proof_start`), so
`requirements_holds` applies by-term without the decomposed-context mismatch. -/
lemma soundness_of_specObligation
    {Spec : Inputs (ZMod p) → DivRemCols (ZMod p) → ProverData (ZMod p) → Prop}
    (h : SpecObligation (p := p) Spec) :
    GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  intro i₀ env input_var input h_input h_assumptions h_holds
  exact ⟨h i₀ env input_var input h_input h_assumptions h_holds,
    (requirements_holds i₀ env input_var input h_input h_assumptions h_holds).2⟩

open Lean Elab Tactic

/-- `circuit_proof_start` for a `SpecObligation` goal: mirrors the stock tactic's setup verbatim
(unfold `SpecObligation`, intro the seven binders, then the identical `circuit_norm`/`dsimp`/
`provable_struct_simp` normalization) so each conjunct's existing spec proof runs unchanged. Must be
an `elab` using `mkIdent` (not a `macro`) so the introduced binders and the use-site `Spec`/`main`/
`elaborated` identifiers resolve in the conjunct's namespace, exactly as `circuit_proof_start` does.
Used after `apply soundness_of_specObligation`. -/
elab "spec_proof_start" : tactic => do
  evalTactic (← `(tactic| unfold SpecObligation))
  for name in [`i₀, `env, `input_var, `input, `h_input, `h_assumptions, `h_holds] do
    evalTactic (← `(tactic| intro $(mkIdent name):ident))
  try evalTactic (← `(tactic| simp only [circuit_norm] at $(mkIdent `input_var):ident)) catch _ => pure ()
  try evalTactic (← `(tactic| simp only [circuit_norm] at $(mkIdent `input):ident)) catch _ => pure ()
  try evalTactic (← `(tactic| simp only [circuit_norm] at $(mkIdent `h_input):ident)) catch _ => pure ()
  evalTactic (← `(tactic| try dsimp only [$(mkIdent `Assumptions):ident] at *))
  evalTactic (← `(tactic| try dsimp only [$(mkIdent `Spec):ident] at *))
  evalTactic (← `(tactic| try dsimp only [$(mkIdent `elaborated):ident] at *))
  evalTactic (← `(tactic| try dsimp only [$(mkIdent `main):ident] at *))
  try evalTactic (← `(tactic| dsimp only [ElaboratedCircuit.withData, ElaboratedCircuit.output])) catch _ => pure ()
  try evalTactic (← `(tactic| provable_struct_simp)) catch _ => pure ()
  try evalTactic (← `(tactic| simp only [circuit_norm] at $(mkIdent `h_input):ident)) catch _ => pure ()
  try evalTactic (← `(tactic| simp only [circuit_norm] at $(mkIdent `h_assumptions):ident)) catch _ => pure ()
  try evalTactic (← `(tactic| simp only [circuit_norm, $(mkIdent `h_input):ident] at $(mkIdent `h_holds):ident)) catch _ => pure ()
  try evalTactic (← `(tactic| simp only [circuit_norm, $(mkIdent `h_input):ident])) catch _ => pure ()

end SP1Clean.DivRemChip
