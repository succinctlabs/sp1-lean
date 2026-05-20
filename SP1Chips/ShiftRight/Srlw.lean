import SP1Chips.ShiftRight.Common

namespace ShiftRight

set_option linter.style.setOption false
-- Imbalanced goal tree: proof applies tactics per-focused-case.
set_option linter.style.multiGoal false
-- Unused variables expected because many proofs are currently stopped.
set_option linter.unusedVariables false
set_option maxHeartbeats 100000000
set_option linter.style.longLine false


section srlw_poly

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

set_option maxHeartbeats 800000000 in
-- 800M heartbeats: cb4 split + 16-way cb-blast for a0/a1 bounds.
/-- U64-bound on the SRLW output word `a`. Lives in `Srlw.lean` rather than `Common.lean`
because `spec.srlw_common_poly` is the only consumer.

Tightened precondition: takes `eq_srlw : Main[66] = 1` directly (SRLW arm only).
The proof: derive h_real and the SRLW-arm projection internally; bound a2, a3 via
the `srw_w2`/`srw_w3` constraints (a_j = msb_srw * 65535) using
`bool_mul_65535_lt_poly`; case-split on `cb4` (∈ {0, 1}) and inside each branch
bound a0, a1 via the chip's lr_j form `hl_j + ll_{j+1} * v0123` together with the
`limb_16_lt_aux_poly` per-pattern bound. -/
private lemma ops_U64_a_poly_local (Main : Vector (ZMod p) 69)
    (cstrs : (constraints Main).allHold_poly)
    (eq_srlw : Main[66] = 1) :
    Word.isU64_poly #v[Main[32], Main[33], Main[34], Main[35]] := by
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  have hp : 2 ^ 17 < p := Fact.out
  haveI : Fact (1 < p) := ⟨by omega⟩
  have h_real := is_real_eq_one_of_srlw Main cstrs eq_srlw
  obtain ⟨_, _, sop_3, _⟩ := single_op_poly Main cstrs
  have ⟨h_no_srl, h_no_sra, h_no_sraw⟩ := sop_3 eq_srlw
  have ⟨is_U64_b, is_U64_c⟩ := ops_U64_b_c_poly Main cstrs h_real
  obtain ⟨b0_16, b1_16, b2_16, b3_16⟩ := Word.lt_cases_of_isU64_poly is_U64_b
  obtain ⟨c0_16, _, _, _⟩ := Word.lt_cases_of_isU64_poly is_U64_c
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
             List.getElem_cons_succ] at b0_16 b1_16 b2_16 b3_16 c0_16
  -- Open cstrs to get individual conjuncts.
  change List.Forall SP1Constraint.toProp (constraints Main) at cstrs
  rw [allHold_constraints_iff_poly] at cstrs
  -- Set local names.
  set b0 := Main[15]; set b1 := Main[16]; set b2 := Main[17]; set b3 := Main[18]
  set a0 := Main[32]; set a1 := Main[33]; set a2 := Main[34]; set a3 := Main[35]
  set msb_b := Main[36]; set msb_srw := Main[37]
  set cb0 := Main[38]; set cb1 := Main[39]; set cb2 := Main[40]
  set cb3 := Main[41]; set cb4 := Main[42]; set cb5 := Main[43]
  set smv := Main[44]; set v0123 := Main[45]; set v012 := Main[46]; set v01 := Main[47]
  set ll0 := Main[48]; set ll1 := Main[49]; set ll2 := Main[50]; set ll3 := Main[51]
  set hl0 := Main[52]; set hl1 := Main[53]; set hl2 := Main[54]; set hl3 := Main[55]
  set lr0 := Main[56]; set lr1 := Main[57]; set lr2 := Main[58]; set lr3 := Main[59]
  set su160 := Main[60]; set su161 := Main[61]; set su162 := Main[62]; set su163 := Main[63]
  -- Destructure cstrs.
  obtain ⟨_, _h_msb_b1_sraw, h_msb_a1_srw, _, _,
           _, _, _, _, _, _,
           b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, _b_cb5, _,
           h_su160, _b_su160, h_su161, _b_su161, h_su162, _b_su162, h_su163, _b_su163,
           one_of_su16s,
           eq_v01, eq_v012, eq_v0123,
           lt_ll0', lt_lh0', _, lt_ll1', lt_lh1', _,
           lt_ll2', lt_lh2', _, _lt_ll3', _lt_lh3', _,
           eq_lr0, eq_lr1, _eq_lr2, _eq_lr3,
           w_msb_b, eq_smv, _w_msb_srv,
           _sr_00, _sr_01, _sr_02, _sr_03,
           _sr_10, _sr_11, _sr_12, _sr_13,
           _sr_20, _sr_21, _sr_22, _sr_23,
           _sr_30, _sr_31, _sr_32, _sr_33,
           srw_00, srw_01, srw_10, srw_11,
           srw_w2, srw_w3,
           _⟩ := cstrs
  have h_v0_val : (0 : ZMod p).val = 0 := ZMod.val_zero
  have h_v1_val : (1 : ZMod p).val = 1 := ZMod.val_one p
  have h_one_ne_zero : (1 : ZMod p) ≠ 0 := by
    intro h; rw [h] at h_v1_val; rw [h_v0_val] at h_v1_val; exact zero_ne_one h_v1_val
  have h_sum_ne : ¬ Main[64] + Main[65] + Main[66] + Main[67] = 0 := by
    intro h
    rw [h_no_srl, h_no_sra, eq_srlw, h_no_sraw] at h
    simp only [add_zero, zero_add] at h
    exact h_one_ne_zero h
  have lt_ll0 := lt_ll0' h_sum_ne
  have lt_lh0 := lt_lh0' h_sum_ne
  have lt_ll1 := lt_ll1' h_sum_ne
  have lt_lh1 := lt_lh1' h_sum_ne
  have lt_ll2 := lt_ll2' h_sum_ne
  have lt_lh2 := lt_lh2' h_sum_ne
  -- Resolve gates under SRLW (srlw + sraw = 1, srl + sra = 0).
  rw [h_no_sraw, eq_srlw] at srw_00 srw_01 srw_10 srw_11 srw_w2 srw_w3
  simp only [add_zero, mul_one] at srw_w2 srw_w3
  simp only [add_zero,
             show ((1 : ZMod p) = 0) ↔ False from ⟨h_one_ne_zero, False.elim⟩, false_or]
    at srw_00 srw_01 srw_10 srw_11
  -- Derive msb_b = 0 from w_msb_b under SRLW.
  rw [h_no_srl, eq_srlw] at w_msb_b
  simp only [zero_add,
             show ((1 : ZMod p) = 0) ↔ False from ⟨h_one_ne_zero, False.elim⟩, false_or]
    at w_msb_b
  have h_msb_b_zero : msb_b = 0 := w_msb_b
  rw [h_msb_b_zero, zero_mul] at eq_smv
  -- Simplify correction terms in srw_01, srw_10, srw_11.
  simp only [h_msb_b_zero, eq_smv, zero_mul, add_zero, sub_self] at srw_01 srw_10 srw_11
  -- Derive msb_srw ∈ {0, 1} from h_msb_a1_srw (U16MSBOperation constraint on a1).
  -- The multiplier is `srlw + sraw`; under SRLW, this is 1.
  rw [h_no_sraw, eq_srlw] at h_msb_a1_srw
  simp only [add_zero] at h_msb_a1_srw
  have h_msb_srw_bool : msb_srw = 0 ∨ msb_srw = 1 := by
    rw [U16MSBOperation.allHold_constraints_iff_poly] at h_msb_a1_srw
    exact h_msb_a1_srw.2.1
  -- Bound a2 = msb_srw * 65535 < 65536 and a3 similarly.
  have h_a2_eq : a2 = msb_srw * 65535 := srw_w2.resolve_left h_one_ne_zero
  have h_a3_eq : a3 = msb_srw * 65535 := srw_w3.resolve_left h_one_ne_zero
  have h_a2_lt : a2.val < 65536 := by
    rw [h_a2_eq]
    have h_eq : msb_srw * (65535 : ZMod p) = msb_srw * (((65535 : ℕ) : ZMod p)) := by
      norm_cast
    rw [h_eq]
    exact bool_mul_65535_lt_poly h_msb_srw_bool
  have h_a3_lt : a3.val < 65536 := by
    rw [h_a3_eq]
    have h_eq : msb_srw * (65535 : ZMod p) = msb_srw * (((65535 : ℕ) : ZMod p)) := by
      norm_cast
    rw [h_eq]
    exact bool_mul_65535_lt_poly h_msb_srw_bool
  -- Resolve su16 dispatch under SRLW (srl+sra=0; cb4 + cb5*2*(srl+sra) = cb4).
  rw [h_no_srl, h_no_sra] at h_su160 h_su161 h_su162 h_su163 one_of_su16s
  simp only [add_zero, zero_add, mul_zero] at h_su160 h_su161 h_su162 h_su163 one_of_su16s
  rw [h_no_sraw, eq_srlw] at one_of_su16s
  simp only [add_zero,
             show ((1 : ZMod p) = 0) ↔ False from ⟨h_one_ne_zero, False.elim⟩, false_or]
    at one_of_su16s
  -- cb4 case-split; bound a0, a1 in each branch.
  -- Goal-form helper for the 16-way blast.
  have lr_blast : ∀ {hl ll : ZMod p}
      (_lt_hl : hl.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                    + cb3 * 8) : ZMod p).val)
      (_lt_ll : ll.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val),
      (hl + ll * v0123).val < 65536 := by
    intro hl ll lt_hl lt_ll
    rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
      rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
    · -- (0,0,0,0): S=0, M=65536, N=1
      exact lr_blast_per_pattern_poly 0 65536 1 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        lt_hl lt_ll
    · -- (0,0,0,1): S=8, M=256, N=256
      exact lr_blast_per_pattern_poly 8 256 256 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        lt_hl lt_ll
    · -- (0,0,1,0): S=4, M=4096, N=16
      exact lr_blast_per_pattern_poly 4 4096 16 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        lt_hl lt_ll
    · -- (0,0,1,1): S=12, M=16, N=4096
      exact lr_blast_per_pattern_poly 12 16 4096 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        lt_hl lt_ll
    · -- (0,1,0,0): S=2, M=16384, N=4
      exact lr_blast_per_pattern_poly 2 16384 4 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        lt_hl lt_ll
    · -- (0,1,0,1): S=10, M=64, N=1024
      exact lr_blast_per_pattern_poly 10 64 1024 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        lt_hl lt_ll
    · -- (0,1,1,0): S=6, M=1024, N=64
      exact lr_blast_per_pattern_poly 6 1024 64 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        lt_hl lt_ll
    · -- (0,1,1,1): S=14, M=4, N=16384
      exact lr_blast_per_pattern_poly 14 4 16384 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        lt_hl lt_ll
    · -- (1,0,0,0): S=1, M=32768, N=2
      exact lr_blast_per_pattern_poly 1 32768 2 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        lt_hl lt_ll
    · -- (1,0,0,1): S=9, M=128, N=512
      exact lr_blast_per_pattern_poly 9 128 512 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        lt_hl lt_ll
    · -- (1,0,1,0): S=5, M=2048, N=32
      exact lr_blast_per_pattern_poly 5 2048 32 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        lt_hl lt_ll
    · -- (1,0,1,1): S=13, M=8, N=8192
      exact lr_blast_per_pattern_poly 13 8 8192 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        lt_hl lt_ll
    · -- (1,1,0,0): S=3, M=8192, N=8
      exact lr_blast_per_pattern_poly 3 8192 8 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        lt_hl lt_ll
    · -- (1,1,0,1): S=11, M=32, N=2048
      exact lr_blast_per_pattern_poly 11 32 2048 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        lt_hl lt_ll
    · -- (1,1,1,0): S=7, M=512, N=128
      exact lr_blast_per_pattern_poly 7 512 128 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        lt_hl lt_ll
    · -- (1,1,1,1): S=15, M=2, N=32768
      exact lr_blast_per_pattern_poly 15 2 32768 (by omega) (by decide) (by omega) rfl rfl
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        lt_hl lt_ll
  -- Bound a0, a1 by case-splitting on cb4 (∈ {0, 1}).
  refine fun i => ?_
  fin_cases i
  · -- a0.val < 65536
    change a0.val < 65536
    rcases b_cb4 with hcb4 | hcb4
    · -- cb4 = 0: resolve su160 = 1 → a0 = lr0
      rw [hcb4] at h_su160 h_su161 h_su162 h_su163
      have h_su161_zero : su161 = 0 :=
        h_su161.resolve_right (fun h => h_one_ne_zero (by linear_combination -h))
      have h_su162_zero : su162 = 0 :=
        h_su162.resolve_right (fun h => val_2_ne_zero (by linear_combination -h))
      have h_su163_zero : su163 = 0 :=
        h_su163.resolve_right (fun h => val_3_ne_zero (by linear_combination -h))
      have h_su160_eq : su160 = 1 := by
        have := one_of_su16s
        rw [h_su161_zero, h_su162_zero, h_su163_zero, add_zero, add_zero, add_zero] at this
        exact this
      have h_su160_ne_zero : su160 ≠ 0 := by rw [h_su160_eq]; exact h_one_ne_zero
      have h_a0_eq : a0 = lr0 := srw_00.resolve_left h_su160_ne_zero
      rw [h_a0_eq, eq_lr0]
      exact lr_blast lt_lh0 lt_ll1
    · -- cb4 = 1: a0 = lr1
      rw [hcb4] at h_su160 h_su161 h_su162 h_su163
      have h_su160_zero : su160 = 0 :=
        h_su160.resolve_right h_one_ne_zero
      have h_su162_zero : su162 = 0 := by
        apply h_su162.resolve_right
        intro h
        have hv1 : (1 : ZMod p).val = 1 := h_v1_val
        have hv2 : (2 : ZMod p).val = 2 := val_2_zmod_p
        have := congrArg ZMod.val h
        rw [hv1, hv2] at this; omega
      have h_su163_zero : su163 = 0 := by
        apply h_su163.resolve_right
        intro h
        have hv1 : (1 : ZMod p).val = 1 := h_v1_val
        have hv3 : (3 : ZMod p).val = 3 := by
          rw [show (3 : ZMod p) = ((3 : ℕ) : ZMod p) from by push_cast; rfl]
          exact ZMod.val_natCast_of_lt (by omega)
        have := congrArg ZMod.val h
        rw [hv1, hv3] at this; omega
      have h_su161_eq : su161 = 1 := by
        have := one_of_su16s
        rw [h_su160_zero, h_su162_zero, h_su163_zero, zero_add, add_zero, add_zero] at this
        exact this
      have h_su161_ne_zero : su161 ≠ 0 := by rw [h_su161_eq]; exact h_one_ne_zero
      have h_a0_eq : a0 = lr1 := srw_10.resolve_left h_su161_ne_zero
      rw [h_a0_eq, eq_lr1]
      exact lr_blast lt_lh1 lt_ll2
  · -- a1.val < 65536
    change a1.val < 65536
    rcases b_cb4 with hcb4 | hcb4
    · -- cb4 = 0: a1 = lr1
      rw [hcb4] at h_su160 h_su161 h_su162 h_su163
      have h_su161_zero : su161 = 0 :=
        h_su161.resolve_right (fun h => h_one_ne_zero (by linear_combination -h))
      have h_su162_zero : su162 = 0 :=
        h_su162.resolve_right (fun h => val_2_ne_zero (by linear_combination -h))
      have h_su163_zero : su163 = 0 :=
        h_su163.resolve_right (fun h => val_3_ne_zero (by linear_combination -h))
      have h_su160_eq : su160 = 1 := by
        have := one_of_su16s
        rw [h_su161_zero, h_su162_zero, h_su163_zero, add_zero, add_zero, add_zero] at this
        exact this
      have h_su160_ne_zero : su160 ≠ 0 := by rw [h_su160_eq]; exact h_one_ne_zero
      have h_a1_eq : a1 = lr1 := srw_01.resolve_left h_su160_ne_zero
      rw [h_a1_eq, eq_lr1]
      exact lr_blast lt_lh1 lt_ll2
    · -- cb4 = 1: a1 = msb_b * 65535 = 0
      rw [hcb4] at h_su160 h_su161 h_su162 h_su163
      have h_su160_zero : su160 = 0 :=
        h_su160.resolve_right h_one_ne_zero
      have h_su162_zero : su162 = 0 := by
        apply h_su162.resolve_right
        intro h
        have hv1 : (1 : ZMod p).val = 1 := h_v1_val
        have hv2 : (2 : ZMod p).val = 2 := val_2_zmod_p
        have := congrArg ZMod.val h
        rw [hv1, hv2] at this; omega
      have h_su163_zero : su163 = 0 := by
        apply h_su163.resolve_right
        intro h
        have hv1 : (1 : ZMod p).val = 1 := h_v1_val
        have hv3 : (3 : ZMod p).val = 3 := by
          rw [show (3 : ZMod p) = ((3 : ℕ) : ZMod p) from by push_cast; rfl]
          exact ZMod.val_natCast_of_lt (by omega)
        have := congrArg ZMod.val h
        rw [hv1, hv3] at this; omega
      have h_su161_eq : su161 = 1 := by
        have := one_of_su16s
        rw [h_su160_zero, h_su162_zero, h_su163_zero, zero_add, add_zero, add_zero] at this
        exact this
      have h_su161_ne_zero : su161 ≠ 0 := by rw [h_su161_eq]; exact h_one_ne_zero
      -- srw_11 was pre-simplified at the prologue (line ~264) using h_msb_b_zero
      -- to collapse `a1 = msb_b * 65535` to `a1 = 0`.
      have h_a1_eq : a1 = 0 := srw_11.resolve_left h_su161_ne_zero
      rw [h_a1_eq]; simp [h_v0_val]
  · -- a2.val < 65536
    exact h_a2_lt
  · -- a3.val < 65536
    exact h_a3_lt

set_option maxHeartbeats 1200000000 in
-- 1.2B heartbeats: 2-way byte_shift (cb4) × 16-way cb0..cb3 rcases = 32 leaves,
-- on top of the SRLW prologue (deriving msb_srw, sign_extend bridge,
-- hl2/ll2/hl3/ll3 = 0 via cb_aux dispatch).
/-- Shared proof body for `spec.srlw_poly` and `spec.srliw_poly`. Structure
mirrors `spec.srl_common_poly` but for 32-bit operands:
- Forces `hl2 = ll2 = hl3 = ll3 = 0` via `cancel_mul_65536_zero_poly` (since
  the b2/b3 byte equations under SRLW have LHS multiplier 0).
- Reduces the 64-bit goal to a 32-bit shift via `sign_extend_32_to_64_msb_poly`.
- 32-way blast (cb5 forced 0 by 5-bit shamt) closes via existing
  `srl_close_su16_{0,1}_case` wrappers on the low half. -/
private lemma spec.srlw_common_poly (Main : Vector (ZMod p) 69)
    (cstrs : (constraints Main).allHold_poly) (eq_srlw : Main[66] = 1) :
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] =
      execute_RTYPEW_pure_w_poly #v[Main[15], Main[16], Main[17], Main[18]]
        #v[Main[25], Main[26], Main[27], Main[28]] .SRLW := by
  -- Setup (mirrors spec.srl_common_poly prologue).
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  have hp : 2 ^ 17 < p := Fact.out
  haveI : Fact (1 < p) := ⟨by omega⟩
  have h_real := is_real_eq_one_of_srlw Main cstrs eq_srlw
  have ⟨is_U64_b, is_U64_c⟩ := ops_U64_b_c_poly Main cstrs h_real
  have is_U64_a := ops_U64_a_poly_local Main cstrs eq_srlw
  have is_U32_b := Word.isU64_poly_low_poly_isU32_poly is_U64_b
  have is_U32_c := Word.isU64_poly_low_poly_isU32_poly is_U64_c
  have is_U32_a := Word.isU64_poly_low_poly_isU32_poly is_U64_a
  obtain ⟨b0_16, b1_16, b2_16, b3_16⟩ := Word.lt_cases_of_isU64_poly is_U64_b
  obtain ⟨c0_16, _c1_16, _c2_16, _c3_16⟩ := Word.lt_cases_of_isU64_poly is_U64_c
  obtain ⟨a0_16, a1_16, _a2_16, _a3_16⟩ := Word.lt_cases_of_isU64_poly is_U64_a
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
             List.getElem_cons_succ] at b0_16 b1_16 b2_16 b3_16 c0_16 a0_16 a1_16
  obtain ⟨_, _, sop_3, _⟩ := single_op_poly Main cstrs
  have ⟨h_no_srl, h_no_sra, h_no_sraw⟩ := sop_3 eq_srlw
  -- Open the iff_poly.
  change List.Forall SP1Constraint.toProp (constraints Main) at cstrs
  rw [allHold_constraints_iff_poly] at cstrs
  -- Set up local names.
  set b0 := Main[15]; set b1 := Main[16]; set b2 := Main[17]; set b3 := Main[18]
  set c0 := Main[25]; set c1 := Main[26]; set c2 := Main[27]; set c3 := Main[28]
  set a0 := Main[32]; set a1 := Main[33]; set a2 := Main[34]; set a3 := Main[35]
  set msb_b := Main[36]; set msb_srw := Main[37]
  set cb0 := Main[38]; set cb1 := Main[39]; set cb2 := Main[40]
  set cb3 := Main[41]; set cb4 := Main[42]; set cb5 := Main[43]
  set smv := Main[44]; set v0123 := Main[45]; set v012 := Main[46]; set v01 := Main[47]
  set ll0 := Main[48]; set ll1 := Main[49]; set ll2 := Main[50]; set ll3 := Main[51]
  set hl0 := Main[52]; set hl1 := Main[53]; set hl2 := Main[54]; set hl3 := Main[55]
  set lr0 := Main[56]; set lr1 := Main[57]; set lr2 := Main[58]; set lr3 := Main[59]
  set su160 := Main[60]; set su161 := Main[61]; set su162 := Main[62]; set su163 := Main[63]
  -- Destructure cstrs (same shape as SRL/SRA prologue).
  obtain ⟨_, _h_msb_b1_sraw, h_msb_a1_srw, _, _,
           _, _, _, _, _, _,
           b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
           h_su160, b_su160, h_su161, b_su161, h_su162, b_su162, h_su163, b_su163,
           one_of_su16s,
           eq_v01, eq_v012, eq_v0123,
           lt_ll0', lt_lh0', h_b0_dec, lt_ll1', lt_lh1', h_b1_dec,
           lt_ll2', lt_lh2', h_b2_dec, lt_ll3', lt_lh3', h_b3_dec,
           eq_lr0, eq_lr1, eq_lr2, eq_lr3,
           w_msb_b, eq_smv, w_msb_srv,
           sr_00, sr_01, sr_02, sr_03,
           sr_10, sr_11, sr_12, sr_13,
           sr_20, sr_21, sr_22, sr_23,
           sr_30, sr_31, sr_32, sr_33,
           srw_00, srw_01, srw_10, srw_11,
           srw_w2, srw_w3,
           _h_M13⟩ := cstrs
  have h_v0_val : (0 : ZMod p).val = 0 := ZMod.val_zero
  have h_v1_val : (1 : ZMod p).val = 1 := ZMod.val_one p
  have h_one_ne_zero : (1 : ZMod p) ≠ 0 := by
    intro h; rw [h] at h_v1_val; rw [h_v0_val] at h_v1_val; exact zero_ne_one h_v1_val
  have h_zero_ne_one : (0 : ZMod p) ≠ 1 := fun h => h_one_ne_zero h.symm
  have h_sum_ne : ¬ Main[64] + Main[65] + Main[66] + Main[67] = 0 := by
    intro h
    rw [h_no_srl, h_no_sra, eq_srlw, h_no_sraw] at h
    simp only [add_zero, zero_add] at h
    exact h_one_ne_zero h
  have lt_ll0 := lt_ll0' h_sum_ne
  have lt_lh0 := lt_lh0' h_sum_ne
  have lt_ll1 := lt_ll1' h_sum_ne
  have lt_lh1 := lt_lh1' h_sum_ne
  have lt_ll2 := lt_ll2' h_sum_ne
  have lt_lh2 := lt_lh2' h_sum_ne
  have lt_ll3 := lt_ll3' h_sum_ne
  have lt_lh3 := lt_lh3' h_sum_ne
  -- Under SRLW: srl + sra = 0, so the LHS multiplier in h_b2_dec, h_b3_dec is 0,
  -- forcing hl2 = ll2 = hl3 = ll3 = 0 via cancel_mul_65536_zero_poly (after 16
  -- cb sub-cases to identify v0123).
  rw [h_no_srl, h_no_sra] at h_b2_dec h_b3_dec
  simp only [add_zero, zero_add, zero_mul, mul_zero] at h_b2_dec h_b3_dec
  symm at h_b2_dec h_b3_dec
  push_cast at h_b2_dec h_b3_dec
  -- Helper: given `M * N = 65536`, `0 < M`, `v0123 = ((M : ℕ) : ZMod p)`,
  -- bounds `hl.val < M`, `ll.val < N`, the equation
  -- `hl * 65536 + ll * v0123 = 0` gives `hl = 0 ∧ ll = 0`.
  -- (Bound shape matches `lt_lh2/lt_ll2` after the cb-determined v0123 value:
  -- lt_lh = `hl.val < 2^(16-S)` = M, lt_ll = `ll.val < 2^S` = N.)
  have zero_aux : ∀ (M N : ℕ), M * N = 65536 → 0 < M →
      ∀ {hl ll : ZMod p}, v0123 = ((M : ℕ) : ZMod p) →
      hl.val < M → ll.val < N →
      hl * 65536 + ll * v0123 = 0 → hl = 0 ∧ ll = 0 := by
    intro M N h_MN h_M_pos hl ll h_v0123_eq h_hl_lt h_ll_lt h_eq
    have h_N_pos : 0 < N := by nlinarith [h_MN, h_M_pos]
    have h_M_dvd : M ∣ 65536 := ⟨N, h_MN.symm⟩
    have h_M_le : M ≤ 65536 := Nat.le_of_dvd (by omega) h_M_dvd
    have h_N_le : N ≤ 65536 := by nlinarith [h_MN, h_M_pos]
    have h_M_lt_p : M < p := by omega
    have h_N_lt_p : N < p := by omega
    have h_v0123_val : v0123.val = M := by
      rw [h_v0123_eq]; exact ZMod.val_natCast_of_lt h_M_lt_p
    have h_v0123_dvd : v0123.val ∣ 65536 := by rw [h_v0123_val]; exact h_M_dvd
    have h_v0123_pos : 0 < v0123.val := by rw [h_v0123_val]; exact h_M_pos
    have h_cancel := cancel_mul_65536_zero_poly h_v0123_dvd h_v0123_pos h_eq
    rw [h_v0123_val] at h_cancel
    -- 65536/M = N from M * N = 65536.
    have h_quot_eq : 65536 / M = N := by
      rw [← h_MN]; exact Nat.mul_div_cancel_left N h_M_pos
    rw [h_quot_eq] at h_cancel
    -- h_cancel : hl * ((N : ℕ) : ZMod p) + ll = 0
    have h_hl_N_lt : hl.val * N < 65536 := by nlinarith [h_hl_lt, h_MN, h_M_pos, h_N_pos]
    have h_hl_N_lt_p : hl.val * N < p := by omega
    have h_hl_N_val : (hl * ((N : ℕ) : ZMod p)).val = hl.val * N := by
      rw [ZMod.val_mul_of_lt]
      · rw [ZMod.val_natCast_of_lt h_N_lt_p]
      · rw [ZMod.val_natCast_of_lt h_N_lt_p]; exact h_hl_N_lt_p
    have h_sum_lt_p : hl.val * N + ll.val < p := by omega
    have h_sum_val : (hl * ((N : ℕ) : ZMod p) + ll).val = hl.val * N + ll.val := by
      rw [ZMod.val_add_of_lt]
      · rw [h_hl_N_val]
      · rw [h_hl_N_val]; exact h_sum_lt_p
    have h_zero_val : (hl * ((N : ℕ) : ZMod p) + ll).val = 0 := by
      rw [h_cancel]; exact ZMod.val_zero
    rw [h_sum_val] at h_zero_val
    have h_hl_val_zero : hl.val = 0 := by
      have h_prod_zero : hl.val * N = 0 := by omega
      exact (Nat.mul_eq_zero.mp h_prod_zero).resolve_right (by omega)
    have h_ll_val_zero : ll.val = 0 := by omega
    exact ⟨(ZMod.val_eq_zero hl).mp h_hl_val_zero,
           (ZMod.val_eq_zero ll).mp h_ll_val_zero⟩
  -- Per-cb-pattern helper: given (S, M, N) for the pattern and the cb-sum
  -- equation in ZMod form (provable by push_cast; ring per pattern), normalize
  -- the symbolic bounds and apply zero_aux. Position-agnostic.
  have cb_aux : ∀ {hl ll : ZMod p}
      (_lt_hl : hl.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) +
                                    cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8) : ZMod p).val)
      (_lt_ll : ll.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) +
                              cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8 : ZMod p).val)
      (_h_dec : hl * 65536 + ll * v0123 = 0)
      (S M N : ℕ) (_h_S_le : S ≤ 15)
      (_h_MN : M * N = 65536) (_h_M_pos : 0 < M)
      (_h_M_eq : (2 : ℕ) ^ (16 - S) = M) (_h_N_eq : (2 : ℕ) ^ S = N)
      (_h_v0123_eq : v0123 = ((M : ℕ) : ZMod p))
      (_h_cb_sum_eq : (cb0 + cb1 * ((2 : ℕ) : ZMod p) +
                       cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8 : ZMod p) = ((S : ℕ) : ZMod p)),
      hl = 0 ∧ ll = 0 := by
    intro hl ll lt_hl lt_ll h_dec S M N h_S_le h_MN h_M_pos h_M_eq h_N_eq h_v0123_eq h_cb_sum_eq
    have h_S_lt_p : S < p := by omega
    have h_cb_sum_val : (cb0 + cb1 * ((2 : ℕ) : ZMod p) +
                        cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8 : ZMod p).val = S := by
      rw [h_cb_sum_eq]; exact ZMod.val_natCast_of_lt h_S_lt_p
    have h_S_le_16 : S ≤ 16 := by omega
    have h_outer_val : ((16 : ZMod p) -
                       (cb0 + cb1 * ((2 : ℕ) : ZMod p) +
                        cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8 : ZMod p)).val = 16 - S := by
      rw [h_cb_sum_eq]
      rw [show ((16 : ZMod p) - ((S : ℕ) : ZMod p)) = (((16 - S) : ℕ) : ZMod p) from by
        rw [Nat.cast_sub h_S_le_16]; push_cast; ring]
      have hp : 2 ^ 17 < p := Fact.out
      exact ZMod.val_natCast_of_lt (by omega)
    rw [h_outer_val] at lt_hl
    rw [h_cb_sum_val] at lt_ll
    rw [h_M_eq] at lt_hl
    rw [h_N_eq] at lt_ll
    exact zero_aux M N h_MN h_M_pos h_v0123_eq lt_hl lt_ll h_dec
  -- 16-case dispatch for hl2 = ll2 = 0. Each branch supplies (S, M, N) for the
  -- specific cb-pattern: M = 2^(16-S), N = 2^S, S = cb0 + 2*cb1 + 4*cb2 + 8*cb3.
  have ⟨eq_hl2, eq_ll2⟩ : hl2 = 0 ∧ ll2 = 0 := by
    rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
      rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
    -- rcases binary-counter order: cb3 innermost, cb0 outermost.
    -- (cb0, cb1, cb2, cb3) → S = cb0 + 2*cb1 + 4*cb2 + 8*cb3, M = 2^(16-S), N = 2^S.
    · -- (0,0,0,0): S=0, M=65536, N=1
      exact cb_aux lt_lh2 lt_ll2 h_b2_dec 0 65536 1 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · -- (0,0,0,1): S=8, M=256, N=256
      exact cb_aux lt_lh2 lt_ll2 h_b2_dec 8 256 256 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · -- (0,0,1,0): S=4, M=4096, N=16
      exact cb_aux lt_lh2 lt_ll2 h_b2_dec 4 4096 16 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · -- (0,0,1,1): S=12, M=16, N=4096
      exact cb_aux lt_lh2 lt_ll2 h_b2_dec 12 16 4096 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · -- (0,1,0,0): S=2, M=16384, N=4
      exact cb_aux lt_lh2 lt_ll2 h_b2_dec 2 16384 4 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · -- (0,1,0,1): S=10, M=64, N=1024
      exact cb_aux lt_lh2 lt_ll2 h_b2_dec 10 64 1024 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · -- (0,1,1,0): S=6, M=1024, N=64
      exact cb_aux lt_lh2 lt_ll2 h_b2_dec 6 1024 64 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · -- (0,1,1,1): S=14, M=4, N=16384
      exact cb_aux lt_lh2 lt_ll2 h_b2_dec 14 4 16384 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · -- (1,0,0,0): S=1, M=32768, N=2
      exact cb_aux lt_lh2 lt_ll2 h_b2_dec 1 32768 2 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · -- (1,0,0,1): S=9, M=128, N=512
      exact cb_aux lt_lh2 lt_ll2 h_b2_dec 9 128 512 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · -- (1,0,1,0): S=5, M=2048, N=32
      exact cb_aux lt_lh2 lt_ll2 h_b2_dec 5 2048 32 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · -- (1,0,1,1): S=13, M=8, N=8192
      exact cb_aux lt_lh2 lt_ll2 h_b2_dec 13 8 8192 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · -- (1,1,0,0): S=3, M=8192, N=8
      exact cb_aux lt_lh2 lt_ll2 h_b2_dec 3 8192 8 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · -- (1,1,0,1): S=11, M=32, N=2048
      exact cb_aux lt_lh2 lt_ll2 h_b2_dec 11 32 2048 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · -- (1,1,1,0): S=7, M=512, N=128
      exact cb_aux lt_lh2 lt_ll2 h_b2_dec 7 512 128 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · -- (1,1,1,1): S=15, M=2, N=32768
      exact cb_aux lt_lh2 lt_ll2 h_b2_dec 15 2 32768 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
  -- Mirror dispatch for hl3 = ll3 = 0 (same 16 cb-patterns, same (S, M, N) per pattern).
  have ⟨eq_hl3, eq_ll3⟩ : hl3 = 0 ∧ ll3 = 0 := by
    rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
      rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
    · -- (0,0,0,0): S=0
      exact cb_aux lt_lh3 lt_ll3 h_b3_dec 0 65536 1 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · -- (0,0,0,1): S=8
      exact cb_aux lt_lh3 lt_ll3 h_b3_dec 8 256 256 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · -- (0,0,1,0): S=4
      exact cb_aux lt_lh3 lt_ll3 h_b3_dec 4 4096 16 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · -- (0,0,1,1): S=12
      exact cb_aux lt_lh3 lt_ll3 h_b3_dec 12 16 4096 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · -- (0,1,0,0): S=2
      exact cb_aux lt_lh3 lt_ll3 h_b3_dec 2 16384 4 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · -- (0,1,0,1): S=10
      exact cb_aux lt_lh3 lt_ll3 h_b3_dec 10 64 1024 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · -- (0,1,1,0): S=6
      exact cb_aux lt_lh3 lt_ll3 h_b3_dec 6 1024 64 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · -- (0,1,1,1): S=14
      exact cb_aux lt_lh3 lt_ll3 h_b3_dec 14 4 16384 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · -- (1,0,0,0): S=1
      exact cb_aux lt_lh3 lt_ll3 h_b3_dec 1 32768 2 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · -- (1,0,0,1): S=9
      exact cb_aux lt_lh3 lt_ll3 h_b3_dec 9 128 512 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · -- (1,0,1,0): S=5
      exact cb_aux lt_lh3 lt_ll3 h_b3_dec 5 2048 32 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · -- (1,0,1,1): S=13
      exact cb_aux lt_lh3 lt_ll3 h_b3_dec 13 8 8192 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · -- (1,1,0,0): S=3
      exact cb_aux lt_lh3 lt_ll3 h_b3_dec 3 8192 8 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · -- (1,1,0,1): S=11
      exact cb_aux lt_lh3 lt_ll3 h_b3_dec 11 32 2048 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · -- (1,1,1,0): S=7
      exact cb_aux lt_lh3 lt_ll3 h_b3_dec 7 512 128 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    · -- (1,1,1,1): S=15
      exact cb_aux lt_lh3 lt_ll3 h_b3_dec 15 2 32768 (by omega) (by decide) (by omega)
        (by decide) (by decide)
        (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
  -- Derive a2 = a3 = msb_srw * 65535 from srw_w2, srw_w3 (disjunctions of form
  -- `1 = 0 ∨ a_j = msb_srw * 65535` after normalization; resolve the False disjunct).
  rw [eq_srlw, h_no_sraw] at srw_w2 srw_w3
  simp only [add_zero, zero_add, mul_one] at srw_w2 srw_w3
  have h_a2_eq : a2 = msb_srw * 65535 := srw_w2.resolve_left h_one_ne_zero
  have h_a3_eq : a3 = msb_srw * 65535 := srw_w3.resolve_left h_one_ne_zero
  -- Relate msb_srw to the MSB of the high-u16 limb a1, via U16MSBOperation.spec_poly.
  -- The constraint h_msb_a1_srw has multiplier `(srlw + sraw) = 1 + 0 = 1`.
  rw [eq_srlw, h_no_sraw] at h_msb_a1_srw
  simp only [zero_add, add_zero] at h_msb_a1_srw
  have h_msb_srw_eq : msb_srw = if a1.val ≥ 32768 then 1 else 0 := by
    rw [show msb_srw = ({ msb := msb_srw } : U16MSBOperation (ZMod p)).msb from rfl]
    apply U16MSBOperation.spec_poly a1_16 h_msb_a1_srw
  -- Bridge MSB-of-low-32 to the a1.val ≥ 32768 condition.
  have h_isU32_a_lo : HWord.isU32_poly #v[a0, a1] := by
    intro i; fin_cases i <;> simp [HWord.isU32_poly]
    · exact a0_16
    · exact a1_16
  have h_a01_msb_eq : (HWord.toBitVec32_poly #v[a0, a1]).msb = decide (a1.val ≥ 32768) := by
    have h_toNat : (HWord.toBitVec32_poly #v[a0, a1]).toNat = a0.val + a1.val * 2 ^ 16 := by
      rw [HWord.toBitVec32_poly_toNat_poly h_isU32_a_lo]
      simp [HWord.toNat_poly]
    rw [BitVec.msb_eq_decide, h_toNat]
    have h_a0_lt : a0.val < 65536 := a0_16
    have h_iff : (2 ^ (32 - 1) ≤ a0.val + a1.val * 2 ^ 16) ↔ (a1.val ≥ 32768) := by
      constructor <;> (intro h; omega)
    exact decide_eq_decide.mpr h_iff
  -- Rewrite a2, a3 using the msb bridge: a_j = if msb then 65535 else 0.
  have h_a2_msb : a2 = if (HWord.toBitVec32_poly #v[a0, a1]).msb = true then ((65535 : ℕ) : ZMod p) else 0 := by
    rw [h_a2_eq, h_msb_srw_eq]
    by_cases h : a1.val ≥ 32768
    · have h_msb : (HWord.toBitVec32_poly #v[a0, a1]).msb = true := by
        rw [h_a01_msb_eq]; simp [h]
      simp [h, h_msb]
    · have h_msb : (HWord.toBitVec32_poly #v[a0, a1]).msb = false := by
        rw [h_a01_msb_eq]; simp [h]
      simp [h, h_msb]
  have h_a3_msb : a3 = if (HWord.toBitVec32_poly #v[a0, a1]).msb = true then ((65535 : ℕ) : ZMod p) else 0 := by
    rw [h_a3_eq, h_msb_srw_eq]
    by_cases h : a1.val ≥ 32768
    · have h_msb : (HWord.toBitVec32_poly #v[a0, a1]).msb = true := by
        rw [h_a01_msb_eq]; simp [h]
      simp [h, h_msb]
    · have h_msb : (HWord.toBitVec32_poly #v[a0, a1]).msb = false := by
        rw [h_a01_msb_eq]; simp [h]
      simp [h, h_msb]
  -- Bridge: LHS Word.toBitVec64 #v[a0, a1, a2, a3] = sign_extend the low 32 bits.
  have h_signext_bridge : Word.toBitVec64 #v[a0, a1, a2, a3] =
      BitVec.signExtend 64 (HWord.toBitVec32_poly #v[a0, a1]) := by
    rw [h_a2_msb, h_a3_msb]
    have := HWord.sign_extend_32_to_64_msb_poly h_isU32_a_lo
    have h_a0_idx : (#v[a0, a1] : HWord (ZMod p))[0] = a0 := rfl
    have h_a1_idx : (#v[a0, a1] : HWord (ZMod p))[1] = a1 := rfl
    rw [h_a0_idx, h_a1_idx] at this
    exact this.symm
  rw [h_signext_bridge]
  -- Unfold execute_RTYPEW_pure_w_poly for SRLW: it's sign_extend (m:=64) of the 32-bit shift.
  simp only [execute_RTYPEW_pure_w_poly, execute_RTYPEW_pure_32_w_poly]
  -- Goal: BitVec.signExtend 64 (HWord.toBitVec32_poly #v[a0, a1])
  --     = sign_extend (m := 64) (low_b.toBitVec32_poly >>> setWidth 5 low_c.toBitVec32_poly)
  -- Bridge sign_extend to BitVec.signExtend by definitional unfolding.
  change BitVec.signExtend 64 (HWord.toBitVec32_poly #v[a0, a1])
       = BitVec.signExtend 64 ((Word.low_poly #v[b0, b1, b2, b3]).toBitVec32_poly >>>
          BitVec.setWidth 5 (Word.low_poly #v[c0, c1, c2, c3]).toBitVec32_poly)
  -- Reduce to 32-bit equality (signExtend on BitVec 32 → 64 is injective).
  congr 1
  -- Goal: HWord.toBitVec32_poly #v[a0, a1]
  --     = (Word.low_poly #v[b0,b1,b2,b3]).toBitVec32_poly >>> setWidth 5 (Word.low_poly #v[c0,c1,c2,c3]).toBitVec32_poly
  -- Step 1: derive is_U32 for low halves.
  have h_isU32_b_lo : (Word.low_poly #v[b0, b1, b2, b3]).isU32_poly :=
    Word.isU64_poly_low_poly_isU32_poly is_U64_b
  have h_isU32_c_lo : (Word.low_poly #v[c0, c1, c2, c3]).isU32_poly :=
    Word.isU64_poly_low_poly_isU32_poly is_U64_c
  -- Step 2: reduce the BitVec 32 equality to toNat equality + unfold the shift.
  rw [← BitVec.toNat_inj]
  simp only [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, BitVec.toNat_setWidth,
             Nat.shiftRight_eq_div_pow]
  -- Step 4: reduce the shift count to `c0.val % 32`.
  have h_shift_eq : (Word.low_poly #v[c0, c1, c2, c3]).toBitVec32_poly.toNat % 2 ^ 5
                  = c0.val % 32 := by
    rw [HWord.toBitVec32_poly_toNat_poly h_isU32_c_lo]
    simp [Word.low_poly, HWord.toNat_poly]
    omega
  rw [h_shift_eq]; clear h_shift_eq
  -- Step 5: keep LHS in HWord form (avoid unfolding via HWord.toBitVec32_poly_toNat_poly).
  -- The new helpers srlw_close_su16_{0,1}_case conclude at HWord level, so we want
  -- to apply them directly without re-folding. Simp only unfolds Word.low_poly to
  -- reduce #v[b0,b1,b2,b3] → #v[b0,b1].
  simp only [Word.low_poly, Vector.getElem_mk, List.getElem_toArray,
             List.getElem_cons_zero, List.getElem_cons_succ]
  -- Goal: (HWord.toBitVec32_poly #v[a0, a1]).toNat
  --     = (HWord.toBitVec32_poly #v[b0, b1]).toNat / 2 ^ (c0.val % 32)
  -- Step 6: derive c0.val % 32 = (cb0 + cb1*2 + cb2*4 + cb3*8 + cb4*16 : ZMod p).val.
  have h_cb_sum_lt_64 : (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32 : ZMod p).val < 64 := by
    have hb0 : cb0.val ≤ 1 := by rcases b_cb0 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
    have hb1 : cb1.val ≤ 1 := by rcases b_cb1 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
    have hb2 : cb2.val ≤ 1 := by rcases b_cb2 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
    have hb3 : cb3.val ≤ 1 := by rcases b_cb3 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
    have hb4 : cb4.val ≤ 1 := by rcases b_cb4 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
    have hb5 : cb5.val ≤ 1 := by rcases b_cb5 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
    have h_eq := cb_sum_val_eq_poly b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
    omega
  have h_val_10 : (10 : ZMod p).val = 10 := by
    rw [show (10 : ZMod p) = ((10 : ℕ) : ZMod p) from by push_cast; rfl]
    exact ZMod.val_natCast_of_lt (by omega)
  have h_diff := diff h_sum_ne
  rw [h_val_10] at h_diff
  have h_c0_mod_64 : c0.val % 64 = (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32 : ZMod p).val := by
    apply is_mod_64_poly (m := cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32)
    · exact h_cb_sum_lt_64
    · exact c0_16
    · exact h_diff
  -- Bridge: c0.val % 32 = (cb0 + cb1*2 + cb2*4 + cb3*8 + cb4*16 : ZMod p).val.
  -- We don't need cb5 = 0; instead derive % 32 from % 64 via mod-of-mod, since the
  -- low 5 bits of c0 are what SRLW uses regardless of cb5.
  have h_cb_sum_eq := cb_sum_val_eq_poly b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
  have hb0_le : cb0.val ≤ 1 := by rcases b_cb0 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
  have hb1_le : cb1.val ≤ 1 := by rcases b_cb1 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
  have hb2_le : cb2.val ≤ 1 := by rcases b_cb2 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
  have hb3_le : cb3.val ≤ 1 := by rcases b_cb3 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
  have hb4_le : cb4.val ≤ 1 := by rcases b_cb4 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
  -- (cb-sum-5).val = cb0.val + cb1.val*2 + cb2.val*4 + cb3.val*8 + cb4.val*16
  have v_2 : (2 : ZMod p).val = 2 := val_2_zmod_p
  have v_4 : (4 : ZMod p).val = 4 := val_4_zmod_p
  have v_8 : (8 : ZMod p).val = 8 := val_8_zmod_p
  have v_16 : (16 : ZMod p).val = 16 := val_16_zmod_p
  have m1 : (cb1 * 2 : ZMod p).val = cb1.val * 2 := by
    rw [ZMod.val_mul_of_lt]
    · rw [v_2]
    · rw [v_2]; omega
  have m2 : (cb2 * 4 : ZMod p).val = cb2.val * 4 := by
    rw [ZMod.val_mul_of_lt]
    · rw [v_4]
    · rw [v_4]; omega
  have m3 : (cb3 * 8 : ZMod p).val = cb3.val * 8 := by
    rw [ZMod.val_mul_of_lt]
    · rw [v_8]
    · rw [v_8]; omega
  have m4 : (cb4 * 16 : ZMod p).val = cb4.val * 16 := by
    rw [ZMod.val_mul_of_lt]
    · rw [v_16]
    · rw [v_16]; omega
  have a1_val : (cb0 + cb1 * 2 : ZMod p).val = cb0.val + cb1.val * 2 := by
    rw [ZMod.val_add_of_lt]
    · rw [m1]
    · rw [m1]; omega
  have a2_val : (cb0 + cb1 * 2 + cb2 * 4 : ZMod p).val =
      cb0.val + cb1.val * 2 + cb2.val * 4 := by
    rw [ZMod.val_add_of_lt]
    · rw [a1_val, m2]
    · rw [a1_val, m2]; omega
  have a3_val : (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 : ZMod p).val =
      cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 := by
    rw [ZMod.val_add_of_lt]
    · rw [a2_val, m3]
    · rw [a2_val, m3]; omega
  have h_cb_sum_5_val : (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 : ZMod p).val =
      cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 + cb4.val * 16 := by
    rw [ZMod.val_add_of_lt]
    · rw [a3_val, m4]
    · rw [a3_val, m4]; omega
  have h_c0_mod_32 : c0.val % 32 =
      (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 : ZMod p).val := by
    have h_dvd : c0.val % 32 = c0.val % 64 % 32 := by
      rw [Nat.mod_mod_of_dvd]; exact ⟨2, rfl⟩
    rw [h_dvd, h_c0_mod_64, h_cb_sum_eq, h_cb_sum_5_val]; omega
  rw [h_c0_mod_32]
  clear h_c0_mod_32 h_c0_mod_64 h_cb_sum_5_val a3_val a2_val a1_val m4 m3 m2 m1
    v_16 v_8 v_4 v_2 hb0_le hb1_le hb2_le hb3_le hb4_le h_cb_sum_eq h_cb_sum_lt_64
    h_diff h_val_10
  -- Goal: (HWord.toBitVec32_poly #v[a0, a1]).toNat
  --     = (HWord.toBitVec32_poly #v[b0, b1]).toNat
  --         / 2 ^ (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 : ZMod p).val
  -- Step 7: resolve srw_00, srw_01, srw_10, srw_11 disjunct gates under SRLW.
  rw [h_no_sraw, eq_srlw] at srw_00 srw_01 srw_10 srw_11
  simp only [add_zero] at srw_00 srw_01 srw_10 srw_11
  simp only [show ((1 : ZMod p) = 0) ↔ False from ⟨h_one_ne_zero, False.elim⟩, false_or]
    at srw_00 srw_01 srw_10 srw_11
  -- srw_00 : su160 = 0 ∨ a0 = lr0
  -- srw_01 : su160 = 0 ∨ a1 = lr1 + (msb_b * 65536 - smv)
  -- srw_10 : su161 = 0 ∨ a0 = lr1 + (msb_b * 65536 - smv)
  -- srw_11 : su161 = 0 ∨ a1 = msb_b * 65535
  -- Step 8: derive msb_b = 0 from w_msb_b under SRLW (srl + srlw = 0 + 1 = 1 ≠ 0).
  rw [h_no_srl, eq_srlw] at w_msb_b
  simp only [zero_add,
             show ((1 : ZMod p) = 0) ↔ False from ⟨h_one_ne_zero, False.elim⟩, false_or]
    at w_msb_b
  have h_msb_b_zero : msb_b = 0 := w_msb_b
  -- eq_smv : smv = msb_b * v0123 = 0
  rw [h_msb_b_zero, zero_mul] at eq_smv
  -- Simplify correction terms in srw_01, srw_10, srw_11.
  simp only [h_msb_b_zero, eq_smv, zero_mul, add_zero, sub_self]
    at srw_01 srw_10 srw_11
  -- srw_01 : su160 = 0 ∨ a1 = lr1
  -- srw_10 : su161 = 0 ∨ a0 = lr1
  -- srw_11 : su161 = 0 ∨ a1 = 0
  -- Step 9: resolve su16 dispatch from cb4 mutex constraints under SRLW (srl+sra=0).
  rw [h_no_srl, h_no_sra] at h_su160 h_su161 h_su162 h_su163 one_of_su16s
  simp only [add_zero, zero_add, mul_zero]
    at h_su160 h_su161 h_su162 h_su163 one_of_su16s
  -- h_su160 : su160 = 0 ∨ cb4 = 0
  -- h_su161 : su161 = 0 ∨ cb4 = 1
  -- h_su162 : su162 = 0 ∨ cb4 = 2  -- forces su162 = 0 (cb4 ∈ {0,1})
  -- h_su163 : su163 = 0 ∨ cb4 = 3  -- forces su163 = 0
  -- one_of_su16s : srl + sra + srlw + sraw = 0 ∨ su160 + su161 + su162 + su163 = 1
  rw [h_no_sraw, eq_srlw] at one_of_su16s
  simp only [add_zero,
             show ((1 : ZMod p) = 0) ↔ False from ⟨h_one_ne_zero, False.elim⟩, false_or]
    at one_of_su16s
  -- one_of_su16s : su160 + su161 + su162 + su163 = 1
  -- Step 10: cb4 case-split with 16-leaf blast in each. Substitute cb4 INSIDE
  -- each branch to make the constant-comparison disjuncts resolvable
  -- (mirrors Srl.lean:287-311 pattern).
  rcases b_cb4 with hcb4 | hcb4
  · -- cb4 = 0: su160 = 1, others = 0.
    rw [hcb4] at h_su160 h_su161 h_su162 h_su163
    -- h_su160 : su160 = 0 ∨ 0 = 0   (right disjunct True; no info)
    -- h_su161 : su161 = 0 ∨ 0 = 1   (right disjunct False)
    -- h_su162 : su162 = 0 ∨ 0 = 2   (right disjunct False)
    -- h_su163 : su163 = 0 ∨ 0 = 3   (right disjunct False)
    have h_su161_zero : su161 = 0 :=
      h_su161.resolve_right (fun h => h_one_ne_zero (by linear_combination -h))
    have h_su162_zero : su162 = 0 :=
      h_su162.resolve_right (fun h => val_2_ne_zero (by linear_combination -h))
    have h_su163_zero : su163 = 0 :=
      h_su163.resolve_right (fun h => val_3_ne_zero (by linear_combination -h))
    have h_su160_eq : su160 = 1 := by
      have := one_of_su16s
      rw [h_su161_zero, h_su162_zero, h_su163_zero, add_zero, add_zero, add_zero] at this
      exact this
    have h_su160_ne_zero : su160 ≠ 0 := by rw [h_su160_eq]; exact h_one_ne_zero
    have h_a0_eq : a0 = lr0 := srw_00.resolve_left h_su160_ne_zero
    have h_a1_eq : a1 = lr1 := srw_01.resolve_left h_su160_ne_zero
    -- Substitute a0, a1 then expand lr0, lr1 via eq_lr0, eq_lr1.
    rw [h_a0_eq, h_a1_eq, eq_lr0, eq_lr1, eq_ll2, zero_mul, add_zero]
    -- Goal: (HWord.toBitVec32_poly #v[hl0 + ll1*v0123, hl1]).toNat
    --     = (HWord.toBitVec32_poly #v[b0, b1]).toNat
    --         / 2 ^ (cb0 + cb1*2 + cb2*4 + cb3*8 + cb4*16 : ZMod p).val
    -- 16-way rcases on cb0..cb3, apply srlw_close_su16_0_case per leaf.
    rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
      rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
    · -- (0,0,0,0): S=0, M=65536, N=1
      exact srlw_close_su16_0_case 0 (by omega) 65536 1 (by decide) (by omega) rfl rfl
        (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
    · -- (0,0,0,1): S=8, M=256, N=256
      exact srlw_close_su16_0_case 8 (by omega) 256 256 (by decide) (by omega) rfl rfl
        (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
    · -- (0,0,1,0): S=4, M=4096, N=16
      exact srlw_close_su16_0_case 4 (by omega) 4096 16 (by decide) (by omega) rfl rfl
        (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
    · -- (0,0,1,1): S=12, M=16, N=4096
      exact srlw_close_su16_0_case 12 (by omega) 16 4096 (by decide) (by omega) rfl rfl
        (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
    · -- (0,1,0,0): S=2, M=16384, N=4
      exact srlw_close_su16_0_case 2 (by omega) 16384 4 (by decide) (by omega) rfl rfl
        (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
    · -- (0,1,0,1): S=10, M=64, N=1024
      exact srlw_close_su16_0_case 10 (by omega) 64 1024 (by decide) (by omega) rfl rfl
        (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
    · -- (0,1,1,0): S=6, M=1024, N=64
      exact srlw_close_su16_0_case 6 (by omega) 1024 64 (by decide) (by omega) rfl rfl
        (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
    · -- (0,1,1,1): S=14, M=4, N=16384
      exact srlw_close_su16_0_case 14 (by omega) 4 16384 (by decide) (by omega) rfl rfl
        (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
    · -- (1,0,0,0): S=1, M=32768, N=2
      exact srlw_close_su16_0_case 1 (by omega) 32768 2 (by decide) (by omega) rfl rfl
        (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
    · -- (1,0,0,1): S=9, M=128, N=512
      exact srlw_close_su16_0_case 9 (by omega) 128 512 (by decide) (by omega) rfl rfl
        (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
    · -- (1,0,1,0): S=5, M=2048, N=32
      exact srlw_close_su16_0_case 5 (by omega) 2048 32 (by decide) (by omega) rfl rfl
        (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
    · -- (1,0,1,1): S=13, M=8, N=8192
      exact srlw_close_su16_0_case 13 (by omega) 8 8192 (by decide) (by omega) rfl rfl
        (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
    · -- (1,1,0,0): S=3, M=8192, N=8
      exact srlw_close_su16_0_case 3 (by omega) 8192 8 (by decide) (by omega) rfl rfl
        (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
    · -- (1,1,0,1): S=11, M=32, N=2048
      exact srlw_close_su16_0_case 11 (by omega) 32 2048 (by decide) (by omega) rfl rfl
        (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
    · -- (1,1,1,0): S=7, M=512, N=128
      exact srlw_close_su16_0_case 7 (by omega) 512 128 (by decide) (by omega) rfl rfl
        (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
    · -- (1,1,1,1): S=15, M=2, N=32768
      exact srlw_close_su16_0_case 15 (by omega) 2 32768 (by decide) (by omega) rfl rfl
        (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
  · -- cb4 = 1: su161 = 1, others = 0.
    rw [hcb4] at h_su160 h_su161 h_su162 h_su163
    -- h_su160 : su160 = 0 ∨ 1 = 0
    -- h_su161 : su161 = 0 ∨ 1 = 1   (right disjunct True; no info)
    -- h_su162 : su162 = 0 ∨ 1 = 2
    -- h_su163 : su163 = 0 ∨ 1 = 3
    have h_su160_zero : su160 = 0 :=
      h_su160.resolve_right h_one_ne_zero
    have h_su162_zero : su162 = 0 := by
      apply h_su162.resolve_right
      intro h
      have hv1 : (1 : ZMod p).val = 1 := ZMod.val_one p
      have hv2 : (2 : ZMod p).val = 2 := val_2_zmod_p
      have hval := congrArg ZMod.val h
      rw [hv1, hv2] at hval
      omega
    have h_su163_zero : su163 = 0 := by
      apply h_su163.resolve_right
      intro h
      have hv1 : (1 : ZMod p).val = 1 := ZMod.val_one p
      have hv3 : (3 : ZMod p).val = 3 := by
        rw [show (3 : ZMod p) = ((3 : ℕ) : ZMod p) from by push_cast; rfl]
        exact ZMod.val_natCast_of_lt (by have := Fact.out (p := 2 ^ 17 < p); omega)
      have hval := congrArg ZMod.val h
      rw [hv1, hv3] at hval
      omega
    have h_su161_eq : su161 = 1 := by
      have := one_of_su16s
      rw [h_su160_zero, h_su162_zero, h_su163_zero, zero_add, add_zero, add_zero] at this
      exact this
    have h_su161_ne_zero : su161 ≠ 0 := by rw [h_su161_eq]; exact h_one_ne_zero
    have h_a0_eq : a0 = lr1 := srw_10.resolve_left h_su161_ne_zero
    have h_a1_eq : a1 = 0 := srw_11.resolve_left h_su161_ne_zero
    rw [h_a0_eq, h_a1_eq, eq_lr1, eq_ll2, zero_mul, add_zero]
    -- Goal: (HWord.toBitVec32_poly #v[hl1, 0]).toNat
    --     = (HWord.toBitVec32_poly #v[b0, b1]).toNat
    --         / 2 ^ (cb0 + cb1*2 + cb2*4 + cb3*8 + cb4*16 : ZMod p).val
    -- 16-way rcases on cb0..cb3, apply srlw_close_su16_1_case per leaf.
    rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
      rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
    · -- (0,0,0,0): S=0, M=65536, N=1, byte_shift=1 → total shift = 16
      exact srlw_close_su16_1_case 0 (by omega) 65536 1 (by decide) (by omega) rfl rfl
        (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
    · -- (0,0,0,1): S=8 → total 24
      exact srlw_close_su16_1_case 8 (by omega) 256 256 (by decide) (by omega) rfl rfl
        (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
    · -- (0,0,1,0): S=4 → total 20
      exact srlw_close_su16_1_case 4 (by omega) 4096 16 (by decide) (by omega) rfl rfl
        (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
    · -- (0,0,1,1): S=12 → total 28
      exact srlw_close_su16_1_case 12 (by omega) 16 4096 (by decide) (by omega) rfl rfl
        (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
    · -- (0,1,0,0): S=2 → total 18
      exact srlw_close_su16_1_case 2 (by omega) 16384 4 (by decide) (by omega) rfl rfl
        (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
    · -- (0,1,0,1): S=10 → total 26
      exact srlw_close_su16_1_case 10 (by omega) 64 1024 (by decide) (by omega) rfl rfl
        (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
    · -- (0,1,1,0): S=6 → total 22
      exact srlw_close_su16_1_case 6 (by omega) 1024 64 (by decide) (by omega) rfl rfl
        (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
    · -- (0,1,1,1): S=14 → total 30
      exact srlw_close_su16_1_case 14 (by omega) 4 16384 (by decide) (by omega) rfl rfl
        (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
    · -- (1,0,0,0): S=1 → total 17
      exact srlw_close_su16_1_case 1 (by omega) 32768 2 (by decide) (by omega) rfl rfl
        (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
    · -- (1,0,0,1): S=9 → total 25
      exact srlw_close_su16_1_case 9 (by omega) 128 512 (by decide) (by omega) rfl rfl
        (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
    · -- (1,0,1,0): S=5 → total 21
      exact srlw_close_su16_1_case 5 (by omega) 2048 32 (by decide) (by omega) rfl rfl
        (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
    · -- (1,0,1,1): S=13 → total 29
      exact srlw_close_su16_1_case 13 (by omega) 8 8192 (by decide) (by omega) rfl rfl
        (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
    · -- (1,1,0,0): S=3 → total 19
      exact srlw_close_su16_1_case 3 (by omega) 8192 8 (by decide) (by omega) rfl rfl
        (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
    · -- (1,1,0,1): S=11 → total 27
      exact srlw_close_su16_1_case 11 (by omega) 32 2048 (by decide) (by omega) rfl rfl
        (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
    · -- (1,1,1,0): S=7 → total 23
      exact srlw_close_su16_1_case 7 (by omega) 512 128 (by decide) (by omega) rfl rfl
        (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
    · -- (1,1,1,1): S=15 → total 31
      exact srlw_close_su16_1_case 15 (by omega) 2 32768 (by decide) (by omega) rfl rfl
        (by omega) (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
        (by rw [hcb0, hcb1, hcb2, hcb3, hcb4]; push_cast; ring)
        lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec

lemma spec.srlw_poly (Main : Vector (ZMod p) 69) (h : is_srlw_poly Main) :
    (constraints Main).allHold_poly →
      Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] =
        execute_RTYPEW_pure_w_poly #v[Main[15], Main[16], Main[17], Main[18]]
          #v[Main[25], Main[26], Main[27], Main[28]] .SRLW :=
  fun cstrs => spec.srlw_common_poly Main cstrs h.1

lemma spec.srliw_poly (Main : Vector (ZMod p) 69) (h : is_srliw_poly Main) :
    (constraints Main).allHold_poly →
      Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] =
        execute_RTYPEW_pure_w_poly #v[Main[15], Main[16], Main[17], Main[18]]
          #v[Main[25], Main[26], Main[27], Main[28]] .SRLW :=
  fun cstrs => spec.srlw_common_poly Main cstrs h.1

end srlw_poly

end ShiftRight
