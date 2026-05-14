import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader
import SP1Chips.ShiftRight.Constraints

namespace ShiftRight

set_option linter.style.setOption false
-- Imbalanced goal tree: proof applies tactics per-focused-case.
set_option linter.style.multiGoal false
-- Unused variables expected because many proofs are currently stopped.
set_option linter.unusedVariables false
set_option maxHeartbeats 100000000

variable (Main : Vector (Fin KB) 69)
variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

def is_real : Prop := Main[64] = 1 ∨ Main[65] = 1 ∨ Main[66] = 1 ∨ Main[67] = 1

omit [Fact (2 ^ 17 < p)] in
@[simp] def is_real_poly (Main : Vector (ZMod p) 69) : Prop :=
  Main[64] = 1 ∨ Main[65] = 1 ∨ Main[66] = 1 ∨ Main[67] = 1

section field_arithmetic

lemma cancel_mul_65536_v1 {a b c x : Fin KB} (h_dvd : (x : ℕ) ∣ 65536) : a * x = b * 65536 + c * x → a = b * ((65536 : ℕ) / (x : ℕ)) + c
  := by
  obtain ⟨z, h_eq⟩ := h_dvd; rw [h_eq]
  have x_pos : 0 < (x : ℕ) := by nlinarith
  have xz_BB : (x : ℕ) * z < 2130706433 := by nlinarith
  have z_BB : z < 2130706433 := by nlinarith
  have h_eq_BB : 65536 = x * z := by
    apply Fin.ext
    simp [Fin.mul_def, Nat.mod_eq_of_lt z_BB, Nat.mod_eq_of_lt xz_BB]
    have hz : ((z : Fin 2130706433) : ℕ) = z := Nat.mod_eq_of_lt z_BB
    rw [hz, Nat.mod_eq_of_lt xz_BB]
    exact h_eq
  rw [h_eq_BB]
  rw [mul_comm x z, ← mul_assoc, ← right_distrib]
  intro eq; apply mul_right_cancel₀ (by omega) at eq; rw [eq]
  congr
  rw [Fin.ext_iff]
  change z % 2130706433 = (↑x * z % 2130706433 / (x.val % 2130706433))
  rw [Nat.mod_eq_of_lt z_BB, Nat.mod_eq_of_lt xz_BB, Nat.mod_eq_of_lt x.isLt,
    Nat.mul_div_cancel_left _ x_pos]

lemma cancel_mul_65536_v2 {b c x : Fin KB} (h_dvd : (x : ℕ) ∣ 65536) : b * 65536 + c * x = 0 → b * ((65536 : ℕ) / (x : ℕ)) + c = 0
  := by intro h_eq; symm; apply cancel_mul_65536_v1 <;> aesop

lemma is_mod_64 {c0 m : Fin KB} : m < 64 → c0 < 65536 → ((c0 - m) * 2097414145).val < 1024 → c0.val % 64 = m := by
  simp [Fin.sub_def, Fin.mul_def, Fin.lt_def]; ring_nf
  intro hm hc hdiff
  suffices : (BitVec.ofNat 64 c0.val) % 64#64 = BitVec.ofNat 64 m.val
  · simp [BitVec.toNat_eq] at this
    repeat rw [Nat.mod_eq_of_lt (b := 18446744073709551616) (by omega)] at this
    assumption
  · suffices : ((2130706433 - BitVec.ofNat 64 ↑m) * BitVec.ofNat 64 2097414145 + BitVec.ofNat 64 ↑c0 * 2097414145#64) % 2130706433#64 < 1024#64
    · clear hdiff
      have : BitVec.ofNat 64 c0.val < 65536 := by simp; omega
      have : BitVec.ofNat 64 m.val < 64 := by simp; omega
      clear hm
      trans (BitVec.ofNat 64 ↑c0) &&& 63#64
      · bv_decide
      · bv_decide
    · rw [← BitVec.ult_iff_lt]
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, BitVec.toNat_umod, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_mul]
      simp [-BitVec.toNat_sub]
      rw [BitVec.toNat_sub_of_le] <;> simp
      · repeat rw [Nat.mod_eq_of_lt (b := 18446744073709551616) (by omega)]
        assumption
      · omega

/-- `(msb * 65535).val < 65536` whenever `msb ∈ {0, 1}`. Shared helper for the
inline `(msb_X * 65535).val < 65536` proofs inside `ops_U64_a`. -/
lemma bool_mul_65535_lt {b : Fin KB} (hb : b = 0 ∨ b = 1) :
    (b * 65535).val < 65536 := by
  rcases hb <;> simp_all

/-- Shared pattern for the `aK_16` proofs inside `ops_U64_a`: a 16-way case split on
`cb0..cb3` closed by `omega` using the limb bounds. -/
lemma limb_16_of_cancel
    {hl_lo hl_hi ll_lo ll_hi : Fin KB}
    {cb0 cb1 cb2 cb3 : Fin KB}
    (b_cb0 : cb0 = 0 ∨ cb0 = 1) (b_cb1 : cb1 = 0 ∨ cb1 = 1)
    (b_cb2 : cb2 = 0 ∨ cb2 = 1) (b_cb3 : cb3 = 0 ∨ cb3 = 1)
    (_lt_ll_lo : ll_lo.val < 2 ^ (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8).val)
    (lt_hl_lo : hl_lo.val < 2 ^ (16 - (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8)).val)
    (lt_ll_hi : ll_hi.val < 2 ^ (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8).val)
    (_lt_hl_hi : hl_hi.val < 2 ^ (16 - (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8)).val) :
    (hl_lo + ll_hi * ((1 - cb0 + 1) * 2 * ((1 - cb1) * 3 + 1) * ((1 - cb2) * 15 + 1) * ((1 - cb3) * 255 + 1))).val < 65536 := by
  rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all
  all_goals {
    simp [Fin.val_add, Fin.val_mul]
    repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
    omega
  }

end field_arithmetic

section opcodes

@[simp] def is_srl := Main[64] = 1 ∧ Main[31] = 0
omit [Fact (2 ^ 17 < p)] in
@[simp] def is_srl_poly (Main : Vector (ZMod p) 69) := Main[64] = 1 ∧ Main[31] = 0

@[simp] def is_sra := Main[65] = 1 ∧ Main[31] = 0
omit [Fact (2 ^ 17 < p)] in
@[simp] def is_sra_poly (Main : Vector (ZMod p) 69) := Main[65] = 1 ∧ Main[31] = 0

@[simp] def is_srlw := Main[66] = 1 ∧ Main[31] = 0
omit [Fact (2 ^ 17 < p)] in
@[simp] def is_srlw_poly (Main : Vector (ZMod p) 69) := Main[66] = 1 ∧ Main[31] = 0

@[simp] def is_sraw := Main[67] = 1 ∧ Main[31] = 0
omit [Fact (2 ^ 17 < p)] in
@[simp] def is_sraw_poly (Main : Vector (ZMod p) 69) := Main[67] = 1 ∧ Main[31] = 0

@[simp] def is_srli := Main[64] = 1 ∧ Main[31] = 1
omit [Fact (2 ^ 17 < p)] in
@[simp] def is_srli_poly (Main : Vector (ZMod p) 69) := Main[64] = 1 ∧ Main[31] = 1

@[simp] def is_srai := Main[65] = 1 ∧ Main[31] = 1
omit [Fact (2 ^ 17 < p)] in
@[simp] def is_srai_poly (Main : Vector (ZMod p) 69) := Main[65] = 1 ∧ Main[31] = 1

@[simp] def is_srliw := Main[66] = 1 ∧ Main[31] = 1
omit [Fact (2 ^ 17 < p)] in
@[simp] def is_srliw_poly (Main : Vector (ZMod p) 69) := Main[66] = 1 ∧ Main[31] = 1

@[simp] def is_sraiw := Main[67] = 1 ∧ Main[31] = 1
omit [Fact (2 ^ 17 < p)] in
@[simp] def is_sraiw_poly (Main : Vector (ZMod p) 69) := Main[67] = 1 ∧ Main[31] = 1

lemma single_op : List.Forall SP1Constraint.toProp (constraints Main) →
  (Main[64] = 1 → Main[65] = 0 ∧ Main[66] = 0 ∧ Main[67] = 0) ∧
  (Main[65] = 1 → Main[64] = 0 ∧ Main[66] = 0 ∧ Main[67] = 0) ∧
  (Main[66] = 1 → Main[64] = 0 ∧ Main[65] = 0 ∧ Main[67] = 0) ∧
  (Main[67] = 1 → Main[64] = 0 ∧ Main[65] = 0 ∧ Main[66] = 0)
   := by
  intro cstrs
  replace cstrs := (allHold_constraints_iff Main).mp cstrs
  obtain ⟨h_msb_b3, h_msb_b1, h_msb_a1, cpu, alu,
            b_srl, b_sra, b_srlw, b_sraw, one_of_ops, rest⟩ := cstrs
  clear *- b_srl b_sra b_srlw b_sraw one_of_ops
  aesop

lemma single_su16 : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main →
  (Main[60] = 1 → Main[61] = 0 ∧ Main[62] = 0 ∧ Main[63] = 0) ∧
  (Main[61] = 1 → Main[60] = 0 ∧ Main[62] = 0 ∧ Main[63] = 0) ∧
  (Main[62] = 1 → Main[60] = 0 ∧ Main[61] = 0 ∧ Main[63] = 0) ∧
  (Main[63] = 1 → Main[60] = 0 ∧ Main[61] = 0 ∧ Main[62] = 0)
   := by
  intro cstrs real
  have ⟨srl, srlw, sra, sraw⟩ := single_op Main cstrs
  replace cstrs := (allHold_constraints_iff Main).mp cstrs; simp [is_real] at real
  obtain ⟨h_msb_b3, h_msb_b1, h_msb_a1, cpu, alu,
            b_srl, b_sra, b_srlw, b_sraw, one_of_ops, eq_bop,
            b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
            h_su160, b_su160, h_su161, b_su161, h_su162, b_su162, h_su163, b_su163, one_of_su16s,
            eq_v01, eq_v012, eq_v0123,
            lt_ll0, lt_hl0, h_b0_dec, lt_ll1, lt_hl1, h_b1_dec,
            lt_ll2, lt_hl2, h_b2_dec, lt_ll3, lt_hl3, h_b3_dec,
            eq_lr0, eq_lr1, eq_lr2, eq_lr3,
            w_msb_b, eq_smv, w_msb_srv, sr_rest⟩ := cstrs
  obtain ⟨nw_00, nw_01, nw_02, nw_03, nw_04, nw_05, nw_06, nw_07, nw_08, nw_09, nw_10, nw_11, nw_12, nw_13, nw_14, nw_15,
            w_00, w_01, w_02, w_03, w_04, w_05⟩ := sr_rest
  clear *- real srl srlw sra sraw b_su160 b_su161 b_su162 b_su163 one_of_su16s
  rcases one_of_su16s
  · rcases real with _ | _ | _ | _ <;> simp_all
  · clear real srl srlw sra sraw; aesop

end opcodes

section is_real

lemma srl_real : Main[64] = 1 → is_real Main := by simp [is_real]; aesop
lemma sra_real : Main[65] = 1 → is_real Main := by simp [is_real]; aesop
lemma srlw_real : Main[66] = 1 → is_real Main := by simp [is_real]; aesop
lemma sraw_real : Main[67] = 1 → is_real Main := by simp [is_real]; aesop

end is_real

section entailed_constraints

lemma register_bounds : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main →
  let imm := Main[31]
  Main[6] < 32 ∧ Main[14] < 32 ∧ (imm = 0 → Main[21] < 32) ∧ Main[3] < 65536
    := by
  intro cstrs real
  have ⟨sop1, sop2, sop3, sop4⟩ := single_op Main cstrs
  simp [is_real] at real
  replace cstrs := (allHold_constraints_iff Main).mp cstrs
  obtain ⟨h0, h1, h2, h3, alu,
            b_srl, b_sra, b_srlw, b_sraw, one_of_ops, h4⟩ := cstrs
  clear h0 h1 h2 h3 h4
  rw [ALUTypeReader.allHold_constraints_iff_is_real (h_trusted := rfl)] at alu
  · obtain ⟨h0, h1, h2, h3, h4, h5, b_imm, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := alu
    rcases real with srl | sra | srlw | sraw <;> simp_all [Opcode.ofNat, Nat.ble, Nat.beq] <;>
    rcases b_imm <;> simp_all
  · clear alu; rcases real with srl | sra | srlw | sraw <;> simp_all

lemma immediate_bounds : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main →
  let imm := Main[31]
  (imm = 1 →
    (Main[21] = Main[25] ∧ Main[26] = 0 ∧ Main[27] = 0 ∧ Main[28] = 0 ∧
      ((Main[64] = 1 ∨ Main[65] = 1 → Main[25] < 64) ∧
       (Main[66] = 1 ∨ Main[67] = 1 → Main[25] < 32)))) := by
  intro cstrs real
  have ⟨sop1, sop2, sop3, sop4⟩ := single_op Main cstrs
  simp [is_real] at real
  replace cstrs := (allHold_constraints_iff Main).mp cstrs
  obtain ⟨h0, h1, h2, h3, alu,
            b_srl, b_sra, b_srlw, b_sraw, one_of_ops, h4⟩ := cstrs
  clear h0 h1 h2 h3 h4
  rw [ALUTypeReader.allHold_constraints_iff_is_real (h_trusted := rfl)] at alu
  · obtain ⟨h0, h1, h2, h3, h4, h5, b_imm, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := alu
    rcases real with srl | sra | srlw | sraw <;> simp_all [Opcode.ofNat, Nat.ble, Nat.beq] <;>
      intro h31 <;> exact (h0.2 h31).2.1
  · clear alu; rcases real with srl | sra | srlw | sraw <;> simp_all

lemma op_a_is_0 : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main →
  (Main[6] = 0 → Main[32] = 0 ∧ Main[33] = 0 ∧ Main[34] = 0 ∧ Main[35] = 0) := by
  intro cstrs real
  have ⟨sop1, sop2, sop3, sop4⟩ := single_op Main cstrs
  have ⟨su1, su2, su3, su4⟩ := single_su16 Main cstrs real
  simp [is_real] at real
  replace cstrs := (allHold_constraints_iff Main).mp cstrs
  obtain ⟨h0, h1, h2, h3, alu,
            b_srl, b_sra, b_srlw, b_sraw, one_of_ops, h4⟩ := cstrs
  clear h0 h1 h2 h3 h4
  rw [ALUTypeReader.allHold_constraints_iff_is_real (h_trusted := rfl)] at alu
  · obtain ⟨h0, h1, h2, h3, h4, h5, b_imm, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := alu
    clear *- h4 h5 h18; simp_all; aesop
  · clear alu; rcases real with srl | sra | srlw | sraw <;> simp_all

lemma ops_U64_b_c : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main →
  Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] ∧
  Word.isU64 #v[Main[25], Main[26], Main[27], Main[28]] := by
  intro cstrs real
  have ⟨sop1, sop2, sop3, sop4⟩ := single_op Main cstrs
  simp [is_real] at real
  replace cstrs := (allHold_constraints_iff Main).mp cstrs
  obtain ⟨h0, h1, h2, h3, alu,
          b_srl, b_sra, b_srlw, b_sraw, one_of_ops, h4⟩ := cstrs
  clear h0 h1 h2 h3 h4
  rw [ALUTypeReader.allHold_constraints_iff_is_real (h_trusted := rfl)] at alu
  · obtain ⟨h0, h1, h2, h3, h4, h5, b_imm, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := alu
    rcases real with srl | sra | srlw | sraw <;> simp_all [Opcode.ofNat, Nat.ble, Nat.beq] <;>
    rcases b_imm <;> simp_all <;> apply Word.isU64_of_cases <;> simp <;> omega
  · clear alu; rcases real with srl | sra | srlw | sraw <;> simp_all

lemma ops_U64_a : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main →
  Word.isU64 #v[Main[32], Main[33], Main[34], Main[35]] := by
  intro cstrs real
  have ⟨is_U64_b, is_U64_c⟩ := ops_U64_b_c Main cstrs real
  obtain ⟨b0_16, b1_16, b2_16, b3_16⟩ := Word.lt_cases_of_isU64 is_U64_b
  obtain ⟨c0_16, c1_16, c2_16, c3_16⟩ := Word.lt_cases_of_isU64 is_U64_c
  have ⟨sop1, sop2, sop3, sop4⟩ := single_op Main cstrs
  have ⟨su1, su2, su3, su4⟩ := single_su16 Main cstrs real
  simp [is_real] at real
  replace cstrs := (allHold_constraints_iff Main).mp cstrs
  obtain ⟨h_msb_b3, h_msb_b1, h_msb_a1, cpu, alu,
            b_srl, b_sra, b_srlw, b_sraw, one_of_ops, eq_bop,
            b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
            h_su160, b_su160, h_su161, b_su161, h_su162, b_su162, h_su163, b_su163, one_of_su16s,
            eq_v01, eq_v012, eq_v0123,
            lt_ll0, lt_hl0, h_b0_dec, lt_ll1, lt_hl1, h_b1_dec,
            lt_ll2, lt_hl2, h_b2_dec, lt_ll3, lt_hl3, h_b3_dec,
            eq_lr0, eq_lr1, eq_lr2, eq_lr3,
            w_msb_b, eq_smv, w_msb_srv, sr_rest⟩ := cstrs
  obtain ⟨nw_00, nw_01, nw_02, nw_03, nw_04, nw_05, nw_06, nw_07, nw_08, nw_09, nw_10, nw_11, nw_12, nw_13, nw_14, nw_15,
            w_00, w_01, w_02, w_03, w_04, w_05⟩ := sr_rest
  clear cpu alu
  set b0 := Main[15]
  set b1 := Main[16]
  set b2 := Main[17]
  set b3 := Main[18]
  set c0 := Main[25]
  set c1 := Main[26]
  set c2 := Main[27]
  set c3 := Main[28]
  set imm := Main[31]
  set a0 := Main[32]
  set a1 := Main[33]
  set a2 := Main[34]
  set a3 := Main[35]
  set msb_b := Main[36]
  set msb_srw := Main[37]
  set cb0 := Main[38]
  set cb1 := Main[39]
  set cb2 := Main[40]
  set cb3 := Main[41]
  set cb4 := Main[42]
  set cb5 := Main[43]
  set smv := Main[44]
  set v0123 := Main[45]
  set v012 := Main[46]
  set v01 := Main[47]
  set ll0 := Main[48]
  set ll1 := Main[49]
  set ll2 := Main[50]
  set ll3 := Main[51]
  set hl0 := Main[52]
  set hl1 := Main[53]
  set hl2 := Main[54]
  set hl3 := Main[55]
  set lr0 := Main[56]
  set lr1 := Main[57]
  set lr2 := Main[58]
  set lr3 := Main[59]
  set su160 := Main[60]
  set su161 := Main[61]
  set su162 := Main[62]
  set su163 := Main[63]
  set srl := Main[64]
  set sra := Main[65]
  set srlw := Main[66]
  set sraw := Main[67]
  set bop := Main[68]
  suffices : a0.val < 65536 ∧ a1.val < 65536 ∧ a2.val < 65536 ∧ a3.val < 65536
  · clear *- this
    apply Word.isU64_of_cases <;> simp_all
  · clear diff eq_bop
    rcases real with hsrl | hsra | hsrlw | hsraw
    · simp_all
      have a0_16 := limb_16_of_cancel b_cb0 b_cb1 b_cb2 b_cb3 lt_ll0 lt_hl0 lt_ll1 lt_hl1
      have a1_16 := limb_16_of_cancel b_cb0 b_cb1 b_cb2 b_cb3 lt_ll1 lt_hl1 lt_ll2 lt_hl2
      have a2_16 := limb_16_of_cancel b_cb0 b_cb1 b_cb2 b_cb3 lt_ll2 lt_hl2 lt_ll3 lt_hl3
      have a3_16 : hl3.val < 65536 := by
        clear *- b_cb0 b_cb1 b_cb2 b_cb3 b3_16 h_b3_dec lt_ll3 lt_hl3
        rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all
        all_goals { clear *- lt_hl3; omega }
      rcases b_su160 <;> simp_all
      rcases b_su161 <;> simp_all
      rcases b_su162 <;> simp_all
    · simp_all
      have a0_16 := limb_16_of_cancel b_cb0 b_cb1 b_cb2 b_cb3 lt_ll0 lt_hl0 lt_ll1 lt_hl1
      have a1_16 := limb_16_of_cancel b_cb0 b_cb1 b_cb2 b_cb3 lt_ll1 lt_hl1 lt_ll2 lt_hl2
      have a2_16 := limb_16_of_cancel b_cb0 b_cb1 b_cb2 b_cb3 lt_ll2 lt_hl2 lt_ll3 lt_hl3
      have a3_16 : (hl3 + (msb_b * 65536 - msb_b * ((1 - cb0 + 1) * 2 * ((1 - cb1) * 3 + 1) * ((1 - cb2) * 15 + 1) * ((1 - cb3) * 255 + 1)))).val < 65536 := by
        clear *- h_msb_b3 b_cb0 b_cb1 b_cb2 b_cb3 b3_16 h_b3_dec lt_ll3 lt_hl3
        rw [U16MSBOperation.allHold_constraints_iff] at h_msb_b3
        obtain ⟨_, b_msb_b3, _⟩ := h_msb_b3
        rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> rcases b_msb_b3 <;> simp_all
        all_goals { clear *- lt_hl3; omega }
      have msb_b : (msb_b * 65535).val < 65536 := by
        apply bool_mul_65535_lt
        rw [U16MSBOperation.allHold_constraints_iff] at h_msb_b3
        clear *- h_msb_b3; simp_all
      rcases b_su160 <;> simp_all
      rcases b_su161 <;> simp_all
      rcases b_su162 <;> simp_all
    · symm at h_b2_dec h_b3_dec
      simp_all
      have ⟨eq_hl2, eq_ll2⟩ : hl2 = 0 ∧ ll2 = 0 := by
        clear *- lt_hl2 lt_ll2 b_cb0 b_cb1 b_cb2 b_cb3 h_b2_dec
        rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all <;>
        apply (cancel_mul_65536_v2 (by simp)) at h_b2_dec <;>
        simp [Fin.ext_iff, Fin.add_def, Fin.mul_def] at h_b2_dec <;>
        rw [Nat.mod_eq_of_lt (by omega)] at h_b2_dec <;>
        split_ands <;> omega
      have ⟨eq_hl3, eq_ll3⟩ : hl3 = 0 ∧ ll3 = 0 := by
        clear *- lt_hl3 lt_ll3 b_cb0 b_cb1 b_cb2 b_cb3 h_b3_dec
        rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all <;>
        apply (cancel_mul_65536_v2 (by simp)) at h_b3_dec <;>
        simp [Fin.ext_iff, Fin.add_def, Fin.mul_def] at h_b3_dec <;>
        rw [Nat.mod_eq_of_lt (by omega)] at h_b3_dec <;>
        split_ands <;> omega
      simp [eq_hl2, eq_ll2, eq_hl3, eq_ll3] at *
      simp_all
      have a0_16 := limb_16_of_cancel b_cb0 b_cb1 b_cb2 b_cb3 lt_ll0 lt_hl0 lt_ll1 lt_hl1
      have a1_16 : hl1.val < 65536 := by
        clear *- b1_16 b2_16 b_cb0 b_cb1 b_cb2 b_cb3 h_b1_dec lt_ll1 lt_hl1
        rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all
        all_goals {
          try apply cancel_mul_65536_v1 (by simp) at h_b1_dec
          try simp [Fin.val_add, Fin.val_mul] at b1_16 b2_16 ⊢
          try omega
        }
      have msb_16 : (msb_srw * 65535).val < 65536 := by
        apply bool_mul_65535_lt
        rw [U16MSBOperation.allHold_constraints_iff] at h_msb_a1
        clear *- h_msb_a1; simp_all
      rcases b_su160 <;> simp_all
      rcases b_su161 <;> simp_all
      rcases b_su162 <;> simp_all
    · symm at h_b2_dec h_b3_dec
      simp_all
      have ⟨eq_hl2, eq_ll2⟩ : hl2 = 0 ∧ ll2 = 0 := by
        clear *- lt_hl2 lt_ll2 b_cb0 b_cb1 b_cb2 b_cb3 h_b2_dec
        rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all <;>
        apply (cancel_mul_65536_v2 (by simp)) at h_b2_dec <;>
        simp [Fin.ext_iff, Fin.add_def, Fin.mul_def] at h_b2_dec <;>
        rw [Nat.mod_eq_of_lt (by omega)] at h_b2_dec <;>
        split_ands <;> omega
      have ⟨eq_hl3, eq_ll3⟩ : hl3 = 0 ∧ ll3 = 0 := by
        clear *- lt_hl3 lt_ll3 b_cb0 b_cb1 b_cb2 b_cb3 h_b3_dec
        rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> simp_all <;>
        apply (cancel_mul_65536_v2 (by simp)) at h_b3_dec <;>
        simp [Fin.ext_iff, Fin.add_def, Fin.mul_def] at h_b3_dec <;>
        rw [Nat.mod_eq_of_lt (by omega)] at h_b3_dec <;>
        split_ands <;> omega
      simp [eq_hl2, eq_ll2, eq_hl3, eq_ll3] at *
      simp_all
      have a0_16 := limb_16_of_cancel b_cb0 b_cb1 b_cb2 b_cb3 lt_ll0 lt_hl0 lt_ll1 lt_hl1
      have a1_16 : (hl1 + (msb_b * 65536 - msb_b * ((1 - cb0 + 1) * 2 * ((1 - cb1) * 3 + 1) * ((1 - cb2) * 15 + 1) * ((1 - cb3) * 255 + 1)))).val < 65536 := by
        clear *- h_msb_b3 b1_16 b2_16 b_cb0 b_cb1 b_cb2 b_cb3 h_b1_dec lt_ll1 lt_hl1
        rw [U16MSBOperation.allHold_constraints_iff] at h_msb_b3
        obtain ⟨_, b_msb_b3, _⟩ := h_msb_b3
        rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;> rcases b_msb_b3 <;> simp_all
        all_goals { clear *- lt_hl1; omega }
      have msb_b: (msb_b * 65535).val < 65536 := by
        apply bool_mul_65535_lt
        rw [U16MSBOperation.allHold_constraints_iff] at h_msb_b1
        clear *- h_msb_b1; simp_all
      have msb_srw : (msb_srw * 65535).val < 65536 := by
        apply bool_mul_65535_lt
        rw [U16MSBOperation.allHold_constraints_iff] at h_msb_a1
        clear *- h_msb_a1; simp_all
      rcases b_su160 <;> simp_all
      rcases b_su161 <;> simp_all
      rcases b_su162 <;> simp_all

lemma ops_U64 : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main →
  Word.isU64 #v[Main[32], Main[33], Main[34], Main[35]] ∧
  Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] ∧
  Word.isU64 #v[Main[25], Main[26], Main[27], Main[28]]
    := by
  intro cstrs real
  constructor
  · exact ops_U64_a Main cstrs real
  · exact ops_U64_b_c Main cstrs real

end entailed_constraints

section operands

@[simp]
def sp1_op_a : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → BitVec 5 := by
  intro cstrs real
  refine BitVec.ofNatLT Main[6] ?_
  change Main[6] < 32
  have := register_bounds Main cstrs real
  tauto

@[simp]
def sp1_op_b : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → BitVec 5 := by
  intro cstrs real
  refine BitVec.ofNatLT Main[14] ?_
  change Main[14] < 32
  have := register_bounds Main cstrs real
  tauto

@[simp]
def sp1_op_c : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → Main[31] = 0 → BitVec 5 := by
  intro cstrs real imm
  refine BitVec.ofNatLT Main[21] ?_
  change Main[21] < 32
  have := register_bounds Main cstrs real
  tauto

@[simp]
def sp1_op_c_imm : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → Main[31] = 1 → Main[64] = 1 ∨ Main[65] = 1 → BitVec 6 := by
  intro cstrs real imm nw
  refine BitVec.ofNatLT Main[21] ?_
  have := immediate_bounds Main cstrs real
  simp_all
  omega

@[simp]
def sp1_op_c_imm_w : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → Main[31] = 1 → Main[66] = 1 ∨ Main[67] = 1 → BitVec 5 := by
  intro cstrs real imm nw
  refine BitVec.ofNatLT Main[21] ?_
  have := immediate_bounds Main cstrs real
  simp_all
  omega

end operands

-- ============================================================================
-- _poly skeleton (Phase 2). Field-arith helpers + boilerplate closures landed.
-- The `is_*_poly` opcode predicates already exist from the earlier groundwork
-- commit `3fc39ba`; see the `opcodes` section above.
-- ============================================================================

section poly_field_arithmetic

/-- Polymorphic version of `is_mod_64`. From `((c0 - m) * 64⁻¹).val < 1024`,
conclude `c0 ≡ m (mod 64)`. Cleaner than Fin KB because no wrap to undo. -/
lemma is_mod_64_poly {c0 m : ZMod p}
    (h_m_lt : m.val < 64) (_h_c0_lt : c0.val < 65536)
    (h_diff : ((c0 - m) * (64 : ZMod p)⁻¹).val < 1024) :
    c0.val % 64 = m.val := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  set k := (c0 - m) * (64 : ZMod p)⁻¹ with k_def
  have h_k_lt : k.val < 1024 := h_diff
  have h_64_ne : (64 : ZMod p) ≠ 0 := val_64_ne_zero
  have h_diff_eq : c0 - m = k * 64 := by rw [k_def]; field_simp
  have h_c0_eq : c0 = m + k * 64 := by linear_combination h_diff_eq
  have h_k64_val : (k * 64).val = k.val * 64 := by
    rw [show (64 : ZMod p) = ((64 : ℕ) : ZMod p) from by push_cast; rfl]
    rw [ZMod.val_mul_of_lt]
    · rw [show ((64 : ℕ) : ZMod p).val = 64 from val_64_zmod_p]
    · rw [show ((64 : ℕ) : ZMod p).val = 64 from val_64_zmod_p]
      have : k.val * 64 < 1024 * 64 := by
        exact Nat.mul_lt_mul_of_lt_of_le h_k_lt (le_refl 64) (by omega)
      omega
  have h_c0_val : c0.val = m.val + k.val * 64 := by
    have : c0.val = (m + k * 64).val := by rw [h_c0_eq]
    rw [this, ZMod.val_add_of_lt]
    · rw [h_k64_val]
    · rw [h_k64_val]; omega
  rw [h_c0_val]; omega

/-- Polymorphic version of `cancel_mul_65536_v1`. Cleaner than Fin KB because
ZMod p (p > 2^17) has no wrap to undo for products ≤ 65536^2 < 2^32 < p. -/
lemma cancel_mul_65536_poly {a b c x : ZMod p}
    (h_x_dvd : x.val ∣ 65536) (h_x_pos : 0 < x.val) :
    a * x = b * 65536 + c * x → a = b * (((65536 / x.val : ℕ) : ZMod p)) + c := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  intro h_eq
  set z : ℕ := 65536 / x.val with z_def
  have h_x_le : x.val ≤ 65536 := Nat.le_of_dvd (by omega) h_x_dvd
  have _h_z_pos : 0 < z := Nat.div_pos h_x_le h_x_pos
  have _h_z_lt : z ≤ 65536 := by rw [z_def]; exact Nat.div_le_self _ _
  have h_xz : x.val * z = 65536 := by rw [z_def, Nat.mul_div_cancel' h_x_dvd]
  have h_xz_zmod : x * ((z : ℕ) : ZMod p) = 65536 := by
    have : ((x.val : ZMod p)) * ((z : ℕ) : ZMod p) = ((x.val * z : ℕ) : ZMod p) := by
      push_cast; ring
    rw [ZMod.natCast_zmod_val] at this
    rw [this, h_xz]; push_cast; rfl
  have h_eq2 : a * x = (b * ((z : ℕ) : ZMod p) + c) * x := by
    rw [← h_xz_zmod] at h_eq; linear_combination h_eq
  have h_x_ne : x ≠ 0 := by
    intro h; have : x.val = 0 := by rw [h]; exact ZMod.val_zero
    omega
  exact mul_right_cancel₀ h_x_ne h_eq2

/-- Polymorphic version of `cancel_mul_65536_v2`: zero-RHS form. -/
lemma cancel_mul_65536_zero_poly {b c x : ZMod p}
    (h_x_dvd : x.val ∣ 65536) (h_x_pos : 0 < x.val) :
    b * 65536 + c * x = 0 → b * (((65536 / x.val : ℕ) : ZMod p)) + c = 0 := by
  intro h_eq
  have := cancel_mul_65536_poly h_x_dvd h_x_pos (a := 0) (b := b) (c := c)
  rw [zero_mul] at this; symm; exact this h_eq.symm

/-- For booleans b ∈ {0, 1}, the product b · 65535 has val < 65536. -/
lemma bool_mul_65535_lt_poly {b : ZMod p} (hb : b = 0 ∨ b = 1) :
    (b * 65535).val < 65536 := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  rcases hb with h | h
  · rw [h, zero_mul]; simp [ZMod.val_zero]
  · rw [h, one_mul]
    have : ((65535 : ℕ) : ZMod p).val = 65535 := ZMod.val_natCast_of_lt (by omega)
    have h_cast : (65535 : ZMod p) = ((65535 : ℕ) : ZMod p) := by push_cast; rfl
    rw [h_cast, this]; omega

end poly_field_arithmetic

section poly_helpers

private lemma val_le_one_of_bool {p : ℕ} [NeZero p] [Fact (1 < p)]
    {k : ZMod p} (hk : k = 0 ∨ k = 1) : k.val ≤ 1 := by
  rcases hk with h | h
  · simp [h, ZMod.val_zero]
  · rw [h]; have := ZMod.val_one p; omega

private lemma val_eq_one_of_eq_one {p : ℕ} [NeZero p] [Fact (1 < p)]
    {k : ZMod p} (h : k = 1) : k.val = 1 := by
  rw [h]; exact ZMod.val_one p

private lemma zero_of_bool_val_zero {p : ℕ} [NeZero p] [Fact (1 < p)]
    {k : ZMod p} (hk : k = 0 ∨ k = 1) (hv : k.val = 0) : k = 0 := by
  rcases hk with h | h
  · exact h
  · exfalso; rw [h] at hv; rw [ZMod.val_one] at hv; omega

/-- 4-way boolean mutex from sum = 1. -/
private lemma four_way_mutex_eq_one_poly {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    {a b c d : ZMod p}
    (ba : a = 0 ∨ a = 1) (bb : b = 0 ∨ b = 1)
    (bc : c = 0 ∨ c = 1) (bd : d = 0 ∨ d = 1)
    (hs : a + b + c + d = 1) :
    (a = 1 → b = 0 ∧ c = 0 ∧ d = 0) ∧
    (b = 1 → a = 0 ∧ c = 0 ∧ d = 0) ∧
    (c = 1 → a = 0 ∧ b = 0 ∧ d = 0) ∧
    (d = 1 → a = 0 ∧ b = 0 ∧ c = 0) := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  haveI : Fact (1 < p) := ⟨by omega⟩
  have va := val_le_one_of_bool ba
  have vb := val_le_one_of_bool bb
  have vc := val_le_one_of_bool bc
  have vd := val_le_one_of_bool bd
  have h_ab : (a + b).val = a.val + b.val := ZMod.val_add_of_lt (by omega)
  have h_abc : (a + b + c).val = a.val + b.val + c.val := by
    rw [ZMod.val_add_of_lt, h_ab]; rw [h_ab]; omega
  have h_sum_val : (a + b + c + d).val = a.val + b.val + c.val + d.val := by
    rw [ZMod.val_add_of_lt, h_abc]; rw [h_abc]; omega
  have h_one : (a + b + c + d).val = 1 := by rw [hs]; exact ZMod.val_one p
  rw [h_sum_val] at h_one
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; have hv := val_eq_one_of_eq_one h
    exact ⟨zero_of_bool_val_zero bb (by omega), zero_of_bool_val_zero bc (by omega),
           zero_of_bool_val_zero bd (by omega)⟩
  · intro h; have hv := val_eq_one_of_eq_one h
    exact ⟨zero_of_bool_val_zero ba (by omega), zero_of_bool_val_zero bc (by omega),
           zero_of_bool_val_zero bd (by omega)⟩
  · intro h; have hv := val_eq_one_of_eq_one h
    exact ⟨zero_of_bool_val_zero ba (by omega), zero_of_bool_val_zero bb (by omega),
           zero_of_bool_val_zero bd (by omega)⟩
  · intro h; have hv := val_eq_one_of_eq_one h
    exact ⟨zero_of_bool_val_zero ba (by omega), zero_of_bool_val_zero bb (by omega),
           zero_of_bool_val_zero bc (by omega)⟩

/-- 4-way booleans: sum = 0 forces each to 0. -/
private lemma four_way_all_zero_of_sum_zero_poly {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    {a b c d : ZMod p}
    (ba : a = 0 ∨ a = 1) (bb : b = 0 ∨ b = 1)
    (bc : c = 0 ∨ c = 1) (bd : d = 0 ∨ d = 1)
    (hs : a + b + c + d = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  haveI : Fact (1 < p) := ⟨by omega⟩
  have va := val_le_one_of_bool ba
  have vb := val_le_one_of_bool bb
  have vc := val_le_one_of_bool bc
  have vd := val_le_one_of_bool bd
  have h_ab : (a + b).val = a.val + b.val := ZMod.val_add_of_lt (by omega)
  have h_abc : (a + b + c).val = a.val + b.val + c.val := by
    rw [ZMod.val_add_of_lt, h_ab]; rw [h_ab]; omega
  have h_sum_val : (a + b + c + d).val = a.val + b.val + c.val + d.val := by
    rw [ZMod.val_add_of_lt, h_abc]; rw [h_abc]; omega
  have h_zero : (a + b + c + d).val = 0 := by rw [hs]; exact ZMod.val_zero
  rw [h_sum_val] at h_zero
  exact ⟨zero_of_bool_val_zero ba (by omega), zero_of_bool_val_zero bb (by omega),
         zero_of_bool_val_zero bc (by omega), zero_of_bool_val_zero bd (by omega)⟩

/-- Mutual-exclusion of the four opcode flags. -/
lemma single_op_poly (Main : Vector (ZMod p) 69)
    (cstrs : (constraints Main).allHold_poly) :
    (Main[64] = 1 → Main[65] = 0 ∧ Main[66] = 0 ∧ Main[67] = 0) ∧
    (Main[65] = 1 → Main[64] = 0 ∧ Main[66] = 0 ∧ Main[67] = 0) ∧
    (Main[66] = 1 → Main[64] = 0 ∧ Main[65] = 0 ∧ Main[67] = 0) ∧
    (Main[67] = 1 → Main[64] = 0 ∧ Main[65] = 0 ∧ Main[66] = 0) := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  haveI : Fact (1 < p) := ⟨by omega⟩
  change List.Forall SP1Constraint.toProp_poly (constraints Main) at cstrs
  rw [allHold_constraints_iff_poly] at cstrs
  obtain ⟨_, _, _, _, _, b_64, b_65, b_66, b_67, sum_disj, _⟩ := cstrs
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    rcases sum_disj with h_sum0 | h_sum1
  · -- Main[64]=1, sum=0: contradiction since sum=0 means each is 0, but Main[64]=1.
    have := four_way_all_zero_of_sum_zero_poly b_64 b_65 b_66 b_67 h_sum0
    exfalso; rw [h] at this; exact one_ne_zero this.1
  · exact (four_way_mutex_eq_one_poly b_64 b_65 b_66 b_67 h_sum1).1 h
  · have := four_way_all_zero_of_sum_zero_poly b_64 b_65 b_66 b_67 h_sum0
    exfalso; rw [h] at this; exact one_ne_zero this.2.1
  · exact (four_way_mutex_eq_one_poly b_64 b_65 b_66 b_67 h_sum1).2.1 h
  · have := four_way_all_zero_of_sum_zero_poly b_64 b_65 b_66 b_67 h_sum0
    exfalso; rw [h] at this; exact one_ne_zero this.2.2.1
  · exact (four_way_mutex_eq_one_poly b_64 b_65 b_66 b_67 h_sum1).2.2.1 h
  · have := four_way_all_zero_of_sum_zero_poly b_64 b_65 b_66 b_67 h_sum0
    exfalso; rw [h] at this; exact one_ne_zero this.2.2.2
  · exact (four_way_mutex_eq_one_poly b_64 b_65 b_66 b_67 h_sum1).2.2.2 h

lemma is_real_eq_one_of_srl (Main : Vector (ZMod p) 69)
    (cstrs : (constraints Main).allHold_poly) (h_srl : Main[64] = 1) :
    Main[64] + Main[65] + Main[66] + Main[67] = 1 := by
  obtain ⟨h, _, _, _⟩ := single_op_poly Main cstrs
  have ⟨h65, h66, h67⟩ := h h_srl
  rw [h_srl, h65, h66, h67]; ring

lemma is_real_eq_one_of_sra (Main : Vector (ZMod p) 69)
    (cstrs : (constraints Main).allHold_poly) (h_sra : Main[65] = 1) :
    Main[64] + Main[65] + Main[66] + Main[67] = 1 := by
  obtain ⟨_, h, _, _⟩ := single_op_poly Main cstrs
  have ⟨h64, h66, h67⟩ := h h_sra
  rw [h_sra, h64, h66, h67]; ring

lemma is_real_eq_one_of_srlw (Main : Vector (ZMod p) 69)
    (cstrs : (constraints Main).allHold_poly) (h_srlw : Main[66] = 1) :
    Main[64] + Main[65] + Main[66] + Main[67] = 1 := by
  obtain ⟨_, _, h, _⟩ := single_op_poly Main cstrs
  have ⟨h64, h65, h67⟩ := h h_srlw
  rw [h_srlw, h64, h65, h67]; ring

lemma is_real_eq_one_of_sraw (Main : Vector (ZMod p) 69)
    (cstrs : (constraints Main).allHold_poly) (h_sraw : Main[67] = 1) :
    Main[64] + Main[65] + Main[66] + Main[67] = 1 := by
  obtain ⟨_, _, _, h⟩ := single_op_poly Main cstrs
  have ⟨h64, h65, h66⟩ := h h_sraw
  rw [h_sraw, h64, h65, h66]; ring

/-- 4-way "which-one" lemma: given 4 booleans summing to 1, exactly one is 1.
Pure ZMod p reasoning; reused by both opcode and su16 dispatchers. -/
private lemma which_of_four_eq_one_poly {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    {a b c d : ZMod p}
    (ba : a = 0 ∨ a = 1) (bb : b = 0 ∨ b = 1)
    (bc : c = 0 ∨ c = 1) (bd : d = 0 ∨ d = 1)
    (hs : a + b + c + d = 1) :
    (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 0) ∨
    (a = 0 ∧ b = 1 ∧ c = 0 ∧ d = 0) ∨
    (a = 0 ∧ b = 0 ∧ c = 1 ∧ d = 0) ∨
    (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 1) := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  haveI : Fact (1 < p) := ⟨by omega⟩
  -- Convert each disjunction to a .val statement (.val ∈ {0,1}, exact via rcases).
  have to_val : ∀ {x : ZMod p}, x = 0 ∨ x = 1 → x.val = 0 ∨ x.val = 1 := fun hx =>
    hx.imp (fun h => by rw [h]; exact ZMod.val_zero)
           (fun h => by rw [h]; exact ZMod.val_one p)
  have of_val : ∀ {x : ZMod p}, x = 0 ∨ x = 1 → x.val = 0 → x = 0 := fun hx hv =>
    hx.elim id (fun h => by rw [h] at hv; rw [ZMod.val_one] at hv; omega)
  have of_val' : ∀ {x : ZMod p}, x = 0 ∨ x = 1 → x.val = 1 → x = 1 := fun hx hv =>
    hx.elim (fun h => by rw [h] at hv; rw [ZMod.val_zero] at hv; omega) id
  have va := to_val ba
  have vb := to_val bb
  have vc := to_val bc
  have vd := to_val bd
  have ha_le : a.val ≤ 1 := by rcases va with h | h <;> omega
  have hb_le : b.val ≤ 1 := by rcases vb with h | h <;> omega
  have hc_le : c.val ≤ 1 := by rcases vc with h | h <;> omega
  have hd_le : d.val ≤ 1 := by rcases vd with h | h <;> omega
  have h_ab : (a + b).val = a.val + b.val :=
    ZMod.val_add_of_lt (by omega)
  have h_abc : (a + b + c).val = a.val + b.val + c.val := by
    rw [ZMod.val_add_of_lt, h_ab]; rw [h_ab]; omega
  have h_sumval : (a + b + c + d).val = a.val + b.val + c.val + d.val := by
    rw [ZMod.val_add_of_lt, h_abc]; rw [h_abc]; omega
  have h_one_val : a.val + b.val + c.val + d.val = 1 := by
    have : (a + b + c + d).val = 1 := by rw [hs]; exact ZMod.val_one p
    omega
  -- Per .val: omega tells us exactly one of va/vb/vc/vd is the .val=1 case.
  rcases va with ha | ha <;> rcases vb with hb | hb <;>
    rcases vc with hc | hc <;> rcases vd with hd | hd <;>
    first
    | (exfalso; omega)
    | (left;             exact ⟨of_val' ba ha, of_val bb hb, of_val bc hc, of_val bd hd⟩)
    | (right; left;      exact ⟨of_val ba ha, of_val' bb hb, of_val bc hc, of_val bd hd⟩)
    | (right; right; left;   exact ⟨of_val ba ha, of_val bb hb, of_val' bc hc, of_val bd hd⟩)
    | (right; right; right;  exact ⟨of_val ba ha, of_val bb hb, of_val bc hc, of_val' bd hd⟩)

/-- 4-way opcode disjunction from the sum = 1 constraint. -/
lemma srl_or_sra_or_srlw_or_sraw_of_real (Main : Vector (ZMod p) 69)
    (cstrs : (constraints Main).allHold_poly)
    (h_real : Main[64] + Main[65] + Main[66] + Main[67] = 1) :
    (Main[64] = 1 ∧ Main[65] = 0 ∧ Main[66] = 0 ∧ Main[67] = 0) ∨
    (Main[64] = 0 ∧ Main[65] = 1 ∧ Main[66] = 0 ∧ Main[67] = 0) ∨
    (Main[64] = 0 ∧ Main[65] = 0 ∧ Main[66] = 1 ∧ Main[67] = 0) ∨
    (Main[64] = 0 ∧ Main[65] = 0 ∧ Main[66] = 0 ∧ Main[67] = 1) := by
  change List.Forall SP1Constraint.toProp_poly (constraints Main) at cstrs
  rw [allHold_constraints_iff_poly] at cstrs
  obtain ⟨_, _, _, _, _, b_64, b_65, b_66, b_67, _⟩ := cstrs
  exact which_of_four_eq_one_poly b_64 b_65 b_66 b_67 h_real

/-- Mutual-exclusion of the four su16-flag columns (cstrs only — needs h_real). -/
lemma single_su16_poly (Main : Vector (ZMod p) 69)
    (cstrs : (constraints Main).allHold_poly)
    (h_real : Main[64] + Main[65] + Main[66] + Main[67] = 1) :
    (Main[60] = 1 → Main[61] = 0 ∧ Main[62] = 0 ∧ Main[63] = 0) ∧
    (Main[61] = 1 → Main[60] = 0 ∧ Main[62] = 0 ∧ Main[63] = 0) ∧
    (Main[62] = 1 → Main[60] = 0 ∧ Main[61] = 0 ∧ Main[63] = 0) ∧
    (Main[63] = 1 → Main[60] = 0 ∧ Main[61] = 0 ∧ Main[62] = 0) := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  haveI : Fact (1 < p) := ⟨by omega⟩
  change List.Forall SP1Constraint.toProp_poly (constraints Main) at cstrs
  rw [allHold_constraints_iff_poly] at cstrs
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _,
           _, _, _, _, _, _, _,
           _, b_su160, _, b_su161, _, b_su162, _, b_su163, one_of_su16s, _⟩ := cstrs
  -- one_of_su16s: opcode_sum = 0 ∨ su16_sum = 1. h_real gives opcode_sum = 1 ≠ 0.
  have h_su16_sum : Main[60] + Main[61] + Main[62] + Main[63] = 1 := by
    rcases one_of_su16s with hopcsum | hsu16sum
    · exfalso
      have : (1 : ZMod p) = 0 := by rw [← h_real]; exact hopcsum
      exact one_ne_zero this
    · exact hsu16sum
  exact four_way_mutex_eq_one_poly b_su160 b_su161 b_su162 b_su163 h_su16_sum

end poly_helpers

section poly_bounds

set_option maxHeartbeats 16000000 in
-- ALU iff for op_b U64; 4-way SRL/SRA/SRLW/SRAW case-split for op_c bound under imm=1.
lemma ops_U64_b_c_poly (Main : Vector (ZMod p) 69)
    (cstrs : (constraints Main).allHold_poly)
    (h_real : Main[64] + Main[65] + Main[66] + Main[67] = 1) :
    Word.isU64_poly #v[Main[15], Main[16], Main[17], Main[18]] ∧
    Word.isU64_poly #v[Main[25], Main[26], Main[27], Main[28]] := by
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  have hp : 2 ^ 17 < p := Fact.out
  have h_disj := srl_or_sra_or_srlw_or_sraw_of_real Main cstrs h_real
  change List.Forall SP1Constraint.toProp_poly (constraints Main) at cstrs
  rw [allHold_constraints_iff_poly] at cstrs
  obtain ⟨_, _, _, _, alu, _⟩ := cstrs
  rw [ALUTypeReader.allHold_constraints_iff_is_real_poly h_real rfl] at alu
  dsimp only at alu
  obtain ⟨h_trusted, _, _, _, _, _, b_imm, _, _, _, _, _, _, _, _,
          _, h_is_U64_b, h_imm0, _, h_imm1_op_c⟩ := alu
  refine ⟨h_is_U64_b, ?_⟩
  rcases b_imm with h_imm0_eq | h_imm1_eq
  · exact (h_imm0 h_imm0_eq).2.2
  · -- imm = 1: op_c_memory.prev_value = op_c; trusted_instr gives c0 < 2^k, c1..c3 = 0
    have h_imm1_ne_0 : ¬ Main[31] = 0 := fun h0 => one_ne_zero (h_imm1_eq ▸ h0.symm).symm
    have ⟨e_25, e_26, e_27, e_28⟩ := h_imm1_op_c h_imm1_ne_0
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ] at e_25 e_26 e_27 e_28
    rw [e_25, e_26, e_27, e_28]
    -- Helper: discharge the 5-bit/6-bit shamt case for any concrete opcode N ∈ {7, 8, 22, 23}.
    have h64_pow : (2 ^ 6 : ZMod p).val = 64 := by
      rw [show (2 ^ 6 : ZMod p) = ((64 : ℕ) : ZMod p) from by push_cast; ring]
      exact ZMod.val_natCast_of_lt (by omega)
    have h32_pow : (2 ^ 5 : ZMod p).val = 32 := by
      rw [show (2 ^ 5 : ZMod p) = ((32 : ℕ) : ZMod p) from by push_cast; ring]
      exact ZMod.val_natCast_of_lt (by omega)
    rcases h_disj with ⟨h_srl, h_no_sra, h_no_srlw, h_no_sraw⟩ |
                       ⟨h_no_srl, h_sra, h_no_srlw, h_no_sraw⟩ |
                       ⟨h_no_srl, h_no_sra, h_srlw, h_no_sraw⟩ |
                       ⟨h_no_srl, h_no_sra, h_no_srlw, h_sraw⟩
    · -- SRL: opcode = 7
      have h_expr : (Main[64] * 7 + Main[65] * 8 + Main[66] * 22 + Main[67] * 23 : ZMod p)
                  = ((7 : ℕ) : ZMod p) := by
        rw [h_srl, h_no_sra, h_no_srlw, h_no_sraw]; push_cast; ring
      have h_opc : ((Main[64] * 7 + Main[65] * 8 + Main[66] * 22 + Main[67] * 23 : ZMod p)).val = 7 := by
        rw [h_expr]; exact ZMod.val_natCast_of_lt (show (7 : ℕ) < p by omega)
      simp only [h_opc, show Opcode.ofNat 7 = .SRL from rfl,
        Opcode.trusted_instr_poly] at h_trusted
      have h_si : shift_i_type_constraints_poly Main[6] Main[14] 0 0 0 Main[21] Main[22] Main[23] Main[24] 0 Main[31] :=
        h_trusted.2 h_imm1_eq
      simp only [shift_i_type_constraints_poly] at h_si
      obtain ⟨_, _, h_c0_lt, h_c1, h_c2, h_c3⟩ := h_si
      apply Word.isU64_of_cases_poly
      · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero]
        have : Main[21].val < (2 ^ 6 : ZMod p).val := h_c0_lt
        rw [h64_pow] at this; omega
      · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
          List.getElem_cons_zero, h_c1, ZMod.val_zero]; omega
      · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
          List.getElem_cons_zero, h_c2, ZMod.val_zero]; omega
      · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
          List.getElem_cons_zero, h_c3, ZMod.val_zero]; omega
    · -- SRA: opcode = 8
      have h_expr : (Main[64] * 7 + Main[65] * 8 + Main[66] * 22 + Main[67] * 23 : ZMod p)
                  = ((8 : ℕ) : ZMod p) := by
        rw [h_no_srl, h_sra, h_no_srlw, h_no_sraw]; push_cast; ring
      have h_opc : ((Main[64] * 7 + Main[65] * 8 + Main[66] * 22 + Main[67] * 23 : ZMod p)).val = 8 := by
        rw [h_expr]; exact ZMod.val_natCast_of_lt (show (8 : ℕ) < p by omega)
      simp only [h_opc, show Opcode.ofNat 8 = .SRA from rfl,
        Opcode.trusted_instr_poly] at h_trusted
      have h_si : shift_i_type_constraints_poly Main[6] Main[14] 0 0 0 Main[21] Main[22] Main[23] Main[24] 0 Main[31] :=
        h_trusted.2 h_imm1_eq
      simp only [shift_i_type_constraints_poly] at h_si
      obtain ⟨_, _, h_c0_lt, h_c1, h_c2, h_c3⟩ := h_si
      apply Word.isU64_of_cases_poly
      · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero]
        have : Main[21].val < (2 ^ 6 : ZMod p).val := h_c0_lt
        rw [h64_pow] at this; omega
      · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
          List.getElem_cons_zero, h_c1, ZMod.val_zero]; omega
      · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
          List.getElem_cons_zero, h_c2, ZMod.val_zero]; omega
      · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
          List.getElem_cons_zero, h_c3, ZMod.val_zero]; omega
    · -- SRLW: opcode = 22
      have h_expr : (Main[64] * 7 + Main[65] * 8 + Main[66] * 22 + Main[67] * 23 : ZMod p)
                  = ((22 : ℕ) : ZMod p) := by
        rw [h_no_srl, h_no_sra, h_srlw, h_no_sraw]; push_cast; ring
      have h_opc : ((Main[64] * 7 + Main[65] * 8 + Main[66] * 22 + Main[67] * 23 : ZMod p)).val = 22 := by
        rw [h_expr]; exact ZMod.val_natCast_of_lt (show (22 : ℕ) < p by omega)
      simp only [h_opc, show Opcode.ofNat 22 = .SRLW from rfl,
        Opcode.trusted_instr_poly] at h_trusted
      have h_wsi : w_shift_i_type_constraints_poly Main[6] Main[14] 0 0 0 Main[21] Main[22] Main[23] Main[24] 0 Main[31] :=
        h_trusted.2 h_imm1_eq
      simp only [w_shift_i_type_constraints_poly] at h_wsi
      obtain ⟨_, _, h_c0_lt, h_c1, h_c2, h_c3⟩ := h_wsi
      apply Word.isU64_of_cases_poly
      · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero]
        have : Main[21].val < (2 ^ 5 : ZMod p).val := h_c0_lt
        rw [h32_pow] at this; omega
      · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
          List.getElem_cons_zero, h_c1, ZMod.val_zero]; omega
      · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
          List.getElem_cons_zero, h_c2, ZMod.val_zero]; omega
      · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
          List.getElem_cons_zero, h_c3, ZMod.val_zero]; omega
    · -- SRAW: opcode = 23
      have h_expr : (Main[64] * 7 + Main[65] * 8 + Main[66] * 22 + Main[67] * 23 : ZMod p)
                  = ((23 : ℕ) : ZMod p) := by
        rw [h_no_srl, h_no_sra, h_no_srlw, h_sraw]; push_cast; ring
      have h_opc : ((Main[64] * 7 + Main[65] * 8 + Main[66] * 22 + Main[67] * 23 : ZMod p)).val = 23 := by
        rw [h_expr]; exact ZMod.val_natCast_of_lt (show (23 : ℕ) < p by omega)
      simp only [h_opc, show Opcode.ofNat 23 = .SRAW from rfl,
        Opcode.trusted_instr_poly] at h_trusted
      have h_wsi : w_shift_i_type_constraints_poly Main[6] Main[14] 0 0 0 Main[21] Main[22] Main[23] Main[24] 0 Main[31] :=
        h_trusted.2 h_imm1_eq
      simp only [w_shift_i_type_constraints_poly] at h_wsi
      obtain ⟨_, _, h_c0_lt, h_c1, h_c2, h_c3⟩ := h_wsi
      apply Word.isU64_of_cases_poly
      · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero]
        have : Main[21].val < (2 ^ 5 : ZMod p).val := h_c0_lt
        rw [h32_pow] at this; omega
      · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
          List.getElem_cons_zero, h_c1, ZMod.val_zero]; omega
      · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
          List.getElem_cons_zero, h_c2, ZMod.val_zero]; omega
      · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
          List.getElem_cons_zero, h_c3, ZMod.val_zero]; omega

lemma ops_U64_a_poly (Main : Vector (ZMod p) 69)
    (cstrs : (constraints Main).allHold_poly)
    (h_real : Main[64] + Main[65] + Main[66] + Main[67] = 1) :
    Word.isU64_poly #v[Main[32], Main[33], Main[34], Main[35]] := by
  sorry

lemma ops_U64_poly (Main : Vector (ZMod p) 69)
    (cstrs : (constraints Main).allHold_poly)
    (h_real : Main[64] + Main[65] + Main[66] + Main[67] = 1) :
    Word.isU64_poly #v[Main[32], Main[33], Main[34], Main[35]] ∧
    Word.isU64_poly #v[Main[15], Main[16], Main[17], Main[18]] ∧
    Word.isU64_poly #v[Main[25], Main[26], Main[27], Main[28]] :=
  ⟨ops_U64_a_poly Main cstrs h_real, ops_U64_b_c_poly Main cstrs h_real⟩

set_option maxHeartbeats 16000000 in
-- 16M heartbeats: 4-way opcode case-split × 6 conjuncts per arm × ALU iff unfold
-- with simp on Opcode.ofNat reflection. ShiftLeft's 2-way analog uses 16M.
/-- Combined register/immediate-bound bundle threaded through every spec proof.
Mirrors `ShiftLeft.bounds_poly` with a 4-way SRL/SRA/SRLW/SRAW case-split. -/
lemma bounds_poly (Main : Vector (ZMod p) 69)
    (cstrs : (constraints Main).allHold_poly)
    (h_real : Main[64] + Main[65] + Main[66] + Main[67] = 1) :
    Main[6].val < 32 ∧ Main[14].val < 32 ∧
    (Main[31] = 0 → Main[21].val < 32) ∧
    Main[3].val < 65536 ∧
    Word.isU64_poly #v[Main[15], Main[16], Main[17], Main[18]] ∧
    Word.isU64_poly #v[Main[25], Main[26], Main[27], Main[28]] ∧
    (Main[31] = 1 →
      (Main[21] = Main[25] ∧ Main[26] = 0 ∧ Main[27] = 0 ∧ Main[28] = 0 ∧
        ((Main[64] = 1 ∨ Main[65] = 1 → Main[25].val < 64) ∧
         (Main[66] = 1 ∨ Main[67] = 1 → Main[25].val < 32)))) ∧
    (Main[6] = 0 → Main[32] = 0 ∧ Main[33] = 0 ∧ Main[34] = 0 ∧ Main[35] = 0) := by
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  have hp : 2 ^ 17 < p := Fact.out
  have h32 : (32 : ZMod p).val = 32 := val_32_zmod_p
  have h65536 : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
  have ⟨is_U64_b, is_U64_c⟩ := ops_U64_b_c_poly Main cstrs h_real
  have h_disj := srl_or_sra_or_srlw_or_sraw_of_real Main cstrs h_real
  change List.Forall SP1Constraint.toProp_poly (constraints Main) at cstrs
  rw [allHold_constraints_iff_poly] at cstrs
  -- Helper: discharge the "x=1 ∨ y=1" contradiction when both are known 0.
  have h_contradict_or : ∀ {x y : ZMod p}, x = 0 → y = 0 → (x = 1 ∨ y = 1) → False :=
    fun hx hy hor => by
      rcases hor with h | h
      · rw [hx] at h; exact zero_ne_one h
      · rw [hy] at h; exact zero_ne_one h
  obtain ⟨_, _, _, _, alu, _, _, _, _, _, _, _, _, _, _, _, _, rest⟩ := cstrs
  -- `rest` has 55 conjuncts (positions 18-72 of the iff RHS). The last is Main[13] = 0.
  -- Destructure with 54 underscores + the named final conjunct.
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          h_M13⟩ := rest
  rw [ALUTypeReader.allHold_constraints_iff_is_real_poly h_real rfl] at alu
  dsimp only at alu
  obtain ⟨h_trusted, h_op_a_lt, _h_op_b_lt, _h_op_c_lts, _, h_op_a_0_iff, b_imm, _,
          h_pc0_lt, _, _, _, _, _, _, _, _, h_imm0, _h_op_a_0_zeros, h_imm1_op_c⟩ := alu
  have h_a_lt : Main[6].val < 32 := by
    have : Main[6].val < (32 : ZMod p).val := h_op_a_lt
    rwa [h32] at this
  have h_pc_lt : Main[3].val < 65536 := by
    have : Main[3].val < (65536 : ZMod p).val := h_pc0_lt
    rwa [h65536] at this
  have h64_pow : (2 ^ 6 : ZMod p).val = 64 := by
    rw [show (2 ^ 6 : ZMod p) = ((64 : ℕ) : ZMod p) from by push_cast; ring]
    exact ZMod.val_natCast_of_lt (by omega)
  have h32_pow : (2 ^ 5 : ZMod p).val = 32 := by
    rw [show (2 ^ 5 : ZMod p) = ((32 : ℕ) : ZMod p) from by push_cast; ring]
    exact ZMod.val_natCast_of_lt (by omega)
  -- The op_a=0 conjunct is vacuously true since Main[13]=0 ⇔ Main[6]≠0.
  have h_a_zero_imp_zeros : Main[6] = 0 → Main[32] = 0 ∧ Main[33] = 0 ∧ Main[34] = 0 ∧ Main[35] = 0 := by
    intro h_a0_eq
    exfalso
    have h13_eq_one : Main[13] = 1 := h_op_a_0_iff.mpr h_a0_eq
    rw [h_M13] at h13_eq_one
    exact zero_ne_one h13_eq_one
  rcases h_disj with ⟨h_srl, h_no_sra, h_no_srlw, h_no_sraw⟩ |
                     ⟨h_no_srl, h_sra, h_no_srlw, h_no_sraw⟩ |
                     ⟨h_no_srl, h_no_sra, h_srlw, h_no_sraw⟩ |
                     ⟨h_no_srl, h_no_sra, h_no_srlw, h_sraw⟩
  · -- SRL case: opcode = 7, shift_i_type (6-bit shamt)
    have h_expr : (Main[64] * 7 + Main[65] * 8 + Main[66] * 22 + Main[67] * 23 : ZMod p)
                = ((7 : ℕ) : ZMod p) := by
      rw [h_srl, h_no_sra, h_no_srlw, h_no_sraw]; push_cast; ring
    have h_opc : ((Main[64] * 7 + Main[65] * 8 + Main[66] * 22 + Main[67] * 23 : ZMod p)).val = 7 := by
      rw [h_expr]; exact ZMod.val_natCast_of_lt (by omega)
    simp only [h_opc, show Opcode.ofNat 7 = .SRL from rfl, Opcode.trusted_instr_poly] at h_trusted
    refine ⟨h_a_lt, ?_, ?_, h_pc_lt, is_U64_b, is_U64_c, ?_, h_a_zero_imp_zeros⟩
    · rcases b_imm with h_imm | h_imm
      · have ⟨_, ⟨h_lt, _⟩, _⟩ := h_trusted.1 h_imm
        have : Main[14].val < (32 : ZMod p).val := h_lt; rwa [h32] at this
      · have ⟨_, ⟨h_lt, _⟩, _⟩ := h_trusted.2 h_imm
        have : Main[14].val < (32 : ZMod p).val := h_lt; rwa [h32] at this
    · intro h_imm0_eq
      have ⟨_, _, h_lt, _⟩ := h_trusted.1 h_imm0_eq
      have : Main[21].val < (32 : ZMod p).val := h_lt; rwa [h32] at this
    · intro h_imm1_eq
      have h_imm1_ne_0 : ¬ Main[31] = 0 := fun h0 => one_ne_zero (h_imm1_eq ▸ h0.symm).symm
      have ⟨e_25, e_26, e_27, e_28⟩ := h_imm1_op_c h_imm1_ne_0
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ] at e_25 e_26 e_27 e_28
      have ⟨_, _, h_c0_lt, h_c1, h_c2, h_c3⟩ := h_trusted.2 h_imm1_eq
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ] at h_c1 h_c2 h_c3
      refine ⟨e_25.symm, e_26.trans h_c1, e_27.trans h_c2, e_28.trans h_c3, ?_, ?_⟩
      · intro _
        rw [e_25]
        have : Main[21].val < (2 ^ 6 : ZMod p).val := h_c0_lt
        rw [h64_pow] at this; omega
      · intro h; exact (h_contradict_or h_no_srlw h_no_sraw h).elim
  · -- SRA case: opcode = 8, shift_i_type (6-bit shamt)
    have h_expr : (Main[64] * 7 + Main[65] * 8 + Main[66] * 22 + Main[67] * 23 : ZMod p)
                = ((8 : ℕ) : ZMod p) := by
      rw [h_no_srl, h_sra, h_no_srlw, h_no_sraw]; push_cast; ring
    have h_opc : ((Main[64] * 7 + Main[65] * 8 + Main[66] * 22 + Main[67] * 23 : ZMod p)).val = 8 := by
      rw [h_expr]; exact ZMod.val_natCast_of_lt (by omega)
    simp only [h_opc, show Opcode.ofNat 8 = .SRA from rfl, Opcode.trusted_instr_poly] at h_trusted
    refine ⟨h_a_lt, ?_, ?_, h_pc_lt, is_U64_b, is_U64_c, ?_, h_a_zero_imp_zeros⟩
    · rcases b_imm with h_imm | h_imm
      · have ⟨_, ⟨h_lt, _⟩, _⟩ := h_trusted.1 h_imm
        have : Main[14].val < (32 : ZMod p).val := h_lt; rwa [h32] at this
      · have ⟨_, ⟨h_lt, _⟩, _⟩ := h_trusted.2 h_imm
        have : Main[14].val < (32 : ZMod p).val := h_lt; rwa [h32] at this
    · intro h_imm0_eq
      have ⟨_, _, h_lt, _⟩ := h_trusted.1 h_imm0_eq
      have : Main[21].val < (32 : ZMod p).val := h_lt; rwa [h32] at this
    · intro h_imm1_eq
      have h_imm1_ne_0 : ¬ Main[31] = 0 := fun h0 => one_ne_zero (h_imm1_eq ▸ h0.symm).symm
      have ⟨e_25, e_26, e_27, e_28⟩ := h_imm1_op_c h_imm1_ne_0
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ] at e_25 e_26 e_27 e_28
      have ⟨_, _, h_c0_lt, h_c1, h_c2, h_c3⟩ := h_trusted.2 h_imm1_eq
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ] at h_c1 h_c2 h_c3
      refine ⟨e_25.symm, e_26.trans h_c1, e_27.trans h_c2, e_28.trans h_c3, ?_, ?_⟩
      · intro _
        rw [e_25]
        have : Main[21].val < (2 ^ 6 : ZMod p).val := h_c0_lt
        rw [h64_pow] at this; omega
      · intro h; exact (h_contradict_or h_no_srlw h_no_sraw h).elim
  · -- SRLW case: opcode = 22, w_shift_i_type (5-bit shamt)
    have h_expr : (Main[64] * 7 + Main[65] * 8 + Main[66] * 22 + Main[67] * 23 : ZMod p)
                = ((22 : ℕ) : ZMod p) := by
      rw [h_no_srl, h_no_sra, h_srlw, h_no_sraw]; push_cast; ring
    have h_opc : ((Main[64] * 7 + Main[65] * 8 + Main[66] * 22 + Main[67] * 23 : ZMod p)).val = 22 := by
      rw [h_expr]; exact ZMod.val_natCast_of_lt (by omega)
    simp only [h_opc, show Opcode.ofNat 22 = .SRLW from rfl, Opcode.trusted_instr_poly] at h_trusted
    refine ⟨h_a_lt, ?_, ?_, h_pc_lt, is_U64_b, is_U64_c, ?_, h_a_zero_imp_zeros⟩
    · rcases b_imm with h_imm | h_imm
      · have ⟨_, ⟨h_lt, _⟩, _⟩ := h_trusted.1 h_imm
        have : Main[14].val < (32 : ZMod p).val := h_lt; rwa [h32] at this
      · have ⟨_, ⟨h_lt, _⟩, _⟩ := h_trusted.2 h_imm
        have : Main[14].val < (32 : ZMod p).val := h_lt; rwa [h32] at this
    · intro h_imm0_eq
      have ⟨_, _, h_lt, _⟩ := h_trusted.1 h_imm0_eq
      have : Main[21].val < (32 : ZMod p).val := h_lt; rwa [h32] at this
    · intro h_imm1_eq
      have h_imm1_ne_0 : ¬ Main[31] = 0 := fun h0 => one_ne_zero (h_imm1_eq ▸ h0.symm).symm
      have ⟨e_25, e_26, e_27, e_28⟩ := h_imm1_op_c h_imm1_ne_0
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ] at e_25 e_26 e_27 e_28
      have ⟨_, _, h_c0_lt, h_c1, h_c2, h_c3⟩ := h_trusted.2 h_imm1_eq
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ] at h_c1 h_c2 h_c3
      refine ⟨e_25.symm, e_26.trans h_c1, e_27.trans h_c2, e_28.trans h_c3, ?_, ?_⟩
      · intro h; exact (h_contradict_or h_no_srl h_no_sra h).elim
      · intro _
        rw [e_25]
        have : Main[21].val < (2 ^ 5 : ZMod p).val := h_c0_lt
        rw [h32_pow] at this; omega
  · -- SRAW case: opcode = 23, w_shift_i_type (5-bit shamt)
    have h_expr : (Main[64] * 7 + Main[65] * 8 + Main[66] * 22 + Main[67] * 23 : ZMod p)
                = ((23 : ℕ) : ZMod p) := by
      rw [h_no_srl, h_no_sra, h_no_srlw, h_sraw]; push_cast; ring
    have h_opc : ((Main[64] * 7 + Main[65] * 8 + Main[66] * 22 + Main[67] * 23 : ZMod p)).val = 23 := by
      rw [h_expr]; exact ZMod.val_natCast_of_lt (by omega)
    simp only [h_opc, show Opcode.ofNat 23 = .SRAW from rfl, Opcode.trusted_instr_poly] at h_trusted
    refine ⟨h_a_lt, ?_, ?_, h_pc_lt, is_U64_b, is_U64_c, ?_, h_a_zero_imp_zeros⟩
    · rcases b_imm with h_imm | h_imm
      · have ⟨_, ⟨h_lt, _⟩, _⟩ := h_trusted.1 h_imm
        have : Main[14].val < (32 : ZMod p).val := h_lt; rwa [h32] at this
      · have ⟨_, ⟨h_lt, _⟩, _⟩ := h_trusted.2 h_imm
        have : Main[14].val < (32 : ZMod p).val := h_lt; rwa [h32] at this
    · intro h_imm0_eq
      have ⟨_, _, h_lt, _⟩ := h_trusted.1 h_imm0_eq
      have : Main[21].val < (32 : ZMod p).val := h_lt; rwa [h32] at this
    · intro h_imm1_eq
      have h_imm1_ne_0 : ¬ Main[31] = 0 := fun h0 => one_ne_zero (h_imm1_eq ▸ h0.symm).symm
      have ⟨e_25, e_26, e_27, e_28⟩ := h_imm1_op_c h_imm1_ne_0
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ] at e_25 e_26 e_27 e_28
      have ⟨_, _, h_c0_lt, h_c1, h_c2, h_c3⟩ := h_trusted.2 h_imm1_eq
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ] at h_c1 h_c2 h_c3
      refine ⟨e_25.symm, e_26.trans h_c1, e_27.trans h_c2, e_28.trans h_c3, ?_, ?_⟩
      · intro h; exact (h_contradict_or h_no_srl h_no_sra h).elim
      · intro _
        rw [e_25]
        have : Main[21].val < (2 ^ 5 : ZMod p).val := h_c0_lt
        rw [h32_pow] at this; omega

end poly_bounds

section poly_operands

@[simp] def sp1_op_a_poly (Main : Vector (ZMod p) 69) : BitVec 5 :=
  BitVec.ofNat 5 Main[6].val
@[simp] def sp1_op_b_poly (Main : Vector (ZMod p) 69) : BitVec 5 :=
  BitVec.ofNat 5 Main[14].val
@[simp] def sp1_op_c_poly (Main : Vector (ZMod p) 69) : BitVec 5 :=
  BitVec.ofNat 5 Main[21].val
@[simp] def sp1_op_c_imm_poly (Main : Vector (ZMod p) 69) : BitVec 6 :=
  BitVec.ofNat 6 Main[21].val
@[simp] def sp1_op_c_imm_w_poly (Main : Vector (ZMod p) 69) : BitVec 5 :=
  BitVec.ofNat 5 Main[21].val

end poly_operands

end ShiftRight
