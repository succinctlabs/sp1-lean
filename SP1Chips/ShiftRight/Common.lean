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

end ShiftRight
