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

/-- Computes `(cb0 + cb1*2 + cb2*4 + cb3*8 + cb4*16 + cb5*32).val` in ZMod p
when each cb_i ∈ {0, 1}, asserting no wrap (sum ≤ 63 < p since p > 2^17). The
RHS is the natural sum-of-vals form. Reused by every spec.*_poly to bridge
`is_mod_64_poly`'s ZMod premise to a Nat equation. -/
lemma cb_sum_val_eq_poly {cb0 cb1 cb2 cb3 cb4 cb5 : ZMod p}
    (b_cb0 : cb0 = 0 ∨ cb0 = 1) (b_cb1 : cb1 = 0 ∨ cb1 = 1)
    (b_cb2 : cb2 = 0 ∨ cb2 = 1) (b_cb3 : cb3 = 0 ∨ cb3 = 1)
    (b_cb4 : cb4 = 0 ∨ cb4 = 1) (b_cb5 : cb5 = 0 ∨ cb5 = 1) :
    (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32 : ZMod p).val =
      cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 + cb4.val * 16 + cb5.val * 32 := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  haveI : Fact (1 < p) := ⟨by omega⟩
  have hb0 : cb0.val ≤ 1 := by rcases b_cb0 with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]
  have hb1 : cb1.val ≤ 1 := by rcases b_cb1 with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]
  have hb2 : cb2.val ≤ 1 := by rcases b_cb2 with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]
  have hb3 : cb3.val ≤ 1 := by rcases b_cb3 with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]
  have hb4 : cb4.val ≤ 1 := by rcases b_cb4 with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]
  have hb5 : cb5.val ≤ 1 := by rcases b_cb5 with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]
  have v_2 : (2 : ZMod p).val = 2 := val_2_zmod_p
  have v_4 : (4 : ZMod p).val = 4 := val_4_zmod_p
  have v_8 : (8 : ZMod p).val = 8 := val_8_zmod_p
  have v_16 : (16 : ZMod p).val = 16 := val_16_zmod_p
  have v_32 : (32 : ZMod p).val = 32 := val_32_zmod_p
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
  have m5 : (cb5 * 32 : ZMod p).val = cb5.val * 32 := by
    rw [ZMod.val_mul_of_lt]
    · rw [v_32]
    · rw [v_32]; omega
  have a1 : (cb0 + cb1 * 2 : ZMod p).val = cb0.val + cb1.val * 2 := by
    rw [ZMod.val_add_of_lt]
    · rw [m1]
    · rw [m1]; omega
  have a2 : (cb0 + cb1 * 2 + cb2 * 4 : ZMod p).val =
      cb0.val + cb1.val * 2 + cb2.val * 4 := by
    rw [ZMod.val_add_of_lt]
    · rw [a1, m2]
    · rw [a1, m2]; omega
  have a3 : (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 : ZMod p).val =
      cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 := by
    rw [ZMod.val_add_of_lt]
    · rw [a2, m3]
    · rw [a2, m3]; omega
  have a4 : (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 : ZMod p).val =
      cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 + cb4.val * 16 := by
    rw [ZMod.val_add_of_lt]
    · rw [a3, m4]
    · rw [a3, m4]; omega
  rw [ZMod.val_add_of_lt]
  · rw [a4, m5]
  · rw [a4, m5]; omega

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

/-- Bridge `(Word.toBitVec64_poly b).msb` to a Nat predicate on the high limb.
For a U64-bounded word, the 64-bit BitVec's msb (bit 63) sits in the high limb
`b[3]` (which occupies bit positions 48..63 of the combined Nat). Used by SRA/SRAW
proofs to bridge `BitVec.sshiftRight` semantics (case-splits on msb) to the
`U16MSBOperation` constraint on `b[3]` (case-splits on `b[3].val ≥ 32768 = 2^15`). -/
lemma toBitVec64_poly_msb_eq_b3_ge {p : ℕ} [NeZero p]
    {b : Word (ZMod p)} (h_isU64 : Word.isU64_poly b) :
    (Word.toBitVec64_poly b).msb = decide (b[3].val ≥ 32768) := by
  have ⟨b0_16, b1_16, b2_16, b3_16⟩ := Word.lt_cases_of_isU64_poly h_isU64
  rw [BitVec.msb_eq_decide, Word.toBitVec64_poly_toNat_poly h_isU64, Word.toNat_poly_def]
  -- Goal: decide (2^(64-1) ≤ b0+b1*2^16+b2*2^32+b3*2^48) = decide (b3 ≥ 32768)
  -- Substitute concrete numerics so omega can close.
  have e16 : (2 : ℕ) ^ 16 = 65536 := by decide
  have e32 : (2 : ℕ) ^ 32 = 4294967296 := by decide
  have e48 : (2 : ℕ) ^ 48 = 281474976710656 := by decide
  have e63 : (2 : ℕ) ^ (64 - 1) = 9223372036854775808 := by decide
  rw [e16, e32, e48, e63] at *
  congr 1
  apply propext
  constructor
  · intro h; omega
  · intro h; omega

/-- Generic bound for the lr_j limb form: given the byte decomposition `hl < M`,
`ll < N` with `M*N = 65536` and `v0123.val = M`, conclude `(hl + ll*v0123).val < 65536`.
This is the poly analog of `limb_16_of_cancel` (Common.lean:81) but as a generic
parameterized bound rather than a 16-way case split — callers supply (M, N) per
sub-case. -/
lemma limb_16_lt_aux_poly {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (M N : ℕ) (h_MN : M * N = 65536) (h_M_pos : 0 < M)
    {hl ll v0123 : ZMod p}
    (h_v0123_eq : v0123.val = M)
    (lt_hl : hl.val < M) (lt_ll : ll.val < N) :
    (hl + ll * v0123).val < 65536 := by
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  have hp : 2 ^ 17 < p := Fact.out
  have h_N_pos : 0 < N := by nlinarith [h_MN, h_M_pos]
  have h_ll_v_lt_p : ll.val * v0123.val < p := by
    rw [h_v0123_eq]; nlinarith [h_MN, lt_ll, h_M_pos]
  have h_ll_v_val : (ll * v0123).val = ll.val * v0123.val :=
    ZMod.val_mul_of_lt h_ll_v_lt_p
  have h_add_lt_p : hl.val + (ll * v0123).val < p := by
    rw [h_ll_v_val, h_v0123_eq]; nlinarith [lt_hl, lt_ll, h_MN, h_M_pos]
  have h_add_val : (hl + ll * v0123).val = hl.val + (ll * v0123).val :=
    ZMod.val_add_of_lt h_add_lt_p
  rw [h_add_val, h_ll_v_val, h_v0123_eq]
  nlinarith [lt_hl, lt_ll, h_MN, h_M_pos]

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

-- `ops_U64_a_poly` (the SRLW-only U64-bound for the output `a`) lives in
-- `SP1Chips.ShiftRight.Srlw` as a private helper since it has exactly one consumer
-- there. The tri-bundle `ops_U64_poly` was unused and has been removed.

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

section srl_close_wrappers

/-- Within-byte right-shift identity for byte_shift=0. Given the cancellation
decomposition `b_j = hl_j * N + ll_j` (with `hl_j < M`, `ll_j < N`, `M*N=65536`,
and `v0123.val = M`), the 4-limb output vector `[hl_j + ll_{j+1}·v0123, ..., hl_3]`
equals the input shifted right by `S = log2(N)` bits.

This is the SR mirror of `sll_within_byte_shift_poly` (ShiftLeft/Common.lean:96).
The role of M/N is swapped from SLL: in SR, `v0123 = 2^(16-S) = M`, and the shift
factor is `N = 2^S`. The output composes `hl_j + ll_{j+1}·v0123` (carries down for
right-shift) instead of `ll_j·v0123 + hl_{j-1}` (carries up for left-shift). -/
lemma srl_within_byte_shift_poly {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (M N : ℕ) (h_MN : M * N = 65536) (h_M_pos : 0 < M)
    {b0 b1 b2 b3 ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 v0123 : ZMod p}
    (h_v_val : v0123.val = M)
    (lt_ll0 : ll0.val < N) (lt_ll1 : ll1.val < N)
    (lt_ll2 : ll2.val < N) (lt_ll3 : ll3.val < N)
    (lt_lh0 : hl0.val < M) (lt_lh1 : hl1.val < M)
    (lt_lh2 : hl2.val < M) (lt_lh3 : hl3.val < M)
    (h_b0 : b0 = hl0 * ((N : ℕ) : ZMod p) + ll0)
    (h_b1 : b1 = hl1 * ((N : ℕ) : ZMod p) + ll1)
    (h_b2 : b2 = hl2 * ((N : ℕ) : ZMod p) + ll2)
    (h_b3 : b3 = hl3 * ((N : ℕ) : ZMod p) + ll3) :
    (Word.toBitVec64_poly #v[hl0 + ll1 * v0123, hl1 + ll2 * v0123,
                              hl2 + ll3 * v0123, hl3]).toNat
    = (Word.toBitVec64_poly #v[b0, b1, b2, b3]).toNat / N := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_N_lt_p : N < p := by nlinarith [h_MN]
  have h_N_val : ((N : ℕ) : ZMod p).val = N := ZMod.val_natCast_of_lt h_N_lt_p
  have h_NM : N * M = 65536 := by linarith [h_MN, Nat.mul_comm M N]
  have h_N_pos : 0 < N := by nlinarith [h_MN, h_M_pos]
  -- val_mul bridges for ll_{j+1} * v0123 (j=0,1,2)
  have h_ll1_mul : (ll1 * v0123).val = ll1.val * M := by
    rw [ZMod.val_mul_of_lt, h_v_val]; rw [h_v_val]; nlinarith [lt_ll1, h_MN]
  have h_ll2_mul : (ll2 * v0123).val = ll2.val * M := by
    rw [ZMod.val_mul_of_lt, h_v_val]; rw [h_v_val]; nlinarith [lt_ll2, h_MN]
  have h_ll3_mul : (ll3 * v0123).val = ll3.val * M := by
    rw [ZMod.val_mul_of_lt, h_v_val]; rw [h_v_val]; nlinarith [lt_ll3, h_MN]
  -- val_mul bridges for hl_j * ↑N
  have h_hl0_mul : (hl0 * ((N : ℕ) : ZMod p)).val = hl0.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh0, h_MN, h_NM]
  have h_hl1_mul : (hl1 * ((N : ℕ) : ZMod p)).val = hl1.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh1, h_MN, h_NM]
  have h_hl2_mul : (hl2 * ((N : ℕ) : ZMod p)).val = hl2.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh2, h_MN, h_NM]
  have h_hl3_mul : (hl3 * ((N : ℕ) : ZMod p)).val = hl3.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh3, h_MN, h_NM]
  -- b_j.val = hl_j.val * N + ll_j.val
  have h_b0_val : b0.val = hl0.val * N + ll0.val := by
    rw [h_b0, ZMod.val_add_of_lt]
    · rw [h_hl0_mul]
    · rw [h_hl0_mul]; nlinarith [lt_ll0, lt_lh0, h_MN, h_NM]
  have h_b1_val : b1.val = hl1.val * N + ll1.val := by
    rw [h_b1, ZMod.val_add_of_lt]
    · rw [h_hl1_mul]
    · rw [h_hl1_mul]; nlinarith [lt_ll1, lt_lh1, h_MN, h_NM]
  have h_b2_val : b2.val = hl2.val * N + ll2.val := by
    rw [h_b2, ZMod.val_add_of_lt]
    · rw [h_hl2_mul]
    · rw [h_hl2_mul]; nlinarith [lt_ll2, lt_lh2, h_MN, h_NM]
  have h_b3_val : b3.val = hl3.val * N + ll3.val := by
    rw [h_b3, ZMod.val_add_of_lt]
    · rw [h_hl3_mul]
    · rw [h_hl3_mul]; nlinarith [lt_ll3, lt_lh3, h_MN, h_NM]
  -- (hl_j + ll_{j+1} * v0123).val for j = 0, 1, 2
  have h_compose0_val : (hl0 + ll1 * v0123).val = hl0.val + ll1.val * M := by
    rw [ZMod.val_add_of_lt]
    · rw [h_ll1_mul]
    · rw [h_ll1_mul]; nlinarith [lt_lh0, lt_ll1, h_MN]
  have h_compose1_val : (hl1 + ll2 * v0123).val = hl1.val + ll2.val * M := by
    rw [ZMod.val_add_of_lt]
    · rw [h_ll2_mul]
    · rw [h_ll2_mul]; nlinarith [lt_lh1, lt_ll2, h_MN]
  have h_compose2_val : (hl2 + ll3 * v0123).val = hl2.val + ll3.val * M := by
    rw [ZMod.val_add_of_lt]
    · rw [h_ll3_mul]
    · rw [h_ll3_mul]; nlinarith [lt_lh2, lt_ll3, h_MN]
  unfold Word.toBitVec64_poly
  simp only [BitVec.toNat_ofNat, Word.toNat_poly_def, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  rw [h_compose0_val, h_compose1_val, h_compose2_val,
      h_b0_val, h_b1_val, h_b2_val, h_b3_val]
  -- Per-byte bounds (used for the final mod_eq_of_lt steps).
  have h_b0_lt : hl0.val * N + ll0.val < 65536 := by nlinarith [lt_lh0, lt_ll0, h_MN]
  have h_b1_lt : hl1.val * N + ll1.val < 65536 := by nlinarith [lt_lh1, lt_ll1, h_MN]
  have h_b2_lt : hl2.val * N + ll2.val < 65536 := by nlinarith [lt_lh2, lt_ll2, h_MN]
  have h_b3_lt : hl3.val * N + ll3.val < 65536 := by nlinarith [lt_lh3, lt_ll3, h_MN]
  have h_lhs0_lt : hl0.val + ll1.val * M < 65536 := by nlinarith [lt_lh0, lt_ll1, h_MN]
  have h_lhs1_lt : hl1.val + ll2.val * M < 65536 := by nlinarith [lt_lh1, lt_ll2, h_MN]
  have h_lhs2_lt : hl2.val + ll3.val * M < 65536 := by nlinarith [lt_lh2, lt_ll3, h_MN]
  have h_lhs3_lt : hl3.val < 65536 := by nlinarith [lt_lh3, h_MN]
  -- Both sides fit in 2^64.
  have h_B_lt : (hl0.val * N + ll0.val) + (hl1.val * N + ll1.val) * 2 ^ 16
              + (hl2.val * N + ll2.val) * 2 ^ 32 + (hl3.val * N + ll3.val) * 2 ^ 48 < 2 ^ 64 := by
    omega
  have h_L_lt : (hl0.val + ll1.val * M) + (hl1.val + ll2.val * M) * 2 ^ 16
              + (hl2.val + ll3.val * M) * 2 ^ 32 + hl3.val * 2 ^ 48 < 2 ^ 64 := by
    omega
  -- Key Nat identity: N * L_inner + ll0.val = B_inner.
  have h_key : N * ((hl0.val + ll1.val * M) + (hl1.val + ll2.val * M) * 2 ^ 16
                + (hl2.val + ll3.val * M) * 2 ^ 32 + hl3.val * 2 ^ 48) + ll0.val
            = (hl0.val * N + ll0.val) + (hl1.val * N + ll1.val) * 2 ^ 16
              + (hl2.val * N + ll2.val) * 2 ^ 32 + (hl3.val * N + ll3.val) * 2 ^ 48 := by
    linear_combination
      (ll1.val + ll2.val * 2 ^ 16 + ll3.val * 2 ^ 32) * h_MN
  -- Goal: L_inner % 2^64 = B_inner % 2^64 / N % 2^64.
  rw [Nat.mod_eq_of_lt h_L_lt, Nat.mod_eq_of_lt h_B_lt, ← h_key]
  -- Goal: L_inner = (N * L_inner + ll0.val) / N % 2^64.
  rw [Nat.add_comm (N * _) ll0.val, Nat.mul_comm N _,
      Nat.add_mul_div_right _ _ h_N_pos, Nat.div_eq_of_lt lt_ll0, Nat.zero_add]

/-- Byte-shift=1 variant of `srl_within_byte_shift_poly`. The output vector starts
at byte index 1 of the within-byte result; the high byte is 0. Total shift = S+16,
so divisor = N * 2^16. -/
lemma srl_within_byte_shift_1_poly {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (M N : ℕ) (h_MN : M * N = 65536) (h_M_pos : 0 < M)
    {b0 b1 b2 b3 ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 v0123 : ZMod p}
    (h_v_val : v0123.val = M)
    (lt_ll0 : ll0.val < N) (lt_ll1 : ll1.val < N)
    (lt_ll2 : ll2.val < N) (lt_ll3 : ll3.val < N)
    (lt_lh0 : hl0.val < M) (lt_lh1 : hl1.val < M)
    (lt_lh2 : hl2.val < M) (lt_lh3 : hl3.val < M)
    (h_b0 : b0 = hl0 * ((N : ℕ) : ZMod p) + ll0)
    (h_b1 : b1 = hl1 * ((N : ℕ) : ZMod p) + ll1)
    (h_b2 : b2 = hl2 * ((N : ℕ) : ZMod p) + ll2)
    (h_b3 : b3 = hl3 * ((N : ℕ) : ZMod p) + ll3) :
    (Word.toBitVec64_poly #v[hl1 + ll2 * v0123, hl2 + ll3 * v0123, hl3, 0]).toNat
    = (Word.toBitVec64_poly #v[b0, b1, b2, b3]).toNat / (N * 2 ^ 16) := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_N_lt_p : N < p := by nlinarith [h_MN]
  have h_N_val : ((N : ℕ) : ZMod p).val = N := ZMod.val_natCast_of_lt h_N_lt_p
  have h_NM : N * M = 65536 := by linarith [h_MN, Nat.mul_comm M N]
  have h_N_pos : 0 < N := by nlinarith [h_MN, h_M_pos]
  have h_ll2_mul : (ll2 * v0123).val = ll2.val * M := by
    rw [ZMod.val_mul_of_lt, h_v_val]; rw [h_v_val]; nlinarith [lt_ll2, h_MN]
  have h_ll3_mul : (ll3 * v0123).val = ll3.val * M := by
    rw [ZMod.val_mul_of_lt, h_v_val]; rw [h_v_val]; nlinarith [lt_ll3, h_MN]
  have h_hl0_mul : (hl0 * ((N : ℕ) : ZMod p)).val = hl0.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh0, h_MN, h_NM]
  have h_hl1_mul : (hl1 * ((N : ℕ) : ZMod p)).val = hl1.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh1, h_MN, h_NM]
  have h_hl2_mul : (hl2 * ((N : ℕ) : ZMod p)).val = hl2.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh2, h_MN, h_NM]
  have h_hl3_mul : (hl3 * ((N : ℕ) : ZMod p)).val = hl3.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh3, h_MN, h_NM]
  have h_b0_val : b0.val = hl0.val * N + ll0.val := by
    rw [h_b0, ZMod.val_add_of_lt]
    · rw [h_hl0_mul]
    · rw [h_hl0_mul]; nlinarith [lt_ll0, lt_lh0, h_MN, h_NM]
  have h_b1_val : b1.val = hl1.val * N + ll1.val := by
    rw [h_b1, ZMod.val_add_of_lt]
    · rw [h_hl1_mul]
    · rw [h_hl1_mul]; nlinarith [lt_ll1, lt_lh1, h_MN, h_NM]
  have h_b2_val : b2.val = hl2.val * N + ll2.val := by
    rw [h_b2, ZMod.val_add_of_lt]
    · rw [h_hl2_mul]
    · rw [h_hl2_mul]; nlinarith [lt_ll2, lt_lh2, h_MN, h_NM]
  have h_b3_val : b3.val = hl3.val * N + ll3.val := by
    rw [h_b3, ZMod.val_add_of_lt]
    · rw [h_hl3_mul]
    · rw [h_hl3_mul]; nlinarith [lt_ll3, lt_lh3, h_MN, h_NM]
  have h_compose1_val : (hl1 + ll2 * v0123).val = hl1.val + ll2.val * M := by
    rw [ZMod.val_add_of_lt]
    · rw [h_ll2_mul]
    · rw [h_ll2_mul]; nlinarith [lt_lh1, lt_ll2, h_MN]
  have h_compose2_val : (hl2 + ll3 * v0123).val = hl2.val + ll3.val * M := by
    rw [ZMod.val_add_of_lt]
    · rw [h_ll3_mul]
    · rw [h_ll3_mul]; nlinarith [lt_lh2, lt_ll3, h_MN]
  unfold Word.toBitVec64_poly
  simp only [BitVec.toNat_ofNat, Word.toNat_poly_def, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, ZMod.val_zero,
    zero_mul, add_zero]
  rw [h_compose1_val, h_compose2_val,
      h_b0_val, h_b1_val, h_b2_val, h_b3_val]
  have h_b0_lt : hl0.val * N + ll0.val < 65536 := by nlinarith [lt_lh0, lt_ll0, h_MN]
  have h_b1_lt : hl1.val * N + ll1.val < 65536 := by nlinarith [lt_lh1, lt_ll1, h_MN]
  have h_b2_lt : hl2.val * N + ll2.val < 65536 := by nlinarith [lt_lh2, lt_ll2, h_MN]
  have h_b3_lt : hl3.val * N + ll3.val < 65536 := by nlinarith [lt_lh3, lt_ll3, h_MN]
  have h_lhs1_lt : hl1.val + ll2.val * M < 65536 := by nlinarith [lt_lh1, lt_ll2, h_MN]
  have h_lhs2_lt : hl2.val + ll3.val * M < 65536 := by nlinarith [lt_lh2, lt_ll3, h_MN]
  have h_lhs3_lt : hl3.val < 65536 := by nlinarith [lt_lh3, h_MN]
  have h_B_lt : (hl0.val * N + ll0.val) + (hl1.val * N + ll1.val) * 2 ^ 16
              + (hl2.val * N + ll2.val) * 2 ^ 32 + (hl3.val * N + ll3.val) * 2 ^ 48 < 2 ^ 64 := by
    omega
  have h_L_lt : (hl1.val + ll2.val * M) + (hl2.val + ll3.val * M) * 2 ^ 16 + hl3.val * 2 ^ 32 < 2 ^ 64 := by
    omega
  have h_rem_lt : (hl0.val * N + ll0.val) + 2 ^ 16 * ll1.val < N * 2 ^ 16 := by
    nlinarith [lt_lh0, lt_ll0, lt_ll1, h_MN, h_NM, h_N_pos]
  have h_NM16_pos : 0 < N * 2 ^ 16 := Nat.mul_pos h_N_pos (by omega)
  -- Key identity: (N * 2^16) * L_1 + (b_0 + 2^16 * ll_1) = B.
  have h_key : (N * 2 ^ 16) * ((hl1.val + ll2.val * M) + (hl2.val + ll3.val * M) * 2 ^ 16
                + hl3.val * 2 ^ 32) + ((hl0.val * N + ll0.val) + 2 ^ 16 * ll1.val)
            = (hl0.val * N + ll0.val) + (hl1.val * N + ll1.val) * 2 ^ 16
              + (hl2.val * N + ll2.val) * 2 ^ 32 + (hl3.val * N + ll3.val) * 2 ^ 48 := by
    linear_combination
      (ll2.val + ll3.val * 2 ^ 16) * 2 ^ 16 * h_MN
  rw [Nat.mod_eq_of_lt h_L_lt, Nat.mod_eq_of_lt h_B_lt, ← h_key]
  rw [Nat.add_comm ((N * 2 ^ 16) * _) _, Nat.mul_comm (N * 2 ^ 16) _,
      Nat.add_mul_div_right _ _ h_NM16_pos, Nat.div_eq_of_lt h_rem_lt, Nat.zero_add]

/-- Byte-shift=2 variant. Output starts at byte index 2; top two bytes are 0.
Total shift = S + 32, so divisor = N * 2^32. -/
lemma srl_within_byte_shift_2_poly {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (M N : ℕ) (h_MN : M * N = 65536) (h_M_pos : 0 < M)
    {b0 b1 b2 b3 ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 v0123 : ZMod p}
    (h_v_val : v0123.val = M)
    (lt_ll0 : ll0.val < N) (lt_ll1 : ll1.val < N)
    (lt_ll2 : ll2.val < N) (lt_ll3 : ll3.val < N)
    (lt_lh0 : hl0.val < M) (lt_lh1 : hl1.val < M)
    (lt_lh2 : hl2.val < M) (lt_lh3 : hl3.val < M)
    (h_b0 : b0 = hl0 * ((N : ℕ) : ZMod p) + ll0)
    (h_b1 : b1 = hl1 * ((N : ℕ) : ZMod p) + ll1)
    (h_b2 : b2 = hl2 * ((N : ℕ) : ZMod p) + ll2)
    (h_b3 : b3 = hl3 * ((N : ℕ) : ZMod p) + ll3) :
    (Word.toBitVec64_poly #v[hl2 + ll3 * v0123, hl3, 0, 0]).toNat
    = (Word.toBitVec64_poly #v[b0, b1, b2, b3]).toNat / (N * 2 ^ 32) := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_N_lt_p : N < p := by nlinarith [h_MN]
  have h_N_val : ((N : ℕ) : ZMod p).val = N := ZMod.val_natCast_of_lt h_N_lt_p
  have h_NM : N * M = 65536 := by linarith [h_MN, Nat.mul_comm M N]
  have h_N_pos : 0 < N := by nlinarith [h_MN, h_M_pos]
  have h_ll3_mul : (ll3 * v0123).val = ll3.val * M := by
    rw [ZMod.val_mul_of_lt, h_v_val]; rw [h_v_val]; nlinarith [lt_ll3, h_MN]
  have h_hl0_mul : (hl0 * ((N : ℕ) : ZMod p)).val = hl0.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh0, h_MN, h_NM]
  have h_hl1_mul : (hl1 * ((N : ℕ) : ZMod p)).val = hl1.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh1, h_MN, h_NM]
  have h_hl2_mul : (hl2 * ((N : ℕ) : ZMod p)).val = hl2.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh2, h_MN, h_NM]
  have h_hl3_mul : (hl3 * ((N : ℕ) : ZMod p)).val = hl3.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh3, h_MN, h_NM]
  have h_b0_val : b0.val = hl0.val * N + ll0.val := by
    rw [h_b0, ZMod.val_add_of_lt]
    · rw [h_hl0_mul]
    · rw [h_hl0_mul]; nlinarith [lt_ll0, lt_lh0, h_MN, h_NM]
  have h_b1_val : b1.val = hl1.val * N + ll1.val := by
    rw [h_b1, ZMod.val_add_of_lt]
    · rw [h_hl1_mul]
    · rw [h_hl1_mul]; nlinarith [lt_ll1, lt_lh1, h_MN, h_NM]
  have h_b2_val : b2.val = hl2.val * N + ll2.val := by
    rw [h_b2, ZMod.val_add_of_lt]
    · rw [h_hl2_mul]
    · rw [h_hl2_mul]; nlinarith [lt_ll2, lt_lh2, h_MN, h_NM]
  have h_b3_val : b3.val = hl3.val * N + ll3.val := by
    rw [h_b3, ZMod.val_add_of_lt]
    · rw [h_hl3_mul]
    · rw [h_hl3_mul]; nlinarith [lt_ll3, lt_lh3, h_MN, h_NM]
  have h_compose2_val : (hl2 + ll3 * v0123).val = hl2.val + ll3.val * M := by
    rw [ZMod.val_add_of_lt]
    · rw [h_ll3_mul]
    · rw [h_ll3_mul]; nlinarith [lt_lh2, lt_ll3, h_MN]
  unfold Word.toBitVec64_poly
  simp only [BitVec.toNat_ofNat, Word.toNat_poly_def, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, ZMod.val_zero,
    zero_mul, add_zero]
  rw [h_compose2_val,
      h_b0_val, h_b1_val, h_b2_val, h_b3_val]
  have h_b0_lt : hl0.val * N + ll0.val < 65536 := by nlinarith [lt_lh0, lt_ll0, h_MN]
  have h_b1_lt : hl1.val * N + ll1.val < 65536 := by nlinarith [lt_lh1, lt_ll1, h_MN]
  have h_b2_lt : hl2.val * N + ll2.val < 65536 := by nlinarith [lt_lh2, lt_ll2, h_MN]
  have h_b3_lt : hl3.val * N + ll3.val < 65536 := by nlinarith [lt_lh3, lt_ll3, h_MN]
  have h_lhs2_lt : hl2.val + ll3.val * M < 65536 := by nlinarith [lt_lh2, lt_ll3, h_MN]
  have h_lhs3_lt : hl3.val < 65536 := by nlinarith [lt_lh3, h_MN]
  have h_B_lt : (hl0.val * N + ll0.val) + (hl1.val * N + ll1.val) * 2 ^ 16
              + (hl2.val * N + ll2.val) * 2 ^ 32 + (hl3.val * N + ll3.val) * 2 ^ 48 < 2 ^ 64 := by
    omega
  have h_L_lt : (hl2.val + ll3.val * M) + hl3.val * 2 ^ 16 < 2 ^ 64 := by
    omega
  have h_rem_lt : ((hl0.val * N + ll0.val) + (hl1.val * N + ll1.val) * 2 ^ 16) + 2 ^ 32 * ll2.val < N * 2 ^ 32 := by
    nlinarith [lt_lh0, lt_ll0, lt_lh1, lt_ll1, lt_ll2, h_MN, h_NM, h_N_pos]
  have h_NM32_pos : 0 < N * 2 ^ 32 := Nat.mul_pos h_N_pos (by omega)
  have h_key : (N * 2 ^ 32) * ((hl2.val + ll3.val * M) + hl3.val * 2 ^ 16)
              + (((hl0.val * N + ll0.val) + (hl1.val * N + ll1.val) * 2 ^ 16) + 2 ^ 32 * ll2.val)
            = (hl0.val * N + ll0.val) + (hl1.val * N + ll1.val) * 2 ^ 16
              + (hl2.val * N + ll2.val) * 2 ^ 32 + (hl3.val * N + ll3.val) * 2 ^ 48 := by
    linear_combination
      ll3.val * 2 ^ 32 * h_MN
  rw [Nat.mod_eq_of_lt h_L_lt, Nat.mod_eq_of_lt h_B_lt, ← h_key]
  rw [Nat.add_comm ((N * 2 ^ 32) * _) _, Nat.mul_comm (N * 2 ^ 32) _,
      Nat.add_mul_div_right _ _ h_NM32_pos, Nat.div_eq_of_lt h_rem_lt, Nat.zero_add]

/-- Byte-shift=3 variant. Output is just `hl_3` in byte 0; bytes 1, 2, 3 are 0.
Total shift = S + 48, so divisor = N * 2^48. -/
lemma srl_within_byte_shift_3_poly {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (M N : ℕ) (h_MN : M * N = 65536) (h_M_pos : 0 < M)
    {b0 b1 b2 b3 ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 v0123 : ZMod p}
    (h_v_val : v0123.val = M)
    (lt_ll0 : ll0.val < N) (lt_ll1 : ll1.val < N)
    (lt_ll2 : ll2.val < N) (lt_ll3 : ll3.val < N)
    (lt_lh0 : hl0.val < M) (lt_lh1 : hl1.val < M)
    (lt_lh2 : hl2.val < M) (lt_lh3 : hl3.val < M)
    (h_b0 : b0 = hl0 * ((N : ℕ) : ZMod p) + ll0)
    (h_b1 : b1 = hl1 * ((N : ℕ) : ZMod p) + ll1)
    (h_b2 : b2 = hl2 * ((N : ℕ) : ZMod p) + ll2)
    (h_b3 : b3 = hl3 * ((N : ℕ) : ZMod p) + ll3) :
    (Word.toBitVec64_poly #v[hl3, 0, 0, 0]).toNat
    = (Word.toBitVec64_poly #v[b0, b1, b2, b3]).toNat / (N * 2 ^ 48) := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_N_lt_p : N < p := by nlinarith [h_MN]
  have h_N_val : ((N : ℕ) : ZMod p).val = N := ZMod.val_natCast_of_lt h_N_lt_p
  have h_NM : N * M = 65536 := by linarith [h_MN, Nat.mul_comm M N]
  have h_N_pos : 0 < N := by nlinarith [h_MN, h_M_pos]
  have h_hl0_mul : (hl0 * ((N : ℕ) : ZMod p)).val = hl0.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh0, h_MN, h_NM]
  have h_hl1_mul : (hl1 * ((N : ℕ) : ZMod p)).val = hl1.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh1, h_MN, h_NM]
  have h_hl2_mul : (hl2 * ((N : ℕ) : ZMod p)).val = hl2.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh2, h_MN, h_NM]
  have h_hl3_mul : (hl3 * ((N : ℕ) : ZMod p)).val = hl3.val * N := by
    rw [ZMod.val_mul_of_lt, h_N_val]; rw [h_N_val]; nlinarith [lt_lh3, h_MN, h_NM]
  have h_b0_val : b0.val = hl0.val * N + ll0.val := by
    rw [h_b0, ZMod.val_add_of_lt]
    · rw [h_hl0_mul]
    · rw [h_hl0_mul]; nlinarith [lt_ll0, lt_lh0, h_MN, h_NM]
  have h_b1_val : b1.val = hl1.val * N + ll1.val := by
    rw [h_b1, ZMod.val_add_of_lt]
    · rw [h_hl1_mul]
    · rw [h_hl1_mul]; nlinarith [lt_ll1, lt_lh1, h_MN, h_NM]
  have h_b2_val : b2.val = hl2.val * N + ll2.val := by
    rw [h_b2, ZMod.val_add_of_lt]
    · rw [h_hl2_mul]
    · rw [h_hl2_mul]; nlinarith [lt_ll2, lt_lh2, h_MN, h_NM]
  have h_b3_val : b3.val = hl3.val * N + ll3.val := by
    rw [h_b3, ZMod.val_add_of_lt]
    · rw [h_hl3_mul]
    · rw [h_hl3_mul]; nlinarith [lt_ll3, lt_lh3, h_MN, h_NM]
  unfold Word.toBitVec64_poly
  simp only [BitVec.toNat_ofNat, Word.toNat_poly_def, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, ZMod.val_zero,
    zero_mul, add_zero]
  rw [h_b0_val, h_b1_val, h_b2_val, h_b3_val]
  have h_b0_lt : hl0.val * N + ll0.val < 65536 := by nlinarith [lt_lh0, lt_ll0, h_MN]
  have h_b1_lt : hl1.val * N + ll1.val < 65536 := by nlinarith [lt_lh1, lt_ll1, h_MN]
  have h_b2_lt : hl2.val * N + ll2.val < 65536 := by nlinarith [lt_lh2, lt_ll2, h_MN]
  have h_b3_lt : hl3.val * N + ll3.val < 65536 := by nlinarith [lt_lh3, lt_ll3, h_MN]
  have h_lhs0_lt : hl3.val < 65536 := by nlinarith [lt_lh3, h_MN]
  have h_B_lt : (hl0.val * N + ll0.val) + (hl1.val * N + ll1.val) * 2 ^ 16
              + (hl2.val * N + ll2.val) * 2 ^ 32 + (hl3.val * N + ll3.val) * 2 ^ 48 < 2 ^ 64 := by
    omega
  have h_L_lt : hl3.val < 2 ^ 64 := by omega
  have h_rem_lt : ((hl0.val * N + ll0.val) + (hl1.val * N + ll1.val) * 2 ^ 16
                 + (hl2.val * N + ll2.val) * 2 ^ 32) + 2 ^ 48 * ll3.val < N * 2 ^ 48 := by
    nlinarith [lt_lh0, lt_ll0, lt_lh1, lt_ll1, lt_lh2, lt_ll2, lt_ll3, h_MN, h_NM, h_N_pos]
  have h_NM48_pos : 0 < N * 2 ^ 48 := Nat.mul_pos h_N_pos (by omega)
  have h_key : (N * 2 ^ 48) * hl3.val
              + (((hl0.val * N + ll0.val) + (hl1.val * N + ll1.val) * 2 ^ 16
                 + (hl2.val * N + ll2.val) * 2 ^ 32) + 2 ^ 48 * ll3.val)
            = (hl0.val * N + ll0.val) + (hl1.val * N + ll1.val) * 2 ^ 16
              + (hl2.val * N + ll2.val) * 2 ^ 32 + (hl3.val * N + ll3.val) * 2 ^ 48 := by
    ring
  rw [Nat.mod_eq_of_lt h_L_lt, Nat.mod_eq_of_lt h_B_lt, ← h_key]
  rw [Nat.add_comm ((N * 2 ^ 48) * _) _, Nat.mul_comm (N * 2 ^ 48) _,
      Nat.add_mul_div_right _ _ h_NM48_pos, Nat.div_eq_of_lt h_rem_lt, Nat.zero_add]

/-- Convenience wrapper for `spec.srl_common_poly`'s `byte_shift=0` case (su160 = 1).
Combines `cancel_mul_65536_poly`, bound normalization, and the `>>>`-to-`/` bridge
so each within-byte sub-case can be closed by providing only the cb_i substitution
facts and the numeric (S, M, N) triple.

Mirrors `sll_close_cb4cb5_zero_case` (ShiftLeft/Common.lean:185); the role-swap
between SLL and SR puts `M = 2^(16-S)` (the v0123 value) and `N = 2^S` (the shift
amount factor) — opposite of SLL where `M = 2^S` and `N = 2^(16-S)`. -/
lemma srl_close_su16_0_case {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (S : ℕ) (h_S_le : S ≤ 15) (M N : ℕ)
    (h_MN : M * N = 65536) (h_M_pos : 0 < M) (h_M_eq : M = 2 ^ (16 - S))
    (h_N_eq : N = 2 ^ S)
    {cb0 cb1 cb2 cb3 cb4 cb5 v0123 b0 b1 b2 b3
      ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 : ZMod p}
    (h_M_lt_p : M < p) (h_v0123_explicit : v0123 = ((M : ℕ) : ZMod p))
    (h_inner_eq : cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8
                  = ((S : ℕ) : ZMod p))
    (h_total_eq : cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32
                  = ((S : ℕ) : ZMod p))
    (lt_ll0 : ll0.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (lt_lh0 : hl0.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_ll1 : ll1.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (lt_lh1 : hl1.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_ll2 : ll2.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (lt_lh2 : hl2.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_ll3 : ll3.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (lt_lh3 : hl3.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (h_b0_dec : b0 * v0123 = hl0 * ((65536 : ℕ) : ZMod p) + ll0 * v0123)
    (h_b1_dec : b1 * v0123 = hl1 * ((65536 : ℕ) : ZMod p) + ll1 * v0123)
    (h_b2_dec : b2 * v0123 = hl2 * ((65536 : ℕ) : ZMod p) + ll2 * v0123)
    (h_b3_dec : b3 * v0123 = hl3 * ((65536 : ℕ) : ZMod p) + ll3 * v0123) :
    (Word.toBitVec64_poly #v[hl0 + ll1 * v0123, hl1 + ll2 * v0123,
                              hl2 + ll3 * v0123, hl3]).toNat
    = (Word.toBitVec64_poly #v[b0, b1, b2, b3]).toNat
        / 2 ^ (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_v_val : v0123.val = M := by
    rw [h_v0123_explicit]; exact ZMod.val_natCast_of_lt h_M_lt_p
  -- Normalize bounds using h_inner_eq. For SR, ll < 2^S (the inner sum), hl < 2^(16-S).
  have h_inner_val : (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                      + cb3 * 8 : ZMod p).val = S := by
    rw [h_inner_eq]; exact ZMod.val_natCast_of_lt (by omega)
  have h_inner_hi_val : (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                + cb3 * 8) : ZMod p).val = 16 - S := by
    rw [show (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
              + cb3 * 8) : ZMod p) = (((16 - S) : ℕ) : ZMod p) from by
      rw [h_inner_eq, Nat.cast_sub (by omega : S ≤ 16)]; push_cast; ring]
    exact ZMod.val_natCast_of_lt (by omega)
  rw [h_inner_val] at lt_ll0 lt_ll1 lt_ll2 lt_ll3
  rw [h_inner_hi_val] at lt_lh0 lt_lh1 lt_lh2 lt_lh3
  -- Total shift = S.
  have h_total_val : (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val
                      = S := by
    rw [h_total_eq]; exact ZMod.val_natCast_of_lt (by omega)
  rw [h_total_val]
  -- Apply cancel_mul_65536_poly to extract b_j = hl_j * N + ll_j.
  have hdvd : v0123.val ∣ 65536 := by rw [h_v_val]; exact ⟨N, h_MN.symm⟩
  have hpos : 0 < v0123.val := by rw [h_v_val]; exact h_M_pos
  have h_b0' := cancel_mul_65536_poly hdvd hpos h_b0_dec
  have h_b1' := cancel_mul_65536_poly hdvd hpos h_b1_dec
  have h_b2' := cancel_mul_65536_poly hdvd hpos h_b2_dec
  have h_b3' := cancel_mul_65536_poly hdvd hpos h_b3_dec
  rw [h_v_val] at h_b0' h_b1' h_b2' h_b3'
  -- Bridge `/ 2^S` to `/ N`.
  rw [show (2 : ℕ) ^ S = N from h_N_eq.symm]
  -- Replace `65536/M` in h_b_j' with `N`.
  have h_div_eq : (65536 : ℕ) / M = N := by
    rw [← h_MN]; exact Nat.mul_div_cancel_left N h_M_pos
  rw [h_div_eq] at h_b0' h_b1' h_b2' h_b3'
  -- Convert bounds from `2^S`/`2^(16-S)` to `N`/`M`.
  have h_lt_ll0 : ll0.val < N := by rw [h_N_eq]; exact lt_ll0
  have h_lt_ll1 : ll1.val < N := by rw [h_N_eq]; exact lt_ll1
  have h_lt_ll2 : ll2.val < N := by rw [h_N_eq]; exact lt_ll2
  have h_lt_ll3 : ll3.val < N := by rw [h_N_eq]; exact lt_ll3
  have h_lt_lh0 : hl0.val < M := by rw [h_M_eq]; exact lt_lh0
  have h_lt_lh1 : hl1.val < M := by rw [h_M_eq]; exact lt_lh1
  have h_lt_lh2 : hl2.val < M := by rw [h_M_eq]; exact lt_lh2
  have h_lt_lh3 : hl3.val < M := by rw [h_M_eq]; exact lt_lh3
  exact srl_within_byte_shift_poly M N h_MN h_M_pos h_v_val
    h_lt_ll0 h_lt_ll1 h_lt_ll2 h_lt_ll3 h_lt_lh0 h_lt_lh1 h_lt_lh2 h_lt_lh3
    h_b0' h_b1' h_b2' h_b3'

/-- Wrapper for `spec.srl_common_poly`'s `byte_shift=1` case (su161 = 1, cb4=1, cb5=0).
Total shift = S + 16. -/
lemma srl_close_su16_1_case {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (S : ℕ) (h_S_le : S ≤ 15) (M N : ℕ)
    (h_MN : M * N = 65536) (h_M_pos : 0 < M) (h_M_eq : M = 2 ^ (16 - S))
    (h_N_eq : N = 2 ^ S)
    {cb0 cb1 cb2 cb3 cb4 cb5 v0123 b0 b1 b2 b3
      ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 : ZMod p}
    (h_M_lt_p : M < p) (h_v0123_explicit : v0123 = ((M : ℕ) : ZMod p))
    (h_inner_eq : cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8
                  = ((S : ℕ) : ZMod p))
    (h_total_eq : cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32
                  = (((S + 16) : ℕ) : ZMod p))
    (lt_ll0 : ll0.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (lt_lh0 : hl0.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_ll1 : ll1.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (lt_lh1 : hl1.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_ll2 : ll2.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (lt_lh2 : hl2.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_ll3 : ll3.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (lt_lh3 : hl3.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (h_b0_dec : b0 * v0123 = hl0 * ((65536 : ℕ) : ZMod p) + ll0 * v0123)
    (h_b1_dec : b1 * v0123 = hl1 * ((65536 : ℕ) : ZMod p) + ll1 * v0123)
    (h_b2_dec : b2 * v0123 = hl2 * ((65536 : ℕ) : ZMod p) + ll2 * v0123)
    (h_b3_dec : b3 * v0123 = hl3 * ((65536 : ℕ) : ZMod p) + ll3 * v0123) :
    (Word.toBitVec64_poly #v[hl1 + ll2 * v0123, hl2 + ll3 * v0123, hl3, 0]).toNat
    = (Word.toBitVec64_poly #v[b0, b1, b2, b3]).toNat
        / 2 ^ (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_v_val : v0123.val = M := by
    rw [h_v0123_explicit]; exact ZMod.val_natCast_of_lt h_M_lt_p
  have h_inner_val : (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                      + cb3 * 8 : ZMod p).val = S := by
    rw [h_inner_eq]; exact ZMod.val_natCast_of_lt (by omega)
  have h_inner_hi_val : (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                + cb3 * 8) : ZMod p).val = 16 - S := by
    rw [show (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
              + cb3 * 8) : ZMod p) = (((16 - S) : ℕ) : ZMod p) from by
      rw [h_inner_eq, Nat.cast_sub (by omega : S ≤ 16)]; push_cast; ring]
    exact ZMod.val_natCast_of_lt (by omega)
  rw [h_inner_val] at lt_ll0 lt_ll1 lt_ll2 lt_ll3
  rw [h_inner_hi_val] at lt_lh0 lt_lh1 lt_lh2 lt_lh3
  have h_total_val : (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val
                      = S + 16 := by
    rw [h_total_eq]; exact ZMod.val_natCast_of_lt (by omega)
  rw [h_total_val]
  have hdvd : v0123.val ∣ 65536 := by rw [h_v_val]; exact ⟨N, h_MN.symm⟩
  have hpos : 0 < v0123.val := by rw [h_v_val]; exact h_M_pos
  have h_b0' := cancel_mul_65536_poly hdvd hpos h_b0_dec
  have h_b1' := cancel_mul_65536_poly hdvd hpos h_b1_dec
  have h_b2' := cancel_mul_65536_poly hdvd hpos h_b2_dec
  have h_b3' := cancel_mul_65536_poly hdvd hpos h_b3_dec
  rw [h_v_val] at h_b0' h_b1' h_b2' h_b3'
  -- Bridge `/ 2^(S+16)` to `/ (N * 2^16)`.
  rw [show (2 : ℕ) ^ (S + 16) = N * 2 ^ 16 from by rw [pow_add, h_N_eq]]
  have h_div_eq : (65536 : ℕ) / M = N := by
    rw [← h_MN]; exact Nat.mul_div_cancel_left N h_M_pos
  rw [h_div_eq] at h_b0' h_b1' h_b2' h_b3'
  have h_lt_ll0 : ll0.val < N := by rw [h_N_eq]; exact lt_ll0
  have h_lt_ll1 : ll1.val < N := by rw [h_N_eq]; exact lt_ll1
  have h_lt_ll2 : ll2.val < N := by rw [h_N_eq]; exact lt_ll2
  have h_lt_ll3 : ll3.val < N := by rw [h_N_eq]; exact lt_ll3
  have h_lt_lh0 : hl0.val < M := by rw [h_M_eq]; exact lt_lh0
  have h_lt_lh1 : hl1.val < M := by rw [h_M_eq]; exact lt_lh1
  have h_lt_lh2 : hl2.val < M := by rw [h_M_eq]; exact lt_lh2
  have h_lt_lh3 : hl3.val < M := by rw [h_M_eq]; exact lt_lh3
  exact srl_within_byte_shift_1_poly M N h_MN h_M_pos h_v_val
    h_lt_ll0 h_lt_ll1 h_lt_ll2 h_lt_ll3 h_lt_lh0 h_lt_lh1 h_lt_lh2 h_lt_lh3
    h_b0' h_b1' h_b2' h_b3'

/-- Wrapper for `spec.srl_common_poly`'s `byte_shift=2` case (su162 = 1, cb4=0, cb5=1).
Total shift = S + 32. -/
lemma srl_close_su16_2_case {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (S : ℕ) (h_S_le : S ≤ 15) (M N : ℕ)
    (h_MN : M * N = 65536) (h_M_pos : 0 < M) (h_M_eq : M = 2 ^ (16 - S))
    (h_N_eq : N = 2 ^ S)
    {cb0 cb1 cb2 cb3 cb4 cb5 v0123 b0 b1 b2 b3
      ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 : ZMod p}
    (h_M_lt_p : M < p) (h_v0123_explicit : v0123 = ((M : ℕ) : ZMod p))
    (h_inner_eq : cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8
                  = ((S : ℕ) : ZMod p))
    (h_total_eq : cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32
                  = (((S + 32) : ℕ) : ZMod p))
    (lt_ll0 : ll0.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (lt_lh0 : hl0.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_ll1 : ll1.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (lt_lh1 : hl1.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_ll2 : ll2.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (lt_lh2 : hl2.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_ll3 : ll3.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (lt_lh3 : hl3.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (h_b0_dec : b0 * v0123 = hl0 * ((65536 : ℕ) : ZMod p) + ll0 * v0123)
    (h_b1_dec : b1 * v0123 = hl1 * ((65536 : ℕ) : ZMod p) + ll1 * v0123)
    (h_b2_dec : b2 * v0123 = hl2 * ((65536 : ℕ) : ZMod p) + ll2 * v0123)
    (h_b3_dec : b3 * v0123 = hl3 * ((65536 : ℕ) : ZMod p) + ll3 * v0123) :
    (Word.toBitVec64_poly #v[hl2 + ll3 * v0123, hl3, 0, 0]).toNat
    = (Word.toBitVec64_poly #v[b0, b1, b2, b3]).toNat
        / 2 ^ (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_v_val : v0123.val = M := by
    rw [h_v0123_explicit]; exact ZMod.val_natCast_of_lt h_M_lt_p
  have h_inner_val : (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                      + cb3 * 8 : ZMod p).val = S := by
    rw [h_inner_eq]; exact ZMod.val_natCast_of_lt (by omega)
  have h_inner_hi_val : (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                + cb3 * 8) : ZMod p).val = 16 - S := by
    rw [show (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
              + cb3 * 8) : ZMod p) = (((16 - S) : ℕ) : ZMod p) from by
      rw [h_inner_eq, Nat.cast_sub (by omega : S ≤ 16)]; push_cast; ring]
    exact ZMod.val_natCast_of_lt (by omega)
  rw [h_inner_val] at lt_ll0 lt_ll1 lt_ll2 lt_ll3
  rw [h_inner_hi_val] at lt_lh0 lt_lh1 lt_lh2 lt_lh3
  have h_total_val : (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val
                      = S + 32 := by
    rw [h_total_eq]; exact ZMod.val_natCast_of_lt (by omega)
  rw [h_total_val]
  have hdvd : v0123.val ∣ 65536 := by rw [h_v_val]; exact ⟨N, h_MN.symm⟩
  have hpos : 0 < v0123.val := by rw [h_v_val]; exact h_M_pos
  have h_b0' := cancel_mul_65536_poly hdvd hpos h_b0_dec
  have h_b1' := cancel_mul_65536_poly hdvd hpos h_b1_dec
  have h_b2' := cancel_mul_65536_poly hdvd hpos h_b2_dec
  have h_b3' := cancel_mul_65536_poly hdvd hpos h_b3_dec
  rw [h_v_val] at h_b0' h_b1' h_b2' h_b3'
  rw [show (2 : ℕ) ^ (S + 32) = N * 2 ^ 32 from by rw [pow_add, h_N_eq]]
  have h_div_eq : (65536 : ℕ) / M = N := by
    rw [← h_MN]; exact Nat.mul_div_cancel_left N h_M_pos
  rw [h_div_eq] at h_b0' h_b1' h_b2' h_b3'
  have h_lt_ll0 : ll0.val < N := by rw [h_N_eq]; exact lt_ll0
  have h_lt_ll1 : ll1.val < N := by rw [h_N_eq]; exact lt_ll1
  have h_lt_ll2 : ll2.val < N := by rw [h_N_eq]; exact lt_ll2
  have h_lt_ll3 : ll3.val < N := by rw [h_N_eq]; exact lt_ll3
  have h_lt_lh0 : hl0.val < M := by rw [h_M_eq]; exact lt_lh0
  have h_lt_lh1 : hl1.val < M := by rw [h_M_eq]; exact lt_lh1
  have h_lt_lh2 : hl2.val < M := by rw [h_M_eq]; exact lt_lh2
  have h_lt_lh3 : hl3.val < M := by rw [h_M_eq]; exact lt_lh3
  exact srl_within_byte_shift_2_poly M N h_MN h_M_pos h_v_val
    h_lt_ll0 h_lt_ll1 h_lt_ll2 h_lt_ll3 h_lt_lh0 h_lt_lh1 h_lt_lh2 h_lt_lh3
    h_b0' h_b1' h_b2' h_b3'

/-- Wrapper for `spec.srl_common_poly`'s `byte_shift=3` case (su163 = 1, cb4=1, cb5=1).
Total shift = S + 48. -/
lemma srl_close_su16_3_case {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (S : ℕ) (h_S_le : S ≤ 15) (M N : ℕ)
    (h_MN : M * N = 65536) (h_M_pos : 0 < M) (h_M_eq : M = 2 ^ (16 - S))
    (h_N_eq : N = 2 ^ S)
    {cb0 cb1 cb2 cb3 cb4 cb5 v0123 b0 b1 b2 b3
      ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 : ZMod p}
    (h_M_lt_p : M < p) (h_v0123_explicit : v0123 = ((M : ℕ) : ZMod p))
    (h_inner_eq : cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p) + cb3 * 8
                  = ((S : ℕ) : ZMod p))
    (h_total_eq : cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32
                  = (((S + 48) : ℕ) : ZMod p))
    (lt_ll0 : ll0.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (lt_lh0 : hl0.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_ll1 : ll1.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (lt_lh1 : hl1.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_ll2 : ll2.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (lt_lh2 : hl2.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (lt_ll3 : ll3.val < 2 ^ (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                              + cb3 * 8 : ZMod p).val)
    (lt_lh3 : hl3.val < 2 ^ (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                   + cb3 * 8) : ZMod p).val)
    (h_b0_dec : b0 * v0123 = hl0 * ((65536 : ℕ) : ZMod p) + ll0 * v0123)
    (h_b1_dec : b1 * v0123 = hl1 * ((65536 : ℕ) : ZMod p) + ll1 * v0123)
    (h_b2_dec : b2 * v0123 = hl2 * ((65536 : ℕ) : ZMod p) + ll2 * v0123)
    (h_b3_dec : b3 * v0123 = hl3 * ((65536 : ℕ) : ZMod p) + ll3 * v0123) :
    (Word.toBitVec64_poly #v[hl3, 0, 0, 0]).toNat
    = (Word.toBitVec64_poly #v[b0, b1, b2, b3]).toNat
        / 2 ^ (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_v_val : v0123.val = M := by
    rw [h_v0123_explicit]; exact ZMod.val_natCast_of_lt h_M_lt_p
  have h_inner_val : (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                      + cb3 * 8 : ZMod p).val = S := by
    rw [h_inner_eq]; exact ZMod.val_natCast_of_lt (by omega)
  have h_inner_hi_val : (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
                                + cb3 * 8) : ZMod p).val = 16 - S := by
    rw [show (16 - (cb0 + cb1 * ((2 : ℕ) : ZMod p) + cb2 * ((4 : ℕ) : ZMod p)
              + cb3 * 8) : ZMod p) = (((16 - S) : ℕ) : ZMod p) from by
      rw [h_inner_eq, Nat.cast_sub (by omega : S ≤ 16)]; push_cast; ring]
    exact ZMod.val_natCast_of_lt (by omega)
  rw [h_inner_val] at lt_ll0 lt_ll1 lt_ll2 lt_ll3
  rw [h_inner_hi_val] at lt_lh0 lt_lh1 lt_lh2 lt_lh3
  have h_total_val : (cb0 + cb1 * (2 : ZMod p) + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32).val
                      = S + 48 := by
    rw [h_total_eq]; exact ZMod.val_natCast_of_lt (by omega)
  rw [h_total_val]
  have hdvd : v0123.val ∣ 65536 := by rw [h_v_val]; exact ⟨N, h_MN.symm⟩
  have hpos : 0 < v0123.val := by rw [h_v_val]; exact h_M_pos
  have h_b0' := cancel_mul_65536_poly hdvd hpos h_b0_dec
  have h_b1' := cancel_mul_65536_poly hdvd hpos h_b1_dec
  have h_b2' := cancel_mul_65536_poly hdvd hpos h_b2_dec
  have h_b3' := cancel_mul_65536_poly hdvd hpos h_b3_dec
  rw [h_v_val] at h_b0' h_b1' h_b2' h_b3'
  rw [show (2 : ℕ) ^ (S + 48) = N * 2 ^ 48 from by rw [pow_add, h_N_eq]]
  have h_div_eq : (65536 : ℕ) / M = N := by
    rw [← h_MN]; exact Nat.mul_div_cancel_left N h_M_pos
  rw [h_div_eq] at h_b0' h_b1' h_b2' h_b3'
  have h_lt_ll0 : ll0.val < N := by rw [h_N_eq]; exact lt_ll0
  have h_lt_ll1 : ll1.val < N := by rw [h_N_eq]; exact lt_ll1
  have h_lt_ll2 : ll2.val < N := by rw [h_N_eq]; exact lt_ll2
  have h_lt_ll3 : ll3.val < N := by rw [h_N_eq]; exact lt_ll3
  have h_lt_lh0 : hl0.val < M := by rw [h_M_eq]; exact lt_lh0
  have h_lt_lh1 : hl1.val < M := by rw [h_M_eq]; exact lt_lh1
  have h_lt_lh2 : hl2.val < M := by rw [h_M_eq]; exact lt_lh2
  have h_lt_lh3 : hl3.val < M := by rw [h_M_eq]; exact lt_lh3
  exact srl_within_byte_shift_3_poly M N h_MN h_M_pos h_v_val
    h_lt_ll0 h_lt_ll1 h_lt_ll2 h_lt_ll3 h_lt_lh0 h_lt_lh1 h_lt_lh2 h_lt_lh3
    h_b0' h_b1' h_b2' h_b3'

end srl_close_wrappers

end ShiftRight
