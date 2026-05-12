import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader
import SP1Chips.ShiftLeft.Constraints

namespace ShiftLeft

set_option linter.style.setOption false
-- Imbalanced goal tree: proof applies tactics per-focused-case.
set_option linter.style.multiGoal false
set_option maxHeartbeats 100000000

variable (Main : Vector (Fin KB) 65)
variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

def is_real : Prop := Main[62] = 1 ∨ Main[63] = 1

omit [Fact (2 ^ 17 < p)] in
@[simp] def is_real_poly (Main : Vector (ZMod p) 65) : Prop := Main[62] = 1 ∨ Main[63] = 1

section field_arithmetic

lemma cancel_mul_65536 {a b c x : Fin KB} (h_dvd : (x : ℕ) ∣ 65536) : a * x = b * 65536 + c * x → a = b * ((65536 : ℕ) / (x : ℕ)) + c
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

end field_arithmetic

section opcodes

@[simp] def is_sll := Main[62] = 1 ∧ Main[31] = 0
omit [Fact (2 ^ 17 < p)] in
@[simp] def is_sll_poly (Main : Vector (ZMod p) 65) := Main[62] = 1 ∧ Main[31] = 0

@[simp] def is_sllw := Main[63] = 1 ∧ Main[31] = 0
omit [Fact (2 ^ 17 < p)] in
@[simp] def is_sllw_poly (Main : Vector (ZMod p) 65) := Main[63] = 1 ∧ Main[31] = 0

@[simp] def is_slli := Main[62] = 1 ∧ Main[31] = 1
omit [Fact (2 ^ 17 < p)] in
@[simp] def is_slli_poly (Main : Vector (ZMod p) 65) := Main[62] = 1 ∧ Main[31] = 1

@[simp] def is_slliw := Main[63] = 1 ∧ Main[31] = 1
omit [Fact (2 ^ 17 < p)] in
@[simp] def is_slliw_poly (Main : Vector (ZMod p) 65) := Main[63] = 1 ∧ Main[31] = 1

lemma single_op : List.Forall SP1Constraint.toProp (constraints Main) →
  (Main[62] = 1 → Main[63] = 0) ∧
  (Main[63] = 1 → Main[62] = 0)
   := by
  intro cstrs
  simp [allHold_constraints_iff] at cstrs
  obtain ⟨h_msb, cpu, alu, one_of_ops, b_sll, b_sllw, rest⟩ := cstrs
  clear *- b_sll b_sllw one_of_ops
  aesop

end opcodes

section is_real

lemma sll_real : Main[62] = 1 → is_real Main := by simp [is_real]; aesop
omit [Fact (2 ^ 17 < p)] in
lemma sll_real_poly (Main : Vector (ZMod p) 65) : Main[62] = 1 → is_real_poly Main := by
  intro h; exact Or.inl h

lemma sllw_real : Main[63] = 1 → is_real Main := by simp [is_real]; aesop
omit [Fact (2 ^ 17 < p)] in
lemma sllw_real_poly (Main : Vector (ZMod p) 65) : Main[63] = 1 → is_real_poly Main := by
  intro h; exact Or.inr h

end is_real

section bounds

lemma bounds : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main →
  let imm := Main[31]
  Main[6] < 32 ∧ Main[14] < 32 ∧ (imm = 0 → Main[21] < 32) ∧ Main[3] < 65536 ∧
  Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] ∧
  Word.isU64 #v[Main[25], Main[26], Main[27], Main[28]] ∧
  (imm = 1 →
    (Main[21] = Main[25] ∧ Main[26] = 0 ∧ Main[27] = 0 ∧ Main[28] = 0 ∧
      ((Main[62] = 1 → Main[25] < 64) ∧
       (Main[63] = 1 → Main[25] < 32)))) ∧
  (Main[6] = 0 → Main[32] = 0 ∧ Main[33] = 0 ∧ Main[34] = 0 ∧ Main[35] = 0)
  := by
  intro cstrs real
  simp [allHold_constraints_iff] at cstrs
  obtain ⟨h_msb, cpu, alu, one_of_ops, b_sll, b_sllw, rest⟩ := cstrs
  clear h_msb cpu rest
  simp [is_real] at real
  rw [ALUTypeReader.allHold_constraints_iff_is_real (h_trusted := rfl)] at alu
  · obtain ⟨h1, h2, h3, _, h4, h5, b_imm, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := alu; simp_all
    by_cases sll : Main[62] = 0
    · by_cases sllw : Main[63] = 0
      · clear *- real sll sllw; aesop
      · have : Main[62] = 0 := by
          clear *- real b_sll b_sllw sll sllw one_of_ops
          aesop
        simp_all [Opcode.ofNat, Nat.beq, Nat.ble]
        split_ands
        · rcases b_imm <;> simp_all
        · rcases b_imm <;> simp_all
          apply Word.isU64_of_cases <;> simp; omega
        · aesop
        · intro h6; exact h18.1 (by have := h5.mpr h6; omega)
    · have : Main[63] = 0 := by
        clear *- real b_sll b_sllw sll one_of_ops
        aesop
      simp_all [Opcode.ofNat, Nat.beq, Nat.ble]
      split_ands
      · rcases b_imm <;> simp_all
      · rcases b_imm <;> simp_all
        apply Word.isU64_of_cases <;> simp; omega
      · aesop
      · intro h6; exact h18.1 (by have := h5.mpr h6; omega)
  · clear alu; aesop

end bounds

section operands

@[simp]
def sp1_op_a : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → BitVec 5 := by
  intro cstrs real
  refine BitVec.ofNatLT Main[6] ?_
  change Main[6] < 32
  have := bounds Main cstrs real
  tauto

@[simp]
def sp1_op_b : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → BitVec 5 := by
  intro cstrs real
  refine BitVec.ofNatLT Main[14] ?_
  change Main[14] < 32
  have := bounds Main cstrs real
  tauto

@[simp]
def sp1_op_c : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → Main[31] = 0 → BitVec 5 := by
  intro cstrs real imm
  refine BitVec.ofNatLT Main[21] ?_
  change Main[21] < 32
  have := bounds Main cstrs real
  tauto

@[simp]
def sp1_op_c_imm : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → Main[31] = 1 → Main[62] = 1 → BitVec 6 := by
  intro cstrs real imm nw
  refine BitVec.ofNatLT Main[21] ?_
  have ⟨_, _, _, _, _, _, h_imm, _⟩ := bounds Main cstrs real
  simp_all
  have ⟨_, _, _, _, _⟩ := h_imm
  tauto

@[simp]
def sp1_op_c_imm_w : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → Main[31] = 1 → Main[63] = 1 → BitVec 5 := by
  intro cstrs real imm nw
  refine BitVec.ofNatLT Main[21] ?_
  have ⟨_, _, _, _, _, _, h_imm, _⟩ := bounds Main cstrs real
  simp_all
  have ⟨_, _, _, _, _⟩ := h_imm
  tauto

end operands

end ShiftLeft
