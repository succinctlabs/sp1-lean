import SP1Foundations
import SP1Operations.Operation.MulOperation.Operation
import SP1Operations.Operation.U16toU8OperationSafe
import SP1Operations.Operation.U16MSBOperation

namespace MulOperation

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.style.setOption false
-- Imbalanced goal tree: proof applies tactics per-focused-case.
set_option linter.style.multiGoal false

section field_operations

lemma div_mod_decomposition {a b c : Fin KB} :
  a < 256 → c.val < 2130706433 / 256 → (a = b - c * 256 ↔ a = b % 256 ∧ c = b / 256) := by
  intro ub_a ub_c
  constructor
  · intro eq_a
    simp [Fin.lt_def, Fin.ext_iff] at *
    have lb_b : c * 256 ≤ b := by
      by_contra lb_b
      simp [Fin.lt_def, Fin.sub_def, Fin.mul_def] at *
      rw [Nat.mod_eq_of_lt (a := (c : ℕ) * 256) (by omega)] at eq_a lb_b
      omega
    rw [Fin.sub_val_of_le lb_b] at eq_a
    simp [Fin.mul_def] at eq_a
    rw [Nat.mod_eq_of_lt (by omega)] at eq_a
    omega
  · intro ⟨eq_a, eq_c⟩
    simp_all
    have := Nat.div_add_mod b.val 256
    symm; rw [sub_eq_iff_eq_add]; symm
    rw [mul_comm, add_comm]
    simp [Fin.ext_iff, Fin.mul_def, Fin.add_def, Fin.mod_def]
    omega

end field_operations

section core_mul

@[grind ->]
lemma le_two_prod {a b : Fin KB} (ha : a.val < 256) (hb : b.val < 256) :
  a.val * b.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

lemma mod_add_split {a b c d n : ℕ} : a % n = c % n → b % n = d % n → (a + b) % n = (c + d) % n := by
  iterate 2 rw [Nat.add_mod_eq_sub]; simp_all

lemma mod_mul_split {a b c d n : ℕ} : a % n = c % n → b % n = d % n → (a * b) % n = (c * d) % n := by
  rw [Nat.mul_mod]; simp_all

lemma mod_add_mod_zero {a b n : ℕ} : 0 < n → b % n = 0 → (a + b) % n = a % n := by
  intro hn hb
  rw [Nat.add_mod_eq_sub]; simp_all
  rw [if_pos] <;> [ simp; apply Nat.mod_lt _ hn ]

set_option hygiene false in
open Lean Elab Tactic in
elab "resolve_decomposition" locs:ident* : tactic => do
  let name (loc : Ident) : Ident × Ident × Nat × Ident :=
    if let pref :: [suff] := (loc.getId.toString.split (·='_')).toList
    then (
      mkIdent (Name.mkSimple (pref.toString ++ suff)),
      mkIdent (Name.mkSimple (pref.toString ++ "c" ++ suff.drop 1)),
      suff.drop 1 |>.toNat!,
      mkIdent (Name.mkSimple suff.toString)
    )
    else default
  for loc in locs do
  let (name₁, name₂, num, suff) := name loc
  let numStx := Syntax.mkNatLit num
  let numPredStx := Syntax.mkNatLit num.pred
  let cNumStx := mkIdent (Name.mkSimple s!"c{suff.getId.toString.drop 1}")
  let term ← if num = 0
             then `(cp bw cw $numStx (of_decide_eq_true (Eq.refl true)))
             else `(cp bw cw $numStx (of_decide_eq_true (Eq.refl true)) + carry[$numPredStx])
  evalTactic <|
    ←`(tactic|(
        obtain ⟨$name₁, $name₂⟩ : prod[$numStx] = ($term) % 256 ∧ carry[$numStx] = ($term) / 256
          := (div_mod_decomposition $suff (by dsimp
                                              rw [show 8323072 = (8323072 : Fin KB).1 from rfl, Fin.val_fin_lt]
                                              apply lt_trans $cNumStx (by decide))).1 $loc
      ))

set_option maxHeartbeats 100000000 in

-- very deep mul-constraint unfolding
set_option maxRecDepth 200000 in
lemma core_mul
  (b : BWord (Fin KB))
  (c : BWord (Fin KB))
  (isU64_b : b.isU64)
  (isU64_c : c.isU64)
  (sgn_b sgn_c : Bool)
  (prod carry : BDWord (Fin KB)) :
  let bw := b.extend sgn_b
  let cw := c.extend sgn_c
  prod[0] = cp bw cw 0 (by decide) - carry[0] * 256 →
  prod[1] = cp bw cw 1 (by decide) + carry[0] - carry[1] * 256 →
  prod[2] = cp bw cw 2 (by decide) + carry[1] - carry[2] * 256 →
  prod[3] = cp bw cw 3 (by decide) + carry[2] - carry[3] * 256 →
  prod[4] = cp bw cw 4 (by decide) + carry[3] - carry[4] * 256 →
  prod[5] = cp bw cw 5 (by decide) + carry[4] - carry[5] * 256 →
  prod[6] = cp bw cw 6 (by decide) + carry[5] - carry[6] * 256 →
  prod[7] = cp bw cw 7 (by decide) + carry[6] - carry[7] * 256 →
  prod[8] = cp bw cw 8 (by decide) + carry[7] - carry[8] * 256 →
  prod[9] = cp bw cw 9 (by decide) + carry[8] - carry[9] * 256 →
  prod[10] = cp bw cw 10 (by decide) + carry[9] - carry[10] * 256 →
  prod[11] = cp bw cw 11 (by decide) + carry[10] - carry[11] * 256 →
  prod[12] = cp bw cw 12 (by decide) + carry[11] - carry[12] * 256 →
  prod[13] = cp bw cw 13 (by decide) + carry[12] - carry[13] * 256 →
  prod[14] = cp bw cw 14 (by decide) + carry[13] - carry[14] * 256 →
  prod[15] = cp bw cw 15 (by decide) + carry[14] - carry[15] * 256 →
  carry[0] < 65536 → carry[1] < 65536 → carry[2] < 65536 → carry[3] < 65536 →
  carry[4] < 65536 → carry[5] < 65536 → carry[6] < 65536 → carry[7] < 65536 →
  carry[8] < 65536 → carry[9] < 65536 → carry[10] < 65536 → carry[11] < 65536 →
  carry[12] < 65536 → carry[13] < 65536 → carry[14] < 65536 → carry[15] < 65536 →
  prod[0] < 256 → prod[1] < 256 → prod[2] < 256 → prod[3] < 256 →
  prod[4] < 256 → prod[5] < 256 → prod[6] < 256 → prod[7] < 256 →
  prod[8] < 256 → prod[9] < 256 → prod[10] < 256 → prod[11] < 256 →
  prod[12] < 256 → prod[13] < 256 → prod[14] < 256 → prod[15] < 256 →
    prod.toBitVec128 = bw.toBitVec128 * cw.toBitVec128 := by
  intro bw cw
        eq_p00 eq_p01 eq_p02 eq_p03 eq_p04 eq_p05 eq_p06 eq_p07
        eq_p08 eq_p09 eq_p10 eq_p11 eq_p12 eq_p13 eq_p14 eq_p15
        c00 c01 c02 c03 c04 c05 c06 c07 c08 c09 c10 c11 c12 c13 c14 c15
        p00 p01 p02 p03 p04 p05 p06 p07 p08 p09 p10 p11 p12 p13 p14 p15
  have isU128_bw : bw.isU128 := BWord.extend_U64_U128 isU64_b sgn_b
  have isU128_cw : cw.isU128 := BWord.extend_U64_U128 isU64_c sgn_c
  apply BDWord.lt_cases_of_isU128 at isU128_bw
  apply BDWord.lt_cases_of_isU128 at isU128_cw
  obtain ⟨bw00, bw01, bw02, bw03, bw04, bw05, bw06, bw07, bw08, bw09, bw10, bw11, bw12, bw13, bw14, bw15⟩ := isU128_bw
  obtain ⟨cw00, cw01, cw02, cw03, cw04, cw05, cw06, cw07, cw08, cw09, cw10, cw11, cw12, cw13, cw14, cw15⟩ := isU128_cw
  resolve_decomposition eq_p00 eq_p01 eq_p02 eq_p03
                        eq_p04 eq_p05 eq_p06 eq_p07
                        eq_p08 eq_p09 eq_p10 eq_p11
                        eq_p12 eq_p13 eq_p14 eq_p15
  have ⟨lt_cp00, lt_cp01, lt_cp02, lt_cp03, lt_cp04, lt_cp05, lt_cp06, lt_cp07,
         lt_cp08, lt_cp09, lt_cp10, lt_cp11, lt_cp12, lt_cp13, lt_cp14, lt_cp15⟩ :
    (cp bw cw 00 (by decide)).val ≤ 01 * 65025 ∧
    (cp bw cw 01 (by decide)).val ≤ 02 * 65025 ∧
    (cp bw cw 02 (by decide)).val ≤ 03 * 65025 ∧
    (cp bw cw 03 (by decide)).val ≤ 04 * 65025 ∧
    (cp bw cw 04 (by decide)).val ≤ 05 * 65025 ∧
    (cp bw cw 05 (by decide)).val ≤ 06 * 65025 ∧
    (cp bw cw 06 (by decide)).val ≤ 07 * 65025 ∧
    (cp bw cw 07 (by decide)).val ≤ 08 * 65025 ∧
    (cp bw cw 08 (by decide)).val ≤ 09 * 65025 ∧
    (cp bw cw 09 (by decide)).val ≤ 10 * 65025 ∧
    (cp bw cw 10 (by decide)).val ≤ 11 * 65025 ∧
    (cp bw cw 11 (by decide)).val ≤ 12 * 65025 ∧
    (cp bw cw 12 (by decide)).val ≤ 13 * 65025 ∧
    (cp bw cw 13 (by decide)).val ≤ 14 * 65025 ∧
    (cp bw cw 14 (by decide)).val ≤ 15 * 65025 ∧
    (cp bw cw 15 (by decide)).val ≤ 16 * 65025
      := by
    clear *- bw00 bw01 bw02 bw03 bw04 bw05 bw06 bw07 bw08 bw09 bw10 bw11 bw12 bw13 bw14 bw15
             cw00 cw01 cw02 cw03 cw04 cw05 cw06 cw07 cw08 cw09 cw10 cw11 cw12 cw13 cw14 cw15
    simp [cp, Vector.ofFn, Vector.get, Fin.val_mul, Fin.val_add]
    grind (ematch := 2048) (splits := 128)
  conv => lhs; simp [BDWord.toBitVec128, BDWord.toNat]
  simp [eqp00, eqp01, eqp02, eqp03, eqp04, eqp05, eqp06, eqp07, eqp08, eqp09, eqp10, eqp11, eqp12, eqp13, eqp14, eqp15,
        eqc00, eqc01, eqc02, eqc03, eqc04, eqc05, eqc06, eqc07, eqc08, eqc09, eqc10, eqc11, eqc12, eqc13, eqc14, eqc15, Fin.val_add]
  clear eqp00 eqp01 eqp02 eqp03 eqp04 eqp05 eqp06 eqp07 eqp08 eqp09 eqp10 eqp11 eqp12 eqp13 eqp14 eqp15
  clear eqc00 eqc01 eqc02 eqc03 eqc04 eqc05 eqc06 eqc07 eqc08 eqc09 eqc10 eqc11 eqc12 eqc13 eqc14 eqc15
  clear p00 p01 p02 p03 p04 p05 p06 p07 p08 p09 p10 p11 p12 p13 p14 p15
  clear c00 c01 c02 c03 c04 c05 c06 c07 c08 c09 c10 c11 c12 c13 c14 c15
  iterate 15 rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
  clear lt_cp00 lt_cp01 lt_cp02 lt_cp03 lt_cp04 lt_cp05 lt_cp06 lt_cp07 lt_cp08 lt_cp09 lt_cp10 lt_cp11 lt_cp12 lt_cp13 lt_cp14 lt_cp15
  have joins : forall (i : Fin 16) (a b : ℕ), a % (256 ^ i.val) + (b + a / (256 ^ i.val)) % 256 * (256 ^ i.val) = (a + b * (256 ^ i.val)) % (256 ^ (i.val + 1)) := by
    clear *-; intro i a b; fin_cases i <;> norm_num <;> omega
  have divs : forall (i : Fin 16) (a b : ℕ), (a + b / (256 ^ i.val)) / 256 = (b + a * (256 ^ i.val)) / (256 ^ (i.val + 1)) := by
    clear *-; intro i a b; fin_cases i <;> norm_num <;> omega
  have j1 := joins 1; have j2 := joins 2; have j3 := joins 3
  have j4 := joins 4; have j5 := joins 5; have j6 := joins 6; have j7 := joins 7;
  have j8 := joins 8; have j9 := joins 9; have j10 := joins 10; have j11 := joins 11;
  have j12 := joins 12; have j13 := joins 13; have j14 := joins 14; have j15 := joins 15;
  have d1 := divs 1; have d2 := divs 2; have d3 := divs 3
  have d4 := divs 4; have d5 := divs 5; have d6 := divs 6; have d7 := divs 7;
  have d8 := divs 8; have d9 := divs 9; have d10 := divs 10; have d11 := divs 11;
  have d12 := divs 12; have d13 := divs 13; have d14 := divs 14; have d15 := divs 15;
  simp at *
  rw [j1, d1, j2, d2, j3, d3, j4, d4, j5, d5, j6, d6, j7, d7, j8, d8,
      j9, d9, j10, d10, j11, d11, j12, d12, j13, d13, j14, d14, j15]
  clear j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 joins
  clear d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 divs
  simp [cp, Vector.ofFn, Vector.get] at *
  simp [Fin.val_add, Fin.val_mul]
  repeat rw [Nat.mod_eq_of_lt (b := 2130706433)]
  rw [← BitVec.toNat_inj, BitVec.toNat_ofNat]
  repeat rw [BitVec.toNat_mul]
  rw [BDWord.toBitVec128_toNat (BWord.extend_U64_U128 isU64_b sgn_b)]
  rw [BDWord.toBitVec128_toNat (BWord.extend_U64_U128 isU64_c sgn_c)]
  subst bw cw
  simp_all [BWord.extend, BDWord.toNat]
  ring_nf
  rw [mod_add_mod_zero (b := _ * _ * 1780731860627700044767655233185921512125162448076065661987177973493530624 ) (by simp)]
  · repeat apply mod_add_split _ (by apply mod_mul_split (by rfl) (by simp))
    rfl
  · split_ifs <;> simp
  all_goals
    clear *- bw00 bw01 bw02 bw03 bw04 bw05 bw06 bw07 bw08 bw09 bw10 bw11 bw12 bw13 bw14 bw15
             cw00 cw01 cw02 cw03 cw04 cw05 cw06 cw07 cw08 cw09 cw10 cw11 cw12 cw13 cw14 cw15
    grind (ematch := 2048) (splits := 128)

set_option maxHeartbeats 100000000 in

-- very deep mul-constraint unfolding
set_option maxRecDepth 200000 in
lemma core_mulw
  (bw : BHWord (Fin KB))
  (cw : BHWord (Fin KB))
  (isU32_b : bw.isU32)
  (isU32_c : cw.isU32)
  (prod carry : BHWord (Fin KB)) :
  prod[0] = cp bw cw 0 (by decide) - carry[0] * 256 →
  prod[1] = cp bw cw 1 (by decide) + carry[0] - carry[1] * 256 →
  prod[2] = cp bw cw 2 (by decide) + carry[1] - carry[2] * 256 →
  prod[3] = cp bw cw 3 (by decide) + carry[2] - carry[3] * 256 →
  carry[0] < 65536 → carry[1] < 65536 → carry[2] < 65536 → carry[3] < 65536 →
  prod[0] < 256 → prod[1] < 256 → prod[2] < 256 → prod[3] < 256 →
    prod.toBitVec32 = bw.toBitVec32 * cw.toBitVec32 := by
  intro eq_p00 eq_p01 eq_p02 eq_p03 c00 c01 c02 c03 p00 p01 p02 p03
  obtain ⟨bw00, bw01, bw02, bw03⟩ := BHWord.lt_cases_of_isU32 isU32_b
  obtain ⟨cw00, cw01, cw02, cw03⟩ := BHWord.lt_cases_of_isU32 isU32_c
  resolve_decomposition eq_p00 eq_p01 eq_p02 eq_p03
  have ⟨lt_cp00, lt_cp01, lt_cp02, lt_cp03⟩ :
    (cp bw cw 00 (by decide)).val ≤ 01 * 65025 ∧
    (cp bw cw 01 (by decide)).val ≤ 02 * 65025 ∧
    (cp bw cw 02 (by decide)).val ≤ 03 * 65025 ∧
    (cp bw cw 03 (by decide)).val ≤ 04 * 65025
      := by
    clear *- bw00 bw01 bw02 bw03 cw00 cw01 cw02 cw03
    simp [cp, Vector.ofFn, Vector.get, Fin.val_mul, Fin.val_add]
    grind (ematch := 2048) (splits := 128)
  conv => lhs; simp [BHWord.toBitVec32, BHWord.toNat]
  simp [eqp00, eqp01, eqp02, eqp03, eqc00, eqc01, eqc02, eqc03, Fin.val_add]
  clear eqp00 eqp01 eqp02 eqp03 eqc00 eqc01 eqc02 eqc03
  clear p00 p01 p02 p03 c00 c01 c02 c03
  iterate 3 rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
  clear lt_cp00 lt_cp01 lt_cp02 lt_cp03
  have joins : forall (i : Fin 4) (a b : ℕ), a % (256 ^ i.val) + (b + a / (256 ^ i.val)) % 256 * (256 ^ i.val) = (a + b * (256 ^ i.val)) % (256 ^ (i.val + 1)) := by
    clear *-; intro i a b; fin_cases i <;> norm_num <;> omega
  have divs : forall (i : Fin 4) (a b : ℕ), (a + b / (256 ^ i.val)) / 256 = (b + a * (256 ^ i.val)) / (256 ^ (i.val + 1)) := by
    clear *-; intro i a b; fin_cases i <;> norm_num <;> omega
  have j1 := joins 1; have j2 := joins 2; have j3 := joins 3
  have d1 := divs 1; have d2 := divs 2; have d3 := divs 3
  simp at *
  rw [j1, d1, j2, d2, j3]
  clear j1 j2 j3 joins d1 d2 d3 divs
  simp [cp, Vector.ofFn, Vector.get] at *
  simp [Fin.val_add, Fin.val_mul]
  repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by clear eq_p00 eq_p01 eq_p02 eq_p03; grind)]
  rw [← BitVec.toNat_inj, BitVec.toNat_ofNat]
  repeat rw [BitVec.toNat_mul]
  rw [BHWord.toBitVec32_toNat isU32_b, BHWord.toBitVec32_toNat isU32_c]
  simp_all [BHWord.toNat]
  ring_nf; omega

end core_mul

section constraints

@[irreducible] def constraints {F : Type} [Field F]
  (a_word : (Word F))
  (b_word : (Word F))
  (c_word : (Word F))
  (cols : MulOperation F)
  (is_real : F)
  (is_mul : F)
  (is_mulh : F)
  (is_mulw : F)
  (is_mulhu : F)
  (is_mulhsu : F)
  : SP1ConstraintList F :=
  let ⟨⟨⟨[E0, E1, E2, E3, E4, E5, E6, E7]⟩, _⟩, CS0⟩ := U16toU8OperationSafe.constraints #v[b_word[0], b_word[1], b_word[2], b_word[3]] { low_bytes := #v[cols.b_lower_byte.low_bytes[0], cols.b_lower_byte.low_bytes[1], cols.b_lower_byte.low_bytes[2], cols.b_lower_byte.low_bytes[3]] } is_real
  let ⟨⟨⟨[E8, E9, E10, E11, E12, E13, E14, E15]⟩, _⟩, CS1⟩ := U16toU8OperationSafe.constraints #v[c_word[0], c_word[1], c_word[2], c_word[3]] { low_bytes := #v[cols.c_lower_byte.low_bytes[0], cols.c_lower_byte.low_bytes[1], cols.c_lower_byte.low_bytes[2], cols.c_lower_byte.low_bytes[3]] } is_real
  let CS2 : SP1ConstraintList F := U16MSBOperation.constraints a_word[1] { msb := cols.product_msb.msb } is_mulw
  let E16 : F := is_mulh + is_mulhsu
  let E17 : F := E16 * cols.b_msb
  let E18 : F := cols.b_sign_extend - E17
  let E19 : F := is_mulh * cols.c_msb
  let E20 : F := cols.c_sign_extend - E19
  let E21 : F := cols.b_sign_extend * 255
  let E22 : F := cols.c_sign_extend * 255
  let E23 : F := cols.b_sign_extend * 255
  let E24 : F := cols.c_sign_extend * 255
  let E25 : F := cols.b_sign_extend * 255
  let E26 : F := cols.c_sign_extend * 255
  let E27 : F := cols.b_sign_extend * 255
  let E28 : F := cols.c_sign_extend * 255
  let E29 : F := cols.b_sign_extend * 255
  let E30 : F := cols.c_sign_extend * 255
  let E31 : F := cols.b_sign_extend * 255
  let E32 : F := cols.c_sign_extend * 255
  let E33 : F := cols.b_sign_extend * 255
  let E34 : F := cols.c_sign_extend * 255
  let E35 : F := cols.b_sign_extend * 255
  let E36 : F := cols.c_sign_extend * 255
  let E37 : F := E0 * E8
  let E38 : F := 0 + E37
  let E39 : F := E0 * E9
  let E40 : F := 0 + E39
  let E41 : F := E0 * E10
  let E42 : F := 0 + E41
  let E43 : F := E0 * E11
  let E44 : F := 0 + E43
  let E45 : F := E0 * E12
  let E46 : F := 0 + E45
  let E47 : F := E0 * E13
  let E48 : F := 0 + E47
  let E49 : F := E0 * E14
  let E50 : F := 0 + E49
  let E51 : F := E0 * E15
  let E52 : F := 0 + E51
  let E53 : F := E0 * E22
  let E54 : F := 0 + E53
  let E55 : F := E0 * E24
  let E56 : F := 0 + E55
  let E57 : F := E0 * E26
  let E58 : F := 0 + E57
  let E59 : F := E0 * E28
  let E60 : F := 0 + E59
  let E61 : F := E0 * E30
  let E62 : F := 0 + E61
  let E63 : F := E0 * E32
  let E64 : F := 0 + E63
  let E65 : F := E0 * E34
  let E66 : F := 0 + E65
  let E67 : F := E0 * E36
  let E68 : F := 0 + E67
  let E69 : F := E1 * E8
  let E70 : F := E40 + E69
  let E71 : F := E1 * E9
  let E72 : F := E42 + E71
  let E73 : F := E1 * E10
  let E74 : F := E44 + E73
  let E75 : F := E1 * E11
  let E76 : F := E46 + E75
  let E77 : F := E1 * E12
  let E78 : F := E48 + E77
  let E79 : F := E1 * E13
  let E80 : F := E50 + E79
  let E81 : F := E1 * E14
  let E82 : F := E52 + E81
  let E83 : F := E1 * E15
  let E84 : F := E54 + E83
  let E85 : F := E1 * E22
  let E86 : F := E56 + E85
  let E87 : F := E1 * E24
  let E88 : F := E58 + E87
  let E89 : F := E1 * E26
  let E90 : F := E60 + E89
  let E91 : F := E1 * E28
  let E92 : F := E62 + E91
  let E93 : F := E1 * E30
  let E94 : F := E64 + E93
  let E95 : F := E1 * E32
  let E96 : F := E66 + E95
  let E97 : F := E1 * E34
  let E98 : F := E68 + E97
  let E99 : F := E2 * E8
  let E100 : F := E72 + E99
  let E101 : F := E2 * E9
  let E102 : F := E74 + E101
  let E103 : F := E2 * E10
  let E104 : F := E76 + E103
  let E105 : F := E2 * E11
  let E106 : F := E78 + E105
  let E107 : F := E2 * E12
  let E108 : F := E80 + E107
  let E109 : F := E2 * E13
  let E110 : F := E82 + E109
  let E111 : F := E2 * E14
  let E112 : F := E84 + E111
  let E113 : F := E2 * E15
  let E114 : F := E86 + E113
  let E115 : F := E2 * E22
  let E116 : F := E88 + E115
  let E117 : F := E2 * E24
  let E118 : F := E90 + E117
  let E119 : F := E2 * E26
  let E120 : F := E92 + E119
  let E121 : F := E2 * E28
  let E122 : F := E94 + E121
  let E123 : F := E2 * E30
  let E124 : F := E96 + E123
  let E125 : F := E2 * E32
  let E126 : F := E98 + E125
  let E127 : F := E3 * E8
  let E128 : F := E102 + E127
  let E129 : F := E3 * E9
  let E130 : F := E104 + E129
  let E131 : F := E3 * E10
  let E132 : F := E106 + E131
  let E133 : F := E3 * E11
  let E134 : F := E108 + E133
  let E135 : F := E3 * E12
  let E136 : F := E110 + E135
  let E137 : F := E3 * E13
  let E138 : F := E112 + E137
  let E139 : F := E3 * E14
  let E140 : F := E114 + E139
  let E141 : F := E3 * E15
  let E142 : F := E116 + E141
  let E143 : F := E3 * E22
  let E144 : F := E118 + E143
  let E145 : F := E3 * E24
  let E146 : F := E120 + E145
  let E147 : F := E3 * E26
  let E148 : F := E122 + E147
  let E149 : F := E3 * E28
  let E150 : F := E124 + E149
  let E151 : F := E3 * E30
  let E152 : F := E126 + E151
  let E153 : F := E4 * E8
  let E154 : F := E130 + E153
  let E155 : F := E4 * E9
  let E156 : F := E132 + E155
  let E157 : F := E4 * E10
  let E158 : F := E134 + E157
  let E159 : F := E4 * E11
  let E160 : F := E136 + E159
  let E161 : F := E4 * E12
  let E162 : F := E138 + E161
  let E163 : F := E4 * E13
  let E164 : F := E140 + E163
  let E165 : F := E4 * E14
  let E166 : F := E142 + E165
  let E167 : F := E4 * E15
  let E168 : F := E144 + E167
  let E169 : F := E4 * E22
  let E170 : F := E146 + E169
  let E171 : F := E4 * E24
  let E172 : F := E148 + E171
  let E173 : F := E4 * E26
  let E174 : F := E150 + E173
  let E175 : F := E4 * E28
  let E176 : F := E152 + E175
  let E177 : F := E5 * E8
  let E178 : F := E156 + E177
  let E179 : F := E5 * E9
  let E180 : F := E158 + E179
  let E181 : F := E5 * E10
  let E182 : F := E160 + E181
  let E183 : F := E5 * E11
  let E184 : F := E162 + E183
  let E185 : F := E5 * E12
  let E186 : F := E164 + E185
  let E187 : F := E5 * E13
  let E188 : F := E166 + E187
  let E189 : F := E5 * E14
  let E190 : F := E168 + E189
  let E191 : F := E5 * E15
  let E192 : F := E170 + E191
  let E193 : F := E5 * E22
  let E194 : F := E172 + E193
  let E195 : F := E5 * E24
  let E196 : F := E174 + E195
  let E197 : F := E5 * E26
  let E198 : F := E176 + E197
  let E199 : F := E6 * E8
  let E200 : F := E180 + E199
  let E201 : F := E6 * E9
  let E202 : F := E182 + E201
  let E203 : F := E6 * E10
  let E204 : F := E184 + E203
  let E205 : F := E6 * E11
  let E206 : F := E186 + E205
  let E207 : F := E6 * E12
  let E208 : F := E188 + E207
  let E209 : F := E6 * E13
  let E210 : F := E190 + E209
  let E211 : F := E6 * E14
  let E212 : F := E192 + E211
  let E213 : F := E6 * E15
  let E214 : F := E194 + E213
  let E215 : F := E6 * E22
  let E216 : F := E196 + E215
  let E217 : F := E6 * E24
  let E218 : F := E198 + E217
  let E219 : F := E7 * E8
  let E220 : F := E202 + E219
  let E221 : F := E7 * E9
  let E222 : F := E204 + E221
  let E223 : F := E7 * E10
  let E224 : F := E206 + E223
  let E225 : F := E7 * E11
  let E226 : F := E208 + E225
  let E227 : F := E7 * E12
  let E228 : F := E210 + E227
  let E229 : F := E7 * E13
  let E230 : F := E212 + E229
  let E231 : F := E7 * E14
  let E232 : F := E214 + E231
  let E233 : F := E7 * E15
  let E234 : F := E216 + E233
  let E235 : F := E7 * E22
  let E236 : F := E218 + E235
  let E237 : F := E21 * E8
  let E238 : F := E222 + E237
  let E239 : F := E21 * E9
  let E240 : F := E224 + E239
  let E241 : F := E21 * E10
  let E242 : F := E226 + E241
  let E243 : F := E21 * E11
  let E244 : F := E228 + E243
  let E245 : F := E21 * E12
  let E246 : F := E230 + E245
  let E247 : F := E21 * E13
  let E248 : F := E232 + E247
  let E249 : F := E21 * E14
  let E250 : F := E234 + E249
  let E251 : F := E21 * E15
  let E252 : F := E236 + E251
  let E253 : F := E23 * E8
  let E254 : F := E240 + E253
  let E255 : F := E23 * E9
  let E256 : F := E242 + E255
  let E257 : F := E23 * E10
  let E258 : F := E244 + E257
  let E259 : F := E23 * E11
  let E260 : F := E246 + E259
  let E261 : F := E23 * E12
  let E262 : F := E248 + E261
  let E263 : F := E23 * E13
  let E264 : F := E250 + E263
  let E265 : F := E23 * E14
  let E266 : F := E252 + E265
  let E267 : F := E25 * E8
  let E268 : F := E256 + E267
  let E269 : F := E25 * E9
  let E270 : F := E258 + E269
  let E271 : F := E25 * E10
  let E272 : F := E260 + E271
  let E273 : F := E25 * E11
  let E274 : F := E262 + E273
  let E275 : F := E25 * E12
  let E276 : F := E264 + E275
  let E277 : F := E25 * E13
  let E278 : F := E266 + E277
  let E279 : F := E27 * E8
  let E280 : F := E270 + E279
  let E281 : F := E27 * E9
  let E282 : F := E272 + E281
  let E283 : F := E27 * E10
  let E284 : F := E274 + E283
  let E285 : F := E27 * E11
  let E286 : F := E276 + E285
  let E287 : F := E27 * E12
  let E288 : F := E278 + E287
  let E289 : F := E29 * E8
  let E290 : F := E282 + E289
  let E291 : F := E29 * E9
  let E292 : F := E284 + E291
  let E293 : F := E29 * E10
  let E294 : F := E286 + E293
  let E295 : F := E29 * E11
  let E296 : F := E288 + E295
  let E297 : F := E31 * E8
  let E298 : F := E292 + E297
  let E299 : F := E31 * E9
  let E300 : F := E294 + E299
  let E301 : F := E31 * E10
  let E302 : F := E296 + E301
  let E303 : F := E33 * E8
  let E304 : F := E300 + E303
  let E305 : F := E33 * E9
  let E306 : F := E302 + E305
  let E307 : F := E35 * E8
  let E308 : F := E306 + E307
  let E309 : F := cols.carry[0] * 256
  let E310 : F := E38 - E309
  let E311 : F := cols.product[0] - E310
  let E312 : F := is_real * E311
  let E313 : F := E70 + cols.carry[0]
  let E314 : F := cols.carry[1] * 256
  let E315 : F := E313 - E314
  let E316 : F := cols.product[1] - E315
  let E317 : F := is_real * E316
  let E318 : F := E100 + cols.carry[1]
  let E319 : F := cols.carry[2] * 256
  let E320 : F := E318 - E319
  let E321 : F := cols.product[2] - E320
  let E322 : F := is_real * E321
  let E323 : F := E128 + cols.carry[2]
  let E324 : F := cols.carry[3] * 256
  let E325 : F := E323 - E324
  let E326 : F := cols.product[3] - E325
  let E327 : F := is_real * E326
  let E328 : F := E154 + cols.carry[3]
  let E329 : F := cols.carry[4] * 256
  let E330 : F := E328 - E329
  let E331 : F := cols.product[4] - E330
  let E332 : F := is_real * E331
  let E333 : F := E178 + cols.carry[4]
  let E334 : F := cols.carry[5] * 256
  let E335 : F := E333 - E334
  let E336 : F := cols.product[5] - E335
  let E337 : F := is_real * E336
  let E338 : F := E200 + cols.carry[5]
  let E339 : F := cols.carry[6] * 256
  let E340 : F := E338 - E339
  let E341 : F := cols.product[6] - E340
  let E342 : F := is_real * E341
  let E343 : F := E220 + cols.carry[6]
  let E344 : F := cols.carry[7] * 256
  let E345 : F := E343 - E344
  let E346 : F := cols.product[7] - E345
  let E347 : F := is_real * E346
  let E348 : F := E238 + cols.carry[7]
  let E349 : F := cols.carry[8] * 256
  let E350 : F := E348 - E349
  let E351 : F := cols.product[8] - E350
  let E352 : F := is_real * E351
  let E353 : F := E254 + cols.carry[8]
  let E354 : F := cols.carry[9] * 256
  let E355 : F := E353 - E354
  let E356 : F := cols.product[9] - E355
  let E357 : F := is_real * E356
  let E358 : F := E268 + cols.carry[9]
  let E359 : F := cols.carry[10] * 256
  let E360 : F := E358 - E359
  let E361 : F := cols.product[10] - E360
  let E362 : F := is_real * E361
  let E363 : F := E280 + cols.carry[10]
  let E364 : F := cols.carry[11] * 256
  let E365 : F := E363 - E364
  let E366 : F := cols.product[11] - E365
  let E367 : F := is_real * E366
  let E368 : F := E290 + cols.carry[11]
  let E369 : F := cols.carry[12] * 256
  let E370 : F := E368 - E369
  let E371 : F := cols.product[12] - E370
  let E372 : F := is_real * E371
  let E373 : F := E298 + cols.carry[12]
  let E374 : F := cols.carry[13] * 256
  let E375 : F := E373 - E374
  let E376 : F := cols.product[13] - E375
  let E377 : F := is_real * E376
  let E378 : F := E304 + cols.carry[13]
  let E379 : F := cols.carry[14] * 256
  let E380 : F := E378 - E379
  let E381 : F := cols.product[14] - E380
  let E382 : F := is_real * E381
  let E383 : F := E308 + cols.carry[14]
  let E384 : F := cols.carry[15] * 256
  let E385 : F := E383 - E384
  let E386 : F := cols.product[15] - E385
  let E387 : F := is_real * E386
  let E388 : F := is_mulh + is_mulhu
  let E389 : F := E388 + is_mulhsu
  let E390 : F := cols.product[1] * 256
  let E391 : F := cols.product[0] + E390
  let E392 : F := E391 - a_word[0]
  let E393 : F := is_mulw * E392
  let E394 : F := cols.product[1] * 256
  let E395 : F := cols.product[0] + E394
  let E396 : F := E395 - a_word[0]
  let E397 : F := is_mul * E396
  let E398 : F := cols.product[9] * 256
  let E399 : F := cols.product[8] + E398
  let E400 : F := E399 - a_word[0]
  let E401 : F := E389 * E400
  let E402 : F := cols.product[3] * 256
  let E403 : F := cols.product[2] + E402
  let E404 : F := E403 - a_word[1]
  let E405 : F := is_mulw * E404
  let E406 : F := cols.product[3] * 256
  let E407 : F := cols.product[2] + E406
  let E408 : F := E407 - a_word[1]
  let E409 : F := is_mul * E408
  let E410 : F := cols.product[11] * 256
  let E411 : F := cols.product[10] + E410
  let E412 : F := E411 - a_word[1]
  let E413 : F := E389 * E412
  let E414 : F := cols.product_msb.msb * 65535
  let E415 : F := E414 - a_word[2]
  let E416 : F := is_mulw * E415
  let E417 : F := cols.product[5] * 256
  let E418 : F := cols.product[4] + E417
  let E419 : F := E418 - a_word[2]
  let E420 : F := is_mul * E419
  let E421 : F := cols.product[13] * 256
  let E422 : F := cols.product[12] + E421
  let E423 : F := E422 - a_word[2]
  let E424 : F := E389 * E423
  let E425 : F := cols.product_msb.msb * 65535
  let E426 : F := E425 - a_word[3]
  let E427 : F := is_mulw * E426
  let E428 : F := cols.product[7] * 256
  let E429 : F := cols.product[6] + E428
  let E430 : F := E429 - a_word[3]
  let E431 : F := is_mul * E430
  let E432 : F := cols.product[15] * 256
  let E433 : F := cols.product[14] + E432
  let E434 : F := E433 - a_word[3]
  let E435 : F := E389 * E434
  let E436 : F := is_mul + is_mulh
  let E437 : F := E436 + is_mulhu
  let E438 : F := E437 + is_mulhsu
  let E439 : F := E438 + is_mulw
  let E440 : F := cols.b_msb - 1
  let E441 : F := cols.b_msb * E440
  let E442 : F := cols.c_msb - 1
  let E443 : F := cols.c_msb * E442
  let E444 : F := cols.b_sign_extend - 1
  let E445 : F := cols.b_sign_extend * E444
  let E446 : F := cols.c_sign_extend - 1
  let E447 : F := cols.c_sign_extend * E446
  let E448 : F := is_mul - 1
  let E449 : F := is_mul * E448
  let E450 : F := is_mulh - 1
  let E451 : F := is_mulh * E450
  let E452 : F := is_mulhu - 1
  let E453 : F := is_mulhu * E452
  let E454 : F := is_mulhsu - 1
  let E455 : F := is_mulhsu * E454
  let E456 : F := is_mulw - 1
  let E457 : F := is_mulw * E456
  let E458 : F := E439 - 1
  let E459 : F := E439 * E458
  let E460 : F := is_real - 1
  let E461 : F := is_real * E460
  let E462 : F := cols.b_msb - 1
  let E463 : F := cols.b_sign_extend * E462
  let E464 : F := cols.c_msb - 1
  let E465 : F := cols.c_sign_extend * E464
  CS0 ++ CS1 ++ CS2 ++ [
    (.send (.byte (ByteOpcode.ofNat 5) cols.b_msb E7 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 5) cols.c_msb E15 0) is_real),
    (.assertZero E18),
    (.assertZero E20),
    (.assertZero E312),
    (.assertZero E317),
    (.assertZero E322),
    (.assertZero E327),
    (.assertZero E332),
    (.assertZero E337),
    (.assertZero E342),
    (.assertZero E347),
    (.assertZero E352),
    (.assertZero E357),
    (.assertZero E362),
    (.assertZero E367),
    (.assertZero E372),
    (.assertZero E377),
    (.assertZero E382),
    (.assertZero E387),
    (.assertZero E393),
    (.assertZero E397),
    (.assertZero E401),
    (.assertZero E405),
    (.assertZero E409),
    (.assertZero E413),
    (.assertZero E416),
    (.assertZero E420),
    (.assertZero E424),
    (.assertZero E427),
    (.assertZero E431),
    (.assertZero E435),
    (.assertZero E441),
    (.assertZero E443),
    (.assertZero E445),
    (.assertZero E447),
    (.assertZero E449),
    (.assertZero E451),
    (.assertZero E453),
    (.assertZero E455),
    (.assertZero E457),
    (.assertZero E459),
    (.assertZero E461),
    (.assertZero E463),
    (.assertZero E465),
    (.send (.byte (ByteOpcode.ofNat 6) cols.carry[0] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.carry[1] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.carry[2] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.carry[3] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.carry[4] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.carry[5] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.carry[6] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.carry[7] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.carry[8] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.carry[9] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.carry[10] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.carry[11] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.carry[12] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.carry[13] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.carry[14] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.carry[15] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 cols.product[0] cols.product[1]) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 cols.product[2] cols.product[3]) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 cols.product[4] cols.product[5]) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 cols.product[6] cols.product[7]) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 cols.product[8] cols.product[9]) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 cols.product[10] cols.product[11]) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 cols.product[12] cols.product[13]) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 cols.product[14] cols.product[15]) is_real),
  ]

end constraints

set_option maxHeartbeats 1000000 in
-- Polymorphic `constraints` adds defEq overhead when specializing at `Fin KB`.
lemma allHold_constraints_iff_is_real
  (aw : (Word (Fin KB)))
  (bw : (Word (Fin KB)))
  (cw : (Word (Fin KB)))
  (cols : MulOperation (Fin KB))
  (is_mul : (Fin KB))
  (is_mulh : (Fin KB))
  (is_mulw : (Fin KB))
  (is_mulhu : (Fin KB))
  (is_mulhsu : (Fin KB)) :
  List.Forall SP1Constraint.toProp (constraints aw bw cw cols 1 is_mul is_mulh is_mulw is_mulhu is_mulhsu) ↔
    have ⟨bbw, U16_b⟩ := U16toU8OperationSafe.constraints #v[bw[0], bw[1], bw[2], bw[3]] { low_bytes := #v[cols.b_lower_byte.low_bytes[0], cols.b_lower_byte.low_bytes[1], cols.b_lower_byte.low_bytes[2], cols.b_lower_byte.low_bytes[3]] } 1
    have ⟨cbw, U16_c⟩ := U16toU8OperationSafe.constraints #v[cw[0], cw[1], cw[2], cw[3]] { low_bytes := #v[cols.c_lower_byte.low_bytes[0], cols.c_lower_byte.low_bytes[1], cols.c_lower_byte.low_bytes[2], cols.c_lower_byte.low_bytes[3]] } 1
    let bbwe : Vector (Fin KB) 16 := #v[bbw[0], bbw[1], bbw[2], bbw[3], bbw[4], bbw[5], bbw[6], bbw[7], cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255]
    let cbwe : Vector (Fin KB) 16 := #v[cbw[0], cbw[1], cbw[2], cbw[3], cbw[4], cbw[5], cbw[6], cbw[7], cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255]
    List.Forall SP1Constraint.toProp U16_b ∧
    List.Forall SP1Constraint.toProp U16_c ∧
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints aw[1] cols.product_msb is_mulw) ∧
    ((cols.b_msb < 256 ∧ bbw[7] < 256) ∧ (cols.b_msb = 0 ∨ cols.b_msb = 1) ∧ (cols.b_msb = 1 ↔ (128 : Fin KB) ≤ bbw[7])) ∧
    ((cols.c_msb < 256 ∧ cbw[7] < 256) ∧ (cols.c_msb = 0 ∨ cols.c_msb = 1) ∧ (cols.c_msb = 1 ↔ (128 : Fin KB) ≤ cbw[7])) ∧
    cols.b_sign_extend = (is_mulh + is_mulhsu) * cols.b_msb ∧
    cols.c_sign_extend = is_mulh * cols.c_msb ∧
    cols.product[0] = cp bbwe cbwe 0 (by omega) - cols.carry[0] * 256 ∧
    cols.product[1] = cp bbwe cbwe 1 (by omega) + cols.carry[0] - cols.carry[1] * 256 ∧
    cols.product[2] = cp bbwe cbwe 2 (by omega) + cols.carry[1] - cols.carry[2] * 256 ∧
    cols.product[3] = cp bbwe cbwe 3 (by omega) + cols.carry[2] - cols.carry[3] * 256 ∧
    cols.product[4] = cp bbwe cbwe 4 (by omega) + cols.carry[3] - cols.carry[4] * 256 ∧
    cols.product[5] = cp bbwe cbwe 5 (by omega) + cols.carry[4] - cols.carry[5] * 256 ∧
    cols.product[6] = cp bbwe cbwe 6 (by omega) + cols.carry[5] - cols.carry[6] * 256 ∧
    cols.product[7] = cp bbwe cbwe 7 (by omega) + cols.carry[6] - cols.carry[7] * 256 ∧
    cols.product[8] = cp bbwe cbwe 8 (by omega) + cols.carry[7] - cols.carry[8] * 256 ∧
    cols.product[9] = cp bbwe cbwe 9 (by omega) + cols.carry[8] - cols.carry[9] * 256 ∧
    cols.product[10] = cp bbwe cbwe 10 (by omega) + cols.carry[9] - cols.carry[10] * 256 ∧
    cols.product[11] = cp bbwe cbwe 11 (by omega) + cols.carry[10] - cols.carry[11] * 256 ∧
    cols.product[12] = cp bbwe cbwe 12 (by omega) + cols.carry[11] - cols.carry[12] * 256 ∧
    cols.product[13] = cp bbwe cbwe 13 (by omega) + cols.carry[12] - cols.carry[13] * 256 ∧
    cols.product[14] = cp bbwe cbwe 14 (by omega) + cols.carry[13] - cols.carry[14] * 256 ∧
    cols.product[15] = cp bbwe cbwe 15 (by omega) + cols.carry[14] - cols.carry[15] * 256 ∧
    (is_mulw = 0 ∨ aw[0] = cols.product[0] + cols.product[1] * 256) ∧
    (is_mul = 0 ∨ aw[0] = cols.product[0] + cols.product[1] * 256) ∧
    (is_mulh + is_mulhu + is_mulhsu = 0 ∨ aw[0] = cols.product[8] + cols.product[9] * 256) ∧
    (is_mulw = 0 ∨ aw[1] = cols.product[2] + cols.product[3] * 256) ∧
    (is_mul = 0 ∨ aw[1] = cols.product[2] + cols.product[3] * 256) ∧
    (is_mulh + is_mulhu + is_mulhsu = 0 ∨ aw[1] = cols.product[10] + cols.product[11] * 256) ∧
    (is_mulw = 0 ∨ aw[2] = cols.product_msb.msb * 65535) ∧
    (is_mul = 0 ∨ aw[2] = cols.product[4] + cols.product[5] * 256) ∧
    (is_mulh + is_mulhu + is_mulhsu = 0 ∨ aw[2] = cols.product[12] + cols.product[13] * 256) ∧
    (is_mulw = 0 ∨ aw[3] = cols.product_msb.msb * 65535) ∧
    (is_mul = 0 ∨ aw[3] = cols.product[6] + cols.product[7] * 256) ∧
    (is_mulh + is_mulhu + is_mulhsu = 0 ∨ aw[3] = cols.product[14] + cols.product[15] * 256) ∧
    (cols.b_msb = 0 ∨ cols.b_msb = 1) ∧
    (cols.c_msb = 0 ∨ cols.c_msb = 1) ∧
    (cols.b_sign_extend = 0 ∨ cols.b_sign_extend = 1) ∧
    (cols.c_sign_extend = 0 ∨ cols.c_sign_extend = 1) ∧
    (is_mul = 0 ∨ is_mul = 1) ∧
    (is_mulh = 0 ∨ is_mulh = 1) ∧
    (is_mulhu = 0 ∨ is_mulhu = 1) ∧
    (is_mulhsu = 0 ∨ is_mulhsu = 1) ∧
    (is_mulw = 0 ∨ is_mulw = 1) ∧
    (is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw = 0 ∨ is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw = 1) ∧
    (cols.b_sign_extend = 0 ∨ cols.b_msb = 1) ∧ (cols.c_sign_extend = 0 ∨ cols.c_msb = 1) ∧
    cols.carry[0].val < 65536 ∧
    cols.carry[1].val < 65536 ∧
    cols.carry[2].val < 65536 ∧
    cols.carry[3].val < 65536 ∧
    cols.carry[4].val < 65536 ∧
    cols.carry[5].val < 65536 ∧
    cols.carry[6].val < 65536 ∧
    cols.carry[7].val < 65536 ∧
    cols.carry[8].val < 65536 ∧
    cols.carry[9].val < 65536 ∧
    cols.carry[10].val < 65536 ∧
    cols.carry[11].val < 65536 ∧
    cols.carry[12].val < 65536 ∧
    cols.carry[13].val < 65536 ∧
    cols.carry[14].val < 65536 ∧
    cols.carry[15].val < 65536 ∧
    cols.product[0] < 256 ∧ cols.product[1] < 256 ∧
    cols.product[2] < 256 ∧ cols.product[3] < 256 ∧
    cols.product[4] < 256 ∧ cols.product[5] < 256 ∧
    cols.product[6] < 256 ∧ cols.product[7] < 256 ∧
    cols.product[8] < 256 ∧ cols.product[9] < 256 ∧
    cols.product[10] < 256 ∧ cols.product[11] < 256 ∧
    cols.product[12] < 256 ∧ cols.product[13] < 256 ∧
    cols.product[14] < 256 ∧ cols.product[15] < 256
  := by
    simp [constraints]
    split; case _ res_b b0 b1 b2 b3 b4 b5 b6 b7 size_b U16_b eq_b =>
      split; case _ res_c c0 c1 c2 c3 c4 c5 c6 c7 size_c U16_c eq_c =>
        rw [eq_b, eq_c]
        simp [sub_eq_zero, cp, Vector.ofFn, and_assoc]
        repeat rw [eq_comm (a := (_ : Fin KB) + _ * 256)]
        repeat rw [eq_comm (a := cols.product_msb.msb * 65535)]
        simp_all

section opcodes

lemma single_op : List.Forall SP1Constraint.toProp (constraints aw bw cw cols 1 is_mul is_mulh is_mulw is_mulhu is_mulhsu) →
  (is_mul = 1 → is_mulh = 0 ∧ is_mulw = 0 ∧ is_mulhu = 0 ∧ is_mulhsu = 0) ∧
  (is_mulh = 1 → is_mul = 0 ∧ is_mulw = 0 ∧ is_mulhu = 0 ∧ is_mulhsu = 0) ∧
  (is_mulw = 1 → is_mul = 0 ∧ is_mulh = 0 ∧ is_mulhu = 0 ∧ is_mulhsu = 0) ∧
  (is_mulhu = 1 → is_mul = 0 ∧ is_mulh = 0 ∧ is_mulw = 0 ∧ is_mulhsu = 0) ∧
  (is_mulhsu = 1 → is_mul = 0 ∧ is_mulh = 0 ∧ is_mulw = 0 ∧ is_mulhu = 0)
   := by
  intro cstrs
  simp [allHold_constraints_iff_is_real] at cstrs
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _,
           _, _, _, _, _, _, _, _, _, _, _, _, _,
           _, _, _, _, _, _, _, _, _, _, _, _, _,
           b_mul, b_mulh, b_mulw, b_mulhu, b_mulhsu, one_of_ops, rest⟩ := cstrs
  clear *- b_mul b_mulh b_mulw b_mulhu b_mulhsu one_of_ops
  split_ands <;> intro is_one <;> simp_all <;> aesop

end opcodes

section mul

lemma spec.mul {aw bw cw cols is_mul is_mulh is_mulw is_mulhu is_mulhsu}
  (isU64_bw : bw.isU64)
  (isU64_cw : cw.isU64)
  (cstrs : List.Forall SP1Constraint.toProp (constraints aw bw cw cols 1 is_mul is_mulh is_mulw is_mulhu is_mulhsu)) :
  is_mul = 1 →
    aw.isU64 ∧ aw.toBitVec64 = execute_MUL_pure bw.toBitVec64 cw.toBitVec64 .MUL
    := by
  intro h_one
  have ⟨sop1, sop2, sop3, sop4, sop5⟩ := single_op cstrs
  simp_all [allHold_constraints_iff_is_real, -h_one]
  set bbw := (U16toU8OperationSafe.constraints #v[bw[0], bw[1], bw[2], bw[3]] { low_bytes := #v[cols.b_lower_byte.low_bytes[0], cols.b_lower_byte.low_bytes[1], cols.b_lower_byte.low_bytes[2], cols.b_lower_byte.low_bytes[3]] } 1).1
  set U16_b := (U16toU8OperationSafe.constraints #v[bw[0], bw[1], bw[2], bw[3]] { low_bytes := #v[cols.b_lower_byte.low_bytes[0], cols.b_lower_byte.low_bytes[1], cols.b_lower_byte.low_bytes[2], cols.b_lower_byte.low_bytes[3]] } 1).2
  set cbw := (U16toU8OperationSafe.constraints #v[cw[0], cw[1], cw[2], cw[3]] { low_bytes := #v[cols.c_lower_byte.low_bytes[0], cols.c_lower_byte.low_bytes[1], cols.c_lower_byte.low_bytes[2], cols.c_lower_byte.low_bytes[3]] } 1).1
  set U16_c := (U16toU8OperationSafe.constraints #v[cw[0], cw[1], cw[2], cw[3]] { low_bytes := #v[cols.c_lower_byte.low_bytes[0], cols.c_lower_byte.low_bytes[1], cols.c_lower_byte.low_bytes[2], cols.c_lower_byte.low_bytes[3]] } 1).2
  set bbwe : Vector (Fin KB) 16 := #v[bbw[0], bbw[1], bbw[2], bbw[3], bbw[4], bbw[5], bbw[6], bbw[7], cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255]
  set cbwe : Vector (Fin KB) 16 := #v[cbw[0], cbw[1], cbw[2], cbw[3], cbw[4], cbw[5], cbw[6], cbw[7], cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255]
  obtain ⟨u16_b_cstrs, u16_c_cstrs, _, _, _, _, _, p0, p1, p2, p3, p4, p5, p6,
           p7, p8, p9, p10, p11, p12, p13, p14, p15, _, _, _, _, _,
           _, _, _, _, _, _, _, _, _, _, _, _, _, _,
           _, _, _, _, _, c0, c1, c2, c3, c4, c5, c6, c7, c8,
           c9, c10, c11, c12, c13, c14, c15, pp0, pp1, pp2, pp3, pp4, pp5, pp6,
           pp7, pp8, pp9, pp10, pp11, pp12, pp13, pp14, pp15⟩ := cstrs
  simp_all [-p0, -p1, -p2, -p3, -p4, -p5, -p6, -p7, -p8, -p9, -p10, -p11, -p12, -p13, -p14, -p15]
  have eq_aw : aw = BWord.toWord (BDWord.low (cols.product : BDWord (Fin KB))) := by
    rw [BDWord.low, BWord.toWord, ← Word.eq_pointwise]
    simp_all
  have eq_bbw : bbw = bw.toBWord := by exact (U16toU8OperationSafe.spec.return u16_b_cstrs)
  have eq_cbw : cbw = cw.toBWord := by exact (U16toU8OperationSafe.spec.return u16_c_cstrs)
  have eq_bbwe : bbwe = BWord.extend bbw false := by simp [bbwe, BWord.extend]; assumption
  have eq_cbwe : cbwe = BWord.extend cbw false := by simp [cbwe, BWord.extend]; assumption
  have isU64_bbw : BWord.isU64 bbw := by rw [eq_bbw]; apply bw.toBWord_toU64 isU64_bw
  have isU64_cbw : BWord.isU64 cbw := by rw [eq_cbw]; apply cw.toBWord_toU64 isU64_cw
  simp_all [-eq_bbw, -eq_cbw, -p0, -p1, -p2, -p3, -p4, -p5, -p6, -p7, -p8, -p9, -p10, -p11, -p12, -p13, -p14, -p15]
  simp [eq_bbwe, eq_cbwe] at p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
  have mul_spec :=
    core_mul bbw cbw isU64_bbw isU64_cbw false false cols.product cols.carry
             p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
             c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15
             pp0 pp1 pp2 pp3 pp4 pp5 pp6 pp7 pp8 pp9 pp10 pp11 pp12 pp13 pp14 pp15
  rw [exec_MUL_pure_bv_to_bw _ _ .MUL isU64_bw isU64_cw]
  simp [execute_MUL_pure_bw, -BitVec.extractLsb]
  rw [← eq_bbw, ← eq_cbw, ← mul_spec]
  have isU128_prod : BDWord.isU128 cols.product := by
    clear *- pp0 pp1 pp2 pp3 pp4 pp5 pp6 pp7 pp8 pp9 pp10 pp11 pp12 pp13 pp14 pp15
    apply BDWord.isU128_of_cases <;> omega
  have : (BDWord.low cols.product).isU64 := BDWord.isU128_low_isU64 isU128_prod
  have is_U64_aw : (BDWord.low cols.product).toWord.isU64 := by
    apply BWord.toWord_U64; apply BDWord.isU128_low_isU64 isU128_prod
  rw [BWord.toWord_toBitVec64 this]
  constructor
  · assumption
  · apply BDWord.low_as_extract
    apply BDWord.isU128_of_cases <;> assumption

end mul

section mulh

lemma spec.mulh {aw bw cw cols is_mul is_mulh is_mulw is_mulhu is_mulhsu}
  (isU64_bw : bw.isU64)
  (isU64_cw : cw.isU64)
  (cstrs : List.Forall SP1Constraint.toProp (constraints aw bw cw cols 1 is_mul is_mulh is_mulw is_mulhu is_mulhsu)) :
  is_mulh = 1 →
    aw.isU64 ∧ aw.toBitVec64 = execute_MUL_pure bw.toBitVec64 cw.toBitVec64 .MULH
    := by
  intro h_one
  have ⟨sop1, sop2, sop3, sop4, sop5⟩ := single_op cstrs
  simp_all [allHold_constraints_iff_is_real, -h_one]
  set bbw := (U16toU8OperationSafe.constraints #v[bw[0], bw[1], bw[2], bw[3]] { low_bytes := #v[cols.b_lower_byte.low_bytes[0], cols.b_lower_byte.low_bytes[1], cols.b_lower_byte.low_bytes[2], cols.b_lower_byte.low_bytes[3]] } 1).1
  set U16_b := (U16toU8OperationSafe.constraints #v[bw[0], bw[1], bw[2], bw[3]] { low_bytes := #v[cols.b_lower_byte.low_bytes[0], cols.b_lower_byte.low_bytes[1], cols.b_lower_byte.low_bytes[2], cols.b_lower_byte.low_bytes[3]] } 1).2
  set cbw := (U16toU8OperationSafe.constraints #v[cw[0], cw[1], cw[2], cw[3]] { low_bytes := #v[cols.c_lower_byte.low_bytes[0], cols.c_lower_byte.low_bytes[1], cols.c_lower_byte.low_bytes[2], cols.c_lower_byte.low_bytes[3]] } 1).1
  set U16_c := (U16toU8OperationSafe.constraints #v[cw[0], cw[1], cw[2], cw[3]] { low_bytes := #v[cols.c_lower_byte.low_bytes[0], cols.c_lower_byte.low_bytes[1], cols.c_lower_byte.low_bytes[2], cols.c_lower_byte.low_bytes[3]] } 1).2
  set bbwe : Vector (Fin KB) 16 := #v[bbw[0], bbw[1], bbw[2], bbw[3], bbw[4], bbw[5], bbw[6], bbw[7], cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255]
  set cbwe : Vector (Fin KB) 16 := #v[cbw[0], cbw[1], cbw[2], cbw[3], cbw[4], cbw[5], cbw[6], cbw[7], cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255]
  obtain ⟨u16_b_cstrs, u16_c_cstrs, _, b_msb_ch, c_msb_ch, b_sgn_ext, c_sgn_ext, p0, p1, p2, p3, p4, p5, p6,
           p7, p8, p9, p10, p11, p12, p13, p14, p15, _, _, _, _, _,
           _, _, _, _, _, _, _, b_b_msb, b_c_msb, _, _, _, _, _,
           _, _, _, _, _, c0, c1, c2, c3, c4, c5, c6, c7, c8,
           c9, c10, c11, c12, c13, c14, c15, pp0, pp1, pp2, pp3, pp4, pp5, pp6,
           pp7, pp8, pp9, pp10, pp11, pp12, pp13, pp14, pp15⟩ := cstrs
  simp_all [-p0, -p1, -p2, -p3, -p4, -p5, -p6, -p7, -p8, -p9, -p10, -p11, -p12, -p13, -p14, -p15]
  have eq_aw : aw = BWord.toWord (BDWord.high (cols.product : BDWord (Fin KB))) := by
    rw [BDWord.high, BWord.toWord, ← Word.eq_pointwise]
    simp_all
  have eq_bbw : bbw = bw.toBWord := by
    exact (U16toU8OperationSafe.spec.return u16_b_cstrs)
  have eq_cbw : cbw = cw.toBWord := by
    exact (U16toU8OperationSafe.spec.return u16_c_cstrs)
  have msb_ext_b : cols.b_sign_extend * 255 = if BWord.isNegative bbw then 255 else 0 := by
    rw [b_sgn_ext]
    clear *- b_b_msb b_msb_ch
    unfold BWord.isNegative; split_ifs
    · suffices : cols.b_msb = 1 <;> simp_all
    · suffices : cols.b_msb = 0 <;> simp_all
  have msb_ext_c : cols.c_sign_extend * 255 = if BWord.isNegative cbw then 255 else 0 := by
    rw [c_sgn_ext]
    clear *- b_c_msb c_msb_ch
    unfold BWord.isNegative; split_ifs
    · suffices : cols.c_msb = 1 <;> simp_all
    · suffices : cols.c_msb = 0 <;> simp_all
  have eq_bbwe : bbwe = BWord.extend bbw true := by simp [bbwe, BWord.extend]; exact msb_ext_b
  have eq_cbwe : cbwe = BWord.extend cbw true := by simp [cbwe, BWord.extend]; exact msb_ext_c
  have isU64_bbw : BWord.isU64 bbw := by rw [eq_bbw]; apply bw.toBWord_toU64 isU64_bw
  have isU64_cbw : BWord.isU64 cbw := by rw [eq_cbw]; apply cw.toBWord_toU64 isU64_cw
  simp_all [-eq_bbw, -eq_cbw, -p0, -p1, -p2, -p3, -p4, -p5, -p6, -p7, -p8, -p9, -p10, -p11, -p12, -p13, -p14, -p15]
  simp [eq_bbwe, eq_cbwe] at p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
  have mul_spec :=
    core_mul bbw cbw isU64_bbw isU64_cbw true true cols.product cols.carry
             p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
             c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15
             pp0 pp1 pp2 pp3 pp4 pp5 pp6 pp7 pp8 pp9 pp10 pp11 pp12 pp13 pp14 pp15
  rw [exec_MUL_pure_bv_to_bw _ _ .MULH isU64_bw isU64_cw]
  simp [execute_MUL_pure_bw, -BitVec.extractLsb]
  rw [← eq_bbw, ← eq_cbw, ← mul_spec]
  have isU128_prod : BDWord.isU128 cols.product := by
    clear *- pp0 pp1 pp2 pp3 pp4 pp5 pp6 pp7 pp8 pp9 pp10 pp11 pp12 pp13 pp14 pp15
    apply BDWord.isU128_of_cases <;> omega
  have : (BDWord.high cols.product).isU64 := BDWord.isU128_high_isU64 isU128_prod
  have is_U64_aw : (BDWord.high cols.product).toWord.isU64 := by
    apply BWord.toWord_U64; apply BDWord.isU128_high_isU64 isU128_prod
  rw [BWord.toWord_toBitVec64 this]
  constructor
  · assumption
  · apply BDWord.high_as_extract
    apply BDWord.isU128_of_cases <;> assumption

end mulh

section mulhu

lemma spec.mulhu {aw bw cw cols is_mul is_mulh is_mulw is_mulhu is_mulhsu}
  (isU64_bw : bw.isU64)
  (isU64_cw : cw.isU64)
  (cstrs : List.Forall SP1Constraint.toProp (constraints aw bw cw cols 1 is_mul is_mulh is_mulw is_mulhu is_mulhsu)) :
  is_mulhu = 1 →
    aw.isU64 ∧ aw.toBitVec64 = execute_MUL_pure bw.toBitVec64 cw.toBitVec64 .MULHU
    := by
  intro h_one
  have ⟨sop1, sop2, sop3, sop4, sop5⟩ := single_op cstrs
  simp_all [allHold_constraints_iff_is_real, -h_one]
  set bbw := (U16toU8OperationSafe.constraints #v[bw[0], bw[1], bw[2], bw[3]] { low_bytes := #v[cols.b_lower_byte.low_bytes[0], cols.b_lower_byte.low_bytes[1], cols.b_lower_byte.low_bytes[2], cols.b_lower_byte.low_bytes[3]] } 1).1
  set U16_b := (U16toU8OperationSafe.constraints #v[bw[0], bw[1], bw[2], bw[3]] { low_bytes := #v[cols.b_lower_byte.low_bytes[0], cols.b_lower_byte.low_bytes[1], cols.b_lower_byte.low_bytes[2], cols.b_lower_byte.low_bytes[3]] } 1).2
  set cbw := (U16toU8OperationSafe.constraints #v[cw[0], cw[1], cw[2], cw[3]] { low_bytes := #v[cols.c_lower_byte.low_bytes[0], cols.c_lower_byte.low_bytes[1], cols.c_lower_byte.low_bytes[2], cols.c_lower_byte.low_bytes[3]] } 1).1
  set U16_c := (U16toU8OperationSafe.constraints #v[cw[0], cw[1], cw[2], cw[3]] { low_bytes := #v[cols.c_lower_byte.low_bytes[0], cols.c_lower_byte.low_bytes[1], cols.c_lower_byte.low_bytes[2], cols.c_lower_byte.low_bytes[3]] } 1).2
  set bbwe : Vector (Fin KB) 16 := #v[bbw[0], bbw[1], bbw[2], bbw[3], bbw[4], bbw[5], bbw[6], bbw[7], cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255]
  set cbwe : Vector (Fin KB) 16 := #v[cbw[0], cbw[1], cbw[2], cbw[3], cbw[4], cbw[5], cbw[6], cbw[7], cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255]
  obtain ⟨u16_b_cstrs, u16_c_cstrs, _, b_msb_ch, c_msb_ch, b_sgn_ext, c_sgn_ext, p0, p1, p2, p3, p4, p5, p6,
           p7, p8, p9, p10, p11, p12, p13, p14, p15, _, _, _, _, _,
           _, _, _, _, _, _, _, b_b_msb, b_c_msb, _, _, _, _, _,
           _, _, _, _, _, c0, c1, c2, c3, c4, c5, c6, c7, c8,
           c9, c10, c11, c12, c13, c14, c15, pp0, pp1, pp2, pp3, pp4, pp5, pp6,
           pp7, pp8, pp9, pp10, pp11, pp12, pp13, pp14, pp15⟩ := cstrs
  simp_all [-p0, -p1, -p2, -p3, -p4, -p5, -p6, -p7, -p8, -p9, -p10, -p11, -p12, -p13, -p14, -p15]
  have eq_aw : aw = BWord.toWord (BDWord.high (cols.product : BDWord (Fin KB))) := by
    rw [BDWord.high, BWord.toWord, ← Word.eq_pointwise]
    simp_all
  have eq_bbw : bbw = bw.toBWord := by
    exact (U16toU8OperationSafe.spec.return u16_b_cstrs)
  have eq_cbw : cbw = cw.toBWord := by
    exact (U16toU8OperationSafe.spec.return u16_c_cstrs)
  have eq_bbwe : bbwe = BWord.extend bbw false := by simp [bbwe, BWord.extend]; assumption
  have eq_cbwe : cbwe = BWord.extend cbw false := by simp [cbwe, BWord.extend]; assumption
  have isU64_bbw : BWord.isU64 bbw := by rw [eq_bbw]; apply bw.toBWord_toU64 isU64_bw
  have isU64_cbw : BWord.isU64 cbw := by rw [eq_cbw]; apply cw.toBWord_toU64 isU64_cw
  simp_all [-eq_bbw, -eq_cbw, -p0, -p1, -p2, -p3, -p4, -p5, -p6, -p7, -p8, -p9, -p10, -p11, -p12, -p13, -p14, -p15]
  simp [eq_bbwe, eq_cbwe] at p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
  have mul_spec :=
    core_mul bbw cbw isU64_bbw isU64_cbw false false cols.product cols.carry
             p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
             c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15
             pp0 pp1 pp2 pp3 pp4 pp5 pp6 pp7 pp8 pp9 pp10 pp11 pp12 pp13 pp14 pp15
  rw [exec_MUL_pure_bv_to_bw _ _ .MULHU isU64_bw isU64_cw]
  simp [execute_MUL_pure_bw, -BitVec.extractLsb]
  rw [← eq_bbw, ← eq_cbw, ← mul_spec]
  have isU128_prod : BDWord.isU128 cols.product := by
    clear *- pp0 pp1 pp2 pp3 pp4 pp5 pp6 pp7 pp8 pp9 pp10 pp11 pp12 pp13 pp14 pp15
    apply BDWord.isU128_of_cases <;> omega
  have : (BDWord.high cols.product).isU64 := BDWord.isU128_high_isU64 isU128_prod
  have is_U64_aw : (BDWord.high cols.product).toWord.isU64 := by
    apply BWord.toWord_U64; apply BDWord.isU128_high_isU64 isU128_prod
  rw [BWord.toWord_toBitVec64 this]
  constructor
  · assumption
  · apply BDWord.high_as_extract
    apply BDWord.isU128_of_cases <;> assumption

end mulhu

section mulhsu

lemma spec.mulhsu {aw bw cw cols is_mul is_mulh is_mulw is_mulhu is_mulhsu}
  (isU64_bw : bw.isU64)
  (isU64_cw : cw.isU64)
  (cstrs : List.Forall SP1Constraint.toProp (constraints aw bw cw cols 1 is_mul is_mulh is_mulw is_mulhu is_mulhsu)) :
  is_mulhsu = 1 →
    aw.isU64 ∧ aw.toBitVec64 = execute_MUL_pure bw.toBitVec64 cw.toBitVec64 .MULHSU
    := by
  intro h_one
  have ⟨sop1, sop2, sop3, sop4, sop5⟩ := single_op cstrs
  simp_all [allHold_constraints_iff_is_real, -h_one]
  set bbw := (U16toU8OperationSafe.constraints #v[bw[0], bw[1], bw[2], bw[3]] { low_bytes := #v[cols.b_lower_byte.low_bytes[0], cols.b_lower_byte.low_bytes[1], cols.b_lower_byte.low_bytes[2], cols.b_lower_byte.low_bytes[3]] } 1).1
  set U16_b := (U16toU8OperationSafe.constraints #v[bw[0], bw[1], bw[2], bw[3]] { low_bytes := #v[cols.b_lower_byte.low_bytes[0], cols.b_lower_byte.low_bytes[1], cols.b_lower_byte.low_bytes[2], cols.b_lower_byte.low_bytes[3]] } 1).2
  set cbw := (U16toU8OperationSafe.constraints #v[cw[0], cw[1], cw[2], cw[3]] { low_bytes := #v[cols.c_lower_byte.low_bytes[0], cols.c_lower_byte.low_bytes[1], cols.c_lower_byte.low_bytes[2], cols.c_lower_byte.low_bytes[3]] } 1).1
  set U16_c := (U16toU8OperationSafe.constraints #v[cw[0], cw[1], cw[2], cw[3]] { low_bytes := #v[cols.c_lower_byte.low_bytes[0], cols.c_lower_byte.low_bytes[1], cols.c_lower_byte.low_bytes[2], cols.c_lower_byte.low_bytes[3]] } 1).2
  set bbwe : Vector (Fin KB) 16 := #v[bbw[0], bbw[1], bbw[2], bbw[3], bbw[4], bbw[5], bbw[6], bbw[7], cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255]
  set cbwe : Vector (Fin KB) 16 := #v[cbw[0], cbw[1], cbw[2], cbw[3], cbw[4], cbw[5], cbw[6], cbw[7], cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255]
  obtain ⟨u16_b_cstrs, u16_c_cstrs, _, b_msb_ch, c_msb_ch, b_sgn_ext, c_sgn_ext, p0, p1, p2, p3, p4, p5, p6,
           p7, p8, p9, p10, p11, p12, p13, p14, p15, _, _, _, _, _,
           _, _, _, _, _, _, _, b_b_msb, b_c_msb, _, _, _, _, _,
           _, _, _, _, _, c0, c1, c2, c3, c4, c5, c6, c7, c8,
           c9, c10, c11, c12, c13, c14, c15, pp0, pp1, pp2, pp3, pp4, pp5, pp6,
           pp7, pp8, pp9, pp10, pp11, pp12, pp13, pp14, pp15⟩ := cstrs
  simp_all [-p0, -p1, -p2, -p3, -p4, -p5, -p6, -p7, -p8, -p9, -p10, -p11, -p12, -p13, -p14, -p15]
  have eq_aw : aw = BWord.toWord (BDWord.high (cols.product : BDWord (Fin KB))) := by
    rw [BDWord.high, BWord.toWord, ← Word.eq_pointwise]
    simp_all
  have eq_bbw : bbw = bw.toBWord := by
    exact (U16toU8OperationSafe.spec.return u16_b_cstrs)
  have eq_cbw : cbw = cw.toBWord := by
    exact (U16toU8OperationSafe.spec.return u16_c_cstrs)
  have msb_ext_b : cols.b_sign_extend * 255 = if BWord.isNegative bbw then 255 else 0 := by
    rw [b_sgn_ext]
    clear *- b_b_msb b_msb_ch
    unfold BWord.isNegative; split_ifs
    · suffices : cols.b_msb = 1 <;> simp_all
    · suffices : cols.b_msb = 0 <;> simp_all
  have eq_bbwe : bbwe = BWord.extend bbw true := by simp [bbwe, BWord.extend]; exact msb_ext_b
  have eq_cbwe : cbwe = BWord.extend cbw false := by simp [cbwe, BWord.extend]; assumption
  have isU64_bbw : BWord.isU64 bbw := by rw [eq_bbw]; apply bw.toBWord_toU64 isU64_bw
  have isU64_cbw : BWord.isU64 cbw := by rw [eq_cbw]; apply cw.toBWord_toU64 isU64_cw
  simp_all [-eq_bbw, -eq_cbw, -p0, -p1, -p2, -p3, -p4, -p5, -p6, -p7, -p8, -p9, -p10, -p11, -p12, -p13, -p14, -p15]
  simp [eq_bbwe, eq_cbwe] at p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
  have mul_spec :=
    core_mul bbw cbw isU64_bbw isU64_cbw true false cols.product cols.carry
             p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
             c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15
             pp0 pp1 pp2 pp3 pp4 pp5 pp6 pp7 pp8 pp9 pp10 pp11 pp12 pp13 pp14 pp15
  rw [exec_MUL_pure_bv_to_bw _ _ .MULHSU isU64_bw isU64_cw]
  simp [execute_MUL_pure_bw, -BitVec.extractLsb]
  rw [← eq_bbw, ← eq_cbw, ← mul_spec]
  have isU128_prod : BDWord.isU128 cols.product := by
    clear *- pp0 pp1 pp2 pp3 pp4 pp5 pp6 pp7 pp8 pp9 pp10 pp11 pp12 pp13 pp14 pp15
    apply BDWord.isU128_of_cases <;> omega
  have : (BDWord.high cols.product).isU64 := BDWord.isU128_high_isU64 isU128_prod
  have is_U64_aw : (BDWord.high cols.product).toWord.isU64 := by
    apply BWord.toWord_U64; apply BDWord.isU128_high_isU64 isU128_prod
  rw [BWord.toWord_toBitVec64 this]
  constructor
  · assumption
  · apply BDWord.high_as_extract
    apply BDWord.isU128_of_cases <;> assumption

end mulhsu

section mulw

lemma spec.mulw {aw bw cw cols is_mul is_mulh is_mulw is_mulhu is_mulhsu}
  (isU64_bw : bw.isU64)
  (isU64_cw : cw.isU64)
  (cstrs : List.Forall SP1Constraint.toProp (constraints aw bw cw cols 1 is_mul is_mulh is_mulw is_mulhu is_mulhsu)) :
  is_mulw = 1 →
    aw.isU64 ∧ aw.toBitVec64 = execute_MULW_pure bw.toBitVec64 cw.toBitVec64
    := by
  intro h_one
  have ⟨sop1, sop2, sop3, sop4, sop5⟩ := single_op cstrs
  simp_all [allHold_constraints_iff_is_real, -h_one]
  set bbw := (U16toU8OperationSafe.constraints #v[bw[0], bw[1], bw[2], bw[3]] { low_bytes := #v[cols.b_lower_byte.low_bytes[0], cols.b_lower_byte.low_bytes[1], cols.b_lower_byte.low_bytes[2], cols.b_lower_byte.low_bytes[3]] } 1).1
  set U16_b := (U16toU8OperationSafe.constraints #v[bw[0], bw[1], bw[2], bw[3]] { low_bytes := #v[cols.b_lower_byte.low_bytes[0], cols.b_lower_byte.low_bytes[1], cols.b_lower_byte.low_bytes[2], cols.b_lower_byte.low_bytes[3]] } 1).2
  set cbw := (U16toU8OperationSafe.constraints #v[cw[0], cw[1], cw[2], cw[3]] { low_bytes := #v[cols.c_lower_byte.low_bytes[0], cols.c_lower_byte.low_bytes[1], cols.c_lower_byte.low_bytes[2], cols.c_lower_byte.low_bytes[3]] } 1).1
  set U16_c := (U16toU8OperationSafe.constraints #v[cw[0], cw[1], cw[2], cw[3]] { low_bytes := #v[cols.c_lower_byte.low_bytes[0], cols.c_lower_byte.low_bytes[1], cols.c_lower_byte.low_bytes[2], cols.c_lower_byte.low_bytes[3]] } 1).2
  set bbwe : Vector (Fin KB) 16 := #v[bbw[0], bbw[1], bbw[2], bbw[3], bbw[4], bbw[5], bbw[6], bbw[7], cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255, cols.b_sign_extend * 255]
  set cbwe : Vector (Fin KB) 16 := #v[cbw[0], cbw[1], cbw[2], cbw[3], cbw[4], cbw[5], cbw[6], cbw[7], cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255, cols.c_sign_extend * 255]
  obtain ⟨u16_b_cstrs, u16_c_cstrs, u16_msb, _, _, _, _, p0, p1, p2, p3, p4, p5, p6,
           p7, p8, p9, p10, p11, p12, p13, p14, p15, aw0, _, _, aw1, _,
           _, aw2, _, _, aw3, _, _, _, _, _, _, _, _, _,
           _, _, _, _, _, c0, c1, c2, c3, c4, c5, c6, c7, c8,
           c9, c10, c11, c12, c13, c14, c15, pp0, pp1, pp2, pp3, pp4, pp5, pp6,
           pp7, pp8, pp9, pp10, pp11, pp12, pp13, pp14, pp15⟩ := cstrs
  clear p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
        c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15
        pp4 pp5 pp6 pp7 pp8 pp9 pp10 pp11 pp12 pp13 pp14 pp15
  simp_all [-p0, -p1, -p2, -p3]
  have eq_bbw : bbw = bw.toBWord := by exact (U16toU8OperationSafe.spec.return u16_b_cstrs)
  have eq_cbw : cbw = cw.toBWord := by exact (U16toU8OperationSafe.spec.return u16_c_cstrs)
  clear u16_b_cstrs u16_c_cstrs U16_b U16_c
  set hbw : BHWord (Fin KB) := #v[bbw[0], bbw[1], bbw[2], bbw[3]]
  set hcw : BHWord (Fin KB) := #v[cbw[0], cbw[1], cbw[2], cbw[3]]
  rcases bbw with ⟨bbw, lpb⟩
  rcases cbw with ⟨cbw, lpc⟩
  set ahw : BHWord (Fin KB) := #v[cols.product[0], cols.product[1], cols.product[2], cols.product[3]]
  have isU32_ahw : BHWord.isU32 ahw := by clear *- pp0 pp1 pp2 pp3; apply BHWord.isU32_of_cases <;> simp [ahw] <;> omega
  have eq_aw : aw = (BWord.toWord (ahw.extend true)) := by
    have isU32_awh : cols.product[2] + cols.product[3] * 256 < 65536 := by
      simp [Fin.lt_def, Fin.val_add, Fin.val_mul]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    have msb_spec := U16MSBOperation.spec isU32_awh u16_msb
    simp [← Word.eq_pointwise, aw0, aw1, aw2, aw3, BHWord.extend, ahw]
    simp [BWord.toWord, BHWord.isNegative, msb_spec]
    split_ifs with h h' h' <;> [ omega; (simp; apply h'); (simp; apply h); omega ]
    all_goals
      clear *- pp2 pp3 h h'
      simp [Fin.lt_def, Fin.le_def, Fin.val_add, Fin.val_mul] at *
      rw [Nat.mod_eq_of_lt (by omega)] at *
      omega
  have eq_hbw : hbw = bw.toBWord.low := by simp [hbw, ← eq_bbw, BWord.low]
  have eq_hcw : hcw = cw.toBWord.low := by simp [hcw, ← eq_cbw, BWord.low]
  rw [exec_MULW_pure_bv_to_bhw _ _ isU64_bw isU64_cw, execute_MULW_pure_bhw]
  rw [eq_aw, ← eq_hbw, ← eq_hcw]
  constructor
  · apply BWord.toWord_U64; apply BHWord.extend_U32_U64 isU32_ahw
  · rw [BWord.toWord_toBitVec64 (BHWord.extend_U32_U64 isU32_ahw true), BHWord.extend_true_is_signExtend isU32_ahw]
    simp [BitVec.extend]; congr
    have isU32_hbw : BHWord.isU32 hbw := by
      rw [eq_hbw]; apply BWord.isU64_low_isU32 _
      apply Word.toBWord_toU64 (by assumption)
    have isU32_hcw : BHWord.isU32 hcw := by
      rw [eq_hcw]; apply BWord.isU64_low_isU32 _
      apply Word.toBWord_toU64 (by assumption)
    have ⟨eq_cp0, eq_cp1, eq_cp2, eq_cp3⟩ :
          cp bbwe cbwe 0 (by decide) = cp hbw hcw 0 (by decide) ∧
          cp bbwe cbwe 1 (by decide) = cp hbw hcw 1 (by decide) ∧
          cp bbwe cbwe 2 (by decide) = cp hbw hcw 2 (by decide) ∧
          cp bbwe cbwe 3 (by decide) = cp hbw hcw 3 (by decide) := by
      simp [bbwe, cbwe, hbw, hcw]; clear *-
      split_ands <;> simp [cp, Vector.get_mk, Vector.ofFn]
    apply core_mulw (prod := #v[cols.product[0], cols.product[1], cols.product[2], cols.product[3]])
                    (carry := #v[cols.carry[0], cols.carry[1], cols.carry[2], cols.carry[3]])
                    hbw hcw isU32_hbw isU32_hcw p0 p1 p2 p3
    all_goals
      simp_all; try rw [Fin.lt_def]; try omega

end mulw

section gen

lemma spec.mul.gen {aw bw cw cols is_real is_mulh is_mulw is_mulhu is_mulhsu}
  (isU64_bw : bw.isU64)
  (isU64_cw : cw.isU64)
  (cstrs : List.Forall SP1Constraint.toProp (constraints aw bw cw cols is_real 1 is_mulh is_mulw is_mulhu is_mulhsu)) :
  is_real = 1 →
    aw.isU64 ∧ aw.toBitVec64 = execute_MUL_pure bw.toBitVec64 cw.toBitVec64 .MUL := by
  intro is_real; simp_all
  apply spec.mul isU64_bw isU64_cw cstrs (by simp)

lemma spec.mulh.gen {aw bw cw cols is_real is_mul is_mulw is_mulhu is_mulhsu}
  (isU64_bw : bw.isU64)
  (isU64_cw : cw.isU64)
  (cstrs : List.Forall SP1Constraint.toProp (constraints aw bw cw cols is_real is_mul is_mulh is_mulw is_mulhu is_mulhsu)) :
  is_real = 1 →
    (is_mulh = 1 → aw.isU64 ∧ aw.toBitVec64 = execute_MUL_pure bw.toBitVec64 cw.toBitVec64 .MULH) ∧
    (is_mulhu = 1 → aw.isU64 ∧ aw.toBitVec64 = execute_MUL_pure bw.toBitVec64 cw.toBitVec64 .MULHU) ∧
    (is_mulhsu = 1 → aw.isU64 ∧ aw.toBitVec64 = execute_MUL_pure bw.toBitVec64 cw.toBitVec64 .MULHSU) := by
  intro h_is_real; split_ands <;> intro h_op <;> simp_all
  · apply spec.mulh isU64_bw isU64_cw cstrs (by simp)
  · apply spec.mulhu isU64_bw isU64_cw cstrs (by simp)
  · apply spec.mulhsu isU64_bw isU64_cw cstrs (by simp)

end gen

section poly_helpers

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

/-- Helper: 4 boolean ZMod values summing to 0 in `ZMod p` are all zero.
Holds because the Nat-side sum is ≤ 4 < p, so the ZMod equality lifts
losslessly. The 15 contradiction cases (where at least one of a,b,c,d is
1) all reduce to `(k : ZMod p) = 0` for `k ∈ {1,2,3,4}` via
`linear_combination`, then `ZMod.val` injection + omega finishes. -/
private lemma four_bools_sum_zero
    {a b c d : ZMod p}
    (b_a : a = 0 ∨ a = 1) (b_b : b = 0 ∨ b = 1)
    (b_c : c = 0 ∨ c = 1) (b_d : d = 0 ∨ d = 1)
    (h_sum : a + b + c + d = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have hp_lt : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  haveI : NeZero p := ⟨by omega⟩
  have h2lt : (2 : ℕ) < p := by omega
  have h3lt : (3 : ℕ) < p := by omega
  have h4lt : (4 : ℕ) < p := by omega
  have h1_val : (1 : ZMod p).val = 1 := ZMod.val_one p
  have h2_val : (2 : ZMod p).val = 2 := ZMod.val_natCast_of_lt h2lt
  have h3_val : (3 : ZMod p).val = 3 := ZMod.val_natCast_of_lt h3lt
  have h4_val : (4 : ZMod p).val = 4 := ZMod.val_natCast_of_lt h4lt
  -- For k ∈ {1, 2, 3, 4}, `(k : ZMod p) ≠ 0`.
  have h1_ne : (1 : ZMod p) ≠ 0 := by
    intro h; have := congrArg ZMod.val h; rw [h1_val, ZMod.val_zero] at this; omega
  have h2_ne : (2 : ZMod p) ≠ 0 := by
    intro h; have := congrArg ZMod.val h; rw [h2_val, ZMod.val_zero] at this; omega
  have h3_ne : (3 : ZMod p) ≠ 0 := by
    intro h; have := congrArg ZMod.val h; rw [h3_val, ZMod.val_zero] at this; omega
  have h4_ne : (4 : ZMod p) ≠ 0 := by
    intro h; have := congrArg ZMod.val h; rw [h4_val, ZMod.val_zero] at this; omega
  rcases b_a with rfl | rfl <;> rcases b_b with rfl | rfl <;>
    rcases b_c with rfl | rfl <;> rcases b_d with rfl | rfl
  -- 16 cases: one passes (all zero), 15 contradict.
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact absurd (by linear_combination h_sum : (1 : ZMod p) = 0) h1_ne
  · exact absurd (by linear_combination h_sum : (1 : ZMod p) = 0) h1_ne
  · exact absurd (by linear_combination h_sum : (2 : ZMod p) = 0) h2_ne
  · exact absurd (by linear_combination h_sum : (1 : ZMod p) = 0) h1_ne
  · exact absurd (by linear_combination h_sum : (2 : ZMod p) = 0) h2_ne
  · exact absurd (by linear_combination h_sum : (2 : ZMod p) = 0) h2_ne
  · exact absurd (by linear_combination h_sum : (3 : ZMod p) = 0) h3_ne
  · exact absurd (by linear_combination h_sum : (1 : ZMod p) = 0) h1_ne
  · exact absurd (by linear_combination h_sum : (2 : ZMod p) = 0) h2_ne
  · exact absurd (by linear_combination h_sum : (2 : ZMod p) = 0) h2_ne
  · exact absurd (by linear_combination h_sum : (3 : ZMod p) = 0) h3_ne
  · exact absurd (by linear_combination h_sum : (2 : ZMod p) = 0) h2_ne
  · exact absurd (by linear_combination h_sum : (3 : ZMod p) = 0) h3_ne
  · exact absurd (by linear_combination h_sum : (3 : ZMod p) = 0) h3_ne
  · exact absurd (by linear_combination h_sum : (4 : ZMod p) = 0) h4_ne

/-- 5-arm boolean cascade: from `is_X = 1` for one variant plus the
`is_Y ∈ {0,1}` disjunctions for the other four and the specialized sum
constraint `sum = 1`, the other four flags must be 0. Mirrors
`Bitwise.single_op_poly` (3-arm version) extended to 5 arms by reducing
to `four_bools_sum_zero` via `linear_combination`. The chip-level proof
extracts `sum = 1` from `(sum_disj : sum = 0 ∨ sum = 1)` and the active
`is_X = 1` via separate `sum_eq_one_of_eq_one_*` helpers. -/
lemma single_op_poly
    {is_mul is_mulh is_mulw is_mulhu is_mulhsu : ZMod p}
    (b_mul : is_mul = 0 ∨ is_mul = 1)
    (b_mulh : is_mulh = 0 ∨ is_mulh = 1)
    (b_mulhu : is_mulhu = 0 ∨ is_mulhu = 1)
    (b_mulhsu : is_mulhsu = 0 ∨ is_mulhsu = 1)
    (b_mulw : is_mulw = 0 ∨ is_mulw = 1)
    (h_sum : is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw = 1) :
    (is_mul = 1 → is_mulh = 0 ∧ is_mulw = 0 ∧ is_mulhu = 0 ∧ is_mulhsu = 0) ∧
    (is_mulh = 1 → is_mul = 0 ∧ is_mulw = 0 ∧ is_mulhu = 0 ∧ is_mulhsu = 0) ∧
    (is_mulw = 1 → is_mul = 0 ∧ is_mulh = 0 ∧ is_mulhu = 0 ∧ is_mulhsu = 0) ∧
    (is_mulhu = 1 → is_mul = 0 ∧ is_mulh = 0 ∧ is_mulw = 0 ∧ is_mulhsu = 0) ∧
    (is_mulhsu = 1 → is_mul = 0 ∧ is_mulh = 0 ∧ is_mulw = 0 ∧ is_mulhu = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h_X
  · have ⟨h1, h2, h3, h4⟩ := four_bools_sum_zero b_mulh b_mulhu b_mulhsu b_mulw
      (by linear_combination h_sum - h_X)
    exact ⟨h1, h4, h2, h3⟩
  · have ⟨h1, h2, h3, h4⟩ := four_bools_sum_zero b_mul b_mulhu b_mulhsu b_mulw
      (by linear_combination h_sum - h_X)
    exact ⟨h1, h4, h2, h3⟩
  · have ⟨h1, h2, h3, h4⟩ := four_bools_sum_zero b_mul b_mulh b_mulhu b_mulhsu
      (by linear_combination h_sum - h_X)
    exact ⟨h1, h2, h3, h4⟩
  · have ⟨h1, h2, h3, h4⟩ := four_bools_sum_zero b_mul b_mulh b_mulhsu b_mulw
      (by linear_combination h_sum - h_X)
    exact ⟨h1, h2, h4, h3⟩
  · have ⟨h1, h2, h3, h4⟩ := four_bools_sum_zero b_mul b_mulh b_mulhu b_mulw
      (by linear_combination h_sum - h_X)
    exact ⟨h1, h2, h4, h3⟩

end poly_helpers

end MulOperation
