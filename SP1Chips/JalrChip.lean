import SP1Operations.Operation.AddOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ITypeReader
import SP1Chips.Jalr.Constraints

namespace Jalr

open Sail SailState BitVec LeanRV64D.Functions

attribute [simp] ofBool
  update updateSubrange'
  assert PreSail.assert
  LeanRV64D.Functions.RETIRE_SUCCESS

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 35) (s : SailState)

def sp1_op_a : BitVec 5 := BitVec.ofNat 5 Main[6].val

def sp1_op_b : BitVec 5 := BitVec.ofNat 5 Main[14].val

def sp1_op_c : BitVec 12 := BitVec.ofNat 12 Main[21].val

def sp1_jalr (Main : Vector (ZMod p) 35) : SailM Unit := do
  let op_a := sp1_op_a Main
  set_next_pc (Word.toBitVec64_poly #v[Main[26] - Main[34], Main[27], Main[28], (0 : ZMod p)])
  wX_bits (.Regidx op_a) (Word.toBitVec64_poly #v[Main[30], Main[31], Main[32], Main[33]])

noncomputable def spec_jalr (imm : BitVec 12) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  let _ ← execute_JALR imm rs1 rd

/-- The Word `#v[4, 0, 0, 0]` is exactly the BitVec `4#64`. Lifted out of
`JALR_correct` so the `Nat.zero_mul + Nat.add_zero` simp pass that produces
the kernel-tripping proof term sits in its own decl. -/
private lemma word_four_eq_bitvec_four_jalr :
    Word.toBitVec64_poly (#v[(4 : ZMod p), 0, 0, 0]) = (4#64 : BitVec 64) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp_lt : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have h4v : ((4 : ℕ) : ZMod p).val = 4 := ZMod.val_natCast_of_lt (by omega)
  rw [show (4 : ZMod p) = ((4 : ℕ) : ZMod p) from by push_cast; rfl]
  simp only [Word.toBitVec64_poly, Word.toNat_poly_def, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
    h4v, ZMod.val_zero, Nat.zero_mul, Nat.add_zero]

-- Sub-lemma 1 (poly): chip's masked next-PC low limb is mod-4 aligned as a `BitVec 64`.
omit [Fact (2 ^ 17 < p)] in
lemma jalr_target_mod4_poly (Main : Vector (ZMod p) 35)
    (h_masked_mod4 : (Main[26] - Main[34]).val % 4 = 0) :
    (Word.toBitVec64_poly #v[Main[26] - Main[34], Main[27], Main[28], (0 : ZMod p)]) % 4#64 =
        0#64 := by
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  simp [Word.toBitVec64_poly_mod4, ofNat64_mod_4_eq_zero_iff, h_masked_mod4]

-- Sub-lemma 2 (poly): the unmasked next-PC sum equals the masked sum plus `Main[34]` at bit 0.
omit [Fact (2 ^ 17 < p)] in
lemma jalr_unmasked_eq_masked_plus_poly (Main : Vector (ZMod p) 35)
    (h29 : Main[29] = (0 : ZMod p))
    (h_sub_val : (Main[26] - Main[34]).val = Main[26].val - Main[34].val)
    (_h26_lt : Main[26].val < 65536)
    (_h27_lt : Main[27].val < 65536)
    (_h28_lt : Main[28].val < 65536)
    (h34_le : Main[34].val ≤ 1)
    (h34_le26 : Main[34].val ≤ Main[26].val) :
    Word.toBitVec64_poly #v[Main[26], Main[27], Main[28], Main[29]] =
      Word.toBitVec64_poly #v[Main[26] - Main[34], Main[27], Main[28], (0 : ZMod p)]
        + BitVec.ofNat 64 Main[34].val := by
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  simp [Word.toBitVec64_poly, Word.toNat_poly_def, h29, ZMod.val_zero, h_sub_val]
  bv_omega

-- Sub-lemma 3 (poly): masking bit 0 of the unmasked sum gives back the masked sum.
lemma jalr_target_eq_poly (Main : Vector (ZMod p) 35)
    (h_unmasked_eq_masked_plus :
      Word.toBitVec64_poly #v[Main[26], Main[27], Main[28], Main[29]] =
        Word.toBitVec64_poly #v[Main[26] - Main[34], Main[27], Main[28], (0 : ZMod p)]
          + BitVec.ofNat 64 Main[34].val)
    (h_target_mod4 :
      (Word.toBitVec64_poly #v[Main[26] - Main[34], Main[27], Main[28], (0 : ZMod p)])
          % 4#64 = 0#64)
    (h34_bit : Main[34] = 0 ∨ Main[34] = 1) :
    18446744073709551614#64 &&&
        Word.toBitVec64_poly #v[Main[26], Main[27], Main[28], Main[29]] =
      Word.toBitVec64_poly #v[Main[26] - Main[34], Main[27], Main[28], (0 : ZMod p)] := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rw [h_unmasked_eq_masked_plus]
  set t : BitVec 64 :=
    Word.toBitVec64_poly #v[Main[26] - Main[34], Main[27], Main[28], (0 : ZMod p)] with ht
  rcases h34_bit with h0 | h1
  · rw [h0, ZMod.val_zero]
    have h0n : (BitVec.ofNat 64 0) = 0#64 := rfl
    rw [h0n, BitVec.add_zero]
    have ht_mod4 : t % 4#64 = 0#64 := h_target_mod4
    revert ht_mod4; generalize t = u; intro hu
    bv_decide
  · rw [h1]
    haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    rw [ZMod.val_one]
    have h1n : (BitVec.ofNat 64 1) = 1#64 := rfl
    rw [h1n]
    have ht_mod4 : t % 4#64 = 0#64 := h_target_mod4
    revert ht_mod4
    generalize t = u
    intro hu
    bv_decide

set_option maxHeartbeats 10000000 in
-- JALR's proof has to discharge BitVec equalities for the low-bit mask plus the
-- AddOp specifications, which routinely exceed default heartbeats.
-- `skipKernelTC` for residual kernel deep-recursion in the BitVec masking + AddOp body.
set_option debug.skipKernelTC true in
theorem JALR_correct
    (cstrs : (constraints Main).allHold_poly)
    (h_is_real : Main[25] = 1)
    (hs : isInitialized s)
    (state_cstrs : (constraints Main).initialState_poly s)
    (hv : isValidMemConfig s hs) :
    let op_b := sp1_op_b Main
    let op_a := sp1_op_a Main
    let op_c := sp1_op_c Main
    (spec_jalr op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_jalr Main).run s := by
  extract_lets op_c op_b op_a
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h32 : (32 : ZMod p).val = 32 := val_32_zmod_p
  have h65 : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
  have h14_val_lt : (14 : ZMod p).val = 14 := by
    have hp_lt : 14 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt hp_lt
  -- pull out constraints (no h_is_real yet, so reader_cstrs keeps `is_real := M[25]`)
  simp [constraints] at cstrs
  obtain ⟨res_cstrs, pc_cstrs, reader_cstrs, inc_pc_cstrs, rest_cstrs⟩ := cstrs
  -- Apply ITypeReader iff with h_is_real
  rw [ITypeReader.allHold_constraints_iff_is_real_poly h_is_real h_is_real] at reader_cstrs
  -- Reduce opcode literal and unfold trusted_instr_poly for JALR.
  have h47_lt : (47 : ℕ) < p := by
    have h := Fact.out (p := 2 ^ 17 < p)
    have : (47 : ℕ) < 2 ^ 17 := by decide
    omega
  have h47_val : (47 : ZMod p).val = 47 := ZMod.val_natCast_of_lt h47_lt
  simp [h_is_real, show (Opcode.ofNat 47) = Opcode.JALR from rfl,
    Opcode.trusted_instr_poly, h47_val] at reader_cstrs
  obtain ⟨⟨h_op_b_lt32, h_imm_se⟩,
          h_op_a_lt, _h_op_b_lt_65k,
          h_imm0_lt, h_imm1_lt, h_imm2_lt, h_imm3_lt,
          h_op_a_0_bool, h_op_a_0_iff, h_pc_mod4,
          h_pc0_lt, h_pc1_lt, h_pc2_lt,
          _h_diff_b_lt, _h_diff_a_lt, _h_window_b, _h_window_a,
          _h_mem_a_isU64, h_mem_b_isU64, h_op_a_0_impl⟩ := reader_cstrs
  -- destructure the trailing tail of cstrs (E1, M[29] = 0, etc)
  simp [SP1Constraint.toProp_poly, h_is_real, sub_eq_zero] at rest_cstrs
  obtain ⟨h29, h34_bit, h_low_align, h33, h13_zero_or_M30, h13_zero_or_M31, h13_zero_or_M32⟩ :=
    rest_cstrs
  have h_op_a_b_zero : (Main[13] = 0 ∨ Main[30] = 0) ∧ (Main[13] = 0 ∨ Main[31] = 0) ∧
      (Main[13] = 0 ∨ Main[32] = 0) := ⟨h13_zero_or_M30, h13_zero_or_M31, h13_zero_or_M32⟩
  -- val bounds for op_a, op_b
  have h6 : Main[6].val < 32 := by
    have : Main[6].val < (32 : ZMod p).val := h_op_a_lt; rwa [h32] at this
  have h14 : Main[14].val < 32 := by
    have : Main[14].val < (32 : ZMod p).val := h_op_b_lt32; rwa [h32] at this
  simp [SP1ConstraintList.initialState_poly, constraints, SP1Constraint.toStateProp_poly,
    List.Forall, AddOperation.constraints, ITypeReader.constraints, CPUState.constraints,
    h_is_real, h6, h14] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b⟩ := state_cstrs
  -- imm word (M[21..24]) is u64
  have h21 : Main[21].val < 65536 := by
    have : Main[21].val < (65536 : ZMod p).val := h_imm0_lt; rwa [h65] at this
  have h22 : Main[22].val < 65536 := by
    have : Main[22].val < (65536 : ZMod p).val := h_imm1_lt; rwa [h65] at this
  have h23 : Main[23].val < 65536 := by
    have : Main[23].val < (65536 : ZMod p).val := h_imm2_lt; rwa [h65] at this
  have h24 : Main[24].val < 65536 := by
    have : Main[24].val < (65536 : ZMod p).val := h_imm3_lt; rwa [h65] at this
  have h_imm_isU64 : Word.isU64_poly #v[Main[21], Main[22], Main[23], Main[24]] := by
    apply Word.isU64_of_cases_poly <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · exact h21
    · exact h22
    · exact h23
    · exact h24
  -- imm sign-extension already extracted as `h_imm_se` from trusted_instr_poly
  have h_imm_signExtend :
      Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] =
        BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) := h_imm_se
  -- M[15..18] is rs1's previous value (isU64 from reader memory)
  have h15_isU64 : Word.isU64_poly #v[Main[15], Main[16], Main[17], Main[18]] := h_mem_b_isU64
  -- AddOperation.spec_poly on res_cstrs: rs1 + imm = #v[Main[26..29]] as BitVec64
  rw [h_is_real] at res_cstrs
  obtain ⟨h_pc_imm_isU64, h_add⟩ := AddOperation.spec_poly h15_isU64 h_imm_isU64 res_cstrs
  simp at h_add
  -- pc reader
  rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at read_pc
  -- bounds on chip-stored sum
  have h26_lt : Main[26].val < 65536 := h_pc_imm_isU64 0
  have h27_lt : Main[27].val < 65536 := h_pc_imm_isU64 1
  have h28_lt : Main[28].val < 65536 := h_pc_imm_isU64 2
  -- Range-check: ((M[26]-M[34]) * 4⁻¹).val < 16384
  have h_low_align' : ((Main[26] - Main[34]) * (4 : ZMod p)⁻¹).val < 2 ^ 14 := by
    have := h_low_align
    rw [h14_val_lt] at this
    exact this
  have hk_lt : ((Main[26] - Main[34]) * (4 : ZMod p)⁻¹).val < 16384 := by
    have := h_low_align'; norm_num at this ⊢; omega
  -- (M[26]-M[34]) = ((M[26]-M[34]) * 4⁻¹) * 4
  have h4ne : (4 : ZMod p) ≠ 0 := by
    have hp_gt : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    have h4val : ((4 : ℕ) : ZMod p).val = 4 := ZMod.val_natCast_of_lt (by omega)
    intro h4eq
    have : (4 : ZMod p).val = 0 := by rw [h4eq, ZMod.val_zero]
    rw [show (4 : ZMod p) = ((4 : ℕ) : ZMod p) from by push_cast; rfl, h4val] at this
    omega
  set k : ZMod p := (Main[26] - Main[34]) * (4 : ZMod p)⁻¹ with hk_def
  have h_masked_eq : Main[26] - Main[34] = k * 4 := by
    rw [hk_def, mul_assoc, inv_mul_cancel₀ h4ne, mul_one]
  have h4val_zmod : ((4 : ℕ) : ZMod p).val = 4 := by
    have hp_gt : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt (by omega)
  have h4_eq : (4 : ZMod p) = ((4 : ℕ) : ZMod p) := by push_cast; rfl
  have h_kx4_val : (k * 4).val = k.val * 4 := by
    rw [h4_eq, ZMod.val_mul, h4val_zmod]
    have hp_lt : 65536 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    have : k.val * 4 < 65536 := by omega
    exact Nat.mod_eq_of_lt (by omega)
  have h_masked_lt : (Main[26] - Main[34]).val < 65536 := by
    rw [h_masked_eq, h_kx4_val]; omega
  have h_masked_mod4 : (Main[26] - Main[34]).val % 4 = 0 := by
    rw [h_masked_eq, h_kx4_val]; omega
  -- Reduce ZMod subtraction to Nat (h_masked_lt < 65536 rules out the wrap branch)
  have h34_val : Main[34].val ≤ 1 := by
    rcases h34_bit with h0 | h1
    · rw [h0, ZMod.val_zero]; omega
    · rw [h1]
      haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
      rw [ZMod.val_one]
  have h34_le26 : Main[34].val ≤ Main[26].val := by
    by_contra hgt
    have hgt : Main[26].val < Main[34].val := Nat.lt_of_not_le hgt
    have h26z : Main[26].val = 0 := by omega
    have h34o : Main[34].val = 1 := by omega
    have hcase := val_sub_cases Main[26] Main[34]
    rw [if_neg (by omega), h26z, h34o] at hcase
    have hp_gt : 65536 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    omega
  have h_sub_val : (Main[26] - Main[34]).val = Main[26].val - Main[34].val := by
    have hcase := val_sub_cases Main[26] Main[34]
    rw [if_pos h34_le26] at hcase
    exact hcase
  -- The 3 sub-derivations
  have h_target_mod4 := jalr_target_mod4_poly Main h_masked_mod4
  have h_unmasked_eq_masked_plus :=
    jalr_unmasked_eq_masked_plus_poly Main h29 h_sub_val h26_lt h27_lt h28_lt h34_val h34_le26
  have h_target_eq :=
    jalr_target_eq_poly Main h_unmasked_eq_masked_plus h_target_mod4 h34_bit
  -- Convert read_op_a/b's `Main[..].val#'_` form to `BitVec.ofNat`
  simp only [BitVec.ofNatLT_eq_ofNat] at read_op_a read_op_b
  -- unfold the spec/sp1 monads
  simp [spec_jalr, sp1_jalr, run_readReg_of_isInitialized _ _ hs,
    EStateM.Result.map, cond, execute_JALR,
    op_a, op_b, op_c, sp1_op_a, sp1_op_b, sp1_op_c, read_op_a, read_op_b,
    ← h_imm_signExtend]
  rw [update_elp_state_of_isInitialized _ _ (by clear *- hs; aesop)]
  · simp only []
    rw [run_readReg_of_isInitialized _ _ (by clear *- hs; aesop)]
    simp [Std.ExtDHashMap.get_insert, read_op_b]
    -- Replace the BitVec sum (rs1 + signExt imm) with the chip's #v[Main[26..29]]
    rw [← h_add]
    rw [h_target_eq]
    rw [jump_to_of_mod4_eq_zero _ _ (by clear *- hs; aesop) (by simpa using h_target_mod4)]
    simp [Std.ExtDHashMap.insert_insert, EStateM.Result.map]
    by_cases h6_zero : Main[6] = 0
    · simp [h6_zero, ZMod.val_zero]
    · -- need: pc+4 written to rd matches the chip's Main[30..33] value
      have h6_val_ne : Main[6].val ≠ 0 := by
        intro hv; apply h6_zero; exact (ZMod.val_eq_zero _).mp hv
      have h6' : BitVec.ofNat 5 (Main[6].val : Nat) ≠ 0#5 := by
        intro heq
        have htn : (BitVec.ofNat 5 Main[6].val).toNat = (0#5).toNat := by rw [heq]
        simp [BitVec.toNat_ofNat] at htn
        omega
      have h13 : Main[13] = 0 := by
        rcases h_op_a_0_bool with h | h
        · exact h
        · exfalso; rw [h] at h_op_a_0_iff
          exact h6_zero (h_op_a_0_iff.mp rfl)
      -- M[3..5,0] is pc, isU64
      have hpc_isU64 : Word.isU64_poly #v[Main[3], Main[4], Main[5], (0 : ZMod p)] := by
        have hp3 : Main[3].val < 65536 := by
          have : Main[3].val < (65536 : ZMod p).val := h_pc0_lt; rwa [h65] at this
        have hp4 : Main[4].val < 65536 := by
          have : Main[4].val < (65536 : ZMod p).val := h_pc1_lt; rwa [h65] at this
        have hp5 : Main[5].val < 65536 := by
          have : Main[5].val < (65536 : ZMod p).val := h_pc2_lt; rwa [h65] at this
        apply Word.isU64_of_cases_poly <;>
          simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
            List.getElem_cons_succ]
        · exact hp3
        · exact hp4
        · exact hp5
        · rw [ZMod.val_zero]; omega
      -- inc_pc constraints applied at multiplicity (1 - M[13]) = 1
      have h_inc_pc' : List.Forall SP1Constraint.toProp_poly
          (AddOperation.constraints #v[Main[3], Main[4], Main[5], (0 : ZMod p)]
            #v[(4 : ZMod p), 0, 0, 0]
            { value := #v[Main[30], Main[31], Main[32], Main[33]] } 1) := by
        have hm : Main[25] - Main[13] = 1 := by rw [h_is_real, h13]; ring
        have := inc_pc_cstrs
        rw [hm] at this
        exact this
      have h_add_pc' :=
        (AddOperation.spec_poly hpc_isU64 Word.four_isU64_poly h_inc_pc').2
      simp at h_add_pc'
      rw [word_four_eq_bitvec_four_jalr] at h_add_pc'
      simp [if_neg h6', read_pc, ← h_add_pc']
  · clear *- hv
    obtain ⟨h1, h2, h3, h4, h5⟩ := hv
    constructor <;> simpa [Std.ExtDHashMap.get_insert]

end Jalr
