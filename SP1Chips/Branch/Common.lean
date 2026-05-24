import SP1Foundations
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Compare.LtOperationSigned.LtOperationSigned
import SP1Operations.Reader.ITypeReaderImmutable.ITypeReaderImmutable
import SP1Chips.Branch.Constraints

namespace Branch

set_option linter.style.setOption false
set_option linter.style.longLine false

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

set_option maxHeartbeats 1600000 in
-- 6-way nested case split, closed by `simp_all` once the disjunctions are
-- destructured. Heartbeats elevated for the 64-case combinatorial closure.
lemma single_op (Main : Vector (ZMod p) 45)
    (cstrs : SP1ConstraintList.allHold (constraints Main)) :
    (Main[28] = 1 → Main[29] = 0 ∧ Main[30] = 0 ∧ Main[31] = 0 ∧ Main[32] = 0 ∧ Main[33] = 0) ∧
    (Main[29] = 1 → Main[28] = 0 ∧ Main[30] = 0 ∧ Main[31] = 0 ∧ Main[32] = 0 ∧ Main[33] = 0) ∧
    (Main[30] = 1 → Main[28] = 0 ∧ Main[29] = 0 ∧ Main[31] = 0 ∧ Main[32] = 0 ∧ Main[33] = 0) ∧
    (Main[31] = 1 → Main[28] = 0 ∧ Main[29] = 0 ∧ Main[30] = 0 ∧ Main[32] = 0 ∧ Main[33] = 0) ∧
    (Main[32] = 1 → Main[28] = 0 ∧ Main[29] = 0 ∧ Main[30] = 0 ∧ Main[31] = 0 ∧ Main[33] = 0) ∧
    (Main[33] = 1 → Main[28] = 0 ∧ Main[29] = 0 ∧ Main[30] = 0 ∧ Main[31] = 0 ∧ Main[32] = 0) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp_lt : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  -- For k ∈ {2, 3, 4, 5, 6}: (k : ZMod p) ≠ 0 ∧ ≠ 1, since k.val = k < p.
  have h2_ne : ((2 : ℕ) : ZMod p) ≠ 0 ∧ ((2 : ℕ) : ZMod p) ≠ 1 := by
    have hv : ((2 : ℕ) : ZMod p).val = 2 := ZMod.val_natCast_of_lt (by omega)
    refine ⟨?_, ?_⟩ <;> intro heq <;>
      (first | rw [heq, ZMod.val_zero] at hv | rw [heq, ZMod.val_one] at hv) <;> omega
  have h3_ne : ((3 : ℕ) : ZMod p) ≠ 0 ∧ ((3 : ℕ) : ZMod p) ≠ 1 := by
    have hv : ((3 : ℕ) : ZMod p).val = 3 := ZMod.val_natCast_of_lt (by omega)
    refine ⟨?_, ?_⟩ <;> intro heq <;>
      (first | rw [heq, ZMod.val_zero] at hv | rw [heq, ZMod.val_one] at hv) <;> omega
  have h4_ne : ((4 : ℕ) : ZMod p) ≠ 0 ∧ ((4 : ℕ) : ZMod p) ≠ 1 := by
    have hv : ((4 : ℕ) : ZMod p).val = 4 := ZMod.val_natCast_of_lt (by omega)
    refine ⟨?_, ?_⟩ <;> intro heq <;>
      (first | rw [heq, ZMod.val_zero] at hv | rw [heq, ZMod.val_one] at hv) <;> omega
  have h5_ne : ((5 : ℕ) : ZMod p) ≠ 0 ∧ ((5 : ℕ) : ZMod p) ≠ 1 := by
    have hv : ((5 : ℕ) : ZMod p).val = 5 := ZMod.val_natCast_of_lt (by omega)
    refine ⟨?_, ?_⟩ <;> intro heq <;>
      (first | rw [heq, ZMod.val_zero] at hv | rw [heq, ZMod.val_one] at hv) <;> omega
  have h6_ne : ((6 : ℕ) : ZMod p) ≠ 0 ∧ ((6 : ℕ) : ZMod p) ≠ 1 := by
    have hv : ((6 : ℕ) : ZMod p).val = 6 := ZMod.val_natCast_of_lt (by omega)
    refine ⟨?_, ?_⟩ <;> intro heq <;>
      (first | rw [heq, ZMod.val_zero] at hv | rw [heq, ZMod.val_one] at hv) <;> omega
  -- Convert to ZMod-side cast-free non-equalities for use in simp_all.
  have h2_ne_zero : (1 + 1 : ZMod p) ≠ 0 := fun h => h2_ne.1 (by push_cast; linear_combination h)
  have h2_ne_one  : (1 + 1 : ZMod p) ≠ 1 := fun h => h2_ne.2 (by push_cast; linear_combination h)
  have h3_ne_zero : (1 + 1 + 1 : ZMod p) ≠ 0 :=
    fun h => h3_ne.1 (by push_cast; linear_combination h)
  have h3_ne_one  : (1 + 1 + 1 : ZMod p) ≠ 1 :=
    fun h => h3_ne.2 (by push_cast; linear_combination h)
  have h4_ne_zero : (1 + 1 + 1 + 1 : ZMod p) ≠ 0 :=
    fun h => h4_ne.1 (by push_cast; linear_combination h)
  have h4_ne_one  : (1 + 1 + 1 + 1 : ZMod p) ≠ 1 :=
    fun h => h4_ne.2 (by push_cast; linear_combination h)
  have h5_ne_zero : (1 + 1 + 1 + 1 + 1 : ZMod p) ≠ 0 :=
    fun h => h5_ne.1 (by push_cast; linear_combination h)
  have h5_ne_one  : (1 + 1 + 1 + 1 + 1 : ZMod p) ≠ 1 :=
    fun h => h5_ne.2 (by push_cast; linear_combination h)
  have h6_ne_zero : (1 + 1 + 1 + 1 + 1 + 1 : ZMod p) ≠ 0 :=
    fun h => h6_ne.1 (by push_cast; linear_combination h)
  have h6_ne_one  : (1 + 1 + 1 + 1 + 1 + 1 : ZMod p) ≠ 1 :=
    fun h => h6_ne.2 (by push_cast; linear_combination h)
  simp [constraints, sub_eq_zero, SP1Constraint.toProp] at cstrs
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, rest⟩ := cstrs
  clear h1 h2 h3 rest
  cases h4 <;> cases h5 <;> cases h6 <;> cases h7 <;> cases h8 <;> cases h9
  all_goals simp_all only [add_zero, zero_add, one_ne_zero, or_true, zero_ne_one,
    and_self, implies_true, or_self,
    h2_ne_zero, h2_ne_one, h3_ne_zero, h3_ne_one,
    h4_ne_zero, h4_ne_one, h5_ne_zero, h5_ne_one,
    h6_ne_zero, h6_ne_one]

set_option maxHeartbeats 1600000 in
-- The 6-arm case-split over `is_real` extracts the trusted_instr
-- signExtend bridge from the active variant's reader constraint. Each
-- variant pins the opcode to a specific small constant (40-45 for
-- branch variants); supply `(k : ZMod p).val = k` simp lemmas
-- explicitly.
lemma eq_signExtend_of_is_real (Main : Vector (ZMod p) 45)
    (cstrs : SP1ConstraintList.allHold (constraints Main))
    (is_real : is_real Main) :
    Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] =
      BitVec.signExtend 64 (BitVec.ofNat 13 Main[21].val) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp_lt : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have h40_lt : (40 : ℕ) < p := by omega
  have h41_lt : (41 : ℕ) < p := by omega
  have h42_lt : (42 : ℕ) < p := by omega
  have h43_lt : (43 : ℕ) < p := by omega
  have h44_lt : (44 : ℕ) < p := by omega
  have h45_lt : (45 : ℕ) < p := by omega
  have h40_val : (40 : ZMod p).val = 40 := ZMod.val_natCast_of_lt h40_lt
  have h41_val : (41 : ZMod p).val = 41 := ZMod.val_natCast_of_lt h41_lt
  have h42_val : (42 : ZMod p).val = 42 := ZMod.val_natCast_of_lt h42_lt
  have h43_val : (43 : ZMod p).val = 43 := ZMod.val_natCast_of_lt h43_lt
  have h44_val : (44 : ZMod p).val = 44 := ZMod.val_natCast_of_lt h44_lt
  have h45_val : (45 : ZMod p).val = 45 := ZMod.val_natCast_of_lt h45_lt
  have := single_op Main cstrs
  rcases is_real with h | h | h | h | h | h
  all_goals
  · simp_all [constraints, ITypeReaderImmutable.constraints,
      SP1Constraint.toProp, Opcode.ofNat, Nat.ble,
      h40_val, h41_val, h42_val, h43_val, h44_val, h45_val]

set_option maxHeartbeats 1600000 in
-- Uses the ZMod %4 → Nat %4 bridge (`val_mod_4_eq_zero_iff_zmod` in Field.lean)
-- to convert `Main[3] % 4 = 0` from the iff's pc-alignment clause
-- into `Main[3].val % 4 = 0`, then closes via the field-agnostic
-- `BitVec.add_mod4_eq_zero_of_mod4_eq_zero` + `BitVec.ofNat64_mod_4_eq_zero_iff`.
lemma add_signExtend_of_constraints (Main : Vector (ZMod p) 45)
    (cstrs : SP1ConstraintList.allHold (constraints Main))
    (is_real : is_real Main) :
    (Word.toBitVec64 #v[Main[3], Main[4], Main[5], (0 : ZMod p)] +
      BitVec.signExtend 64 (BitVec.ofNat 13 Main[21].val)) % 4 = 0 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h_signExt := eq_signExtend_of_is_real Main cstrs is_real
  have hp_lt : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have h40_lt : (40 : ℕ) < p := by omega
  have h41_lt : (41 : ℕ) < p := by omega
  have h42_lt : (42 : ℕ) < p := by omega
  have h43_lt : (43 : ℕ) < p := by omega
  have h44_lt : (44 : ℕ) < p := by omega
  have h45_lt : (45 : ℕ) < p := by omega
  have h40_val : (40 : ZMod p).val = 40 := ZMod.val_natCast_of_lt h40_lt
  have h41_val : (41 : ZMod p).val = 41 := ZMod.val_natCast_of_lt h41_lt
  have h42_val : (42 : ZMod p).val = 42 := ZMod.val_natCast_of_lt h42_lt
  have h43_val : (43 : ZMod p).val = 43 := ZMod.val_natCast_of_lt h43_lt
  have h44_val : (44 : ZMod p).val = 44 := ZMod.val_natCast_of_lt h44_lt
  have h45_val : (45 : ZMod p).val = 45 := ZMod.val_natCast_of_lt h45_lt
  -- Extract Main[3] % 4 = 0 from the active variant's reader iff (as ZMod equation).
  have h_pc_mod_zmod : Main[3] % (4 : ZMod p) = (0 : ZMod p) := by
    have := single_op Main cstrs
    rcases is_real with h | h | h | h | h | h
    all_goals
    · simp_all [constraints, ITypeReaderImmutable.constraints,
        SP1Constraint.toProp, Opcode.ofNat, Nat.ble,
        h40_val, h41_val, h42_val, h43_val, h44_val, h45_val]
  have h_pc_mod : Main[3].val % 4 = 0 := (val_mod_4_eq_zero_iff_zmod _).mp h_pc_mod_zmod
  -- pc[0] limb bound for the Word.toNat decomposition.
  -- Extract the alignment fact from the active variant's trusted_instr (b_type's 4th clause).
  have h_imm_aligned :
      Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] % 4#64 = 0#64 := by
    have := single_op Main cstrs
    rcases is_real with h | h | h | h | h | h
    all_goals
    · simp_all [constraints, ITypeReaderImmutable.constraints,
        SP1Constraint.toProp, Opcode.ofNat, Nat.ble,
        h40_val, h41_val, h42_val, h43_val, h44_val, h45_val]
  apply BitVec.add_mod4_eq_zero_of_mod4_eq_zero
  · -- pc[0]'s BitVec form is mod-4-zero.
    change _ % 4#64 = 0#64
    simp only [Word.toBitVec64]
    rw [BitVec.ofNat64_mod_4_eq_zero_iff]
    simp only [Word.toNat_def, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, ZMod.val_zero]
    omega
  · -- signExtend(imm) is mod-4-zero: bridge via h_signExt to the imm's toBitVec64 form.
    rw [← h_signExt]
    exact h_imm_aligned

/-- Per-limb Nat lift: same as `AddrAddOperation.limb_lift`. Converts a ZMod
equation `bb + vv + prev = aa + cc * 65536` (where prev/cc are carry bits and
the other three limbs are < 2^16) to the corresponding Nat equation. Public
so the chip-level `correct_b*` proofs can lift the post-simp ZMod
limb equations directly without round-tripping through `pc_plus_4_eq`'s
strict carry-disjunction shape. -/
lemma limb_lift_branch
    (bb vv aa prev cc : ZMod p)
    (hbb : bb.val < 2 ^ 16) (hvv : vv.val < 2 ^ 16) (haa : aa.val < 2 ^ 16)
    (hprev : prev = 0 ∨ prev = 1) (hcc : cc = 0 ∨ cc = 1)
    (h : bb + vv + prev = aa + cc * 65536) :
    bb.val + vv.val + prev.val = aa.val + cc.val * 65536 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  apply_fun ZMod.val at h
  have hprev_lt : prev.val ≤ 1 := by
    rcases hprev with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hcc_lt : cc.val ≤ 1 := by
    rcases hcc with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hbv : (bb + vv).val = bb.val + vv.val :=
    ZMod.val_add_of_lt (by omega)
  have h1 : (bb + vv + prev).val = bb.val + vv.val + prev.val := by
    rw [ZMod.val_add_of_lt (by rw [hbv]; omega), hbv]
  have h2 : (cc * 65536 : ZMod p).val = cc.val * 65536 := by
    rcases hcc with h | h <;> simp [h, ZMod.val_zero, val_65536_zmod_p, ZMod.val_one]
  have h3 : (aa + cc * 65536 : ZMod p).val = aa.val + cc.val * 65536 := by
    rw [ZMod.val_add_of_lt
      (by rw [h2]; rcases hcc with h | h <;>
            simp [h, ZMod.val_zero, ZMod.val_one] <;> omega), h2]
  rw [h1, h3] at h
  exact h

/-- Bare-`ℕ` close for `branch_addr_eq`'s carry chain. Mirrors the
`AddrAddOperation.close_addr_add_nat` recipe — extracted helper isolates the
`% 2 ^ 64` exposure so the kernel re-check passes without `skipKernelTC`. -/
private lemma close_branch_addr_nat
    (a0 a1 a2 b0 b1 b2 b3 v0 v1 v2 c0 c1 c2 c3 : ℕ)
    (hv0 : v0 < 2 ^ 16) (hv1 : v1 < 2 ^ 16) (hv2 : v2 < 2 ^ 16)
    (n0 : a0 + b0 = v0 + c0 * 65536)
    (n1 : a1 + b1 + c0 = v1 + c1 * 65536)
    (n2 : a2 + b2 + c1 = v2 + c2 * 65536)
    (n3 : b3 + c2 = c3 * 65536) :
    v0 + v1 * 2 ^ 16 + v2 * 2 ^ 32 + 0 * 2 ^ 48 =
      (a0 + a1 * 2 ^ 16 + a2 * 2 ^ 32 + 0 * 2 ^ 48 +
        (b0 + b1 * 2 ^ 16 + b2 * 2 ^ 32 + b3 * 2 ^ 48)) % 2 ^ 64 := by
  omega

set_option maxHeartbeats 16000000 in
-- Mirrors `AddrAddOperation.spec_of_constraints`'s `linear_combination * h65inv`
-- + `limb_lift` recipe. The four carry hypotheses come from the chip's
-- assertZero'd limb-binarity constraints (E102/E109/E116/E123 with Main[34]=1
-- substituted), which after destructuring yield disjunctions of the form
-- `c = 0 ∨ c = 1` where `c` is the inverse-form carry expression. The high
-- limb of the result vector is `0` (the chip pins next_pc[3] = 0 via E121's
-- final-carry = 0 case).
lemma branch_addr_eq
    (Main : Vector (ZMod p) 45)
    (h_imm_signExtend :
      Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] =
        BitVec.signExtend 64 (BitVec.ofNat 13 Main[21].val))
    (h_pc_0 : Main[3].val < 65536) (h_pc_1 : Main[4].val < 65536)
    (h_pc_2 : Main[5].val < 65536)
    (h_imm_0 : Main[21].val < 65536) (h_imm_1 : Main[22].val < 65536)
    (h_imm_2 : Main[23].val < 65536) (h_imm_3 : Main[24].val < 65536)
    (h25 : Main[25].val < 65536) (h26 : Main[26].val < 65536)
    (h27 : Main[27].val < 65536)
    (hc0 : (Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ = 0
        ∨ (Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ = 1)
    (hc1 : ((Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22] - Main[26]) *
              (65536 : ZMod p)⁻¹ = 0
        ∨ ((Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22] - Main[26]) *
              (65536 : ZMod p)⁻¹ = 1)
    (hc2 : (((Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22] - Main[26]) *
              (65536 : ZMod p)⁻¹ + Main[5] + Main[23] - Main[27]) * (65536 : ZMod p)⁻¹ = 0
        ∨ (((Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22] - Main[26]) *
              (65536 : ZMod p)⁻¹ + Main[5] + Main[23] - Main[27]) * (65536 : ZMod p)⁻¹ = 1)
    (hc3 : ((((Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22] - Main[26]) *
              (65536 : ZMod p)⁻¹ + Main[5] + Main[23] - Main[27]) * (65536 : ZMod p)⁻¹ +
              Main[24]) * (65536 : ZMod p)⁻¹ = 0
        ∨ ((((Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22] - Main[26]) *
              (65536 : ZMod p)⁻¹ + Main[5] + Main[23] - Main[27]) * (65536 : ZMod p)⁻¹ +
              Main[24]) * (65536 : ZMod p)⁻¹ = 1) :
    Word.toBitVec64 #v[Main[3], Main[4], Main[5], (0 : ZMod p)] +
        BitVec.signExtend 64 (BitVec.ofNat 13 Main[21].val)
      = Word.toBitVec64 #v[Main[25], Main[26], Main[27], (0 : ZMod p)] := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rw [← h_imm_signExtend]
  -- isU64 facts to feed Word.toBitVec64_toNat.
  have h_zero_val : ((0 : ZMod p)).val = 0 := ZMod.val_zero
  have hzero_lt : ((0 : ZMod p)).val < 2 ^ 16 := by rw [h_zero_val]; omega
  have h_pc_isU64 : Word.isU64 #v[Main[3], Main[4], Main[5], (0 : ZMod p)] := by
    apply Word.isU64_of_cases <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · exact h_pc_0
    · exact h_pc_1
    · exact h_pc_2
    · rw [h_zero_val]; omega
  have h_imm_isU64 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := by
    apply Word.isU64_of_cases <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · exact h_imm_0
    · exact h_imm_1
    · exact h_imm_2
    · exact h_imm_3
  have h_npc_isU64 : Word.isU64 #v[Main[25], Main[26], Main[27], (0 : ZMod p)] := by
    apply Word.isU64_of_cases <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · exact h25
    · exact h26
    · exact h27
    · rw [h_zero_val]; omega
  have h65inv : (65536 : ZMod p) * (65536 : ZMod p)⁻¹ = 1 :=
    mul_inv_cancel₀ val_65536_ne_zero
  rw [← BitVec.toNat_inj, BitVec.toNat_add,
      Word.toBitVec64_toNat h_npc_isU64,
      Word.toBitVec64_toNat h_imm_isU64,
      Word.toBitVec64_toNat h_pc_isU64,
      Word.toNat_def, Word.toNat_def, Word.toNat_def]
  -- Reduce vector literal indices, keep `+ 0 * 2 ^ 48` for the helper.
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, h_zero_val]
  -- Carry-chain rearrangement, mirroring AddrAddOperation.spec_of_constraints.
  set c0 : ZMod p := (Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ with hc0_def
  set c1 : ZMod p := (c0 + Main[4] + Main[22] - Main[26]) * (65536 : ZMod p)⁻¹ with hc1_def
  set c2 : ZMod p := (c1 + Main[5] + Main[23] - Main[27]) * (65536 : ZMod p)⁻¹ with hc2_def
  set c3 : ZMod p := (c2 + Main[24]) * (65536 : ZMod p)⁻¹ with hc3_def
  have e0 : Main[3] + Main[21] + (0 : ZMod p) = Main[25] + c0 * 65536 := by
    rw [hc0_def]; linear_combination -1 * (Main[3] + Main[21] - Main[25]) * h65inv
  have e1 : Main[4] + Main[22] + c0 = Main[26] + c1 * 65536 := by
    rw [hc1_def]
    linear_combination -1 * (c0 + Main[4] + Main[22] - Main[26]) * h65inv
  have e2 : Main[5] + Main[23] + c1 = Main[27] + c2 * 65536 := by
    rw [hc2_def]
    linear_combination -1 * (c1 + Main[5] + Main[23] - Main[27]) * h65inv
  have e3 : (0 : ZMod p) + Main[24] + c2 = (0 : ZMod p) + c3 * 65536 := by
    rw [hc3_def]
    linear_combination -1 * (c2 + Main[24]) * h65inv
  have hc_zero : (0 : ZMod p) = 0 ∨ (0 : ZMod p) = 1 := Or.inl rfl
  have h_pc_0_lt : Main[3].val < 2 ^ 16 := by simpa using h_pc_0
  have h_pc_1_lt : Main[4].val < 2 ^ 16 := by simpa using h_pc_1
  have h_pc_2_lt : Main[5].val < 2 ^ 16 := by simpa using h_pc_2
  have h_imm_0_lt : Main[21].val < 2 ^ 16 := by simpa using h_imm_0
  have h_imm_1_lt : Main[22].val < 2 ^ 16 := by simpa using h_imm_1
  have h_imm_2_lt : Main[23].val < 2 ^ 16 := by simpa using h_imm_2
  have h_imm_3_lt : Main[24].val < 2 ^ 16 := by simpa using h_imm_3
  have h25_lt : Main[25].val < 2 ^ 16 := by simpa using h25
  have h26_lt : Main[26].val < 2 ^ 16 := by simpa using h26
  have h27_lt : Main[27].val < 2 ^ 16 := by simpa using h27
  have n0 := limb_lift_branch _ _ _ _ _ h_pc_0_lt h_imm_0_lt h25_lt hc_zero hc0 e0
  have n1 := limb_lift_branch _ _ _ _ _ h_pc_1_lt h_imm_1_lt h26_lt hc0 hc1 e1
  have n2 := limb_lift_branch _ _ _ _ _ h_pc_2_lt h_imm_2_lt h27_lt hc1 hc2 e2
  have n3 := limb_lift_branch _ _ _ _ _ hzero_lt h_imm_3_lt hzero_lt hc2 hc3 e3
  simp only [ZMod.val_zero, add_zero, zero_add] at n0 n3
  exact (close_branch_addr_nat _ _ _ _ _ _ _ _ _ _ _ _ _ _
    h25_lt h26_lt h27_lt n0 n1 n2 n3).symm

/-- Bare-`ℕ` close for `pc_plus_4_eq`'s carry chain. The `4 % 2 ^ 64`
appears because `BitVec.toNat_ofNat` was used to unfold `4#64.toNat`; omega
absorbs it trivially. Same isolation principle as `close_branch_addr_nat`. -/
private lemma close_pc_plus_4_nat
    (a0 a1 a2 v0 v1 v2 c0 c1 c2 c3 : ℕ)
    (hv0 : v0 < 2 ^ 16) (hv1 : v1 < 2 ^ 16) (hv2 : v2 < 2 ^ 16)
    (n0 : a0 + 4 = v0 + c0 * 65536)
    (n1 : a1 + c0 = v1 + c1 * 65536)
    (n2 : a2 + c1 = v2 + c2 * 65536)
    (n3 : c2 = c3 * 65536) :
    v0 + v1 * 2 ^ 16 + v2 * 2 ^ 32 + 0 * 2 ^ 48 =
      (a0 + a1 * 2 ^ 16 + a2 * 2 ^ 32 + 0 * 2 ^ 48 + 4 % 2 ^ 64) % 2 ^ 64 := by
  omega

set_option maxHeartbeats 16000000 in
-- Not-branching-case PC arithmetic. Same recipe as `branch_addr_eq`
-- but with the addend fixed to `4#64`
-- (i.e. `b = #v[4, 0, 0, 0]` viewed as a Word). The four carry hypotheses
-- come from the chip's E131/E139/E147/E155 binarity assertZeros (gated by
-- `E16 - Main[34] = 1` when not branching, i.e. Main[34] = 0). The high
-- three limbs of the addend are 0; only the low limb gets `+4`. This is
-- the missing companion to `branch_addr_eq` for the BEQ/BNE/etc.
-- "branch was not taken" path.
lemma pc_plus_4_eq
    (Main : Vector (ZMod p) 45)
    (h_pc_0 : Main[3].val < 65536) (h_pc_1 : Main[4].val < 65536)
    (h_pc_2 : Main[5].val < 65536)
    (h25 : Main[25].val < 65536) (h26 : Main[26].val < 65536)
    (h27 : Main[27].val < 65536)
    (hc0 : (Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ = 0
        ∨ (Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ = 1)
    (hc1 : ((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + 0 - Main[26]) *
              (65536 : ZMod p)⁻¹ = 0
        ∨ ((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + 0 - Main[26]) *
              (65536 : ZMod p)⁻¹ = 1)
    (hc2 : (((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + 0 - Main[26]) *
              (65536 : ZMod p)⁻¹ + Main[5] + 0 - Main[27]) * (65536 : ZMod p)⁻¹ = 0
        ∨ (((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + 0 - Main[26]) *
              (65536 : ZMod p)⁻¹ + Main[5] + 0 - Main[27]) * (65536 : ZMod p)⁻¹ = 1)
    (hc3 : ((((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + 0 - Main[26]) *
              (65536 : ZMod p)⁻¹ + Main[5] + 0 - Main[27]) * (65536 : ZMod p)⁻¹ +
              0 + 0 - 0) * (65536 : ZMod p)⁻¹ = 0
        ∨ ((((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + 0 - Main[26]) *
              (65536 : ZMod p)⁻¹ + Main[5] + 0 - Main[27]) * (65536 : ZMod p)⁻¹ +
              0 + 0 - 0) * (65536 : ZMod p)⁻¹ = 1) :
    Word.toBitVec64 #v[Main[3], Main[4], Main[5], (0 : ZMod p)] + 4#64
      = Word.toBitVec64 #v[Main[25], Main[26], Main[27], (0 : ZMod p)] := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h_zero_val : ((0 : ZMod p)).val = 0 := ZMod.val_zero
  have hzero_lt : ((0 : ZMod p)).val < 2 ^ 16 := by rw [h_zero_val]; omega
  have h_pc_isU64 : Word.isU64 #v[Main[3], Main[4], Main[5], (0 : ZMod p)] := by
    apply Word.isU64_of_cases <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · exact h_pc_0
    · exact h_pc_1
    · exact h_pc_2
    · rw [h_zero_val]; omega
  have h_npc_isU64 : Word.isU64 #v[Main[25], Main[26], Main[27], (0 : ZMod p)] := by
    apply Word.isU64_of_cases <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · exact h25
    · exact h26
    · exact h27
    · rw [h_zero_val]; omega
  have h65inv : (65536 : ZMod p) * (65536 : ZMod p)⁻¹ = 1 :=
    mul_inv_cancel₀ val_65536_ne_zero
  -- Bridge `... + 4#64 = ...` via toNat:
  rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
      ← BitVec.toNat_inj, BitVec.toNat_add,
      Word.toBitVec64_toNat h_npc_isU64,
      Word.toBitVec64_toNat h_pc_isU64,
      Word.toNat_def, Word.toNat_def, BitVec.toNat_ofNat]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, h_zero_val]
  set c0 : ZMod p := (Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ with hc0_def
  set c1 : ZMod p := (c0 + Main[4] + 0 - Main[26]) * (65536 : ZMod p)⁻¹ with hc1_def
  set c2 : ZMod p := (c1 + Main[5] + 0 - Main[27]) * (65536 : ZMod p)⁻¹ with hc2_def
  set c3 : ZMod p := (c2 + 0 + 0 - 0) * (65536 : ZMod p)⁻¹ with hc3_def
  have e0 : Main[3] + (4 : ZMod p) + (0 : ZMod p) = Main[25] + c0 * 65536 := by
    rw [hc0_def]; linear_combination -1 * (Main[3] + 4 - Main[25]) * h65inv
  have e1 : Main[4] + (0 : ZMod p) + c0 = Main[26] + c1 * 65536 := by
    rw [hc1_def]
    linear_combination -1 * (c0 + Main[4] + 0 - Main[26]) * h65inv
  have e2 : Main[5] + (0 : ZMod p) + c1 = Main[27] + c2 * 65536 := by
    rw [hc2_def]
    linear_combination -1 * (c1 + Main[5] + 0 - Main[27]) * h65inv
  have e3 : (0 : ZMod p) + (0 : ZMod p) + c2 = (0 : ZMod p) + c3 * 65536 := by
    rw [hc3_def]
    linear_combination -1 * (c2 + 0 + 0 - 0) * h65inv
  have hc_zero : (0 : ZMod p) = 0 ∨ (0 : ZMod p) = 1 := Or.inl rfl
  have h_pc_0_lt : Main[3].val < 2 ^ 16 := by simpa using h_pc_0
  have h_pc_1_lt : Main[4].val < 2 ^ 16 := by simpa using h_pc_1
  have h_pc_2_lt : Main[5].val < 2 ^ 16 := by simpa using h_pc_2
  have h25_lt : Main[25].val < 2 ^ 16 := by simpa using h25
  have h26_lt : Main[26].val < 2 ^ 16 := by simpa using h26
  have h27_lt : Main[27].val < 2 ^ 16 := by simpa using h27
  -- Treat `4` as `((4 : ℕ) : ZMod p)` for limb_lift_branch (which expects
  -- the second arg as the "vv" limb with vv.val < 2^16).
  have h4_val : ((4 : ℕ) : ZMod p).val = 4 := by
    have hp : 2 ^ 17 < p := Fact.out
    exact ZMod.val_natCast_of_lt (by omega)
  have h4_lt : ((4 : ZMod p)).val < 2 ^ 16 := by
    rw [show (4 : ZMod p) = ((4 : ℕ) : ZMod p) from by push_cast; rfl, h4_val]
    omega
  have n0 := limb_lift_branch _ _ _ _ _ h_pc_0_lt h4_lt h25_lt hc_zero hc0 e0
  have n1 := limb_lift_branch _ _ _ _ _ h_pc_1_lt hzero_lt h26_lt hc0 hc1 e1
  have n2 := limb_lift_branch _ _ _ _ _ h_pc_2_lt hzero_lt h27_lt hc1 hc2 e2
  have n3 := limb_lift_branch _ _ _ _ _ hzero_lt hzero_lt hzero_lt hc2 hc3 e3
  have h4val_eq : ((4 : ZMod p)).val = 4 := by
    rw [show (4 : ZMod p) = ((4 : ℕ) : ZMod p) from by push_cast; rfl, h4_val]
  rw [h4val_eq] at n0
  simp only [ZMod.val_zero, add_zero, zero_add] at n0 n1 n2 n3
  exact (close_pc_plus_4_nat _ _ _ _ _ _ _ _ _ _
    h25_lt h26_lt h27_lt n0 n1 n2 n3).symm

set_option maxHeartbeats 16000000 in
-- Variant of `pc_plus_4_eq` accepting the chip's *natural* post-simp
-- limb form: each carry hypothesis is the simp-fragmented disjunction
-- `((a = b ∨ 65536 = 0) ∨ (a - b) * (65536 : ZMod p)⁻¹ = 1)` from default simp's
-- `mul_eq_zero` + `inv_eq_zero` + `sub_eq_zero` firing on the assertZero
-- constraint `((a - b) * (65536 : ZMod p)⁻¹) * (((a - b) * (65536 : ZMod p)⁻¹) - 1) = 0`. The chip
-- proof passes `chip_cstrs.h_limb0..3` directly without any pre-bridge step.
-- Internally bridges to canonical form, then mirrors `pc_plus_4_eq`'s
-- `limb_lift_branch` chain. Heartbeats elevated for the bridges + chain.
lemma pc_plus_4_eq_chip
    (Main : Vector (ZMod p) 45)
    (h_pc_0 : Main[3].val < 65536) (h_pc_1 : Main[4].val < 65536)
    (h_pc_2 : Main[5].val < 65536)
    (h25 : Main[25].val < 65536) (h26 : Main[26].val < 65536)
    (h27 : Main[27].val < 65536)
    (hc0 : (Main[3] + 4 = Main[25] ∨ (65536 : ZMod p) = 0)
        ∨ (Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ = 1)
    (hc1 : (((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] = Main[26]
              ∨ (65536 : ZMod p) = 0)
        ∨ ((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] - Main[26]) *
              (65536 : ZMod p)⁻¹ = 1))
    (hc2 : ((((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] - Main[26]) *
              (65536 : ZMod p)⁻¹ + Main[5] = Main[27] ∨ (65536 : ZMod p) = 0)
        ∨ (((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] - Main[26]) *
              (65536 : ZMod p)⁻¹ + Main[5] - Main[27]) * (65536 : ZMod p)⁻¹ = 1))
    (hc3 : ((((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] - Main[26]) *
              (65536 : ZMod p)⁻¹ + Main[5] = Main[27] ∨ (65536 : ZMod p) = 0)
        ∨ (((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] - Main[26]) *
              (65536 : ZMod p)⁻¹ + Main[5] - Main[27]) * (65536 : ZMod p)⁻¹ *
                (65536 : ZMod p)⁻¹ = 1)) :
    Word.toBitVec64 #v[Main[3], Main[4], Main[5], (0 : ZMod p)] + 4#64
      = Word.toBitVec64 #v[Main[25], Main[26], Main[27], (0 : ZMod p)] := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h_65_ne : (65536 : ZMod p) ≠ 0 := val_65536_ne_zero
  -- Bridge each carry from the chip's messy form to canonical `c = 0 ∨ c = 1`.
  have hc0' : (Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ = 0
      ∨ (Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ = 1 := by
    rcases hc0 with (h | h) | h
    · left; rw [show Main[3] + 4 - Main[25] = 0 from by linear_combination h, zero_mul]
    · exact absurd h h_65_ne
    · right; exact h
  have hc1' : ((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] - Main[26])
                  * (65536 : ZMod p)⁻¹ = 0
      ∨ ((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] - Main[26])
                  * (65536 : ZMod p)⁻¹ = 1 := by
    rcases hc1 with (h | h) | h
    · left
      rw [show (Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] - Main[26] = 0
          from by linear_combination h, zero_mul]
    · exact absurd h h_65_ne
    · right; exact h
  have hc2' :
      (((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] - Main[26])
                  * (65536 : ZMod p)⁻¹ + Main[5] - Main[27]) * (65536 : ZMod p)⁻¹ = 0
      ∨ (((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] - Main[26])
                  * (65536 : ZMod p)⁻¹ + Main[5] - Main[27]) * (65536 : ZMod p)⁻¹ = 1 := by
    rcases hc2 with (h | h) | h
    · left
      rw [show ((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] - Main[26])
                  * (65536 : ZMod p)⁻¹ + Main[5] - Main[27] = 0 from by linear_combination h,
          zero_mul]
    · exact absurd h h_65_ne
    · right; exact h
  have hc3' :
      (((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] - Main[26])
                  * (65536 : ZMod p)⁻¹ + Main[5] - Main[27]) * (65536 : ZMod p)⁻¹
                * (65536 : ZMod p)⁻¹ = 0
      ∨ (((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] - Main[26])
                  * (65536 : ZMod p)⁻¹ + Main[5] - Main[27]) * (65536 : ZMod p)⁻¹
                * (65536 : ZMod p)⁻¹ = 1 := by
    rcases hc3 with (h | h) | h
    · left
      rw [show ((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] - Main[26])
                  * (65536 : ZMod p)⁻¹ + Main[5] - Main[27] = 0 from by linear_combination h,
          zero_mul, zero_mul]
    · exact absurd h h_65_ne
    · right; exact h
  -- Now mirror pc_plus_4_eq's body using the canonical-form carries.
  have h_zero_val : ((0 : ZMod p)).val = 0 := ZMod.val_zero
  have hzero_lt : ((0 : ZMod p)).val < 2 ^ 16 := by rw [h_zero_val]; omega
  have h_pc_isU64 : Word.isU64 #v[Main[3], Main[4], Main[5], (0 : ZMod p)] := by
    apply Word.isU64_of_cases <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · exact h_pc_0
    · exact h_pc_1
    · exact h_pc_2
    · rw [h_zero_val]; omega
  have h_npc_isU64 : Word.isU64 #v[Main[25], Main[26], Main[27], (0 : ZMod p)] := by
    apply Word.isU64_of_cases <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · exact h25
    · exact h26
    · exact h27
    · rw [h_zero_val]; omega
  have h65inv : (65536 : ZMod p) * (65536 : ZMod p)⁻¹ = 1 :=
    mul_inv_cancel₀ val_65536_ne_zero
  rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
      ← BitVec.toNat_inj, BitVec.toNat_add,
      Word.toBitVec64_toNat h_npc_isU64,
      Word.toBitVec64_toNat h_pc_isU64,
      Word.toNat_def, Word.toNat_def, BitVec.toNat_ofNat]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, h_zero_val]
  set c0 : ZMod p := (Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ with hc0_def
  set c1 : ZMod p := (c0 + Main[4] - Main[26]) * (65536 : ZMod p)⁻¹ with hc1_def
  set c2 : ZMod p := (c1 + Main[5] - Main[27]) * (65536 : ZMod p)⁻¹ with hc2_def
  set c3 : ZMod p := c2 * (65536 : ZMod p)⁻¹ with hc3_def
  have e0 : Main[3] + (4 : ZMod p) + (0 : ZMod p) = Main[25] + c0 * 65536 := by
    rw [hc0_def]; linear_combination -1 * (Main[3] + 4 - Main[25]) * h65inv
  have e1 : Main[4] + (0 : ZMod p) + c0 = Main[26] + c1 * 65536 := by
    rw [hc1_def]
    linear_combination -1 * (c0 + Main[4] - Main[26]) * h65inv
  have e2 : Main[5] + (0 : ZMod p) + c1 = Main[27] + c2 * 65536 := by
    rw [hc2_def]
    linear_combination -1 * (c1 + Main[5] - Main[27]) * h65inv
  have e3 : (0 : ZMod p) + (0 : ZMod p) + c2 = (0 : ZMod p) + c3 * 65536 := by
    rw [hc3_def]
    linear_combination -1 * c2 * h65inv
  have hc_zero : (0 : ZMod p) = 0 ∨ (0 : ZMod p) = 1 := Or.inl rfl
  have h_pc_0_lt : Main[3].val < 2 ^ 16 := by simpa using h_pc_0
  have h_pc_1_lt : Main[4].val < 2 ^ 16 := by simpa using h_pc_1
  have h_pc_2_lt : Main[5].val < 2 ^ 16 := by simpa using h_pc_2
  have h25_lt : Main[25].val < 2 ^ 16 := by simpa using h25
  have h26_lt : Main[26].val < 2 ^ 16 := by simpa using h26
  have h27_lt : Main[27].val < 2 ^ 16 := by simpa using h27
  have h4_val : ((4 : ℕ) : ZMod p).val = 4 := by
    have hp : 2 ^ 17 < p := Fact.out
    exact ZMod.val_natCast_of_lt (by omega)
  have h4_lt : ((4 : ZMod p)).val < 2 ^ 16 := by
    rw [show (4 : ZMod p) = ((4 : ℕ) : ZMod p) from by push_cast; rfl, h4_val]
    omega
  have n0 := limb_lift_branch _ _ _ _ _ h_pc_0_lt h4_lt h25_lt hc_zero hc0' e0
  have n1 := limb_lift_branch _ _ _ _ _ h_pc_1_lt hzero_lt h26_lt hc0' hc1' e1
  have n2 := limb_lift_branch _ _ _ _ _ h_pc_2_lt hzero_lt h27_lt hc1' hc2' e2
  have n3 := limb_lift_branch _ _ _ _ _ hzero_lt hzero_lt hzero_lt hc2' hc3' e3
  have h4val_eq : ((4 : ZMod p)).val = 4 := by
    rw [show (4 : ZMod p) = ((4 : ℕ) : ZMod p) from by push_cast; rfl, h4_val]
  rw [h4val_eq] at n0
  simp only [ZMod.val_zero, add_zero, zero_add] at n0 n1 n2 n3
  exact (close_pc_plus_4_nat _ _ _ _ _ _ _ _ _ _
    h25_lt h26_lt h27_lt n0 n1 n2 n3).symm


set_option linter.unusedSectionVars false in
-- Polymorphic iff lemma mirroring `Bitwise.allHold_constraints_iff`.
-- Exposes 3 sub-allHolds (CPUState/ITypeReaderImmutable/LtOperationSigned) +
-- 17 chip-list assertZero props + 3 byte-send props (PC alignment Range checks).
-- The is_real sum and the inverse-form carry expressions are inlined verbatim.
lemma allHold_constraints_iff (Main : Vector (ZMod p) 45) :
    List.Forall SP1Constraint.toProp (constraints Main) ↔
    List.Forall SP1Constraint.toProp
        (_root_.CPUState.constraints
          (CPUState.mk Main[0] Main[1] Main[2] #v[Main[3], Main[4], Main[5]])
          #v[Main[25], Main[26], Main[27]] 8
          (Main[28] + Main[29] + Main[30] + Main[31] + Main[32] + Main[33])) ∧
    List.Forall SP1Constraint.toProp
        (ITypeReaderImmutable.constraints Main[0] (Main[2] + Main[1] * 65536)
          #v[Main[3], Main[4], Main[5]]
          (Main[28] * 40 + Main[29] * 41 + Main[30] * 42 + Main[31] * 43 +
            Main[32] * 44 + Main[33] * 45)
          { op_a := Main[6],
            op_a_memory :=
              { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
                access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } },
            op_a_0 := Main[13], op_b := Main[14],
            op_b_memory :=
              { prev_value := #v[Main[15], Main[16], Main[17], Main[18]],
                access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } },
            op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]] }
          (Main[28] + Main[29] + Main[30] + Main[31] + Main[32] + Main[33])
          (Main[28] + Main[29] + Main[30] + Main[31] + Main[32] + Main[33])) ∧
    List.Forall SP1Constraint.toProp
        (LtOperationSigned.constraints
          #v[Main[7], Main[8], Main[9], Main[10]]
          #v[Main[15], Main[16], Main[17], Main[18]]
          { result :=
              { u16_compare_operation := { bit := Main[35] },
                u16_flags := #v[Main[36], Main[37], Main[38], Main[39]],
                not_eq_inv := Main[40],
                comparison_limbs := #v[Main[41], Main[42]] },
            b_msb := { msb := Main[43] }, c_msb := { msb := Main[44] } }
          (Main[30] + Main[31])
          (Main[28] + Main[29] + Main[30] + Main[31] + Main[32] + Main[33])) ∧
    Main[28] * (Main[28] - 1) = 0 ∧
    Main[29] * (Main[29] - 1) = 0 ∧
    Main[30] * (Main[30] - 1) = 0 ∧
    Main[31] * (Main[31] - 1) = 0 ∧
    Main[32] * (Main[32] - 1) = 0 ∧
    Main[33] * (Main[33] - 1) = 0 ∧
    (Main[28] + Main[29] + Main[30] + Main[31] + Main[32] + Main[33]) *
      (Main[28] + Main[29] + Main[30] + Main[31] + Main[32] + Main[33] - 1) = 0 ∧
    Main[34] * (Main[34] - 1) = 0 ∧
    (Main[28] + Main[29] + Main[30] + Main[31] + Main[32] + Main[33]) *
        (Main[34] -
          (0 + Main[28] * (1 - (Main[36] + Main[37] + Main[38] + Main[39])) +
              Main[29] * (1 - (1 - (Main[36] + Main[37] + Main[38] + Main[39]))) +
              (Main[31] + Main[33]) * (1 - Main[35]) +
            (Main[30] + Main[32]) * Main[35])) = 0 ∧
    Main[34] *
        ((0 + Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ *
          ((0 + Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ - 1)) = 0 ∧
    Main[34] *
        (((0 + Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22] - Main[26]) *
            (65536 : ZMod p)⁻¹ *
          (((0 + Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22] - Main[26]) *
              (65536 : ZMod p)⁻¹ - 1)) = 0 ∧
    Main[34] *
        ((((0 + Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22] - Main[26]) *
                (65536 : ZMod p)⁻¹ + Main[5] + Main[23] - Main[27]) *
            (65536 : ZMod p)⁻¹ *
          ((((0 + Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22] - Main[26]) *
                  (65536 : ZMod p)⁻¹ + Main[5] + Main[23] - Main[27]) *
              (65536 : ZMod p)⁻¹ - 1)) = 0 ∧
    Main[34] *
        (((((0 + Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22] - Main[26]) *
                  (65536 : ZMod p)⁻¹ + Main[5] + Main[23] - Main[27]) *
              (65536 : ZMod p)⁻¹ + 0 + Main[24] - 0) *
            (65536 : ZMod p)⁻¹ *
          (((((0 + Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22] - Main[26]) *
                    (65536 : ZMod p)⁻¹ + Main[5] + Main[23] - Main[27]) *
                (65536 : ZMod p)⁻¹ + 0 + Main[24] - 0) *
              (65536 : ZMod p)⁻¹ - 1)) = 0 ∧
    (Main[28] + Main[29] + Main[30] + Main[31] + Main[32] + Main[33] - Main[34]) *
        ((0 + Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ *
          ((0 + Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ - 1)) = 0 ∧
    (Main[28] + Main[29] + Main[30] + Main[31] + Main[32] + Main[33] - Main[34]) *
        (((0 + Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + 0 - Main[26]) *
            (65536 : ZMod p)⁻¹ *
          (((0 + Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + 0 - Main[26]) *
              (65536 : ZMod p)⁻¹ - 1)) = 0 ∧
    (Main[28] + Main[29] + Main[30] + Main[31] + Main[32] + Main[33] - Main[34]) *
        ((((0 + Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + 0 - Main[26]) *
                (65536 : ZMod p)⁻¹ + Main[5] + 0 - Main[27]) *
            (65536 : ZMod p)⁻¹ *
          ((((0 + Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + 0 - Main[26]) *
                  (65536 : ZMod p)⁻¹ + Main[5] + 0 - Main[27]) *
              (65536 : ZMod p)⁻¹ - 1)) = 0 ∧
    (Main[28] + Main[29] + Main[30] + Main[31] + Main[32] + Main[33] - Main[34]) *
        (((((0 + Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + 0 - Main[26]) *
                  (65536 : ZMod p)⁻¹ + Main[5] + 0 - Main[27]) *
              (65536 : ZMod p)⁻¹ + 0 + 0 - 0) *
            (65536 : ZMod p)⁻¹ *
          (((((0 + Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + 0 - Main[26]) *
                    (65536 : ZMod p)⁻¹ + Main[5] + 0 - Main[27]) *
                (65536 : ZMod p)⁻¹ + 0 + 0 - 0) *
              (65536 : ZMod p)⁻¹ - 1)) = 0 ∧
    (Main[28] + Main[29] + Main[30] + Main[31] + Main[32] + Main[33] ≠ 0 →
      (ByteOpcode.ofNat 6).constrain (Main[25] * (4 : ZMod p)⁻¹) 14 0) ∧
    (Main[28] + Main[29] + Main[30] + Main[31] + Main[32] + Main[33] ≠ 0 →
      (ByteOpcode.ofNat 6).constrain Main[26] 16 0) ∧
    (Main[28] + Main[29] + Main[30] + Main[31] + Main[32] + Main[33] ≠ 0 →
      (ByteOpcode.ofNat 6).constrain Main[27] 16 0) := by
  simp only [constraints, List.forall_append, List.Forall, SP1Constraint.toProp,
    and_assoc]
  push_cast
  rfl

end Branch
