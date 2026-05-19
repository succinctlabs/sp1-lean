import SP1Operations.Operation.AddOperation
import SP1Chips.Jal.Constraints

namespace Jal

open BitVec

open Sail SailState BitVec LeanRV64D.Functions

attribute [simp] assert PreSail.assert
  RETIRE_SUCCESS

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 31) (s : SailState)

lemma op_a_lt32_of_constraints {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    {Main : Vector (ZMod p) 31}
    (h_cstrs : (constraints Main).allHold_poly) (h_is_real : Main[30] = 1) :
    Main[6].val < 32 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h32 : (32 : ZMod p).val = 32 := val_32_zmod_p
  simp [SP1ConstraintList.allHold_poly, constraints, SP1Constraint.toProp_poly] at h_cstrs
  -- Extract Main[6] < 32 from the constraint list (the program send clause).
  have h6_lt : Main[6] < (32 : ZMod p) := by aesop
  have : Main[6].val < (32 : ZMod p).val := h6_lt
  rwa [h32] at this

def sp1_op_a (cstrs : (constraints Main).allHold_poly) (h_is_real : Main[30] = 1) :
    BitVec 5 :=
  Main[6].val#'(op_a_lt32_of_constraints cstrs h_is_real)

def sp1_op_b : BitVec 21 := BitVec.ofNat 21 (Main[14].val + Main[15].val * 65536)

def sp1_jal (Main : Vector (ZMod p) 31) : SailM Unit := do
  let op_a := regidx.Regidx (BitVec.ofNat 5 Main[6].val)
  set_next_pc (Word.toBitVec64_poly #v[Main[22], Main[23], Main[24], Main[25]])
  wX_bits op_a (Word.toBitVec64_poly #v[Main[26], Main[27], Main[28], Main[29]])

noncomputable def spec_jal (imm : BitVec 21) (rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  let _ ← execute_JAL imm rd

/-- The Word `#v[4, 0, 0, 0]` is exactly the BitVec `4#64`. Lifted out of
`SP1JAL_correct` so the `Nat.zero_mul + Nat.add_zero` simp pass that produces
the kernel-tripping proof term sits in its own decl. -/
private lemma word_four_eq_bitvec_four {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] :
    Word.toBitVec64_poly (#v[4, 0, 0, 0] : Word (ZMod p)) = (4#64 : BitVec 64) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp_lt : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have h4_val : ((4 : ℕ) : ZMod p).val = 4 := ZMod.val_natCast_of_lt (by omega)
  rw [show (4 : ZMod p) = ((4 : ℕ) : ZMod p) from by push_cast; rfl]
  simp only [Word.toBitVec64_poly, Word.toNat_poly_def, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
    h4_val, ZMod.val_zero, Nat.zero_mul, Nat.add_zero]

/-- Bare-`BitVec` JAL spec-to-sp1 reduction. The full `(spec_jal imm rd).run s` chain —
including `readReg PC` from the inserted state, the match-on-match iota collapse, and
`jump_to (pc + signExtend imm)` via `jump_to_of_mod4_eq_zero` — is performed here at the
bare-`BitVec` level (no `Word (ZMod p)` polymorphism in the proof term), so the kernel
re-check stays within stack bounds. Chip-side `SP1JAL_correct` discharges the `target_word`
+ `link_word` equalities from its `AddOperation.spec_poly` constraints, then `exact`s this
lemma. -/
private lemma jal_spec_eq_sp1 (s : SailState) (hs : SailState.isInitialized s)
    (pc : BitVec 64) (h_pc : s.regs.get? Register.PC = some pc)
    (imm : BitVec 21)
    (target : BitVec 64)
    (h_target : target = pc + BitVec.signExtend 64 imm)
    (h_target_mod4 : target % 4 = 0)
    (rd : BitVec 5) (link : BitVec 64)
    (h_link : rd ≠ 0#5 → link = pc + 4#64) :
    (spec_jal imm (regidx.Regidx rd)).run s =
      (do
        Sail.writeReg Register.nextPC target
        wX_bits (regidx.Regidx rd) link).run s := by
  subst h_target
  -- Derive the `get`-form of `h_pc` (the simp set works in `get?` form but the inserted-state
  -- readReg via `run_readReg_insert_of_ne` returns the `get?`-then-some form which we then
  -- need to collapse via this `get`-form equality).
  have h_pc_get : s.regs.get Register.PC (hs _) = pc := by
    have := (Std.ExtDHashMap.get?_eq_some_get (hs _)).symm.trans h_pc
    exact Option.some.inj this
  -- Unfold spec_jal + execute_JAL. Reads the first `readReg PC` via `read_pc`; the writeReg
  -- + second `readReg PC` (now on inserted state) collapse via `run_readReg_insert_of_ne`.
  simp [spec_jal, execute_JAL, get_next_pc, set_next_pc,
    run_readReg_of_isInitialized _ _ hs, h_pc_get]
  rw [run_readReg_insert_of_ne s (show Register.nextPC ≠ Register.PC from by decide)]
  rw [h_pc]
  dsimp only []
  rw [jump_to_of_mod4_eq_zero _ _ (by clear *- hs; aesop) h_target_mod4]
  simp [Std.ExtDHashMap.insert_insert, EStateM.Result.map, wX_bits]
  -- Case-split on `rd = 0#5`. In the zero case `wX_bits` short-circuits via the `if rd = 0`
  -- guard and both sides reduce to the same `pure ()`-after-insert form; in the nonzero
  -- case, `h_link` substitutes `link` with `pc + 4#64`, matching the spec's `link_address`.
  by_cases hrd : rd = 0#5
  · simp [hrd]
  · rw [h_link hrd]
    match
      h : (EStateM.run (writeReg (reg_idx_to_Register rd) (bitVecToRegidxVal rd (pc + 4#64))))
            { s with regs := s.regs.insert Register.nextPC (pc + BitVec.signExtend 64 imm) } with
    | .ok a s' => cases a; simp [hrd]
    | .error e s' => simp [hrd]

-- Sail-state JAL semantics + AddOperation chain + PC alignment via the ZMod %4 bridge.
-- The kernel-tripping `simp [Std.ExtDHashMap.get_insert, read_pc]` chain is now absorbed
-- by the bare-`BitVec` helper `jal_spec_eq_sp1` above; the chip's only remaining work is
-- discharging the `target` and `link` equalities from the chip's `AddOperation.spec_poly`
-- constraints.
theorem SP1JAL_correct
    (cstrs : (constraints Main).allHold_poly)
    (h_is_real : Main[30] = 1)
    (state_cstrs : (constraints Main).initialState_poly s)
    (hs : SailState.isInitialized s) :
    let op_a := sp1_op_a Main cstrs h_is_real
    let op_b := sp1_op_b Main
    (spec_jal op_b (.Regidx op_a)).run s = (sp1_jal Main).run s := by
  extract_lets op_a op_b
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h_op_a : Main[6].val < 32 := op_a_lt32_of_constraints cstrs h_is_real
  have h32 : (32 : ZMod p).val = 32 := val_32_zmod_p
  have h65 : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
  -- state_cstrs extraction: PC read + AddOperation state-prop.
  simp [SP1ConstraintList.initialState_poly, constraints, SP1Constraint.toStateProp_poly,
    List.Forall, AddOperation.constraints, h_is_real] at state_cstrs
  obtain ⟨read_pc, h⟩ := state_cstrs
  -- h_cstrs extraction.
  simp [SP1ConstraintList.allHold_poly, constraints, SP1Constraint.toProp_poly,
    sub_eq_zero, h_is_real] at cstrs
  have h3 : Main[3] < (65536 : ZMod p) := by simp_all only
  have h4 : Main[4] < (65536 : ZMod p) := by simp_all only
  have h5 : Main[5] < (65536 : ZMod p) := by simp_all only
  have h14 : Main[14] < (65536 : ZMod p) := by simp_all only
  have h15 : Main[15] < (65536 : ZMod p) := by simp_all only
  have h16 : Main[16] < (65536 : ZMod p) := by simp_all only
  have h17 : Main[17] < (65536 : ZMod p) := by simp_all only
  have h3_val : Main[3].val < 65536 := by
    have : Main[3].val < (65536 : ZMod p).val := h3; rwa [h65] at this
  have h4_val : Main[4].val < 65536 := by
    have : Main[4].val < (65536 : ZMod p).val := h4; rwa [h65] at this
  have h5_val : Main[5].val < 65536 := by
    have : Main[5].val < (65536 : ZMod p).val := h5; rwa [h65] at this
  have h14_val : Main[14].val < 65536 := by
    have : Main[14].val < (65536 : ZMod p).val := h14; rwa [h65] at this
  have h15_val : Main[15].val < 65536 := by
    have : Main[15].val < (65536 : ZMod p).val := h15; rwa [h65] at this
  have h16_val : Main[16].val < 65536 := by
    have : Main[16].val < (65536 : ZMod p).val := h16; rwa [h65] at this
  have h17_val : Main[17].val < 65536 := by
    have : Main[17].val < (65536 : ZMod p).val := h17; rwa [h65] at this
  have h_sign_extend : Word.toBitVec64_poly #v[Main[14], Main[15], Main[16], Main[17]] =
      BitVec.signExtend 64 (BitVec.ofNat 21 (Main[14].val + Main[15].val * 65536)) := by
    simp_all only [show (Opcode.ofNat 46) = Opcode.JAL from rfl]
  have hmod4 : (Word.toBitVec64_poly #v[Main[3], Main[4], Main[5], (0 : ZMod p)] +
      Word.toBitVec64_poly #v[Main[14], Main[15], Main[16], Main[17]]) % 4 = 0 := by
    simp
    refine add_mod4_eq_zero_of_mod4_eq_zero ?_ ?_
    · -- pc % 4 = 0 from chip cstrs (active is_real → pc[0] % 4 = 0 via val_mod_4 bridge)
      simp only [Word.toBitVec64_poly, BitVec.ofNat_eq_ofNat, ofNat64_mod_4_eq_zero_iff,
        Word.toNat_poly_def, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, ZMod.val_zero]
      have h_pc_mod_zmod : Main[3] % (4 : ZMod p) = 0 := by simp_all only
      have h_pc_mod : Main[3].val % 4 = 0 :=
        (val_mod_4_eq_zero_iff_zmod _).mp h_pc_mod_zmod
      omega
    · simp only [← h_sign_extend, Word.toBitVec64_poly, BitVec.ofNat_eq_ofNat,
        ofNat64_mod_4_eq_zero_iff, Word.toNat_poly_def, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
      simp_all only [show (Opcode.ofNat 46) = Opcode.JAL from rfl]
  have hmod  := (mul4_means_0_1_are_0 hmod4).2
  have hmod' := (mul4_means_0_1_are_0 hmod4).1
  have h_add_imm : List.Forall SP1Constraint.toProp_poly (AddOperation.constraints
      #v[Main[3], Main[4], Main[5], (0 : ZMod p)]
      #v[Main[14], Main[15], Main[16], Main[17]]
      {value := #v[Main[22], Main[23], Main[24], Main[25]]} 1) := cstrs.1
  have pc_isU64 : Word.isU64_poly #v[Main[3], Main[4], Main[5], (0 : ZMod p)] := by
    apply Word.isU64_of_cases_poly <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · exact h3_val
    · exact h4_val
    · exact h5_val
    · rw [ZMod.val_zero]; omega
  have imm_isU64 : Word.isU64_poly #v[Main[14], Main[15], Main[16], Main[17]] := by
    apply Word.isU64_of_cases_poly <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · exact h14_val
    · exact h15_val
    · exact h16_val
    · exact h17_val
  have h_add' := (AddOperation.spec_poly pc_isU64 imm_isU64 h_add_imm).2
  simp at h_add'
  have hmod4_target :
      Word.toBitVec64_poly #v[Main[22], Main[23], Main[24], Main[25]] % 4 = 0 :=
    h_add' ▸ hmod4
  -- Discharge the `h_link` precondition of `jal_spec_eq_sp1` conditionally on rd ≠ 0.
  have h_link_cond : (BitVec.ofNat 5 Main[6].val : BitVec 5) ≠ 0#5 →
      Word.toBitVec64_poly #v[Main[26], Main[27], Main[28], Main[29]] =
        Word.toBitVec64_poly #v[Main[3], Main[4], Main[5], 0] + 4#64 := by
    intro hrd_ne
    have h6_ne : Main[6] ≠ 0 := by
      intro h0
      apply hrd_ne
      simp [h0, BitVec.ofNat_eq_ofNat]
    have h_add_pc : List.Forall SP1Constraint.toProp_poly (AddOperation.constraints
      #v[Main[3], Main[4], Main[5], (0 : ZMod p)] #v[4, 0, 0, 0]
      {value := #v[Main[26], Main[27], Main[28], Main[29]]} 1) := by aesop
    have h_add_pc' := (AddOperation.spec_poly pc_isU64 Word.four_isU64_poly h_add_pc).2
    simp at h_add_pc'
    rw [word_four_eq_bitvec_four] at h_add_pc'
    exact h_add_pc'
  -- Apply the bare-`BitVec` helper. Goal: `(spec_jal op_b (.Regidx op_a)).run s
  -- = (do set_next_pc target_word; wX_bits (.Regidx rd_word) link_word).run s`.
  -- Bridge `op_a` (`Main[6].val#'_`) to `BitVec.ofNat 5 Main[6].val` and unfold `set_next_pc`.
  have hop_a : op_a = BitVec.ofNat 5 Main[6].val := BitVec.ofNatLT_eq_ofNat ..
  rw [hop_a]
  refine jal_spec_eq_sp1 s hs
    (Word.toBitVec64_poly #v[Main[3], Main[4], Main[5], 0])
    read_pc
    op_b
    (Word.toBitVec64_poly #v[Main[22], Main[23], Main[24], Main[25]])
    ?_ hmod4_target
    (BitVec.ofNat 5 Main[6].val)
    (Word.toBitVec64_poly #v[Main[26], Main[27], Main[28], Main[29]])
    h_link_cond
  rw [h_add', h_sign_extend]
  rfl

end Jal
