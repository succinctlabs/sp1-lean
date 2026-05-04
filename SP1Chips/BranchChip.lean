import SP1Foundations
import SP1Chips.Branch.Constraints

namespace Branch

open Sail SailState BitVec LeanRV64D.Functions

attribute [simp] jump_to assert PreSail.assert ofBool
  zopz0zI_s zopz0zKzJ_s zopz0zKzJ_u zopz0zI_u

-- Top-level lift of the `close_branch_addr_eq` macro: closes the branching-case
-- address equation `PC + signExtend imm = #v[Main[25..27], 0]` from the per-limb
-- chip constraints. Lifting it to a single lemma means the kernel walks the
-- 4-limb-add proof term **once** instead of being re-inlined into each of the
-- 6 `correct_b*` chip bodies. The simp set `[BitVec.add_def, Word.toBitVec64,
-- Word.toNat, ← BitVec.toNat_inj]` is the kernel-clean variant — using the
-- abstract `Word.toNat` (handled by `@[simp] toNat_aux_def`) plus
-- `BitVec.add_def` instead of `Word.toNat_def` + `BitVec.toNat_add` avoids the
-- `_ % 2^64`-bearing proof-term shape that previously required
-- `set_option debug.skipKernelTC true in` (kernel deep-recursion gotcha
-- documented in `docs/GOTCHAS.md`).
set_option maxHeartbeats 4000000 in
-- Trailing `omega` over the per-limb constraints + the inverse-bridge rewrites
-- routinely needs more than the default budget.
lemma branch_addr_eq
    (Main : Vector (Fin KB) 45)
    (h_imm_signExtend :
      Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]]
        = BitVec.signExtend 64 (BitVec.ofNat 13 ↑Main[21]))
    (h_pc_0 : Main[3].val < 65536) (h_pc_1 : Main[4].val < 65536)
    (h_pc_2 : Main[5].val < 65536)
    (h_imm_0 : Main[21].val < 65536) (h_imm_1 : Main[22].val < 65536)
    (h_imm_2 : Main[23].val < 65536) (h_imm_3 : Main[24].val < 65536)
    (h26 : Main[25].val < 65536)
    (h_limb0 : Main[3] + Main[21] = Main[25]
        ∨ Main[3] + Main[21] - Main[25] = (65536 : Fin KB))
    (h_limb1 : (Main[3] + Main[21] - Main[25]) * (65536 : Fin KB)⁻¹ + Main[4] + Main[22] = Main[26]
        ∨ (Main[3] + Main[21] - Main[25]) * (65536 : Fin KB)⁻¹ + Main[4] + Main[22] - Main[26]
            = (65536 : Fin KB))
    (h_limb2 : ((Main[3] + Main[21] - Main[25]) * (65536 : Fin KB)⁻¹ + Main[4] + Main[22] - Main[26])
              * (65536 : Fin KB)⁻¹ + Main[5] + Main[23] = Main[27]
        ∨ ((Main[3] + Main[21] - Main[25]) * (65536 : Fin KB)⁻¹ + Main[4] + Main[22] - Main[26])
              * (65536 : Fin KB)⁻¹ + Main[5] + Main[23] - Main[27] = (65536 : Fin KB))
    (h_limb3 : (((Main[3] + Main[21] - Main[25]) * (65536 : Fin KB)⁻¹ + Main[4] + Main[22] - Main[26])
              * (65536 : Fin KB)⁻¹ + Main[5] + Main[23] - Main[27]) * (65536 : Fin KB)⁻¹
              + Main[24] = 0
        ∨ (((Main[3] + Main[21] - Main[25]) * (65536 : Fin KB)⁻¹ + Main[4] + Main[22] - Main[26])
              * (65536 : Fin KB)⁻¹ + Main[5] + Main[23] - Main[27]) * (65536 : Fin KB)⁻¹
              + Main[24] = (65536 : Fin KB))
    (h_bound_checks : (Main[25] * (4 : Fin KB)⁻¹).val < 16384
        ∧ Main[26].val < 65536 ∧ Main[27].val < 65536) :
    Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0]
        + BitVec.signExtend 64 (BitVec.ofNat 13 ↑Main[21])
      = Word.toBitVec64 #v[Main[25], Main[26], Main[27], 0] := by
  rw [← h_imm_signExtend]
  simp only [← inv_4BB_eq', ← inv_65536BB_eq']
    at h_bound_checks h_limb0 h_limb1 h_limb2 h_limb3
  simp [BitVec.add_def, Word.toBitVec64, Word.toNat, ← BitVec.toNat_inj]
  omega

-- Thin macro wrapper so the 6 `correct_b*` proofs keep their existing call site;
-- expands to a single `exact branch_addr_eq …` term application.
set_option hygiene false in
local macro "close_branch_addr_eq" : tactic => `(tactic| (
  unfold imm
  rw [sp1_imm]
  exact branch_addr_eq Main reader_cstrs.1.1.1 h_pc_0 h_pc_1 h_pc_2
    h_imm_0 h_imm_1 h_imm_2 h_imm_3 h26 h_limb0 h_limb1 h_limb2 h_limb3 h_bound_checks))

variable (Main : Vector (Fin KB) 45)

def sp1_op_a : BitVec 5 := BitVec.ofNat 5 Main[6]

def sp1_op_b : BitVec 5 := BitVec.ofNat 5 Main[14]

def sp1_imm : BitVec 13 := BitVec.ofNat 13 Main[21]

def sp1_branch : SailM ExecutionResult := do
  writeReg Register.nextPC (Word.toBitVec64 #v[Main[25], Main[26], Main[27], 0])
  pure RETIRE_SUCCESS

section poly_defs

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 45)

def sp1_op_a_poly : BitVec 5 := BitVec.ofNat 5 Main[6].val

def sp1_op_b_poly : BitVec 5 := BitVec.ofNat 5 Main[14].val

def sp1_imm_poly : BitVec 13 := BitVec.ofNat 13 Main[21].val

def sp1_branch_poly : SailM ExecutionResult := do
  writeReg Register.nextPC (Word.toBitVec64_poly #v[Main[25], Main[26], Main[27], 0])
  pure RETIRE_SUCCESS

end poly_defs

namespace BEQ

noncomputable def spec_beq (imm : (BitVec 13)) (rs2 : regidx) (rs1 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_BTYPE imm rs2 rs1 bop.BEQ

set_option maxHeartbeats 8000000 in
-- correctness proof across all 6 branch-opcode cases
theorem correct_beq
    (Main : Vector (Fin KB) 45)
    (s : SailState) (hs : s.isInitialized)
    (h_is_beq : Main[28] = 1)
    (cstrs : (constraints Main).allHold)
    (state_cstrs : (constraints Main).initialState s) :
    let imm := sp1_imm Main
    let op_b := .Regidx (sp1_op_b Main)
    let op_a := .Regidx (sp1_op_a Main)
    (spec_beq imm op_b op_a).run s = (sp1_branch Main).run s := by
  extract_lets imm op_b op_a
  have h_is_real : is_real Main := by simp [is_real, h_is_beq]
  have h_sign_extend := eq_signExtend_of_is_real Main cstrs h_is_real
  have h_next_pc_is_mul4 : (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] +
    BitVec.signExtend 64 imm) % 4 = 0 := add_signExtend_of_constraints Main cstrs h_is_real
  obtain ⟨h_next_pc_b0, h_next_pc_b1⟩ := mul4_means_0_1_are_0 h_next_pc_is_mul4
  obtain ⟨h_28, h_30, h_31, h_32, h_33⟩ := (single_op Main cstrs).1 h_is_beq
  simp [SP1ConstraintList.allHold, Branch.constraints] at cstrs
  obtain ⟨_, reader_cstrs, lt_cstrs, chip_cstrs⟩ := cstrs
  -- simplify reader constraints
  simp [ITypeReaderImmutable.constraints, SP1Constraint.toProp,
    h_is_beq, h_28, h_30, h_31, h_32, h_33, Opcode.ofNat, Nat.ble] at reader_cstrs
  -- Introduce bounds on values
  have op_a_is_u64 : Word.isU64 #v[Main[7], Main[8], Main[9], Main[10]] := by simp_all only
  have op_b_is_u64 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := by simp_all only
  let op_a_val := Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]]
  let op_b_val := Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]
  have h6 : Main[6] < 32 := by aesop
  have h14 : Main[14] < 32 := by aesop
  have h_imm_0 : Main[21].val < 65536 := by change Main[21] < 65536; simp_all only
  have h_imm_1 : Main[22].val < 65536 := by change Main[22] < 65536; simp_all only
  have h_imm_2 : Main[23].val < 65536 := by change Main[23] < 65536; simp_all only
  have h_imm_3 : Main[24].val < 65536 := by change Main[24] < 65536; simp_all only
  have h_imm_is_u64 : Main[21].val + Main[22].val * 65536 + ↑Main[23] * 4294967296 + ↑Main[24] * 281474976710656 < 2^64 := by omega
  have op_c_is_u64 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := Word.isU64_of_cases h_imm_0 h_imm_1 h_imm_2 h_imm_3
  have h_pc_0 : Main[3].val < 65536 := by change Main[3] < 65536; aesop
  have h_pc_1 : Main[4].val < 65536 := by change Main[4] < 65536; aesop
  have h_pc_2 : Main[5].val < 65536 := by change Main[5] < 65536; aesop
  have h_pc_is_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 < 2^64 := by omega
  have h_pc_add4_is_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 + 4 < 2^64 := by omega
  have h_nextpc_is_u64 : Main[25].val + Main[26].val * 65536 + Main[27].val * 4294967296 < 2^64 := by omega
  simp_all
  -- simplify lt operation constraints
  have spec_lt := LtOperationSigned.spec.branch op_a_is_u64 op_b_is_u64 lt_cstrs
  clear lt_cstrs
  simp [LtOperationSigned.spec.branch.def] at spec_lt
  -- simplify state constraints
  simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall,
    CPUState.constraints, ITypeReaderImmutable.constraints, LtOperationSigned.constraints,
    LtOperationUnsigned.constraints, U16MSBOperation.constraints, U16CompareOperation.constraints,
    h_is_beq, h6, h14, h_28, h_30, h_31, h_32, h_33, Opcode.ofNat, Nat.ble] at state_cstrs
  obtain ⟨h_pc_read, h_op_a_read, h_op_b_read⟩ := state_cstrs
  specialize h_op_a_read
  specialize h_op_b_read
  -- simplify main goal
  simp [spec_beq, sp1_branch, execute_BTYPE]
  rw [run_readReg]
  simp [h_pc_read]
  simp_all only [BitVec.ofNatLT_eq_ofNat]
  simp [op_a, sp1_op_a, h_op_a_read, op_b, sp1_op_b, h_op_b_read]
  by_cases h_eq : op_a_val = op_b_val <;> simp [op_a_val, op_b_val] at h_eq
  · simp [h_eq]
    rw [run_readReg]
    simp [Std.ExtDHashMap.get?_insert, h_pc_read, h_next_pc_b0, h_next_pc_b1]
    rw [SailME_run_readReg_map_writeReg _ Register.misa Register.nextPC
      (by simp [Std.ExtDHashMap.get?_insert]; exact hs Register.misa) _ _]
    simp only [Std.ExtDHashMap.insert_insert]
    have h_is_eq : Main[36] + Main[37] + Main[38] + Main[39] = 0 := by
      clear *- spec_lt h_eq h_30 h_31; simp_all
    have h_is_branching : Main[34] = 1 := by
      clear *- h_is_eq chip_cstrs; simp_all [sub_eq_zero]
    simp [h_is_branching, sub_eq_zero, h_is_eq] at chip_cstrs
    obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs
    have h26 : Main[25].val < 65536 := by
      apply lt_65536_of_mul_inv_4_lt
      exact h_bound_checks.1
    have h_addr_eq : Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] + BitVec.signExtend 64 imm
        = Word.toBitVec64 #v[Main[25], Main[26], Main[27], 0] := by
      close_branch_addr_eq
    rw [h_addr_eq]
  · have h_is_neq : (Main[36] + Main[37] + Main[38] + Main[39]) = 1 := by
      clear *- spec_lt h_eq h_30 h_31; simp_all
    simp [h_is_neq, sub_eq_zero] at chip_cstrs
    have h_is_branching : Main[34] = 0 := by
      clear *- h_is_neq chip_cstrs; simp_all [sub_eq_zero]
    simp [h_is_branching] at chip_cstrs
    simp [h_eq]
    obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs
    have h26 : Main[25].val < 65536 := by
      apply lt_65536_of_mul_inv_4_lt
      exact h_bound_checks.1
    simp only [← inv_4BB_eq', ← inv_65536BB_eq'] at h_bound_checks h_limb0 h_limb1 h_limb2 h_limb3
    simp [BitVec.add_def, Word.toBitVec64, Word.toNat, ← BitVec.toNat_inj]
    clear * - h26 h_pc_0 h_pc_1 h_pc_2 h_bound_checks h_limb0 h_limb1 h_limb2 h_limb3
    omega

set_option maxHeartbeats 16000000 in
-- Polymorphic counterpart of `correct_beq`. Mirrors the concrete proof
-- but threads `single_op_poly`, `eq_signExtend_of_is_real_poly`,
-- `add_signExtend_of_constraints_poly`, `branch_addr_eq_poly`, and
-- `pc_plus_4_eq_poly` through the same skeleton. Heartbeats elevated
-- for the post-state-cstrs `simp_all` chain (ZMod cast normalization
-- runs ~3× the concrete budget). `skipKernelTC` for `BitVec.toNat_add`
-- kernel deep-recursion in branch_addr_eq_poly's body.
set_option debug.skipKernelTC true in
theorem correct_beq_poly
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (Main : Vector (ZMod p) 45)
    (s : SailState) (hs : s.isInitialized)
    (h_is_beq : Main[28] = 1)
    (cstrs : (Branch.constraints Main).allHold_poly)
    (state_cstrs : (Branch.constraints Main).initialState_poly s) :
    let imm := sp1_imm_poly Main
    let op_b := regidx.Regidx (sp1_op_b_poly Main)
    let op_a := regidx.Regidx (sp1_op_a_poly Main)
    (spec_beq imm op_b op_a).run s = (sp1_branch_poly Main).run s := by
  extract_lets imm op_b op_a
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp_lt : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have h_is_real : is_real_poly Main := Or.inl h_is_beq
  obtain ⟨h_29, h_30, h_31, h_32, h_33⟩ := (single_op_poly Main cstrs).1 h_is_beq
  have h_sign_extend := eq_signExtend_of_is_real_poly Main cstrs h_is_real
  have h_next_pc_is_mul4 := add_signExtend_of_constraints_poly Main cstrs h_is_real
  obtain ⟨h_next_pc_b0, h_next_pc_b1⟩ := mul4_means_0_1_are_0 h_next_pc_is_mul4
  -- destructure cstrs into the 4 sub-lists
  simp [SP1ConstraintList.allHold_poly, Branch.constraints] at cstrs
  obtain ⟨_, reader_cstrs, lt_cstrs, chip_cstrs⟩ := cstrs
  -- cast lemmas for opcode/limb literals
  have h32_val : (32 : ZMod p).val = 32 := val_32_zmod_p
  have h65_val : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
  have h40_lt : (40 : ℕ) < p := by omega
  have h40_val : (40 : ZMod p).val = 40 := ZMod.val_natCast_of_lt h40_lt
  -- simplify reader constraints (BEQ -> opcode 40)
  simp [ITypeReaderImmutable.constraints, SP1Constraint.toProp_poly,
    h_is_beq, h_29, h_30, h_31, h_32, h_33, Opcode.ofNat, Nat.ble, h40_val] at reader_cstrs
  -- bounds from reader cstrs
  have op_a_is_u64 : Word.isU64_poly #v[Main[7], Main[8], Main[9], Main[10]] := by simp_all only
  have op_b_is_u64 : Word.isU64_poly #v[Main[15], Main[16], Main[17], Main[18]] := by simp_all only
  let op_a_val := Word.toBitVec64_poly #v[Main[7], Main[8], Main[9], Main[10]]
  let op_b_val := Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]
  have h6_zmod : Main[6] < (32 : ZMod p) := by simp_all only
  have h14_zmod : Main[14] < (32 : ZMod p) := by simp_all only
  have h6 : Main[6].val < 32 := by
    have : Main[6].val < (32 : ZMod p).val := h6_zmod; rwa [h32_val] at this
  have h14 : Main[14].val < 32 := by
    have : Main[14].val < (32 : ZMod p).val := h14_zmod; rwa [h32_val] at this
  have h_imm_0_z : Main[21] < (65536 : ZMod p) := by simp_all only
  have h_imm_1_z : Main[22] < (65536 : ZMod p) := by simp_all only
  have h_imm_2_z : Main[23] < (65536 : ZMod p) := by simp_all only
  have h_imm_3_z : Main[24] < (65536 : ZMod p) := by simp_all only
  have h_imm_0 : Main[21].val < 65536 := by
    have : Main[21].val < (65536 : ZMod p).val := h_imm_0_z; rwa [h65_val] at this
  have h_imm_1 : Main[22].val < 65536 := by
    have : Main[22].val < (65536 : ZMod p).val := h_imm_1_z; rwa [h65_val] at this
  have h_imm_2 : Main[23].val < 65536 := by
    have : Main[23].val < (65536 : ZMod p).val := h_imm_2_z; rwa [h65_val] at this
  have h_imm_3 : Main[24].val < 65536 := by
    have : Main[24].val < (65536 : ZMod p).val := h_imm_3_z; rwa [h65_val] at this
  have h_pc_0_z : Main[3] < (65536 : ZMod p) := by simp_all only
  have h_pc_1_z : Main[4] < (65536 : ZMod p) := by simp_all only
  have h_pc_2_z : Main[5] < (65536 : ZMod p) := by simp_all only
  have h_pc_0 : Main[3].val < 65536 := by
    have : Main[3].val < (65536 : ZMod p).val := h_pc_0_z; rwa [h65_val] at this
  have h_pc_1 : Main[4].val < 65536 := by
    have : Main[4].val < (65536 : ZMod p).val := h_pc_1_z; rwa [h65_val] at this
  have h_pc_2 : Main[5].val < 65536 := by
    have : Main[5].val < (65536 : ZMod p).val := h_pc_2_z; rwa [h65_val] at this
  -- LtOperationSigned spec.branch_poly expects `is_real = 1` literal in constraints.
  -- Rewrite the chip's is_real sum to 1 first, then is_signed (Main[30]+Main[31]) to 0.
  have h_is_real_one :
      Main[28] + Main[29] + Main[30] + Main[31] + Main[32] + Main[33] = (1 : ZMod p) := by
    rw [h_is_beq, h_29, h_30, h_31, h_32, h_33]; ring
  rw [h_is_real_one] at lt_cstrs
  have h_is_signed_eq : (Main[30] + Main[31] : ZMod p) = 0 := by rw [h_30, h_31]; ring
  rw [h_is_signed_eq] at lt_cstrs
  have spec_lt := LtOperationSigned.spec.branch_poly op_a_is_u64 op_b_is_u64 lt_cstrs
  clear lt_cstrs
  -- Take the is_signed = 0 branch (BEQ uses unsigned-style equality only).
  -- Defer extraction of iff bodies + Word↔BV bridge until inside each by_cases arm,
  -- so that the upcoming `simp_all only [BitVec.ofNatLT_eq_ofNat]` doesn't rewrite
  -- the iff RHS (using iff hyps as simp lemmas would chain `Word.eq ↔ BV.eq`
  -- with `BV.eq ↔ flags-zero-quad`, breaking the bridge's expected shape).
  have spec_lt_unsigned := spec_lt.1 rfl
  -- state cstrs: extract PC read + op_a/op_b reads
  simp [SP1ConstraintList.initialState_poly, Branch.constraints, SP1Constraint.toStateProp_poly,
    List.Forall, CPUState.constraints, ITypeReaderImmutable.constraints,
    LtOperationSigned.constraints, LtOperationUnsigned.constraints,
    U16MSBOperation.constraints, U16CompareOperation.constraints,
    h_is_beq, h6, h14, h_29, h_30, h_31, h_32, h_33,
    Opcode.ofNat, Nat.ble, h40_val] at state_cstrs
  obtain ⟨h_pc_read, h_op_a_read, h_op_b_read⟩ := state_cstrs
  specialize h_op_a_read
  specialize h_op_b_read
  -- main goal: bridge spec_beq through to sp1_branch_poly
  simp [spec_beq, sp1_branch_poly, execute_BTYPE]
  rw [run_readReg]
  simp [h_pc_read]
  simp only [BitVec.ofNatLT_eq_ofNat] at h_op_a_read h_op_b_read
  simp [op_a, sp1_op_a_poly, h_op_a_read, op_b, sp1_op_b_poly, h_op_b_read]
  -- Local helpers used by both arms — inlined to avoid simp-leakage from the
  -- preceding `simp_all only [...]`-style steps. Word ↔ BV equality bridge
  -- under isU64_poly bounds.
  obtain ⟨h_eq_iff, h_neq_iff, _h_lt_ite⟩ := spec_lt_unsigned
  have h_BV_to_Word :
      Word.toBitVec64_poly #v[Main[7], Main[8], Main[9], Main[10]] =
        Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] →
      (#v[Main[7], Main[8], Main[9], Main[10]] : Word (ZMod p)) =
        #v[Main[15], Main[16], Main[17], Main[18]] := by
    intro h
    have h_a := Word.toBitVec64_poly_toNat_poly op_a_is_u64
    have h_b := Word.toBitVec64_poly_toNat_poly op_b_is_u64
    have h_nat : Word.toNat_poly (#v[Main[7], Main[8], Main[9], Main[10]] : Word (ZMod p)) =
        Word.toNat_poly #v[Main[15], Main[16], Main[17], Main[18]] := by
      rw [← h_a, ← h_b, h]
    have h7_lt : Main[7].val < 65536 := op_a_is_u64 0
    have h8_lt : Main[8].val < 65536 := op_a_is_u64 1
    have h9_lt : Main[9].val < 65536 := op_a_is_u64 2
    have h10_lt : Main[10].val < 65536 := op_a_is_u64 3
    have h15_lt : Main[15].val < 65536 := op_b_is_u64 0
    have h16_lt : Main[16].val < 65536 := op_b_is_u64 1
    have h17_lt : Main[17].val < 65536 := op_b_is_u64 2
    have h18_lt : Main[18].val < 65536 := op_b_is_u64 3
    simp only [Word.toNat_poly_def, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ] at h_nat
    have h7_eq : Main[7].val = Main[15].val := by omega
    have h8_eq : Main[8].val = Main[16].val := by omega
    have h9_eq : Main[9].val = Main[17].val := by omega
    have h10_eq : Main[10].val = Main[18].val := by omega
    have h7 : Main[7] = Main[15] := ZMod.val_injective _ h7_eq
    have h8 : Main[8] = Main[16] := ZMod.val_injective _ h8_eq
    have h9 : Main[9] = Main[17] := ZMod.val_injective _ h9_eq
    have h10 : Main[10] = Main[18] := ZMod.val_injective _ h10_eq
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [h7, h8, h9, h10]
  by_cases h_eq : op_a_val = op_b_val <;> simp only [op_a_val, op_b_val] at h_eq
  · -- branching arm
    simp [h_eq]
    rw [run_readReg]
    -- Unfold `imm` so h_next_pc_b0/b1 (in terms of `BitVec.ofNat 13 Main[21].val`)
    -- can match the goal's `BitVec.signExtend 64 imm` subterm.
    simp only [show imm = BitVec.ofNat 13 Main[21].val from rfl]
    simp [Std.ExtDHashMap.get?_insert, h_pc_read, h_next_pc_b0, h_next_pc_b1]
    rw [SailME_run_readReg_map_writeReg _ Register.misa Register.nextPC
      (by simp [Std.ExtDHashMap.get?_insert]; exact hs Register.misa) _ _]
    simp only [Std.ExtDHashMap.insert_insert]
    have h_word_eq : (#v[Main[7], Main[8], Main[9], Main[10]] : Word (ZMod p)) =
        #v[Main[15], Main[16], Main[17], Main[18]] := h_BV_to_Word h_eq
    have h_flags_zero_quad := h_eq_iff.mp h_word_eq
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ] at h_flags_zero_quad
    have h_flags_zero : Main[36] + Main[37] + Main[38] + Main[39] = 0 := by
      obtain ⟨h36, h37, h38, h39⟩ := h_flags_zero_quad
      rw [h36, h37, h38, h39]; ring
    have h_is_branching : Main[34] = 1 := by
      clear *- h_flags_zero chip_cstrs h_is_beq h_29 h_30 h_31 h_32 h_33
      simp_all [sub_eq_zero]
    simp [h_is_branching, sub_eq_zero, h_flags_zero,
      h_is_beq, h_29, h_30, h_31, h_32, h_33] at chip_cstrs
    obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs
    have h14_lt : (14 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    have h14_val : (14 : ZMod p).val = 14 := ZMod.val_natCast_of_lt h14_lt
    have h25 : Main[25].val < 65536 := by
      apply lt_65536_of_mul_inv_4_lt_poly
      have h := h_bound_checks.1
      rw [h14_val] at h
      change _ < 16384 at h
      exact h
    have h26 : Main[26].val < 65536 := h_bound_checks.2.1
    have h27 : Main[27].val < 65536 := h_bound_checks.2.2
    have h_65_ne : (65536 : ZMod p) ≠ 0 := val_65536_ne_zero
    -- Bridge each carry from the chip's messy disjunction form
    -- `((eq form ∨ 65536 = 0) ∨ (a - b) * 65536⁻¹ = 1)` to the canonical
    -- `(a - b) * 65536⁻¹ = 0 ∨ ... = 1` form expected by branch_addr_eq_poly.
    have h_limb0' : (Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ = 0
        ∨ (Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ = 1 := by
      rcases h_limb0 with (h | h) | h
      · left
        have hsub : Main[3] + Main[21] - Main[25] = 0 := by linear_combination h
        rw [hsub]; ring
      · exact absurd h h_65_ne
      · right; exact h
    have h_limb1' :
        ((Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22] - Main[26])
                * (65536 : ZMod p)⁻¹ = 0
        ∨ ((Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22] - Main[26])
                * (65536 : ZMod p)⁻¹ = 1 := by
      rcases h_limb1 with (h | h) | h
      · left
        have hsub : (Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22]
                      - Main[26] = 0 := by linear_combination h
        rw [hsub]; ring
      · exact absurd h h_65_ne
      · right; exact h
    have h_limb2' :
        (((Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22] - Main[26])
                  * (65536 : ZMod p)⁻¹ + Main[5] + Main[23] - Main[27]) * (65536 : ZMod p)⁻¹ = 0
        ∨ (((Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22] - Main[26])
                  * (65536 : ZMod p)⁻¹ + Main[5] + Main[23] - Main[27]) * (65536 : ZMod p)⁻¹ = 1
        := by
      rcases h_limb2 with (h | h) | h
      · left
        have hsub : ((Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22]
                      - Main[26]) * (65536 : ZMod p)⁻¹ + Main[5] + Main[23] - Main[27] = 0 := by
          linear_combination h
        rw [hsub]; ring
      · exact absurd h h_65_ne
      · right; exact h
    have h_limb3' :
        ((((Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22] - Main[26])
                  * (65536 : ZMod p)⁻¹ + Main[5] + Main[23] - Main[27]) * (65536 : ZMod p)⁻¹
                + Main[24]) * (65536 : ZMod p)⁻¹ = 0
        ∨ ((((Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22] - Main[26])
                  * (65536 : ZMod p)⁻¹ + Main[5] + Main[23] - Main[27]) * (65536 : ZMod p)⁻¹
                + Main[24]) * (65536 : ZMod p)⁻¹ = 1 := by
      rcases h_limb3 with (h | h) | h
      · left
        have hsub : (((Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22]
                      - Main[26]) * (65536 : ZMod p)⁻¹ + Main[5] + Main[23] - Main[27])
                      * (65536 : ZMod p)⁻¹ + Main[24] = 0 := by linear_combination h
        rw [hsub]; ring
      · exact absurd h h_65_ne
      · right; exact h
    have h_addr_eq :
        Word.toBitVec64_poly #v[Main[3], Main[4], Main[5], (0 : ZMod p)] +
            BitVec.signExtend 64 (BitVec.ofNat 13 Main[21].val) =
          Word.toBitVec64_poly #v[Main[25], Main[26], Main[27], (0 : ZMod p)] :=
      branch_addr_eq_poly Main h_sign_extend h_pc_0 h_pc_1 h_pc_2
        h_imm_0 h_imm_1 h_imm_2 h_imm_3 h25 h26 h27 h_limb0' h_limb1' h_limb2' h_limb3'
    rw [h_addr_eq]
  · -- non-branching arm — derive h_is_branching first via two-step simp like concrete,
    -- then pass single simp identical to branching arm so both produce the same chip_cstrs shape.
    have h_word_ne : ¬ (#v[Main[7], Main[8], Main[9], Main[10]] : Word (ZMod p)) =
        #v[Main[15], Main[16], Main[17], Main[18]] := by
      intro h_word_eq; apply h_eq
      exact congr_arg Word.toBitVec64_poly h_word_eq
    have h_flags_one : Main[36] + Main[37] + Main[38] + Main[39] = 1 := h_neq_iff.mp h_word_ne
    have h_is_branching : Main[34] = 0 := by
      have chip_tmp := chip_cstrs
      clear *- h_flags_one chip_tmp h_is_beq h_29 h_30 h_31 h_32 h_33
      simp_all [sub_eq_zero]
    simp [h_is_branching, sub_eq_zero, h_flags_one,
      h_is_beq, h_29, h_30, h_31, h_32, h_33] at chip_cstrs
    simp [h_eq]
    obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs
    have h14_lt : (14 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    have h14_val : (14 : ZMod p).val = 14 := ZMod.val_natCast_of_lt h14_lt
    have h25 : Main[25].val < 65536 := by
      apply lt_65536_of_mul_inv_4_lt_poly
      have h := h_bound_checks.1
      rw [h14_val] at h
      change _ < 16384 at h
      exact h
    have h26 : Main[26].val < 65536 := h_bound_checks.2.1
    have h27 : Main[27].val < 65536 := h_bound_checks.2.2
    have h_pc4_eq :
        Word.toBitVec64_poly #v[Main[3], Main[4], Main[5], (0 : ZMod p)] + 4#64 =
          Word.toBitVec64_poly #v[Main[25], Main[26], Main[27], (0 : ZMod p)] :=
      pc_plus_4_eq_poly_chip Main h_pc_0 h_pc_1 h_pc_2 h25 h26 h27
        h_limb0 h_limb1 h_limb2 h_limb3
    rw [h_pc4_eq]

end BEQ

namespace BNE

noncomputable def spec_bne (imm : (BitVec 13)) (rs2 : regidx) (rs1 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_BTYPE imm rs2 rs1 bop.BNE

set_option maxHeartbeats 2000000 in
-- correctness proof across all 6 branch-opcode cases
theorem correct_bne
    (Main : Vector (Fin KB) 45)
    (s : SailState) (hs : s.isInitialized)
    (h_is_bne : Main[29] = 1)
    (cstrs : (constraints Main).allHold)
    (state_cstrs : (constraints Main).initialState s) :
    let imm := sp1_imm Main
    let op_b := .Regidx (sp1_op_b Main)
    let op_a := .Regidx (sp1_op_a Main)
    (spec_bne imm op_b op_a).run s = (sp1_branch Main).run s := by
  extract_lets imm op_b op_a
  have h_is_real : is_real Main := by simp [is_real, h_is_bne]
  have h_sign_extend := eq_signExtend_of_is_real Main cstrs h_is_real
  have h_next_pc_is_mul4 : (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] +
    BitVec.signExtend 64 imm) % 4 = 0 := add_signExtend_of_constraints Main cstrs h_is_real
  obtain ⟨h_next_pc_b0, h_next_pc_b1⟩ := mul4_means_0_1_are_0 h_next_pc_is_mul4
  obtain ⟨h_28, h_30, h_31, h_32, h_33⟩ := (single_op Main cstrs).2.1 h_is_bne
  simp [SP1ConstraintList.allHold, Branch.constraints] at cstrs
  obtain ⟨_, reader_cstrs, lt_cstrs, chip_cstrs⟩ := cstrs
  -- simplify reader constraints
  simp [ITypeReaderImmutable.constraints, SP1Constraint.toProp,
    h_is_bne, h_28, h_30, h_31, h_32, h_33, Opcode.ofNat, Nat.ble] at reader_cstrs
  -- Introduce bounds on values
  have op_a_is_u64 : Word.isU64 #v[Main[7], Main[8], Main[9], Main[10]] := by simp_all only
  have op_b_is_u64 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := by simp_all only
  let op_a_val := Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]]
  let op_b_val := Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]
  have h6 : Main[6] < 32 := by aesop
  have h14 : Main[14] < 32 := by aesop
  have h_imm_0 : Main[21].val < 65536 := by change Main[21] < 65536; simp_all only
  have h_imm_1 : Main[22].val < 65536 := by change Main[22] < 65536; simp_all only
  have h_imm_2 : Main[23].val < 65536 := by change Main[23] < 65536; simp_all only
  have h_imm_3 : Main[24].val < 65536 := by change Main[24] < 65536; simp_all only
  have h_imm_is_u64 : Main[21].val + Main[22].val * 65536 + ↑Main[23] * 4294967296 + ↑Main[24] * 281474976710656 < 2^64 := by omega
  have op_c_is_u64 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := Word.isU64_of_cases h_imm_0 h_imm_1 h_imm_2 h_imm_3
  have h_pc_0 : Main[3].val < 65536 := by change Main[3] < 65536; aesop
  have h_pc_1 : Main[4].val < 65536 := by change Main[4] < 65536; aesop
  have h_pc_2 : Main[5].val < 65536 := by change Main[5] < 65536; aesop
  have h_pc_is_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 < 2^64 := by omega
  have h_pc_add4_is_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 + 4 < 2^64 := by omega
  have h_nextpc_is_u64 : Main[25].val + Main[26].val * 65536 + Main[27].val * 4294967296 < 2^64 := by omega
  simp_all
  -- simplify lt operation constraints
  have spec_lt := LtOperationSigned.spec.branch op_a_is_u64 op_b_is_u64 lt_cstrs
  clear lt_cstrs
  simp [LtOperationSigned.spec.branch.def] at spec_lt
  -- simplify state constraints
  simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall,
    CPUState.constraints, ITypeReaderImmutable.constraints, LtOperationSigned.constraints,
    LtOperationUnsigned.constraints, U16MSBOperation.constraints, U16CompareOperation.constraints,
    h_is_bne, h6, h14, h_28, h_30, h_31, h_32, h_33, Opcode.ofNat, Nat.ble] at state_cstrs
  obtain ⟨h_pc_read, h_op_a_read, h_op_b_read⟩ := state_cstrs
  specialize h_op_a_read
  specialize h_op_b_read
  -- simplify main goal
  simp [spec_bne, sp1_branch, execute_BTYPE]
  rw [run_readReg]
  simp [h_pc_read]
  simp_all only [BitVec.ofNatLT_eq_ofNat]
  simp [op_a, sp1_op_a, h_op_a_read, op_b, sp1_op_b, h_op_b_read]
  by_cases h_eq : op_a_val ≠ op_b_val <;> simp [op_a_val, op_b_val] at h_eq
  · simp [h_eq]
    rw [run_readReg]
    simp [Std.ExtDHashMap.get?_insert, h_pc_read, h_next_pc_b0, h_next_pc_b1]
    rw [SailME_run_readReg_map_writeReg _ Register.misa Register.nextPC
      (by simp [Std.ExtDHashMap.get?_insert]; exact hs Register.misa) _ _]
    simp only [Std.ExtDHashMap.insert_insert]
    have h_is_eq : Main[36] + Main[37] + Main[38] + Main[39] = 1 := by
      clear *- spec_lt h_eq h_30 h_31; simp_all
    have h_is_branching : Main[34] = 1 := by
      clear *- h_is_eq chip_cstrs; simp_all [sub_eq_zero]
    simp [h_is_branching, sub_eq_zero, h_is_eq] at chip_cstrs
    obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs
    have h26 : Main[25].val < 65536 := by
      apply lt_65536_of_mul_inv_4_lt
      exact h_bound_checks.1
    have h_addr_eq : Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] + BitVec.signExtend 64 imm
        = Word.toBitVec64 #v[Main[25], Main[26], Main[27], 0] := by
      close_branch_addr_eq
    rw [h_addr_eq]
  · have h_is_neq : (Main[36] + Main[37] + Main[38] + Main[39]) = 0 := by
      clear *- spec_lt h_eq h_30 h_31; simp_all
    simp [h_is_neq, sub_eq_zero] at chip_cstrs
    have h_is_branching : Main[34] = 0 := by
      clear *- chip_cstrs; simp_all [sub_eq_zero]
    simp [h_is_branching] at chip_cstrs
    simp [h_eq]
    obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs
    have h26 : Main[25].val < 65536 := by
      apply lt_65536_of_mul_inv_4_lt
      exact h_bound_checks.1
    simp only [← inv_4BB_eq', ← inv_65536BB_eq'] at h_bound_checks h_limb0 h_limb1 h_limb2 h_limb3
    simp [BitVec.add_def, Word.toBitVec64, Word.toNat, ← BitVec.toNat_inj]
    clear * - h26 h_pc_0 h_pc_1 h_pc_2 h_bound_checks h_limb0 h_limb1 h_limb2 h_limb3
    omega

set_option maxHeartbeats 16000000 in
-- Polymorphic counterpart of `correct_bne`. Same structure as
-- `correct_beq_poly` but with NEQ/EQ polarity flipped: branching arm
-- corresponds to NEQ (sum = 1), non-branching to EQ (sum = 0).
set_option debug.skipKernelTC true in
theorem correct_bne_poly
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (Main : Vector (ZMod p) 45)
    (s : SailState) (hs : s.isInitialized)
    (h_is_bne : Main[29] = 1)
    (cstrs : (Branch.constraints Main).allHold_poly)
    (state_cstrs : (Branch.constraints Main).initialState_poly s) :
    let imm := sp1_imm_poly Main
    let op_b := regidx.Regidx (sp1_op_b_poly Main)
    let op_a := regidx.Regidx (sp1_op_a_poly Main)
    (spec_bne imm op_b op_a).run s = (sp1_branch_poly Main).run s := by
  extract_lets imm op_b op_a
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp_lt : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have h_is_real : is_real_poly Main := Or.inr (Or.inl h_is_bne)
  obtain ⟨h_28, h_30, h_31, h_32, h_33⟩ := (single_op_poly Main cstrs).2.1 h_is_bne
  have h_sign_extend := eq_signExtend_of_is_real_poly Main cstrs h_is_real
  have h_next_pc_is_mul4 := add_signExtend_of_constraints_poly Main cstrs h_is_real
  obtain ⟨h_next_pc_b0, h_next_pc_b1⟩ := mul4_means_0_1_are_0 h_next_pc_is_mul4
  simp [SP1ConstraintList.allHold_poly, Branch.constraints] at cstrs
  obtain ⟨_, reader_cstrs, lt_cstrs, chip_cstrs⟩ := cstrs
  have h32_val : (32 : ZMod p).val = 32 := val_32_zmod_p
  have h65_val : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
  have h41_lt : (41 : ℕ) < p := by omega
  have h41_val : (41 : ZMod p).val = 41 := ZMod.val_natCast_of_lt h41_lt
  simp [ITypeReaderImmutable.constraints, SP1Constraint.toProp_poly,
    h_is_bne, h_28, h_30, h_31, h_32, h_33, Opcode.ofNat, Nat.ble, h41_val] at reader_cstrs
  have op_a_is_u64 : Word.isU64_poly #v[Main[7], Main[8], Main[9], Main[10]] := by simp_all only
  have op_b_is_u64 : Word.isU64_poly #v[Main[15], Main[16], Main[17], Main[18]] := by simp_all only
  let op_a_val := Word.toBitVec64_poly #v[Main[7], Main[8], Main[9], Main[10]]
  let op_b_val := Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]
  have h6_zmod : Main[6] < (32 : ZMod p) := by simp_all only
  have h14_zmod : Main[14] < (32 : ZMod p) := by simp_all only
  have h6 : Main[6].val < 32 := by
    have : Main[6].val < (32 : ZMod p).val := h6_zmod; rwa [h32_val] at this
  have h14 : Main[14].val < 32 := by
    have : Main[14].val < (32 : ZMod p).val := h14_zmod; rwa [h32_val] at this
  have h_imm_0_z : Main[21] < (65536 : ZMod p) := by simp_all only
  have h_imm_1_z : Main[22] < (65536 : ZMod p) := by simp_all only
  have h_imm_2_z : Main[23] < (65536 : ZMod p) := by simp_all only
  have h_imm_3_z : Main[24] < (65536 : ZMod p) := by simp_all only
  have h_imm_0 : Main[21].val < 65536 := by
    have : Main[21].val < (65536 : ZMod p).val := h_imm_0_z; rwa [h65_val] at this
  have h_imm_1 : Main[22].val < 65536 := by
    have : Main[22].val < (65536 : ZMod p).val := h_imm_1_z; rwa [h65_val] at this
  have h_imm_2 : Main[23].val < 65536 := by
    have : Main[23].val < (65536 : ZMod p).val := h_imm_2_z; rwa [h65_val] at this
  have h_imm_3 : Main[24].val < 65536 := by
    have : Main[24].val < (65536 : ZMod p).val := h_imm_3_z; rwa [h65_val] at this
  have h_pc_0_z : Main[3] < (65536 : ZMod p) := by simp_all only
  have h_pc_1_z : Main[4] < (65536 : ZMod p) := by simp_all only
  have h_pc_2_z : Main[5] < (65536 : ZMod p) := by simp_all only
  have h_pc_0 : Main[3].val < 65536 := by
    have : Main[3].val < (65536 : ZMod p).val := h_pc_0_z; rwa [h65_val] at this
  have h_pc_1 : Main[4].val < 65536 := by
    have : Main[4].val < (65536 : ZMod p).val := h_pc_1_z; rwa [h65_val] at this
  have h_pc_2 : Main[5].val < 65536 := by
    have : Main[5].val < (65536 : ZMod p).val := h_pc_2_z; rwa [h65_val] at this
  -- LtOperationSigned spec.branch_poly: is_signed = 0 (BNE uses unsigned-style equality)
  have h_is_real_one :
      Main[28] + Main[29] + Main[30] + Main[31] + Main[32] + Main[33] = (1 : ZMod p) := by
    rw [h_is_bne, h_28, h_30, h_31, h_32, h_33]; ring
  rw [h_is_real_one] at lt_cstrs
  have h_is_signed_eq : (Main[30] + Main[31] : ZMod p) = 0 := by rw [h_30, h_31]; ring
  rw [h_is_signed_eq] at lt_cstrs
  have spec_lt := LtOperationSigned.spec.branch_poly op_a_is_u64 op_b_is_u64 lt_cstrs
  clear lt_cstrs
  have spec_lt_unsigned := spec_lt.1 rfl
  -- state cstrs
  simp [SP1ConstraintList.initialState_poly, Branch.constraints, SP1Constraint.toStateProp_poly,
    List.Forall, CPUState.constraints, ITypeReaderImmutable.constraints,
    LtOperationSigned.constraints, LtOperationUnsigned.constraints,
    U16MSBOperation.constraints, U16CompareOperation.constraints,
    h_is_bne, h6, h14, h_28, h_30, h_31, h_32, h_33,
    Opcode.ofNat, Nat.ble, h41_val] at state_cstrs
  obtain ⟨h_pc_read, h_op_a_read, h_op_b_read⟩ := state_cstrs
  specialize h_op_a_read
  specialize h_op_b_read
  simp [spec_bne, sp1_branch_poly, execute_BTYPE]
  rw [run_readReg]
  simp [h_pc_read]
  simp only [BitVec.ofNatLT_eq_ofNat] at h_op_a_read h_op_b_read
  simp [op_a, sp1_op_a_poly, h_op_a_read, op_b, sp1_op_b_poly, h_op_b_read]
  obtain ⟨h_eq_iff, h_neq_iff, _h_lt_ite⟩ := spec_lt_unsigned
  have h_BV_to_Word :
      Word.toBitVec64_poly #v[Main[7], Main[8], Main[9], Main[10]] =
        Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] →
      (#v[Main[7], Main[8], Main[9], Main[10]] : Word (ZMod p)) =
        #v[Main[15], Main[16], Main[17], Main[18]] := by
    intro h
    have h_a := Word.toBitVec64_poly_toNat_poly op_a_is_u64
    have h_b := Word.toBitVec64_poly_toNat_poly op_b_is_u64
    have h_nat : Word.toNat_poly (#v[Main[7], Main[8], Main[9], Main[10]] : Word (ZMod p)) =
        Word.toNat_poly #v[Main[15], Main[16], Main[17], Main[18]] := by
      rw [← h_a, ← h_b, h]
    have h7_lt : Main[7].val < 65536 := op_a_is_u64 0
    have h8_lt : Main[8].val < 65536 := op_a_is_u64 1
    have h9_lt : Main[9].val < 65536 := op_a_is_u64 2
    have h10_lt : Main[10].val < 65536 := op_a_is_u64 3
    have h15_lt : Main[15].val < 65536 := op_b_is_u64 0
    have h16_lt : Main[16].val < 65536 := op_b_is_u64 1
    have h17_lt : Main[17].val < 65536 := op_b_is_u64 2
    have h18_lt : Main[18].val < 65536 := op_b_is_u64 3
    simp only [Word.toNat_poly_def, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ] at h_nat
    have h7_eq : Main[7].val = Main[15].val := by omega
    have h8_eq : Main[8].val = Main[16].val := by omega
    have h9_eq : Main[9].val = Main[17].val := by omega
    have h10_eq : Main[10].val = Main[18].val := by omega
    have h7 : Main[7] = Main[15] := ZMod.val_injective _ h7_eq
    have h8 : Main[8] = Main[16] := ZMod.val_injective _ h8_eq
    have h9 : Main[9] = Main[17] := ZMod.val_injective _ h9_eq
    have h10 : Main[10] = Main[18] := ZMod.val_injective _ h10_eq
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [h7, h8, h9, h10]
  by_cases h_eq : op_a_val ≠ op_b_val <;> simp only [op_a_val, op_b_val] at h_eq
  · -- branching arm (NEQ)
    simp [h_eq]
    rw [run_readReg]
    simp only [show imm = BitVec.ofNat 13 Main[21].val from rfl]
    simp [Std.ExtDHashMap.get?_insert, h_pc_read, h_next_pc_b0, h_next_pc_b1]
    rw [SailME_run_readReg_map_writeReg _ Register.misa Register.nextPC
      (by simp [Std.ExtDHashMap.get?_insert]; exact hs Register.misa) _ _]
    simp only [Std.ExtDHashMap.insert_insert]
    have h_word_ne : ¬ (#v[Main[7], Main[8], Main[9], Main[10]] : Word (ZMod p)) =
        #v[Main[15], Main[16], Main[17], Main[18]] := by
      intro h_word_eq; apply h_eq
      exact congr_arg Word.toBitVec64_poly h_word_eq
    have h_flags_one : Main[36] + Main[37] + Main[38] + Main[39] = 1 := h_neq_iff.mp h_word_ne
    have h_is_branching : Main[34] = 1 := by
      clear *- h_flags_one chip_cstrs h_is_bne h_28 h_30 h_31 h_32 h_33
      simp_all [sub_eq_zero]
    simp [h_is_branching, sub_eq_zero, h_flags_one,
      h_is_bne, h_28, h_30, h_31, h_32, h_33] at chip_cstrs
    obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs
    have h14_lt : (14 : ℕ) < p := by omega
    have h14_val : (14 : ZMod p).val = 14 := ZMod.val_natCast_of_lt h14_lt
    have h25 : Main[25].val < 65536 := by
      apply lt_65536_of_mul_inv_4_lt_poly
      have h := h_bound_checks.1
      rw [h14_val] at h
      change _ < 16384 at h
      exact h
    have h26 : Main[26].val < 65536 := h_bound_checks.2.1
    have h27 : Main[27].val < 65536 := h_bound_checks.2.2
    have h_65_ne : (65536 : ZMod p) ≠ 0 := val_65536_ne_zero
    have h_limb0' : (Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ = 0
        ∨ (Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ = 1 := by
      rcases h_limb0 with (h | h) | h
      · left
        have hsub : Main[3] + Main[21] - Main[25] = 0 := by linear_combination h
        rw [hsub]; ring
      · exact absurd h h_65_ne
      · right; exact h
    have h_limb1' :
        ((Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22] - Main[26])
                * (65536 : ZMod p)⁻¹ = 0
        ∨ ((Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22] - Main[26])
                * (65536 : ZMod p)⁻¹ = 1 := by
      rcases h_limb1 with (h | h) | h
      · left
        have hsub : (Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22]
                      - Main[26] = 0 := by linear_combination h
        rw [hsub]; ring
      · exact absurd h h_65_ne
      · right; exact h
    have h_limb2' :
        (((Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22] - Main[26])
                  * (65536 : ZMod p)⁻¹ + Main[5] + Main[23] - Main[27]) * (65536 : ZMod p)⁻¹ = 0
        ∨ (((Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22] - Main[26])
                  * (65536 : ZMod p)⁻¹ + Main[5] + Main[23] - Main[27]) * (65536 : ZMod p)⁻¹ = 1
        := by
      rcases h_limb2 with (h | h) | h
      · left
        have hsub : ((Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22]
                      - Main[26]) * (65536 : ZMod p)⁻¹ + Main[5] + Main[23] - Main[27] = 0 := by
          linear_combination h
        rw [hsub]; ring
      · exact absurd h h_65_ne
      · right; exact h
    have h_limb3' :
        ((((Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22] - Main[26])
                  * (65536 : ZMod p)⁻¹ + Main[5] + Main[23] - Main[27]) * (65536 : ZMod p)⁻¹
                + Main[24]) * (65536 : ZMod p)⁻¹ = 0
        ∨ ((((Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22] - Main[26])
                  * (65536 : ZMod p)⁻¹ + Main[5] + Main[23] - Main[27]) * (65536 : ZMod p)⁻¹
                + Main[24]) * (65536 : ZMod p)⁻¹ = 1 := by
      rcases h_limb3 with (h | h) | h
      · left
        have hsub : (((Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22]
                      - Main[26]) * (65536 : ZMod p)⁻¹ + Main[5] + Main[23] - Main[27])
                      * (65536 : ZMod p)⁻¹ + Main[24] = 0 := by linear_combination h
        rw [hsub]; ring
      · exact absurd h h_65_ne
      · right; exact h
    have h_addr_eq :
        Word.toBitVec64_poly #v[Main[3], Main[4], Main[5], (0 : ZMod p)] +
            BitVec.signExtend 64 (BitVec.ofNat 13 Main[21].val) =
          Word.toBitVec64_poly #v[Main[25], Main[26], Main[27], (0 : ZMod p)] :=
      branch_addr_eq_poly Main h_sign_extend h_pc_0 h_pc_1 h_pc_2
        h_imm_0 h_imm_1 h_imm_2 h_imm_3 h25 h26 h27 h_limb0' h_limb1' h_limb2' h_limb3'
    rw [h_addr_eq]
  · -- non-branching arm (EQ)
    have h_word_eq : (#v[Main[7], Main[8], Main[9], Main[10]] : Word (ZMod p)) =
        #v[Main[15], Main[16], Main[17], Main[18]] := by
      apply h_BV_to_Word
      by_contra hne; exact h_eq hne
    have h_flags_zero_quad := h_eq_iff.mp h_word_eq
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ] at h_flags_zero_quad
    have h_flags_zero : Main[36] + Main[37] + Main[38] + Main[39] = 0 := by
      obtain ⟨h36, h37, h38, h39⟩ := h_flags_zero_quad
      rw [h36, h37, h38, h39]; ring
    simp [h_flags_zero, sub_eq_zero, h_is_bne, h_28, h_30, h_31, h_32, h_33] at chip_cstrs
    have h_is_branching : Main[34] = 0 := by
      clear *- h_flags_zero chip_cstrs; simp_all [sub_eq_zero]
    simp [h_is_branching] at chip_cstrs
    -- Bridge h_word_eq (Word equality) to BV equality for the if-then-else collapse.
    have h_BV_eq :
        Word.toBitVec64_poly #v[Main[7], Main[8], Main[9], Main[10]] =
          Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] :=
      congr_arg Word.toBitVec64_poly h_word_eq
    simp [h_BV_eq]
    obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs
    have h14_lt : (14 : ℕ) < p := by omega
    have h14_val : (14 : ZMod p).val = 14 := ZMod.val_natCast_of_lt h14_lt
    have h25 : Main[25].val < 65536 := by
      apply lt_65536_of_mul_inv_4_lt_poly
      have h := h_bound_checks.1
      rw [h14_val] at h
      change _ < 16384 at h
      exact h
    have h26 : Main[26].val < 65536 := h_bound_checks.2.1
    have h27 : Main[27].val < 65536 := h_bound_checks.2.2
    have h_pc4_eq :
        Word.toBitVec64_poly #v[Main[3], Main[4], Main[5], (0 : ZMod p)] + 4#64 =
          Word.toBitVec64_poly #v[Main[25], Main[26], Main[27], (0 : ZMod p)] :=
      pc_plus_4_eq_poly_chip Main h_pc_0 h_pc_1 h_pc_2 h25 h26 h27
        h_limb0 h_limb1 h_limb2 h_limb3
    rw [h_pc4_eq]

end BNE

namespace BLT

noncomputable def spec_blt (imm : (BitVec 13)) (rs2 : regidx) (rs1 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_BTYPE imm rs2 rs1 bop.BLT

set_option maxHeartbeats 2000000 in
-- correctness proof across all 6 branch-opcode cases
theorem correct_blt
    (Main : Vector (Fin KB) 45)
    (s : SailState) (hs : s.isInitialized)
    (h_is_blt : Main[30] = 1)
    (cstrs : (constraints Main).allHold)
    (state_cstrs : (constraints Main).initialState s) :
    let imm := sp1_imm Main
    let op_b := .Regidx (sp1_op_b Main)
    let op_a := .Regidx (sp1_op_a Main)
    (spec_blt imm op_b op_a).run s = (sp1_branch Main).run s := by
  extract_lets imm op_b op_a
  have h_is_real : is_real Main := by simp [is_real, h_is_blt]
  have h_sign_extend := eq_signExtend_of_is_real Main cstrs h_is_real
  have h_next_pc_is_mul4 : (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] +
    BitVec.signExtend 64 imm) % 4 = 0 := add_signExtend_of_constraints Main cstrs h_is_real
  obtain ⟨h_next_pc_b0, h_next_pc_b1⟩ := mul4_means_0_1_are_0 h_next_pc_is_mul4
  obtain ⟨h_28, h_30, h_31, h_32, h_33⟩ := (single_op Main cstrs).2.2.1 h_is_blt
  simp [SP1ConstraintList.allHold, Branch.constraints] at cstrs
  obtain ⟨_, reader_cstrs, lt_cstrs, chip_cstrs⟩ := cstrs
  -- simplify reader constraints
  simp [ITypeReaderImmutable.constraints, SP1Constraint.toProp,
    h_is_blt, h_28, h_30, h_31, h_32, h_33, Opcode.ofNat, Nat.ble] at reader_cstrs
  -- Introduce bounds on values
  have op_a_is_u64 : Word.isU64 #v[Main[7], Main[8], Main[9], Main[10]] := by simp_all only
  have op_b_is_u64 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := by simp_all only
  let op_a_val := Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]]
  let op_b_val := Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]
  have h6 : Main[6] < 32 := by aesop
  have h14 : Main[14] < 32 := by aesop
  have h_imm_0 : Main[21].val < 65536 := by change Main[21] < 65536; simp_all only
  have h_imm_1 : Main[22].val < 65536 := by change Main[22] < 65536; simp_all only
  have h_imm_2 : Main[23].val < 65536 := by change Main[23] < 65536; simp_all only
  have h_imm_3 : Main[24].val < 65536 := by change Main[24] < 65536; simp_all only
  have h_imm_is_u64 : Main[21].val + Main[22].val * 65536 + ↑Main[23] * 4294967296 + ↑Main[24] * 281474976710656 < 2^64 := by omega
  have op_c_is_u64 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := Word.isU64_of_cases h_imm_0 h_imm_1 h_imm_2 h_imm_3
  have h_pc_0 : Main[3].val < 65536 := by change Main[3] < 65536; aesop
  have h_pc_1 : Main[4].val < 65536 := by change Main[4] < 65536; aesop
  have h_pc_2 : Main[5].val < 65536 := by change Main[5] < 65536; aesop
  have h_pc_is_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 < 2^64 := by omega
  have h_pc_add4_is_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 + 4 < 2^64 := by omega
  have h_nextpc_is_u64 : Main[25].val + Main[26].val * 65536 + Main[27].val * 4294967296 < 2^64 := by omega
  simp_all
  -- simplify lt operation constraints
  have spec_lt := LtOperationSigned.spec.branch op_a_is_u64 op_b_is_u64 lt_cstrs
  clear lt_cstrs
  simp [LtOperationSigned.spec.branch.def] at spec_lt
  -- simplify state constraints
  simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall,
    CPUState.constraints, ITypeReaderImmutable.constraints, LtOperationSigned.constraints,
    LtOperationUnsigned.constraints, U16MSBOperation.constraints, U16CompareOperation.constraints,
    h_is_blt, h6, h14, h_28, h_30, h_31, h_32, h_33, Opcode.ofNat, Nat.ble] at state_cstrs
  obtain ⟨h_pc_read, h_op_a_read, h_op_b_read⟩ := state_cstrs
  specialize h_op_a_read
  specialize h_op_b_read
  -- simplify main goal
  simp [spec_blt, sp1_branch, execute_BTYPE]
  rw [run_readReg]
  simp [h_pc_read]
  simp_all only [BitVec.ofNatLT_eq_ofNat]
  simp [op_a, sp1_op_a, h_op_a_read, op_b, sp1_op_b, h_op_b_read]
  by_cases h_eq : op_a_val.toInt < op_b_val.toInt <;> simp only [op_a_val, op_b_val] at h_eq
  · simp [h_eq]
    rw [run_readReg]
    simp [Std.ExtDHashMap.get?_insert, h_pc_read, h_next_pc_b0, h_next_pc_b1]
    rw [SailME_run_readReg_map_writeReg _ Register.misa Register.nextPC
      (by simp [Std.ExtDHashMap.get?_insert]; exact hs Register.misa) _ _]
    simp only [Std.ExtDHashMap.insert_insert]
    have h_ne : (Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]]) ≠
        (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]) := by
      clear *- h_eq; aesop
    simp [h_ne, h_eq, BitVec.slt] at spec_lt
    have h36 : Main[35] = 1 := by simp_all only
    have h_is_branching : Main[34] = 1 := by
      clear *- chip_cstrs h36; simp_all [sub_eq_zero]
    simp [h_is_branching, sub_eq_zero, h36] at chip_cstrs
    obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs
    have h26 : Main[25].val < 65536 := by
      apply lt_65536_of_mul_inv_4_lt
      exact h_bound_checks.1
    have h_addr_eq : Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] + BitVec.signExtend 64 imm
        = Word.toBitVec64 #v[Main[25], Main[26], Main[27], 0] := by
      close_branch_addr_eq
    rw [h_addr_eq]
  · simp [h_eq]
    simp [h_eq, BitVec.slt] at spec_lt
    have h36 : Main[35] = 0 := by simp_all only
    have h35 : Main[34] = 0 := by clear *- chip_cstrs h36; simp_all
    simp [h35, h36, sub_eq_zero] at chip_cstrs
    obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs
    have h26 : Main[25].val < 65536 := by
      apply lt_65536_of_mul_inv_4_lt
      exact h_bound_checks.1
    simp only [← inv_4BB_eq', ← inv_65536BB_eq'] at h_bound_checks h_limb0 h_limb1 h_limb2 h_limb3
    simp [BitVec.add_def, Word.toBitVec64, Word.toNat, ← BitVec.toNat_inj]
    clear * - h26 h_pc_0 h_pc_1 h_pc_2 h_bound_checks h_limb0 h_limb1 h_limb2 h_limb3
    omega

end BLT

namespace BGE

noncomputable def spec_bge (imm : (BitVec 13)) (rs2 : regidx) (rs1 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_BTYPE imm rs2 rs1 bop.BGE

set_option maxHeartbeats 2000000 in
-- correctness proof across all 6 branch-opcode cases
theorem correct_bge
    (Main : Vector (Fin KB) 45)
    (s : SailState) (hs : s.isInitialized)
    (h_is_bge : Main[31] = 1)
    (cstrs : (constraints Main).allHold)
    (state_cstrs : (constraints Main).initialState s) :
    let imm := sp1_imm Main
    let op_b := .Regidx (sp1_op_b Main)
    let op_a := .Regidx (sp1_op_a Main)
    (spec_bge imm op_b op_a).run s = (sp1_branch Main).run s := by
  extract_lets imm op_b op_a
  have h_is_real : is_real Main := by simp [is_real, h_is_bge]
  have h_sign_extend := eq_signExtend_of_is_real Main cstrs h_is_real
  have h_next_pc_is_mul4 : (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] +
    BitVec.signExtend 64 imm) % 4 = 0 := add_signExtend_of_constraints Main cstrs h_is_real
  obtain ⟨h_next_pc_b0, h_next_pc_b1⟩ := mul4_means_0_1_are_0 h_next_pc_is_mul4
  obtain ⟨h_28, h_30, h_31, h_32, h_33⟩ := (single_op Main cstrs).2.2.2.1 h_is_bge
  simp [SP1ConstraintList.allHold, Branch.constraints] at cstrs
  obtain ⟨_, reader_cstrs, lt_cstrs, chip_cstrs⟩ := cstrs
  -- simplify reader constraints
  simp [ITypeReaderImmutable.constraints, SP1Constraint.toProp,
    h_is_bge, h_28, h_30, h_31, h_32, h_33, Opcode.ofNat, Nat.ble] at reader_cstrs
  -- Introduce bounds on values
  have op_a_is_u64 : Word.isU64 #v[Main[7], Main[8], Main[9], Main[10]] := by simp_all only
  have op_b_is_u64 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := by simp_all only
  let op_a_val := Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]]
  let op_b_val := Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]
  have h6 : Main[6] < 32 := by aesop
  have h14 : Main[14] < 32 := by aesop
  have h_imm_0 : Main[21].val < 65536 := by change Main[21] < 65536; simp_all only
  have h_imm_1 : Main[22].val < 65536 := by change Main[22] < 65536; simp_all only
  have h_imm_2 : Main[23].val < 65536 := by change Main[23] < 65536; simp_all only
  have h_imm_3 : Main[24].val < 65536 := by change Main[24] < 65536; simp_all only
  have h_imm_is_u64 : Main[21].val + Main[22].val * 65536 + ↑Main[23] * 4294967296 + ↑Main[24] * 281474976710656 < 2^64 := by omega
  have op_c_is_u64 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := Word.isU64_of_cases h_imm_0 h_imm_1 h_imm_2 h_imm_3
  have h_pc_0 : Main[3].val < 65536 := by change Main[3] < 65536; aesop
  have h_pc_1 : Main[4].val < 65536 := by change Main[4] < 65536; aesop
  have h_pc_2 : Main[5].val < 65536 := by change Main[5] < 65536; aesop
  have h_pc_is_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 < 2^64 := by omega
  have h_pc_add4_is_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 + 4 < 2^64 := by omega
  have h_nextpc_is_u64 : Main[25].val + Main[26].val * 65536 + Main[27].val * 4294967296 < 2^64 := by omega
  simp_all
  -- simplify lt operation constraints
  have spec_lt := LtOperationSigned.spec.branch op_a_is_u64 op_b_is_u64 lt_cstrs
  clear lt_cstrs
  simp [LtOperationSigned.spec.branch.def] at spec_lt
  -- simplify state constraints
  simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall,
    CPUState.constraints, ITypeReaderImmutable.constraints, LtOperationSigned.constraints,
    LtOperationUnsigned.constraints, U16MSBOperation.constraints, U16CompareOperation.constraints,
    h_is_bge, h6, h14, h_28, h_30, h_31, h_32, h_33, Opcode.ofNat, Nat.ble] at state_cstrs
  obtain ⟨h_pc_read, h_op_a_read, h_op_b_read⟩ := state_cstrs
  specialize h_op_a_read
  specialize h_op_b_read
  -- simplify main goal
  simp [spec_bge, sp1_branch, execute_BTYPE]
  rw [run_readReg]
  simp [h_pc_read]
  simp_all only [BitVec.ofNatLT_eq_ofNat]
  simp [op_a, sp1_op_a, h_op_a_read, op_b, sp1_op_b, h_op_b_read]
  by_cases h_eq : op_a_val.toInt ≥ op_b_val.toInt <;> simp only [op_a_val, op_b_val] at h_eq
  · simp [h_eq]
    rw [run_readReg]
    simp [Std.ExtDHashMap.get?_insert, h_pc_read, h_next_pc_b0, h_next_pc_b1]
    rw [SailME_run_readReg_map_writeReg _ Register.misa Register.nextPC
      (by simp [Std.ExtDHashMap.get?_insert]; exact hs Register.misa) _ _]
    simp only [Std.ExtDHashMap.insert_insert]
    have h_ne : ¬ ((Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]]).toInt <
        (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toInt) := by
      clear *- h_eq; omega
    simp [h_ne, h_eq, BitVec.slt] at spec_lt
    have h36 : Main[35] = 0 := by simp_all only
    have h_is_branching : Main[34] = 1 := by
      clear *- chip_cstrs h36; simp_all [sub_eq_zero]
    simp [h_is_branching, sub_eq_zero, h36] at chip_cstrs
    obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs
    have h26 : Main[25].val < 65536 := by
      apply lt_65536_of_mul_inv_4_lt
      exact h_bound_checks.1
    have h_addr_eq : Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] + BitVec.signExtend 64 imm
        = Word.toBitVec64 #v[Main[25], Main[26], Main[27], 0] := by
      close_branch_addr_eq
    rw [h_addr_eq]
  · simp [h_eq]
    have h_ne : ((Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]]).toInt <
        (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toInt) := by
      clear *- h_eq; omega
    simp [h_eq, h_ne, BitVec.slt] at spec_lt
    have h36 : Main[35] = 1 := by simp_all only
    have h35 : Main[34] = 0 := by clear *- chip_cstrs h36; simp_all
    simp [h35, h36, sub_eq_zero] at chip_cstrs
    obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs
    have h26 : Main[25].val < 65536 := by
      apply lt_65536_of_mul_inv_4_lt
      exact h_bound_checks.1
    simp only [← inv_4BB_eq', ← inv_65536BB_eq'] at h_bound_checks h_limb0 h_limb1 h_limb2 h_limb3
    simp [BitVec.add_def, Word.toBitVec64, Word.toNat, ← BitVec.toNat_inj]
    clear * - h26 h_pc_0 h_pc_1 h_pc_2 h_bound_checks h_limb0 h_limb1 h_limb2 h_limb3
    omega

end BGE

namespace BLTU

noncomputable def spec_bltu (imm : (BitVec 13)) (rs2 : regidx) (rs1 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_BTYPE imm rs2 rs1 bop.BLTU

set_option maxHeartbeats 2000000 in
-- correctness proof across all 6 branch-opcode cases
theorem correct_bltu
    (Main : Vector (Fin KB) 45)
    (s : SailState) (hs : s.isInitialized)
    (h_is_bltu : Main[32] = 1)
    (cstrs : (constraints Main).allHold)
    (state_cstrs : (constraints Main).initialState s) :
    let imm := sp1_imm Main
    let op_b := .Regidx (sp1_op_b Main)
    let op_a := .Regidx (sp1_op_a Main)
    (spec_bltu imm op_b op_a).run s = (sp1_branch Main).run s := by
  extract_lets imm op_b op_a
  have h_is_real : is_real Main := by simp [is_real, h_is_bltu]
  have h_sign_extend := eq_signExtend_of_is_real Main cstrs h_is_real
  have h_next_pc_is_mul4 : (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] +
    BitVec.signExtend 64 imm) % 4 = 0 := add_signExtend_of_constraints Main cstrs h_is_real
  obtain ⟨h_next_pc_b0, h_next_pc_b1⟩ := mul4_means_0_1_are_0 h_next_pc_is_mul4
  obtain ⟨h_28, h_30, h_31, h_32, h_33⟩ := (single_op Main cstrs).2.2.2.2.1 h_is_bltu
  simp [SP1ConstraintList.allHold, Branch.constraints] at cstrs
  obtain ⟨_, reader_cstrs, lt_cstrs, chip_cstrs⟩ := cstrs
  -- simplify reader constraints
  simp [ITypeReaderImmutable.constraints, SP1Constraint.toProp,
    h_is_bltu, h_28, h_30, h_31, h_32, h_33, Opcode.ofNat, Nat.ble] at reader_cstrs
  -- Introduce bounds on values
  have op_a_is_u64 : Word.isU64 #v[Main[7], Main[8], Main[9], Main[10]] := by simp_all only
  have op_b_is_u64 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := by simp_all only
  let op_a_val := Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]]
  let op_b_val := Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]
  have h6 : Main[6] < 32 := by aesop
  have h14 : Main[14] < 32 := by aesop
  have h_imm_0 : Main[21].val < 65536 := by change Main[21] < 65536; simp_all only
  have h_imm_1 : Main[22].val < 65536 := by change Main[22] < 65536; simp_all only
  have h_imm_2 : Main[23].val < 65536 := by change Main[23] < 65536; simp_all only
  have h_imm_3 : Main[24].val < 65536 := by change Main[24] < 65536; simp_all only
  have h_imm_is_u64 : Main[21].val + Main[22].val * 65536 + ↑Main[23] * 4294967296 + ↑Main[24] * 281474976710656 < 2^64 := by omega
  have op_c_is_u64 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := Word.isU64_of_cases h_imm_0 h_imm_1 h_imm_2 h_imm_3
  have h_pc_0 : Main[3].val < 65536 := by change Main[3] < 65536; aesop
  have h_pc_1 : Main[4].val < 65536 := by change Main[4] < 65536; aesop
  have h_pc_2 : Main[5].val < 65536 := by change Main[5] < 65536; aesop
  have h_pc_is_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 < 2^64 := by omega
  have h_pc_add4_is_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 + 4 < 2^64 := by omega
  have h_nextpc_is_u64 : Main[25].val + Main[26].val * 65536 + Main[27].val * 4294967296 < 2^64 := by omega
  simp_all
  -- simplify lt operation constraints
  have spec_lt := LtOperationSigned.spec.branch op_a_is_u64 op_b_is_u64 lt_cstrs
  clear lt_cstrs
  simp [LtOperationSigned.spec.branch.def] at spec_lt
  -- simplify state constraints
  simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall,
    CPUState.constraints, ITypeReaderImmutable.constraints, LtOperationSigned.constraints,
    LtOperationUnsigned.constraints, U16MSBOperation.constraints, U16CompareOperation.constraints,
    h_is_bltu, h6, h14, h_28, h_30, h_31, h_32, h_33, Opcode.ofNat, Nat.ble] at state_cstrs
  obtain ⟨h_pc_read, h_op_a_read, h_op_b_read⟩ := state_cstrs
  specialize h_op_a_read
  specialize h_op_b_read
  -- simplify main goal
  simp [spec_bltu, sp1_branch, execute_BTYPE]
  rw [run_readReg]
  simp [h_pc_read]
  simp_all only [BitVec.ofNatLT_eq_ofNat]
  simp [op_a, sp1_op_a, h_op_a_read, op_b, sp1_op_b, h_op_b_read]
  by_cases h_eq : op_a_val.toNat < op_b_val.toNat <;> simp only [op_a_val, op_b_val] at h_eq
  · simp [h_eq]
    rw [run_readReg]
    simp [Std.ExtDHashMap.get?_insert, h_pc_read, h_next_pc_b0, h_next_pc_b1]
    rw [SailME_run_readReg_map_writeReg _ Register.misa Register.nextPC
      (by simp [Std.ExtDHashMap.get?_insert]; exact hs Register.misa) _ _]
    simp only [Std.ExtDHashMap.insert_insert]
    have h_ne : ((Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]]).toNat <
        (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat) := by
      clear *- h_eq; omega
    simp [h_ne, h_eq, BitVec.ult] at spec_lt
    have h36 : Main[35] = 1 := by simp_all only
    have h_is_branching : Main[34] = 1 := by
      clear *- chip_cstrs h36; simp_all [sub_eq_zero]
    simp [h_is_branching, sub_eq_zero, h36] at chip_cstrs
    obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs
    have h26 : Main[25].val < 65536 := by
      apply lt_65536_of_mul_inv_4_lt
      exact h_bound_checks.1
    have h_addr_eq : Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] + BitVec.signExtend 64 imm
        = Word.toBitVec64 #v[Main[25], Main[26], Main[27], 0] := by
      close_branch_addr_eq
    rw [h_addr_eq]
  · simp [h_eq]
    have h_ne : ¬ ((Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]]).toNat <
        (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat) := by
      clear *- h_eq; omega
    simp [h_eq, h_ne, BitVec.ult] at spec_lt
    have h36 : Main[35] = 0 := by simp_all only
    have h35 : Main[34] = 0 := by clear *- chip_cstrs h36; simp_all
    simp [h35, h36, sub_eq_zero] at chip_cstrs
    obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs
    have h26 : Main[25].val < 65536 := by
      apply lt_65536_of_mul_inv_4_lt
      exact h_bound_checks.1
    simp only [← inv_4BB_eq', ← inv_65536BB_eq'] at h_bound_checks h_limb0 h_limb1 h_limb2 h_limb3
    simp [BitVec.add_def, Word.toBitVec64, Word.toNat, ← BitVec.toNat_inj]
    clear * - h26 h_pc_0 h_pc_1 h_pc_2 h_bound_checks h_limb0 h_limb1 h_limb2 h_limb3
    omega

end BLTU

namespace BGEU

noncomputable def spec_bgeu (imm : (BitVec 13)) (rs2 : regidx) (rs1 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_BTYPE imm rs2 rs1 bop.BGEU

set_option maxHeartbeats 2000000 in
-- correctness proof across all 6 branch-opcode cases
theorem correct_bgeu
    (Main : Vector (Fin KB) 45)
    (s : SailState) (hs : s.isInitialized)
    (h_is_bgeu : Main[33] = 1)
    (cstrs : (constraints Main).allHold)
    (state_cstrs : (constraints Main).initialState s) :
    let imm := sp1_imm Main
    let op_b := .Regidx (sp1_op_b Main)
    let op_a := .Regidx (sp1_op_a Main)
    (spec_bgeu imm op_b op_a).run s = (sp1_branch Main).run s := by
  extract_lets imm op_b op_a
  have h_is_real : is_real Main := by simp [is_real, h_is_bgeu]
  have h_sign_extend := eq_signExtend_of_is_real Main cstrs h_is_real
  have h_next_pc_is_mul4 : (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] +
    BitVec.signExtend 64 imm) % 4 = 0 := add_signExtend_of_constraints Main cstrs h_is_real
  obtain ⟨h_next_pc_b0, h_next_pc_b1⟩ := mul4_means_0_1_are_0 h_next_pc_is_mul4
  obtain ⟨h_28, h_30, h_31, h_32, h_33⟩ := (single_op Main cstrs).2.2.2.2.2 h_is_bgeu
  simp [SP1ConstraintList.allHold, Branch.constraints] at cstrs
  obtain ⟨_, reader_cstrs, lt_cstrs, chip_cstrs⟩ := cstrs
  -- simplify reader constraints
  simp [ITypeReaderImmutable.constraints, SP1Constraint.toProp,
    h_is_bgeu, h_28, h_30, h_31, h_32, h_33, Opcode.ofNat, Nat.ble] at reader_cstrs
  -- Introduce bounds on values
  have op_a_is_u64 : Word.isU64 #v[Main[7], Main[8], Main[9], Main[10]] := by simp_all only
  have op_b_is_u64 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := by simp_all only
  let op_a_val := Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]]
  let op_b_val := Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]
  have h6 : Main[6] < 32 := by aesop
  have h14 : Main[14] < 32 := by aesop
  have h_imm_0 : Main[21].val < 65536 := by change Main[21] < 65536; simp_all only
  have h_imm_1 : Main[22].val < 65536 := by change Main[22] < 65536; simp_all only
  have h_imm_2 : Main[23].val < 65536 := by change Main[23] < 65536; simp_all only
  have h_imm_3 : Main[24].val < 65536 := by change Main[24] < 65536; simp_all only
  have h_imm_is_u64 : Main[21].val + Main[22].val * 65536 + ↑Main[23] * 4294967296 + ↑Main[24] * 281474976710656 < 2^64 := by omega
  have op_c_is_u64 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := Word.isU64_of_cases h_imm_0 h_imm_1 h_imm_2 h_imm_3
  have h_pc_0 : Main[3].val < 65536 := by change Main[3] < 65536; aesop
  have h_pc_1 : Main[4].val < 65536 := by change Main[4] < 65536; aesop
  have h_pc_2 : Main[5].val < 65536 := by change Main[5] < 65536; aesop
  have h_pc_is_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 < 2^64 := by omega
  have h_pc_add4_is_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 + 4 < 2^64 := by omega
  have h_nextpc_is_u64 : Main[25].val + Main[26].val * 65536 + Main[27].val * 4294967296 < 2^64 := by omega
  simp_all
  -- simplify lt operation constraints
  have spec_lt := LtOperationSigned.spec.branch op_a_is_u64 op_b_is_u64 lt_cstrs
  clear lt_cstrs
  simp [LtOperationSigned.spec.branch.def] at spec_lt
  -- simplify state constraints
  simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall,
    CPUState.constraints, ITypeReaderImmutable.constraints, LtOperationSigned.constraints,
    LtOperationUnsigned.constraints, U16MSBOperation.constraints, U16CompareOperation.constraints,
    h_is_bgeu, h6, h14, h_28, h_30, h_31, h_32, h_33, Opcode.ofNat, Nat.ble] at state_cstrs
  obtain ⟨h_pc_read, h_op_a_read, h_op_b_read⟩ := state_cstrs
  specialize h_op_a_read
  specialize h_op_b_read
  -- simplify main goal
  simp [spec_bgeu, sp1_branch, execute_BTYPE]
  rw [run_readReg]
  simp [h_pc_read]
  simp_all only [BitVec.ofNatLT_eq_ofNat]
  simp [op_a, sp1_op_a, h_op_a_read, op_b, sp1_op_b, h_op_b_read]
  by_cases h_eq : op_a_val.toNat ≥ op_b_val.toNat <;> simp only [op_a_val, op_b_val] at h_eq
  · simp [h_eq]
    rw [run_readReg]
    simp [Std.ExtDHashMap.get?_insert, h_pc_read, h_next_pc_b0, h_next_pc_b1]
    rw [SailME_run_readReg_map_writeReg _ Register.misa Register.nextPC
      (by simp [Std.ExtDHashMap.get?_insert]; exact hs Register.misa) _ _]
    simp only [Std.ExtDHashMap.insert_insert]
    have h_ne : ¬ ((Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]]).toNat <
        (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat) := by
      clear *- h_eq; omega
    simp [h_ne, h_eq, BitVec.ult] at spec_lt
    have h36 : Main[35] = 0 := by simp_all only
    have h_is_branching : Main[34] = 1 := by
      clear *- chip_cstrs h36; simp_all [sub_eq_zero]
    simp [h_is_branching, sub_eq_zero, h36] at chip_cstrs
    obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs
    have h26 : Main[25].val < 65536 := by
      apply lt_65536_of_mul_inv_4_lt
      exact h_bound_checks.1
    have h_addr_eq : Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] + BitVec.signExtend 64 imm
        = Word.toBitVec64 #v[Main[25], Main[26], Main[27], 0] := by
      close_branch_addr_eq
    rw [h_addr_eq]
  · simp [h_eq]
    have h_ne : ((Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]]).toNat <
        (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat) := by
      clear *- h_eq; omega
    simp [h_eq, h_ne, BitVec.ult] at spec_lt
    have h36 : Main[35] = 1 := by simp_all only
    have h35 : Main[34] = 0 := by clear *- chip_cstrs h36; simp_all
    simp [h35, h36, sub_eq_zero] at chip_cstrs
    obtain ⟨h_limb0, h_limb1, h_limb2, h_limb3, h_bound_checks⟩ := chip_cstrs
    have h26 : Main[25].val < 65536 := by
      apply lt_65536_of_mul_inv_4_lt
      exact h_bound_checks.1
    simp only [← inv_4BB_eq', ← inv_65536BB_eq'] at h_bound_checks h_limb0 h_limb1 h_limb2 h_limb3
    simp [BitVec.add_def, Word.toBitVec64, Word.toNat, ← BitVec.toNat_inj]
    clear * - h26 h_pc_0 h_pc_1 h_pc_2 h_bound_checks h_limb0 h_limb1 h_limb2 h_limb3
    omega

end BGEU

end Branch
