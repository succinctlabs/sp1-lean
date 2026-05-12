import SP1Foundations
import SP1Chips.Load.LoadX0.Constraints
import SP1Operations.Operation.AddrAddOperation
import SP1Operations.Reader.ITypeReaderImmutable

open LeanRV64D.Functions Sail SailState

namespace Load

namespace LoadX0

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

/-- LoadX0's destination is `op_a = x0`. The reader's
`op_a_0 = 1 ↔ op_a = 0` clause combined with the chip's
`(Main[13] - 1) * E72 = 0` clause forces `Main[13] = 1` and hence
`Main[6] = 0`. -/
def sp1_op_a (Main : Vector (ZMod p) 48) : BitVec 5 :=
  BitVec.ofNat 5 Main[6].val

def sp1_ob_b (Main : Vector (ZMod p) 48) : BitVec 5 :=
  BitVec.ofNat 5 Main[14].val

def sp1_imm_c (Main : Vector (ZMod p) 48) : BitVec 12 :=
  BitVec.ofNat 12 Main[21].val

/-- LoadX0's chip-side semantics: the destination is `x0` (per
`Lean_RV64D/Regs.lean:663`, `wX 0 _` is a no-op), so the load result
is discarded. The only observable effect is the next-PC write
(`PC + 4`), determined by the chip's `CPUState` constraints clause
`#v[Main[3] + 4, Main[4], Main[5]]` for the new PC.

The `op_a` (Main[6]) and `op_b` (Main[14]) registers are exposed by
the `ITypeReaderImmutable` reader on the chip's `Main[6]/Main[14]`
columns; the immediate by `Main[21..24]`. The reader additionally
enforces `Main[13] = 1` (op_a is x0) by combining the chip's
`(Main[13] - 1) * E72 = 0` constraint with the umbrella
`E72 = Main[41] + … + Main[47]` "is real" gate. -/
def sp1_loadX0 (Main : Vector (ZMod p) 48) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC
    (Word.toBitVec64_poly #v[Main[3], Main[4], Main[5], (0 : ZMod p)] + 4)
  return RETIRE_SUCCESS

/-- Spec for the LD sub-opcode (`Main[47] = 1`): 8-byte unsigned load.
RISC-V `LD imm(rs1), x0`. -/
noncomputable def spec_loadX0_ld (imm : BitVec 12) (rs1 rs2 : regidx) :
    SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_LOAD imm rs1 rs2 (is_unsigned := true) (width := 8)

/-- Spec for the LBU sub-opcode (`Main[42] = 1`). -/
noncomputable def spec_loadX0_lbu (imm : BitVec 12) (rs1 rs2 : regidx) :
    SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_LOAD imm rs1 rs2 (is_unsigned := true) (width := 1)

/-- Spec for the LB sub-opcode (`Main[41] = 1`). -/
noncomputable def spec_loadX0_lb (imm : BitVec 12) (rs1 rs2 : regidx) :
    SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_LOAD imm rs1 rs2 (is_unsigned := false) (width := 1)

/-- Spec for the LH sub-opcode (`Main[43] = 1`). -/
noncomputable def spec_loadX0_lh (imm : BitVec 12) (rs1 rs2 : regidx) :
    SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_LOAD imm rs1 rs2 (is_unsigned := false) (width := 2)

/-- Spec for the LHU sub-opcode (`Main[44] = 1`). -/
noncomputable def spec_loadX0_lhu (imm : BitVec 12) (rs1 rs2 : regidx) :
    SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_LOAD imm rs1 rs2 (is_unsigned := true) (width := 2)

/-- Spec for the LW sub-opcode (`Main[45] = 1`). -/
noncomputable def spec_loadX0_lw (imm : BitVec 12) (rs1 rs2 : regidx) :
    SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_LOAD imm rs1 rs2 (is_unsigned := false) (width := 4)

/-- Spec for the LWU sub-opcode (`Main[46] = 1`). -/
noncomputable def spec_loadX0_lwu (imm : BitVec 12) (rs1 rs2 : regidx) :
    SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_LOAD imm rs1 rs2 (is_unsigned := true) (width := 4)

/-- Sum-of-7 collapse helper: given that each of `a₁..a₆` is `{0, 1}`-
valued, the sum `a₁ + … + a₇` is `{0, 1}`-valued, and `a₇ = 1`, the
other six must be zero. Pinned `Fact (2 ^ 17 < p)` is sufficient — it
gives `p > 131072 > 7` so the natural-number sum of values does not
wrap. Position-agnostic: each LoadX0 sub-opcode picks a different
`Main[i]` (`i ∈ {41..47}`) as the selected one and feeds the remaining
six (in any order) as `a₁..a₆`. -/
private lemma seven_collapse
    {a₁ a₂ a₃ a₄ a₅ a₆ a₇ : ZMod p}
    (h1 : a₁ = 0 ∨ a₁ = 1) (h2 : a₂ = 0 ∨ a₂ = 1) (h3 : a₃ = 0 ∨ a₃ = 1)
    (h4 : a₄ = 0 ∨ a₄ = 1) (h5 : a₅ = 0 ∨ a₅ = 1) (h6 : a₆ = 0 ∨ a₆ = 1)
    (h7_eq_one : a₇ = 1)
    (h_sum_01 : (a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ - 1) *
                (a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇) = 0) :
    a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0 ∧ a₄ = 0 ∧ a₅ = 0 ∧ a₆ = 0 := by
  have hp : 131072 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    have h17 : (2 : ℕ) ^ 17 = 131072 := by decide
    omega
  have h_one_val : (1 : ZMod p).val = 1 := by
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
  have h_each_le : ∀ x : ZMod p, x = 0 ∨ x = 1 → x.val ≤ 1 := by
    intro x hx
    rcases hx with h | h
    · rw [h, ZMod.val_zero]; omega
    · rw [h, h_one_val]
  have h7_val : a₇.val = 1 := by rw [h7_eq_one, h_one_val]
  have hl1 := h_each_le _ h1
  have hl2 := h_each_le _ h2
  have hl3 := h_each_le _ h3
  have hl4 := h_each_le _ h4
  have hl5 := h_each_le _ h5
  have hl6 := h_each_le _ h6
  -- Bottom-up val computation for each partial sum.
  have ha12 : (a₁ + a₂).val = a₁.val + a₂.val :=
    ZMod.val_add_of_lt (by omega)
  have ha123 : (a₁ + a₂ + a₃).val = a₁.val + a₂.val + a₃.val := by
    rw [show a₁ + a₂ + a₃ = (a₁ + a₂) + a₃ from rfl,
      ZMod.val_add_of_lt (by rw [ha12]; omega), ha12]
  have ha1234 : (a₁ + a₂ + a₃ + a₄).val = a₁.val + a₂.val + a₃.val + a₄.val := by
    rw [show a₁ + a₂ + a₃ + a₄ = (a₁ + a₂ + a₃) + a₄ from rfl,
      ZMod.val_add_of_lt (by rw [ha123]; omega), ha123]
  have ha12345 : (a₁ + a₂ + a₃ + a₄ + a₅).val =
      a₁.val + a₂.val + a₃.val + a₄.val + a₅.val := by
    rw [show a₁ + a₂ + a₃ + a₄ + a₅ = (a₁ + a₂ + a₃ + a₄) + a₅ from rfl,
      ZMod.val_add_of_lt (by rw [ha1234]; omega), ha1234]
  have ha123456 : (a₁ + a₂ + a₃ + a₄ + a₅ + a₆).val =
      a₁.val + a₂.val + a₃.val + a₄.val + a₅.val + a₆.val := by
    rw [show a₁ + a₂ + a₃ + a₄ + a₅ + a₆ = (a₁ + a₂ + a₃ + a₄ + a₅) + a₆ from rfl,
      ZMod.val_add_of_lt (by rw [ha12345]; omega), ha12345]
  have h_sum_val_eq : (a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇).val =
      a₁.val + a₂.val + a₃.val + a₄.val + a₅.val + a₆.val + a₇.val := by
    rw [show a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ = (a₁ + a₂ + a₃ + a₄ + a₅ + a₆) + a₇ from rfl,
      ZMod.val_add_of_lt (by rw [ha123456]; omega), ha123456]
  -- From `sum * (sum - 1) = 0`, sum ∈ {0, 1}.
  have h_sum_01' : a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ = 0 ∨
                   a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ = 1 := by
    rcases mul_eq_zero.mp h_sum_01 with h | h
    · right; linear_combination h
    · left; exact h
  -- For `a₇ = 1`, sum.val ≥ 1, so sum ≠ 0, hence sum = 1.
  have h_sum_eq_one : a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ = 1 := by
    rcases h_sum_01' with h | h
    · exfalso
      have : (a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇).val = 0 := by rw [h, ZMod.val_zero]
      rw [h_sum_val_eq] at this
      omega
    · exact h
  -- Now the val equation pins each aᵢ.val to 0 (i ∈ {1..6}).
  have h_sum_val_one : (a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇).val = 1 := by
    rw [h_sum_eq_one, h_one_val]
  rw [h_sum_val_eq, h7_val] at h_sum_val_one
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · apply (ZMod.val_eq_zero _).mp; omega

set_option maxHeartbeats 1600000 in
-- LoadX0 LD sub-opcode correct proof. Mirrors `Load.LoadDouble.correct_ld`
-- with three structural differences:
-- - No register write — `op_a = x0` makes `wX_bits 0 _` a no-op, so
--   `sp1_loadX0` only advances PC.
-- - Reader is `ITypeReaderImmutable` (rather than `ITypeReader`).
-- - 7-way sub-opcode flags `Main[41..47]` collapse via `seven_collapse_M47`
--   to give `Main[41..46] = 0`. Byte-routing constraints `E92`/`E95`/`E100`
--   then force `Main[38..40] = 0` (8-byte aligned read).
set_option debug.skipKernelTC true in
theorem correct_loadX0_ld (Main : Vector (ZMod p) 48)
    (s : SailState) (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (LoadX0.constraints Main).allHold_poly)
    (state_cstrs : (LoadX0.constraints Main).initialState_poly s)
    (h_is_loadX0_ld : Main[47] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (sp1_imm_c Main)).toNat
      reg_val + offset + 8 < 2 ^ 64)
    (h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 Main[21].val))) 8 = true)
    :
    let op_a := sp1_op_a Main
    let op_b := sp1_ob_b Main
    let imm_c := sp1_imm_c Main
    (spec_loadX0_ld imm_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_loadX0 Main).run s := by
  extract_lets op_a op_b imm_c
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  obtain ⟨_, _, _, _, _⟩ := hs_config
  -- Inline constraint flattening via simp; LoadX0 has no per-sub-opcode
  -- iff lemma, so we destructure the 29-conjunct simp normal form directly.
  simp [SP1ConstraintList.allHold_poly, LoadX0.constraints,
    AddressOperation.constraints, sub_eq_zero,
    SP1Constraint.toProp_poly] at h_cstrs
  obtain ⟨h_addr, _h_sum_or1, h_M38_or, h_M39_or, h_M40_or, h28_inv, _h_low_align,
    h_cpu, h_reader,
    h_M41_or, h_M42_or, h_M43_or, h_M44_or, h_M45_or, h_M46_or, _h_M47_or,
    h_sum_or, h_E92, h_E95, h_E100, _h_sum_or3,
    _h_E106, _h_E109, _h_E123, _h_M36_lt, _h_byte3, h_mem_isU64,
    h_E125, _h_E127⟩ := h_cstrs
  -- Use seven_collapse_M47 to derive Main[41..46] = 0.
  have ⟨hM41_zero, hM42_zero, hM43_zero, hM44_zero, hM45_zero, hM46_zero⟩ :=
    seven_collapse h_M41_or h_M42_or h_M43_or h_M44_or h_M45_or h_M46_or
      h_is_loadX0_ld (by
        rcases h_sum_or with h | h
        · rw [h, mul_zero]
        · rw [show (Main[41] + Main[42] + Main[43] + Main[44] + Main[45] + Main[46] +
            Main[47]) - 1 = 0 from by linear_combination h, zero_mul])
  -- Sum-equals-one is now derivable.
  have h_sum_eq_one : Main[41] + Main[42] + Main[43] + Main[44] + Main[45] + Main[46] +
      Main[47] = 1 := by
    rw [hM41_zero, hM42_zero, hM43_zero, hM44_zero, hM45_zero, hM46_zero, h_is_loadX0_ld]
    ring
  -- Derive Main[38..40] = 0 from byte-routing constraints.
  have hM40_zero : Main[40] = 0 := by
    rcases h_E92 with h | h
    · exfalso; rw [h_is_loadX0_ld] at h; exact one_ne_zero h
    · exact h
  have hM39_zero : Main[39] = 0 := by
    rcases h_E95 with h | h
    · exfalso
      rw [hM45_zero, hM46_zero, h_is_loadX0_ld, zero_add, zero_add] at h
      exact one_ne_zero h
    · exact h
  have hM38_zero : Main[38] = 0 := by
    rcases h_E100 with h | h
    · exfalso
      rw [hM43_zero, hM44_zero, hM45_zero, hM46_zero, h_is_loadX0_ld,
        zero_add, zero_add, zero_add, zero_add] at h
      exact one_ne_zero h
    · exact h
  -- Derive Main[13] = 1 from h_E125 (sum = 0 ∨ Main[13] = 1) + sum = 1.
  have hM13 : Main[13] = 1 := by
    rcases h_E125 with h | h
    · exfalso; rw [h_sum_eq_one] at h; exact one_ne_zero h
    · exact h
  -- AddrAdd's `is_real` argument collapses to 1 via h_sum_eq_one.
  rw [h_sum_eq_one] at h_addr
  -- Reader's `is_real` argument collapses to 1 via h_sum_eq_one.
  -- Also `Main[13] = 1` collapses the op_a_0-related clauses.
  rw [h_sum_eq_one, hM41_zero, hM42_zero, hM43_zero, hM44_zero, hM45_zero, hM46_zero,
    h_is_loadX0_ld] at h_reader
  -- Reader extraction via the iff_is_real_poly specialization.
  have h_reader' :=
    ITypeReaderImmutable.allHold_constraints_iff_is_real_poly (h := rfl) (h_trusted := rfl) |>.mp h_reader
  obtain ⟨h_trusted, h6_lt, h14_lt, h21_lt, h22_lt, h23_lt, h24_lt,
    _hM13_or, h13_iff_op_a_zero, _hPC_align, _hPC0_lt, _hPC1_lt, _hPC2_lt,
    _hM12_lt, _hM20_lt, _h_clk_a, _h_clk_b, _h_op_a_isU64, h15u64,
    _h_op_a_zero_implies⟩ := h_reader'
  -- Bounds + h_imm_se via opcode trusted_instr.
  have hp_lt : 131072 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    have h17 : (2 : ℕ) ^ 17 = 131072 := by decide
    omega
  have h32val : (32 : ZMod p).val = 32 := val_32_zmod_p
  have h65val : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
  have h35_lt_p : (35 : ℕ) < p := by omega
  have h35_val : (35 : ZMod p).val = 35 := ZMod.val_natCast_of_lt h35_lt_p
  -- The opcode argument simp-reduces to 35 since only Main[47] is non-zero.
  -- Reduce h_trusted (Opcode.trusted_instr_poly) to extract h_imm_se.
  -- The opcode value `35*Main[47]` collapses to `35`.
  -- We need: Word.toBitVec64_poly Main[21..24] = signExtend 64 (BitVec.ofNat 12 Main[21].val).
  -- h_trusted reduces to i_type_constraints_poly for opcode 35 (LD).
  -- Reduce it to extract `Main[14] < 32` and `h_imm_se`.
  simp [Opcode.trusted_instr_poly, Opcode.ofNat, Nat.ble,
    h35_val, i_type_constraints_poly] at h_trusted
  -- h_trusted now: Main[14] < 32 ∧ h_imm_se (after collapse).
  have h14_lt_zmod : Main[14] < (32 : ZMod p) := by clear *- h_trusted; simp_all only
  have h_imm_se : Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] =
      BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) := by
    clear *- h_trusted; simp_all only
  have h6 : Main[6].val < 32 := by
    have : Main[6].val < (32 : ZMod p).val := h6_lt; rwa [h32val] at this
  have h14 : Main[14].val < 32 := by
    have : Main[14].val < (32 : ZMod p).val := h14_lt_zmod; rwa [h32val] at this
  have h6_eq_zero : Main[6] = 0 := h13_iff_op_a_zero.mp hM13
  have h6_val_eq_zero : Main[6].val = 0 := by rw [h6_eq_zero, ZMod.val_zero]
  have h_op_a_zero : (BitVec.ofNat 5 Main[6].val : BitVec 5) = 0#5 := by
    rw [h6_val_eq_zero]
  have h21u64 : Word.isU64_poly #v[Main[21], Main[22], Main[23], Main[24]] := by
    apply Word.isU64_of_cases_poly <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · have : Main[21].val < (65536 : ZMod p).val := h21_lt; rwa [h65val] at this
    · have : Main[22].val < (65536 : ZMod p).val := h22_lt; rwa [h65val] at this
    · have : Main[23].val < (65536 : ZMod p).val := h23_lt; rwa [h65val] at this
    · have : Main[24].val < (65536 : ZMod p).val := h24_lt; rwa [h65val] at this
  -- Memory result Word.isU64_poly.
  have h_mem_isU64' : Word.isU64_poly #v[Main[29], Main[30], Main[31], Main[32]] := by
    apply h_mem_isU64
    rw [h_sum_eq_one]; exact one_ne_zero
  -- AddrAdd spec
  have haddr_spec := AddrAddOperation.spec_of_constraints_poly _ _ h15u64 h21u64 _ h_addr
  obtain ⟨haddr_isU64, haddr_eq⟩ := haddr_spec
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ] at haddr_isU64 haddr_eq
  have h25_lt : Main[25].val < 65536 := haddr_isU64 0
  have h26_lt : Main[26].val < 65536 := haddr_isU64 1
  have h27_lt : Main[27].val < 65536 := haddr_isU64 2
  -- Derive `h_in_range` from `h28_inv` (top-two-limb-inv) + addr bounds + alignment.
  -- LoadX0's `h28_inv` is parameterised on the 7-way is_real sum; collapse to 1.
  have h28_inv' : Main[28] * (Main[26] + Main[27]) = 1 := by
    rw [h28_inv, h_sum_eq_one]
  obtain ⟨h_addr_lo, h_addr_hi⟩ :=
    AddressOperation.addr_limbs_bounds Main[25] Main[26] Main[27] Main[28]
      h25_lt h26_lt h27_lt h28_inv'
  have h_addr_eq :
      (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] +
        Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]]).toNat =
        Main[25].val + Main[26].val * 2 ^ 16 + Main[27].val * 2 ^ 32 := by
    rw [← haddr_eq, Word.toBitVec64_poly_toNat_poly haddr_isU64,
      Word.toNat_poly_def]; simp
  have h_offset_eq :
      Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] =
        BitVec.signExtend 64 (sp1_imm_c Main) := by
    rw [h_imm_se]; rfl
  have h_align : (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] +
        Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]]).toNat % 8 = 0 := by
    have h := h_is_aligned
    rw [← h_imm_se, is_aligned_vaddr_iff_mod] at h
    exact h
  have h_in_range :
      range_subset (zero_extend (BitVec.addInt
          (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] +
            BitVec.signExtend 64 (sp1_imm_c Main)) 0))
        (to_bits 8) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true := by
    rw [← h_offset_eq]
    refine range_subset_sp1_pma _ 8 (by omega) ?_ ?_
    · rw [h_addr_eq]; exact h_addr_lo
    · omega
  have h_mem0_lt : Main[29].val < 65536 := h_mem_isU64' 0
  have h_mem1_lt : Main[30].val < 65536 := h_mem_isU64' 1
  have h_mem2_lt : Main[31].val < 65536 := h_mem_isU64' 2
  have h_mem3_lt : Main[32].val < 65536 := h_mem_isU64' 3
  -- Initial-state extraction. Mirror LoadDouble: simp + obtain.
  have h2728 : ¬ (Main[26] = 0 ∧ Main[27] = 0) := by
    intro ⟨hm26, hm27⟩
    rw [hm26, hm27, add_zero, mul_zero] at h28_inv
    rw [h_sum_eq_one] at h28_inv
    exact zero_ne_one h28_inv
  -- AddressOperation's E89/E90/E91 collapse: bit shifts are 0, so
  -- E89 = Main[25], E90 = Main[26], E91 = Main[27].
  simp [SP1ConstraintList.initialState_poly, LoadX0.constraints,
    AddressOperation.constraints, SP1Constraint.toStateProp_poly,
    AddrAddOperation.constraints, ITypeReaderImmutable.constraints,
    CPUState.constraints, BitVec.ofNatLT_eq_ofNat,
    Opcode.ofNat, Nat.ble, h6, h14, h35_val, h_is_loadX0_ld,
    hM38_zero, hM39_zero, hM40_zero, hM41_zero, hM42_zero, hM43_zero,
    hM44_zero, hM45_zero, hM46_zero, h2728] at state_cstrs
  obtain ⟨h_read_pc, _h6_op_a, h14_op_a, hload⟩ := state_cstrs
  rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_read_pc
  -- Address fits + haddr_nat + haddr_plus mirrors LoadDouble exactly.
  have h_fits_real : (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat +
      (Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]]).toNat < 2 ^ 64 := by
    have := h_fits_in_mem
    simp only [sp1_imm_c] at this
    rw [← h_imm_se] at this
    omega
  have haddr_nat : (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat +
          (Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]]).toNat =
        Word.toNat_poly #v[Main[25], Main[26], Main[27], (0 : ZMod p)] := by
    have heq := congr_arg BitVec.toNat haddr_eq
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt h_fits_real] at heq
    rw [← heq, Word.toBitVec64_poly, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by
        rw [Word.toNat_poly_def]
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ, ZMod.val_zero, Nat.zero_mul, Nat.add_zero]
        have hpow : (2 ^ 64 : ℕ) = 18446744073709551616 := by decide
        rw [hpow]
        have h26m : Main[26].val * 65536 ≤ 65535 * 65536 := by
          have : Main[26].val ≤ 65535 := by omega
          exact Nat.mul_le_mul_right _ this
        have h27m : Main[27].val * 4294967296 ≤ 65535 * 4294967296 := by
          have : Main[27].val ≤ 65535 := by omega
          exact Nat.mul_le_mul_right _ this
        omega)]
  have haddr_plus : ∀ (k : ℕ), k < 8 →
      Word.toNat_poly #v[Main[25], Main[26], Main[27], (0 : ZMod p)] + k =
      Word.toNat_poly #v[Main[25] + (k : ZMod p), Main[26], Main[27], (0 : ZMod p)] := by
    intro k hk
    have hk_val : ((k : ℕ) : ZMod p).val = k := ZMod.val_natCast_of_lt (by omega)
    have h25k_lt : Main[25].val + (k : ZMod p).val < p := by rw [hk_val]; omega
    have h25k_val : (Main[25] + (k : ZMod p)).val = Main[25].val + k := by
      rw [ZMod.val_add_of_lt h25k_lt, hk_val]
    simp only [Word.toNat_poly_def, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, ZMod.val_zero, Nat.zero_mul,
      Nat.add_zero, h25k_val]
    omega
  -- Simplify the spec side; the `wX_bits 0 _` step is a no-op.
  simp [spec_loadX0_ld, sp1_loadX0,
    sp1_op_a, sp1_ob_b, sp1_imm_c,
    op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
    EStateM.Result.map, execute_LOAD, h_read_pc, h_op_a_zero]
  rw [run_vmem_read_of_width_8' (BitVec.ofNat 5 Main[14].val)
    (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]])
    (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
    (BitVec.ofNat 8 Main[29].val)
    (BitVec.ofNat 8 (Main[29].val >>> 8))
    (BitVec.ofNat 8 Main[30].val)
    (BitVec.ofNat 8 (Main[30].val >>> 8))
    (BitVec.ofNat 8 Main[31].val)
    (BitVec.ofNat 8 (Main[31].val >>> 8))
    (BitVec.ofNat 8 Main[32].val)
    (BitVec.ofNat 8 (Main[32].val >>> 8))]
  · -- Main goal: write_reg 0 (extend_value true data) is no-op since op_a = 0;
    -- the spec and sp1 sides both reduce to the same writeReg + RETIRE_SUCCESS.
    simp
  · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true, implies_true]
  · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
  · exact h_is_aligned
  · constructor <;> simpa [Std.ExtDHashMap.get_insert]
  · exact h_fits_in_mem
  · exact h_in_range
  -- 8 memory side-conditions for bytes 0..7 (mirror LoadDouble).
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
            Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
        haddr_nat]
    simpa using hload.1
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
            Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
        haddr_nat, haddr_plus 1 (by omega)]
    simpa using hload.2.1
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
            Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
        haddr_nat, haddr_plus 2 (by omega)]
    simpa using hload.2.2.1
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
            Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
        haddr_nat, haddr_plus 3 (by omega)]
    simpa using hload.2.2.2.1
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
            Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
        haddr_nat, haddr_plus 4 (by omega)]
    simpa using hload.2.2.2.2.1
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
            Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
        haddr_nat, haddr_plus 5 (by omega)]
    simpa using hload.2.2.2.2.2.1
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
            Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
        haddr_nat, haddr_plus 6 (by omega)]
    simpa using hload.2.2.2.2.2.2.1
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
            Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
        haddr_nat, haddr_plus 7 (by omega)]
    simpa using hload.2.2.2.2.2.2.2

set_option maxHeartbeats 1600000 in
-- LoadX0 LWU sub-opcode correct proof. Mirrors `correct_loadX0_ld`
-- but for 4-byte unsigned load. Key differences:
-- - Selected flag: `Main[46] = 1` (instead of `Main[47] = 1`).
-- - Width 4 (uses `run_vmem_read_of_width_4'`); 4-byte alignment.
-- - Byte-routing constraints force `Main[38] = Main[39] = 0`, but
--   `Main[40]` (bit2) is free. We case-split on `h_M40_or` and
--   provide bytes from `Main[29..30]` (bit2=0) or `Main[31..32]`
--   (bit2=1) to `run_vmem_read_of_width_4'`.
-- - The opcode encoding `E14` collapses to `34` (LWU) since only
--   `Main[46] = 1`.
set_option debug.skipKernelTC true in
theorem correct_loadX0_lwu (Main : Vector (ZMod p) 48)
    (s : SailState) (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (LoadX0.constraints Main).allHold_poly)
    (state_cstrs : (LoadX0.constraints Main).initialState_poly s)
    (h_is_loadX0_lwu : Main[46] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (sp1_imm_c Main)).toNat
      reg_val + offset + 4 < 2 ^ 64)
    (h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 Main[21].val))) 4 = true)
    :
    let op_a := sp1_op_a Main
    let op_b := sp1_ob_b Main
    let imm_c := sp1_imm_c Main
    (spec_loadX0_lwu imm_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_loadX0 Main).run s := by
  extract_lets op_a op_b imm_c
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  obtain ⟨_, _, _, _, _⟩ := hs_config
  simp [SP1ConstraintList.allHold_poly, LoadX0.constraints,
    AddressOperation.constraints, sub_eq_zero,
    SP1Constraint.toProp_poly] at h_cstrs
  obtain ⟨h_addr, _h_sum_or1, h_M38_or, h_M39_or, h_M40_or, h28_inv, _h_low_align,
    h_cpu, h_reader,
    h_M41_or, h_M42_or, h_M43_or, h_M44_or, h_M45_or, _h_M46_or, h_M47_or,
    h_sum_or, h_E92, h_E95, h_E100, _h_sum_or3,
    _h_E106, _h_E109, _h_E123, _h_M36_lt, _h_byte3, h_mem_isU64,
    h_E125, _h_E127⟩ := h_cstrs
  -- seven_collapse: select Main[46] as a₇; permute the rest as a₁..a₆.
  have ⟨hM41_zero, hM42_zero, hM43_zero, hM44_zero, hM45_zero, hM47_zero⟩ :=
    seven_collapse h_M41_or h_M42_or h_M43_or h_M44_or h_M45_or h_M47_or
      h_is_loadX0_lwu (by
        rcases h_sum_or with h | h
        · rw [show (Main[41] + Main[42] + Main[43] + Main[44] + Main[45] + Main[47] +
            Main[46]) = 0 from by linear_combination h]; ring
        · rw [show (Main[41] + Main[42] + Main[43] + Main[44] + Main[45] + Main[47] +
            Main[46]) - 1 = 0 from by linear_combination h, zero_mul])
  -- Sum-equals-one is now derivable.
  have h_sum_eq_one : Main[41] + Main[42] + Main[43] + Main[44] + Main[45] + Main[46] +
      Main[47] = 1 := by
    rw [hM41_zero, hM42_zero, hM43_zero, hM44_zero, hM45_zero, hM47_zero, h_is_loadX0_lwu]
    ring
  -- Derive Main[38] = Main[39] = 0; Main[40] is free (in {0,1}).
  -- E92 = Main[47] * Main[40], with Main[47] = 0 — gives no info on Main[40].
  -- E95 = (Main[45] + Main[46] + Main[47]) * Main[39] forces Main[39] = 0.
  have hM39_zero : Main[39] = 0 := by
    rcases h_E95 with h | h
    · exfalso
      rw [hM45_zero, hM47_zero, h_is_loadX0_lwu, zero_add, add_zero] at h
      exact one_ne_zero h
    · exact h
  -- E100 = (Main[43]+Main[44]+Main[45]+Main[46]+Main[47]) * Main[38] forces Main[38] = 0.
  have hM38_zero : Main[38] = 0 := by
    rcases h_E100 with h | h
    · exfalso
      rw [hM43_zero, hM44_zero, hM45_zero, hM47_zero, h_is_loadX0_lwu,
        zero_add, zero_add, zero_add, add_zero] at h
      exact one_ne_zero h
    · exact h
  -- Derive Main[13] = 1 from h_E125.
  have hM13 : Main[13] = 1 := by
    rcases h_E125 with h | h
    · exfalso; rw [h_sum_eq_one] at h; exact one_ne_zero h
    · exact h
  rw [h_sum_eq_one] at h_addr
  rw [h_sum_eq_one, hM41_zero, hM42_zero, hM43_zero, hM44_zero, hM45_zero, hM47_zero,
    h_is_loadX0_lwu] at h_reader
  have h_reader' :=
    ITypeReaderImmutable.allHold_constraints_iff_is_real_poly (h := rfl) (h_trusted := rfl) |>.mp h_reader
  obtain ⟨h_trusted, h6_lt, h14_lt, h21_lt, h22_lt, h23_lt, h24_lt,
    _hM13_or, h13_iff_op_a_zero, _hPC_align, _hPC0_lt, _hPC1_lt, _hPC2_lt,
    _hM12_lt, _hM20_lt, _h_clk_a, _h_clk_b, _h_op_a_isU64, h15u64,
    _h_op_a_zero_implies⟩ := h_reader'
  have hp_lt : 131072 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    have h17 : (2 : ℕ) ^ 17 = 131072 := by decide
    omega
  have h32val : (32 : ZMod p).val = 32 := val_32_zmod_p
  have h65val : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
  have h34_lt_p : (34 : ℕ) < p := by omega
  have h34_val : (34 : ZMod p).val = 34 := ZMod.val_natCast_of_lt h34_lt_p
  -- The opcode argument simp-reduces to 34 since only Main[46] is non-zero.
  simp [Opcode.trusted_instr_poly, Opcode.ofNat, Nat.ble,
    h34_val, i_type_constraints_poly] at h_trusted
  have h14_lt_zmod : Main[14] < (32 : ZMod p) := by clear *- h_trusted; simp_all only
  have h_imm_se : Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] =
      BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) := by
    clear *- h_trusted; simp_all only
  have h6 : Main[6].val < 32 := by
    have : Main[6].val < (32 : ZMod p).val := h6_lt; rwa [h32val] at this
  have h14 : Main[14].val < 32 := by
    have : Main[14].val < (32 : ZMod p).val := h14_lt_zmod; rwa [h32val] at this
  have h6_eq_zero : Main[6] = 0 := h13_iff_op_a_zero.mp hM13
  have h6_val_eq_zero : Main[6].val = 0 := by rw [h6_eq_zero, ZMod.val_zero]
  have h_op_a_zero : (BitVec.ofNat 5 Main[6].val : BitVec 5) = 0#5 := by
    rw [h6_val_eq_zero]
  have h21u64 : Word.isU64_poly #v[Main[21], Main[22], Main[23], Main[24]] := by
    apply Word.isU64_of_cases_poly <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · have : Main[21].val < (65536 : ZMod p).val := h21_lt; rwa [h65val] at this
    · have : Main[22].val < (65536 : ZMod p).val := h22_lt; rwa [h65val] at this
    · have : Main[23].val < (65536 : ZMod p).val := h23_lt; rwa [h65val] at this
    · have : Main[24].val < (65536 : ZMod p).val := h24_lt; rwa [h65val] at this
  have h_mem_isU64' : Word.isU64_poly #v[Main[29], Main[30], Main[31], Main[32]] := by
    apply h_mem_isU64
    rw [h_sum_eq_one]; exact one_ne_zero
  have haddr_spec := AddrAddOperation.spec_of_constraints_poly _ _ h15u64 h21u64 _ h_addr
  obtain ⟨haddr_isU64, haddr_eq⟩ := haddr_spec
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ] at haddr_isU64 haddr_eq
  have h25_lt : Main[25].val < 65536 := haddr_isU64 0
  have h26_lt : Main[26].val < 65536 := haddr_isU64 1
  have h27_lt : Main[27].val < 65536 := haddr_isU64 2
  have h28_inv' : Main[28] * (Main[26] + Main[27]) = 1 := by
    rw [h28_inv, h_sum_eq_one]
  obtain ⟨h_addr_lo, h_addr_hi⟩ :=
    AddressOperation.addr_limbs_bounds Main[25] Main[26] Main[27] Main[28]
      h25_lt h26_lt h27_lt h28_inv'
  have h_addr_eq :
      (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] +
        Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]]).toNat =
        Main[25].val + Main[26].val * 2 ^ 16 + Main[27].val * 2 ^ 32 := by
    rw [← haddr_eq, Word.toBitVec64_poly_toNat_poly haddr_isU64,
      Word.toNat_poly_def]; simp
  have h_offset_eq :
      Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] =
        BitVec.signExtend 64 (sp1_imm_c Main) := by
    rw [h_imm_se]; rfl
  have h_align : (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] +
        Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]]).toNat % 4 = 0 := by
    have h := h_is_aligned
    rw [← h_imm_se, is_aligned_vaddr_iff_mod] at h
    exact h
  have h_in_range :
      range_subset (zero_extend (BitVec.addInt
          (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] +
            BitVec.signExtend 64 (sp1_imm_c Main)) 0))
        (to_bits 4) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true := by
    rw [← h_offset_eq]
    refine range_subset_sp1_pma _ 4 (by omega) ?_ ?_
    · rw [h_addr_eq]; exact h_addr_lo
    · omega
  have h_mem0_lt : Main[29].val < 65536 := h_mem_isU64' 0
  have h_mem1_lt : Main[30].val < 65536 := h_mem_isU64' 1
  have h_mem2_lt : Main[31].val < 65536 := h_mem_isU64' 2
  have h_mem3_lt : Main[32].val < 65536 := h_mem_isU64' 3
  have h2728 : ¬ (Main[26] = 0 ∧ Main[27] = 0) := by
    intro ⟨hm26, hm27⟩
    rw [hm26, hm27, add_zero, mul_zero] at h28_inv
    rw [h_sum_eq_one] at h28_inv
    exact zero_ne_one h28_inv
  -- For LWU we don't pre-fold Main[40] (it's free in {0,1}).
  simp [SP1ConstraintList.initialState_poly, LoadX0.constraints,
    AddressOperation.constraints, SP1Constraint.toStateProp_poly,
    AddrAddOperation.constraints, ITypeReaderImmutable.constraints,
    CPUState.constraints, BitVec.ofNatLT_eq_ofNat,
    Opcode.ofNat, Nat.ble, h6, h14, h34_val, h_is_loadX0_lwu,
    hM38_zero, hM39_zero, hM41_zero, hM42_zero, hM43_zero,
    hM44_zero, hM45_zero, hM47_zero, h2728] at state_cstrs
  obtain ⟨h_read_pc, _h6_op_a, h14_op_a, hload⟩ := state_cstrs
  rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_read_pc
  have h_fits_real : (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat +
      (Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]]).toNat < 2 ^ 64 := by
    have := h_fits_in_mem
    simp only [sp1_imm_c] at this
    rw [← h_imm_se] at this
    omega
  have haddr_nat : (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat +
          (Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]]).toNat =
        Word.toNat_poly #v[Main[25], Main[26], Main[27], (0 : ZMod p)] := by
    have heq := congr_arg BitVec.toNat haddr_eq
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt h_fits_real] at heq
    rw [← heq, Word.toBitVec64_poly, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by
        rw [Word.toNat_poly_def]
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ, ZMod.val_zero, Nat.zero_mul, Nat.add_zero]
        have hpow : (2 ^ 64 : ℕ) = 18446744073709551616 := by decide
        rw [hpow]
        have h26m : Main[26].val * 65536 ≤ 65535 * 65536 := by
          have : Main[26].val ≤ 65535 := by omega
          exact Nat.mul_le_mul_right _ this
        have h27m : Main[27].val * 4294967296 ≤ 65535 * 4294967296 := by
          have : Main[27].val ≤ 65535 := by omega
          exact Nat.mul_le_mul_right _ this
        omega)]
  have haddr_plus : ∀ (k : ℕ), k < 8 →
      Word.toNat_poly #v[Main[25], Main[26], Main[27], (0 : ZMod p)] + k =
      Word.toNat_poly #v[Main[25] + (k : ZMod p), Main[26], Main[27], (0 : ZMod p)] := by
    intro k hk
    have hk_val : ((k : ℕ) : ZMod p).val = k := ZMod.val_natCast_of_lt (by omega)
    have h25k_lt : Main[25].val + (k : ZMod p).val < p := by rw [hk_val]; omega
    have h25k_val : (Main[25] + (k : ZMod p)).val = Main[25].val + k := by
      rw [ZMod.val_add_of_lt h25k_lt, hk_val]
    simp only [Word.toNat_poly_def, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, ZMod.val_zero, Nat.zero_mul,
      Nat.add_zero, h25k_val]
    omega
  -- Case-split on bit2 (Main[40]).
  rcases h_M40_or with hM40_zero | hM40_one
  · -- Bit2 = 0: aligned address = unaligned. Use bytes from Main[29], Main[30].
    simp [spec_loadX0_lwu, sp1_loadX0,
      sp1_op_a, sp1_ob_b, sp1_imm_c,
      op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
      EStateM.Result.map, execute_LOAD, h_read_pc, h_op_a_zero]
    rw [run_vmem_read_of_width_4' (BitVec.ofNat 5 Main[14].val)
      (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]])
      (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
      (BitVec.ofNat 8 Main[29].val)
      (BitVec.ofNat 8 (Main[29].val >>> 8))
      (BitVec.ofNat 8 Main[30].val)
      (BitVec.ofNat 8 (Main[30].val >>> 8))]
    · simp
    · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true,
        implies_true]
    · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
    · exact h_is_aligned
    · constructor <;> simpa [Std.ExtDHashMap.get_insert]
    · exact h_fits_in_mem
    · exact h_in_range
    · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
              Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
          haddr_nat,
          show (Main[25] : ZMod p) = Main[25] - 4 * Main[40] from by rw [hM40_zero]; ring]
      simpa using hload.1
    · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
              Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
          haddr_nat, haddr_plus 1 (by omega),
          show (Main[25] + ((1 : ℕ) : ZMod p) : ZMod p) =
            Main[25] - 4 * Main[40] + 1 from by rw [hM40_zero]; push_cast; ring]
      simpa using hload.2.1
    · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
              Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
          haddr_nat, haddr_plus 2 (by omega),
          show (Main[25] + ((2 : ℕ) : ZMod p) : ZMod p) =
            Main[25] - 4 * Main[40] + 2 from by rw [hM40_zero]; push_cast; ring]
      simpa using hload.2.2.1
    · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
              Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
          haddr_nat, haddr_plus 3 (by omega),
          show (Main[25] + ((3 : ℕ) : ZMod p) : ZMod p) =
            Main[25] - 4 * Main[40] + 3 from by rw [hM40_zero]; push_cast; ring]
      simpa using hload.2.2.2.1
  · -- Bit2 = 1: aligned = unaligned - 4. Use bytes from Main[31], Main[32].
    simp [spec_loadX0_lwu, sp1_loadX0,
      sp1_op_a, sp1_ob_b, sp1_imm_c,
      op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
      EStateM.Result.map, execute_LOAD, h_read_pc, h_op_a_zero]
    rw [run_vmem_read_of_width_4' (BitVec.ofNat 5 Main[14].val)
      (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]])
      (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
      (BitVec.ofNat 8 Main[31].val)
      (BitVec.ofNat 8 (Main[31].val >>> 8))
      (BitVec.ofNat 8 Main[32].val)
      (BitVec.ofNat 8 (Main[32].val >>> 8))]
    · simp
    · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true,
        implies_true]
    · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
    · exact h_is_aligned
    · constructor <;> simpa [Std.ExtDHashMap.get_insert]
    · exact h_fits_in_mem
    · exact h_in_range
    -- byte 0 at unaligned + 0 = aligned + 4 → hload offset-4 byte (Main[31] low).
    · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
              Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
          haddr_nat,
          show (Main[25] : ZMod p) = Main[25] - 4 * Main[40] + 4 from by rw [hM40_one]; ring]
      simpa using hload.2.2.2.2.1
    · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
              Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
          haddr_nat, haddr_plus 1 (by omega),
          show (Main[25] + ((1 : ℕ) : ZMod p) : ZMod p) =
            Main[25] - 4 * Main[40] + 5 from by rw [hM40_one]; push_cast; ring]
      simpa using hload.2.2.2.2.2.1
    · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
              Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
          haddr_nat, haddr_plus 2 (by omega),
          show (Main[25] + ((2 : ℕ) : ZMod p) : ZMod p) =
            Main[25] - 4 * Main[40] + 6 from by rw [hM40_one]; push_cast; ring]
      simpa using hload.2.2.2.2.2.2.1
    · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
              Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
          haddr_nat, haddr_plus 3 (by omega),
          show (Main[25] + ((3 : ℕ) : ZMod p) : ZMod p) =
            Main[25] - 4 * Main[40] + 7 from by rw [hM40_one]; push_cast; ring]
      simpa using hload.2.2.2.2.2.2.2

set_option maxHeartbeats 1600000 in
-- LoadX0 LW sub-opcode correct proof. Mirrors `correct_loadX0_lwu`
-- but for the signed 4-byte load. Key differences:
-- - Selected flag: `Main[45] = 1` (instead of `Main[46] = 1`).
-- - Width 4 (uses `run_vmem_read_of_width_4'`); 4-byte alignment.
-- - Byte-routing constraints force `Main[38] = Main[39] = 0`, but
--   `Main[40]` (bit2) is free. Same routing as LWU.
-- - The opcode encoding `E14` collapses to `31` (LW) since only
--   `Main[45] = 1`.
-- - Sign-extension does not matter because `rd = x0` makes `wX_bits 0`
--   a no-op.
set_option debug.skipKernelTC true in
theorem correct_loadX0_lw (Main : Vector (ZMod p) 48)
    (s : SailState) (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (LoadX0.constraints Main).allHold_poly)
    (state_cstrs : (LoadX0.constraints Main).initialState_poly s)
    (h_is_loadX0_lw : Main[45] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (sp1_imm_c Main)).toNat
      reg_val + offset + 4 < 2 ^ 64)
    (h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 Main[21].val))) 4 = true)
    :
    let op_a := sp1_op_a Main
    let op_b := sp1_ob_b Main
    let imm_c := sp1_imm_c Main
    (spec_loadX0_lw imm_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_loadX0 Main).run s := by
  extract_lets op_a op_b imm_c
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  obtain ⟨_, _, _, _, _⟩ := hs_config
  simp [SP1ConstraintList.allHold_poly, LoadX0.constraints,
    AddressOperation.constraints, sub_eq_zero,
    SP1Constraint.toProp_poly] at h_cstrs
  obtain ⟨h_addr, _h_sum_or1, h_M38_or, h_M39_or, h_M40_or, h28_inv, _h_low_align,
    h_cpu, h_reader,
    h_M41_or, h_M42_or, h_M43_or, h_M44_or, _h_M45_or, h_M46_or, h_M47_or,
    h_sum_or, h_E92, h_E95, h_E100, _h_sum_or3,
    _h_E106, _h_E109, _h_E123, _h_M36_lt, _h_byte3, h_mem_isU64,
    h_E125, _h_E127⟩ := h_cstrs
  -- seven_collapse: select Main[45] as a₇; permute the rest as a₁..a₆.
  have ⟨hM41_zero, hM42_zero, hM43_zero, hM44_zero, hM46_zero, hM47_zero⟩ :=
    seven_collapse h_M41_or h_M42_or h_M43_or h_M44_or h_M46_or h_M47_or
      h_is_loadX0_lw (by
        rcases h_sum_or with h | h
        · rw [show (Main[41] + Main[42] + Main[43] + Main[44] + Main[46] + Main[47] +
            Main[45]) = 0 from by linear_combination h]; ring
        · rw [show (Main[41] + Main[42] + Main[43] + Main[44] + Main[46] + Main[47] +
            Main[45]) - 1 = 0 from by linear_combination h, zero_mul])
  -- Sum-equals-one is now derivable.
  have h_sum_eq_one : Main[41] + Main[42] + Main[43] + Main[44] + Main[45] + Main[46] +
      Main[47] = 1 := by
    rw [hM41_zero, hM42_zero, hM43_zero, hM44_zero, hM46_zero, hM47_zero, h_is_loadX0_lw]
    ring
  -- Derive Main[38] = Main[39] = 0; Main[40] is free (in {0,1}).
  -- E92 = Main[47] * Main[40], with Main[47] = 0 — gives no info on Main[40].
  -- E95 = (Main[45] + Main[46] + Main[47]) * Main[39] forces Main[39] = 0
  -- (since Main[45] = 1 here).
  have hM39_zero : Main[39] = 0 := by
    rcases h_E95 with h | h
    · exfalso
      rw [hM46_zero, hM47_zero, h_is_loadX0_lw, add_zero, add_zero] at h
      exact one_ne_zero h
    · exact h
  -- E100 = (Main[43]+Main[44]+Main[45]+Main[46]+Main[47]) * Main[38] forces Main[38] = 0.
  have hM38_zero : Main[38] = 0 := by
    rcases h_E100 with h | h
    · exfalso
      rw [hM43_zero, hM44_zero, hM46_zero, hM47_zero, h_is_loadX0_lw,
        zero_add, zero_add, add_zero, add_zero] at h
      exact one_ne_zero h
    · exact h
  -- Derive Main[13] = 1 from h_E125.
  have hM13 : Main[13] = 1 := by
    rcases h_E125 with h | h
    · exfalso; rw [h_sum_eq_one] at h; exact one_ne_zero h
    · exact h
  rw [h_sum_eq_one] at h_addr
  rw [h_sum_eq_one, hM41_zero, hM42_zero, hM43_zero, hM44_zero, hM46_zero, hM47_zero,
    h_is_loadX0_lw] at h_reader
  have h_reader' :=
    ITypeReaderImmutable.allHold_constraints_iff_is_real_poly (h := rfl) (h_trusted := rfl) |>.mp h_reader
  obtain ⟨h_trusted, h6_lt, h14_lt, h21_lt, h22_lt, h23_lt, h24_lt,
    _hM13_or, h13_iff_op_a_zero, _hPC_align, _hPC0_lt, _hPC1_lt, _hPC2_lt,
    _hM12_lt, _hM20_lt, _h_clk_a, _h_clk_b, _h_op_a_isU64, h15u64,
    _h_op_a_zero_implies⟩ := h_reader'
  have hp_lt : 131072 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    have h17 : (2 : ℕ) ^ 17 = 131072 := by decide
    omega
  have h32val : (32 : ZMod p).val = 32 := val_32_zmod_p
  have h65val : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
  have h31_lt_p : (31 : ℕ) < p := by omega
  have h31_val : (31 : ZMod p).val = 31 := ZMod.val_natCast_of_lt h31_lt_p
  -- The opcode argument simp-reduces to 31 since only Main[45] is non-zero.
  simp [Opcode.trusted_instr_poly, Opcode.ofNat, Nat.ble,
    h31_val, i_type_constraints_poly] at h_trusted
  have h14_lt_zmod : Main[14] < (32 : ZMod p) := by clear *- h_trusted; simp_all only
  have h_imm_se : Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] =
      BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) := by
    clear *- h_trusted; simp_all only
  have h6 : Main[6].val < 32 := by
    have : Main[6].val < (32 : ZMod p).val := h6_lt; rwa [h32val] at this
  have h14 : Main[14].val < 32 := by
    have : Main[14].val < (32 : ZMod p).val := h14_lt_zmod; rwa [h32val] at this
  have h6_eq_zero : Main[6] = 0 := h13_iff_op_a_zero.mp hM13
  have h6_val_eq_zero : Main[6].val = 0 := by rw [h6_eq_zero, ZMod.val_zero]
  have h_op_a_zero : (BitVec.ofNat 5 Main[6].val : BitVec 5) = 0#5 := by
    rw [h6_val_eq_zero]
  have h21u64 : Word.isU64_poly #v[Main[21], Main[22], Main[23], Main[24]] := by
    apply Word.isU64_of_cases_poly <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · have : Main[21].val < (65536 : ZMod p).val := h21_lt; rwa [h65val] at this
    · have : Main[22].val < (65536 : ZMod p).val := h22_lt; rwa [h65val] at this
    · have : Main[23].val < (65536 : ZMod p).val := h23_lt; rwa [h65val] at this
    · have : Main[24].val < (65536 : ZMod p).val := h24_lt; rwa [h65val] at this
  have h_mem_isU64' : Word.isU64_poly #v[Main[29], Main[30], Main[31], Main[32]] := by
    apply h_mem_isU64
    rw [h_sum_eq_one]; exact one_ne_zero
  have haddr_spec := AddrAddOperation.spec_of_constraints_poly _ _ h15u64 h21u64 _ h_addr
  obtain ⟨haddr_isU64, haddr_eq⟩ := haddr_spec
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ] at haddr_isU64 haddr_eq
  have h25_lt : Main[25].val < 65536 := haddr_isU64 0
  have h26_lt : Main[26].val < 65536 := haddr_isU64 1
  have h27_lt : Main[27].val < 65536 := haddr_isU64 2
  have h28_inv' : Main[28] * (Main[26] + Main[27]) = 1 := by
    rw [h28_inv, h_sum_eq_one]
  obtain ⟨h_addr_lo, h_addr_hi⟩ :=
    AddressOperation.addr_limbs_bounds Main[25] Main[26] Main[27] Main[28]
      h25_lt h26_lt h27_lt h28_inv'
  have h_addr_eq :
      (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] +
        Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]]).toNat =
        Main[25].val + Main[26].val * 2 ^ 16 + Main[27].val * 2 ^ 32 := by
    rw [← haddr_eq, Word.toBitVec64_poly_toNat_poly haddr_isU64,
      Word.toNat_poly_def]; simp
  have h_offset_eq :
      Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] =
        BitVec.signExtend 64 (sp1_imm_c Main) := by
    rw [h_imm_se]; rfl
  have h_align : (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] +
        Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]]).toNat % 4 = 0 := by
    have h := h_is_aligned
    rw [← h_imm_se, is_aligned_vaddr_iff_mod] at h
    exact h
  have h_in_range :
      range_subset (zero_extend (BitVec.addInt
          (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] +
            BitVec.signExtend 64 (sp1_imm_c Main)) 0))
        (to_bits 4) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true := by
    rw [← h_offset_eq]
    refine range_subset_sp1_pma _ 4 (by omega) ?_ ?_
    · rw [h_addr_eq]; exact h_addr_lo
    · omega
  have h_mem0_lt : Main[29].val < 65536 := h_mem_isU64' 0
  have h_mem1_lt : Main[30].val < 65536 := h_mem_isU64' 1
  have h_mem2_lt : Main[31].val < 65536 := h_mem_isU64' 2
  have h_mem3_lt : Main[32].val < 65536 := h_mem_isU64' 3
  have h2728 : ¬ (Main[26] = 0 ∧ Main[27] = 0) := by
    intro ⟨hm26, hm27⟩
    rw [hm26, hm27, add_zero, mul_zero] at h28_inv
    rw [h_sum_eq_one] at h28_inv
    exact zero_ne_one h28_inv
  -- For LW we don't pre-fold Main[40] (it's free in {0,1}).
  simp [SP1ConstraintList.initialState_poly, LoadX0.constraints,
    AddressOperation.constraints, SP1Constraint.toStateProp_poly,
    AddrAddOperation.constraints, ITypeReaderImmutable.constraints,
    CPUState.constraints, BitVec.ofNatLT_eq_ofNat,
    Opcode.ofNat, Nat.ble, h6, h14, h31_val, h_is_loadX0_lw,
    hM38_zero, hM39_zero, hM41_zero, hM42_zero, hM43_zero,
    hM44_zero, hM46_zero, hM47_zero, h2728] at state_cstrs
  obtain ⟨h_read_pc, _h6_op_a, h14_op_a, hload⟩ := state_cstrs
  rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_read_pc
  have h_fits_real : (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat +
      (Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]]).toNat < 2 ^ 64 := by
    have := h_fits_in_mem
    simp only [sp1_imm_c] at this
    rw [← h_imm_se] at this
    omega
  have haddr_nat : (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat +
          (Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]]).toNat =
        Word.toNat_poly #v[Main[25], Main[26], Main[27], (0 : ZMod p)] := by
    have heq := congr_arg BitVec.toNat haddr_eq
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt h_fits_real] at heq
    rw [← heq, Word.toBitVec64_poly, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by
        rw [Word.toNat_poly_def]
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ, ZMod.val_zero, Nat.zero_mul, Nat.add_zero]
        have hpow : (2 ^ 64 : ℕ) = 18446744073709551616 := by decide
        rw [hpow]
        have h26m : Main[26].val * 65536 ≤ 65535 * 65536 := by
          have : Main[26].val ≤ 65535 := by omega
          exact Nat.mul_le_mul_right _ this
        have h27m : Main[27].val * 4294967296 ≤ 65535 * 4294967296 := by
          have : Main[27].val ≤ 65535 := by omega
          exact Nat.mul_le_mul_right _ this
        omega)]
  have haddr_plus : ∀ (k : ℕ), k < 8 →
      Word.toNat_poly #v[Main[25], Main[26], Main[27], (0 : ZMod p)] + k =
      Word.toNat_poly #v[Main[25] + (k : ZMod p), Main[26], Main[27], (0 : ZMod p)] := by
    intro k hk
    have hk_val : ((k : ℕ) : ZMod p).val = k := ZMod.val_natCast_of_lt (by omega)
    have h25k_lt : Main[25].val + (k : ZMod p).val < p := by rw [hk_val]; omega
    have h25k_val : (Main[25] + (k : ZMod p)).val = Main[25].val + k := by
      rw [ZMod.val_add_of_lt h25k_lt, hk_val]
    simp only [Word.toNat_poly_def, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, ZMod.val_zero, Nat.zero_mul,
      Nat.add_zero, h25k_val]
    omega
  -- Case-split on bit2 (Main[40]).
  rcases h_M40_or with hM40_zero | hM40_one
  · -- Bit2 = 0: aligned address = unaligned. Use bytes from Main[29], Main[30].
    simp [spec_loadX0_lw, sp1_loadX0,
      sp1_op_a, sp1_ob_b, sp1_imm_c,
      op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
      EStateM.Result.map, execute_LOAD, h_read_pc, h_op_a_zero]
    rw [run_vmem_read_of_width_4' (BitVec.ofNat 5 Main[14].val)
      (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]])
      (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
      (BitVec.ofNat 8 Main[29].val)
      (BitVec.ofNat 8 (Main[29].val >>> 8))
      (BitVec.ofNat 8 Main[30].val)
      (BitVec.ofNat 8 (Main[30].val >>> 8))]
    · simp
    · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true,
        implies_true]
    · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
    · exact h_is_aligned
    · constructor <;> simpa [Std.ExtDHashMap.get_insert]
    · exact h_fits_in_mem
    · exact h_in_range
    · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
              Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
          haddr_nat,
          show (Main[25] : ZMod p) = Main[25] - 4 * Main[40] from by rw [hM40_zero]; ring]
      simpa using hload.1
    · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
              Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
          haddr_nat, haddr_plus 1 (by omega),
          show (Main[25] + ((1 : ℕ) : ZMod p) : ZMod p) =
            Main[25] - 4 * Main[40] + 1 from by rw [hM40_zero]; push_cast; ring]
      simpa using hload.2.1
    · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
              Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
          haddr_nat, haddr_plus 2 (by omega),
          show (Main[25] + ((2 : ℕ) : ZMod p) : ZMod p) =
            Main[25] - 4 * Main[40] + 2 from by rw [hM40_zero]; push_cast; ring]
      simpa using hload.2.2.1
    · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
              Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
          haddr_nat, haddr_plus 3 (by omega),
          show (Main[25] + ((3 : ℕ) : ZMod p) : ZMod p) =
            Main[25] - 4 * Main[40] + 3 from by rw [hM40_zero]; push_cast; ring]
      simpa using hload.2.2.2.1
  · -- Bit2 = 1: aligned = unaligned - 4. Use bytes from Main[31], Main[32].
    simp [spec_loadX0_lw, sp1_loadX0,
      sp1_op_a, sp1_ob_b, sp1_imm_c,
      op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
      EStateM.Result.map, execute_LOAD, h_read_pc, h_op_a_zero]
    rw [run_vmem_read_of_width_4' (BitVec.ofNat 5 Main[14].val)
      (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]])
      (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
      (BitVec.ofNat 8 Main[31].val)
      (BitVec.ofNat 8 (Main[31].val >>> 8))
      (BitVec.ofNat 8 Main[32].val)
      (BitVec.ofNat 8 (Main[32].val >>> 8))]
    · simp
    · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true,
        implies_true]
    · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
    · exact h_is_aligned
    · constructor <;> simpa [Std.ExtDHashMap.get_insert]
    · exact h_fits_in_mem
    · exact h_in_range
    -- byte 0 at unaligned + 0 = aligned + 4 → hload offset-4 byte (Main[31] low).
    · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
              Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
          haddr_nat,
          show (Main[25] : ZMod p) = Main[25] - 4 * Main[40] + 4 from by rw [hM40_one]; ring]
      simpa using hload.2.2.2.2.1
    · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
              Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
          haddr_nat, haddr_plus 1 (by omega),
          show (Main[25] + ((1 : ℕ) : ZMod p) : ZMod p) =
            Main[25] - 4 * Main[40] + 5 from by rw [hM40_one]; push_cast; ring]
      simpa using hload.2.2.2.2.2.1
    · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
              Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
          haddr_nat, haddr_plus 2 (by omega),
          show (Main[25] + ((2 : ℕ) : ZMod p) : ZMod p) =
            Main[25] - 4 * Main[40] + 6 from by rw [hM40_one]; push_cast; ring]
      simpa using hload.2.2.2.2.2.2.1
    · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
              Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
          haddr_nat, haddr_plus 3 (by omega),
          show (Main[25] + ((3 : ℕ) : ZMod p) : ZMod p) =
            Main[25] - 4 * Main[40] + 7 from by rw [hM40_one]; push_cast; ring]
      simpa using hload.2.2.2.2.2.2.2

set_option maxHeartbeats 1600000 in
-- LoadX0 LHU sub-opcode correct proof. Mirrors `correct_loadX0_lwu`
-- but for 2-byte unsigned load. Key differences:
-- - Selected flag: `Main[44] = 1` (instead of `Main[46] = 1`).
-- - Width 2 (uses `run_vmem_read_of_width_2'`); 2-byte alignment.
-- - Byte-routing constraints force `Main[38] = 0`, but BOTH `Main[40]`
--   (bit2) and `Main[39]` (bit1) are free. We do a 4-way nested
--   case-split on (Main[40], Main[39]) and provide bytes from
--   `Main[29..32]` per case.
-- - The opcode encoding `E14` collapses to `33` (LHU) since only
--   `Main[44] = 1`.
set_option debug.skipKernelTC true in
theorem correct_loadX0_lhu (Main : Vector (ZMod p) 48)
    (s : SailState) (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (LoadX0.constraints Main).allHold_poly)
    (state_cstrs : (LoadX0.constraints Main).initialState_poly s)
    (h_is_loadX0_lhu : Main[44] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (sp1_imm_c Main)).toNat
      reg_val + offset + 2 < 2 ^ 64)
    (h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 Main[21].val))) 2 = true)
    :
    let op_a := sp1_op_a Main
    let op_b := sp1_ob_b Main
    let imm_c := sp1_imm_c Main
    (spec_loadX0_lhu imm_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_loadX0 Main).run s := by
  extract_lets op_a op_b imm_c
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  obtain ⟨_, _, _, _, _⟩ := hs_config
  simp [SP1ConstraintList.allHold_poly, LoadX0.constraints,
    AddressOperation.constraints, sub_eq_zero,
    SP1Constraint.toProp_poly] at h_cstrs
  obtain ⟨h_addr, _h_sum_or1, h_M38_or, h_M39_or, h_M40_or, h28_inv, _h_low_align,
    h_cpu, h_reader,
    h_M41_or, h_M42_or, h_M43_or, _h_M44_or, h_M45_or, h_M46_or, h_M47_or,
    h_sum_or, h_E92, h_E95, h_E100, _h_sum_or3,
    _h_E106, _h_E109, _h_E123, _h_M36_lt, _h_byte3, h_mem_isU64,
    h_E125, _h_E127⟩ := h_cstrs
  -- seven_collapse: select Main[44] as a₇; permute the rest as a₁..a₆.
  have ⟨hM41_zero, hM42_zero, hM43_zero, hM45_zero, hM46_zero, hM47_zero⟩ :=
    seven_collapse h_M41_or h_M42_or h_M43_or h_M45_or h_M46_or h_M47_or
      h_is_loadX0_lhu (by
        rcases h_sum_or with h | h
        · rw [show (Main[41] + Main[42] + Main[43] + Main[45] + Main[46] + Main[47] +
            Main[44]) = 0 from by linear_combination h]; ring
        · rw [show (Main[41] + Main[42] + Main[43] + Main[45] + Main[46] + Main[47] +
            Main[44]) - 1 = 0 from by linear_combination h, zero_mul])
  -- Sum-equals-one is now derivable.
  have h_sum_eq_one : Main[41] + Main[42] + Main[43] + Main[44] + Main[45] + Main[46] +
      Main[47] = 1 := by
    rw [hM41_zero, hM42_zero, hM43_zero, hM45_zero, hM46_zero, hM47_zero, h_is_loadX0_lhu]
    ring
  -- E92 = Main[47] * Main[40] with Main[47] = 0 — gives no info on Main[40].
  -- E95 = (Main[45] + Main[46] + Main[47]) * Main[39]: sum = 0 here since
  --   Main[44] is NOT in the sum. So E95 = 0 unconditionally; no info on Main[39].
  -- E100 = (Main[43]+Main[44]+Main[45]+Main[46]+Main[47]) * Main[38] forces Main[38] = 0
  --   (since Main[44] = 1 puts the bracket equal to 1).
  have hM38_zero : Main[38] = 0 := by
    rcases h_E100 with h | h
    · exfalso
      rw [hM43_zero, hM45_zero, hM46_zero, hM47_zero, h_is_loadX0_lhu,
        zero_add, add_zero, add_zero, add_zero] at h
      exact one_ne_zero h
    · exact h
  -- Derive Main[13] = 1 from h_E125.
  have hM13 : Main[13] = 1 := by
    rcases h_E125 with h | h
    · exfalso; rw [h_sum_eq_one] at h; exact one_ne_zero h
    · exact h
  rw [h_sum_eq_one] at h_addr
  rw [h_sum_eq_one, hM41_zero, hM42_zero, hM43_zero, hM45_zero, hM46_zero, hM47_zero,
    h_is_loadX0_lhu] at h_reader
  have h_reader' :=
    ITypeReaderImmutable.allHold_constraints_iff_is_real_poly (h := rfl) (h_trusted := rfl) |>.mp h_reader
  obtain ⟨h_trusted, h6_lt, h14_lt, h21_lt, h22_lt, h23_lt, h24_lt,
    _hM13_or, h13_iff_op_a_zero, _hPC_align, _hPC0_lt, _hPC1_lt, _hPC2_lt,
    _hM12_lt, _hM20_lt, _h_clk_a, _h_clk_b, _h_op_a_isU64, h15u64,
    _h_op_a_zero_implies⟩ := h_reader'
  have hp_lt : 131072 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    have h17 : (2 : ℕ) ^ 17 = 131072 := by decide
    omega
  have h32val : (32 : ZMod p).val = 32 := val_32_zmod_p
  have h65val : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
  have h33_lt_p : (33 : ℕ) < p := by omega
  have h33_val : (33 : ZMod p).val = 33 := ZMod.val_natCast_of_lt h33_lt_p
  -- The opcode argument simp-reduces to 33 since only Main[44] is non-zero.
  simp [Opcode.trusted_instr_poly, Opcode.ofNat, Nat.ble,
    h33_val, i_type_constraints_poly] at h_trusted
  have h14_lt_zmod : Main[14] < (32 : ZMod p) := by clear *- h_trusted; simp_all only
  have h_imm_se : Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] =
      BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) := by
    clear *- h_trusted; simp_all only
  have h6 : Main[6].val < 32 := by
    have : Main[6].val < (32 : ZMod p).val := h6_lt; rwa [h32val] at this
  have h14 : Main[14].val < 32 := by
    have : Main[14].val < (32 : ZMod p).val := h14_lt_zmod; rwa [h32val] at this
  have h6_eq_zero : Main[6] = 0 := h13_iff_op_a_zero.mp hM13
  have h6_val_eq_zero : Main[6].val = 0 := by rw [h6_eq_zero, ZMod.val_zero]
  have h_op_a_zero : (BitVec.ofNat 5 Main[6].val : BitVec 5) = 0#5 := by
    rw [h6_val_eq_zero]
  have h21u64 : Word.isU64_poly #v[Main[21], Main[22], Main[23], Main[24]] := by
    apply Word.isU64_of_cases_poly <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · have : Main[21].val < (65536 : ZMod p).val := h21_lt; rwa [h65val] at this
    · have : Main[22].val < (65536 : ZMod p).val := h22_lt; rwa [h65val] at this
    · have : Main[23].val < (65536 : ZMod p).val := h23_lt; rwa [h65val] at this
    · have : Main[24].val < (65536 : ZMod p).val := h24_lt; rwa [h65val] at this
  have h_mem_isU64' : Word.isU64_poly #v[Main[29], Main[30], Main[31], Main[32]] := by
    apply h_mem_isU64
    rw [h_sum_eq_one]; exact one_ne_zero
  have haddr_spec := AddrAddOperation.spec_of_constraints_poly _ _ h15u64 h21u64 _ h_addr
  obtain ⟨haddr_isU64, haddr_eq⟩ := haddr_spec
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ] at haddr_isU64 haddr_eq
  have h25_lt : Main[25].val < 65536 := haddr_isU64 0
  have h26_lt : Main[26].val < 65536 := haddr_isU64 1
  have h27_lt : Main[27].val < 65536 := haddr_isU64 2
  have h28_inv' : Main[28] * (Main[26] + Main[27]) = 1 := by
    rw [h28_inv, h_sum_eq_one]
  obtain ⟨h_addr_lo, h_addr_hi⟩ :=
    AddressOperation.addr_limbs_bounds Main[25] Main[26] Main[27] Main[28]
      h25_lt h26_lt h27_lt h28_inv'
  have h_addr_eq :
      (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] +
        Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]]).toNat =
        Main[25].val + Main[26].val * 2 ^ 16 + Main[27].val * 2 ^ 32 := by
    rw [← haddr_eq, Word.toBitVec64_poly_toNat_poly haddr_isU64,
      Word.toNat_poly_def]; simp
  have h_offset_eq :
      Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] =
        BitVec.signExtend 64 (sp1_imm_c Main) := by
    rw [h_imm_se]; rfl
  have h_align : (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] +
        Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]]).toNat % 2 = 0 := by
    have h := h_is_aligned
    rw [← h_imm_se, is_aligned_vaddr_iff_mod] at h
    exact h
  have h_in_range :
      range_subset (zero_extend (BitVec.addInt
          (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] +
            BitVec.signExtend 64 (sp1_imm_c Main)) 0))
        (to_bits 2) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true := by
    rw [← h_offset_eq]
    refine range_subset_sp1_pma _ 2 (by omega) ?_ ?_
    · rw [h_addr_eq]; exact h_addr_lo
    · omega
  have h_mem0_lt : Main[29].val < 65536 := h_mem_isU64' 0
  have h_mem1_lt : Main[30].val < 65536 := h_mem_isU64' 1
  have h_mem2_lt : Main[31].val < 65536 := h_mem_isU64' 2
  have h_mem3_lt : Main[32].val < 65536 := h_mem_isU64' 3
  have h2728 : ¬ (Main[26] = 0 ∧ Main[27] = 0) := by
    intro ⟨hm26, hm27⟩
    rw [hm26, hm27, add_zero, mul_zero] at h28_inv
    rw [h_sum_eq_one] at h28_inv
    exact zero_ne_one h28_inv
  -- For LHU we don't pre-fold Main[39] or Main[40] (both free in {0,1}).
  -- Pre-fold Main[38] = 0 only.
  simp [SP1ConstraintList.initialState_poly, LoadX0.constraints,
    AddressOperation.constraints, SP1Constraint.toStateProp_poly,
    AddrAddOperation.constraints, ITypeReaderImmutable.constraints,
    CPUState.constraints, BitVec.ofNatLT_eq_ofNat,
    Opcode.ofNat, Nat.ble, h6, h14, h33_val, h_is_loadX0_lhu,
    hM38_zero, hM41_zero, hM42_zero, hM43_zero,
    hM45_zero, hM46_zero, hM47_zero, h2728] at state_cstrs
  obtain ⟨h_read_pc, _h6_op_a, h14_op_a, hload⟩ := state_cstrs
  rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_read_pc
  have h_fits_real : (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat +
      (Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]]).toNat < 2 ^ 64 := by
    have := h_fits_in_mem
    simp only [sp1_imm_c] at this
    rw [← h_imm_se] at this
    omega
  have haddr_nat : (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat +
          (Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]]).toNat =
        Word.toNat_poly #v[Main[25], Main[26], Main[27], (0 : ZMod p)] := by
    have heq := congr_arg BitVec.toNat haddr_eq
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt h_fits_real] at heq
    rw [← heq, Word.toBitVec64_poly, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by
        rw [Word.toNat_poly_def]
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ, ZMod.val_zero, Nat.zero_mul, Nat.add_zero]
        have hpow : (2 ^ 64 : ℕ) = 18446744073709551616 := by decide
        rw [hpow]
        have h26m : Main[26].val * 65536 ≤ 65535 * 65536 := by
          have : Main[26].val ≤ 65535 := by omega
          exact Nat.mul_le_mul_right _ this
        have h27m : Main[27].val * 4294967296 ≤ 65535 * 4294967296 := by
          have : Main[27].val ≤ 65535 := by omega
          exact Nat.mul_le_mul_right _ this
        omega)]
  have haddr_plus : ∀ (k : ℕ), k < 8 →
      Word.toNat_poly #v[Main[25], Main[26], Main[27], (0 : ZMod p)] + k =
      Word.toNat_poly #v[Main[25] + (k : ZMod p), Main[26], Main[27], (0 : ZMod p)] := by
    intro k hk
    have hk_val : ((k : ℕ) : ZMod p).val = k := ZMod.val_natCast_of_lt (by omega)
    have h25k_lt : Main[25].val + (k : ZMod p).val < p := by rw [hk_val]; omega
    have h25k_val : (Main[25] + (k : ZMod p)).val = Main[25].val + k := by
      rw [ZMod.val_add_of_lt h25k_lt, hk_val]
    simp only [Word.toNat_poly_def, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, ZMod.val_zero, Nat.zero_mul,
      Nat.add_zero, h25k_val]
    omega
  -- 4-way nested case-split on (Main[40], Main[39]).
  rcases h_M40_or with hM40_zero | hM40_one
  · rcases h_M39_or with hM39_zero | hM39_one
    · -- bit2 = 0, bit1 = 0: aligned = unaligned. Bytes from Main[29].
      simp [spec_loadX0_lhu, sp1_loadX0,
        sp1_op_a, sp1_ob_b, sp1_imm_c,
        op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
        EStateM.Result.map, execute_LOAD, h_read_pc, h_op_a_zero]
      rw [run_vmem_read_of_width_2' (BitVec.ofNat 5 Main[14].val)
        (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]])
        (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
        (BitVec.ofNat 8 Main[29].val)
        (BitVec.ofNat 8 (Main[29].val >>> 8))]
      · simp
      · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true,
          implies_true]
      · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
      · exact h_is_aligned
      · constructor <;> simpa [Std.ExtDHashMap.get_insert]
      · exact h_fits_in_mem
      · exact h_in_range
      · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
                Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
            haddr_nat,
            show (Main[25] : ZMod p) =
              Main[25] - 4 * Main[40] - 2 * Main[39] from by
                rw [hM40_zero, hM39_zero]; ring]
        simpa using hload.1
      · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
                Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
            haddr_nat, haddr_plus 1 (by omega),
            show (Main[25] + ((1 : ℕ) : ZMod p) : ZMod p) =
              Main[25] - 4 * Main[40] - 2 * Main[39] + 1 from by
                rw [hM40_zero, hM39_zero]; push_cast; ring]
        simpa using hload.2.1
    · -- bit2 = 0, bit1 = 1: aligned = unaligned - 2. Bytes from Main[30].
      simp [spec_loadX0_lhu, sp1_loadX0,
        sp1_op_a, sp1_ob_b, sp1_imm_c,
        op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
        EStateM.Result.map, execute_LOAD, h_read_pc, h_op_a_zero]
      rw [run_vmem_read_of_width_2' (BitVec.ofNat 5 Main[14].val)
        (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]])
        (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
        (BitVec.ofNat 8 Main[30].val)
        (BitVec.ofNat 8 (Main[30].val >>> 8))]
      · simp
      · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true,
          implies_true]
      · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
      · exact h_is_aligned
      · constructor <;> simpa [Std.ExtDHashMap.get_insert]
      · exact h_fits_in_mem
      · exact h_in_range
      · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
                Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
            haddr_nat,
            show (Main[25] : ZMod p) =
              Main[25] - 4 * Main[40] - 2 * Main[39] + 2 from by
                rw [hM40_zero, hM39_one]; ring]
        simpa using hload.2.2.1
      · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
                Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
            haddr_nat, haddr_plus 1 (by omega),
            show (Main[25] + ((1 : ℕ) : ZMod p) : ZMod p) =
              Main[25] - 4 * Main[40] - 2 * Main[39] + 3 from by
                rw [hM40_zero, hM39_one]; push_cast; ring]
        simpa using hload.2.2.2.1
  · rcases h_M39_or with hM39_zero | hM39_one
    · -- bit2 = 1, bit1 = 0: aligned = unaligned - 4. Bytes from Main[31].
      simp [spec_loadX0_lhu, sp1_loadX0,
        sp1_op_a, sp1_ob_b, sp1_imm_c,
        op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
        EStateM.Result.map, execute_LOAD, h_read_pc, h_op_a_zero]
      rw [run_vmem_read_of_width_2' (BitVec.ofNat 5 Main[14].val)
        (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]])
        (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
        (BitVec.ofNat 8 Main[31].val)
        (BitVec.ofNat 8 (Main[31].val >>> 8))]
      · simp
      · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true,
          implies_true]
      · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
      · exact h_is_aligned
      · constructor <;> simpa [Std.ExtDHashMap.get_insert]
      · exact h_fits_in_mem
      · exact h_in_range
      · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
                Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
            haddr_nat,
            show (Main[25] : ZMod p) =
              Main[25] - 4 * Main[40] - 2 * Main[39] + 4 from by
                rw [hM40_one, hM39_zero]; ring]
        simpa using hload.2.2.2.2.1
      · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
                Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
            haddr_nat, haddr_plus 1 (by omega),
            show (Main[25] + ((1 : ℕ) : ZMod p) : ZMod p) =
              Main[25] - 4 * Main[40] - 2 * Main[39] + 5 from by
                rw [hM40_one, hM39_zero]; push_cast; ring]
        simpa using hload.2.2.2.2.2.1
    · -- bit2 = 1, bit1 = 1: aligned = unaligned - 6. Bytes from Main[32].
      simp [spec_loadX0_lhu, sp1_loadX0,
        sp1_op_a, sp1_ob_b, sp1_imm_c,
        op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
        EStateM.Result.map, execute_LOAD, h_read_pc, h_op_a_zero]
      rw [run_vmem_read_of_width_2' (BitVec.ofNat 5 Main[14].val)
        (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]])
        (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
        (BitVec.ofNat 8 Main[32].val)
        (BitVec.ofNat 8 (Main[32].val >>> 8))]
      · simp
      · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true,
          implies_true]
      · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
      · exact h_is_aligned
      · constructor <;> simpa [Std.ExtDHashMap.get_insert]
      · exact h_fits_in_mem
      · exact h_in_range
      · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
                Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
            haddr_nat,
            show (Main[25] : ZMod p) =
              Main[25] - 4 * Main[40] - 2 * Main[39] + 6 from by
                rw [hM40_one, hM39_one]; ring]
        simpa using hload.2.2.2.2.2.2.1
      · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
                Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
            haddr_nat, haddr_plus 1 (by omega),
            show (Main[25] + ((1 : ℕ) : ZMod p) : ZMod p) =
              Main[25] - 4 * Main[40] - 2 * Main[39] + 7 from by
                rw [hM40_one, hM39_one]; push_cast; ring]
        simpa using hload.2.2.2.2.2.2.2

set_option maxHeartbeats 1600000 in
-- LoadX0 LH sub-opcode correct proof. Mirrors `correct_loadX0_lhu`
-- but for the signed 2-byte load. Key differences:
-- - Selected flag: `Main[43] = 1` (instead of `Main[44] = 1`).
-- - Width 2; same byte-routing (Main[39], Main[40] both free; Main[38] = 0).
-- - The opcode encoding `E14` collapses to `30` (LH) since only
--   `Main[43] = 1`.
-- - Sign-extension does not matter because `rd = x0` makes `wX_bits 0`
--   a no-op.
set_option debug.skipKernelTC true in
theorem correct_loadX0_lh (Main : Vector (ZMod p) 48)
    (s : SailState) (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (LoadX0.constraints Main).allHold_poly)
    (state_cstrs : (LoadX0.constraints Main).initialState_poly s)
    (h_is_loadX0_lh : Main[43] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (sp1_imm_c Main)).toNat
      reg_val + offset + 2 < 2 ^ 64)
    (h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 Main[21].val))) 2 = true)
    :
    let op_a := sp1_op_a Main
    let op_b := sp1_ob_b Main
    let imm_c := sp1_imm_c Main
    (spec_loadX0_lh imm_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_loadX0 Main).run s := by
  extract_lets op_a op_b imm_c
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  obtain ⟨_, _, _, _, _⟩ := hs_config
  simp [SP1ConstraintList.allHold_poly, LoadX0.constraints,
    AddressOperation.constraints, sub_eq_zero,
    SP1Constraint.toProp_poly] at h_cstrs
  obtain ⟨h_addr, _h_sum_or1, h_M38_or, h_M39_or, h_M40_or, h28_inv, _h_low_align,
    h_cpu, h_reader,
    h_M41_or, h_M42_or, _h_M43_or, h_M44_or, h_M45_or, h_M46_or, h_M47_or,
    h_sum_or, h_E92, h_E95, h_E100, _h_sum_or3,
    _h_E106, _h_E109, _h_E123, _h_M36_lt, _h_byte3, h_mem_isU64,
    h_E125, _h_E127⟩ := h_cstrs
  -- seven_collapse: select Main[43] as a₇; permute the rest as a₁..a₆.
  have ⟨hM41_zero, hM42_zero, hM44_zero, hM45_zero, hM46_zero, hM47_zero⟩ :=
    seven_collapse h_M41_or h_M42_or h_M44_or h_M45_or h_M46_or h_M47_or
      h_is_loadX0_lh (by
        rcases h_sum_or with h | h
        · rw [show (Main[41] + Main[42] + Main[44] + Main[45] + Main[46] + Main[47] +
            Main[43]) = 0 from by linear_combination h]; ring
        · rw [show (Main[41] + Main[42] + Main[44] + Main[45] + Main[46] + Main[47] +
            Main[43]) - 1 = 0 from by linear_combination h, zero_mul])
  -- Sum-equals-one is now derivable.
  have h_sum_eq_one : Main[41] + Main[42] + Main[43] + Main[44] + Main[45] + Main[46] +
      Main[47] = 1 := by
    rw [hM41_zero, hM42_zero, hM44_zero, hM45_zero, hM46_zero, hM47_zero, h_is_loadX0_lh]
    ring
  -- E92, E95: same as LHU — no info on Main[39] or Main[40].
  -- E100 = (Main[43]+Main[44]+Main[45]+Main[46]+Main[47]) * Main[38] forces Main[38] = 0
  --   (since Main[43] = 1 puts the bracket equal to 1).
  have hM38_zero : Main[38] = 0 := by
    rcases h_E100 with h | h
    · exfalso
      rw [hM44_zero, hM45_zero, hM46_zero, hM47_zero, h_is_loadX0_lh,
        add_zero, add_zero, add_zero, add_zero] at h
      exact one_ne_zero h
    · exact h
  -- Derive Main[13] = 1 from h_E125.
  have hM13 : Main[13] = 1 := by
    rcases h_E125 with h | h
    · exfalso; rw [h_sum_eq_one] at h; exact one_ne_zero h
    · exact h
  rw [h_sum_eq_one] at h_addr
  rw [h_sum_eq_one, hM41_zero, hM42_zero, hM44_zero, hM45_zero, hM46_zero, hM47_zero,
    h_is_loadX0_lh] at h_reader
  have h_reader' :=
    ITypeReaderImmutable.allHold_constraints_iff_is_real_poly (h := rfl) (h_trusted := rfl) |>.mp h_reader
  obtain ⟨h_trusted, h6_lt, h14_lt, h21_lt, h22_lt, h23_lt, h24_lt,
    _hM13_or, h13_iff_op_a_zero, _hPC_align, _hPC0_lt, _hPC1_lt, _hPC2_lt,
    _hM12_lt, _hM20_lt, _h_clk_a, _h_clk_b, _h_op_a_isU64, h15u64,
    _h_op_a_zero_implies⟩ := h_reader'
  have hp_lt : 131072 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    have h17 : (2 : ℕ) ^ 17 = 131072 := by decide
    omega
  have h32val : (32 : ZMod p).val = 32 := val_32_zmod_p
  have h65val : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
  have h30_lt_p : (30 : ℕ) < p := by omega
  have h30_val : (30 : ZMod p).val = 30 := ZMod.val_natCast_of_lt h30_lt_p
  -- The opcode argument simp-reduces to 30 since only Main[43] is non-zero.
  simp [Opcode.trusted_instr_poly, Opcode.ofNat, Nat.ble,
    h30_val, i_type_constraints_poly] at h_trusted
  have h14_lt_zmod : Main[14] < (32 : ZMod p) := by clear *- h_trusted; simp_all only
  have h_imm_se : Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] =
      BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) := by
    clear *- h_trusted; simp_all only
  have h6 : Main[6].val < 32 := by
    have : Main[6].val < (32 : ZMod p).val := h6_lt; rwa [h32val] at this
  have h14 : Main[14].val < 32 := by
    have : Main[14].val < (32 : ZMod p).val := h14_lt_zmod; rwa [h32val] at this
  have h6_eq_zero : Main[6] = 0 := h13_iff_op_a_zero.mp hM13
  have h6_val_eq_zero : Main[6].val = 0 := by rw [h6_eq_zero, ZMod.val_zero]
  have h_op_a_zero : (BitVec.ofNat 5 Main[6].val : BitVec 5) = 0#5 := by
    rw [h6_val_eq_zero]
  have h21u64 : Word.isU64_poly #v[Main[21], Main[22], Main[23], Main[24]] := by
    apply Word.isU64_of_cases_poly <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · have : Main[21].val < (65536 : ZMod p).val := h21_lt; rwa [h65val] at this
    · have : Main[22].val < (65536 : ZMod p).val := h22_lt; rwa [h65val] at this
    · have : Main[23].val < (65536 : ZMod p).val := h23_lt; rwa [h65val] at this
    · have : Main[24].val < (65536 : ZMod p).val := h24_lt; rwa [h65val] at this
  have h_mem_isU64' : Word.isU64_poly #v[Main[29], Main[30], Main[31], Main[32]] := by
    apply h_mem_isU64
    rw [h_sum_eq_one]; exact one_ne_zero
  have haddr_spec := AddrAddOperation.spec_of_constraints_poly _ _ h15u64 h21u64 _ h_addr
  obtain ⟨haddr_isU64, haddr_eq⟩ := haddr_spec
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ] at haddr_isU64 haddr_eq
  have h25_lt : Main[25].val < 65536 := haddr_isU64 0
  have h26_lt : Main[26].val < 65536 := haddr_isU64 1
  have h27_lt : Main[27].val < 65536 := haddr_isU64 2
  have h28_inv' : Main[28] * (Main[26] + Main[27]) = 1 := by
    rw [h28_inv, h_sum_eq_one]
  obtain ⟨h_addr_lo, h_addr_hi⟩ :=
    AddressOperation.addr_limbs_bounds Main[25] Main[26] Main[27] Main[28]
      h25_lt h26_lt h27_lt h28_inv'
  have h_addr_eq :
      (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] +
        Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]]).toNat =
        Main[25].val + Main[26].val * 2 ^ 16 + Main[27].val * 2 ^ 32 := by
    rw [← haddr_eq, Word.toBitVec64_poly_toNat_poly haddr_isU64,
      Word.toNat_poly_def]; simp
  have h_offset_eq :
      Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] =
        BitVec.signExtend 64 (sp1_imm_c Main) := by
    rw [h_imm_se]; rfl
  have h_align : (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] +
        Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]]).toNat % 2 = 0 := by
    have h := h_is_aligned
    rw [← h_imm_se, is_aligned_vaddr_iff_mod] at h
    exact h
  have h_in_range :
      range_subset (zero_extend (BitVec.addInt
          (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] +
            BitVec.signExtend 64 (sp1_imm_c Main)) 0))
        (to_bits 2) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true := by
    rw [← h_offset_eq]
    refine range_subset_sp1_pma _ 2 (by omega) ?_ ?_
    · rw [h_addr_eq]; exact h_addr_lo
    · omega
  have h_mem0_lt : Main[29].val < 65536 := h_mem_isU64' 0
  have h_mem1_lt : Main[30].val < 65536 := h_mem_isU64' 1
  have h_mem2_lt : Main[31].val < 65536 := h_mem_isU64' 2
  have h_mem3_lt : Main[32].val < 65536 := h_mem_isU64' 3
  have h2728 : ¬ (Main[26] = 0 ∧ Main[27] = 0) := by
    intro ⟨hm26, hm27⟩
    rw [hm26, hm27, add_zero, mul_zero] at h28_inv
    rw [h_sum_eq_one] at h28_inv
    exact zero_ne_one h28_inv
  -- Pre-fold Main[38] = 0 only.
  simp [SP1ConstraintList.initialState_poly, LoadX0.constraints,
    AddressOperation.constraints, SP1Constraint.toStateProp_poly,
    AddrAddOperation.constraints, ITypeReaderImmutable.constraints,
    CPUState.constraints, BitVec.ofNatLT_eq_ofNat,
    Opcode.ofNat, Nat.ble, h6, h14, h30_val, h_is_loadX0_lh,
    hM38_zero, hM41_zero, hM42_zero, hM44_zero,
    hM45_zero, hM46_zero, hM47_zero, h2728] at state_cstrs
  obtain ⟨h_read_pc, _h6_op_a, h14_op_a, hload⟩ := state_cstrs
  rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_read_pc
  have h_fits_real : (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat +
      (Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]]).toNat < 2 ^ 64 := by
    have := h_fits_in_mem
    simp only [sp1_imm_c] at this
    rw [← h_imm_se] at this
    omega
  have haddr_nat : (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat +
          (Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]]).toNat =
        Word.toNat_poly #v[Main[25], Main[26], Main[27], (0 : ZMod p)] := by
    have heq := congr_arg BitVec.toNat haddr_eq
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt h_fits_real] at heq
    rw [← heq, Word.toBitVec64_poly, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by
        rw [Word.toNat_poly_def]
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ, ZMod.val_zero, Nat.zero_mul, Nat.add_zero]
        have hpow : (2 ^ 64 : ℕ) = 18446744073709551616 := by decide
        rw [hpow]
        have h26m : Main[26].val * 65536 ≤ 65535 * 65536 := by
          have : Main[26].val ≤ 65535 := by omega
          exact Nat.mul_le_mul_right _ this
        have h27m : Main[27].val * 4294967296 ≤ 65535 * 4294967296 := by
          have : Main[27].val ≤ 65535 := by omega
          exact Nat.mul_le_mul_right _ this
        omega)]
  have haddr_plus : ∀ (k : ℕ), k < 8 →
      Word.toNat_poly #v[Main[25], Main[26], Main[27], (0 : ZMod p)] + k =
      Word.toNat_poly #v[Main[25] + (k : ZMod p), Main[26], Main[27], (0 : ZMod p)] := by
    intro k hk
    have hk_val : ((k : ℕ) : ZMod p).val = k := ZMod.val_natCast_of_lt (by omega)
    have h25k_lt : Main[25].val + (k : ZMod p).val < p := by rw [hk_val]; omega
    have h25k_val : (Main[25] + (k : ZMod p)).val = Main[25].val + k := by
      rw [ZMod.val_add_of_lt h25k_lt, hk_val]
    simp only [Word.toNat_poly_def, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, ZMod.val_zero, Nat.zero_mul,
      Nat.add_zero, h25k_val]
    omega
  -- 4-way nested case-split on (Main[40], Main[39]).
  rcases h_M40_or with hM40_zero | hM40_one
  · rcases h_M39_or with hM39_zero | hM39_one
    · -- bit2 = 0, bit1 = 0: aligned = unaligned. Bytes from Main[29].
      simp [spec_loadX0_lh, sp1_loadX0,
        sp1_op_a, sp1_ob_b, sp1_imm_c,
        op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
        EStateM.Result.map, execute_LOAD, h_read_pc, h_op_a_zero]
      rw [run_vmem_read_of_width_2' (BitVec.ofNat 5 Main[14].val)
        (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]])
        (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
        (BitVec.ofNat 8 Main[29].val)
        (BitVec.ofNat 8 (Main[29].val >>> 8))]
      · simp
      · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true,
          implies_true]
      · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
      · exact h_is_aligned
      · constructor <;> simpa [Std.ExtDHashMap.get_insert]
      · exact h_fits_in_mem
      · exact h_in_range
      · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
                Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
            haddr_nat,
            show (Main[25] : ZMod p) =
              Main[25] - 4 * Main[40] - 2 * Main[39] from by
                rw [hM40_zero, hM39_zero]; ring]
        simpa using hload.1
      · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
                Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
            haddr_nat, haddr_plus 1 (by omega),
            show (Main[25] + ((1 : ℕ) : ZMod p) : ZMod p) =
              Main[25] - 4 * Main[40] - 2 * Main[39] + 1 from by
                rw [hM40_zero, hM39_zero]; push_cast; ring]
        simpa using hload.2.1
    · -- bit2 = 0, bit1 = 1: aligned = unaligned - 2. Bytes from Main[30].
      simp [spec_loadX0_lh, sp1_loadX0,
        sp1_op_a, sp1_ob_b, sp1_imm_c,
        op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
        EStateM.Result.map, execute_LOAD, h_read_pc, h_op_a_zero]
      rw [run_vmem_read_of_width_2' (BitVec.ofNat 5 Main[14].val)
        (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]])
        (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
        (BitVec.ofNat 8 Main[30].val)
        (BitVec.ofNat 8 (Main[30].val >>> 8))]
      · simp
      · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true,
          implies_true]
      · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
      · exact h_is_aligned
      · constructor <;> simpa [Std.ExtDHashMap.get_insert]
      · exact h_fits_in_mem
      · exact h_in_range
      · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
                Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
            haddr_nat,
            show (Main[25] : ZMod p) =
              Main[25] - 4 * Main[40] - 2 * Main[39] + 2 from by
                rw [hM40_zero, hM39_one]; ring]
        simpa using hload.2.2.1
      · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
                Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
            haddr_nat, haddr_plus 1 (by omega),
            show (Main[25] + ((1 : ℕ) : ZMod p) : ZMod p) =
              Main[25] - 4 * Main[40] - 2 * Main[39] + 3 from by
                rw [hM40_zero, hM39_one]; push_cast; ring]
        simpa using hload.2.2.2.1
  · rcases h_M39_or with hM39_zero | hM39_one
    · -- bit2 = 1, bit1 = 0: aligned = unaligned - 4. Bytes from Main[31].
      simp [spec_loadX0_lh, sp1_loadX0,
        sp1_op_a, sp1_ob_b, sp1_imm_c,
        op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
        EStateM.Result.map, execute_LOAD, h_read_pc, h_op_a_zero]
      rw [run_vmem_read_of_width_2' (BitVec.ofNat 5 Main[14].val)
        (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]])
        (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
        (BitVec.ofNat 8 Main[31].val)
        (BitVec.ofNat 8 (Main[31].val >>> 8))]
      · simp
      · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true,
          implies_true]
      · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
      · exact h_is_aligned
      · constructor <;> simpa [Std.ExtDHashMap.get_insert]
      · exact h_fits_in_mem
      · exact h_in_range
      · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
                Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
            haddr_nat,
            show (Main[25] : ZMod p) =
              Main[25] - 4 * Main[40] - 2 * Main[39] + 4 from by
                rw [hM40_one, hM39_zero]; ring]
        simpa using hload.2.2.2.2.1
      · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
                Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
            haddr_nat, haddr_plus 1 (by omega),
            show (Main[25] + ((1 : ℕ) : ZMod p) : ZMod p) =
              Main[25] - 4 * Main[40] - 2 * Main[39] + 5 from by
                rw [hM40_one, hM39_zero]; push_cast; ring]
        simpa using hload.2.2.2.2.2.1
    · -- bit2 = 1, bit1 = 1: aligned = unaligned - 6. Bytes from Main[32].
      simp [spec_loadX0_lh, sp1_loadX0,
        sp1_op_a, sp1_ob_b, sp1_imm_c,
        op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
        EStateM.Result.map, execute_LOAD, h_read_pc, h_op_a_zero]
      rw [run_vmem_read_of_width_2' (BitVec.ofNat 5 Main[14].val)
        (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]])
        (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
        (BitVec.ofNat 8 Main[32].val)
        (BitVec.ofNat 8 (Main[32].val >>> 8))]
      · simp
      · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true,
          implies_true]
      · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
      · exact h_is_aligned
      · constructor <;> simpa [Std.ExtDHashMap.get_insert]
      · exact h_fits_in_mem
      · exact h_in_range
      · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
                Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
            haddr_nat,
            show (Main[25] : ZMod p) =
              Main[25] - 4 * Main[40] - 2 * Main[39] + 6 from by
                rw [hM40_one, hM39_one]; ring]
        simpa using hload.2.2.2.2.2.2.1
      · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
                Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
            haddr_nat, haddr_plus 1 (by omega),
            show (Main[25] + ((1 : ℕ) : ZMod p) : ZMod p) =
              Main[25] - 4 * Main[40] - 2 * Main[39] + 7 from by
                rw [hM40_one, hM39_one]; push_cast; ring]
        simpa using hload.2.2.2.2.2.2.2

set_option maxHeartbeats 1600000 in
-- LoadX0 LBU sub-opcode correct proof. Mirrors `correct_loadX0_lhu`
-- but for 1-byte unsigned load. Key differences:
-- - Selected flag: `Main[42] = 1` (instead of `Main[44] = 1`).
-- - Width 1 (uses `run_vmem_read_of_width_1'`); 1-byte alignment is
--   trivial (`% 1 = 0` always), but we keep the parameter for symmetry.
-- - Byte-routing constraints leave ALL three of `Main[38]`, `Main[39]`,
--   `Main[40]` free. We do an 8-way nested case-split on
--   (Main[40], Main[39], Main[38]) and provide one byte from
--   `Main[29..32]` per case (low byte vs high byte selected by bit0).
-- - The opcode encoding `E14` collapses to `32` (LBU) since only
--   `Main[42] = 1`.
set_option debug.skipKernelTC true in
theorem correct_loadX0_lbu (Main : Vector (ZMod p) 48)
    (s : SailState) (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (LoadX0.constraints Main).allHold_poly)
    (state_cstrs : (LoadX0.constraints Main).initialState_poly s)
    (h_is_loadX0_lbu : Main[42] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (sp1_imm_c Main)).toNat
      reg_val + offset + 1 < 2 ^ 64)
    (h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 Main[21].val))) 1 = true)
    :
    let op_a := sp1_op_a Main
    let op_b := sp1_ob_b Main
    let imm_c := sp1_imm_c Main
    (spec_loadX0_lbu imm_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_loadX0 Main).run s := by
  extract_lets op_a op_b imm_c
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  obtain ⟨_, _, _, _, _⟩ := hs_config
  simp [SP1ConstraintList.allHold_poly, LoadX0.constraints,
    AddressOperation.constraints, sub_eq_zero,
    SP1Constraint.toProp_poly] at h_cstrs
  obtain ⟨h_addr, _h_sum_or1, h_M38_or, h_M39_or, h_M40_or, h28_inv, _h_low_align,
    h_cpu, h_reader,
    h_M41_or, _h_M42_or, h_M43_or, h_M44_or, h_M45_or, h_M46_or, h_M47_or,
    h_sum_or, _h_E92, _h_E95, _h_E100, _h_sum_or3,
    _h_E106, _h_E109, _h_E123, _h_M36_lt, _h_byte3, h_mem_isU64,
    h_E125, _h_E127⟩ := h_cstrs
  -- seven_collapse: select Main[42] as a₇; permute the rest as a₁..a₆.
  have ⟨hM41_zero, hM43_zero, hM44_zero, hM45_zero, hM46_zero, hM47_zero⟩ :=
    seven_collapse h_M41_or h_M43_or h_M44_or h_M45_or h_M46_or h_M47_or
      h_is_loadX0_lbu (by
        rcases h_sum_or with h | h
        · rw [show (Main[41] + Main[43] + Main[44] + Main[45] + Main[46] + Main[47] +
            Main[42]) = 0 from by linear_combination h]; ring
        · rw [show (Main[41] + Main[43] + Main[44] + Main[45] + Main[46] + Main[47] +
            Main[42]) - 1 = 0 from by linear_combination h, zero_mul])
  -- Sum-equals-one is now derivable.
  have h_sum_eq_one : Main[41] + Main[42] + Main[43] + Main[44] + Main[45] + Main[46] +
      Main[47] = 1 := by
    rw [hM41_zero, hM43_zero, hM44_zero, hM45_zero, hM46_zero, hM47_zero, h_is_loadX0_lbu]
    ring
  -- For LBU, NONE of E92/E95/E100 force any of Main[38], Main[39], Main[40]:
  -- E92 = Main[47] * Main[40] = 0 (Main[47] = 0); no info on Main[40].
  -- E95 = (Main[45]+Main[46]+Main[47]) * Main[39] = 0; no info on Main[39].
  -- E100 = (Main[43]+Main[44]+Main[45]+Main[46]+Main[47]) * Main[38] = 0; no info on Main[38].
  -- All three offset bits are free.
  -- Derive Main[13] = 1 from h_E125.
  have hM13 : Main[13] = 1 := by
    rcases h_E125 with h | h
    · exfalso; rw [h_sum_eq_one] at h; exact one_ne_zero h
    · exact h
  rw [h_sum_eq_one] at h_addr
  rw [h_sum_eq_one, hM41_zero, hM43_zero, hM44_zero, hM45_zero, hM46_zero, hM47_zero,
    h_is_loadX0_lbu] at h_reader
  have h_reader' :=
    ITypeReaderImmutable.allHold_constraints_iff_is_real_poly (h := rfl) (h_trusted := rfl) |>.mp h_reader
  obtain ⟨h_trusted, h6_lt, h14_lt, h21_lt, h22_lt, h23_lt, h24_lt,
    _hM13_or, h13_iff_op_a_zero, _hPC_align, _hPC0_lt, _hPC1_lt, _hPC2_lt,
    _hM12_lt, _hM20_lt, _h_clk_a, _h_clk_b, _h_op_a_isU64, h15u64,
    _h_op_a_zero_implies⟩ := h_reader'
  have hp_lt : 131072 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    have h17 : (2 : ℕ) ^ 17 = 131072 := by decide
    omega
  have h32val : (32 : ZMod p).val = 32 := val_32_zmod_p
  have h65val : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
  -- The opcode argument simp-reduces to 32 since only Main[42] is non-zero.
  simp [Opcode.trusted_instr_poly, Opcode.ofNat, Nat.ble,
    h32val, i_type_constraints_poly] at h_trusted
  have h14_lt_zmod : Main[14] < (32 : ZMod p) := by clear *- h_trusted; simp_all only
  have h_imm_se : Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] =
      BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) := by
    clear *- h_trusted; simp_all only
  have h6 : Main[6].val < 32 := by
    have : Main[6].val < (32 : ZMod p).val := h6_lt; rwa [h32val] at this
  have h14 : Main[14].val < 32 := by
    have : Main[14].val < (32 : ZMod p).val := h14_lt_zmod; rwa [h32val] at this
  have h6_eq_zero : Main[6] = 0 := h13_iff_op_a_zero.mp hM13
  have h6_val_eq_zero : Main[6].val = 0 := by rw [h6_eq_zero, ZMod.val_zero]
  have h_op_a_zero : (BitVec.ofNat 5 Main[6].val : BitVec 5) = 0#5 := by
    rw [h6_val_eq_zero]
  have h21u64 : Word.isU64_poly #v[Main[21], Main[22], Main[23], Main[24]] := by
    apply Word.isU64_of_cases_poly <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · have : Main[21].val < (65536 : ZMod p).val := h21_lt; rwa [h65val] at this
    · have : Main[22].val < (65536 : ZMod p).val := h22_lt; rwa [h65val] at this
    · have : Main[23].val < (65536 : ZMod p).val := h23_lt; rwa [h65val] at this
    · have : Main[24].val < (65536 : ZMod p).val := h24_lt; rwa [h65val] at this
  have h_mem_isU64' : Word.isU64_poly #v[Main[29], Main[30], Main[31], Main[32]] := by
    apply h_mem_isU64
    rw [h_sum_eq_one]; exact one_ne_zero
  have haddr_spec := AddrAddOperation.spec_of_constraints_poly _ _ h15u64 h21u64 _ h_addr
  obtain ⟨haddr_isU64, haddr_eq⟩ := haddr_spec
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ] at haddr_isU64 haddr_eq
  have h25_lt : Main[25].val < 65536 := haddr_isU64 0
  have h26_lt : Main[26].val < 65536 := haddr_isU64 1
  have h27_lt : Main[27].val < 65536 := haddr_isU64 2
  have h28_inv' : Main[28] * (Main[26] + Main[27]) = 1 := by
    rw [h28_inv, h_sum_eq_one]
  obtain ⟨h_addr_lo, h_addr_hi⟩ :=
    AddressOperation.addr_limbs_bounds Main[25] Main[26] Main[27] Main[28]
      h25_lt h26_lt h27_lt h28_inv'
  have h_addr_eq :
      (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] +
        Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]]).toNat =
        Main[25].val + Main[26].val * 2 ^ 16 + Main[27].val * 2 ^ 32 := by
    rw [← haddr_eq, Word.toBitVec64_poly_toNat_poly haddr_isU64,
      Word.toNat_poly_def]; simp
  have h_offset_eq :
      Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] =
        BitVec.signExtend 64 (sp1_imm_c Main) := by
    rw [h_imm_se]; rfl
  have h_align : (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] +
        Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]]).toNat % 1 = 0 := by
    have h := h_is_aligned
    rw [← h_imm_se, is_aligned_vaddr_iff_mod] at h
    exact h
  have h_in_range :
      range_subset (zero_extend (BitVec.addInt
          (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] +
            BitVec.signExtend 64 (sp1_imm_c Main)) 0))
        (to_bits 1) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true := by
    rw [← h_offset_eq]
    refine range_subset_sp1_pma _ 1 (by omega) ?_ ?_
    · rw [h_addr_eq]; exact h_addr_lo
    · omega
  have h_mem0_lt : Main[29].val < 65536 := h_mem_isU64' 0
  have h_mem1_lt : Main[30].val < 65536 := h_mem_isU64' 1
  have h_mem2_lt : Main[31].val < 65536 := h_mem_isU64' 2
  have h_mem3_lt : Main[32].val < 65536 := h_mem_isU64' 3
  have h2728 : ¬ (Main[26] = 0 ∧ Main[27] = 0) := by
    intro ⟨hm26, hm27⟩
    rw [hm26, hm27, add_zero, mul_zero] at h28_inv
    rw [h_sum_eq_one] at h28_inv
    exact zero_ne_one h28_inv
  -- For LBU we don't pre-fold any of Main[38], Main[39], Main[40] (all free in {0,1}).
  simp [SP1ConstraintList.initialState_poly, LoadX0.constraints,
    AddressOperation.constraints, SP1Constraint.toStateProp_poly,
    AddrAddOperation.constraints, ITypeReaderImmutable.constraints,
    CPUState.constraints, BitVec.ofNatLT_eq_ofNat,
    Opcode.ofNat, Nat.ble, h6, h14, h32val, h_is_loadX0_lbu,
    hM41_zero, hM43_zero, hM44_zero,
    hM45_zero, hM46_zero, hM47_zero, h2728] at state_cstrs
  obtain ⟨h_read_pc, _h6_op_a, h14_op_a, hload⟩ := state_cstrs
  rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_read_pc
  have h_fits_real : (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat +
      (Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]]).toNat < 2 ^ 64 := by
    have := h_fits_in_mem
    simp only [sp1_imm_c] at this
    rw [← h_imm_se] at this
    omega
  have haddr_nat : (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat +
          (Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]]).toNat =
        Word.toNat_poly #v[Main[25], Main[26], Main[27], (0 : ZMod p)] := by
    have heq := congr_arg BitVec.toNat haddr_eq
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt h_fits_real] at heq
    rw [← heq, Word.toBitVec64_poly, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by
        rw [Word.toNat_poly_def]
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ, ZMod.val_zero, Nat.zero_mul, Nat.add_zero]
        have hpow : (2 ^ 64 : ℕ) = 18446744073709551616 := by decide
        rw [hpow]
        have h26m : Main[26].val * 65536 ≤ 65535 * 65536 := by
          have : Main[26].val ≤ 65535 := by omega
          exact Nat.mul_le_mul_right _ this
        have h27m : Main[27].val * 4294967296 ≤ 65535 * 4294967296 := by
          have : Main[27].val ≤ 65535 := by omega
          exact Nat.mul_le_mul_right _ this
        omega)]
  have haddr_plus : ∀ (k : ℕ), k < 8 →
      Word.toNat_poly #v[Main[25], Main[26], Main[27], (0 : ZMod p)] + k =
      Word.toNat_poly #v[Main[25] + (k : ZMod p), Main[26], Main[27], (0 : ZMod p)] := by
    intro k hk
    have hk_val : ((k : ℕ) : ZMod p).val = k := ZMod.val_natCast_of_lt (by omega)
    have h25k_lt : Main[25].val + (k : ZMod p).val < p := by rw [hk_val]; omega
    have h25k_val : (Main[25] + (k : ZMod p)).val = Main[25].val + k := by
      rw [ZMod.val_add_of_lt h25k_lt, hk_val]
    simp only [Word.toNat_poly_def, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, ZMod.val_zero, Nat.zero_mul,
      Nat.add_zero, h25k_val]
    omega
  -- 8-way nested case-split on (Main[40], Main[39], Main[38]).
  rcases h_M40_or with hM40_zero | hM40_one
  · rcases h_M39_or with hM39_zero | hM39_one
    · rcases h_M38_or with hM38_zero | hM38_one
      · -- 000: offset 0. Byte = Main[29] low.
        simp [spec_loadX0_lbu, sp1_loadX0,
          sp1_op_a, sp1_ob_b, sp1_imm_c,
          op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
          EStateM.Result.map, execute_LOAD, h_read_pc, h_op_a_zero]
        rw [run_vmem_read_of_width_1' (BitVec.ofNat 5 Main[14].val)
          (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]])
          (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
          (BitVec.ofNat 8 Main[29].val)]
        · simp
        · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true,
            implies_true]
        · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
        · exact h_is_aligned
        · constructor <;> simpa [Std.ExtDHashMap.get_insert]
        · exact h_fits_in_mem
        · exact h_in_range
        · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
                  Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
              haddr_nat,
              show (Main[25] : ZMod p) =
                Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38] from by
                  rw [hM40_zero, hM39_zero, hM38_zero]; ring]
          simpa using hload.1
      · -- 001: offset 1. Byte = Main[29] high.
        simp [spec_loadX0_lbu, sp1_loadX0,
          sp1_op_a, sp1_ob_b, sp1_imm_c,
          op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
          EStateM.Result.map, execute_LOAD, h_read_pc, h_op_a_zero]
        rw [run_vmem_read_of_width_1' (BitVec.ofNat 5 Main[14].val)
          (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]])
          (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
          (BitVec.ofNat 8 (Main[29].val >>> 8))]
        · simp
        · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true,
            implies_true]
        · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
        · exact h_is_aligned
        · constructor <;> simpa [Std.ExtDHashMap.get_insert]
        · exact h_fits_in_mem
        · exact h_in_range
        · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
                  Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
              haddr_nat,
              show (Main[25] : ZMod p) =
                Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38] + 1 from by
                  rw [hM40_zero, hM39_zero, hM38_one]; ring]
          simpa using hload.2.1
    · rcases h_M38_or with hM38_zero | hM38_one
      · -- 010: offset 2. Byte = Main[30] low.
        simp [spec_loadX0_lbu, sp1_loadX0,
          sp1_op_a, sp1_ob_b, sp1_imm_c,
          op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
          EStateM.Result.map, execute_LOAD, h_read_pc, h_op_a_zero]
        rw [run_vmem_read_of_width_1' (BitVec.ofNat 5 Main[14].val)
          (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]])
          (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
          (BitVec.ofNat 8 Main[30].val)]
        · simp
        · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true,
            implies_true]
        · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
        · exact h_is_aligned
        · constructor <;> simpa [Std.ExtDHashMap.get_insert]
        · exact h_fits_in_mem
        · exact h_in_range
        · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
                  Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
              haddr_nat,
              show (Main[25] : ZMod p) =
                Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38] + 2 from by
                  rw [hM40_zero, hM39_one, hM38_zero]; ring]
          simpa using hload.2.2.1
      · -- 011: offset 3. Byte = Main[30] high.
        simp [spec_loadX0_lbu, sp1_loadX0,
          sp1_op_a, sp1_ob_b, sp1_imm_c,
          op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
          EStateM.Result.map, execute_LOAD, h_read_pc, h_op_a_zero]
        rw [run_vmem_read_of_width_1' (BitVec.ofNat 5 Main[14].val)
          (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]])
          (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
          (BitVec.ofNat 8 (Main[30].val >>> 8))]
        · simp
        · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true,
            implies_true]
        · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
        · exact h_is_aligned
        · constructor <;> simpa [Std.ExtDHashMap.get_insert]
        · exact h_fits_in_mem
        · exact h_in_range
        · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
                  Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
              haddr_nat,
              show (Main[25] : ZMod p) =
                Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38] + 3 from by
                  rw [hM40_zero, hM39_one, hM38_one]; ring]
          simpa using hload.2.2.2.1
  · rcases h_M39_or with hM39_zero | hM39_one
    · rcases h_M38_or with hM38_zero | hM38_one
      · -- 100: offset 4. Byte = Main[31] low.
        simp [spec_loadX0_lbu, sp1_loadX0,
          sp1_op_a, sp1_ob_b, sp1_imm_c,
          op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
          EStateM.Result.map, execute_LOAD, h_read_pc, h_op_a_zero]
        rw [run_vmem_read_of_width_1' (BitVec.ofNat 5 Main[14].val)
          (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]])
          (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
          (BitVec.ofNat 8 Main[31].val)]
        · simp
        · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true,
            implies_true]
        · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
        · exact h_is_aligned
        · constructor <;> simpa [Std.ExtDHashMap.get_insert]
        · exact h_fits_in_mem
        · exact h_in_range
        · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
                  Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
              haddr_nat,
              show (Main[25] : ZMod p) =
                Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38] + 4 from by
                  rw [hM40_one, hM39_zero, hM38_zero]; ring]
          simpa using hload.2.2.2.2.1
      · -- 101: offset 5. Byte = Main[31] high.
        simp [spec_loadX0_lbu, sp1_loadX0,
          sp1_op_a, sp1_ob_b, sp1_imm_c,
          op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
          EStateM.Result.map, execute_LOAD, h_read_pc, h_op_a_zero]
        rw [run_vmem_read_of_width_1' (BitVec.ofNat 5 Main[14].val)
          (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]])
          (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
          (BitVec.ofNat 8 (Main[31].val >>> 8))]
        · simp
        · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true,
            implies_true]
        · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
        · exact h_is_aligned
        · constructor <;> simpa [Std.ExtDHashMap.get_insert]
        · exact h_fits_in_mem
        · exact h_in_range
        · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
                  Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
              haddr_nat,
              show (Main[25] : ZMod p) =
                Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38] + 5 from by
                  rw [hM40_one, hM39_zero, hM38_one]; ring]
          simpa using hload.2.2.2.2.2.1
    · rcases h_M38_or with hM38_zero | hM38_one
      · -- 110: offset 6. Byte = Main[32] low.
        simp [spec_loadX0_lbu, sp1_loadX0,
          sp1_op_a, sp1_ob_b, sp1_imm_c,
          op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
          EStateM.Result.map, execute_LOAD, h_read_pc, h_op_a_zero]
        rw [run_vmem_read_of_width_1' (BitVec.ofNat 5 Main[14].val)
          (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]])
          (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
          (BitVec.ofNat 8 Main[32].val)]
        · simp
        · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true,
            implies_true]
        · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
        · exact h_is_aligned
        · constructor <;> simpa [Std.ExtDHashMap.get_insert]
        · exact h_fits_in_mem
        · exact h_in_range
        · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
                  Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
              haddr_nat,
              show (Main[25] : ZMod p) =
                Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38] + 6 from by
                  rw [hM40_one, hM39_one, hM38_zero]; ring]
          simpa using hload.2.2.2.2.2.2.1
      · -- 111: offset 7. Byte = Main[32] high.
        simp [spec_loadX0_lbu, sp1_loadX0,
          sp1_op_a, sp1_ob_b, sp1_imm_c,
          op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
          EStateM.Result.map, execute_LOAD, h_read_pc, h_op_a_zero]
        rw [run_vmem_read_of_width_1' (BitVec.ofNat 5 Main[14].val)
          (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]])
          (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
          (BitVec.ofNat 8 (Main[32].val >>> 8))]
        · simp
        · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true,
            implies_true]
        · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
        · exact h_is_aligned
        · constructor <;> simpa [Std.ExtDHashMap.get_insert]
        · exact h_fits_in_mem
        · exact h_in_range
        · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
                  Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
              haddr_nat,
              show (Main[25] : ZMod p) =
                Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38] + 7 from by
                  rw [hM40_one, hM39_one, hM38_one]; ring]
          simpa using hload.2.2.2.2.2.2.2

set_option maxHeartbeats 1600000 in
-- LoadX0 LB sub-opcode correct proof. Mirrors `correct_loadX0_lbu`
-- but for the signed 1-byte load. Key differences:
-- - Selected flag: `Main[41] = 1` (instead of `Main[42] = 1`).
-- - Width 1; same 8-way byte-routing on (Main[40], Main[39], Main[38]).
-- - The opcode encoding `E14` collapses to `29` (LB) since only
--   `Main[41] = 1`.
-- - Sign-extension does not matter because `rd = x0` makes `wX_bits 0`
--   a no-op.
set_option debug.skipKernelTC true in
theorem correct_loadX0_lb (Main : Vector (ZMod p) 48)
    (s : SailState) (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (LoadX0.constraints Main).allHold_poly)
    (state_cstrs : (LoadX0.constraints Main).initialState_poly s)
    (h_is_loadX0_lb : Main[41] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (sp1_imm_c Main)).toNat
      reg_val + offset + 1 < 2 ^ 64)
    (h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 Main[21].val))) 1 = true)
    :
    let op_a := sp1_op_a Main
    let op_b := sp1_ob_b Main
    let imm_c := sp1_imm_c Main
    (spec_loadX0_lb imm_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_loadX0 Main).run s := by
  extract_lets op_a op_b imm_c
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  obtain ⟨_, _, _, _, _⟩ := hs_config
  simp [SP1ConstraintList.allHold_poly, LoadX0.constraints,
    AddressOperation.constraints, sub_eq_zero,
    SP1Constraint.toProp_poly] at h_cstrs
  obtain ⟨h_addr, _h_sum_or1, h_M38_or, h_M39_or, h_M40_or, h28_inv, _h_low_align,
    h_cpu, h_reader,
    _h_M41_or, h_M42_or, h_M43_or, h_M44_or, h_M45_or, h_M46_or, h_M47_or,
    h_sum_or, _h_E92, _h_E95, _h_E100, _h_sum_or3,
    _h_E106, _h_E109, _h_E123, _h_M36_lt, _h_byte3, h_mem_isU64,
    h_E125, _h_E127⟩ := h_cstrs
  -- seven_collapse: select Main[41] as a₇; permute the rest as a₁..a₆.
  have ⟨hM42_zero, hM43_zero, hM44_zero, hM45_zero, hM46_zero, hM47_zero⟩ :=
    seven_collapse h_M42_or h_M43_or h_M44_or h_M45_or h_M46_or h_M47_or
      h_is_loadX0_lb (by
        rcases h_sum_or with h | h
        · rw [show (Main[42] + Main[43] + Main[44] + Main[45] + Main[46] + Main[47] +
            Main[41]) = 0 from by linear_combination h]; ring
        · rw [show (Main[42] + Main[43] + Main[44] + Main[45] + Main[46] + Main[47] +
            Main[41]) - 1 = 0 from by linear_combination h, zero_mul])
  -- Sum-equals-one is now derivable.
  have h_sum_eq_one : Main[41] + Main[42] + Main[43] + Main[44] + Main[45] + Main[46] +
      Main[47] = 1 := by
    rw [hM42_zero, hM43_zero, hM44_zero, hM45_zero, hM46_zero, hM47_zero, h_is_loadX0_lb]
    ring
  -- For LB, NONE of E92/E95/E100 force any of Main[38], Main[39], Main[40]:
  -- all three offset bits are free.
  -- Derive Main[13] = 1 from h_E125.
  have hM13 : Main[13] = 1 := by
    rcases h_E125 with h | h
    · exfalso; rw [h_sum_eq_one] at h; exact one_ne_zero h
    · exact h
  rw [h_sum_eq_one] at h_addr
  rw [h_sum_eq_one, hM42_zero, hM43_zero, hM44_zero, hM45_zero, hM46_zero, hM47_zero,
    h_is_loadX0_lb] at h_reader
  have h_reader' :=
    ITypeReaderImmutable.allHold_constraints_iff_is_real_poly (h := rfl) (h_trusted := rfl) |>.mp h_reader
  obtain ⟨h_trusted, h6_lt, h14_lt, h21_lt, h22_lt, h23_lt, h24_lt,
    _hM13_or, h13_iff_op_a_zero, _hPC_align, _hPC0_lt, _hPC1_lt, _hPC2_lt,
    _hM12_lt, _hM20_lt, _h_clk_a, _h_clk_b, _h_op_a_isU64, h15u64,
    _h_op_a_zero_implies⟩ := h_reader'
  have hp_lt : 131072 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    have h17 : (2 : ℕ) ^ 17 = 131072 := by decide
    omega
  have h32val : (32 : ZMod p).val = 32 := val_32_zmod_p
  have h65val : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
  have h29_lt_p : (29 : ℕ) < p := by omega
  have h29_val : (29 : ZMod p).val = 29 := ZMod.val_natCast_of_lt h29_lt_p
  -- The opcode argument simp-reduces to 29 since only Main[41] is non-zero.
  simp [Opcode.trusted_instr_poly, Opcode.ofNat, Nat.ble,
    h29_val, i_type_constraints_poly] at h_trusted
  have h14_lt_zmod : Main[14] < (32 : ZMod p) := by clear *- h_trusted; simp_all only
  have h_imm_se : Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] =
      BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) := by
    clear *- h_trusted; simp_all only
  have h6 : Main[6].val < 32 := by
    have : Main[6].val < (32 : ZMod p).val := h6_lt; rwa [h32val] at this
  have h14 : Main[14].val < 32 := by
    have : Main[14].val < (32 : ZMod p).val := h14_lt_zmod; rwa [h32val] at this
  have h6_eq_zero : Main[6] = 0 := h13_iff_op_a_zero.mp hM13
  have h6_val_eq_zero : Main[6].val = 0 := by rw [h6_eq_zero, ZMod.val_zero]
  have h_op_a_zero : (BitVec.ofNat 5 Main[6].val : BitVec 5) = 0#5 := by
    rw [h6_val_eq_zero]
  have h21u64 : Word.isU64_poly #v[Main[21], Main[22], Main[23], Main[24]] := by
    apply Word.isU64_of_cases_poly <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · have : Main[21].val < (65536 : ZMod p).val := h21_lt; rwa [h65val] at this
    · have : Main[22].val < (65536 : ZMod p).val := h22_lt; rwa [h65val] at this
    · have : Main[23].val < (65536 : ZMod p).val := h23_lt; rwa [h65val] at this
    · have : Main[24].val < (65536 : ZMod p).val := h24_lt; rwa [h65val] at this
  have h_mem_isU64' : Word.isU64_poly #v[Main[29], Main[30], Main[31], Main[32]] := by
    apply h_mem_isU64
    rw [h_sum_eq_one]; exact one_ne_zero
  have haddr_spec := AddrAddOperation.spec_of_constraints_poly _ _ h15u64 h21u64 _ h_addr
  obtain ⟨haddr_isU64, haddr_eq⟩ := haddr_spec
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ] at haddr_isU64 haddr_eq
  have h25_lt : Main[25].val < 65536 := haddr_isU64 0
  have h26_lt : Main[26].val < 65536 := haddr_isU64 1
  have h27_lt : Main[27].val < 65536 := haddr_isU64 2
  have h28_inv' : Main[28] * (Main[26] + Main[27]) = 1 := by
    rw [h28_inv, h_sum_eq_one]
  obtain ⟨h_addr_lo, h_addr_hi⟩ :=
    AddressOperation.addr_limbs_bounds Main[25] Main[26] Main[27] Main[28]
      h25_lt h26_lt h27_lt h28_inv'
  have h_addr_eq :
      (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] +
        Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]]).toNat =
        Main[25].val + Main[26].val * 2 ^ 16 + Main[27].val * 2 ^ 32 := by
    rw [← haddr_eq, Word.toBitVec64_poly_toNat_poly haddr_isU64,
      Word.toNat_poly_def]; simp
  have h_offset_eq :
      Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] =
        BitVec.signExtend 64 (sp1_imm_c Main) := by
    rw [h_imm_se]; rfl
  have h_align : (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] +
        Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]]).toNat % 1 = 0 := by
    have h := h_is_aligned
    rw [← h_imm_se, is_aligned_vaddr_iff_mod] at h
    exact h
  have h_in_range :
      range_subset (zero_extend (BitVec.addInt
          (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] +
            BitVec.signExtend 64 (sp1_imm_c Main)) 0))
        (to_bits 1) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true := by
    rw [← h_offset_eq]
    refine range_subset_sp1_pma _ 1 (by omega) ?_ ?_
    · rw [h_addr_eq]; exact h_addr_lo
    · omega
  have h_mem0_lt : Main[29].val < 65536 := h_mem_isU64' 0
  have h_mem1_lt : Main[30].val < 65536 := h_mem_isU64' 1
  have h_mem2_lt : Main[31].val < 65536 := h_mem_isU64' 2
  have h_mem3_lt : Main[32].val < 65536 := h_mem_isU64' 3
  have h2728 : ¬ (Main[26] = 0 ∧ Main[27] = 0) := by
    intro ⟨hm26, hm27⟩
    rw [hm26, hm27, add_zero, mul_zero] at h28_inv
    rw [h_sum_eq_one] at h28_inv
    exact zero_ne_one h28_inv
  -- All three offset bits free.
  simp [SP1ConstraintList.initialState_poly, LoadX0.constraints,
    AddressOperation.constraints, SP1Constraint.toStateProp_poly,
    AddrAddOperation.constraints, ITypeReaderImmutable.constraints,
    CPUState.constraints, BitVec.ofNatLT_eq_ofNat,
    Opcode.ofNat, Nat.ble, h6, h14, h29_val, h_is_loadX0_lb,
    hM42_zero, hM43_zero, hM44_zero,
    hM45_zero, hM46_zero, hM47_zero, h2728] at state_cstrs
  obtain ⟨h_read_pc, _h6_op_a, h14_op_a, hload⟩ := state_cstrs
  rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_read_pc
  have h_fits_real : (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat +
      (Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]]).toNat < 2 ^ 64 := by
    have := h_fits_in_mem
    simp only [sp1_imm_c] at this
    rw [← h_imm_se] at this
    omega
  have haddr_nat : (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat +
          (Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]]).toNat =
        Word.toNat_poly #v[Main[25], Main[26], Main[27], (0 : ZMod p)] := by
    have heq := congr_arg BitVec.toNat haddr_eq
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt h_fits_real] at heq
    rw [← heq, Word.toBitVec64_poly, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by
        rw [Word.toNat_poly_def]
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ, ZMod.val_zero, Nat.zero_mul, Nat.add_zero]
        have hpow : (2 ^ 64 : ℕ) = 18446744073709551616 := by decide
        rw [hpow]
        have h26m : Main[26].val * 65536 ≤ 65535 * 65536 := by
          have : Main[26].val ≤ 65535 := by omega
          exact Nat.mul_le_mul_right _ this
        have h27m : Main[27].val * 4294967296 ≤ 65535 * 4294967296 := by
          have : Main[27].val ≤ 65535 := by omega
          exact Nat.mul_le_mul_right _ this
        omega)]
  have haddr_plus : ∀ (k : ℕ), k < 8 →
      Word.toNat_poly #v[Main[25], Main[26], Main[27], (0 : ZMod p)] + k =
      Word.toNat_poly #v[Main[25] + (k : ZMod p), Main[26], Main[27], (0 : ZMod p)] := by
    intro k hk
    have hk_val : ((k : ℕ) : ZMod p).val = k := ZMod.val_natCast_of_lt (by omega)
    have h25k_lt : Main[25].val + (k : ZMod p).val < p := by rw [hk_val]; omega
    have h25k_val : (Main[25] + (k : ZMod p)).val = Main[25].val + k := by
      rw [ZMod.val_add_of_lt h25k_lt, hk_val]
    simp only [Word.toNat_poly_def, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, ZMod.val_zero, Nat.zero_mul,
      Nat.add_zero, h25k_val]
    omega
  -- 8-way nested case-split on (Main[40], Main[39], Main[38]).
  rcases h_M40_or with hM40_zero | hM40_one
  · rcases h_M39_or with hM39_zero | hM39_one
    · rcases h_M38_or with hM38_zero | hM38_one
      · -- 000: offset 0. Byte = Main[29] low.
        simp [spec_loadX0_lb, sp1_loadX0,
          sp1_op_a, sp1_ob_b, sp1_imm_c,
          op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
          EStateM.Result.map, execute_LOAD, h_read_pc, h_op_a_zero]
        rw [run_vmem_read_of_width_1' (BitVec.ofNat 5 Main[14].val)
          (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]])
          (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
          (BitVec.ofNat 8 Main[29].val)]
        · simp
        · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true,
            implies_true]
        · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
        · exact h_is_aligned
        · constructor <;> simpa [Std.ExtDHashMap.get_insert]
        · exact h_fits_in_mem
        · exact h_in_range
        · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
                  Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
              haddr_nat,
              show (Main[25] : ZMod p) =
                Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38] from by
                  rw [hM40_zero, hM39_zero, hM38_zero]; ring]
          simpa using hload.1
      · -- 001: offset 1. Byte = Main[29] high.
        simp [spec_loadX0_lb, sp1_loadX0,
          sp1_op_a, sp1_ob_b, sp1_imm_c,
          op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
          EStateM.Result.map, execute_LOAD, h_read_pc, h_op_a_zero]
        rw [run_vmem_read_of_width_1' (BitVec.ofNat 5 Main[14].val)
          (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]])
          (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
          (BitVec.ofNat 8 (Main[29].val >>> 8))]
        · simp
        · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true,
            implies_true]
        · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
        · exact h_is_aligned
        · constructor <;> simpa [Std.ExtDHashMap.get_insert]
        · exact h_fits_in_mem
        · exact h_in_range
        · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
                  Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
              haddr_nat,
              show (Main[25] : ZMod p) =
                Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38] + 1 from by
                  rw [hM40_zero, hM39_zero, hM38_one]; ring]
          simpa using hload.2.1
    · rcases h_M38_or with hM38_zero | hM38_one
      · -- 010: offset 2. Byte = Main[30] low.
        simp [spec_loadX0_lb, sp1_loadX0,
          sp1_op_a, sp1_ob_b, sp1_imm_c,
          op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
          EStateM.Result.map, execute_LOAD, h_read_pc, h_op_a_zero]
        rw [run_vmem_read_of_width_1' (BitVec.ofNat 5 Main[14].val)
          (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]])
          (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
          (BitVec.ofNat 8 Main[30].val)]
        · simp
        · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true,
            implies_true]
        · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
        · exact h_is_aligned
        · constructor <;> simpa [Std.ExtDHashMap.get_insert]
        · exact h_fits_in_mem
        · exact h_in_range
        · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
                  Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
              haddr_nat,
              show (Main[25] : ZMod p) =
                Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38] + 2 from by
                  rw [hM40_zero, hM39_one, hM38_zero]; ring]
          simpa using hload.2.2.1
      · -- 011: offset 3. Byte = Main[30] high.
        simp [spec_loadX0_lb, sp1_loadX0,
          sp1_op_a, sp1_ob_b, sp1_imm_c,
          op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
          EStateM.Result.map, execute_LOAD, h_read_pc, h_op_a_zero]
        rw [run_vmem_read_of_width_1' (BitVec.ofNat 5 Main[14].val)
          (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]])
          (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
          (BitVec.ofNat 8 (Main[30].val >>> 8))]
        · simp
        · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true,
            implies_true]
        · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
        · exact h_is_aligned
        · constructor <;> simpa [Std.ExtDHashMap.get_insert]
        · exact h_fits_in_mem
        · exact h_in_range
        · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
                  Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
              haddr_nat,
              show (Main[25] : ZMod p) =
                Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38] + 3 from by
                  rw [hM40_zero, hM39_one, hM38_one]; ring]
          simpa using hload.2.2.2.1
  · rcases h_M39_or with hM39_zero | hM39_one
    · rcases h_M38_or with hM38_zero | hM38_one
      · -- 100: offset 4. Byte = Main[31] low.
        simp [spec_loadX0_lb, sp1_loadX0,
          sp1_op_a, sp1_ob_b, sp1_imm_c,
          op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
          EStateM.Result.map, execute_LOAD, h_read_pc, h_op_a_zero]
        rw [run_vmem_read_of_width_1' (BitVec.ofNat 5 Main[14].val)
          (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]])
          (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
          (BitVec.ofNat 8 Main[31].val)]
        · simp
        · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true,
            implies_true]
        · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
        · exact h_is_aligned
        · constructor <;> simpa [Std.ExtDHashMap.get_insert]
        · exact h_fits_in_mem
        · exact h_in_range
        · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
                  Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
              haddr_nat,
              show (Main[25] : ZMod p) =
                Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38] + 4 from by
                  rw [hM40_one, hM39_zero, hM38_zero]; ring]
          simpa using hload.2.2.2.2.1
      · -- 101: offset 5. Byte = Main[31] high.
        simp [spec_loadX0_lb, sp1_loadX0,
          sp1_op_a, sp1_ob_b, sp1_imm_c,
          op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
          EStateM.Result.map, execute_LOAD, h_read_pc, h_op_a_zero]
        rw [run_vmem_read_of_width_1' (BitVec.ofNat 5 Main[14].val)
          (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]])
          (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
          (BitVec.ofNat 8 (Main[31].val >>> 8))]
        · simp
        · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true,
            implies_true]
        · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
        · exact h_is_aligned
        · constructor <;> simpa [Std.ExtDHashMap.get_insert]
        · exact h_fits_in_mem
        · exact h_in_range
        · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
                  Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
              haddr_nat,
              show (Main[25] : ZMod p) =
                Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38] + 5 from by
                  rw [hM40_one, hM39_zero, hM38_one]; ring]
          simpa using hload.2.2.2.2.2.1
    · rcases h_M38_or with hM38_zero | hM38_one
      · -- 110: offset 6. Byte = Main[32] low.
        simp [spec_loadX0_lb, sp1_loadX0,
          sp1_op_a, sp1_ob_b, sp1_imm_c,
          op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
          EStateM.Result.map, execute_LOAD, h_read_pc, h_op_a_zero]
        rw [run_vmem_read_of_width_1' (BitVec.ofNat 5 Main[14].val)
          (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]])
          (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
          (BitVec.ofNat 8 Main[32].val)]
        · simp
        · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true,
            implies_true]
        · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
        · exact h_is_aligned
        · constructor <;> simpa [Std.ExtDHashMap.get_insert]
        · exact h_fits_in_mem
        · exact h_in_range
        · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
                  Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
              haddr_nat,
              show (Main[25] : ZMod p) =
                Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38] + 6 from by
                  rw [hM40_one, hM39_one, hM38_zero]; ring]
          simpa using hload.2.2.2.2.2.2.1
      · -- 111: offset 7. Byte = Main[32] high.
        simp [spec_loadX0_lb, sp1_loadX0,
          sp1_op_a, sp1_ob_b, sp1_imm_c,
          op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
          EStateM.Result.map, execute_LOAD, h_read_pc, h_op_a_zero]
        rw [run_vmem_read_of_width_1' (BitVec.ofNat 5 Main[14].val)
          (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]])
          (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
          (BitVec.ofNat 8 (Main[32].val >>> 8))]
        · simp
        · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true,
            implies_true]
        · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
        · exact h_is_aligned
        · constructor <;> simpa [Std.ExtDHashMap.get_insert]
        · exact h_fits_in_mem
        · exact h_in_range
        · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
                  Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
              haddr_nat,
              show (Main[25] : ZMod p) =
                Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38] + 7 from by
                  rw [hM40_one, hM39_one, hM38_one]; ring]
          simpa using hload.2.2.2.2.2.2.2

end LoadX0

end Load
