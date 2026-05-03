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
wrap. Used to collapse the 7-way sub-opcode flag space inside LoadX0
when one specific flag is selected (here, `Main[47] = 1` for LD;
analogous helpers can be derived for the other six sub-opcodes by
permuting `a₇` to the relevant position). -/
private lemma seven_collapse_M47
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

/-
Per-sub-opcode `correct_loadX0_*` theorems are next-step work. The
LoadX0 chip lacks a single-flag iff lemma analogous to
`Load.LoadDouble.allHold_constraints_iff_of_is_ld_poly` because the
chip's constraint list interleaves all 7 sub-opcode flags via the
`E72 = Main[41] + … + Main[47]` umbrella gate. The required pieces
have all landed in this commit:

- `sp1_loadX0` advances PC only — the spec's `wX_bits 0 _` step is
  a no-op (`Lean_RV64D/Regs.lean:663`).
- `seven_collapse_M47` discharges the 7-way collapse from the
  mutual-exclusion + sum-equals-one constraints; an analog
  `seven_collapse_<flag>` for each of the other six sub-opcodes is
  a one-line permutation.
- For LD specifically (`Main[47] = 1`), byte-routing constraints
  `E92`/`E95`/`E100` then force `Main[38..40] = 0`, collapsing the
  AddressOperation offsets and matching LoadDouble's 8-byte aligned
  read structure exactly. The proof can then mirror
  `Load.LoadDouble.correct_ld` line-for-line, swapping
  `ITypeReader.allHold_constraints_iff_is_real_poly` for
  `ITypeReaderImmutable.allHold_constraints_iff_is_real_poly` and
  dropping the result-write step on the SP1 side.
-/

end LoadX0

end Load
