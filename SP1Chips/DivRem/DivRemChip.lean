import SP1Operations.Operation.MulOperation.MulOperation
import SP1Operations.Operation.AddOperation.AddOperation
import SP1Operations.Compare.IsEqualWordOperation.IsEqualWordOperation
import SP1Operations.Compare.IsZeroWordOperation.IsZeroWordOperation
import SP1Operations.Compare.LtOperationUnsigned.LtOperationUnsigned
import SP1Operations.Operation.U16MSBOperation.U16MSBOperation
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.RTypeReader.RTypeReader
import SP1Chips.DivRem.DivRem
import SP1Chips.DivRem.DivuRemu
import SP1Chips.DivRem.DivwRemw
import SP1Chips.DivRem.DivuwRemuw

set_option linter.style.setOption false
set_option linter.style.longLine false

open LeanRV64D.Functions
open BitVec

open DivRem

section poly_prologue

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 246)

/-- Variant-INDEPENDENT facts available without the active variant flag in scope:
register bounds (`op_a < 32`, `op_b/op_c/pc[0] < 65536`), the U64 shapes for
`op_b`/`op_c`, the `op_a = 0 → result = 0` implication, and the eight
`sop_i` mutual-exclusion implications. The op_b/op_c bounds at `< 32` and
the four state-side reads remain variant-dependent and are derived per-arm
in each `correct_<v>`. -/
lemma correct_prologue_facts
  (cstrs : (constraints Main).allHold)
  (h_is_real : is_real Main) :
  Main[6].val < 32 ∧
  Main[14].val < 65536 ∧
  Main[21].val < 65536 ∧
  Main[3].val < 65536 ∧
  Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] ∧
  Word.isU64 #v[Main[22], Main[23], Main[24], Main[25]] ∧
  (Main[6] = 0 → Main[28] = 0 ∧ Main[29] = 0 ∧ Main[30] = 0 ∧ Main[31] = 0) ∧
  (Main[201] = 1 → Main[202] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0) ∧
  (Main[202] = 1 → Main[201] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0) ∧
  (Main[203] = 1 → Main[201] = 0 ∧ Main[202] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0) ∧
  (Main[204] = 1 → Main[201] = 0 ∧ Main[202] = 0 ∧ Main[203] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0) ∧
  (Main[205] = 1 → Main[201] = 0 ∧ Main[202] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0) ∧
  (Main[206] = 1 → Main[201] = 0 ∧ Main[202] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0) ∧
  (Main[207] = 1 → Main[201] = 0 ∧ Main[202] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[208] = 0) ∧
  (Main[208] = 1 → Main[201] = 0 ∧ Main[202] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0) := by
  obtain ⟨ha, hb, hc, hpc⟩ := register_bounds Main cstrs h_is_real
  obtain ⟨is_U64_b, is_U64_c⟩ := ops_U64_b_c Main cstrs h_is_real
  have h_a0 := op_a_is_0 Main cstrs h_is_real
  obtain ⟨sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8⟩ := single_op Main cstrs
  exact ⟨ha, hb, hc, hpc, is_U64_b, is_U64_c, h_a0,
    sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8⟩

end poly_prologue

namespace Div

open DivRem

def spec_div (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_DIV rs2 rs1 rd false
  pure ()

end Div

namespace Divu

open DivRem

def spec_divu (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_DIV rs2 rs1 rd true
  pure ()

end Divu

namespace Divw

open DivRem

def spec_divw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_DIVW rs2 rs1 rd false
  pure ()

end Divw

namespace Divuw

open DivRem

def spec_divuw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_DIVW rs2 rs1 rd true
  pure ()

end Divuw

namespace Rem

open DivRem

def spec_rem (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_REM rs2 rs1 rd false
  pure ()

end Rem

namespace Remu

open DivRem

def spec_remu (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_REM rs2 rs1 rd true
  pure ()

end Remu

namespace Remw

open DivRem

def spec_remw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_REMW rs2 rs1 rd false
  pure ()

end Remw

namespace Remuw

open DivRem

def spec_remuw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_REMW rs2 rs1 rd true
  pure ()

end Remuw

-- ============================================================================
-- Chip-level correctness theorems.
-- ============================================================================
-- Each `correct_<variant>` delegates the variant-specific witness to the
-- corresponding `spec.<variant>` wrapper in
-- `SP1Chips/DivRem/{DivRem,DivuRemu,DivwRemw,DivuwRemuw}.lean`.
-- `correct_prologue_facts` handles the prologue shared by all 8 variants.

namespace DivRem.Poly

open DivRem

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)]
  (Main : Vector (ZMod p) 246)
  (s : SailState)
  (h_is_real : is_real Main)

def sp1_op : SailM Unit := do
  let op_a := sp1_op_a Main
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[28], Main[29], Main[30], Main[31]])

open Sail

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 8000000 in
-- Heavy reader/state-cstrs destructure + spec.<v> delegate exceeds the
-- default budget on every chip-level correct_<v> variant.
set_option maxRecDepth 2000000 in
theorem correct_div
    (cstrs : (constraints Main).allHold)
    (h_is_real : is_real Main)
    (h_is_div : is_div Main)
    (state_cstrs : (constraints Main).initialState s) :
    let op_c := sp1_op_c Main
    let op_b := sp1_op_b Main
    let op_a := sp1_op_a Main
    (Div.spec_div (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op Main).run s
  := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  have h17 : 2 ^ 17 < p := Fact.out
  obtain ⟨h6, h14, h21, is_U64_b, is_U64_c⟩ :=
    DivRem.div_chip_bounds Main cstrs h_is_real h_is_div
  have h_a0 := DivRem.op_a_is_0 Main cstrs h_is_real
  obtain ⟨_, _, _, h_pc3, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    correct_prologue_facts Main cstrs h_is_real
  simp only [DivRem.is_real] at h_is_real
  simp only [SP1ConstraintList.initialState, constraints,
    SP1Constraint.toStateProp, List.Forall] at state_cstrs
  simp only [MulOperation.constraints, IsEqualWordOperation.constraints,
    IsZeroWordOperation.constraints, U16MSBOperation.constraints,
    AddOperation.constraints, LtOperationUnsigned.constraints,
    U16toU8OperationSafe.constraints, U16CompareOperation.constraints,
    IsZeroOperation.constraints,
    CPUState.constraints, RTypeReader.constraints,
    SP1Constraint.toStateProp, List.Forall] at state_cstrs
  simp [h6, h14, h21, h_is_real] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
  simp only [BitVec.ofNatLT_eq_ofNat] at *
  simp [Div.spec_div, sp1_op, execute_DIV']
  rw [Sail.run_readReg, read_pc]
  simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
  by_cases h_is_op_a_0 : Main[6] = 0
  · obtain ⟨ha28, ha29, ha30, ha31⟩ := h_a0 h_is_op_a_0
    rw [ha28, ha29, ha30, ha31]
    have h_zero : Word.toBitVec64 (#v[0, 0, 0, 0] : Word (ZMod p)) = 0#64 := by
      simp [Word.toBitVec64, Word.toNat, ZMod.val_zero]
    rw [if_pos h_zero]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    have h_bv_zero : BitVec.ofNat 5 Main[6].val = 0#5 := by
      rw [h_is_op_a_0, ZMod.val_zero]
    simp [h_bv_zero]
  · have h6_val : Main[6].val ≠ 0 := by
      intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
    have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
      intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
    rw [if_neg h_bv_neq, if_neg h_bv_neq]
    simp [DivRem.spec.div Main cstrs h_is_real h_is_div]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    simp [bitVecToRegidxVal]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 8000000 in
-- Heavy reader/state-cstrs destructure + spec.<v> delegate exceeds the
-- default budget on every chip-level correct_<v> variant.
set_option maxRecDepth 2000000 in
theorem correct_divu
    (cstrs : (constraints Main).allHold)
    (h_is_real : is_real Main)
    (h_is_divu : is_divu Main)
    (state_cstrs : (constraints Main).initialState s) :
    let op_c := sp1_op_c Main
    let op_b := sp1_op_b Main
    let op_a := sp1_op_a Main
    (Divu.spec_divu (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op Main).run s
  := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  -- Surface the prime-size bound as a Nat fact so omega can use it.
  have h17 : 2 ^ 17 < p := Fact.out
  -- Extract op_a/op_b/op_c < 32 bounds + U64 properties via the Common.lean helper.
  obtain ⟨h6, h14, h21, is_U64_b, is_U64_c⟩ :=
    DivRem.divu_chip_bounds Main cstrs h_is_real h_is_divu
  -- op_a = 0 → writeback limbs all 0 (for the case-pos op-a-x0 collapse).
  have h_a0 := DivRem.op_a_is_0 Main cstrs h_is_real
  -- PC[0] < 65536 bound (needed by lowLimb_add_nat's carry-check side condition).
  obtain ⟨_, _, _, h_pc3, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    correct_prologue_facts Main cstrs h_is_real
  -- Unfold h_is_real's type so simp can use it as a Main[244] = 1 rewrite.
  simp only [DivRem.is_real] at h_is_real
  -- State extraction in multi-pass simp to keep stack usage bounded.
  simp only [SP1ConstraintList.initialState, constraints,
    SP1Constraint.toStateProp, List.Forall] at state_cstrs
  simp only [MulOperation.constraints, IsEqualWordOperation.constraints,
    IsZeroWordOperation.constraints, U16MSBOperation.constraints,
    AddOperation.constraints, LtOperationUnsigned.constraints,
    U16toU8OperationSafe.constraints, U16CompareOperation.constraints,
    IsZeroOperation.constraints,
    CPUState.constraints, RTypeReader.constraints,
    SP1Constraint.toStateProp, List.Forall] at state_cstrs
  simp [h6, h14, h21, h_is_real] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
  -- Bridge BitVec↔Fin so read_op_b/c rewrites apply against the goal's BitVec form.
  simp only [BitVec.ofNatLT_eq_ofNat] at *
  simp [Divu.spec_divu, sp1_op, execute_DIV']
  rw [Sail.run_readReg, read_pc]
  simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
  by_cases h_is_op_a_0 : Main[6] = 0
  · obtain ⟨ha28, ha29, ha30, ha31⟩ := h_a0 h_is_op_a_0
    rw [ha28, ha29, ha30, ha31]
    have h_zero : Word.toBitVec64 (#v[0, 0, 0, 0] : Word (ZMod p)) = 0#64 := by
      simp [Word.toBitVec64, Word.toNat, ZMod.val_zero]
    rw [if_pos h_zero]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    have h_bv_zero : BitVec.ofNat 5 Main[6].val = 0#5 := by
      rw [h_is_op_a_0, ZMod.val_zero]
    simp [h_bv_zero]
  · have h6_val : Main[6].val ≠ 0 := by
      intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
    have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
      intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
    rw [if_neg h_bv_neq, if_neg h_bv_neq]
    simp [DivRem.spec.divu Main cstrs h_is_real h_is_divu]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    simp [bitVecToRegidxVal]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 8000000 in
-- Heavy reader/state-cstrs destructure + spec.<v> delegate exceeds the
-- default budget on every chip-level correct_<v> variant.
set_option maxRecDepth 2000000 in
theorem correct_divw
    (cstrs : (constraints Main).allHold)
    (h_is_real : is_real Main)
    (h_is_divw : is_divw Main)
    (state_cstrs : (constraints Main).initialState s) :
    let op_c := sp1_op_c Main
    let op_b := sp1_op_b Main
    let op_a := sp1_op_a Main
    (Divw.spec_divw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op Main).run s
  := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  have h17 : 2 ^ 17 < p := Fact.out
  obtain ⟨h6, h14, h21, is_U64_b, is_U64_c⟩ :=
    DivRem.divw_chip_bounds Main cstrs h_is_real h_is_divw
  have h_a0 := DivRem.op_a_is_0 Main cstrs h_is_real
  obtain ⟨_, _, _, h_pc3, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    correct_prologue_facts Main cstrs h_is_real
  simp only [DivRem.is_real] at h_is_real
  simp only [SP1ConstraintList.initialState, constraints,
    SP1Constraint.toStateProp, List.Forall] at state_cstrs
  simp only [MulOperation.constraints, IsEqualWordOperation.constraints,
    IsZeroWordOperation.constraints, U16MSBOperation.constraints,
    AddOperation.constraints, LtOperationUnsigned.constraints,
    U16toU8OperationSafe.constraints, U16CompareOperation.constraints,
    IsZeroOperation.constraints,
    CPUState.constraints, RTypeReader.constraints,
    SP1Constraint.toStateProp, List.Forall] at state_cstrs
  simp [h6, h14, h21, h_is_real] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
  simp only [BitVec.ofNatLT_eq_ofNat] at *
  simp [Divw.spec_divw, sp1_op, execute_DIVW']
  rw [Sail.run_readReg, read_pc]
  simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
  by_cases h_is_op_a_0 : Main[6] = 0
  · obtain ⟨ha28, ha29, ha30, ha31⟩ := h_a0 h_is_op_a_0
    rw [ha28, ha29, ha30, ha31]
    have h_zero : Word.toBitVec64 (#v[0, 0, 0, 0] : Word (ZMod p)) = 0#64 := by
      simp [Word.toBitVec64, Word.toNat, ZMod.val_zero]
    rw [if_pos h_zero]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    have h_bv_zero : BitVec.ofNat 5 Main[6].val = 0#5 := by
      rw [h_is_op_a_0, ZMod.val_zero]
    simp [h_bv_zero]
  · have h6_val : Main[6].val ≠ 0 := by
      intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
    have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
      intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
    rw [if_neg h_bv_neq, if_neg h_bv_neq]
    simp [DivRem.spec.divw Main cstrs h_is_real h_is_divw]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    simp [bitVecToRegidxVal]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 8000000 in
-- Heavy reader/state-cstrs destructure + spec.<v> delegate exceeds the
-- default budget on every chip-level correct_<v> variant.
set_option maxRecDepth 2000000 in
theorem correct_divuw
    (cstrs : (constraints Main).allHold)
    (h_is_real : is_real Main)
    (h_is_divuw : is_divuw Main)
    (state_cstrs : (constraints Main).initialState s) :
    let op_c := sp1_op_c Main
    let op_b := sp1_op_b Main
    let op_a := sp1_op_a Main
    (Divuw.spec_divuw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op Main).run s
  := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  have h17 : 2 ^ 17 < p := Fact.out
  obtain ⟨h6, h14, h21, is_U64_b, is_U64_c⟩ :=
    DivRem.divuw_chip_bounds Main cstrs h_is_real h_is_divuw
  have h_a0 := DivRem.op_a_is_0 Main cstrs h_is_real
  obtain ⟨_, _, _, h_pc3, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    correct_prologue_facts Main cstrs h_is_real
  simp only [DivRem.is_real] at h_is_real
  simp only [SP1ConstraintList.initialState, constraints,
    SP1Constraint.toStateProp, List.Forall] at state_cstrs
  simp only [MulOperation.constraints, IsEqualWordOperation.constraints,
    IsZeroWordOperation.constraints, U16MSBOperation.constraints,
    AddOperation.constraints, LtOperationUnsigned.constraints,
    U16toU8OperationSafe.constraints, U16CompareOperation.constraints,
    IsZeroOperation.constraints,
    CPUState.constraints, RTypeReader.constraints,
    SP1Constraint.toStateProp, List.Forall] at state_cstrs
  simp [h6, h14, h21, h_is_real] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
  simp only [BitVec.ofNatLT_eq_ofNat] at *
  simp [Divuw.spec_divuw, sp1_op, execute_DIVW']
  rw [Sail.run_readReg, read_pc]
  simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
  by_cases h_is_op_a_0 : Main[6] = 0
  · obtain ⟨ha28, ha29, ha30, ha31⟩ := h_a0 h_is_op_a_0
    rw [ha28, ha29, ha30, ha31]
    have h_zero : Word.toBitVec64 (#v[0, 0, 0, 0] : Word (ZMod p)) = 0#64 := by
      simp [Word.toBitVec64, Word.toNat, ZMod.val_zero]
    rw [if_pos h_zero]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    have h_bv_zero : BitVec.ofNat 5 Main[6].val = 0#5 := by
      rw [h_is_op_a_0, ZMod.val_zero]
    simp [h_bv_zero]
  · have h6_val : Main[6].val ≠ 0 := by
      intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
    have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
      intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
    rw [if_neg h_bv_neq, if_neg h_bv_neq]
    simp [DivRem.spec.divuw Main cstrs h_is_real h_is_divuw]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    simp [bitVecToRegidxVal]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 8000000 in
-- Heavy reader/state-cstrs destructure + spec.<v> delegate exceeds the
-- default budget on every chip-level correct_<v> variant.
set_option maxRecDepth 2000000 in
theorem correct_rem
    (cstrs : (constraints Main).allHold)
    (h_is_real : is_real Main)
    (h_is_rem : is_rem Main)
    (state_cstrs : (constraints Main).initialState s) :
    let op_c := sp1_op_c Main
    let op_b := sp1_op_b Main
    let op_a := sp1_op_a Main
    (Rem.spec_rem (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op Main).run s
  := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  have h17 : 2 ^ 17 < p := Fact.out
  obtain ⟨h6, h14, h21, is_U64_b, is_U64_c⟩ :=
    DivRem.rem_chip_bounds Main cstrs h_is_real h_is_rem
  have h_a0 := DivRem.op_a_is_0 Main cstrs h_is_real
  obtain ⟨_, _, _, h_pc3, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    correct_prologue_facts Main cstrs h_is_real
  simp only [DivRem.is_real] at h_is_real
  simp only [SP1ConstraintList.initialState, constraints,
    SP1Constraint.toStateProp, List.Forall] at state_cstrs
  simp only [MulOperation.constraints, IsEqualWordOperation.constraints,
    IsZeroWordOperation.constraints, U16MSBOperation.constraints,
    AddOperation.constraints, LtOperationUnsigned.constraints,
    U16toU8OperationSafe.constraints, U16CompareOperation.constraints,
    IsZeroOperation.constraints,
    CPUState.constraints, RTypeReader.constraints,
    SP1Constraint.toStateProp, List.Forall] at state_cstrs
  simp [h6, h14, h21, h_is_real] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
  simp only [BitVec.ofNatLT_eq_ofNat] at *
  simp [Rem.spec_rem, sp1_op, execute_REM']
  rw [Sail.run_readReg, read_pc]
  simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
  by_cases h_is_op_a_0 : Main[6] = 0
  · obtain ⟨ha28, ha29, ha30, ha31⟩ := h_a0 h_is_op_a_0
    rw [ha28, ha29, ha30, ha31]
    have h_zero : Word.toBitVec64 (#v[0, 0, 0, 0] : Word (ZMod p)) = 0#64 := by
      simp [Word.toBitVec64, Word.toNat, ZMod.val_zero]
    rw [if_pos h_zero]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    have h_bv_zero : BitVec.ofNat 5 Main[6].val = 0#5 := by
      rw [h_is_op_a_0, ZMod.val_zero]
    simp [h_bv_zero]
  · have h6_val : Main[6].val ≠ 0 := by
      intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
    have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
      intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
    rw [if_neg h_bv_neq, if_neg h_bv_neq]
    simp [DivRem.spec.rem Main cstrs h_is_real h_is_rem]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    simp [bitVecToRegidxVal]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 8000000 in
-- Heavy reader/state-cstrs destructure + spec.<v> delegate exceeds the
-- default budget on every chip-level correct_<v> variant.
set_option maxRecDepth 2000000 in
theorem correct_remu
    (cstrs : (constraints Main).allHold)
    (h_is_real : is_real Main)
    (h_is_remu : is_remu Main)
    (state_cstrs : (constraints Main).initialState s) :
    let op_c := sp1_op_c Main
    let op_b := sp1_op_b Main
    let op_a := sp1_op_a Main
    (Remu.spec_remu (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op Main).run s
  := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  have h17 : 2 ^ 17 < p := Fact.out
  obtain ⟨h6, h14, h21, is_U64_b, is_U64_c⟩ :=
    DivRem.remu_chip_bounds Main cstrs h_is_real h_is_remu
  have h_a0 := DivRem.op_a_is_0 Main cstrs h_is_real
  obtain ⟨_, _, _, h_pc3, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    correct_prologue_facts Main cstrs h_is_real
  simp only [DivRem.is_real] at h_is_real
  simp only [SP1ConstraintList.initialState, constraints,
    SP1Constraint.toStateProp, List.Forall] at state_cstrs
  simp only [MulOperation.constraints, IsEqualWordOperation.constraints,
    IsZeroWordOperation.constraints, U16MSBOperation.constraints,
    AddOperation.constraints, LtOperationUnsigned.constraints,
    U16toU8OperationSafe.constraints, U16CompareOperation.constraints,
    IsZeroOperation.constraints,
    CPUState.constraints, RTypeReader.constraints,
    SP1Constraint.toStateProp, List.Forall] at state_cstrs
  simp [h6, h14, h21, h_is_real] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
  simp only [BitVec.ofNatLT_eq_ofNat] at *
  simp [Remu.spec_remu, sp1_op, execute_REM']
  rw [Sail.run_readReg, read_pc]
  simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
  by_cases h_is_op_a_0 : Main[6] = 0
  · obtain ⟨ha28, ha29, ha30, ha31⟩ := h_a0 h_is_op_a_0
    rw [ha28, ha29, ha30, ha31]
    have h_zero : Word.toBitVec64 (#v[0, 0, 0, 0] : Word (ZMod p)) = 0#64 := by
      simp [Word.toBitVec64, Word.toNat, ZMod.val_zero]
    rw [if_pos h_zero]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    have h_bv_zero : BitVec.ofNat 5 Main[6].val = 0#5 := by
      rw [h_is_op_a_0, ZMod.val_zero]
    simp [h_bv_zero]
  · have h6_val : Main[6].val ≠ 0 := by
      intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
    have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
      intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
    rw [if_neg h_bv_neq, if_neg h_bv_neq]
    simp [DivRem.spec.remu Main cstrs h_is_real h_is_remu]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    simp [bitVecToRegidxVal]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 8000000 in
-- Heavy reader/state-cstrs destructure + spec.<v> delegate exceeds the
-- default budget on every chip-level correct_<v> variant.
set_option maxRecDepth 2000000 in
theorem correct_remw
    (cstrs : (constraints Main).allHold)
    (h_is_real : is_real Main)
    (h_is_remw : is_remw Main)
    (state_cstrs : (constraints Main).initialState s) :
    let op_c := sp1_op_c Main
    let op_b := sp1_op_b Main
    let op_a := sp1_op_a Main
    (Remw.spec_remw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op Main).run s
  := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  have h17 : 2 ^ 17 < p := Fact.out
  obtain ⟨h6, h14, h21, is_U64_b, is_U64_c⟩ :=
    DivRem.remw_chip_bounds Main cstrs h_is_real h_is_remw
  have h_a0 := DivRem.op_a_is_0 Main cstrs h_is_real
  obtain ⟨_, _, _, h_pc3, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    correct_prologue_facts Main cstrs h_is_real
  simp only [DivRem.is_real] at h_is_real
  simp only [SP1ConstraintList.initialState, constraints,
    SP1Constraint.toStateProp, List.Forall] at state_cstrs
  simp only [MulOperation.constraints, IsEqualWordOperation.constraints,
    IsZeroWordOperation.constraints, U16MSBOperation.constraints,
    AddOperation.constraints, LtOperationUnsigned.constraints,
    U16toU8OperationSafe.constraints, U16CompareOperation.constraints,
    IsZeroOperation.constraints,
    CPUState.constraints, RTypeReader.constraints,
    SP1Constraint.toStateProp, List.Forall] at state_cstrs
  simp [h6, h14, h21, h_is_real] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
  simp only [BitVec.ofNatLT_eq_ofNat] at *
  simp [Remw.spec_remw, sp1_op, execute_REMW']
  rw [Sail.run_readReg, read_pc]
  simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
  by_cases h_is_op_a_0 : Main[6] = 0
  · obtain ⟨ha28, ha29, ha30, ha31⟩ := h_a0 h_is_op_a_0
    rw [ha28, ha29, ha30, ha31]
    have h_zero : Word.toBitVec64 (#v[0, 0, 0, 0] : Word (ZMod p)) = 0#64 := by
      simp [Word.toBitVec64, Word.toNat, ZMod.val_zero]
    rw [if_pos h_zero]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    have h_bv_zero : BitVec.ofNat 5 Main[6].val = 0#5 := by
      rw [h_is_op_a_0, ZMod.val_zero]
    simp [h_bv_zero]
  · have h6_val : Main[6].val ≠ 0 := by
      intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
    have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
      intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
    rw [if_neg h_bv_neq, if_neg h_bv_neq]
    simp [DivRem.spec.remw Main cstrs h_is_real h_is_remw]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    simp [bitVecToRegidxVal]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 8000000 in
-- Heavy reader/state-cstrs destructure + spec.<v> delegate exceeds the
-- default budget on every chip-level correct_<v> variant.
set_option maxRecDepth 2000000 in
theorem correct_remuw
    (cstrs : (constraints Main).allHold)
    (h_is_real : is_real Main)
    (h_is_remuw : is_remuw Main)
    (state_cstrs : (constraints Main).initialState s) :
    let op_c := sp1_op_c Main
    let op_b := sp1_op_b Main
    let op_a := sp1_op_a Main
    (Remuw.spec_remuw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_op Main).run s
  := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  have h17 : 2 ^ 17 < p := Fact.out
  obtain ⟨h6, h14, h21, is_U64_b, is_U64_c⟩ :=
    DivRem.remuw_chip_bounds Main cstrs h_is_real h_is_remuw
  have h_a0 := DivRem.op_a_is_0 Main cstrs h_is_real
  obtain ⟨_, _, _, h_pc3, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    correct_prologue_facts Main cstrs h_is_real
  simp only [DivRem.is_real] at h_is_real
  simp only [SP1ConstraintList.initialState, constraints,
    SP1Constraint.toStateProp, List.Forall] at state_cstrs
  simp only [MulOperation.constraints, IsEqualWordOperation.constraints,
    IsZeroWordOperation.constraints, U16MSBOperation.constraints,
    AddOperation.constraints, LtOperationUnsigned.constraints,
    U16toU8OperationSafe.constraints, U16CompareOperation.constraints,
    IsZeroOperation.constraints,
    CPUState.constraints, RTypeReader.constraints,
    SP1Constraint.toStateProp, List.Forall] at state_cstrs
  simp [h6, h14, h21, h_is_real] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
  simp only [BitVec.ofNatLT_eq_ofNat] at *
  simp [Remuw.spec_remuw, sp1_op, execute_REMW']
  rw [Sail.run_readReg, read_pc]
  simp [sp1_op_a, sp1_op_b, sp1_op_c, read_op_b, read_op_c]
  by_cases h_is_op_a_0 : Main[6] = 0
  · obtain ⟨ha28, ha29, ha30, ha31⟩ := h_a0 h_is_op_a_0
    rw [ha28, ha29, ha30, ha31]
    have h_zero : Word.toBitVec64 (#v[0, 0, 0, 0] : Word (ZMod p)) = 0#64 := by
      simp [Word.toBitVec64, Word.toNat, ZMod.val_zero]
    rw [if_pos h_zero]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    have h_bv_zero : BitVec.ofNat 5 Main[6].val = 0#5 := by
      rw [h_is_op_a_0, ZMod.val_zero]
    simp [h_bv_zero]
  · have h6_val : Main[6].val ≠ 0 := by
      intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
    have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
      intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
    rw [if_neg h_bv_neq, if_neg h_bv_neq]
    simp [DivRem.spec.remuw Main cstrs h_is_real h_is_remuw]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    simp [bitVecToRegidxVal]

end DivRem.Poly
