import SP1Clean.Chips.ALU.ShiftLeftChip.Cols
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ALUTypeReader
import SP1Clean.Operations.U16MSBOperation
import SP1Chips.ShiftLeft.Common

/-! # `ShiftLeftChip` cols-level lemmas (4-lemma scaffold, all sorry'd)

2-variant chip (`sll`/`sllw`). The shift operation is inline (no
separate `ShiftLeftOperation` module); the chip-level
`_root_.ShiftLeft.allHold_constraints_iff` exposes the byte-level
internals directly. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.ShiftLeft

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
/-- Round-trip on the cols struct: `toMain` then `fromMain` recovers `cols`,
given the UserMode TrustMode marker (`adapter_cols.is_trusted` aliases the
`is_sll + is_sllw` sum, the one non-column cell `fromMain` synthesizes). -/
lemma fromMain_toMain (cols : ShiftLeftCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted = cols.is_sll + cols.is_sllw) :
    fromMain (toMain cols) = cols := by
  rcases cols with ⟨state, adapter, result, c_bits, v_01, v_012, v_0123, shift_u16,
    lower_limb, higher_limb, limb_result, sllw_msb, is_sll, is_sllw, is_sllw_imm, adapter_cols⟩
  rcases state with ⟨clk_high, clk_16_24, clk_0_16, pc⟩
  rcases adapter with ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c, op_c_memory, imm_c⟩
  rcases op_a_memory with ⟨op_a_pv, op_a_ts⟩; rcases op_a_ts with ⟨op_a_pl, op_a_dll⟩
  rcases op_b_memory with ⟨op_b_pv, op_b_ts⟩; rcases op_b_ts with ⟨op_b_pl, op_b_dll⟩
  rcases op_c_memory with ⟨op_c_pv, op_c_ts⟩; rcases op_c_ts with ⟨op_c_pl, op_c_dll⟩
  rcases sllw_msb with ⟨msb⟩
  rcases adapter_cols with ⟨is_trusted⟩
  have h : is_trusted = is_sll + is_sllw := by simpa using h_trusted
  simp only [h, fromMain, toMain, ShiftLeftCols.mk.injEq, CPUState.mk.injEq,
    ALUTypeReader.mk.injEq, MemoryAccessInSharedCols.mk.injEq,
    MemoryAccessInShardTimestamp.mk.injEq, U16MSBOperation.mk.injEq,
    UserModeReaderCols.mk.injEq, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ, and_self, true_and,
    and_true, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply Vector.ext; intro i hi; interval_cases i <;> rfl)

lemma allHold_iff_structural
    (Main : Vector (ZMod p) 65)
    (h_is_real : Main[62] + Main[63] = 1) :
    (_root_.ShiftLeft.constraints Main).allHold ↔
      Assertion.FormalSpec (fromMain Main) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  haveI : Fact (p > 65536) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rw [show (_root_.ShiftLeft.constraints Main).allHold
        = List.Forall SP1Constraint.toProp (_root_.ShiftLeft.constraints Main) from rfl,
    _root_.ShiftLeft.allHold_constraints_iff Main]
  simp only [Assertion.FormalSpec, fromMain, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ Iff.rfl))
  · -- U16MSB block (faithful reformulation; range bridged by `range_at_sixteen`)
    simp only [U16MSBOperation.constraints, SP1ConstraintList.allHold, List.Forall,
      SP1Constraint.toProp, ByteOpcode.ofNat_seven,
      SP1Clean.U16MSBOp.range_at_sixteen, and_true, Nat.cast_ofNat]
  · -- CPUState
    exact SP1Clean.CPUState.Gated.Assertion.Spec_iff_sp1
  · -- ALUTypeReader (gate args normalize to `1 1` via `is_real = 1`)
    rw [h_is_real]
    exact SP1Clean.ALUTypeReader.Gated.Assertion.Spec_iff_sp1

end SP1Clean.ShiftLeft
