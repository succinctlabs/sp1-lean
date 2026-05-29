import SP1Clean.Chips.ALU.ShiftRightChip.Cols
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ALUTypeReader
import SP1Clean.Operations.U16MSBOperation
import SP1Chips.ShiftRight.Common

/-! # `ShiftRightChip` cols-level lemmas: `fromMain_toMain` round-trip +
`allHold_iff_structural` (SP1 row `.allHold` ↔ structural `FormalSpec`).

4-variant chip (`srl`/`sra`/`srlw`/`sraw`). The shift operation is inline (no
separate `ShiftRightOperation` module); the chip-level
`_root_.ShiftRight.allHold_constraints_iff` exposes the byte-level internals
directly. Same discipline as `ShiftLeftChip`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.ShiftRight

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
/-- Round-trip on the cols struct: `toMain` then `fromMain` recovers `cols`,
given the UserMode TrustMode marker (`adapter_cols.is_trusted` aliases the
`is_srl + is_sra + is_srlw + is_sraw` sum, the one non-column cell `fromMain`
synthesizes). -/
lemma fromMain_toMain (cols : ShiftRightCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted =
      cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw) :
    fromMain (toMain cols) = cols := by
  rcases cols with ⟨state, adapter, op_a_write_value, b_msb, srw_msb, c_bits,
    sra_msb_v0123, v_0123, v_012, v_01, lower_limb, higher_limb, limb_result,
    shift_u16, is_srl, is_sra, is_srlw, is_sraw, is_w_imm, adapter_cols⟩
  rcases state with ⟨clk_high, clk_16_24, clk_0_16, pc⟩
  rcases adapter with ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c, op_c_memory, imm_c⟩
  rcases op_a_memory with ⟨op_a_pv, op_a_ts⟩; rcases op_a_ts with ⟨op_a_pl, op_a_dll⟩
  rcases op_b_memory with ⟨op_b_pv, op_b_ts⟩; rcases op_b_ts with ⟨op_b_pl, op_b_dll⟩
  rcases op_c_memory with ⟨op_c_pv, op_c_ts⟩; rcases op_c_ts with ⟨op_c_pl, op_c_dll⟩
  rcases b_msb with ⟨bmsb⟩
  rcases srw_msb with ⟨smsb⟩
  rcases adapter_cols with ⟨is_trusted⟩
  have h : is_trusted = is_srl + is_sra + is_srlw + is_sraw := by simpa using h_trusted
  simp only [h, fromMain, toMain, ShiftRightCols.mk.injEq, CPUState.mk.injEq,
    ALUTypeReader.mk.injEq, MemoryAccessInSharedCols.mk.injEq,
    MemoryAccessInShardTimestamp.mk.injEq, U16MSBOperation.mk.injEq,
    UserModeReaderCols.mk.injEq, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ, and_self, true_and,
    and_true, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply Vector.ext; intro i hi; interval_cases i <;> rfl)

lemma allHold_iff_structural
    (Main : Vector (ZMod p) 69)
    (h_is_real : Main[64] + Main[65] + Main[66] + Main[67] = 1) :
    (_root_.ShiftRight.constraints Main).allHold ↔
      Assertion.FormalSpec (fromMain Main) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  haveI : Fact (p > 65536) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rw [show (_root_.ShiftRight.constraints Main).allHold
        = List.Forall SP1Constraint.toProp (_root_.ShiftRight.constraints Main) from rfl,
    _root_.ShiftRight.allHold_constraints_iff Main]
  simp only [Assertion.FormalSpec, fromMain, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ Iff.rfl))))
  · -- U16MSB block 1 (SRA, op_b high limb)
    simp only [U16MSBOperation.constraints, SP1ConstraintList.allHold, List.Forall,
      SP1Constraint.toProp, ByteOpcode.ofNat_seven,
      SP1Clean.U16MSBOp.range_at_sixteen, and_true, Nat.cast_ofNat]
  · -- U16MSB block 2 (SRAW, op_b mid limb)
    simp only [U16MSBOperation.constraints, SP1ConstraintList.allHold, List.Forall,
      SP1Constraint.toProp, ByteOpcode.ofNat_seven,
      SP1Clean.U16MSBOp.range_at_sixteen, and_true, Nat.cast_ofNat]
  · -- U16MSB block 3 (SRLW/SRAW, result high limb)
    simp only [U16MSBOperation.constraints, SP1ConstraintList.allHold, List.Forall,
      SP1Constraint.toProp, ByteOpcode.ofNat_seven,
      SP1Clean.U16MSBOp.range_at_sixteen, and_true, Nat.cast_ofNat]
  · -- CPUState
    exact SP1Clean.CPUState.Gated.Assertion.Spec_iff_sp1
  · -- ALUTypeReader (gate args normalize to `1 1` via `is_real = 1`)
    rw [h_is_real]
    exact SP1Clean.ALUTypeReader.Gated.Assertion.Spec_iff_sp1

end SP1Clean.ShiftRight
