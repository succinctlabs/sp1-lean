import SP1Clean.Chips.ALU.AddwChip.Lemmas
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import SP1Foundations.ByteOpcode
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.Reader.OperandAccess
import SP1Clean.Reader.ALUTypeReader
import SP1Clean.Operations.AddwOperation
import SP1Clean.MemoryAccess
import SP1Clean.SP1Lookup
import RISCV.Instructions

/-! # `AddwChip` Clean circuit + `FormalAssertion`

Composes `CPUState.assertion` + `ALUTypeReader.assertion` (which itself
bundles ProgramTable + 3 gated OperandAccess + 4 op_a_0 gates + 4
imm_c-equality gates) + 2 trailing scalar gates. Mirrors the pattern of
`AddChip` (which uses `RTypeReader.assertion`) and `AddiChip` (which uses
`ITypeReader.assertion`).

**Multiplicity-aware semantics for op_c.** The gating mechanism lives in
`ALUTypeReader.assertion`'s internal `OperandAccess.assertionGated` call
with `mult := 1 - imm_c` (the reader pins is_real = 1, so this is
`is_real - imm_c` semantically). On ADDIW rows (`imm_c = 1`, hence
`mult = 0`), the op_c byte-bus lookup is vacuous, matching SP1's actual
emission (`alu_type.rs:142`). The chip-level `FormalSpec` exposes the
full `aluTypeReaderSpec` which captures both the unconditional clauses
and the `imm_c = 0 → byte facts` / `imm_c = 1 → prev_value = op_c`
implications.

The AddwOp carry chain is *not* emitted via subcircuit composition — its
`Assertion.Spec` inlines U16MSB clauses in a form that doesn't directly
match `AddwOp.Spec`'s `List.Forall SP1Constraint.toProp ...` envelope.
TraceSpec (used by SailBridge) carries `AddwOp.Spec` directly. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Addw

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

/-- Clean-side chip circuit. Composes `AddwOp.assertion` (the 32-bit ADDW
carry chain + sign-extension MSB) + `CPUState.Gated.assertion` +
`ALUTypeReader.Gated.assertion` (which bundles ProgramTable + 3 gated
OperandAccess + 4 op_a_0 gates + 4 imm_c-equality gates) + chip-level
`op_a_0 = 0` gate. The free `is_real * (is_real - 1) === 0` gate now
lives inside both Gated sub-circuits' first conjuncts. -/
@[reducible]
def main (cols : Var AddwCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩, adapter,
       addw_value, addw_msb, is_real, adapter_cols⟩ := cols
  let clk_low := clk_0_16 + clk_16_24 * 65536
  let op_a_write_value : Vector (Expression (ZMod p)) 4 :=
    #v[addw_value[0], addw_value[1], addw_msb * 65535, addw_msb * 65535]
  SP1Clean.AddwOp.assertion
    (⟨adapter.op_b_memory.prev_value, adapter.op_c_memory.prev_value,
       addw_value, addw_msb⟩ :
      Var SP1Clean.AddwOp.Inputs (ZMod p))
  SP1Clean.CPUState.Gated.assertion
    (⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩,
       #v[pc[0] + 4, pc[1], pc[2]], 8, is_real⟩ :
      Var SP1Clean.CPUState.Gated.Inputs (ZMod p))
  SP1Clean.ALUTypeReader.Gated.assertion
    (⟨clk_high, clk_low, 19, pc, op_a_write_value, adapter,
       is_real, adapter_cols.is_trusted⟩ :
      Var SP1Clean.ALUTypeReader.Gated.Inputs (ZMod p))
  adapter.op_a_0 === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) AddwCols unit where
  name := "SP1Clean.Addw"
  main := main
  -- Computed from main; ALUTypeReader contributes 72 (3 assertionGated × 24).
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

/-- The chip is the `UserMode` variant (`M = UserMode` in upstream Rust),
so its `adapter_cols.is_trusted` payload is structurally equal to `is_real`
(both alias `Main[35]` in the constraint compiler's emission). The
`is_real = 1` precondition restricts the FormalAssertion to non-padding
rows: completeness reconstructs `AddwOp.Assertion.Spec` for the
sub-circuit witness via the `addwOp_spec_iff_rv64_addw` backward
direction (which needs the BV64 + isU64 pair from `FormalSpec`'s
`is_real = 1 → ...` conjunct + operand bounds), so the chip contract is
only meaningful on real rows. Trace-soundness drivers discharge
`is_real = 1` per row before invoking `Addw.assertion`. -/
def Assumptions (cols : AddwCols (ZMod p)) : Prop :=
  cols.adapter_cols.is_trusted = cols.is_real ∧ cols.is_real = 1

/-- The unified chip Spec is defined in `Cols.lean` (`SP1Clean.Addw.FormalSpec`)
so `Lemmas.lean` can reference it. Re-exported here for the
`FormalAssertion` glue. -/
abbrev FormalSpec := @SP1Clean.Addw.FormalSpec p

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22⟩ := h_input
  subst_eqs
  obtain ⟨_h_trusted, h_is_real⟩ := h_assumptions
  obtain ⟨h_addwop_sub, h_cpu_sub, h_alu_sub, h_op_a_0⟩ := h_holds
  unfold id at *
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  change (Expression.eval env input_var_is_real : ZMod p) = 1 at h_is_real
  have h_addwop := h_addwop_sub trivial
  have h_alu := h_alu_sub trivial
  refine ⟨h_cpu_sub trivial, ?_, h_op_a_0, ?_⟩
  · -- Bridge ALU Gated `assertion.Spec` (lowercase) → `Gated.Assertion.Spec` (uppercase).
    simpa [SP1Clean.ALUTypeReader.Gated.assertion,
           SP1Clean.ALUTypeReader.Gated.Assertion.Spec, sub_eq_add_neg,
           Vector.getElem_map] using h_alu
  · -- Semantic conjunct: (isU64 ∧ BV64 = RV64.addw) via the bidirectional bridge.
    intro _h_is_real_eq
    -- Unfold the ALU spec into its 13 conjuncts to extract isU64_b / isU64_c.
    simp only [SP1Clean.ALUTypeReader.Gated.assertion,
               SP1Clean.ALUTypeReader.Gated.Assertion.Spec,
               SP1Clean.RegisterAccess.Assertion.Spec,
               SP1Clean.OperandAccess.AssertionGated.Spec,
               sub_eq_add_neg, Vector.getElem_map] at h_alu
    obtain ⟨_h_ir_bin, h_prog, _h_ra_a, h_ra_b, h_ra_c, _, _, _, _,
            h_im0, h_im1, h_im2, h_im3⟩ := h_alu
    have h_ir_ne_zero :
        (Expression.eval env input_var_is_real : ZMod p) ≠ 0 := by
      rw [h_is_real]; exact one_ne_zero
    have h_isU64_b : Word.isU64 input_adapter_op_b_memory_prev_value :=
      (h_ra_b.resolve_left h_ir_ne_zero).2.2
    have h_isU64_c : Word.isU64 input_adapter_op_c_memory_prev_value := by
      have hp : 2 ^ 17 < p := Fact.out
      have h_trusted_one :
          (Expression.eval env input_var_adapter_cols_is_trusted : ZMod p) = 1 := by
        change Expression.eval env input_var_adapter_cols_is_trusted = _ at _h_trusted
        rw [_h_trusted, h_is_real]
      have h_prog' :=
        h_prog.resolve_left (by simp [h_trusted_one])
      obtain ⟨_h_trusted2, _h_op_a_lt, _h_op_b_lt, h_op_c_lt, _, _, _h_imm_b_bin,
              h_imm_c_bin, _⟩ := h_prog'
      obtain ⟨h_oc0_lt, h_oc1_lt, h_oc2_lt, h_oc3_lt⟩ := h_op_c_lt
      by_cases h_imm_c : (Expression.eval env input_adapter_imm_c : ZMod p) = 0
      · have h_ir_imm_ne_zero :
            (Expression.eval env input_var_is_real : ZMod p)
              + -(Expression.eval env input_adapter_imm_c : ZMod p) ≠ 0 := by
          rw [h_is_real, h_imm_c]; simp
        exact (h_ra_c.resolve_left h_ir_imm_ne_zero).2.2
      · have h_imm_c_one : input_adapter_imm_c = (1 : ZMod p) := by
          rcases h_imm_c_bin with h | h
          · exact absurd (by simpa using h) h_imm_c
          · simpa using h
        have h_pv0 : input_adapter_op_c_memory_prev_value[0] = input_adapter_op_c[0] := by
          rw [h_imm_c_one, one_mul] at h_im0; linear_combination h_im0
        have h_pv1 : input_adapter_op_c_memory_prev_value[1] = input_adapter_op_c[1] := by
          rw [h_imm_c_one, one_mul] at h_im1; linear_combination h_im1
        have h_pv2 : input_adapter_op_c_memory_prev_value[2] = input_adapter_op_c[2] := by
          rw [h_imm_c_one, one_mul] at h_im2; linear_combination h_im2
        have h_pv3 : input_adapter_op_c_memory_prev_value[3] = input_adapter_op_c[3] := by
          rw [h_imm_c_one, one_mul] at h_im3; linear_combination h_im3
        have h_65536_val : (65536 : ZMod p).val = 65536 := by
          rw [show (65536 : ZMod p) = ((65536 : ℕ) : ZMod p) from by push_cast; rfl]
          rw [ZMod.val_natCast_of_lt (by omega)]
        have h_oc0_val_lt : input_adapter_op_c[0].val < 65536 := by
          have : input_adapter_op_c[0].val < (65536 : ZMod p).val := h_oc0_lt
          omega
        have h_oc1_val_lt : input_adapter_op_c[1].val < 65536 := by
          have : input_adapter_op_c[1].val < (65536 : ZMod p).val := h_oc1_lt
          omega
        have h_oc2_val_lt : input_adapter_op_c[2].val < 65536 := by
          have : input_adapter_op_c[2].val < (65536 : ZMod p).val := h_oc2_lt
          omega
        have h_oc3_val_lt : input_adapter_op_c[3].val < 65536 := by
          have : input_adapter_op_c[3].val < (65536 : ZMod p).val := h_oc3_lt
          omega
        apply Word.isU64_of_cases
        · simp only [h_pv0]; exact (by simpa using h_oc0_val_lt)
        · simp only [h_pv1]; exact (by simpa using h_oc1_val_lt)
        · simp only [h_pv2]; exact (by simpa using h_oc2_val_lt)
        · simp only [h_pv3]; exact (by simpa using h_oc3_val_lt)
    -- Use the bidirectional bridge's forward direction.
    exact (SP1Clean.Addw.addwOp_spec_iff_rv64_addw h_isU64_b h_isU64_c).mp h_addwop

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22⟩ := h_input
  subst_eqs
  obtain ⟨_h_trusted, h_is_real⟩ := h_assumptions
  obtain ⟨h_cpu, h_alu, h_op_a_0, h_sem⟩ := h_spec
  unfold id at *
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  change (Expression.eval env input_var_is_real : ZMod p) = 1 at h_is_real
  -- Save the original h_alu (Gated.Assertion.Spec form) for the final refine.
  have h_alu_orig := h_alu
  -- Re-derive isU64 of op_b / op_c from h_alu (unfolded form).
  simp only [SP1Clean.ALUTypeReader.Gated.assertion,
             SP1Clean.ALUTypeReader.Gated.Assertion.Spec,
             SP1Clean.RegisterAccess.Assertion.Spec,
             SP1Clean.OperandAccess.AssertionGated.Spec,
             sub_eq_add_neg, Vector.getElem_map] at h_alu
  obtain ⟨_h_ir_bin, h_prog, _h_ra_a, h_ra_b, h_ra_c, _, _, _, _,
          h_im0, h_im1, h_im2, h_im3⟩ := h_alu
  have h_ir_ne_zero :
      (Expression.eval env input_var_is_real : ZMod p) ≠ 0 := by
    rw [h_is_real]; exact one_ne_zero
  have h_isU64_b : Word.isU64 input_adapter_op_b_memory_prev_value :=
    (h_ra_b.resolve_left h_ir_ne_zero).2.2
  have h_isU64_c : Word.isU64 input_adapter_op_c_memory_prev_value := by
    have hp : 2 ^ 17 < p := Fact.out
    have h_trusted_one :
        (Expression.eval env input_var_adapter_cols_is_trusted : ZMod p) = 1 := by
      change Expression.eval env input_var_adapter_cols_is_trusted = _ at _h_trusted
      rw [_h_trusted, h_is_real]
    have h_prog' :=
      h_prog.resolve_left (by simp [h_trusted_one])
    obtain ⟨_h_trusted2, _h_op_a_lt, _h_op_b_lt, h_op_c_lt, _, _, _h_imm_b_bin,
            h_imm_c_bin, _⟩ := h_prog'
    obtain ⟨h_oc0_lt, h_oc1_lt, h_oc2_lt, h_oc3_lt⟩ := h_op_c_lt
    by_cases h_imm_c : (Expression.eval env input_adapter_imm_c : ZMod p) = 0
    · have h_ir_imm_ne_zero :
          (Expression.eval env input_var_is_real : ZMod p)
            + -(Expression.eval env input_adapter_imm_c : ZMod p) ≠ 0 := by
        rw [h_is_real, h_imm_c]; simp
      exact (h_ra_c.resolve_left h_ir_imm_ne_zero).2.2
    · have h_imm_c_one : input_adapter_imm_c = (1 : ZMod p) := by
        rcases h_imm_c_bin with h | h
        · exact absurd (by simpa using h) h_imm_c
        · simpa using h
      have h_pv0 : input_adapter_op_c_memory_prev_value[0] = input_adapter_op_c[0] := by
        rw [h_imm_c_one, one_mul] at h_im0; linear_combination h_im0
      have h_pv1 : input_adapter_op_c_memory_prev_value[1] = input_adapter_op_c[1] := by
        rw [h_imm_c_one, one_mul] at h_im1; linear_combination h_im1
      have h_pv2 : input_adapter_op_c_memory_prev_value[2] = input_adapter_op_c[2] := by
        rw [h_imm_c_one, one_mul] at h_im2; linear_combination h_im2
      have h_pv3 : input_adapter_op_c_memory_prev_value[3] = input_adapter_op_c[3] := by
        rw [h_imm_c_one, one_mul] at h_im3; linear_combination h_im3
      have h_65536_val : (65536 : ZMod p).val = 65536 := by
        rw [show (65536 : ZMod p) = ((65536 : ℕ) : ZMod p) from by push_cast; rfl]
        rw [ZMod.val_natCast_of_lt (by omega)]
      have h_oc0_val_lt : input_adapter_op_c[0].val < 65536 := by
        have : input_adapter_op_c[0].val < (65536 : ZMod p).val := h_oc0_lt
        omega
      have h_oc1_val_lt : input_adapter_op_c[1].val < 65536 := by
        have : input_adapter_op_c[1].val < (65536 : ZMod p).val := h_oc1_lt
        omega
      have h_oc2_val_lt : input_adapter_op_c[2].val < 65536 := by
        have : input_adapter_op_c[2].val < (65536 : ZMod p).val := h_oc2_lt
        omega
      have h_oc3_val_lt : input_adapter_op_c[3].val < 65536 := by
        have : input_adapter_op_c[3].val < (65536 : ZMod p).val := h_oc3_lt
        omega
      apply Word.isU64_of_cases
      · simp only [h_pv0]; exact (by simpa using h_oc0_val_lt)
      · simp only [h_pv1]; exact (by simpa using h_oc1_val_lt)
      · simp only [h_pv2]; exact (by simpa using h_oc2_val_lt)
      · simp only [h_pv3]; exact (by simpa using h_oc3_val_lt)
  -- Reverse bridge: h_sem h_is_real gives (isU64 ∧ BV64 = RV64.addw); recover
  -- AddwOp.Spec.
  have h_pair := h_sem h_is_real
  have h_addwop : SP1Clean.AddwOp.Spec
      ⟨input_adapter_op_b_memory_prev_value,
       input_adapter_op_c_memory_prev_value,
       input_var_addw_value.map (Expression.eval env.toEnvironment),
       Expression.eval env.toEnvironment input_var_addw_msb⟩ :=
    (SP1Clean.Addw.addwOp_spec_iff_rv64_addw h_isU64_b h_isU64_c).mpr h_pair
  refine ⟨⟨trivial, h_addwop⟩, ⟨trivial, h_cpu⟩, ⟨trivial, ?_⟩, h_op_a_0⟩
  simpa [SP1Clean.ALUTypeReader.Gated.assertion,
         SP1Clean.ALUTypeReader.Gated.Assertion.Spec, sub_eq_add_neg,
         Vector.getElem_map] using h_alu_orig

end Assertion

/-- The full Clean `FormalAssertion` for `AddwChip`. -/
def assertion : FormalAssertion (ZMod p) AddwCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.Addw
