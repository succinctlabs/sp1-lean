import SP1Clean.AddwChip.Circuit
import SP1Chips.Soundness

/-! # External Sail-equivalence bridge for `AddwChip`

AddwChip bundles two RV64IM variants — ADDW (R-type) and ADDIW (I-type) —
behind the shared `imm_c` flag at `cols.adapter.imm_c`. This file provides
two on-demand Sail-equivalence bridges, one per variant. Both consume a
cols-level `TraceSpec` (the conjunction of `AddwOp.Spec`, `cpuStateSpec`,
`aluTypeReaderSpec`, and the two trailing scalar gates) and produce the
monadic Sail equivalence to `_root_.Addw.spec_addw` / `_root_.Addiw.spec_addiw`.

`TraceSpec` is strictly stronger than `FormalSpec` from `Circuit.lean`:
- `FormalSpec` carries only the byte/program-lookup-derivable subset
  (CPUState + ProgramTable + 3 OperandAccess + 2 scalar gates).
- `TraceSpec` additionally requires `AddwOp.Spec` (the carry-chain
  consequence) and the full `aluTypeReaderSpec` (which includes the
  imm_c-conditional clauses).

The architectural split — Circuit.lean for the lookup-derivable
FormalAssertion, SailBridge.lean for the full Sail bridge — mirrors the
flat-file pattern in `SP1Clean/AddwChip.lean`.

The bridges compose:
- `fromMain_toMain` (round-trip on the cols struct under the UserMode
  TrustMode marker),
- `allHold_iff_structural` (reconstruct `(Addw.constraints (toMain cols)).allHold`
  from the structural conjuncts of `TraceSpec`),
- `_root_.Addw.correct_addw` or `_root_.Addiw.correct_addw` (the
  Main-level Sail-equivalence proof). -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Addw

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Cols-level full trace spec for AddwChip. Mirrors the flat-file
`SP1Clean.Addw.TraceSpec` shape: structural conjunction of the carry-chain,
CPU-state byte bounds, full ALU-type reader spec, and 2 trailing gates. -/
def TraceSpec (cols : AddwCols (ZMod p)) : Prop :=
  SP1Clean.AddwOp.Spec
      cols.adapter.op_b_memory.prev_value cols.adapter.op_c_memory.prev_value
      { value := cols.addw_value, msb := { msb := cols.addw_msb } } ∧
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ALUTypeReader.aluTypeReaderSpec
      (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 19 cols.state.pc
      #v[cols.addw_value[0], cols.addw_value[1],
         cols.addw_msb * 65535, cols.addw_msb * 65535]
      cols.adapter ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.adapter.op_a_0 = 0

/-- Common bridge: reconstruct `(_root_.Addw.constraints (toMain cols)).allHold`
from a cols-level `TraceSpec` and the UserMode TrustMode marker. -/
private theorem allHold_of_traceSpec
    (cols : AddwCols (ZMod p))
    (h_spec : TraceSpec cols)
    (h_assumptions : cols.adapter_cols.is_trusted = cols.is_real)
    (h_is_real : cols.is_real = 1) :
    (_root_.Addw.constraints (toMain cols)).allHold := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h_addwop, h_cpu, h_alu, h_isreal, h_op_a_0⟩ := h_spec
  have h_round_trip := fromMain_toMain cols h_assumptions
  have h_isreal' : (toMain cols)[35] = 1 := h_is_real
  -- Re-state each cols-level Spec hypothesis through `fromMain (toMain cols)`
  -- (which equals `cols` by h_round_trip). The `(fromMain (toMain cols)).X`
  -- projections then unfold to the matching `(toMain cols)[k]` / `#v[…]` forms.
  have h_addwop' : SP1Clean.AddwOp.Spec
        (fromMain (toMain cols)).adapter.op_b_memory.prev_value
        (fromMain (toMain cols)).adapter.op_c_memory.prev_value
        { value := (fromMain (toMain cols)).addw_value,
          msb := { msb := (fromMain (toMain cols)).addw_msb } } := by
    rw [h_round_trip]; exact h_addwop
  have h_alu' : SP1Clean.ALUTypeReader.aluTypeReaderSpec
        ((fromMain (toMain cols)).state.clk_0_16 +
            (fromMain (toMain cols)).state.clk_16_24 * 65536) 19
        (fromMain (toMain cols)).state.pc
        #v[(fromMain (toMain cols)).addw_value[0],
           (fromMain (toMain cols)).addw_value[1],
           (fromMain (toMain cols)).addw_msb * 65535,
           (fromMain (toMain cols)).addw_msb * 65535]
        (fromMain (toMain cols)).adapter := by
    rw [h_round_trip]; exact h_alu
  rw [allHold_iff_structural (toMain cols) h_isreal']
  refine ⟨h_addwop', h_cpu, h_alu', ?_, h_op_a_0⟩
  change cols.is_real * (cols.is_real - 1) = 0
  linear_combination h_isreal

/-- Cols-level Sail bridge for ADDW (R-type, `imm_c = 0`). -/
theorem sail_correct_addw_of_traceSpec
    (cols : AddwCols (ZMod p))
    (h_spec : TraceSpec cols)
    (h_assumptions : cols.adapter_cols.is_trusted = cols.is_real)
    (h_is_real : cols.is_real = 1)
    (h_is_addw : cols.adapter.imm_c = 0)
    (s : SailState)
    (h_init : addwInitialState_cols cols s) :
    (sp1_addw_cols cols).run s =
      (_root_.Addw.spec_addw (.Regidx (sp1_op_c_cols cols))
                             (.Regidx (sp1_op_b_cols cols))
                             (.Regidx (sp1_op_a_cols cols))).run s := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h_round_trip := fromMain_toMain cols h_assumptions
  have h_state := h_init (toMain cols) h_round_trip
  have h_allHold := allHold_of_traceSpec cols h_spec h_assumptions h_is_real
  have h_isreal' : (toMain cols)[35] = 1 := h_is_real
  have h_is_addw' : (toMain cols)[31] = 0 := h_is_addw
  -- Apply Main-level `Addw.correct_addw`; the result reads `sp1_X (toMain cols)`,
  -- which is definitionally `sp1_X_cols cols` for each helper.
  exact (_root_.Addw.correct_addw (toMain cols) s h_allHold h_isreal' h_is_addw'
      h_state).symm

/-- Cols-level Sail bridge for ADDIW (I-type, `imm_c = 1`). -/
theorem sail_correct_addiw_of_traceSpec
    (cols : AddwCols (ZMod p))
    (h_spec : TraceSpec cols)
    (h_assumptions : cols.adapter_cols.is_trusted = cols.is_real)
    (h_is_real : cols.is_real = 1)
    (h_is_addiw : cols.adapter.imm_c = 1)
    (s : SailState)
    (h_init : addwInitialState_cols cols s) :
    (sp1_addw_cols cols).run s =
      (_root_.Addiw.spec_addiw (sp1_op_c_imm_cols cols)
                               (.Regidx (sp1_op_b_cols cols))
                               (.Regidx (sp1_op_a_cols cols))).run s := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h_round_trip := fromMain_toMain cols h_assumptions
  have h_state := h_init (toMain cols) h_round_trip
  have h_allHold := allHold_of_traceSpec cols h_spec h_assumptions h_is_real
  have h_isreal' : (toMain cols)[35] = 1 := h_is_real
  have h_is_addiw' : (toMain cols)[31] = 1 := h_is_addiw
  exact (_root_.Addiw.correct_addw (toMain cols) s h_allHold h_isreal' h_is_addiw'
      h_state).symm

end SP1Clean.Addw
