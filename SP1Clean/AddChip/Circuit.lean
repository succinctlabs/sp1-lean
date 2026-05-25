import SP1Clean.AddChip.Lemmas
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import SP1Foundations.ByteOpcode
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.Reader.OperandAccess
import SP1Clean.MemoryAccess
import RISCV.Instructions

/-! # `AddChip` Clean circuit + `FormalAssertion`

Wraps the chip-level constraint surface into a single Clean `FormalAssertion`
whose `Spec` is the unified semantic-and-structural contract:
- `AddOperation` arithmetic `Spec` (carry chain).
- CPU-state byte bounds (`cpuStateSpec`).
- Full R-type reader spec (`rtypeReaderSpec` — program + memory + bounds).
- Two trailing scalar gates (`is_real` binary, `op_a_0 = 0`).
- Pure BitVec `RV64.add` semantic (conditional on `is_real = 1`).

`Assertion.main` composes three subcircuits — `AddOp.assertion`,
`CPUState.assertion`, `RTypeReader.assertion` (the last itself wrapping
`ProgramTable.assertion` + 3 `OperandAccess.assertion` calls) — mirroring
`SP1Chips/Add/Constraints.lean`'s single `RTypeReader.constraints` call
and the upstream Rust `AddChip::eval`'s `RTypeReader::eval` invocation
1:1.

The per-row Sail-monadic equivalence to `_root_.Add.spec_add` is *not*
inside `FormalSpec`; it's derived externally via
`SP1Clean.AddChip.SailBridge.sail_correct_of_formalSpec`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Add

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

/-- Clean-side chip circuit. Mirrors SP1 Rust's `AddChip::eval(builder, cols)`
1:1: one `AddOp.assertion` + one `CPUState.assertion` + one
`RTypeReader.assertion` + two scalar gates. -/
@[reducible]
def main (cols : Var AddCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩,
       adapter,
       op_a_write_value, is_real, _adapter_cols⟩ := cols
  SP1Clean.AddOp.assertion
    (⟨adapter.op_b_memory.prev_value, adapter.op_c_memory.prev_value,
      op_a_write_value⟩ :
      Var SP1Clean.AddOp.Inputs (ZMod p))
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.RTypeReader.assertion
    (⟨clk_high, clk_0_16 + clk_16_24 * 65536, 0, pc, op_a_write_value, adapter⟩ :
      Var SP1Clean.RTypeReader.Inputs (ZMod p))
  is_real * (is_real - 1) === 0
  adapter.op_a_0 === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) AddCols unit where
  name := "SP1Clean.Add"
  main := main
  -- Computed from main; RTypeReader contributes 72 (3 assertionGated × 24).
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

/-- The chip is the `UserMode` variant (`M = UserMode` in upstream Rust),
so its `adapter_cols.is_trusted` payload is structurally equal to `is_real`
(both alias `Main[32]` in the constraint compiler's emission). This is a
type-level / TrustMode-marker fact that the circuit doesn't enforce; it's
needed by `fromMain_toMain` (`Lemmas.lean`) for the cols→Main→cols
round-trip. -/
def Assumptions (cols : AddCols (ZMod p)) : Prop :=
  cols.adapter_cols.is_trusted = cols.is_real

/-- The unified chip Spec is defined in `Cols.lean` (`SP1Clean.Add.FormalSpec`)
so `Lemmas.lean` can reference it. Re-exported here for the
`FormalAssertion` glue. -/
abbrev FormalSpec := @SP1Clean.Add.FormalSpec p

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e_adapter, e_oawv, e_is_real, e_ac⟩ := h_input
  subst_eqs
  obtain ⟨h_addop_sub, h_cpu_sub, h_rtr_sub, h_isreal, h_op_a_0⟩ := h_holds
  unfold id at *
  have h_addop := h_addop_sub trivial
  have h_cpu := h_cpu_sub trivial
  have h_rtr := h_rtr_sub trivial
  -- Rebind the explicit eval'd-form struct under the name `cols` so the
  -- helper-cols functions and `addInitialState_cols` references in the
  -- residual BitVec clause unfold against a single named term rather than
  -- a giant inlined struct in every position.
  set cols : AddCols (ZMod p) :=
    { state :=
        { clk_high := Expression.eval env input_var_state_clk_high,
          clk_16_24 := Expression.eval env input_var_state_clk_16_24,
          clk_0_16 := Expression.eval env input_var_state_clk_0_16,
          pc := Vector.map (Expression.eval env) input_var_state_pc },
      adapter :=
        { op_a := input_adapter_op_a,
          op_a_memory :=
            { prev_value := input_adapter_op_a_memory_prev_value,
              access_timestamp :=
                { prev_low := input_adapter_op_a_memory_access_timestamp_prev_low,
                  diff_low_limb := input_adapter_op_a_memory_access_timestamp_diff_low_limb } },
          op_a_0 := input_adapter_op_a_0, op_b := input_adapter_op_b,
          op_b_memory :=
            { prev_value := input_adapter_op_b_memory_prev_value,
              access_timestamp :=
                { prev_low := input_adapter_op_b_memory_access_timestamp_prev_low,
                  diff_low_limb := input_adapter_op_b_memory_access_timestamp_diff_low_limb } },
          op_c := input_adapter_op_c,
          op_c_memory :=
            { prev_value := input_adapter_op_c_memory_prev_value,
              access_timestamp :=
                { prev_low := input_adapter_op_c_memory_access_timestamp_prev_low,
                  diff_low_limb := input_adapter_op_c_memory_access_timestamp_diff_low_limb } } },
      op_a_write_value := Vector.map (Expression.eval env) input_var_op_a_write_value,
      is_real := Expression.eval env input_var_is_real,
      adapter_cols := { is_trusted := Expression.eval env input_var_is_real } }
    with hcols
  refine ⟨h_addop, h_cpu, h_rtr, by linear_combination h_isreal, h_op_a_0, ?_⟩
  -- BitVec `RV64.add` conjunct: discharge from `AddOp.Spec` (the carry
  -- chain) + `rtypeReaderSpec`'s isU64 bounds for op_b/op_c, via
  -- `AddOperation.spec`. No `toMain` round-trip, no monadic dispatch.
  intro _h_is_real_eq
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  -- Extract isU64_b, isU64_c from `rtypeReaderSpec`'s memory-bus tuple
  -- (positions 8.3.2 and 8.3.3) and convert from index-form to whole-Vector.
  obtain ⟨_, _, _, _, _, _, _,
          ⟨_, _, ⟨_h_isU64_a_idx, h_isU64_b_idx, h_isU64_c_idx⟩⟩, _⟩ := h_rtr
  have h_isU64_b : Word.isU64 cols.adapter.op_b_memory.prev_value :=
    (SP1Clean.RTypeReader.Assertion.isU64_iff_index_form _).mpr h_isU64_b_idx
  have h_isU64_c : Word.isU64 cols.adapter.op_c_memory.prev_value :=
    (SP1Clean.RTypeReader.Assertion.isU64_iff_index_form _).mpr h_isU64_c_idx
  -- Bridge the cols-level `AddOp.Spec` to SP1's constraint allHold form,
  -- then to the BitVec equation via `AddOperation.spec`.
  have h_allHold : (AddOperation.constraints
        cols.adapter.op_b_memory.prev_value
        cols.adapter.op_c_memory.prev_value
        { value := cols.op_a_write_value } 1).allHold :=
    (SP1Clean.AddOp.iff_sp1 _ _ _).mpr h_addop
  have ⟨_, h_bv⟩ := AddOperation.spec h_isU64_b h_isU64_c h_allHold
  -- `h_bv : op_a_write_value.toBitVec64 = op_b.toBitVec64 + op_c.toBitVec64`.
  -- Goal after `RV64.add` unfold: same RHS modulo arg order
  -- (`RV64.add v2 v1 = v1 + v2`). Close by direct substitution.
  simp only [RV64.add]
  exact h_bv

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e_adapter, e_oawv, e_is_real, e_ac⟩ := h_input
  subst_eqs
  obtain ⟨h_addop, h_cpu, h_rtr, h_isreal, h_op_a_0, _h_rv64add⟩ := h_spec
  unfold id at *
  refine ⟨⟨trivial, h_addop⟩, ⟨trivial, h_cpu⟩, ⟨trivial, h_rtr⟩,
          by linear_combination h_isreal, h_op_a_0⟩

end Assertion

/-- The full Clean `FormalAssertion` for `AddChip`. Single subcircuit
composition (`AddOp.assertion + CPUState.assertion + RTypeReader.assertion
+ 2 scalar gates`) backing one unified `Spec` whose last conjunct is the
pure BitVec `RV64.add` semantic (auditable at a glance). Per-row Sail
equivalence is derived externally via `sail_correct_of_formalSpec`
(`SailBridge.lean`). -/
def assertion : FormalAssertion (ZMod p) AddCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.Add
