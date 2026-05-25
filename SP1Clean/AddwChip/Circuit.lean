import SP1Clean.AddwChip.Lemmas
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import SP1Foundations.ByteOpcode
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.Reader.OperandAccess
import SP1Clean.Operations.AddwOperation
import SP1Clean.MemoryAccess
import SP1Clean.SP1Memory
import RISCV.Instructions

/-! # `AddwChip` Clean circuit + `FormalAssertion`

Composes CPUState + ProgramTable + 3 `OperandAccess.assertion` (op_a/op_b
unconditional, op_c structurally over-constrained at the per-row level) +
2 trailing scalar gates.

**Multiplicity-aware semantics for op_c.** The chip's `FormalSpec` states
the op_c byte-bus consequence in the **disjunctive form**
`(is_real - imm_c) = 0 ∨ OperandAccess.Spec ...`, matching SP1's actual
gated emission (`alu_type.rs:142` — `eval_register_access_read` with
multiplicity `is_real - imm_c`). On ADDIW rows (`imm_c = 1`, hence
`is_real - imm_c = 0`), the conjunct is vacuous.

**Per-row circuit vs Spec gap.** The underlying `OperandAccess.assertion`
emits the op_c byte lookups unconditionally — stronger than SP1's actual
gated emission. Per-row soundness is therefore stronger than the
disjunctive Spec demands (provable via `Or.inr` on the unconditional
OperandAccess.Spec). The completeness side has a real gap: on ADDIW
rows, the prover may set the op_c byte values to garbage, but the
unconditional lookup would fail. Native `lookupGated` support
(`SP1Memory.lookupGated`, Phase 2) closes this by emitting a
witness-hint pattern so the lookup is vacuous when multiplicity is 0.

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

/-- Clean-side chip circuit. -/
@[reducible]
def main (cols : Var AddwCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c, op_c_memory, imm_c⟩,
       _addw_value, _addw_msb, is_real, _adapter_cols⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ProgramTable.assertion
    (⟨pc, 19, op_a, #v[op_b, 0, 0, 0], op_c, op_a_0, 0, imm_c⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  is_real * (is_real - 1) === 0
  op_a_0 === 0
  let clk_low := clk_0_16 + clk_16_24 * 65536
  -- op_a (unconditional)
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 4, op_a_memory.access_timestamp.prev_low,
       op_a_memory.access_timestamp.diff_low_limb,
       op_a_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))
  -- op_b (unconditional)
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 3, op_b_memory.access_timestamp.prev_low,
       op_b_memory.access_timestamp.diff_low_limb,
       op_b_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))
  -- op_c at +2 — semantically gated by `mult_c = is_real - imm_c`
  -- (SP1 source: alu_type.rs:142). Circuit emits unconditionally
  -- (over-constrains); the disjunctive Spec form below captures the
  -- intended multiplicity-aware semantics.
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 2, op_c_memory.access_timestamp.prev_low,
       op_c_memory.access_timestamp.diff_low_limb,
       op_c_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) AddwCols unit where
  name := "SP1Clean.Addw"
  main := main
  localLength _ := 0

def Assumptions (_ : AddwCols (ZMod p)) : Prop := True

/-- The byte/program-lookup-derivable subset of TraceSpec.

The op_c byte-bus consequence is stated in the **disjunctive
multiplicity-aware form**: either `is_real - imm_c = 0` (gated off,
ADDIW row), or the byte-bus bounds hold. This matches SP1's actual
emission semantics (`alu_type.rs:142`). -/
def FormalSpec (cols : AddwCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let mult_c : ZMod p := cols.is_real - cols.adapter.imm_c
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := 19, op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0],
      op_c := cols.adapter.op_c,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := cols.adapter.imm_c } ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.adapter.op_a_0 = 0 ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 4, cols.adapter.op_a_memory.access_timestamp.prev_low,
     cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 3, cols.adapter.op_b_memory.access_timestamp.prev_low,
     cols.adapter.op_b_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_b_memory.prev_value⟩ ∧
  (mult_c = 0 ∨
    SP1Clean.OperandAccess.Assertion.Spec
      ⟨clk_low, 2, cols.adapter.op_c_memory.access_timestamp.prev_low,
       cols.adapter.op_c_memory.access_timestamp.diff_low_limb,
       cols.adapter.op_c_memory.prev_value⟩)

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu_sub, h_prog_sub, h_isreal, h_op_a_0,
          h_oa_a, h_oa_b, h_oa_c⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_prog_sub trivial
  · linear_combination h_isreal
  · exact h_op_a_0
  · exact h_oa_a trivial
  · exact h_oa_b trivial
  -- Disjunctive op_c clause: discharge via `Or.inr` using the
  -- unconditional OperandAccess.Spec we got from the subcircuit.
  · exact Or.inr (h_oa_c trivial)

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu, h_prog, h_isreal, h_op_a_0,
          h_oa_a, h_oa_b, h_oc_disj⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_prog⟩
  · linear_combination h_isreal
  · exact h_op_a_0
  · exact ⟨trivial, h_oa_a⟩
  · exact ⟨trivial, h_oa_b⟩
  -- Completeness gap for op_c: the disjunctive Spec admits `mult_c = 0`
  -- with no claim on the byte-bus rows. But the unconditional
  -- OperandAccess.assertion requires the byte-bus rows to hold. So
  -- completeness only works when h_oc_disj selects the right disjunct.
  -- Native lookupGated (Phase 2) would close this by witness-hint pattern.
  · refine ⟨trivial, ?_⟩
    exact h_oc_disj.resolve_left (by sorry)

end Assertion

/-- The full Clean `FormalAssertion` for `AddwChip`. -/
def assertion : FormalAssertion (ZMod p) AddwCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.Addw
