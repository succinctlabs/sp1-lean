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
1:1 via flag-threaded `Gated` sub-circuits: one `AddOp.assertion` +
one `CPUState.Gated.assertion` (binary gate + state-bus + byte-opcode,
all gated by `is_real`) + one `RTypeReader.Gated.assertion` (binary gate
+ program-bus + 3 register accesses + op_a_0 masked gates, gated by
`is_real`/`is_trusted`) + chip-level `op_a_0 = 0` gate. The free
`is_real * (is_real - 1) === 0` gate now lives inside both Gated
sub-circuits' first conjuncts (redundant but propositionally fine). -/
@[reducible]
def main (cols : Var AddCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩,
       adapter,
       op_a_write_value, is_real, adapter_cols⟩ := cols
  SP1Clean.AddOp.assertion
    (⟨adapter.op_b_memory.prev_value, adapter.op_c_memory.prev_value,
      op_a_write_value, is_real⟩ :
      Var SP1Clean.AddOp.Inputs (ZMod p))
  SP1Clean.CPUState.Gated.assertion
    (⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩,
       #v[pc[0] + 4, pc[1], pc[2]], 8, is_real⟩ :
      Var SP1Clean.CPUState.Gated.Inputs (ZMod p))
  SP1Clean.RTypeReader.Gated.assertion
    (⟨clk_high, clk_0_16 + clk_16_24 * 65536, 0, pc, op_a_write_value, adapter,
       is_real, adapter_cols.is_trusted⟩ :
      Var SP1Clean.RTypeReader.Gated.Inputs (ZMod p))
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
round-trip.

The `is_real = 1` precondition restricts the FormalAssertion to
non-padding rows: completeness reconstructs `AddOp.RawSpec` for the
sub-circuit witness via `AddOp.iff_sp1_full` (which needs the BitVec
identity from FormalSpec's `is_real = 1 → ...` conjunct), so the chip
contract is only meaningful on real rows. Trace-soundness drivers
discharge `is_real = 1` per row before invoking `Add.assertion`. -/
def Assumptions (cols : AddCols (ZMod p)) : Prop :=
  cols.adapter_cols.is_trusted = cols.is_real ∧ cols.is_real = 1

/-- The unified chip Spec is defined in `Cols.lean` (`SP1Clean.Add.FormalSpec`)
so `Lemmas.lean` can reference it. Re-exported here for the
`FormalAssertion` glue. -/
abbrev FormalSpec := @SP1Clean.Add.FormalSpec p

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e_adapter, e_oawv, e_is_real, e_ac⟩ := h_input
  subst_eqs
  obtain ⟨_h_trusted, h_is_real⟩ := h_assumptions
  obtain ⟨h_addop_sub, h_cpu_sub, h_rtr_sub, h_op_a_0⟩ := h_holds
  unfold id at *
  have h_cpu := h_cpu_sub trivial
  have h_rtr := h_rtr_sub trivial
  -- Discharge AddOp.assertion's new Assumptions from the chip-level
  -- `is_real = 1` + the per-operand `Word.isU64` bounds available inside
  -- `RTypeReader.Gated.Spec`'s 4th/5th `RegisterAccess.Spec` sub-conjuncts.
  change (Expression.eval env input_var_is_real : ZMod p) = 1 at h_is_real
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h_ir_ne_zero :
      (Expression.eval env input_var_is_real : ZMod p) ≠ 0 := by
    rw [h_is_real]; exact one_ne_zero
  have h_isU64_b : Word.isU64 input_adapter_op_b_memory_prev_value :=
    (h_rtr.2.2.2.1.resolve_left h_ir_ne_zero).2.2
  have h_isU64_c : Word.isU64 input_adapter_op_c_memory_prev_value :=
    (h_rtr.2.2.2.2.1.resolve_left h_ir_ne_zero).2.2
  have h_addop := h_addop_sub
    ⟨Or.inr h_is_real, fun _ => ⟨h_isU64_b, h_isU64_c⟩⟩
  refine ⟨h_cpu, h_rtr, h_op_a_0, ?_⟩
  -- AddOp.Spec under `is_real = 1` gives `(isU64 result ∧ result = a + b)`
  -- directly. The chip-level FormalSpec wants `RV64.add op_c op_b` which is
  -- `op_b + op_c` definitionally — exactly what AddOp gives us since the
  -- chip passes `Inputs.a := op_b, Inputs.b := op_c`.
  intro h_is_real_eq
  have ⟨h_isU64_v, h_bv⟩ := h_addop h_is_real_eq
  refine ⟨h_isU64_v, ?_⟩
  simp only [RV64.add]
  exact h_bv

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e_adapter, e_oawv, e_is_real, e_ac⟩ := h_input
  subst_eqs
  obtain ⟨_h_trusted, h_is_real⟩ := h_assumptions
  obtain ⟨h_cpu, h_rtr, h_op_a_0, h_sem⟩ := h_spec
  unfold id at *
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  change (Expression.eval env input_var_is_real : ZMod p) = 1 at h_is_real
  have h_ir_ne_zero :
      (Expression.eval env input_var_is_real : ZMod p) ≠ 0 := by
    rw [h_is_real]; exact one_ne_zero
  have h_isU64_b : Word.isU64 input_adapter_op_b_memory_prev_value :=
    (h_rtr.2.2.2.1.resolve_left h_ir_ne_zero).2.2
  have h_isU64_c : Word.isU64 input_adapter_op_c_memory_prev_value :=
    (h_rtr.2.2.2.2.1.resolve_left h_ir_ne_zero).2.2
  -- Discharge AddOp.assertion's Assumptions + Spec directly from the
  -- chip's `h_sem` semantic conjunct and the operand bounds.
  refine ⟨⟨⟨Or.inr h_is_real, fun _ => ⟨h_isU64_b, h_isU64_c⟩⟩, ?_⟩,
          ⟨trivial, h_cpu⟩, ⟨trivial, h_rtr⟩, h_op_a_0⟩
  intro h_is_real_eq
  have ⟨h_isU64_v, h_bv⟩ := h_sem h_is_real_eq
  refine ⟨h_isU64_v, ?_⟩
  simp only [RV64.add] at h_bv
  exact h_bv

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
