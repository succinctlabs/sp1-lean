import SP1Clean.Chips.ALU.SubChip.Lemmas
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

/-! # `SubChip` Clean circuit + `FormalAssertion`

Wraps the chip-level constraint surface into a single Clean `FormalAssertion`
whose `Spec` is the unified semantic-and-structural contract:
- `SubOperation` arithmetic `Spec` (natural-form carry chain).
- CPU-state gated sub-circuit composition (binary gate + state-bus + byte
  opcode, all gated by `is_real`).
- Full R-type reader gated sub-circuit composition (binary gate +
  program-bus + 3 register accesses + op_a_0 masked gates, gated by
  `is_real`/`is_trusted`).
- `adapter.op_a_0 = 0` chip-level gate.
- Pure BitVec `RV64.sub` semantic (conditional on `is_real = 1`).

`Assertion.main` composes three sub-circuits — `SubOp.assertion`,
`CPUState.Gated.assertion`, `RTypeReader.Gated.assertion` — mirroring
`SP1Chips/Sub/Constraints.lean`'s single `RTypeReader.constraints` call
and the upstream Rust `SubChip::eval`'s `RTypeReader::eval` invocation 1:1.

The per-row Sail-monadic equivalence to `_root_.Sub.spec_sub` is *not*
inside `FormalSpec`; it's derived externally via
`SP1Clean.Sub.SailBridge.sail_correct_of_formalSpec`.

Mirrors `SP1Clean/AddChip/Circuit.lean` 1-for-1 with `AddOp` → `SubOp` and
opcode `0` → `2`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Sub

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

/-- Clean-side chip circuit. Mirrors SP1 Rust's `SubChip::eval(builder, cols)`
1:1 via flag-threaded `Gated` sub-circuits: one `SubOp.assertion` +
one `CPUState.Gated.assertion` (binary gate + state-bus + byte-opcode,
all gated by `is_real`) + one `RTypeReader.Gated.assertion` (binary gate
+ program-bus + 3 register accesses + op_a_0 masked gates, gated by
`is_real`/`is_trusted`) + chip-level `op_a_0 = 0` gate. The free
`is_real * (is_real - 1) === 0` gate now lives inside both Gated
sub-circuits' first conjuncts (redundant but propositionally fine). -/
@[reducible]
def main (cols : Var SubCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩,
       adapter,
       op_a_write_value, is_real, adapter_cols⟩ := cols
  SP1Clean.SubOp.assertion
    (⟨adapter.op_b_memory.prev_value, adapter.op_c_memory.prev_value,
      op_a_write_value, is_real⟩ :
      Var SP1Clean.SubOp.Inputs (ZMod p))
  SP1Clean.CPUState.Gated.assertion
    (⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩,
       #v[pc[0] + 4, pc[1], pc[2]], 8, is_real⟩ :
      Var SP1Clean.CPUState.Gated.Inputs (ZMod p))
  SP1Clean.RTypeReader.Gated.assertion
    (⟨clk_high, clk_0_16 + clk_16_24 * 65536, 2, pc, op_a_write_value, adapter,
       is_real, adapter_cols.is_trusted⟩ :
      Var SP1Clean.RTypeReader.Gated.Inputs (ZMod p))
  adapter.op_a_0 === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) SubCols unit where
  name := "SP1Clean.Sub"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

/-- The chip is the `UserMode` variant (`M = UserMode` in upstream Rust),
so its `adapter_cols.is_trusted` payload is structurally equal to `is_real`
(both alias `Main[32]` in the constraint compiler's emission). The
`is_real = 1` precondition restricts the FormalAssertion to non-padding
rows: completeness reconstructs `SubOp.RawSpec` for the sub-circuit
witness via `SubOperation.iff_sp1_full` (which needs the BitVec identity
from FormalSpec's `is_real = 1 → ...` conjunct), so the chip contract is
only meaningful on real rows. Trace-soundness drivers discharge
`is_real = 1` per row before invoking `Sub.assertion`. -/
def Assumptions (cols : SubCols (ZMod p)) : Prop :=
  cols.adapter_cols.is_trusted = cols.is_real ∧ cols.is_real = 1

/-- The unified chip Spec is defined in `Cols.lean`
(`SP1Clean.Sub.FormalSpec`). -/
abbrev FormalSpec := @SP1Clean.Sub.FormalSpec p

/-- Soundness collapses to a single application of the structural
mirror lemma `formalSpec_of_subcircuit_specs` (`Lemmas.lean`) once
`circuit_proof_start` peels back the Clean elaboration plumbing and the
`h_input` / `h_assumptions` / `h_holds` destructure surfaces the four
sub-circuit witnesses (`SubOp` Spec implication, `CPUState.Gated` Spec,
`RTypeReader.Gated` Spec, scalar `op_a_0 = 0` gate). All the
sub-circuit composition logic — including the `Word.isU64 op_b/op_c`
extraction from `h_rtr` needed to discharge `SubOp.Assumptions` — lives
inside the named lemma. -/
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e_adapter, e_oawv, e_is_real, e_ac⟩ := h_input
  subst_eqs
  obtain ⟨_h_trusted, h_is_real⟩ := h_assumptions
  obtain ⟨h_subop_sub, h_cpu_sub, h_rtr_sub, h_op_a_0⟩ := h_holds
  unfold id at *
  exact formalSpec_of_subcircuit_specs _ h_is_real
    h_subop_sub (h_cpu_sub trivial) (h_rtr_sub trivial) h_op_a_0

/-- Completeness peels `h_spec` (= `FormalSpec input`) via
`subcircuit_specs_of_formalSpec` into the four sub-circuit `Spec`s, then
re-wraps each as the `(Assumptions, Spec)` pair the corresponding
`FormalAssertion.completeness` expects. The `Word.isU64 op_b/op_c`
bounds needed for `SubOp.Assumptions` come from
`isU64_operands_of_spec`. -/
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e_adapter, e_oawv, e_is_real, e_ac⟩ := h_input
  subst_eqs
  obtain ⟨_h_trusted, h_is_real⟩ := h_assumptions
  unfold id at *
  obtain ⟨h_subop, h_cpu, h_rtr, h_op_a_0⟩ :=
    subcircuit_specs_of_formalSpec _ h_is_real h_spec
  obtain ⟨h_isU64_b, h_isU64_c⟩ :=
    SP1Clean.RTypeReader.Gated.Assertion.isU64_operands_of_spec h_is_real h_rtr
  exact ⟨⟨⟨Or.inr h_is_real, fun _ => ⟨h_isU64_b, h_isU64_c⟩⟩, h_subop⟩,
         ⟨trivial, h_cpu⟩, ⟨trivial, h_rtr⟩, h_op_a_0⟩

end Assertion

/-- The full Clean `FormalAssertion` for `SubChip`. Single subcircuit
composition (`SubOp.assertion + CPUState.Gated.assertion +
RTypeReader.Gated.assertion + 1 scalar gate`) backing one unified `Spec`
whose last conjunct is the pure BitVec `RV64.sub` semantic. Per-row Sail
equivalence is derived externally via `sail_correct_of_formalSpec`
(`SailBridge.lean`). -/
def assertion : FormalAssertion (ZMod p) SubCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.Sub
