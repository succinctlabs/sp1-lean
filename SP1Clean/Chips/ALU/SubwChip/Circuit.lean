import SP1Clean.Chips.ALU.SubwChip.Lemmas
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import SP1Foundations.ByteOpcode
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.Reader.OperandAccess
import SP1Clean.Reader.RTypeReader
import SP1Clean.Operations.SubwOperation
import SP1Clean.MemoryAccess
import RISCV.Instructions

/-! # `SubwChip` Clean circuit + `FormalAssertion`

Composes `SubwOp.assertion` + `CPUState.Gated.assertion` +
`RTypeReader.Gated.assertion` (opcode 20 = SUBW) + chip-level
`op_a_0 = 0` gate. Mirrors `SP1Clean/SubChip/Circuit.lean` for the
single-variant R-type pattern but with the W-style result shape
(`subw_value` + `subw_msb` sign extension). The free
`is_real * (is_real - 1) === 0` gate now lives inside both Gated
sub-circuits' first conjuncts. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Subw

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

/-- Clean-side chip circuit. Mirrors SP1 Rust's `SubwChip::eval(builder, cols)`
1:1 via flag-threaded `Gated` sub-circuits: one `SubwOp.assertionGated`
(multiplicity-gated 32-bit borrow chain + sign-extension MSB) + one
`CPUState.Gated.assertion` (binary gate + state-bus + byte-opcode, all
gated by `is_real`) + one `RTypeReader.Gated.assertion` (opcode 20,
binary gate + program-bus + 3 register accesses + op_a_0 masked gates,
gated by `is_real`/`is_trusted`) + chip-level `op_a_0 = 0` gate. The
sign-extended 4-limb word fed into RTypeReader is
`[subw_value[0], subw_value[1], subw_msb * 65535, subw_msb * 65535]`. -/
@[reducible]
def main (cols : Var SubwCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩, adapter,
       subw_value, subw_msb, is_real, adapter_cols⟩ := cols
  let clk_low := clk_0_16 + clk_16_24 * 65536
  let op_a_write_value : Vector (Expression (ZMod p)) 4 :=
    #v[subw_value[0], subw_value[1], subw_msb * 65535, subw_msb * 65535]
  SP1Clean.SubwOp.assertionGated
    (⟨adapter.op_b_memory.prev_value, adapter.op_c_memory.prev_value,
       subw_value, subw_msb, is_real⟩ :
      Var SP1Clean.SubwOp.InputsGated (ZMod p))
  SP1Clean.CPUState.Gated.assertion
    (⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩,
       #v[pc[0] + 4, pc[1], pc[2]], 8, is_real⟩ :
      Var SP1Clean.CPUState.Gated.Inputs (ZMod p))
  SP1Clean.RTypeReader.Gated.assertion
    (⟨clk_high, clk_low, 20, pc, op_a_write_value, adapter,
       is_real, adapter_cols.is_trusted⟩ :
      Var SP1Clean.RTypeReader.Gated.Inputs (ZMod p))
  adapter.op_a_0 === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) SubwCols unit where
  name := "SP1Clean.Subw"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

/-- The chip is the `UserMode` variant (`M = UserMode` in upstream Rust),
so its `adapter_cols.is_trusted` payload is structurally equal to
`is_real` (both alias `Main[31]`). The `is_real = 1` precondition
restricts the FormalAssertion to non-padding rows: completeness
reconstructs `SubwOp.Assertion.Spec` for the sub-circuit witness via
the `Assertion_Spec_iff_Spec ↔ iff_sp1 ↔ iff_sp1_full` round-trip
(which needs the BitVec triple from FormalSpec's `is_real = 1 → ...`
conjunct + operand bounds), so the chip contract is only meaningful on
real rows. Trace-soundness drivers discharge `is_real = 1` per row
before invoking `Subw.assertion`. -/
def Assumptions (cols : SubwCols (ZMod p)) : Prop :=
  cols.adapter_cols.is_trusted = cols.is_real ∧ cols.is_real = 1

/-- The unified chip Spec is defined in `Cols.lean`
(`SP1Clean.Subw.FormalSpec`). -/
abbrev FormalSpec := @SP1Clean.Subw.FormalSpec p

/-- Soundness collapses to a single application of the structural
mirror lemma `formalSpec_of_subcircuit_specs` (`Lemmas.lean`) once
`circuit_proof_start` peels back the Clean elaboration plumbing and the
`h_input` / `h_assumptions` / `h_holds` destructure surfaces the four
sub-circuit witnesses (`SubwOp.AssertionGated` Assumptions→Spec,
`CPUState.Gated` Spec, `RTypeReader.Gated` Spec, scalar `op_a_0 = 0`
gate). The lowercase `RTypeReader.Gated.assertion.Spec` produced by
`circuit_proof_start` needs a one-line `simpa` bridge to the uppercase
`Gated.Assertion.Spec` form because the inline-constructed
`op_a_write_value` (`#v[subw_value[0], subw_value[1], subw_msb*65535,
subw_msb*65535]`) goes through `Vector.map (Expression.eval env)` and
doesn't reduce automatically. All other sub-circuit composition logic —
including the `Word.isU64 op_b/op_c` extraction from `h_rtr` and the
BV64 `RV64.subw` clause construction — lives inside the named lemma. -/
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e_adapter, e_subw_value, e_subw_msb, e_is_real, e_ac⟩
    := h_input
  subst_eqs
  obtain ⟨_h_trusted, h_is_real⟩ := h_assumptions
  obtain ⟨h_subwop_sub, h_cpu_sub, h_rtr_sub, h_op_a_0⟩ := h_holds
  unfold id at *
  -- Bridge the lowercase `RTypeReader.Gated.assertion.Spec` produced by
  -- `circuit_proof_start` (with `Vector.map (Expression.eval env)` views of
  -- the inline-constructed `op_a_write_value`) to the uppercase
  -- `Gated.Assertion.Spec` form (with `cols.subw_value[i]` /
  -- `cols.subw_msb` projections) expected by
  -- `formalSpec_of_subcircuit_specs`. The same simp set is used both sides.
  refine formalSpec_of_subcircuit_specs _ h_is_real
    h_subwop_sub (h_cpu_sub trivial) ?_ h_op_a_0
  simpa [SP1Clean.RTypeReader.Gated.assertion,
         SP1Clean.RTypeReader.Gated.Assertion.Spec, sub_eq_add_neg,
         Vector.getElem_map] using h_rtr_sub trivial

/-- Completeness peels `h_spec` (= `FormalSpec input`) via
`subcircuit_specs_of_formalSpec` into the four sub-circuit `Spec`s, then
re-wraps each as the `(Assumptions, Spec)` pair the corresponding
`FormalAssertion.completeness` expects. The `Word.isU64 op_b/op_c`
bounds needed for `SubwOp.AssertionGated.Assumptions` come from
`isU64_operands_of_spec`. The lowercase
`RTypeReader.Gated.assertion.Spec` expected by the `FormalAssertion`
machinery needs a one-line `simpa` bridge from the uppercase
`Gated.Assertion.Spec` produced by the named lemma (mirror of the
soundness bridge). -/
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e_adapter, e_subw_value, e_subw_msb, e_is_real, e_ac⟩
    := h_input
  subst_eqs
  obtain ⟨_h_trusted, h_is_real⟩ := h_assumptions
  unfold id at *
  obtain ⟨h_subwop, h_cpu, h_rtr, h_op_a_0⟩ :=
    subcircuit_specs_of_formalSpec _ h_is_real h_spec
  obtain ⟨h_isU64_b, h_isU64_c⟩ :=
    SP1Clean.RTypeReader.Gated.Assertion.isU64_operands_of_spec h_is_real h_rtr
  refine ⟨⟨⟨Or.inr h_is_real, fun _ => ⟨h_isU64_b, h_isU64_c⟩⟩, h_subwop⟩,
          ⟨trivial, h_cpu⟩, ⟨trivial, ?_⟩, h_op_a_0⟩
  simpa [SP1Clean.RTypeReader.Gated.assertion,
         SP1Clean.RTypeReader.Gated.Assertion.Spec, sub_eq_add_neg,
         Vector.getElem_map] using h_rtr

end Assertion

/-- The full Clean `FormalAssertion` for `SubwChip`. Single subcircuit
composition (`SubwOp.assertion + CPUState.Gated.assertion +
RTypeReader.Gated.assertion + 1 scalar gate`) backing one unified `Spec`.
Per-row Sail equivalence is derived externally via
`sail_correct_of_formalSpec` (`SailBridge.lean`). -/
def assertion : FormalAssertion (ZMod p) SubwCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.Subw
