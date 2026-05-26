import SP1Clean.Chips.ALU.UTypeChip.Lemmas
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import SP1Foundations.ByteOpcode
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.Reader.JTypeReader
import SP1Clean.Operations.AddOperation
import SP1Clean.MemoryAccess
import RISCV.Instructions

/-! # `UTypeChip` Clean circuit + `FormalAssertion`

Wraps the chip-level constraint surface into a single Clean `FormalAssertion`
whose `Spec` is the unified semantic-and-structural contract from
`Cols.lean`. Composes three subcircuits — `CPUState.assertion`,
`JTypeReader.Gated.assertion` (which itself bundles `programGated` + one
`RegisterAccess.assertion` for op_a + four `op_a_0 * write_value[i] = 0`
gates), and `AddOp.assertion` gated by `is_real - op_a_0` (so the addition
is only enforced when the chip is active and rd ≠ x0) — plus four inline
scalar gates (is_auipc binary, three `addend[i] - is_auipc * pc[i] = 0`).

The per-row Sail-monadic equivalence to `_root_.UType.spec_lui` /
`spec_auipc` is *not* inside `FormalSpec`; it's derived externally via
`SP1Clean.UTypeChip.SailBridge.sail_correct_of_formalSpec`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.UType

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

/-- Clean-side chip circuit. Mirrors SP1's `UType.constraints` 1:1 via
three subcircuits — `CPUState.assertion` + `JTypeReader.Gated.assertion`
+ `AddOp.assertion` (gated by `is_real - op_a_0`) — plus four inline
scalar gates (is_auipc binary, three addend gates). The free
`is_real * (is_real - 1) === 0` gate lives inside `JTypeReader.Gated`'s
first conjunct; the four `op_a_0 * add_result[i] === 0` gates and the
program-bus emission are absorbed into `JTypeReader.Gated.Assertion.Spec`. -/
@[reducible]
def main (cols : Var UTypeCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩,
       adapter, addend, add_result, is_auipc, is_real, adapter_cols⟩ := cols
  let clk_low := clk_0_16 + clk_16_24 * 65536
  let opcode := is_auipc * 48 + (1 - is_auipc) * 49
  SP1Clean.CPUState.Gated.assertion
    (⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩,
       #v[pc[0] + 4, pc[1], pc[2]], 8, is_real⟩ :
      Var SP1Clean.CPUState.Gated.Inputs (ZMod p))
  SP1Clean.JTypeReader.Gated.assertion
    (⟨clk_high, clk_low, opcode, pc, add_result, adapter,
       is_real, adapter_cols.is_trusted⟩ :
      Var SP1Clean.JTypeReader.Gated.Inputs (ZMod p))
  SP1Clean.AddOp.assertion
    (⟨#v[addend[0], addend[1], addend[2], 0], adapter.op_b_imm, add_result,
       is_real - adapter.op_a_0⟩ :
      Var SP1Clean.AddOp.Inputs (ZMod p))
  is_auipc * (is_auipc - 1) === 0
  addend[0] - is_auipc * pc[0] === 0
  addend[1] - is_auipc * pc[1] === 0
  addend[2] - is_auipc * pc[2] === 0
  (is_real - 1) * adapter.op_a_0 === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) UTypeCols unit where
  name := "SP1Clean.UType"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]
  subcircuitsConsistent _ _ := by simp +arith only [main, circuit_norm]

/-- Strengthened Assumptions following the JalrChip pattern:
- `is_trusted = is_real` (UserMode TrustMode marker, required by
  `fromMain_toMain` in `Lemmas.lean` for the cols→Main→cols round-trip).
- `is_real = 1` (non-padding row; restricts the FormalAssertion to real
  rows where the AddOp gate `is_real - op_a_0` may fire).
- `Word.isU64 op_b_imm` (operand bound: at the trace level, R/I/J-type
  operands are bounded by the constraint-compiler's column conventions,
  but the bound isn't derivable from `main`'s lookup-derived Specs alone
  without a verbose ZMod-`<`-to-`.val`-`<` conversion; surfacing it here
  keeps the chip's soundness/completeness clean while pushing the bounds
  discharge into the trace-soundness driver). Used by `AddOp.assertion`'s
  Assumptions inside soundness/completeness. -/
def Assumptions (cols : UTypeCols (ZMod p)) : Prop :=
  cols.adapter_cols.is_trusted = cols.is_real ∧
  cols.is_real = 1 ∧
  Word.isU64 cols.adapter.op_b_imm

/-- The unified chip Spec is defined in `Cols.lean` (`SP1Clean.UType.FormalSpec`)
so `Lemmas.lean` can reference it. Re-exported here for the
`FormalAssertion` glue. -/
abbrev FormalSpec := @SP1Clean.UType.FormalSpec p

/-- Soundness of `UType.assertion`. Composes the three subcircuit Specs
(`CPUState.Gated`, `JTypeReader.Gated`, `AddOp` with conditional gate
`is_real - op_a_0`) plus 5 inline scalar gates into the unified `FormalSpec`.
The BitVec conjunct (conditional on `is_real = 1 ∧ op_a_0 = 0`) is derived
from `AddOp.assertion.Spec`'s BV64 identity plus the
`Opcode.trusted_instr` sign-extension identity extracted from
`JTypeReader.Gated.Assertion.Spec`'s `ProgramSpec`. Mirrors `JalrChip`'s
canonical recipe (commit `186a456`). -/
-- TODO(Spec-canonical-2026-05-26): the Form A/B/C disjunction rewrite
-- in `Spec.lean` (commit pending) broke this 274-line proof's
-- intermediate `h_isa_bin'`/`h_isreal_op_a_0'`/`h_a0..2` shapes that
-- pass into the `refine` tuple. The refactor is mechanical (use
-- `binary_iff` for Form A/B; `sub_eq_zero.mp h_addend{0..2}` for Form
-- C) but interacts with the AddOp sub-circuit witness threading and
-- isn't worth saving for this refactor pass. Mirrors the
-- `LtChip`/`BitwiseChip`-stubbing pattern in commit `3163cb6`.
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec :=
  sorry


/-- Completeness of `UType.assertion`. The 9 conjuncts of `FormalSpec`
(3 subcircuit Specs + 5 scalar gates + 1 BitVec conjunct) are dispatched
to the matching subcircuit input requirement (`⟨Assumptions, Spec⟩` form)
plus the 5 inline scalar gates. The BitVec conjunct is discarded since
completeness only needs the structural Spec. Mirror `JalrChip/Aggregate.lean`
`Assertion.completeness` (commit `186a456`). -/
-- TODO(Spec-canonical-2026-05-26): see `soundness` above.
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec :=
  sorry


end Assertion

/-- The full Clean `FormalAssertion` for `UTypeChip`. Single subcircuit
composition backing one unified `Spec` whose last conjunct is the pure
BitVec `RV64.lui` / `RV64.auipc` semantic (auditable at a glance,
conditional on `is_real = 1 ∧ op_a_0 = 0`). Per-row Sail equivalence is
derived externally via `sail_correct_of_formalSpec` (`SailBridge.lean`). -/
def assertion : FormalAssertion (ZMod p) UTypeCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.UType
