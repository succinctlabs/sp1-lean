import SP1Clean.UTypeChip.Lemmas
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import SP1Foundations.ByteOpcode
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.Reader.OperandAccess
import SP1Clean.Operations.AddOperation
import SP1Clean.MemoryAccess
import RISCV.Instructions

/-! # `UTypeChip` Clean circuit + `FormalAssertion`

Wraps the chip-level constraint surface into a single Clean `FormalAssertion`
whose `Spec` is the unified semantic-and-structural contract from
`Cols.lean`. Composes four subcircuits — `CPUState.assertion`,
`ProgramTable.assertion` (with `imm_b = 1, imm_c = 1` matching the SP1-side
J-type reader's program-bus emission), `OperandAccess.assertion` (op_a
register access), and `AddOp.assertion` (gated by `is_real - op_a_0` so
the addition is only enforced when the chip is active and rd ≠ x0) — plus
ten inline scalar gates: six chip-level (is_real/is_auipc binary, three
addend gates, op_a_0 zero) and four `op_a_0 * add_result[i] = 0` gates
that mirror JTypeReader.constraints' op_a_0-masked write-value emission.

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

/-- Clean-side chip circuit. Composes four subcircuits plus ten inline
scalar gates, mirroring the union of `SP1Chips/UType/Constraints.lean`'s
direct emissions and `_root_.JTypeReader.constraints`' internal emissions
(program send + 4 op_a_0-masked write gates + byte-bus + memory). -/
@[reducible]
def main (cols : Var UTypeCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, op_a_memory, op_a_0, op_b_imm, op_c_imm⟩,
       addend, add_result, is_auipc, is_real, _adapter_cols⟩ := cols
  let clk_low := clk_0_16 + clk_16_24 * 65536
  let opcode := is_auipc * 48 + (1 - is_auipc) * 49
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ProgramTable.assertion
    (⟨pc, opcode, op_a, op_b_imm, op_c_imm, op_a_0, 1, 1⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 4, op_a_memory.access_timestamp.prev_low,
       op_a_memory.access_timestamp.diff_low_limb,
       op_a_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))
  SP1Clean.AddOp.assertion
    (⟨#v[addend[0], addend[1], addend[2], 0], op_b_imm, add_result,
       is_real - op_a_0⟩ :
      Var SP1Clean.AddOp.Inputs (ZMod p))
  is_real * (is_real - 1) === 0
  is_auipc * (is_auipc - 1) === 0
  addend[0] - is_auipc * pc[0] === 0
  addend[1] - is_auipc * pc[1] === 0
  addend[2] - is_auipc * pc[2] === 0
  (is_real - 1) * op_a_0 === 0
  op_a_0 * add_result[0] === 0
  op_a_0 * add_result[1] === 0
  op_a_0 * add_result[2] === 0
  op_a_0 * add_result[3] === 0

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

/-- The chip is the `UserMode` variant (`M = UserMode` in upstream Rust),
so its `adapter_cols.is_trusted` payload is structurally equal to `is_real`
(both alias `Main[30]` in the constraint compiler's emission). Required by
`fromMain_toMain` (`Lemmas.lean`) for the cols→Main→cols round-trip. -/
def Assumptions (cols : UTypeCols (ZMod p)) : Prop :=
  cols.adapter_cols.is_trusted = cols.is_real

/-- The unified chip Spec is defined in `Cols.lean` (`SP1Clean.UType.FormalSpec`)
so `Lemmas.lean` can reference it. Re-exported here for the
`FormalAssertion` glue. -/
abbrev FormalSpec := @SP1Clean.UType.FormalSpec p

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  -- TODO: full soundness proof. The structural conjuncts (cpuStateSpec,
  -- jtypeReaderSpec assembly from ProgramTable.Spec + OperandAccess.Spec
  -- + 4 op_a_0 gates, raw AddOp `.allHold` from AddOp.RawSpec via case split
  -- on op_a_0 binary, six scalar trailing gates) and the conditional BitVec
  -- `RV64.lui` / `RV64.auipc` equation (via `AddOperation.spec` + program-bus
  -- `trusted_instr` sign-ext fact, with `by_cases` on `is_auipc`) close the
  -- proof. Skeleton modeled on `SP1Clean/AddChip/Circuit.lean:100-142` +
  -- `SP1Chips/UType/UTypeChip.lean:62-247` (the SP1-native `correct_lui` /
  -- `correct_auipc` proofs the BitVec leg recapitulates).
  sorry

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  -- TODO: full completeness proof. Mirror AddiChip's pattern: destructure
  -- FormalSpec into its conjuncts and dispatch each to the matching subcircuit's
  -- input requirement (trivial Assumptions + Spec re-use). The BitVec
  -- conjunct is discarded (Completeness only sees the structural Spec).
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
