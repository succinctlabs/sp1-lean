import SP1Clean.Chips.Control.JalChip.Lemmas
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
import SP1Clean.SP1Lookup
import SP1Clean.MemoryAccess
import RISCV.Instructions

/-! # `JalChip` Clean circuit + `FormalAssertion`

Wraps the chip-level constraint surface into a single Clean `FormalAssertion`
whose `Spec` is the unified semantic-and-structural contract from
`Chips/Spec.lean` (`SP1Clean.Jal.Assertion.FormalSpec`). Composes five
subcircuits — `CPUState.Gated.assertion` (clock/state-bus), two
`AddOp.assertion` (jump-target gated by `is_real`, return-address gated
by `is_real - op_a_0`), `JTypeReader.Gated.assertion` (program-bus + op_a
register access), and one `SP1Lookup.byteOpcodeGated` (next_pc[0] 4-alignment
Range14) — plus three trailing scalar gates (`next_pc[3] = 0`,
`op_a_write_value[3] = 0`, `(is_real - 1) * op_a_0 = 0`). Mirrors UTypeChip's
canonical pattern with the jump-target AddOp / alignment lookup added for
control flow.

The per-row Sail-monadic equivalence to `_root_.Jal.spec_jal` is *not*
inside `FormalSpec`; it's derived externally via
`SP1Clean.JalChip.SailBridge.sail_correct_of_formalSpec`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Jal

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

/-- Clean-side chip circuit. Mirrors SP1's `Jal.constraints` shape:
- `CPUState.Gated.assertion` — clock byte sends + state-bus interactions,
  all gated by `is_real`. Absorbs the free `is_real * (is_real - 1) = 0`
  gate.
- `AddOp.assertion` (jump-target) — `pc + op_b_imm = next_pc`, gated by
  `is_real`.
- `AddOp.assertion` (return-address) — `pc + 4 = op_a_write_value`, gated
  by `is_real - op_a_0` (active only on a real row that writes to a
  non-x0 destination).
- `JTypeReader.Gated.assertion` — program-bus send for opcode 46 (JAL)
  plus op_a register-access subcircuit, gated by `is_real`/`is_trusted`.
- `SP1Lookup.byteOpcodeGated` — `next_pc[0] / 4 ∈ Range(14)` (jump-target
  4-alignment), gated by `is_real`.
- Three trailing scalar gates. -/
@[reducible]
def main (cols : Var JalCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩,
       adapter, next_pc, op_a_write_value, is_real, adapter_cols⟩ := cols
  let clk_low := clk_0_16 + clk_16_24 * 65536
  SP1Clean.CPUState.Gated.assertion
    (⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩,
       #v[next_pc[0], next_pc[1], next_pc[2]], 8, is_real⟩ :
      Var SP1Clean.CPUState.Gated.Inputs (ZMod p))
  SP1Clean.AddOp.assertion
    (⟨pc.push 0, adapter.op_b_imm, next_pc, is_real⟩ :
      Var SP1Clean.AddOp.Inputs (ZMod p))
  SP1Clean.AddOp.assertion
    (⟨pc.push 0, #v[(4 : Expression (ZMod p)), 0, 0, 0], op_a_write_value,
       is_real - adapter.op_a_0⟩ :
      Var SP1Clean.AddOp.Inputs (ZMod p))
  SP1Clean.JTypeReader.Gated.assertion
    (⟨clk_high, clk_low, 46, pc, op_a_write_value, adapter,
       is_real, adapter_cols.is_trusted⟩ :
      Var SP1Clean.JTypeReader.Gated.Inputs (ZMod p))
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), next_pc[0] * (4 : ZMod p)⁻¹, 14, 0],
       is_real⟩ : Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  next_pc[3] === 0
  op_a_write_value[3] === 0
  (is_real - 1) * adapter.op_a_0 === 0

set_option maxHeartbeats 800000 in
-- Higher heartbeats: 5 subcircuits + 3 scalar asserts + the JalCols flatten
-- to ~30 input bits pushes `localLength_eq` synthesis past the 200k default.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) JalCols unit where
  name := "SP1Clean.Jal"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]
  subcircuitsConsistent _ _ := by simp +arith only [main, circuit_norm]

/-- Strengthened Assumptions following the UTypeChip pattern:
- `is_trusted = is_real` (UserMode TrustMode marker, required by
  `fromMain_toMain` in `Lemmas.lean` for the cols→Main→cols round-trip).
- `is_real = 1` (non-padding row; the chip's contract is only meaningful
  on real rows, and the AddOp gates may fire).
- `Word.isU64` of `pc.push 0` and `op_b_imm` (operand bounds: at the trace
  level these come from `JTypeReader.Gated`'s program-bus clause and the
  4-aligned pc range, but they're not extractable from `main`'s
  lookup-derived Specs without a verbose ZMod-`<`-to-`.val`-`<` conversion;
  surfacing them keeps the chip's soundness/completeness clean while
  pushing the bounds discharge into the trace-soundness driver). -/
def Assumptions (cols : JalCols (ZMod p)) : Prop :=
  cols.adapter_cols.is_trusted = cols.is_real ∧
  cols.is_real = 1 ∧
  Word.isU64 (cols.state.pc.push 0) ∧
  Word.isU64 cols.adapter.op_b_imm

/-- Soundness of `Jal.assertion`. Composes the five subcircuit Specs
(`CPUState.Gated`, `AddOp` × 2, `JTypeReader.Gated`, `byteOpcodeGated`)
plus the three scalar gates into the unified `FormalSpec`. The two
AddOp `Spec`s under their gate values (`is_real`, `is_real - op_a_0`)
deliver the BV64 identity directly; the trailing `next_pc[0]/4 ∈
Range(14)` clause is derived from `byteOpcodeGated.Spec`'s disjunctive
form under `is_real = 1`. Mirrors UTypeChip's canonical recipe. -/
-- TODO(Spec-canonical-2026-05-26): close after `Lemmas.allHold_iff_structural`
-- lands. The proof mirrors `SP1Clean.UType.Assertion.soundness` (currently
-- also sorry'd post-Spec-canonicalization). circuit_proof_start gives
-- h_holds as a 5-tuple of subcircuit-Specs + 3 scalar gates; refine into
-- the 8-conjunct FormalSpec.
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec :=
  sorry

/-- Completeness of `Jal.assertion`. The 8 conjuncts of `FormalSpec`
(4 subcircuit Specs + 3 scalar gates + 1 byte-opcode Spec) are
dispatched to the matching subcircuit input requirement (`⟨Assumptions,
Spec⟩` form) plus the 3 inline scalar gates. -/
-- TODO(Spec-canonical-2026-05-26): see `soundness` above.
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec :=
  sorry

end Assertion

/-- The full Clean `FormalAssertion` for `JalChip`. Single subcircuit
composition (`CPUState.Gated.assertion + AddOp.assertion × 2 +
JTypeReader.Gated.assertion + byteOpcodeGated` + 3 scalar gates) backing
one unified `Spec` whose semantic content is two BV64 equations (jump
target = pc + imm; return address = pc + 4) plus the JTypeReader's
program-bus / memory-bus consequences. Per-row Sail equivalence is
derived externally via `sail_correct_of_formalSpec` (`SailBridge.lean`). -/
def assertion : FormalAssertion (ZMod p) JalCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.Jal
