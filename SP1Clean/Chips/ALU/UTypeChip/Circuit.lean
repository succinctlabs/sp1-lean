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
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
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

/-- **Status: structural refactor landed (Phases 1-4), proof body open.**

The chip's `main` now composes `CPUState.assertion` + `JTypeReader.Gated.assertion`
+ `AddOp.assertion` (with conditional gate `is_real - op_a_0`) + 5 inline
scalar gates, matching SP1's `_root_.UType.constraints` 1:1. `FormalSpec`
(in `Cols.lean`) and `allHold_iff_structural` (in `Lemmas.lean`) are
aligned with `JTypeReader.Gated.Assertion.Spec` (new lemma in
`SP1Clean/Reader/JTypeReader.lean`).

What remains to close `soundness`:
1. **Structural conjuncts** (8 of FormalSpec's 9): destructure `h_holds`
   into the 3 subcircuit `_sub` hypotheses + 5 scalar-gate equalities;
   each maps to one FormalSpec conjunct. CPUState/JTypeReader.Gated bridge
   via `simpa` analogous to `AddwChip/Circuit.lean:113-117`.
2. **AddOp → `.allHold` bridge.** `h_addop_sub trivial` gives `AddOp.RawSpec`
   (unconditional, per the assertion's current Spec). FormalSpec asks for
   `(AddOperation.constraints _ _ _ (is_real - op_a_0)).allHold`. Bridge
   via a local helper: case-split on `is_real ∈ {0, 1}` (from
   `h_jtr.1`) and `op_a_0 ∈ {0, 1}` (resolve `ProgramGated.Spec` disjunct
   via `is_trusted = is_real ≠ 0` from Assumptions). At gate=1 use
   `AddOperation.allHold_constraints_iff`; at gate=0 the constraint list
   is trivially satisfied (every gate is `0 * _ = 0` and byte sends at
   `mult = 0` are vacuous). The chip-scalar `(is_real - 1) * op_a_0 = 0`
   ensures `is_real - op_a_0 ∈ {0, 1}` (no `gate = -1` case).
3. **BitVec leg** (the 9th conjunct, conditional on `is_real = 1 ∧ op_a_0 = 0`):
   - Resolve `JTypeReader.Gated.Spec.ProgramGated` disjunct under
     `is_trusted = 1` → `ProgramSpec`. Extract `Opcode.trusted_instr` over
     the U-type opcode encoding (48 = AUIPC, 49 = LUI) — yields the
     sign-extension identity `op_b_imm.toBitVec64 = signExtend 64 (imm +++ 0#12)`.
   - `by_cases h_au : is_auipc = 1`:
     - **AUIPC.** Three addend gates give `addend[i] = pc[i]`. From `h_addop`,
       `AddOperation.spec` + `Word.isU64 op_b_imm` (from
       `RegisterAccess.Assertion.Spec` under `is_real ≠ 0`) yield
       `add_result.toBitVec64 = pc.toBitVec64 + op_b_imm.toBitVec64`.
       Combine with sign-ext fact to conclude `= RV64.auipc imm pc`.
     - **LUI.** From `h_isa_bin` and `¬(is_auipc = 1)`, `is_auipc = 0`.
       Addend gates give `addend[i] = 0`. `AddOperation.spec` yields
       `add_result.toBitVec64 = 0 + op_b_imm.toBitVec64 = op_b_imm.toBitVec64`.
       Conclude `= RV64.lui imm`. (Re-derive inline; the SP1-native
       `_root_.UType.correct_lui` produces a Sail-monadic equation, not
       this BitVec equation, so it's not directly applicable.)

The closure is mechanically tractable but ~80–120 lines of intricate Lean
mirroring `SP1Clean/AddwChip/Circuit.lean:102-147` (for the BitVec leg
structure) and `SP1Chips/UType/UTypeChip.lean:62-247` (for the
addend/sign-ext algebra). Soundness will be valid modulo the still-`sorry`'d
`AddOp.assertion.soundness` in `SP1Clean/Operations/AddOperation.lean:226`. -/
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

/-- **Status: structural refactor landed (Phases 1-4), proof body open.**

Completeness destructures `FormalSpec` (8 structural conjuncts + 1 BitVec
conjunct that's discarded since Completeness only sees the structural Spec)
and dispatches each to the matching subcircuit's input requirement
(`⟨trivial, h_<sub>⟩` form) plus the 5 inline scalar gates. The BitVec
conjunct is discarded. Mirror `SP1Clean/AddwChip/Circuit.lean:149-160`. -/
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
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
