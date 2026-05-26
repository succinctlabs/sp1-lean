import SP1Clean.LtChip.Lemmas
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import SP1Foundations.ByteOpcode
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.Reader.OperandAccess
import SP1Clean.Reader.ALUTypeReader
import SP1Clean.Operations.LtOperationSigned
import SP1Clean.Operations.GatedLtSignedOp
import SP1Clean.MemoryAccess
import RISCV.Instructions

/-! # `LtChip` Clean circuit + `FormalAssertion` (directory-form scaffold)

Composes the Rust subcircuit graph for `LtChip::eval`:
- `LtSignedOp.assertion` (the comparison arithmetic — itself wrapping
  `U16MSBOp.assertion` ×2 + `LtUnsignedOp.assertion`),
- `CPUState.assertion`,
- `ALUTypeReader.assertion` (program + memory + imm_c switch),
- 4 trailing scalar gates (2 selector binaries + sum binary + op_a_0).

`is_real = is_slt + is_sltu`. The `is_signed` toggle for the
`LtSignedOp` sub-call is `cols.is_slt` (only the signed SLT/SLTI
variants need the sign-flip — SLTU/SLTIU use is_signed=0).

Soundness/completeness bodies are `sorry`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.LtChip

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

/-- Clean-side chip circuit. Mirrors SP1 Rust's `LtChip::eval(builder, cols)`
1:1 via flag-threaded `Gated` sub-circuits:
- `GatedLtSignedOp.assertion` (carries its own `gate = is_slt + is_sltu`),
- `CPUState.Gated.assertion` (binary gate + state-bus + byte-opcode),
- `ALUTypeReader.Gated.assertion` (program + memory + imm_c switch),
- 3 chip-level selector gates (`is_slt` / `is_sltu` binary + sum binary)
  and `op_a_0 = 0`. The free `is_real * (is_real - 1) === 0` gate now
  lives inside both Gated.Specs' first conjuncts (redundant but
  propositionally fine). -/
@[reducible]
def main (cols : Var LtCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩, adapter,
       compare_bit, u16_flags, not_eq_inv, comparison_limbs,
       b_msb, c_msb, is_slt, is_sltu, adapter_cols⟩ := cols
  let clk_low := clk_0_16 + clk_16_24 * 65536
  let is_real := is_slt + is_sltu
  let op_a_write_value : Vector (Expression (ZMod p)) 4 := #v[compare_bit, 0, 0, 0]
  SP1Clean.GatedLtSignedOp.assertion
    (⟨adapter.op_b_memory.prev_value, adapter.op_c_memory.prev_value,
       is_slt,
       compare_bit, u16_flags, not_eq_inv, comparison_limbs,
       b_msb, c_msb, is_real⟩ : Var SP1Clean.GatedLtSignedOp.Inputs (ZMod p))
  SP1Clean.CPUState.Gated.assertion
    (⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩,
       #v[pc[0] + 4, pc[1], pc[2]], 8, is_real⟩ :
      Var SP1Clean.CPUState.Gated.Inputs (ZMod p))
  SP1Clean.ALUTypeReader.Gated.assertion
    (⟨clk_high, clk_low, is_slt * 9 + is_sltu * 10, pc, op_a_write_value,
       adapter, is_real, adapter_cols.is_trusted⟩ :
      Var SP1Clean.ALUTypeReader.Gated.Inputs (ZMod p))
  is_slt * (is_slt - 1) === 0
  is_sltu * (is_sltu - 1) === 0
  is_real * (is_real - 1) === 0
  adapter.op_a_0 === 0

set_option maxHeartbeats 3200000 in
-- Sub-circuit chain (GatedLtSignedOp → GatedLtUnsignedOp) + 4 scalar
-- gates exceeds default `subcircuitsConsistent` synth budget by a
-- substantial margin (the nested gating multiplies the search depth).
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) LtCols unit where
  name := "SP1Clean.Lt"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]
  subcircuitsConsistent input offset := by
    simp only [main, circuit_norm]
    refine ⟨by omega, by omega, by omega, by omega⟩

/-- The chip is the `UserMode` variant; the adapter's `is_trusted`
payload is structurally equal to the aggregate `is_real = is_slt + is_sltu`.
Same TrustMode marker as AddChip's `Assumptions`. -/
def Assumptions (cols : LtCols (ZMod p)) : Prop :=
  cols.adapter_cols.is_trusted = cols.is_slt + cols.is_sltu

/-- The unified chip Spec is defined in `Cols.lean`
(`SP1Clean.LtChip.FormalSpec`). -/
abbrev FormalSpec := @SP1Clean.LtChip.FormalSpec p

-- TODO[clean-master-plan-phase-3,p3-lt-gated-iff-sp1]: blocked on the same
-- missing operation-level iff_sp1 bridges that block `Lemmas.lean:55`
-- (see breadcrumb there). Note `GatedLtUnsignedOp.Spec` already carries
-- the byte-range conjunct (`gate = 0 ∨ ByteOpcodeSpec ...` for the
-- U16Compare lookup, lines 87-90); the older inline comment below predates
-- that addition. The remaining gap is the iff_sp1 bridge, not a missing
-- byte-range fact.
-- BLOCKED on byte-range gap: the chip's FormalSpec carries conditional
-- BitVec semantic clauses (RV64.slt / RV64.sltu) that require
-- `LtOperationSigned.spec.signed` / `.unsigned`. Those theorems take the
-- full SP1 `LtOperationSigned.constraints.allHold` (including U16MSB /
-- U16Compare byte-range sends) plus `Word.isU64` on op_b/op_c. The
-- current `GatedLtSignedOp.Spec` (gate=1 case) drops the byte-range
-- facts, so we can't reconstruct the full SP1 allHold from the chip's
-- holds. Path forward: strengthen `GatedLtUnsignedOp.Spec` +
-- `GatedLtSignedOp.Spec` with U16Compare / U16MSB byte-range conjuncts
-- (Option A from the sunbeam plan) and add matching `byteOpcodeGated`
-- emissions to their `main`. Tracked alongside [[multiplicity-bus-GatedLt-migration]].
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨h_lt, h_cpu, h_alu, h_slt_bin, h_sltu_bin, h_real_bin, h_op_a_0,
          _h_slt_sem, _h_sltu_sem⟩ := h_spec
  unfold id at *
  -- Three sub-circuits' completeness premises (`⟨assumption, spec⟩`) plus
  -- 4 scalar gates. The is_real binary disjunction in h_real_bin recovers
  -- `is_real * (is_real - 1) = 0` via `Or.elim`.
  refine ⟨⟨trivial, h_lt⟩, ⟨trivial, h_cpu⟩, ⟨trivial, h_alu⟩,
          ?_, ?_, ?_, h_op_a_0⟩
  · linear_combination h_slt_bin
  · linear_combination h_sltu_bin
  · rcases h_real_bin with h_zero | h_one
    · linear_combination (input_is_slt + input_is_sltu - 1) * h_zero
    · linear_combination (input_is_slt + input_is_sltu) * h_one

end Assertion

/-- The full Clean `FormalAssertion` for `LtChip`. -/
def assertion : FormalAssertion (ZMod p) LtCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.LtChip
