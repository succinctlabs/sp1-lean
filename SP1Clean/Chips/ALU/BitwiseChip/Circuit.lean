import SP1Clean.Chips.ALU.BitwiseChip.Lemmas
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
import SP1Clean.Operations.BitwiseU16Operation
import SP1Clean.MemoryAccess
import RISCV.Instructions

/-! # `BitwiseChip` Clean circuit + `FormalAssertion`

Wraps the chip-level constraint surface into a Clean `FormalAssertion`
whose `Spec` is the faithful structural bundle for the R-type
`xor`/`or`/`and` variants. Composes `BitwiseU16Op.assertion`
(8 gated byte-table lookups on the byte-decomposition) +
`CPUState.Gated.assertion` + `ALUTypeReader.Gated.assertion` + three
selector binarity gates + the sum binarity + `op_a_0 = 0`.

Mirrors `SP1Clean/Chips/ALU/LtChip/Circuit.lean`: both soundness and
completeness close via the structural midpoint lemmas
(`formalSpec_of_subcircuit_specs` / `subcircuit_specs_of_formalSpec`),
since the structural `FormalSpec` exposes the byte-decomposition
witnesses directly. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Bitwise

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

/-- Clean-side chip circuit. Mirrors SP1 Rust's `BitwiseChip::eval(builder, cols)`
1:1 via flag-threaded sub-circuits: `BitwiseU16Op.assertion` (byte lookups,
gated by `sum := is_xor + is_or + is_and`, opcode `is_xor*2 + is_or*1`)
+ `CPUState.Gated.assertion` + `ALUTypeReader.Gated.assertion` + three
selector binarity gates + sum binarity + chip-level `op_a_0 = 0`. -/
@[reducible]
def main (cols : Var BitwiseCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩, adapter,
       bitwise_operation, is_xor, is_or, is_and, adapter_cols⟩ := cols
  let sum := is_xor + is_or + is_and
  let opcode_e := is_xor * 3 + is_or * 4 + is_and * 5
  let opcode_bw := is_xor * 2 + is_or * 1 + is_and * 0
  let clk_low := clk_0_16 + clk_16_24 * 65536
  let res := bitwise_operation.bitwise_operation.result
  let op_a_write_value : Vector (Expression (ZMod p)) 4 :=
    #v[res[0] + res[1] * 256, res[2] + res[3] * 256,
       res[4] + res[5] * 256, res[6] + res[7] * 256]
  SP1Clean.BitwiseU16Op.assertion
    (⟨adapter.op_b_memory.prev_value, adapter.op_c_memory.prev_value,
       bitwise_operation.b_low_bytes.low_bytes,
       bitwise_operation.c_low_bytes.low_bytes,
       bitwise_operation.bitwise_operation.result,
       opcode_bw, sum⟩ :
      Var SP1Clean.BitwiseU16Op.Inputs (ZMod p))
  SP1Clean.CPUState.Gated.assertion
    (⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩,
       #v[pc[0] + 4, pc[1], pc[2]], 8, sum⟩ :
      Var SP1Clean.CPUState.Gated.Inputs (ZMod p))
  SP1Clean.ALUTypeReader.Gated.assertion
    (⟨clk_high, clk_low, opcode_e, pc, op_a_write_value, adapter,
       sum, adapter_cols.is_trusted⟩ :
      Var SP1Clean.ALUTypeReader.Gated.Inputs (ZMod p))
  is_xor * (is_xor - 1) === 0
  is_or * (is_or - 1) === 0
  is_and * (is_and - 1) === 0
  sum * (sum - 1) === 0
  adapter.op_a_0 === 0

set_option maxHeartbeats 800000 in
-- 3 subcircuits + 5 scalar gates; subcircuitsConsistent synthesis
-- exceeds the default cap.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) BitwiseCols unit where
  name := "SP1Clean.Bitwise"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]
  subcircuitsConsistent input offset := by
    simp +arith only [main, circuit_norm]

/-- The chip is the `UserMode` variant; `adapter_cols.is_trusted` aliases
the aggregate `is_xor + is_or + is_and` sum (the is_real flag). Non-padding
rows have `is_xor + is_or + is_and = 1`. -/
def Assumptions (cols : BitwiseCols (ZMod p)) : Prop :=
  cols.adapter_cols.is_trusted = cols.is_xor + cols.is_or + cols.is_and ∧
  cols.is_xor + cols.is_or + cols.is_and = 1

/-- Soundness collapses to `formalSpec_of_subcircuit_specs` once
`circuit_proof_start` peels back the Clean elaboration plumbing. -/
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  -- Deep destructure so the `result`/byte vectors fully substitute to
  -- `Vector.map eval input_var_<X>`, letting `Vector.getElem_map` bridge the
  -- element-wise `op_a_write_value` reconstruction in the ALU sub-Spec.
  obtain ⟨⟨e_clk_h, e_clk_16, e_clk_0, e_pc⟩,
          ⟨e_oa, ⟨e_oapv, ⟨e_oapl, e_oadll⟩⟩, e_oa0, e_ob,
            ⟨e_obpv, ⟨e_obpl, e_obdll⟩⟩, e_oc,
            ⟨e_ocpv, ⟨e_ocpl, e_ocdll⟩⟩, e_imm⟩,
          ⟨⟨e_blb⟩, ⟨e_clb⟩, ⟨e_br⟩⟩,
          e_is_xor, e_is_or, e_is_and, ⟨e_itrust⟩⟩ := h_input
  subst_eqs
  obtain ⟨h_bw_sub, h_cpu_sub, h_alu_sub, h_is_xor_bin, h_is_or_bin,
          h_is_and_bin, h_sum_bin, h_op_a_0⟩ := h_holds
  unfold id at *
  refine formalSpec_of_subcircuit_specs _ (h_bw_sub trivial)
    (h_cpu_sub trivial) ?_ ?_ ?_ ?_ ?_ h_op_a_0
  · -- ALU op_a_write_value reconstruction: bridge `(Vector.map eval rv)[i]`
    -- (cols projection in the lemma) ↔ `eval rv[i]` (in `h_alu_sub`).
    simp only [Vector.getElem_map]; exact h_alu_sub trivial
  · linear_combination h_is_xor_bin
  · linear_combination h_is_or_bin
  · linear_combination h_is_and_bin
  · linear_combination h_sum_bin

/-- Completeness. Provable since `FormalSpec` *is* the structural bundle:
`subcircuit_specs_of_formalSpec` unbundles `h_spec` into the three
sub-circuit Specs + the binary gates + `op_a_0`, then each gated
sub-assertion is re-wrapped as `⟨trivial, its-Spec⟩` (all three carry
trivial `Assumptions`) and each scalar gate re-stated in `x + -1` form. -/
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e_clk_h, e_clk_16, e_clk_0, e_pc⟩,
          ⟨e_oa, ⟨e_oapv, ⟨e_oapl, e_oadll⟩⟩, e_oa0, e_ob,
            ⟨e_obpv, ⟨e_obpl, e_obdll⟩⟩, e_oc,
            ⟨e_ocpv, ⟨e_ocpl, e_ocdll⟩⟩, e_imm⟩,
          ⟨⟨e_blb⟩, ⟨e_clb⟩, ⟨e_br⟩⟩,
          e_is_xor, e_is_or, e_is_and, ⟨e_itrust⟩⟩ := h_input
  subst_eqs
  unfold id at *
  obtain ⟨h_bw, h_cpu, h_alu, h_xor_bin, h_or_bin, h_and_bin, h_sum_bin, h_op_a_0⟩ :=
    subcircuit_specs_of_formalSpec _ h_spec
  -- Bridge the ALU `op_a_write_value` reconstruction from the cols-projection
  -- form (`(Vector.map eval rv)[i]`) to the `eval rv[i]` form the goal carries.
  simp only [Vector.getElem_map] at h_alu
  refine ⟨⟨trivial, h_bw⟩, ⟨trivial, h_cpu⟩, ⟨trivial, h_alu⟩,
          ?_, ?_, ?_, ?_, h_op_a_0⟩
  · linear_combination h_xor_bin
  · linear_combination h_or_bin
  · linear_combination h_and_bin
  · linear_combination h_sum_bin

end Assertion

/-- The full Clean `FormalAssertion` for `BitwiseChip`'s R-type variants. -/
def assertion : FormalAssertion (ZMod p) BitwiseCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.Bitwise
