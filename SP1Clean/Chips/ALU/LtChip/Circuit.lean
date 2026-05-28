import SP1Clean.Chips.ALU.LtChip.Lemmas
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
import SP1Clean.MemoryAccess
import RISCV.Instructions

/-! # `LtChip` Clean circuit + `FormalAssertion`

Wraps the chip-level constraint surface into a Clean `FormalAssertion`
whose `Spec` is the canonical (a)-shape unified contract for the
R-type `slt` / `sltu` variants. Composes `LtSignedOp.assertionGated` +
`CPUState.Gated.assertion` + `ALUTypeReader.Gated.assertion` + three
selector binarity gates + `op_a_0 = 0`.

`Assumptions` mirror AddChip's: `adapter_cols.is_trusted = is_slt + is_sltu`
(the UserMode TrustMode aliasing) plus `is_slt + is_sltu = 1` (the
non-padding-row gate).

Both soundness and completeness close axiom-clean: the structural
`FormalSpec` exposes the `LtSignedOp.AssertionGated.Spec` byte-decomp
witnesses directly, so completeness needs only `subcircuit_specs_of_formalSpec`
(an unbundling) rather than the `iff_sp1_full.mpr` `spec_inv` reconstruction
that a pure-semantic spec would have required. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Lt

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

/-- Clean-side chip circuit. Mirrors SP1 Rust's `LtChip::eval(builder, cols)`
1:1 via flag-threaded `Gated` sub-circuits: `LtSignedOp.assertionGated`
(byte-decomposition + comparison, gated by `sum := is_slt + is_sltu`,
with `is_signed := is_slt`) + `CPUState.Gated.assertion` (gated by `sum`)
+ `ALUTypeReader.Gated.assertion` (gated by `sum`/`is_trusted`) + three
selector binarity gates (`is_slt`, `is_sltu`, sum) + chip-level
`op_a_0 = 0`. -/
@[reducible]
def main (cols : Var LtCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩, adapter,
       is_slt, is_sltu, lt_operation, adapter_cols⟩ := cols
  let sum := is_slt + is_sltu
  let opcode_e := is_slt * 9 + is_sltu * 10
  let clk_low := clk_0_16 + clk_16_24 * 65536
  let op_a_write_value : Vector (Expression (ZMod p)) 4 :=
    #v[lt_operation.result.u16_compare_operation.bit, 0, 0, 0]
  SP1Clean.LtSignedOp.assertionGated
    (⟨adapter.op_b_memory.prev_value, adapter.op_c_memory.prev_value,
       is_slt,
       lt_operation.result.u16_compare_operation.bit,
       lt_operation.result.u16_flags,
       lt_operation.result.not_eq_inv,
       lt_operation.result.comparison_limbs,
       lt_operation.b_msb.msb,
       lt_operation.c_msb.msb,
       sum⟩ : Var SP1Clean.LtSignedOp.InputsGated (ZMod p))
  SP1Clean.CPUState.Gated.assertion
    (⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩,
       #v[pc[0] + 4, pc[1], pc[2]], 8, sum⟩ :
      Var SP1Clean.CPUState.Gated.Inputs (ZMod p))
  SP1Clean.ALUTypeReader.Gated.assertion
    (⟨clk_high, clk_low, opcode_e, pc, op_a_write_value, adapter,
       sum, adapter_cols.is_trusted⟩ :
      Var SP1Clean.ALUTypeReader.Gated.Inputs (ZMod p))
  is_slt * (is_slt - 1) === 0
  is_sltu * (is_sltu - 1) === 0
  sum * (sum - 1) === 0
  adapter.op_a_0 === 0

set_option maxHeartbeats 800000 in
-- LtChip has 3 subcircuits + 4 scalar gates; subcircuitsConsistent
-- synthesis exceeds default cap.
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
    simp +arith only [main, circuit_norm]

/-- The chip is the `UserMode` variant; `adapter_cols.is_trusted` aliases
the aggregate `is_slt + is_sltu` sum (the is_real flag). Non-padding
rows have `is_slt + is_sltu = 1`. -/
def Assumptions (cols : LtCols (ZMod p)) : Prop :=
  cols.adapter_cols.is_trusted = cols.is_slt + cols.is_sltu ∧
  cols.is_slt + cols.is_sltu = 1

/-- Soundness collapses to a single application of the structural
mirror lemma `formalSpec_of_subcircuit_specs` (`Lemmas.lean`) once
`circuit_proof_start` peels back the Clean elaboration plumbing. -/
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e_adapter, e_is_slt, e_is_sltu, e_ltop, e_ac⟩ := h_input
  subst_eqs
  obtain ⟨h_trusted, h_is_real_sum⟩ := h_assumptions
  obtain ⟨h_ltop_sub, h_cpu_sub, h_alu_sub, h_is_slt_bin, h_is_sltu_bin,
          h_sum_bin, h_op_a_0⟩ := h_holds
  unfold id at *
  -- `circuit_proof_start` normalizes `x - 1` to `x + -1` in the binarity
  -- gates; bridge each with `linear_combination` in the call site.
  refine formalSpec_of_subcircuit_specs _ h_is_real_sum h_trusted
    h_ltop_sub (h_cpu_sub trivial) (h_alu_sub trivial)
    ?_ ?_ ?_ h_op_a_0
  · linear_combination h_is_slt_bin
  · linear_combination h_is_sltu_bin
  · linear_combination h_sum_bin

/-- Completeness. Now provable since `FormalSpec` *is* the structural
bundle: `subcircuit_specs_of_formalSpec` unbundles `h_spec` into the
three sub-circuit Specs + the 3 binary gates + `op_a_0`, then each gated
sub-assertion is re-wrapped as `⟨its-Assumptions, its-Spec⟩` and each
scalar gate re-stated in the `x + -1` normal form. The `LtSignedOp`
sub-assumptions (is_real binary / is_signed binary / padding-unsigned)
are discharged from the binary gates + selector arithmetic. -/
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e_adapter, e_is_slt, e_is_sltu, e_ltop, e_ac⟩ := h_input
  subst_eqs
  obtain ⟨h_trusted, h_is_real_sum⟩ := h_assumptions
  unfold id at *
  obtain ⟨h_ltop, h_cpu, h_alu, h_slt_bin, h_sltu_bin, h_sum_bin, h_op_a_0⟩ :=
    subcircuit_specs_of_formalSpec _ h_is_real_sum h_trusted h_spec
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hbin : ∀ x : ZMod p, x * (x - 1) = 0 → (x = 0 ∨ x = 1) := fun x h => by
    binary_iff (by linear_combination h : x * (x + -1) = 0)
  have h_slt_or := hbin _ h_slt_bin
  have h_sltu_or := hbin _ h_sltu_bin
  have h_sum_or := hbin _ h_sum_bin
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have h2lt : (2 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    have h2val : (2 : ZMod p).val = 2 := ZMod.val_natCast_of_lt h2lt
    intro heq; rw [heq, ZMod.val_zero] at h2val; omega
  -- `LtSignedOp.assertionGated`: ⟨its-Assumptions, its-Spec⟩; the Assumptions
  -- type is inferred from the goal. Padding-unsigned uses selector arithmetic.
  refine ⟨⟨⟨h_sum_or, h_slt_or, fun h_ir0 => ?_⟩, h_ltop⟩,
          ⟨trivial, h_cpu⟩, ⟨trivial, h_alu⟩, ?_, ?_, ?_, h_op_a_0⟩
  · -- `h_ir0 : is_real = 0` (is_real = is_slt + is_sltu); the gated input's
    -- `is_real` projection is defeq to the sum, so `h_ir0` re-types as it.
    have hsum : Expression.eval env.toEnvironment input_var_is_slt +
        Expression.eval env.toEnvironment input_var_is_sltu = 0 := h_ir0
    rcases h_slt_or with h | h
    · exact h
    · exfalso
      dsimp only at h
      rcases h_sltu_or with h' | h'
      · dsimp only at h'
        rw [h, h'] at hsum
        exact absurd (by linear_combination hsum : (1 : ZMod p) = 0) one_ne_zero
      · dsimp only at h'
        rw [h, h'] at hsum
        exact absurd (by linear_combination hsum : (2 : ZMod p) = 0) h2ne
  · linear_combination h_slt_bin
  · linear_combination h_sltu_bin
  · linear_combination h_sum_bin

end Assertion

/-- The full Clean `FormalAssertion` for `LtChip`'s R-type variants. -/
def assertion : FormalAssertion (ZMod p) LtCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.Lt
