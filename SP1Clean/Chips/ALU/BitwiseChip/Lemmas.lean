import SP1Clean.Chips.ALU.BitwiseChip.Cols
import SP1Operations.Operation.BitwiseU16Operation.BitwiseU16Operation
import SP1Clean.Operations.BitwiseOperation
import SP1Clean.Operations.BitwiseU16Operation
import SP1Clean.Reader.ALUTypeReader
import SP1Chips.Bitwise.Common
import SP1Chips.Bitwise.BitwiseChip

/-! # `BitwiseChip` cols-level lemmas

Mirrors `SP1Clean/Chips/ALU/LtChip/Lemmas.lean`, adapted for the
3-variant (`xor`/`or`/`and`) bitwise chip. The chip's `FormalSpec`
(`Chips/Spec.lean`) is the faithful bundle of the three sub-circuit
Specs (`BitwiseU16Op.Assertion` + `CPUState.Gated` + `ALUTypeReader.Gated`)
plus the selector/sum binarities and `op_a_0 = 0`, NOT a pure-semantic
`RV64.{xor,or,and}` word — exposing the byte-decomposition structurally
is mandatory for completeness (the semantic word doesn't pin the free
`b_low_bytes`/`c_low_bytes` witnesses).

- `fromMain_toMain` — `fromMain (toMain cols) = cols` round-trip,
  conditional on the UserMode TrustMode marker.
- `formalSpec_of_subcircuit_specs` — soundness midpoint: bundle the
  per-sub-circuit Specs into `FormalSpec`.
- `subcircuit_specs_of_formalSpec` — completeness midpoint: unbundle.

NOTE: the `allHold_iff_structural` bridge to `(_root_.Bitwise.constraints
Main).allHold` (the basis for a real Sail-equivalence `SailBridge`, à la
`SP1Clean.Lt.allHold_iff_structural`) is not yet ported. It is blocked
only on a `Nat.cast`-vs-`OfNat` literal-normalization issue between the
auto-generated `Bitwise.allHold_constraints_iff` (which emits opcode
literals as `↑2, ↑3, ↑4`) and `BitwiseU16Op.iff_sp1` / the reader
`Spec_iff_sp1` bridges — not on any missing mathematics. The chip-level
`FormalAssertion` (soundness + completeness) is complete without it. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Bitwise

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
/-- `fromMain` is a left inverse of `toMain` (cols → Main → cols
round-trip), conditional on the UserMode TrustMode marker
`cols.adapter_cols.is_trusted = cols.is_xor + cols.is_or + cols.is_and`. -/
lemma fromMain_toMain (cols : BitwiseCols (ZMod p))
    (h_trusted_eq_sum :
      cols.adapter_cols.is_trusted = cols.is_xor + cols.is_or + cols.is_and) :
    fromMain (toMain cols) = cols := by
  rcases cols with ⟨state, adapter, bitwise_operation, is_xor, is_or, is_and, adapter_cols⟩
  rcases bitwise_operation with ⟨⟨b_low⟩, ⟨c_low⟩, ⟨result⟩⟩
  have h : adapter_cols.is_trusted = is_xor + is_or + is_and := by simpa using h_trusted_eq_sum
  simp [h, BitwiseCols.ext_iff, CPUState.ext_iff, ALUTypeReader.ext_iff,
    MemoryAccessInSharedCols.ext_iff, UserModeReaderCols.ext_iff,
    BitwiseU16Operation.ext_iff, U16toU8Operation.ext_iff, BitwiseOperation.ext_iff]
  refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    (simp [Array.ext_iff]; intro i hi; interval_cases i <;> simp)

omit [Fact (2 ^ 17 < p)] in
/-- Boolean-from-binary-gate helper. -/
private lemma bin_of_gate (x : ZMod p) (h : x * (x - 1) = 0) : x = 0 ∨ x = 1 := by
  binary_iff (by linear_combination h : x * (x + -1) = 0)

/-- **Forward** (soundness midpoint): assemble the chip-level structural
`FormalSpec` from the per-sub-circuit Specs returned by `circuit_proof_start`.
`BitwiseU16Op` carries no `Assumptions`, so the three sub-Specs feed in
directly; only the three selector + sum `x*(x-1)=0` gates are converted
to disjunctions. -/
lemma formalSpec_of_subcircuit_specs
    (cols : BitwiseCols (ZMod p))
    (h_bw : SP1Clean.BitwiseU16Op.Assertion.Spec
        ⟨cols.adapter.op_b_memory.prev_value, cols.adapter.op_c_memory.prev_value,
         cols.bitwise_operation.b_low_bytes.low_bytes,
         cols.bitwise_operation.c_low_bytes.low_bytes,
         cols.bitwise_operation.bitwise_operation.result,
         cols.is_xor * 2 + cols.is_or * 1 + cols.is_and * 0,
         cols.is_xor + cols.is_or + cols.is_and⟩)
    (h_cpu : SP1Clean.CPUState.Gated.Assertion.Spec
        ⟨cols.state, #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
         8, cols.is_xor + cols.is_or + cols.is_and⟩)
    (h_alu : SP1Clean.ALUTypeReader.Gated.Assertion.Spec
        ⟨cols.state.clk_high,
         cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
         cols.is_xor * 3 + cols.is_or * 4 + cols.is_and * 5,
         cols.state.pc,
         #v[cols.bitwise_operation.bitwise_operation.result[0] +
              cols.bitwise_operation.bitwise_operation.result[1] * 256,
            cols.bitwise_operation.bitwise_operation.result[2] +
              cols.bitwise_operation.bitwise_operation.result[3] * 256,
            cols.bitwise_operation.bitwise_operation.result[4] +
              cols.bitwise_operation.bitwise_operation.result[5] * 256,
            cols.bitwise_operation.bitwise_operation.result[6] +
              cols.bitwise_operation.bitwise_operation.result[7] * 256],
         cols.adapter,
         cols.is_xor + cols.is_or + cols.is_and,
         cols.adapter_cols.is_trusted⟩)
    (h_is_xor_bin : cols.is_xor * (cols.is_xor - 1) = 0)
    (h_is_or_bin : cols.is_or * (cols.is_or - 1) = 0)
    (h_is_and_bin : cols.is_and * (cols.is_and - 1) = 0)
    (h_sum_bin : (cols.is_xor + cols.is_or + cols.is_and) *
                    (cols.is_xor + cols.is_or + cols.is_and - 1) = 0)
    (h_op_a_0 : cols.adapter.op_a_0 = 0) :
    Assertion.FormalSpec cols :=
  ⟨h_bw, h_cpu, h_alu, bin_of_gate _ h_is_xor_bin, bin_of_gate _ h_is_or_bin,
   bin_of_gate _ h_is_and_bin, bin_of_gate _ h_sum_bin, h_op_a_0⟩

/-- **Backward** (completeness midpoint): peel the chip-level structural
`FormalSpec` apart into per-sub-circuit `Spec`s. Trivial now that
`FormalSpec` *is* the bundle. -/
lemma subcircuit_specs_of_formalSpec
    (cols : BitwiseCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols) :
    SP1Clean.BitwiseU16Op.Assertion.Spec
        ⟨cols.adapter.op_b_memory.prev_value, cols.adapter.op_c_memory.prev_value,
         cols.bitwise_operation.b_low_bytes.low_bytes,
         cols.bitwise_operation.c_low_bytes.low_bytes,
         cols.bitwise_operation.bitwise_operation.result,
         cols.is_xor * 2 + cols.is_or * 1 + cols.is_and * 0,
         cols.is_xor + cols.is_or + cols.is_and⟩ ∧
    SP1Clean.CPUState.Gated.Assertion.Spec
        ⟨cols.state, #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
         8, cols.is_xor + cols.is_or + cols.is_and⟩ ∧
    SP1Clean.ALUTypeReader.Gated.Assertion.Spec
        ⟨cols.state.clk_high,
         cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
         cols.is_xor * 3 + cols.is_or * 4 + cols.is_and * 5,
         cols.state.pc,
         #v[cols.bitwise_operation.bitwise_operation.result[0] +
              cols.bitwise_operation.bitwise_operation.result[1] * 256,
            cols.bitwise_operation.bitwise_operation.result[2] +
              cols.bitwise_operation.bitwise_operation.result[3] * 256,
            cols.bitwise_operation.bitwise_operation.result[4] +
              cols.bitwise_operation.bitwise_operation.result[5] * 256,
            cols.bitwise_operation.bitwise_operation.result[6] +
              cols.bitwise_operation.bitwise_operation.result[7] * 256],
         cols.adapter,
         cols.is_xor + cols.is_or + cols.is_and,
         cols.adapter_cols.is_trusted⟩ ∧
    cols.is_xor * (cols.is_xor - 1) = 0 ∧
    cols.is_or * (cols.is_or - 1) = 0 ∧
    cols.is_and * (cols.is_and - 1) = 0 ∧
    (cols.is_xor + cols.is_or + cols.is_and) *
      (cols.is_xor + cols.is_or + cols.is_and - 1) = 0 ∧
    cols.adapter.op_a_0 = 0 := by
  obtain ⟨h_bw, h_cpu, h_alu, h_xor_or, h_or_or, h_and_or, h_sum_or, h_op_a_0⟩ := h_spec
  refine ⟨h_bw, h_cpu, h_alu, ?_, ?_, ?_, ?_, h_op_a_0⟩
  · rcases h_xor_or with h | h <;> rw [h] <;> ring
  · rcases h_or_or with h | h <;> rw [h] <;> ring
  · rcases h_and_or with h | h <;> rw [h] <;> ring
  · rcases h_sum_or with h | h <;> rw [h] <;> ring

end SP1Clean.Bitwise
