import SP1Clean.Native.Operations.BitwiseOperation.RawSpec
import SP1Clean.Native.Operations.BitwiseOperation.Populate

/-! # `BitwiseOperation` — the `FormalAssertion` (soundness / completeness / contract)

SP1's `BitwiseOperation::eval` as a Clean `FormalAssertion`. Emits one
`send_byte(opcode, result[i], a[i], b[i])` per byte; witnesses nothing (result bytes threaded in).
Soundness routes through `RawSpec.bitwise_of_byteOp`. -/

namespace SP1Clean.BitwiseOperation

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Opcode is one of AND/OR/XOR; `is_real` is binary (the latter discharged by the composing
operation's gate).
The operand byte bounds are **not** preconditions: the byte table guarantees them on every fired send,
so soundness exports them through `Spec` (and completeness reads them back from `Spec`), letting a
composing operation feed free byte columns without range-checking them itself. -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  input.opcode.val < 3 ∧ (input.is_real = 0 ∨ input.is_real = 1)

set_option maxHeartbeats 2000000 in
theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hopcode, _hbin⟩ := h_assumptions
  obtain ⟨hia, hib, hir, _, _⟩ := h_input
  have ea : ∀ i (hi : i < 8), Expression.eval env input_var_a[i] = input_a[i] := by
    intro i hi; rw [← hia]; simp only [Vector.getElem_map]
  have eb : ∀ i (hi : i < 8), Expression.eval env input_var_b[i] = input_b[i] := by
    intro i hi; rw [← hib]; simp only [Vector.getElem_map]
  have er : ∀ i (hi : i < 8),
      Expression.eval env input_var_cols_result[i] = input_cols_result[i] := by
    intro i hi; rw [← hir]; simp only [Vector.getElem_map]
  simp only [circuit_norm, byteChannel, ea, eb, er] at h_holds ⊢
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7⟩ := h_holds
  -- post-#398 the byte receives owe no padding requirement, so the goal is exactly `Spec`.
  intro h1
  have hneg : -input_is_real = -1 := by rw [h1]
  have R0 := hg0 hneg; have R1 := hg1 hneg; have R2 := hg2 hneg; have R3 := hg3 hneg
  have R4 := hg4 hneg; have R5 := hg5 hneg; have R6 := hg6 hneg; have R7 := hg7 hneg
  -- The byte table guarantees each fired send's operands are bytes and `result = byteOp`.
  have H : ∀ i : Fin 8,
      (input_cols_result[(i : ℕ)].val < 256 ∧ input_a[(i : ℕ)].val < 256 ∧ input_b[(i : ℕ)].val < 256) ∧
        input_cols_result[(i : ℕ)].val
          = byteOp input_opcode.val input_a[(i : ℕ)].val input_b[(i : ℕ)].val := by
    intro i
    fin_cases i
    · exact (byteRowSpec_byteOp _ _ _ hopcode).mp R0
    · exact (byteRowSpec_byteOp _ _ _ hopcode).mp R1
    · exact (byteRowSpec_byteOp _ _ _ hopcode).mp R2
    · exact (byteRowSpec_byteOp _ _ _ hopcode).mp R3
    · exact (byteRowSpec_byteOp _ _ _ hopcode).mp R4
    · exact (byteRowSpec_byteOp _ _ _ hopcode).mp R5
    · exact (byteRowSpec_byteOp _ _ _ hopcode).mp R6
    · exact (byteRowSpec_byteOp _ _ _ hopcode).mp R7
  exact ⟨fun i => ⟨(H i).1.2.1, (H i).1.2.2⟩,
    bitwise_of_byteOp (a := input_a) (b := input_b) (fun i => (H i).2)⟩

set_option maxHeartbeats 2000000 in
theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hopcode, hbin⟩ := h_assumptions
  obtain ⟨hia, hib, hir, _, _⟩ := h_input
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have ea : ∀ i (hi : i < 8), Expression.eval env.toEnvironment input_var_a[i] = input_a[i] := by
    intro i hi; rw [← hia]; simp only [Vector.getElem_map]
  have eb : ∀ i (hi : i < 8), Expression.eval env.toEnvironment input_var_b[i] = input_b[i] := by
    intro i hi; rw [← hib]; simp only [Vector.getElem_map]
  have er : ∀ i (hi : i < 8),
      Expression.eval env.toEnvironment input_var_cols_result[i] = input_cols_result[i] := by
    intro i hi; rw [← hir]; simp only [Vector.getElem_map]
  have key : input_is_real = 1 → ∀ i : Fin 8,
      ByteRowSpec (⟨input_opcode, input_cols_result[↑i], input_a[↑i], input_b[↑i]⟩ : ByteRow (ZMod p)) := by
    intro hr1 i
    obtain ⟨hb_bounds, hand, hor, hxor⟩ := h_spec hr1
    have hb := hb_bounds i
    have hcast : ((input_opcode.val : ℕ) : ZMod p) = input_opcode := ZMod.natCast_zmod_val _
    have hres : input_cols_result[↑i].val = byteOp input_opcode.val input_a[↑i].val input_b[↑i].val := by
      rcases (show input_opcode.val = 0 ∨ input_opcode.val = 1 ∨ input_opcode.val = 2 from by omega)
        with h | h | h
      · rw [h, byteOp_zero]; exact hand (by rw [← hcast, h]; norm_num) i
      · rw [h, byteOp_one]; exact hor (by rw [← hcast, h]; norm_num) i
      · rw [h, byteOp_two]; exact hxor (by rw [← hcast, h]; norm_num) i
    exact (byteRowSpec_byteOp _ _ _ hopcode).mpr
      ⟨⟨by rw [hres]; exact byteOp_lt256 _ _ _ hb.1 hb.2, hb.1, hb.2⟩, hres⟩
  simp only [circuit_norm, byteChannel, ea, eb, er]
  refine ⟨fun hneg => ?_, fun hneg => ?_, fun hneg => ?_, fun hneg => ?_,
    fun hneg => ?_, fun hneg => ?_, fun hneg => ?_, fun hneg => ?_⟩
  · exact key (neg_inj.mp hneg) 0
  · exact key (neg_inj.mp hneg) 1
  · exact key (neg_inj.mp hneg) 2
  · exact key (neg_inj.mp hneg) 3
  · exact key (neg_inj.mp hneg) 4
  · exact key (neg_inj.mp hneg) 5
  · exact key (neg_inj.mp hneg) 6
  · exact key (neg_inj.mp hneg) 7

/-- The `BitwiseOperation` gadget as a Clean-native `FormalAssertion`: `is_real`- and opcode-gated
semantic spec, byte-bus AND/OR/XOR pulls, witnessing nothing. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.BitwiseOperation
