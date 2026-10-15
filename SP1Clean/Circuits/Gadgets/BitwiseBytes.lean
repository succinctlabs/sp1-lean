module

public import SP1Clean.Semantics.Specs.BitwiseBytes
public import SP1Clean.Model.ByteTable
public import SP1Clean.Model.Channels
public import Clean.Circuit.Subcircuit
import SP1Clean.Math.Gate
import Clean.Utils.Tactics.CircuitProofStart
import Mathlib.Tactic.FinCases

/-! # Bundled bytewise bitwise gadget

Eight byte-channel pulls certify AND/OR/XOR. Witness construction and the formal assertion
share one contract; operand bounds are obtained from active lookups.
-/

@[expose] public section

namespace SP1Clean.BitwiseOperation

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Native port of SP1's `BitwiseOperation` result column: each result byte is `byteOp opcode a b`. -/
def populate (a b : Vector (ZMod p) 8) (opcode : ZMod p) : Columns (ZMod p) :=
  ⟨#v[((byteOp opcode.val a[0].val b[0].val : ℕ) : ZMod p),
      ((byteOp opcode.val a[1].val b[1].val : ℕ) : ZMod p),
      ((byteOp opcode.val a[2].val b[2].val : ℕ) : ZMod p),
      ((byteOp opcode.val a[3].val b[3].val : ℕ) : ZMod p),
      ((byteOp opcode.val a[4].val b[4].val : ℕ) : ZMod p),
      ((byteOp opcode.val a[5].val b[5].val : ℕ) : ZMod p),
      ((byteOp opcode.val a[6].val b[6].val : ℕ) : ZMod p),
      ((byteOp opcode.val a[7].val b[7].val : ℕ) : ZMod p)]⟩

/-- The witnessed result bytes `populate a b opcode` satisfy the gadget `Spec` for any `is_real`, given
the operand bytes are genuine bytes and the opcode is one of AND/OR/XOR. The composing
`BitwiseU16Operation` uses this to discharge its `assertion BitwiseOperation.circuit` prover obligation. -/
theorem spec_populate {a b : Vector (ZMod p) 8} {opcode : ZMod p}
    (hbytes : ∀ i : Fin 8, a[(i : ℕ)].val < 256 ∧ b[(i : ℕ)].val < 256) (_hopcode : opcode.val < 3)
    (is_real : ZMod p) :
    Spec (⟨a, b, populate a b opcode, opcode, is_real⟩ : Inputs (ZMod p)) := by
  have hp : 2 ^ 17 < p := Fact.out
  have hb256 : (256 : ℕ) < p := by omega
  intro _
  have hres : ∀ i : Fin 8,
      (populate a b opcode).result[(i : ℕ)].val
        = byteOp opcode.val a[(i : ℕ)].val b[(i : ℕ)].val := by
    intro i
    have hi := hbytes i
    fin_cases i <;>
      simp only [populate, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ] <;>
      exact ZMod.val_natCast_of_lt (lt_trans (byteOp_lt256 _ _ _ hi.1 hi.2) hb256)
  exact ⟨hbytes, bitwise_of_byteOp (a := a) (b := b) hres⟩

/-- Eight gated byte lookups and the binary row gate. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let a := input.a
  let b := input.b
  let cols := input.cols
  let opcode := input.opcode
  let is_real := input.is_real
  byteChannel.pullIf is_real (⟨opcode, cols.result[0], a[0], b[0]⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf is_real (⟨opcode, cols.result[1], a[1], b[1]⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf is_real (⟨opcode, cols.result[2], a[2], b[2]⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf is_real (⟨opcode, cols.result[3], a[3], b[3]⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf is_real (⟨opcode, cols.result[4], a[4], b[4]⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf is_real (⟨opcode, cols.result[5], a[5], b[5]⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf is_real (⟨opcode, cols.result[6], a[6], b[6]⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf is_real (⟨opcode, cols.result[7], a[7], b[7]⟩ : ByteRow (Expression (ZMod p)))
  assertZero (is_real * (is_real - 1))

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main := by
  elaborate_circuit_with {
    channelsWithGuarantees := [byteChannel.toRaw]
  }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [byteChannel.toRaw] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hopcode, hbin⟩ := h_assumptions
  obtain ⟨hia, hib, hir, _, _⟩ := h_input
  have ea : ∀ i (hi : i < 8), Expression.eval env input_var_a[i] = input_a[i] := by
    intro i hi; rw [← hia]; simp only [Vector.getElem_map]
  have eb : ∀ i (hi : i < 8), Expression.eval env input_var_b[i] = input_b[i] := by
    intro i hi; rw [← hib]; simp only [Vector.getElem_map]
  have er : ∀ i (hi : i < 8),
      Expression.eval env input_var_cols_result[i] = input_cols_result[i] := by
    intro i hi; rw [← hir]; simp only [Vector.getElem_map]
  simp only [circuit_norm, byteChannel, ea, eb, er] at h_holds ⊢
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, _hbool⟩ := h_holds
  -- The eight trailing conjuncts are the byte pulls' own `Requirements` — vacuous off-gate.
  refine ⟨fun h1 => ?_, fun h1 h0 => off_gate_vacuous hbin h1 h0,
    fun h1 h0 => off_gate_vacuous hbin h1 h0, fun h1 h0 => off_gate_vacuous hbin h1 h0,
    fun h1 h0 => off_gate_vacuous hbin h1 h0, fun h1 h0 => off_gate_vacuous hbin h1 h0,
    fun h1 h0 => off_gate_vacuous hbin h1 h0, fun h1 h0 => off_gate_vacuous hbin h1 h0,
    fun h1 h0 => off_gate_vacuous hbin h1 h0⟩
  have hneg : - input_is_real = -1 := by rw [h1]
  -- The byte table guarantees each fired send's operands are bytes and `result = byteOp`.
  have H : ∀ i : Fin 8,
      (input_cols_result[(i : ℕ)].val < 256 ∧ input_a[(i : ℕ)].val < 256 ∧ input_b[(i : ℕ)].val < 256) ∧
        input_cols_result[(i : ℕ)].val
          = byteOp input_opcode.val input_a[(i : ℕ)].val input_b[(i : ℕ)].val := by
    have B := fun {r a b : ZMod p} => (byteRowSpec_byteOp (p := p) r a b hopcode).mp
    intro i
    fin_cases i
    exacts [B (hg0 hneg), B (hg1 hneg), B (hg2 hneg), B (hg3 hneg),
      B (hg4 hneg), B (hg5 hneg), B (hg6 hneg), B (hg7 hneg)]
  exact ⟨fun i => ⟨(H i).1.2.1, (H i).1.2.2⟩,
    bitwise_of_byteOp (a := input_a) (b := input_b) (fun i => (H i).2)⟩

theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hopcode, hbin⟩ := h_assumptions
  obtain ⟨hia, hib, hir, _, _⟩ := h_input
  have hp : 2 ^ 17 < p := Fact.out
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
  refine ⟨fun hn => key (neg_inj.mp hn) 0, fun hn => key (neg_inj.mp hn) 1,
    fun hn => key (neg_inj.mp hn) 2, fun hn => key (neg_inj.mp hn) 3,
    fun hn => key (neg_inj.mp hn) 4, fun hn => key (neg_inj.mp hn) 5,
    fun hn => key (neg_inj.mp hn) 6, fun hn => key (neg_inj.mp hn) 7, ?_⟩
  rcases hbin with h | h <;> rw [h] <;> simp

/-- The `BitwiseOperation` gadget as a Clean-native `FormalAssertion`: `is_real`- and opcode-gated
semantic spec, byte-bus AND/OR/XOR pulls, witnessing nothing. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness,
    channelsWithRequirements := [],
    requirementsChannelsLawful := fun input_var i₀ => by
      preserve_tactic_target
      simp only [circuit_norm, main, byteChannel]; grind }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.BitwiseOperation
