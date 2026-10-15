module

public import SP1Clean.Circuits.Gadgets.Bitwise.Witness
public import Clean.Circuit.Subcircuit
public import Clean.Gadgets.Equality
import Clean.Utils.Tactics.CircuitProofStart

/-! # Bundled word-level bitwise gadget

Pure byte decomposition feeds the bundled bytewise assertion. Soundness and completeness
use the complete byte certificate, including unrestricted padding columns.
-/

@[expose] public section

namespace SP1Clean.BitwiseU16Operation

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- SP1's `BitwiseU16Operation::eval` as a `FormalAssertion`: the `is_real` binary gate plus the
composed `BitwiseOperation.circuit` on the two byte decompositions. Witnesses nothing. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let b := input.b
  let c := input.c
  let lb := input.cols.b_low_bytes.low_bytes
  let lc := input.cols.c_low_bytes.low_bytes
  input.is_real * (input.is_real - 1) === 0
  assertion BitwiseOperation.circuit
    (⟨#v[lb[0], (b[0] - lb[0]) * (256 : ZMod p)⁻¹, lb[1], (b[1] - lb[1]) * (256 : ZMod p)⁻¹,
         lb[2], (b[2] - lb[2]) * (256 : ZMod p)⁻¹, lb[3], (b[3] - lb[3]) * (256 : ZMod p)⁻¹],
      #v[lc[0], (c[0] - lc[0]) * (256 : ZMod p)⁻¹, lc[1], (c[1] - lc[1]) * (256 : ZMod p)⁻¹,
         lc[2], (c[2] - lc[2]) * (256 : ZMod p)⁻¹, lc[3], (c[3] - lc[3]) * (256 : ZMod p)⁻¹],
      input.cols.bitwise_operation, input.opcode, input.is_real⟩ :
      Var SP1Clean.BitwiseOperation.Inputs (ZMod p))

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main where
  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := [byteChannel.toRaw]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [byteChannel.toRaw] := rfl

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hop, hbin⟩ := h_assumptions
  obtain ⟨hib, hic, ⟨hilb, hilc, _hires⟩, _hiop, _hireal⟩ := h_input
  have eb : ∀ (k : ℕ) (_ : k < 4), Expression.eval env input_var_b[k] = input_b[k] :=
    fun k _ => by rw [← hib]; simp only [Vector.getElem_map]
  have ec : ∀ (k : ℕ) (_ : k < 4), Expression.eval env input_var_c[k] = input_c[k] :=
    fun k _ => by rw [← hic]; simp only [Vector.getElem_map]
  have elb : ∀ (k : ℕ) (_ : k < 4),
      Expression.eval env input_var_cols_b_low_bytes_low_bytes[k]
        = input_cols_b_low_bytes_low_bytes[k] :=
    fun k _ => by rw [← hilb]; simp only [Vector.getElem_map]
  have elc : ∀ (k : ℕ) (_ : k < 4),
      Expression.eval env input_var_cols_c_low_bytes_low_bytes[k]
        = input_cols_c_low_bytes_low_bytes[k] :=
    fun k _ => by rw [← hilc]; simp only [Vector.getElem_map]
  obtain ⟨_h_gate, h_bw⟩ := h_holds
  have h_spec := h_bw ⟨hop, hbin⟩
  change BitwiseOperation.Spec _ at h_spec
  refine ⟨?_, Or.inr ⟨hop, hbin⟩⟩
  simpa only [decompBytes, eb, ec, elb, elc, ← sub_eq_add_neg] using h_spec

theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hop, hbin⟩ := h_assumptions
  obtain ⟨hib, hic, ⟨hilb, hilc, _hires⟩, _hiop, _hireal⟩ := h_input
  have eb : ∀ (k : ℕ) (_ : k < 4), Expression.eval env.toEnvironment input_var_b[k] = input_b[k] :=
    fun k _ => by rw [← hib]; simp only [Vector.getElem_map]
  have ec : ∀ (k : ℕ) (_ : k < 4), Expression.eval env.toEnvironment input_var_c[k] = input_c[k] :=
    fun k _ => by rw [← hic]; simp only [Vector.getElem_map]
  have elb : ∀ (k : ℕ) (_ : k < 4),
      Expression.eval env.toEnvironment input_var_cols_b_low_bytes_low_bytes[k]
        = input_cols_b_low_bytes_low_bytes[k] :=
    fun k _ => by rw [← hilb]; simp only [Vector.getElem_map]
  have elc : ∀ (k : ℕ) (_ : k < 4),
      Expression.eval env.toEnvironment input_var_cols_c_low_bytes_low_bytes[k]
        = input_cols_c_low_bytes_low_bytes[k] :=
    fun k _ => by rw [← hilc]; simp only [Vector.getElem_map]
  refine ⟨?_, ⟨hop, hbin⟩, ?_⟩
  · rcases hbin with h | h <;> rw [h] <;> simp
  · change BitwiseOperation.Spec _
    simpa only [decompBytes, eb, ec, elb, elc, ← sub_eq_add_neg] using h_spec

/-- SP1's `BitwiseU16Operation::eval` as a Clean-native `FormalAssertion`: the `is_real` binary gate
plus the composed `BitwiseOperation` on the two `U16toU8` byte decompositions, witnessing nothing. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness,
    channelsWithRequirements := [] }

set_option linter.unusedSectionVars false in
/-- Since Lean 4.32, class projections through `ProvableType`-derived instances no longer whnf-reduce
at `.reducible` transparency (Clean `088a9287`), so `circuit_norm` can no longer cross
`circuit.Spec` ↔ `Spec` on its own. Supply the bridge as a rewrite. -/
@[circuit_norm] lemma circuit_Spec_eq : (circuit (p := p)).Spec = Spec := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.BitwiseU16Operation
