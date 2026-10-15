module

public import SP1Clean.Semantics.Specs.U16toU8Safe
public import SP1Clean.Math.Bitwise
public import SP1Clean.Model.Channels
public import SP1Clean.Model.ByteTable
public import Clean.Circuit.Subcircuit
import Clean.Utils.Tactics.CircuitProofStart

/-! # Safe byte-decomposition gadget

Four gated byte-channel pulls certify the low/high decomposition of four 16-bit limbs.
The low-byte witness constructor and bundled assertion share the pure decomposition contract.
`RawSpec` remains implementation evidence for transitional Rust faithfulness.
-/

@[expose] public section

namespace SP1Clean.U16toU8OperationSafe

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The literal meaning of SP1's `U16toU8OperationSafe` constraint list at `is_real = 1`: each
low byte and each derived high byte `(u16_values[i] - low_bytes[i]) * 256⁻¹` is a genuine byte. -/
def RawSpec (u16_values : Vector (ZMod p) 4) (cols : Circuits.Types.U16toU8Operation (ZMod p)) : Prop :=
  (cols.low_bytes[0].val < 256 ∧ ((u16_values[0] - cols.low_bytes[0]) * 256⁻¹).val < 256) ∧
  (cols.low_bytes[1].val < 256 ∧ ((u16_values[1] - cols.low_bytes[1]) * 256⁻¹).val < 256) ∧
  (cols.low_bytes[2].val < 256 ∧ ((u16_values[2] - cols.low_bytes[2]) * 256⁻¹).val < 256) ∧
  (cols.low_bytes[3].val < 256 ∧ ((u16_values[3] - cols.low_bytes[3]) * 256⁻¹).val < 256)

/-- The high byte `(u - (u.val % 256)) * 256⁻¹` of a 16-bit value is itself a byte. -/
lemma high_byte_lt (u : ZMod p) (hu : u.val < 2 ^ 16) :
    ((u - ((u.val % 256 : ℕ) : ZMod p)) * (256 : ZMod p)⁻¹).val < 2 ^ 8 := by
  have hp : 2 ^ 17 < p := Fact.out
  have key : ((u.val % 256 : ℕ) : ZMod p) + ((256 * (u.val / 256) : ℕ) : ZMod p) = u := by
    rw [← Nat.cast_add, show u.val % 256 + 256 * (u.val / 256) = u.val from by omega,
      ZMod.natCast_zmod_val]
  have hdiff : u - ((u.val % 256 : ℕ) : ZMod p) = ((256 * (u.val / 256) : ℕ) : ZMod p) := by
    linear_combination -key
  rw [hdiff]
  have hcollapse : ((256 * (u.val / 256) : ℕ) : ZMod p) * (256 : ZMod p)⁻¹
      = ((u.val / 256 : ℕ) : ZMod p) := by
    push_cast
    rw [mul_comm (256 : ZMod p) ((u.val / 256 : ℕ) : ZMod p), mul_assoc,
      mul_inv_cancel₀ val_256_ne_zero, mul_one]
  rw [hcollapse, ZMod.val_natCast_of_lt (by omega : u.val / 256 < p)]
  omega

/-! ## The witnessed `FormalCircuit` -/

/-- The witness assignment (trace generation): each low byte is `u16_values[i] % 256` (the `% 256`
makes it a genuine byte unconditionally). Mirrors SP1's `populate_u16_to_u8_safe`. -/
def populate (u16_values : Word (ZMod p)) : Circuits.Types.U16toU8Operation (ZMod p) :=
  ⟨#v[((u16_values[0].val % 256 : ℕ) : ZMod p), ((u16_values[1].val % 256 : ℕ) : ZMod p),
      ((u16_values[2].val % 256 : ℕ) : ZMod p), ((u16_values[3].val % 256 : ℕ) : ZMod p)]⟩

/-- SP1's `U16toU8OperationSafe::eval`: four `is_real`-gated byte pulls over the given low bytes.
Witnesses nothing (the column struct is an input). -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let u16_values := input.u16_values
  let cols := input.cols
  let is_real := input.is_real
  byteChannel.pullIf is_real
    (⟨3, 0, cols.low_bytes[0], (u16_values[0] - cols.low_bytes[0]) * (256 : ZMod p)⁻¹⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf is_real
    (⟨3, 0, cols.low_bytes[1], (u16_values[1] - cols.low_bytes[1]) * (256 : ZMod p)⁻¹⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf is_real
    (⟨3, 0, cols.low_bytes[2], (u16_values[2] - cols.low_bytes[2]) * (256 : ZMod p)⁻¹⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf is_real
    (⟨3, 0, cols.low_bytes[3], (u16_values[3] - cols.low_bytes[3]) * (256 : ZMod p)⁻¹⟩ : ByteRow (Expression (ZMod p)))
  assertZero (is_real * (is_real - 1))

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

set_option linter.unusedSimpArgs false in
/-- `populate u16_values` satisfies the gadget `Spec` for any `is_real`. The composing op uses this
to discharge its assertion obligation. -/
theorem spec_populate {u16_values : Word (ZMod p)}
    (h0 : u16_values[0].val < 2 ^ 16) (h1 : u16_values[1].val < 2 ^ 16)
    (h2 : u16_values[2].val < 2 ^ 16) (h3 : u16_values[3].val < 2 ^ 16) (is_real : ZMod p) :
    Spec (⟨u16_values, populate u16_values, is_real⟩ : Inputs (ZMod p)) := by
  have hp256 : (256 : ℕ) < p := by
    have := Fact.out (p := 2 ^ 17 < p); omega
  have lowlt : ∀ (u : ZMod p), (((u.val % 256 : ℕ) : ZMod p)).val < 256 := fun u => by
    rw [ZMod.val_natCast_of_lt (by omega : u.val % 256 < p)]; omega
  intro _ i
  fin_cases i <;>
    simp only [populate, Spec, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
  · exact ⟨lowlt _, high_byte_lt _ h0, reassemble _ _⟩
  · exact ⟨lowlt _, high_byte_lt _ h1, reassemble _ _⟩
  · exact ⟨lowlt _, high_byte_lt _ h2, reassemble _ _⟩
  · exact ⟨lowlt _, high_byte_lt _ h3, reassemble _ _⟩

-- Keep the input/column evaluation projections factored; both proofs fit the default budget.
theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  have hbin := h_assumptions
  obtain ⟨hiu, hicols, _⟩ := h_input
  have e8 : (2 : ℕ) ^ 8 = 256 := by norm_num
  have ea : ∀ (i : ℕ) (hi : i < 4),
      Expression.eval env input_var_u16_values[i] = input_u16_values[i] := by
    intro i hi; rw [← hiu]; simp only [Vector.getElem_map]
  have el : ∀ (i : ℕ) (hi : i < 4),
      Expression.eval env input_var_cols_low_bytes[i] = input_cols_low_bytes[i] := by
    intro i hi; rw [← hicols]; simp only [Vector.getElem_map]
  simp only [circuit_norm, byteChannel, ea, el] at h_holds ⊢
  obtain ⟨hr0, hr1, hr2, hr3, _hbool⟩ := h_holds
  -- The four trailing conjuncts are the byte pulls' own `Requirements` — vacuous off-gate.
  refine ⟨fun hr1eq => ?_, fun h1 h0 => off_gate_vacuous hbin h1 h0,
    fun h1 h0 => off_gate_vacuous hbin h1 h0, fun h1 h0 => off_gate_vacuous hbin h1 h0,
    fun h1 h0 => off_gate_vacuous hbin h1 h0⟩
  have hneg : - input_is_real = -1 := by rw [hr1eq]
  have R0 := hr0 hneg; have R1 := hr1 hneg; have R2 := hr2 hneg; have R3 := hr3 hneg
  rw [byteRowSpec_u8range_pair, e8] at R0 R1 R2 R3
  intro i
  fin_cases i
  · exact ⟨R0.1, R0.2, reassemble _ _⟩
  · exact ⟨R1.1, R1.2, reassemble _ _⟩
  · exact ⟨R2.1, R2.2, reassemble _ _⟩
  · exact ⟨R3.1, R3.2, reassemble _ _⟩

theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  have hbin := h_assumptions
  obtain ⟨hiu, hicols, _⟩ := h_input
  have e8 : (2 : ℕ) ^ 8 = 256 := by norm_num
  have ea : ∀ (i : ℕ) (hi : i < 4),
      Expression.eval env.toEnvironment input_var_u16_values[i] = input_u16_values[i] := by
    intro i hi; rw [← hiu]; simp only [Vector.getElem_map]
  have el : ∀ (i : ℕ) (hi : i < 4),
      Expression.eval env.toEnvironment input_var_cols_low_bytes[i] = input_cols_low_bytes[i] := by
    intro i hi; rw [← hicols]; simp only [Vector.getElem_map]
  simp only [circuit_norm, byteChannel, ea, el]
  refine ⟨?_, ?_, ?_, ?_, by rcases hbin with h | h <;> rw [h] <;> simp⟩
  all_goals intro hneg
  all_goals have hsp := h_spec (neg_inj.mp hneg)
  all_goals rw [byteRowSpec_u8range_pair, e8]
  · exact ⟨(hsp 0).1, (hsp 0).2.1⟩
  · exact ⟨(hsp 1).1, (hsp 1).2.1⟩
  · exact ⟨(hsp 2).1, (hsp 2).2.1⟩
  · exact ⟨(hsp 3).1, (hsp 3).2.1⟩

/-- SP1's `U16toU8OperationSafe::eval` as a Clean-native `FormalAssertion`: `is_real`-gated byte-bus
range checks over the `populate`d low bytes, no fresh witnesses (the column struct is an input). -/
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
@[circuit_norm] lemma channelsWithRequirements_eq :
    (circuit (p := p)).channelsWithRequirements = [] := rfl

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    (circuit (p := p)).localLength x = 0 := rfl

end SP1Clean.U16toU8OperationSafe
