module

public import SP1Clean.Semantics.Specs.U16Compare
public import SP1Clean.Model.Channels
public import Clean.Gadgets.Equality
import Clean.Utils.Tactics.CircuitProofStart

/-! # Native 16-bit comparison gadget

Witness generation, arithmetic evidence and the bundled `FormalAssertion` live together.
`Semantics/Specs/U16Compare` owns the semantic contract. `RawSpec` is intermediate constraint
evidence used by the local proof and transitional Rust-faithfulness checks.
-/

@[expose] public section

namespace SP1Clean.U16CompareOperation

open Circuit
open SP1Clean.Channels (byteChannel)
open SP1Clean.Circuits.Types

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The literal meaning of SP1's `U16CompareOperation` constraint list at `is_real = 1`: `bit` is
boolean and `(a - b) + bit * 2^16` is a genuine 16-bit value. -/
def RawSpec (a b : ZMod p) (cols : Circuits.Types.U16CompareOperation (ZMod p)) : Prop :=
  (cols.bit = 0 ∨ cols.bit = 1) ∧ (a - b + cols.bit * 65536).val < 2 ^ 16

/-- Soundness core: `bit` boolean + `(a - b + bit·2^16)` a genuine 16-bit value force `bit = (a < b)`. -/
theorem compare_of_raw {a b : ZMod p} {cols : Circuits.Types.U16CompareOperation (ZMod p)}
    (ha : a.val < 2 ^ 16) (hb : b.val < 2 ^ 16) (h_raw : RawSpec a b cols) :
    cols.bit = if a.val < b.val then 1 else 0 := by
  obtain ⟨hbit, hlt⟩ := h_raw
  have hp : 2 ^ 17 < p := Fact.out
  set v := (a - b + cols.bit * 65536).val with hv_def
  have hcong : (v : ZMod p) = a - b + cols.bit * 65536 := by rw [hv_def, ZMod.natCast_zmod_val]
  have ea : ((a.val : ℕ) : ZMod p) = a := ZMod.natCast_zmod_val a
  have eb : ((b.val : ℕ) : ZMod p) = b := ZMod.natCast_zmod_val b
  rcases hbit with h0 | h1
  · rw [h0] at hcong
    have e : ((a.val : ℕ) : ZMod p) = ((b.val + v : ℕ) : ZMod p) := by
      rw [ea]; push_cast; rw [eb]; linear_combination -hcong
    have hnat : a.val = b.val + v := by
      have hval := congrArg ZMod.val e
      rwa [ZMod.val_natCast_of_lt (show a.val < p by omega),
        ZMod.val_natCast_of_lt (show b.val + v < p by omega)] at hval
    rw [h0, if_neg (show ¬ a.val < b.val by omega)]
  · rw [h1] at hcong
    have e : ((a.val + 65536 : ℕ) : ZMod p) = ((b.val + v : ℕ) : ZMod p) := by
      push_cast; rw [ea, eb]; linear_combination -hcong
    have hnat : a.val + 65536 = b.val + v := by
      have hval := congrArg ZMod.val e
      rwa [ZMod.val_natCast_of_lt (show a.val + 65536 < p by omega),
        ZMod.val_natCast_of_lt (show b.val + v < p by omega)] at hval
    rw [h1, if_pos (show a.val < b.val by omega)]

/-- The witness assignment: the strict-less-than indicator. -/
def populate_bit (a b : ZMod p) : ZMod p := if a.val < b.val then 1 else 0

omit [Fact (2 ^ 17 < p)] in
/-- `populate_bit` is always boolean — the composing operation uses this to discharge the gadget's
(ungated) `bit` booleanness obligation on every row. -/
theorem populate_bit_bool (a b : ZMod p) : populate_bit a b = 0 ∨ populate_bit a b = 1 := by
  simp only [populate_bit]; split <;> simp

omit [Fact (2 ^ 17 < p)] in
/-- The witnessed `bit = populate_bit a b` satisfies the gadget `Spec` for any `is_real`. -/
theorem spec_populate {a b : ZMod p} (_ha : a.val < 2 ^ 16) (_hb : b.val < 2 ^ 16) (is_real : ZMod p) :
    Spec (⟨a, b, ⟨populate_bit a b⟩, is_real⟩ : Inputs (ZMod p)) :=
  ⟨populate_bit_bool a b, fun _ => rfl⟩

/-- Check the activity/result bits and send the active arithmetic range check to the byte bus. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let a := input.a
  let b := input.b
  let cols := input.cols
  let is_real := input.is_real
  let E0 := is_real - 1
  let E1 := is_real * E0
  let E2 := cols.bit - 1
  let E3 := cols.bit * E2
  let E4 := a - b
  let E5 := cols.bit * 65536
  let E6 := E4 + E5
  byteChannel.pullIf is_real (⟨6, E6, Expression.const ((16 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))
  assertZero E1
  E3 === 0

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main := by
  elaborate_circuit_with {
    channelsWithGuarantees := [byteChannel.toRaw]
  }

omit [Fact (2 ^ 17 < p)] in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [byteChannel.toRaw] := rfl
omit [Fact (2 ^ 17 < p)] in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hab, hbin⟩ := h_assumptions
  have c16 : ((16 : ℕ) : ZMod p) = (16 : ZMod p) := Nat.cast_ofNat
  simp only [circuit_norm, byteChannel] at h_holds ⊢
  obtain ⟨hr, _hbool, hgc⟩ := h_holds
  refine ⟨⟨bool_of_mul_pred hgc, ?_⟩, fun h1 h0 => off_gate_vacuous hbin h1 h0⟩
  intro hr1eq
  obtain ⟨ha, hb⟩ := hab hr1eq
  have hneg : - input_is_real = -1 := by rw [hr1eq]
  have R := hr hneg
  rw [← c16] at R
  refine compare_of_raw ha hb ?_
  simp only [RawSpec]
  exact ⟨bool_of_mul_pred hgc, (byteRowSpec_range _ sixteen_lt).mp R⟩

theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  have hp : 2 ^ 17 < p := Fact.out
  obtain ⟨hab, hbin⟩ := h_assumptions
  obtain ⟨hbitbool, hbiteq⟩ := h_spec
  have c16 : ((16 : ℕ) : ZMod p) = (16 : ZMod p) := Nat.cast_ofNat
  simp only [circuit_norm, byteChannel]
  refine ⟨?_, ?_, ?_⟩
  · intro hneg
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    obtain ⟨ha, hb⟩ := hab hr1
    have hbit := hbiteq hr1
    rw [← c16]
    apply (byteRowSpec_range _ sixteen_lt).mpr
    rw [hbit]
    by_cases hlt : input_a.val < input_b.val
    · rw [if_pos hlt]
      have hle : input_b.val ≤ input_a.val + 65536 := by omega
      have key : input_a - input_b + (1 : ZMod p) * 65536
          = ((input_a.val + 65536 - input_b.val : ℕ) : ZMod p) := by
        rw [Nat.cast_sub hle]; push_cast [ZMod.natCast_zmod_val]; ring
      rw [key, ZMod.val_natCast_of_lt (show input_a.val + 65536 - input_b.val < p by omega)]; omega
    · rw [if_neg hlt]
      have hle : input_b.val ≤ input_a.val := by omega
      have key : input_a - input_b + (0 : ZMod p) * 65536
          = ((input_a.val - input_b.val : ℕ) : ZMod p) := by
        rw [Nat.cast_sub hle]; push_cast [ZMod.natCast_zmod_val]; ring
      rw [key, ZMod.val_natCast_of_lt (show input_a.val - input_b.val < p by omega)]; omega
  · rcases hbin with h | h <;> rw [h] <;> simp
  · rcases hbitbool with h | h <;> rw [h] <;> simp

/-- The `U16CompareOperation` gadget as a Clean-native `FormalAssertion`. -/
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

@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.U16CompareOperation
