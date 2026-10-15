module

public import SP1Clean.Semantics.Specs.U16MSB
public import SP1Clean.Model.Channels
public import Clean.Gadgets.Equality
import Clean.Utils.Tactics.CircuitProofStart

/-! # Native 16-bit high-bit gadget

Witness generation, arithmetic evidence and the bundled `FormalAssertion` live together.
`Semantics/Specs/U16MSB` owns the semantic contract. `RawSpec` is intermediate constraint
evidence used by the local proof and transitional Rust-faithfulness checks.
-/

@[expose] public section

namespace SP1Clean.U16MSBOperation

open Circuit
open SP1Clean.Channels (byteChannel)
open SP1Clean.Circuits.Types

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

instance : Fact (p > 2) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- The booleanness + range form of the msb constraint (the literal meaning of the extracted
constraint list at `is_real = 1`), stated against the result column `cols.msb`. The range term
`2 * a - cols.msb * 65536` is `2*a - msb*2^16` (the native `main`'s normal form). -/
def RawSpec (a : ZMod p) (cols : Circuits.Types.U16MSBOperation (ZMod p)) : Prop :=
  (cols.msb = 0 ∨ cols.msb = 1) ∧ (2 * a - cols.msb * 65536).val < 2 ^ 16

/-- Forward (soundness) core: booleanness + range force `msb` to be the high bit of `a`. -/
theorem msb_of_raw {a : ZMod p} {cols : Circuits.Types.U16MSBOperation (ZMod p)}
    (ha : a.val < 2 ^ 16) (h_raw : RawSpec a cols) :
    cols.msb = if a.val ≥ 32768 then 1 else 0 := by
  have hp : 2 ^ 17 < p := Fact.out
  obtain ⟨hbool, hr⟩ := h_raw
  have h2 : (2 * a : ZMod p).val = 2 * a.val := by
    rw [two_mul, ZMod.val_add_of_lt (by omega)]; omega
  rcases hbool with h0 | h1
  · rw [h0] at hr ⊢
    simp only [zero_mul, sub_zero] at hr
    rw [h2] at hr
    rw [if_neg (by omega)]
  · rw [h1] at hr ⊢
    simp only [one_mul] at hr
    have hge : a.val ≥ 32768 := by
      have hsum : (2 * a - 65536 : ZMod p) + 65536 = 2 * a := by ring
      have hbound : (2 * a - 65536 : ZMod p).val + (65536 : ZMod p).val < p := by
        rw [val_65536_zmod_p]; omega
      have hval := ZMod.val_add_of_lt hbound
      rw [hsum, h2, val_65536_zmod_p] at hval
      omega
    rw [if_pos hge]

/-- SP1's `eval_msb` witness: the high bit of `a` (`a.val / 2^15`). -/
def populate_msb (a : ZMod p) : ZMod p := ((a.val / 32768 : ℕ) : ZMod p)

omit [Fact (2 ^ 17 < p)] in
/-- The closed form of the witness: the `2^15` division is the high-bit indicator. Both the
booleanness lemma and the `Spec` obligation are instances of this one case split. -/
private lemma populate_msb_eq {a : ZMod p} (ha : a.val < 2 ^ 16) :
    populate_msb a = if a.val ≥ 32768 then 1 else 0 := by
  simp only [populate_msb]
  by_cases hge : a.val ≥ 32768
  · rw [if_pos hge, show a.val / 32768 = 1 by omega, Nat.cast_one]
  · rw [if_neg hge, show a.val / 32768 = 0 by omega, Nat.cast_zero]

omit [Fact (2 ^ 17 < p)] in
/-- `populate_msb` is always boolean (for a genuine 16-bit `a`) — the composing operation uses this to
discharge the gadget's (now unconditional) `msb` booleanness obligation on every row. -/
theorem populate_msb_bool {a : ZMod p} (ha : a.val < 2 ^ 16) :
    populate_msb a = 0 ∨ populate_msb a = 1 := by
  rw [populate_msb_eq ha]; split <;> simp

omit [Fact (2 ^ 17 < p)] in
/-- `populate_msb a` satisfies the gadget `Spec` for any `is_real`. The composing operation uses this
to discharge its assertion obligation. -/
theorem spec_populate {a : ZMod p} (ha : a.val < 2 ^ 16) (is_real : ZMod p) :
    Spec (⟨a, ⟨populate_msb a⟩, is_real⟩ : Inputs (ZMod p)) :=
  ⟨populate_msb_bool ha, fun _ => populate_msb_eq ha⟩

/-! ## Witness IR

The exportable `FExpr` twin of `populate_msb`, for composition into the witness-IR programs of the
operations that thread a high bit (`Lt`'s sign compare, `Mul`'s sign extension, the shift chips'
operand msbs). Deliberately **not** `@[circuit_norm]` — consumers name it in their `simp only` sets
beside their own `populateIR` (the opacity doctrine, see `AddOperation/Populate.lean`). -/

/-- The `FExpr` twin of `populate_msb`: the high bit of a 16-bit operand, as the u64-sort division
`x.val / 2^15`. -/
def populate_msbF (x : Witgen.FExpr (ZMod p)) : Witgen.FExpr (ZMod p) :=
  (x.val / 32768).toField

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating the `FExpr` twin is exactly `populate_msb` on the evaluated operand. The 16-bit
bound keeps the u64-sorted `val` from wrapping, so the IR's division agrees with `populate_msb`'s
ℕ division. -/
theorem populate_msbF_eval (ctx : Witgen.Ctx (ZMod p)) (x : Witgen.FExpr (ZMod p))
    (hx : (x.eval ctx).val < 2 ^ 16) :
    (populate_msbF x).eval ctx = populate_msb (x.eval ctx) := by
  simp only [populate_msbF, populate_msb, circuit_norm, FiniteField.fromNat]

omit [Fact (2 ^ 17 < p)] in
/-- Environment-locality of the `FExpr` twin (the `ComputableWitnesses` counterpart of
`populate_msbF_eval` — a congruence, so it needs no bounds). -/
theorem populate_msbF_congr (ctx ctx' : Witgen.Ctx (ZMod p)) (x : Witgen.FExpr (ZMod p))
    (hx : x.eval ctx = x.eval ctx') :
    (populate_msbF x).eval ctx = (populate_msbF x).eval ctx' := by
  simp only [populate_msbF, circuit_norm, -Witgen.u64Wrap, hx]

/-- Check the activity/result bits and send the active arithmetic range check to the byte bus. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let a := input.a
  let cols := input.cols
  let is_real := input.is_real
  let E0 := is_real - 1
  let E1 := is_real * E0
  let E2 := cols.msb - 1
  let E3 := cols.msb * E2
  let E4 := 2 * a
  let E5 := cols.msb * 65536
  let E6 := E4 - E5
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
  obtain ⟨ha, hbin⟩ := h_assumptions
  have c16 : ((16 : ℕ) : ZMod p) = (16 : ZMod p) := Nat.cast_ofNat
  simp only [circuit_norm, byteChannel] at h_holds ⊢
  obtain ⟨hr, _hbool, hgc⟩ := h_holds
  refine ⟨⟨bool_of_mul_pred hgc, ?_⟩, fun h1 h0 => off_gate_vacuous hbin h1 h0⟩
  intro hr1eq
  have hneg : - input_is_real = -1 := by rw [hr1eq]
  have R := hr hneg
  rw [← c16] at R
  refine msb_of_raw (ha hr1eq) ?_
  simp only [RawSpec]
  exact ⟨bool_of_mul_pred hgc, (byteRowSpec_range _ sixteen_lt).mp R⟩

theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  have hp : 2 ^ 17 < p := Fact.out
  obtain ⟨ha, hbin⟩ := h_assumptions
  obtain ⟨hmsbbool, hmsbeq⟩ := h_spec
  have c16 : ((16 : ℕ) : ZMod p) = (16 : ZMod p) := Nat.cast_ofNat
  simp only [circuit_norm, byteChannel]
  refine ⟨?_, ?_, ?_⟩
  · intro hneg
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    have hav := ha hr1
    have hin_cast : ((input_a.val : ℕ) : ZMod p) = input_a := ZMod.natCast_zmod_val input_a
    have h2 : (2 * input_a : ZMod p).val = 2 * input_a.val := by
      rw [two_mul, ZMod.val_add_of_lt (by omega)]; omega
    have hmsb := hmsbeq hr1
    rw [← c16]
    apply (byteRowSpec_range _ sixteen_lt).mpr
    rw [hmsb]
    by_cases hge : input_a.val ≥ 32768
    · rw [if_pos hge, one_mul]
      have hsub : (2 * input_a - 65536 : ZMod p) = (((2 * input_a.val - 65536 : ℕ) : ZMod p)) := by
        rw [Nat.cast_sub (by omega)]; push_cast; rw [hin_cast]
      rw [hsub, ZMod.val_natCast_of_lt (by omega)]; omega
    · rw [if_neg hge, zero_mul, sub_zero, h2]; omega
  · rcases hbin with h | h <;> rw [h] <;> simp
  · rcases hmsbbool with h | h <;> rw [h] <;> simp

/-- SP1's `U16MSBOperation::eval_msb` as a Clean-native `FormalAssertion`. -/
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

@[circuit_norm] lemma channelsWithRequirements_eq :
    (circuit (p := p)).channelsWithRequirements = [] := rfl

@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.U16MSBOperation
