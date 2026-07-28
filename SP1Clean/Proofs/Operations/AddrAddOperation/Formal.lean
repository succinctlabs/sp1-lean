import SP1Clean.Native.Operations.AddrAddOperation.RawSpec
import SP1Clean.Native.Operations.AddrAddOperation.Populate
import SP1Clean.Native.Operations.AddrAddOperation.Defs

/-! # `AddrAddOperation` — the `FormalAssertion` (soundness / completeness / contract)

SP1's `AddrAddOperation::eval` (48-bit/3-limb address add) as a Clean `FormalAssertion`: the
`Assumptions`, the soundness/completeness proofs (routing through `RawSpec`'s
`addrAddSemantics_of_carries`/`carries_of_addrAddSemantics`), and the bundled `circuit`. The high
carry runs against `0`: its booleanity proves the address-fits fact in soundness, while completeness
recovers the same fact from the semantic `Spec`. The arithmetic core lives in `RawSpec`, the native
circuit (`main`/`elaborated`) in `Defs`, and the `populate` witness in `Populate`. -/

namespace SP1Clean.AddrAddOperation

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Operand words fit in 64 bits and `is_real` is binary (discharged by the composing chip's gate).
The address-fits fact is not an assumption: the AIR's boolean high carry against zero proves it. -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  Word.isU64 input.a ∧ Word.isU64 input.b ∧ (input.is_real = 0 ∨ input.is_real = 1)

theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨ha, hb, hbin⟩ := h_assumptions
  obtain ⟨hia, hib, hiv, _⟩ := h_input
  have c16 : ((16 : ℕ) : ZMod p) = (16 : ZMod p) := Nat.cast_ofNat
  have h65536 : (2 : ℕ) ^ 16 = 65536 := by norm_num
  have ev {n : ℕ} {w : Vector (Expression (ZMod p)) n} {v : Vector (ZMod p) n}
      (h : Vector.map (Expression.eval env) w = v) :
      ∀ i (_ : i < n), Expression.eval env w[i] = v[i] := fun i _ => by rw [← h, Vector.getElem_map]
  simp only [circuit_norm, byteChannel, ev hia, ev hib, ev hiv] at h_holds ⊢
  obtain ⟨hr0, hr1, hr2, _hbool, hgc0, hgc1, hgc2, hgc3⟩ := h_holds
  -- The three trailing conjuncts are the limb byte pulls' own `Requirements` — vacuous off-gate.
  refine ⟨fun hr1eq => ?_, fun h1 h0 => off_gate_vacuous hbin h1 h0,
    fun h1 h0 => off_gate_vacuous hbin h1 h0, fun h1 h0 => off_gate_vacuous hbin h1 h0⟩
  have hneg : - input_is_real = -1 := by rw [hr1eq]
  have R0 := hr0 hneg; have R1 := hr1 hneg; have R2 := hr2 hneg
  rw [← c16] at R0 R1 R2
  rw [hr1eq, one_mul] at hgc0 hgc1 hgc2 hgc3
  simp only [sub_zero] at hgc3
  have Rb0 := (byteRowSpec_range _ sixteen_lt).mp R0
  have Rb1 := (byteRowSpec_range _ sixteen_lt).mp R1
  have Rb2 := (byteRowSpec_range _ sixteen_lt).mp R2
  have hraw : RawSpec input_a input_b (⟨input_cols_value⟩ : Extracted.AddrAddOperation (ZMod p)) := by
    simp only [RawSpec]
    exact ⟨bool_of_mul_pred hgc0, bool_of_mul_pred hgc1, bool_of_mul_pred hgc2,
    bool_of_mul_pred hgc3, by rw [← h65536]; exact Rb0, by rw [← h65536]; exact Rb1,
    by rw [← h65536]; exact Rb2⟩
  exact ⟨addrAddSemantics_of_carries ha hb hraw, Rb0, Rb1, Rb2,
    addrAddFits_of_carries ha hb hraw⟩

theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨ha, hb, hbin⟩ := h_assumptions
  obtain ⟨hia, hib, hiv, _⟩ := h_input
  have c16 : ((16 : ℕ) : ZMod p) = (16 : ZMod p) := Nat.cast_ofNat
  have ev {n : ℕ} {w : Vector (Expression (ZMod p)) n} {v : Vector (ZMod p) n}
      (h : Vector.map (Expression.eval env.toEnvironment) w = v) :
      ∀ i (_ : i < n), Expression.eval env.toEnvironment w[i] = v[i] :=
    fun i _ => by rw [← h, Vector.getElem_map]
  have key (hneg : - input_is_real = -1) := h_spec (neg_inj.mp hneg)
  simp only [circuit_norm, byteChannel, ev hia, ev hib, ev hiv]
  refine ⟨fun hneg => ?_, fun hneg => ?_, fun hneg => ?_, ?_⟩
  · rw [← c16]; exact (byteRowSpec_range _ sixteen_lt).mpr (key hneg).2.1
  · rw [← c16]; exact (byteRowSpec_range _ sixteen_lt).mpr (key hneg).2.2.1
  · rw [← c16]; exact (byteRowSpec_range _ sixteen_lt).mpr (key hneg).2.2.2.1
  · rcases hbin with h0 | h1
    · simp [h0]
    · obtain ⟨heq, hrng0, hrng1, hrng2, hfit⟩ := h_spec h1
      have hraw : RawSpec input_a input_b (⟨input_cols_value⟩ : Extracted.AddrAddOperation (ZMod p)) :=
        carries_of_addrAddSemantics ha hb hfit hrng0 hrng1 hrng2 heq
      simp only [RawSpec] at hraw
      obtain ⟨hc0, hc1, hc2, hc3, _, _, _⟩ := hraw
      rw [h1]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp
      · rw [one_mul]; rcases hc0 with h | h <;> rw [h] <;> simp
      · rw [one_mul]; rcases hc1 with h | h <;> rw [h] <;> simp
      · rw [one_mul]; rcases hc2 with h | h <;> rw [h] <;> simp
      · simp only [sub_zero]
        rw [one_mul]
        rcases hc3 with h | h <;> rw [h] <;> simp

/-- SP1's `AddrAddOperation::eval` as a Clean-native `FormalAssertion`. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness,
    channelsWithRequirements := [],
    requirementsChannelsLawful := fun input_var i₀ => by
      simp only [circuit_norm, main, byteChannel]; grind }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.AddrAddOperation
