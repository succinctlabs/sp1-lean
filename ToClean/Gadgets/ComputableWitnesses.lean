module

public import ToClean.Circuit.WitgenBridge
public import ToClean.Gadgets.BitwiseByte

/-! # Computable witnesses for bit gadgets

Clean's `ToBits` circuits prove completeness but do not expose the witness-locality fact needed
by the array-backed row builder. These additive upstream APIs show that their witness IR reads
only the input expression, including under changes to prover data. The range-check wrapper
composes the same fact through the ordinary subcircuit bridge. The bitwise-byte gadget composes
two decompositions and a result witness through that same API.

Move these declarations beside Clean's bit gadgets and delete this module when upstream supplies
these APIs. The data-aware composition lemmas live in `ToClean/Circuit/WitgenBridge.lean`.
-/

@[expose] public section

namespace Gadgets.ToBits

open Circuit

variable {p : ℕ} [Fact p.Prime]

/-- `toBits` has computable witnesses: its one witness operation is the bit decomposition of the
input expression, so an environment agreeing on the input agrees on every declared bit. The two
tails — the per-bit boolean assertions (a `forEach` of zero-witness assertions) and the closing
equality subcircuit — declare no cells at all. -/
theorem toBits_computableWitnesses [Fact (p > 2)] (n : ℕ) (hn : 2 ^ n < p) :
    (toBits n hn (p := p)).base.ComputableWitnessesWithData := by
  intro k input env env'
  simp only [toBits, main, circuit_norm, Operations.forAllFlat, Operations.forAll]
  refine ⟨fun _ h_in => ?_,
    Operations.forAllFlat_witnessCongr_of_localLength_zero _ _ (by simp [circuit_norm]),
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ (by simp [circuit_norm])⟩
  simp only [Witgen.WitgenIR.eval, Witgen.VExpr.eval, Witgen.FExpr.eval, h_in]

/-- `rangeCheck` has computable witnesses: it is the assertion wrapper around `toBits`, whose own
`ComputableWitnesses` dispatches the single composed subcircuit. -/
theorem rangeCheck_computableWitnesses [Fact (p > 2)] (n : ℕ) (hn : 2 ^ n < p) :
    (rangeCheck n hn (p := p)).base.ComputableWitnessesWithData := by
  intro k input env env'
  simp only [rangeCheck, circuit_norm, Operations.forAllFlat, Operations.forAll]
  exact FlatOperation.forAll_witnessCongr_of_generalSubcircuit _ _ _
    (toBits_computableWitnesses n hn) fun h => by simpa [circuit_norm] using h

end Gadgets.ToBits

namespace Gadgets.BitwiseByte

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

/-- Every witness depends only on the two inputs. -/
theorem computableWitnesses (op : Op) (hp : 2 ^ 8 < p) :
    (circuit op hp).base.ComputableWitnessesWithData := by
  intro k input env env'
  simp only [circuit, main, circuit_norm, Operations.forAllFlat]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact FlatOperation.forAll_witnessCongr_of_generalSubcircuit
      (ToBits.toBits 8 hp) input.1 k (ToBits.toBits_computableWitnesses 8 hp)
      (fun h => by simpa only [circuit_norm] using congrArg Prod.fst h)
  · rw [show (ToBits.toBits 8 hp).localLength input.1 + k =
        k + ((ToBits.toBits 8 hp).localLength input.1 + 0) by omega]
    exact FlatOperation.forAll_witnessCongr_of_generalSubcircuit
      (ToBits.toBits 8 hp) input.2 _ (ToBits.toBits_computableWitnesses 8 hp)
      (fun h => by simpa only [circuit_norm] using congrArg Prod.snd h)
  · intro _ h
    obtain ⟨hx, hy⟩ := Prod.mk.inj h
    cases op <;> simp [circuit_norm, hx, hy]
  · exact FlatOperation.forAll_witnessCongr_of_subcircuit _ _ (by simp [circuit_norm])

end Gadgets.BitwiseByte
