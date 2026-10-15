import SP1Clean.FormalModel.Contracts.ClockOrder

/-! # Clock comparisons from natural event times

Splitting bounded natural clocks into high/low limbs supplies the complete semantic comparison
contract. Queue handlers share this construction; no comparison columns are supplied by callers.
-/

namespace SP1Clean.ClockOrder

variable {p : ℕ} [Fact (2 ^ 25 < p)]

def encode (previous current : ℕ) : Inputs (ZMod p) :=
  ⟨(previous / 2 ^ 24 : ℕ), (previous % 2 ^ 24 : ℕ),
    (current / 2 ^ 24 : ℕ), (current % 2 ^ 24 : ℕ)⟩

theorem encode_spec (previous current : ℕ) (fits : current < 2 ^ 48) (order : previous < current) :
    Spec (encode (p := p) previous current) := by
  have hp := Fact.out (p := 2 ^ 25 < p)
  have previousHigh : previous / 2 ^ 24 < p := by omega
  have previousLow : previous % 2 ^ 24 < p := by omega
  have currentHigh : current / 2 ^ 24 < p := by omega
  have currentLow : current % 2 ^ 24 < p := by omega
  simp only [Spec, encode, Semantics.clkNat,
    ZMod.val_natCast_of_lt previousHigh, ZMod.val_natCast_of_lt previousLow,
    ZMod.val_natCast_of_lt currentHigh, ZMod.val_natCast_of_lt currentLow]
  omega

end SP1Clean.ClockOrder
