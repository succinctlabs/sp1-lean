import SP1Clean.Proofs.Chips.HostRamAccessChip.Formal
import SP1Clean.Model.MemoryClock

/-! # Constructing the host RAM timestamp witness

The caller supplies the prior Memory record and the event clock. The constructor computes the
comparison selector and both gap limbs. Its domain consists of bounded words, an aligned guest
address, a canonical event clock, and strict time order; no timestamp-column equations are assumed.
-/

namespace SP1Clean.HostRamAccessChip

open Circuit Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def populate (prior : MemoryMsg (ZMod p)) (clkHigh clk0 clk1 : ZMod p)
    (newValue : Word (ZMod p)) : Inputs (ZMod p) :=
  let sameHigh := prior.clk_high = clkHigh
  let previous := if sameHigh then prior.clk_low else prior.clk_high
  let current := if sameHigh then clk0 + clk1 * 65536 + 1 else clkHigh
  let gap := current.val - previous.val - 1
  ⟨⟨prior.value, ⟨prior.clk_high, prior.clk_low, if sameHigh then 1 else 0,
      (gap % 65536 : ℕ), (gap / 65536 : ℕ)⟩⟩,
    clkHigh, clk0, clk1, prior.addr0, prior.addr1, prior.addr2, newValue⟩

def Domain (prior : MemoryMsg (ZMod p)) (clkHigh clk0 clk1 : ZMod p)
    (newValue : Word (ZMod p)) : Prop :=
  FinalRamProvider.Domain prior ∧ Word.isU64 prior.value ∧ Word.isU64 newValue ∧
    prior.clk_high.val < 2 ^ 24 ∧ MemoryMsg.ClkBound prior ∧ clkHigh.val < 2 ^ 24 ∧
    ((clk0 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧ clk1.val < 2 ^ 8 ∧
    Semantics.MemoryMsg.timeNat prior < Semantics.clkNat clkHigh (clk0 + clk1 * 65536 + 1)

/-- Honest word transfers construct every internal timestamp witness needed by completeness. -/
theorem populate_assumptions (prior : MemoryMsg (ZMod p)) (clkHigh clk0 clk1 : ZMod p)
    (newValue : Word (ZMod p)) (valid : Domain prior clkHigh clk0 clk1 newValue) :
    ProverAssumptions (populate prior clkHigh clk0 clk1 newValue) := by
  obtain ⟨address, oldWord, newWord, previousHigh, previousLow, high, low0, low1, increases⟩ := valid
  have discipline : Readers.ClkDiscipline (clk0 + clk1 * 65536) (1 : ZMod p) :=
    Readers.ClkDiscipline.of_cpuState_spec (fun _ => ⟨low0, low1⟩)
  have currentLow := discipline.at_one rfl
  refine ⟨address, newWord, low0, low1, high, previousHigh, ?_⟩
  intro _
  simp only [Semantics.MemoryMsg.timeNat, Semantics.clkNat, MemoryMsg.ClkBound] at increases previousLow
  by_cases sameHigh : prior.clk_high = clkHigh
  · have lowIncreases : prior.clk_low.val < (clk0 + clk1 * 65536 + 1).val := by
      rw [sameHigh] at increases
      omega
    obtain ⟨gap, gapLow, gapHigh⟩ := MemoryClock.gap_encoding _ _ lowIncreases currentLow
    simp only [populate, Inputs.reader, Inputs.clockLow,
      Readers.MemoryAccess.selCur, Readers.MemoryAccess.selPrev, sub_self, zero_mul, one_mul,
      add_zero, sameHigh, if_true, mul_zero]
    exact ⟨Or.inr (by trivial), by trivial, gap, gapLow, gapHigh, oldWord, previousLow⟩
  · have highDifferent : prior.clk_high.val ≠ clkHigh.val := fun equal =>
      sameHigh (ZMod.val_injective p equal)
    have highIncreases : prior.clk_high.val < clkHigh.val := by omega
    obtain ⟨gap, gapLow, gapHigh⟩ := MemoryClock.gap_encoding _ _ highIncreases high
    simp only [populate, if_neg sameHigh, Inputs.reader, Inputs.clockLow,
      Readers.MemoryAccess.selCur, Readers.MemoryAccess.selPrev, zero_mul, sub_zero, one_mul,
      zero_add]
    exact ⟨Or.inl (by trivial), by trivial, gap, gapLow, gapHigh, oldWord, previousLow⟩

end SP1Clean.HostRamAccessChip
