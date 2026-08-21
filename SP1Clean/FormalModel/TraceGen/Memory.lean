import SP1Clean.FormalModel.TraceGen.Readers
import SP1Clean.Native.Readers.MemoryAccess

/-! # Trace generation — the RAM access block's contract

One theorem, split out of `Readers.lean` for a layering reason worth stating. Eight of the nine
reader families keep their `Inputs`/`Spec` on the `FormalModel/Contracts/` audit surface, so
`Readers.lean` proves their contracts while importing nothing below `FormalModel/`. The
`MemoryAccess` primitive is the documented exception: its contract block is **Native-resident**
(`Native/Readers/MemoryAccess.lean`, the "Spec homing" backlog item recorded in
`docs/architecture.md` § deliberate layering exceptions), so the theorem about it has to import
`Native/`. Keeping it in its own module confines that import to one file instead of putting it on
the whole reader-contract layer.

The content is the RAM half of every memory chip's `ProverAssumptions`: from the clock discipline,
the 48-bit clock bound, and "the cell's previous access is strictly earlier", the block SP1's
`MemoryAccessCols::populate` builds satisfies `Readers.MemoryAccess.Spec`.

This is also the only place in the trace-generation layer where a timestamp comparison's
**cross-window** branch is exercised. A register access commits one previous clock (`prev_low`,
zeroed across a window boundary), so its difference is always a low-half difference; a RAM access
commits both halves plus a `compare_low` selector and really does subtract high limbs. That is the
whole reason `MemoryEvent.WellFormed` carries `clk_lt` and the register families' records carry no
clock bound at all. -/

namespace SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## Sub-word limb selection

The half-word and byte loads (and the matching stores) select the *same* u16 limb out of the
8-byte RAM cell, with the same two committed offset bits — address bit 1 and address bit 2. Only
what they do *inside* that limb differs (a half-word takes it whole; a byte then splits it with
address bit 0). So the limb index, the limb itself, and the four-way selection fact are shared. -/

/-- The index of the u16 RAM limb an address selects: bits 1 and 2 of the address, read as a
half-word index. The chips commit it as two bits — `memLimbIndex addr % 2` (address bit 1) and
`memLimbIndex addr / 2` (address bit 2). -/
def memLimbIndex (addr : ℕ) : ℕ := addr % 8 / 2

/-- The selected u16 limb of the RAM cell, as an `ℕ`. -/
def memLimb (mem addr : ℕ) : ℕ := mem / 2 ^ (16 * memLimbIndex addr) % 2 ^ 16

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- The selected limb is a u16, by construction. -/
lemma memLimb_lt (mem addr : ℕ) : memLimb mem addr < 2 ^ 16 := by
  rw [memLimb]; omega

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- The limb index is one of four. -/
lemma memLimbIndex_lt (addr : ℕ) : memLimbIndex addr < 4 := by rw [memLimbIndex]; omega

omit [Fact (2 ^ 24 < p)] in
/-- **The four-way selection.** In each of the four address cases the two committed offset bits are
the case's own constants and the selected limb *is* the corresponding limb of the built RAM word —
which is what makes the chips' four selection gates hold (an equality in the selected branch, a
zero factor in each of the other three). -/
theorem memLimb_cases (mem addr : ℕ) :
    (((memLimbIndex addr % 2 : ℕ) : ZMod p) = 0 ∧ ((memLimbIndex addr / 2 : ℕ) : ZMod p) = 0
        ∧ ((memLimb mem addr : ℕ) : ZMod p) = (wordOfNat (p := p) mem)[0])
      ∨ (((memLimbIndex addr % 2 : ℕ) : ZMod p) = 1 ∧ ((memLimbIndex addr / 2 : ℕ) : ZMod p) = 0
        ∧ ((memLimb mem addr : ℕ) : ZMod p) = (wordOfNat (p := p) mem)[1])
      ∨ (((memLimbIndex addr % 2 : ℕ) : ZMod p) = 0 ∧ ((memLimbIndex addr / 2 : ℕ) : ZMod p) = 1
        ∧ ((memLimb mem addr : ℕ) : ZMod p) = (wordOfNat (p := p) mem)[2])
      ∨ (((memLimbIndex addr % 2 : ℕ) : ZMod p) = 1 ∧ ((memLimbIndex addr / 2 : ℕ) : ZMod p) = 1
        ∧ ((memLimb mem addr : ℕ) : ZMod p) = (wordOfNat (p := p) mem)[3]) := by
  have h4 : memLimbIndex addr = 0 ∨ memLimbIndex addr = 1 ∨ memLimbIndex addr = 2
      ∨ memLimbIndex addr = 3 := by have := memLimbIndex_lt addr; omega
  rw [memLimb, wordOfNat_zero, wordOfNat_one, wordOfNat_two, wordOfNat_three]
  rcases h4 with hI | hI | hI | hI
  · exact Or.inl ⟨by simp [hI], by simp [hI], by simp [hI]⟩
  · exact Or.inr (Or.inl ⟨by simp [hI], by simp [hI], by simp [hI]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨by simp [hI], by simp [hI], by simp [hI]⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by simp [hI], by simp [hI], by simp [hI]⟩))

/-- **The RAM access block's contract.** From the clock discipline, the 48-bit clock bound, and
"the cell's previous access is strictly earlier", the built block satisfies
`Readers.MemoryAccess.Spec` at the built state block's clock limbs. The address and `new_value`
parameters are arbitrary: the reader's contract mentions neither (they are bus payload, checked by
the channel, not by this `Spec`).

Both branches of `compare_low` are proved. Same window: the compared gap is
`clk % 2^24 - prevTs % 2^24`, which is 24-bit because both sides are. Different windows: it is
`clk >>> 24 - prevTs >>> 24 - 1`, which is 24-bit because `clk < 2^48`. -/
theorem memoryAccess_spec {value prevTs clk pc : ℕ} {addr0 addr1 addr2 is_real : ZMod p}
    {new_value : Word (ZMod p)} (hclk : clk % 8 = 1) (hclk48 : clk < 2 ^ 48)
    (hprev : prevTs < clk + 1) :
    Readers.MemoryAccess.Spec
      { mem := memoryAccessCols value prevTs (clk + 1),
        clk_high := (cpuStateCols (p := p) clk pc).clk_high,
        clk_low := (cpuStateCols (p := p) clk pc).clk_0_16
          + (cpuStateCols (p := p) clk pc).clk_16_24 * 65536,
        addr0 := addr0, addr1 := addr1, addr2 := addr2,
        new_value := new_value, is_real := is_real } := by
  have hp : 2 ^ 24 < p := Fact.out
  have hwin : clk % 2 ^ 24 + 4 < 2 ^ 24 := clk_window_of_mod hclk
  have hprevSR : prevTs >>> 24 = prevTs / 2 ^ 24 := Nat.shiftRight_eq_div_pow prevTs 24
  have hclkSR : clk >>> 24 = clk / 2 ^ 24 := Nat.shiftRight_eq_div_pow clk 24
  have hcurrSR : (clk + 1) >>> 24 = clk >>> 24 := by rw [Nat.shiftRight_eq_div_pow, hclkSR]; omega
  intro _
  -- reduce the reader `Inputs` literal's projections and fold the built block's columns; after
  -- this the goal names only the two `ℕ` builders `memCompareLow` / `memDiffOf` and the clock
  -- residues, so neither the row nor the state block is normalized again.
  simp only [Readers.MemoryAccess.selCur, Readers.MemoryAccess.selPrev,
    memoryAccessCols_compare_low, memoryAccessCols_prev_high, memoryAccessCols_prev_low,
    memoryAccessCols_prev_value, memoryAccessCols_diff_low_limb, memoryAccessCols_diff_high_limb,
    cpuStateCols_clk_high, clkLow_eq]
  by_cases hsame : prevTs >>> 24 = (clk + 1) >>> 24
  · -- same 24-bit window: the low halves are compared, and their gap is 24-bit because both are
    have hle : prevTs % 2 ^ 24 ≤ clk % 2 ^ 24 := by
      rw [hcurrSR, hprevSR, hclkSR] at hsame; omega
    have hd : memDiffOf prevTs (clk + 1) = clk % 2 ^ 24 - prevTs % 2 ^ 24 := by
      rw [memDiffOf, if_pos hsame]; omega
    have hc : ((memCompareLow prevTs (clk + 1) : ℕ) : ZMod p) = 1 := by
      rw [memCompareLow, if_pos hsame, Nat.cast_one]
    have hheq : ((prevTs >>> 24 : ℕ) : ZMod p) = ((clk >>> 24 : ℕ) : ZMod p) := by
      rw [← hcurrSR, hsame]
    have hcast : ((clk % 2 ^ 24 : ℕ) : ZMod p) = ((prevTs % 2 ^ 24 : ℕ) : ZMod p)
        + (((memDiffOf prevTs (clk + 1) % 2 ^ 16 : ℕ) : ZMod p)
          + ((memDiffOf prevTs (clk + 1) / 2 ^ 16 : ℕ) : ZMod p) * 65536) := by
      conv_lhs => rw [show clk % 2 ^ 24 = prevTs % 2 ^ 24 + (memDiffOf prevTs (clk + 1) % 2 ^ 16
        + memDiffOf prevTs (clk + 1) / 2 ^ 16 * 65536) from by omega]
      push_cast
      ring
    rw [hc]
    refine ⟨Or.inr rfl, by rw [hheq, sub_self, mul_zero], by linear_combination hcast, ?_, ?_,
      wordOfNat_isU64 _, ?_⟩
    · rw [ZMod.val_natCast_of_lt (by omega)]; omega
    · rw [ZMod.val_natCast_of_lt (by omega)]; omega
    · rw [ZMod.val_natCast_of_lt (by omega)]; omega
  · -- different windows: the high halves are compared, and `clk < 2 ^ 48` bounds their gap
    have hhigh : prevTs >>> 24 + 1 <= clk >>> 24 := by
      rw [hcurrSR] at hsame; rw [hprevSR, hclkSR] at hsame ⊢; omega
    have hclkhigh : clk >>> 24 < 2 ^ 24 := by rw [hclkSR]; omega
    have hd : memDiffOf prevTs (clk + 1) = clk >>> 24 - prevTs >>> 24 - 1 := by
      rw [memDiffOf, if_neg hsame, hcurrSR]
    have hc : ((memCompareLow prevTs (clk + 1) : ℕ) : ZMod p) = 0 := by
      rw [memCompareLow, if_neg hsame, Nat.cast_zero]
    have hcast : ((clk >>> 24 : ℕ) : ZMod p) = ((prevTs >>> 24 : ℕ) : ZMod p) + 1
        + (((memDiffOf prevTs (clk + 1) % 2 ^ 16 : ℕ) : ZMod p)
          + ((memDiffOf prevTs (clk + 1) / 2 ^ 16 : ℕ) : ZMod p) * 65536) := by
      conv_lhs => rw [show clk >>> 24 = prevTs >>> 24 + 1 + (memDiffOf prevTs (clk + 1) % 2 ^ 16
        + memDiffOf prevTs (clk + 1) / 2 ^ 16 * 65536) from by omega]
      push_cast
      ring
    rw [hc]
    refine ⟨Or.inl rfl, by rw [zero_mul], by linear_combination hcast, ?_, ?_,
      wordOfNat_isU64 _, ?_⟩
    · rw [ZMod.val_natCast_of_lt (by omega)]; omega
    · rw [ZMod.val_natCast_of_lt (by omega)]; omega
    · rw [ZMod.val_natCast_of_lt (by omega)]; omega

end SP1Clean.TraceGen
