import SP1Clean.FormalModel.TraceGen.Readers
import SP1Clean.FormalModel.Contracts.SystemChips
import SP1Clean.Model.Semantics.AccessSchedule

/-!
# Trace generation — the two system-table bump rows

The 25 instruction chips advance the machine's clock and program counter **without carrying**: a
row adds `8` (or `264`) to `clk_low` and `4` to `pc0` and pushes the result straight back onto the
State bus. That is what makes the per-row constraint cheap, and it is why the limbs drift out of
canonical range: after roughly `2 ^ 21` rows `clk_low` passes `2 ^ 24`, and `pc0` passes `2 ^ 16`
every 16 KiB of straight-line code.

SP1's two system tables put them back. `StateBumpChip` pulls the drifted State message and pushes
the re-limbed one, moving one carry from `clk_low` into `clk_high` and running the pc's borrow
cascade. `MemoryBumpChip` does the same for a register record's timestamp: it pulls the record and
re-pushes it at a refreshed clock, so the memory argument's strictly-increasing chain survives a
window boundary.

Both were free fields of `SupportedCoreTraceWitness`, carrying `Spec` as an assumption. This module
**derives** them: each takes the semantic description of one crossing and produces a row whose
`Spec` is a theorem. That is what makes a shard above the `~2 ^ 21`-row cap witnessable on the
completeness side, and it needs no execution generator in hand — a bump row is a function of the
state at the crossing, nothing more.

**Field bound.** `Fact (2 ^ 25 < p)`, one step above the rest of this layer: the *drifted* clock a
bump row pulls is up to a whole window past `2 ^ 24`, so its cast has to stay non-wrapping. That is
the same bound the grounding engine and the completeness assembly already carry.
-/

namespace SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-! ## StateBump -/

/-- One State-bus re-canonicalization: the drifted state a `StateBumpChip` row pulls, as plain
naturals. The pushed state is a function of it, so nothing else needs supplying. -/
structure StateBumpEvent where
  clkHigh : ℕ
  clkLow : ℕ
  pc0 : ℕ
  pc1 : ℕ
  pc2 : ℕ

namespace StateBumpEvent

/-- Does this crossing carry into the high clock limb? -/
def isClk (e : StateBumpEvent) : ℕ := if 2 ^ 24 ≤ e.clkLow then 1 else 0

/-- The low pc limb's carry, and the middle limb's. -/
def b0 (e : StateBumpEvent) : ℕ := if 2 ^ 16 ≤ e.pc0 then 1 else 0
def b1 (e : StateBumpEvent) : ℕ := if 2 ^ 16 ≤ e.pc1 + e.b0 then 1 else 0

/-- The canonical clock the row pushes. -/
def nextClkHigh (e : StateBumpEvent) : ℕ := e.clkHigh + e.isClk
def nextClkLow (e : StateBumpEvent) : ℕ := e.clkLow - e.isClk * 2 ^ 24

/-- The canonical pc the row pushes. -/
def nextPc0 (e : StateBumpEvent) : ℕ := e.pc0 - e.b0 * 2 ^ 16
def nextPc1 (e : StateBumpEvent) : ℕ := e.pc1 + e.b0 - e.b1 * 2 ^ 16
def nextPc2 (e : StateBumpEvent) : ℕ := e.pc2 + e.b1

/--
**When a crossing is one a bump row can absorb.**

Each clause is a "drifted by at most one step" bound, which is exactly the invariant SP1 maintains
by bumping *before* a second carry could accumulate: the clock is `≡ 1 (mod 8)` (it starts at 1 and
steps by 8 or 264) and has drifted at most one window; the high limb has room for the carry; and
each pc limb has drifted at most one `2 ^ 16` unit.
-/
structure WellFormed (e : StateBumpEvent) : Prop where
  clkMod : e.clkLow % 8 = 1
  clkLow : e.clkLow < 2 ^ 25
  clkHigh : e.clkHigh + 1 < 2 ^ 24
  pc0 : e.pc0 < 2 ^ 17
  pc1 : e.pc1 + 1 < 2 ^ 17
  pc2 : e.pc2 + 1 < 2 ^ 16

end StateBumpEvent


namespace StateBumpEvent

variable {e : StateBumpEvent}

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
/-- The two clock limbs recombine to the pushed clock, and the pushed clock is the pulled one with
one carry moved up. -/
theorem clk_split (h : e.WellFormed) :
    e.nextClkHigh % 256 + e.nextClkHigh / 256 * 256 = e.clkHigh + e.isClk ∧
      e.nextClkLow % 65536 + e.nextClkLow / 65536 * 65536 + e.isClk * 16777216 = e.clkLow := by
  have hclk := h.clkLow
  simp only [nextClkHigh, nextClkLow, isClk]
  split <;> omega

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
/-- The pushed clock and pc limbs are canonical. -/
theorem next_bounds (h : e.WellFormed) :
    e.nextClkLow < 2 ^ 24 ∧ e.nextClkHigh < 2 ^ 24 ∧
      e.nextPc0 < 2 ^ 16 ∧ e.nextPc1 < 2 ^ 16 ∧ e.nextPc2 < 2 ^ 16 := by
  obtain ⟨-, hlow, hhigh, hpc0, hpc1, hpc2⟩ := h
  simp only [nextClkLow, nextClkHigh, isClk, nextPc0, nextPc1, nextPc2, b1, b0]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> split_ifs <;> omega

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
/-- The pc borrow cascade, over `ℕ`. -/
theorem pc_cascade (h : e.WellFormed) :
    e.pc0 = e.nextPc0 + e.b0 * 65536 ∧
      e.b0 + e.pc1 = e.nextPc1 + e.b1 * 65536 ∧
      e.b1 + e.pc2 = e.nextPc2 := by
  obtain ⟨-, -, -, hpc0, hpc1, -⟩ := h
  simp only [nextPc0, nextPc1, nextPc2, b1, b0]
  refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
/-- The pushed low clock keeps the machine's `≡ 1 (mod 8)` discipline. -/
theorem nextClkLow_mod (h : e.WellFormed) : e.nextClkLow % 65536 % 8 = 1 := by
  have := h.clkMod
  simp only [nextClkLow, isClk]
  split <;> omega

end StateBumpEvent

/-- SP1's `StateBumpChip` row for one crossing: the drifted limbs it pulls, and the canonical ones
it pushes, split as `clk_high = clk_24_32 + clk_32_48 · 2^8` and
`clk_low = clk_0_16 + clk_16_24 · 2^16`. -/
def stateBumpCols (e : StateBumpEvent) : StateBumpChip.Inputs (ZMod p) where
  next_clk_32_48 := ((e.nextClkHigh / 256 : ℕ) : ZMod p)
  next_clk_24_32 := ((e.nextClkHigh % 256 : ℕ) : ZMod p)
  next_clk_16_24 := ((e.nextClkLow / 65536 : ℕ) : ZMod p)
  next_clk_0_16 := ((e.nextClkLow % 65536 : ℕ) : ZMod p)
  clk_high := ((e.clkHigh : ℕ) : ZMod p)
  clk_low := ((e.clkLow : ℕ) : ZMod p)
  next_pc0 := ((e.nextPc0 : ℕ) : ZMod p)
  next_pc1 := ((e.nextPc1 : ℕ) : ZMod p)
  next_pc2 := ((e.nextPc2 : ℕ) : ZMod p)
  pc0 := ((e.pc0 : ℕ) : ZMod p)
  pc1 := ((e.pc1 : ℕ) : ZMod p)
  pc2 := ((e.pc2 : ℕ) : ZMod p)
  is_clk := ((e.isClk : ℕ) : ZMod p)
  is_real := 1


/-- **A built `StateBump` row satisfies its contract.**

The obligation that carries the content is the last pair: the pulled clock really is the pushed one
plus the `is_clk · 2^24` carry, as a field identity. Everything else is a range fact about a limb
split, or the pc borrow cascade, and all of it is `ℕ` arithmetic cast forward — which is why the
`Fact (2 ^ 25 < p)` bound is where the drifted clock's non-wrapping lives. -/
theorem stateBump_spec {e : StateBumpEvent} (h : e.WellFormed) :
    StateBumpChip.Spec (stateBumpCols (p := p) e) := by
  have hp : 2 ^ 25 < p := Fact.out
  obtain ⟨hhigh, hlow⟩ := StateBumpEvent.clk_split h
  obtain ⟨hnextLow, hnextHigh, hnp0, hnp1, hnp2⟩ := StateBumpEvent.next_bounds h
  obtain ⟨hc0, hc1, hc2⟩ := StateBumpEvent.pc_cascade h
  have hmod := StateBumpEvent.nextClkLow_mod h
  refine ⟨?_, ?_, ⟨((e.b0 : ℕ) : ZMod p), ((e.b1 : ℕ) : ZMod p), ?_, ?_, ?_, ?_, ?_⟩, fun _ => ?_⟩
  · exact Or.inr rfl
  · show (((e.isClk : ℕ) : ZMod p) = 0 ∨ ((e.isClk : ℕ) : ZMod p) = 1)
    simp only [StateBumpEvent.isClk]
    split
    · exact Or.inr (by push_cast; ring)
    · exact Or.inl (by push_cast; ring)
  · simp only [StateBumpEvent.b0]
    split
    · exact Or.inr (by push_cast; ring)
    · exact Or.inl (by push_cast; ring)
  · simp only [StateBumpEvent.b1]
    split
    · exact Or.inr (by push_cast; ring)
    · exact Or.inl (by push_cast; ring)
  · show ((e.pc0 : ℕ) : ZMod p) = ((e.nextPc0 : ℕ) : ZMod p) + ((e.b0 : ℕ) : ZMod p) * 65536
    rw [show ((65536 : ZMod p)) = ((65536 : ℕ) : ZMod p) from by push_cast; ring,
      ← Nat.cast_mul, ← Nat.cast_add, hc0]
  · show ((e.b0 : ℕ) : ZMod p) + ((e.pc1 : ℕ) : ZMod p)
      = ((e.nextPc1 : ℕ) : ZMod p) + ((e.b1 : ℕ) : ZMod p) * 65536
    rw [show ((65536 : ZMod p)) = ((65536 : ℕ) : ZMod p) from by push_cast; ring,
      ← Nat.cast_mul, ← Nat.cast_add, ← Nat.cast_add, hc1]
  · show ((e.b1 : ℕ) : ZMod p) + ((e.pc2 : ℕ) : ZMod p) = ((e.nextPc2 : ℕ) : ZMod p)
    rw [← Nat.cast_add, hc2]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hlt16 : e.nextClkLow % 65536 < 65536 := Nat.mod_lt _ (by norm_num)
      obtain ⟨q, hq, hqlt⟩ : ∃ q, e.nextClkLow % 65536 = 8 * q + 1 ∧ q < 2 ^ 13 :=
        ⟨e.nextClkLow % 65536 / 8, by omega, by omega⟩
      show ((((e.nextClkLow % 65536 : ℕ) : ZMod p) - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13
      rw [hq]
      push_cast
      rw [show (8 : ZMod p) * (q : ZMod p) + 1 - 1 = (q : ZMod p) * 8 from by ring, mul_assoc,
        mul_inv_cancel₀ (val_8_ne_zero (p := p)), mul_one, ZMod.val_natCast_of_lt (by omega)]
      exact hqlt
    · show (((e.nextClkLow / 65536 : ℕ) : ZMod p)).val < 2 ^ 8
      rw [ZMod.val_natCast_of_lt (by omega)]
      omega
    · show (((e.nextClkHigh % 256 : ℕ) : ZMod p)).val < 2 ^ 8
      rw [ZMod.val_natCast_of_lt (by omega)]
      omega
    · show (((e.nextClkHigh / 256 : ℕ) : ZMod p)).val < 2 ^ 16
      rw [ZMod.val_natCast_of_lt (by omega)]
      omega
    · show (((e.nextPc0 : ℕ) : ZMod p)).val < 2 ^ 16
      rw [ZMod.val_natCast_of_lt (by omega)]; omega
    · show (((e.nextPc1 : ℕ) : ZMod p)).val < 2 ^ 16
      rw [ZMod.val_natCast_of_lt (by omega)]; omega
    · show (((e.nextPc2 : ℕ) : ZMod p)).val < 2 ^ 16
      rw [ZMod.val_natCast_of_lt (by omega)]; omega
    · show ((e.nextClkHigh % 256 : ℕ) : ZMod p) + ((e.nextClkHigh / 256 : ℕ) : ZMod p) * 256
        = ((e.clkHigh : ℕ) : ZMod p) + ((e.isClk : ℕ) : ZMod p)
      rw [show ((256 : ZMod p)) = ((256 : ℕ) : ZMod p) from by push_cast; ring,
        ← Nat.cast_mul, ← Nat.cast_add, ← Nat.cast_add, hhigh]
    · show ((e.nextClkLow % 65536 : ℕ) : ZMod p)
        + ((e.nextClkLow / 65536 : ℕ) : ZMod p) * 65536
        + ((e.isClk : ℕ) : ZMod p) * 16777216 = ((e.clkLow : ℕ) : ZMod p)
      rw [show ((65536 : ZMod p)) = ((65536 : ℕ) : ZMod p) from by push_cast; ring,
        show ((16777216 : ZMod p)) = ((16777216 : ℕ) : ZMod p) from by push_cast; ring,
        ← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_add, ← Nat.cast_add, hlow]


/-! ## MemoryBump -/

/-- SP1's `MemoryBumpChip` row for one refresh: the standard `MemoryAccessCols` carrier at the old
and new timestamps, the refreshed clock's four canonical limbs, and the register index. -/
def memoryBumpCols (e : MemoryBumpEvent) : MemoryBumpChip.Inputs (ZMod p) where
  access := memoryAccessCols e.value e.prevTs e.currTs
  clk_32_48 := ((e.currTs >>> 24 / 2 ^ 8 : ℕ) : ZMod p)
  clk_24_32 := ((e.currTs >>> 24 % 2 ^ 8 : ℕ) : ZMod p)
  clk_16_24 := ((e.currTs % 2 ^ 24 / 2 ^ 16 : ℕ) : ZMod p)
  clk_0_16 := ((e.currTs % 2 ^ 24 % 2 ^ 16 : ℕ) : ZMod p)
  addr := ((e.addr : ℕ) : ZMod p)
  is_real := 1

/-- **A built `MemoryBump` row satisfies its contract.**

The same two-branch timestamp argument the RAM access block runs (`TraceGen/Memory.lean`'s
`memoryAccess_spec`), at an arbitrary refreshed timestamp rather than at `clk + 1`: same 24-bit
window and the low halves are compared, different windows and the high halves are, and either gap
is 24-bit — the first because both residues are, the second because the clock is 48-bit. -/
theorem memoryBump_spec {e : MemoryBumpEvent} (h : e.WellFormed) :
    MemoryBumpChip.Spec (memoryBumpCols (p := p) e) := by
  have hp : 2 ^ 24 < p := Fact.out
  obtain ⟨haddr, hinc, hcurr⟩ := h
  have hprevSR : e.prevTs >>> 24 = e.prevTs / 2 ^ 24 := Nat.shiftRight_eq_div_pow e.prevTs 24
  have hcurrSR : e.currTs >>> 24 = e.currTs / 2 ^ 24 := Nat.shiftRight_eq_div_pow e.currTs 24
  refine ⟨Or.inr rfl, fun _ => ?_⟩
  simp only [memoryBumpCols, memoryAccessCols_compare_low, memoryAccessCols_prev_high,
    memoryAccessCols_prev_low, memoryAccessCols_prev_value, memoryAccessCols_diff_low_limb,
    memoryAccessCols_diff_high_limb]
  have hclkHigh : ((e.currTs >>> 24 % 2 ^ 8 : ℕ) : ZMod p)
      + ((e.currTs >>> 24 / 2 ^ 8 : ℕ) : ZMod p) * (256 : ZMod p)
      = ((e.currTs >>> 24 : ℕ) : ZMod p) := by
    have hnat : e.currTs >>> 24 % 2 ^ 8 + e.currTs >>> 24 / 2 ^ 8 * 256 = e.currTs >>> 24 := by
      omega
    calc ((e.currTs >>> 24 % 2 ^ 8 : ℕ) : ZMod p)
          + ((e.currTs >>> 24 / 2 ^ 8 : ℕ) : ZMod p) * (256 : ZMod p)
        = ((e.currTs >>> 24 % 2 ^ 8 + e.currTs >>> 24 / 2 ^ 8 * 256 : ℕ) : ZMod p) := by
          push_cast; ring
      _ = ((e.currTs >>> 24 : ℕ) : ZMod p) := by rw [hnat]
  have hclkLow : ((e.currTs % 2 ^ 24 % 2 ^ 16 : ℕ) : ZMod p)
      + ((e.currTs % 2 ^ 24 / 2 ^ 16 : ℕ) : ZMod p) * (65536 : ZMod p)
      = ((e.currTs % 2 ^ 24 : ℕ) : ZMod p) := by
    have hnat : e.currTs % 2 ^ 24 % 2 ^ 16 + e.currTs % 2 ^ 24 / 2 ^ 16 * 65536
        = e.currTs % 2 ^ 24 := by omega
    calc ((e.currTs % 2 ^ 24 % 2 ^ 16 : ℕ) : ZMod p)
          + ((e.currTs % 2 ^ 24 / 2 ^ 16 : ℕ) : ZMod p) * (65536 : ZMod p)
        = ((e.currTs % 2 ^ 24 % 2 ^ 16 + e.currTs % 2 ^ 24 / 2 ^ 16 * 65536 : ℕ) : ZMod p) := by
          push_cast; ring
      _ = ((e.currTs % 2 ^ 24 : ℕ) : ZMod p) := by rw [hnat]
  refine ⟨wordOfNat_isU64 _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ZMod.val_natCast_of_lt (by omega)]; omega
  · rw [ZMod.val_natCast_of_lt (by omega)]; omega
  · rw [ZMod.val_natCast_of_lt (by omega)]; omega
  · rw [ZMod.val_natCast_of_lt (by omega)]; omega
  · rw [ZMod.val_natCast_of_lt (by omega)]; omega
  · rw [ZMod.val_natCast_of_lt (by omega)]; omega
  · by_cases hsame : e.prevTs >>> 24 = e.currTs >>> 24
    · exact Or.inr (by rw [memCompareLow, if_pos hsame, Nat.cast_one])
    · exact Or.inl (by rw [memCompareLow, if_neg hsame, Nat.cast_zero])
  · by_cases hsame : e.prevTs >>> 24 = e.currTs >>> 24
    · rw [memCompareLow, if_pos hsame, Nat.cast_one, one_mul, hclkHigh, hsame, sub_self]
    · rw [memCompareLow, if_neg hsame, Nat.cast_zero, zero_mul]
  · by_cases hsame : e.prevTs >>> 24 = e.currTs >>> 24
    · have hle : e.prevTs % 2 ^ 24 < e.currTs % 2 ^ 24 := by
        rw [hprevSR, hcurrSR] at hsame; omega
      have hd : memDiffOf e.prevTs e.currTs = e.currTs % 2 ^ 24 - e.prevTs % 2 ^ 24 - 1 := by
        rw [memDiffOf, if_pos hsame]
      have hcast : ((e.currTs % 2 ^ 24 : ℕ) : ZMod p) = ((e.prevTs % 2 ^ 24 : ℕ) : ZMod p) + 1
          + (((memDiffOf e.prevTs e.currTs % 2 ^ 16 : ℕ) : ZMod p)
            + ((memDiffOf e.prevTs e.currTs / 2 ^ 16 : ℕ) : ZMod p) * 65536) := by
        conv_lhs => rw [show e.currTs % 2 ^ 24 = e.prevTs % 2 ^ 24 + 1
          + (memDiffOf e.prevTs e.currTs % 2 ^ 16
            + memDiffOf e.prevTs e.currTs / 2 ^ 16 * 65536) from by omega]
        push_cast
        ring
      rw [memCompareLow, if_pos hsame, Nat.cast_one]
      rw [hclkLow]
      linear_combination hcast
    · have hhigh : e.prevTs >>> 24 + 1 ≤ e.currTs >>> 24 := by
        rw [hprevSR, hcurrSR] at hsame ⊢; omega
      have hd : memDiffOf e.prevTs e.currTs = e.currTs >>> 24 - e.prevTs >>> 24 - 1 := by
        rw [memDiffOf, if_neg hsame]
      have hcast : ((e.currTs >>> 24 : ℕ) : ZMod p) = ((e.prevTs >>> 24 : ℕ) : ZMod p) + 1
          + (((memDiffOf e.prevTs e.currTs % 2 ^ 16 : ℕ) : ZMod p)
            + ((memDiffOf e.prevTs e.currTs / 2 ^ 16 : ℕ) : ZMod p) * 65536) := by
        conv_lhs => rw [show e.currTs >>> 24 = e.prevTs >>> 24 + 1
          + (memDiffOf e.prevTs e.currTs % 2 ^ 16
            + memDiffOf e.prevTs e.currTs / 2 ^ 16 * 65536) from by omega]
        push_cast
        ring
      rw [memCompareLow, if_neg hsame, Nat.cast_zero]
      rw [hclkHigh]
      linear_combination hcast
  · rw [ZMod.val_natCast_of_lt (by omega)]
    exact Nat.mod_lt _ (by norm_num)
  · by_cases hsame : e.prevTs >>> 24 = e.currTs >>> 24
    · have hd : memDiffOf e.prevTs e.currTs = e.currTs % 2 ^ 24 - e.prevTs % 2 ^ 24 - 1 := by
        rw [memDiffOf, if_pos hsame]
      rw [ZMod.val_natCast_of_lt (by omega)]
      omega
    · have hd : memDiffOf e.prevTs e.currTs = e.currTs >>> 24 - e.prevTs >>> 24 - 1 := by
        rw [memDiffOf, if_neg hsame]
      rw [ZMod.val_natCast_of_lt (by omega)]
      omega


/-! ## The trace-level row lists

The shape the other twenty-five chips already have: the trace record carries *events*, and the
table is built from them. These two tables were the last that carried pre-built rows with `Spec` as
an assumption. -/

/-- The `StateBump` rows a shard's crossings build. -/
def stateBumpTraceInputs (events : List StateBumpEvent) : List (StateBumpChip.Inputs (ZMod p)) :=
  events.map stateBumpCols

/-- The `MemoryBump` rows a shard's timestamp refreshes build. -/
def memoryBumpTraceInputs (events : List MemoryBumpEvent) :
    List (MemoryBumpChip.Inputs (ZMod p)) :=
  events.map memoryBumpCols

theorem stateBumpTraceInputs_spec {events : List StateBumpEvent}
    (h : ∀ e ∈ events, e.WellFormed) :
    ∀ r ∈ stateBumpTraceInputs (p := p) events, StateBumpChip.Spec r := by
  intro r hr
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
  exact stateBump_spec (h e he)

theorem memoryBumpTraceInputs_spec {events : List MemoryBumpEvent}
    (h : ∀ e ∈ events, e.WellFormed) :
    ∀ r ∈ memoryBumpTraceInputs (p := p) events, MemoryBumpChip.Spec r := by
  intro r hr
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
  exact memoryBump_spec (h e he)


/-! ## Non-vacuity

Both `WellFormed` predicates are conjunctions of bounds, and a conjunction of bounds is exactly the
shape that can be accidentally unsatisfiable. These two witnesses are the guard, and both are the
crossing the table exists for rather than a degenerate one: a clock one tick past the `2 ^ 24`
window with a pc limb one step past `2 ^ 16`, and a timestamp refresh that really does cross a
window (so it exercises the comparison's high-limb branch, not the cheap one). -/

/-- A real State-bus crossing. -/
theorem stateBumpEvent_wellFormed_witness :
    StateBumpEvent.WellFormed ⟨0, 2 ^ 24 + 1, 2 ^ 16, 0, 0⟩ where
  clkMod := by norm_num
  clkLow := by norm_num
  clkHigh := by norm_num
  pc0 := by norm_num
  pc1 := by norm_num
  pc2 := by norm_num

/-- A real cross-window timestamp refresh. -/
theorem memoryBumpEvent_wellFormed_witness :
    MemoryBumpEvent.WellFormed ⟨1, 0, 2 ^ 24 - 1, 2 ^ 24 + 7⟩ where
  addr := by norm_num
  increases := by norm_num
  currLt := by norm_num

end SP1Clean.TraceGen
