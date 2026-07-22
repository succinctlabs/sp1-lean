import SP1Clean.FormalModel.Contracts.Readers
import SP1Clean.Model.Semantics.MicroTime

/-! # Extracting natural-number time from CPUState clocks

SP1 emits State-channel clocks as field elements.  The CPUState byte checks are precisely what rules
out wraparound and lets the whole-machine layer interpret its `clk + 8` edge as a strict step in `ℕ`.
This module proves that arithmetic fact once, independently of any particular instruction chip.

Two axes:

* **State** — `clkNat_add_eight_of_cpuState_bounds`: the row's own `clk + 8` edge.
* **Memory** — `prevLow_val_lt_of_accessTimestamp` / `memoryTimeNat_lt_of_accessTimestamp`: the
  register-access timestamp comparison, i.e. SP1's `prev_clk < access_clk`.  The row's own
  `Readers.RegisterAccessTimestamp.Spec` bounds only the *difference* `clk_target − prev_low − 1`, so
  as field elements the prior clock could be the huge representative `p + clk_target − 1 − diff` and
  the ℕ-level comparison would fail.  The missing piece is a bound on `prev_low` itself, which is a
  **received** fact: the memory channel's `Channels.MemoryMsg.ClkBound` guarantee, proved by whoever
  pushed the prior record.  This is exactly the gap SP1's own AIR comment names
  (`crates/core/machine/src/air/memory.rs`: the underflow argument is valid "as long as both
  `current_comp_val, prev_comp_value` are range-checked to be `< 2^24` and as long as we're working in
  a field larger than `2 * 2^24`") — and `Fact (2 ^ 25 < p)` is precisely that `2 · 2^24` field bound.
-/

namespace SP1Clean.Soundness.TimeExtraction

open SP1Clean.Semantics
open SP1Clean.Channels (MemoryMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- The two CPUState range checks make the field-valued low-clock increment an exact natural-number
increment.  The stronger machine-level field bound leaves enough room for the final `+ 8` after the
24-bit clock limbs have been reconstructed. -/
theorem clkNat_add_eight_of_cpuState_bounds (clkHigh clk0 clk1 : ZMod p)
    (clk0Bound : ((clk0 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13)
    (clk1Bound : clk1.val < 2 ^ 8) :
    clkNat clkHigh (clk0 + clk1 * 65536 + 8) =
      clkNat clkHigh (clk0 + clk1 * 65536) + 8 := by
  let scaled := (clk0 - 1) * (8 : ZMod p)⁻¹
  have eightNe : (8 : ZMod p) ≠ 0 := val_8_ne_zero
  have scaledBound : scaled.val < 2 ^ 13 := clk0Bound
  have reconstruct : scaled * 8 + 1 = clk0 := by
    dsimp only [scaled]
    rw [mul_assoc, inv_mul_cancel₀ eightNe, mul_one]
    ring_nf
  have scaledMulLt : scaled.val * (8 : ZMod p).val < p := by
    rw [val_8_zmod_p]
    have := Fact.out (p := 2 ^ 25 < p)
    omega
  have scaledMulVal : (scaled * 8).val = scaled.val * 8 := by
    rw [ZMod.val_mul_of_lt scaledMulLt, val_8_zmod_p]
  have clk0AddLt : (scaled * 8).val + (1 : ZMod p).val < p := by
    rw [scaledMulVal, ZMod.val_one]
    have := Fact.out (p := 2 ^ 25 < p)
    omega
  have clk0Val : clk0.val = scaled.val * 8 + 1 := by
    calc
      clk0.val = (scaled * 8 + 1).val := congrArg ZMod.val reconstruct.symm
      _ = (scaled * 8).val + (1 : ZMod p).val := ZMod.val_add_of_lt clk0AddLt
      _ = scaled.val * 8 + 1 := by rw [scaledMulVal, ZMod.val_one]
  have highLimbMulLt : clk1.val * (65536 : ZMod p).val < p := by
    rw [val_65536_zmod_p]
    have := Fact.out (p := 2 ^ 25 < p)
    omega
  have highLimbVal : (clk1 * 65536).val = clk1.val * 65536 := by
    rw [ZMod.val_mul_of_lt highLimbMulLt, val_65536_zmod_p]
  have lowAddLt : clk0.val + (clk1 * 65536).val < p := by
    rw [clk0Val, highLimbVal]
    have := Fact.out (p := 2 ^ 25 < p)
    omega
  have lowVal : (clk0 + clk1 * 65536).val = clk0.val + clk1.val * 65536 := by
    rw [ZMod.val_add_of_lt lowAddLt, highLimbVal]
  have incrementAddLt : (clk0 + clk1 * 65536).val + (8 : ZMod p).val < p := by
    rw [lowVal, clk0Val, val_8_zmod_p]
    have := Fact.out (p := 2 ^ 25 < p)
    omega
  have incrementedVal : (clk0 + clk1 * 65536 + 8).val =
      (clk0 + clk1 * 65536).val + 8 := by
    rw [ZMod.val_add_of_lt incrementAddLt, val_8_zmod_p]
  simp only [clkNat, incrementedVal]
  omega

/-- Contract-level form used by instruction-row proofs. -/
theorem clkNat_add_eight_of_cpuState_spec (input : Readers.CPUState.Inputs (ZMod p))
    (real : input.is_real = 1) (spec : Readers.CPUState.Spec input)
    (clkInc : input.clk_inc = 8) :
    clkNat input.cols.clk_high
        (input.cols.clk_0_16 + input.cols.clk_16_24 * 65536 + input.clk_inc) =
      clkNat input.cols.clk_high
        (input.cols.clk_0_16 + input.cols.clk_16_24 * 65536) + 8 := by
  rw [clkInc]
  exact clkNat_add_eight_of_cpuState_bounds _ _ _ (spec real).1 (spec real).2

/-! ## The memory axis — `prev_clk < access_clk` -/

/-- **The register-access timestamp comparison, in `ℕ`.**  The row's timestamp block decomposes the
field difference as `clk_target = prev_low + 1 + (diff_low_limb + diff_high * 2^16)` with
`diff_low_limb < 2^16` and `diff_high < 2^8`, so the difference is a genuine `< 2^24` natural number.
Adding the *received* bound `prev_low < 2^24` (the memory channel's `Channels.MemoryMsg.ClkBound`
guarantee on the pulled prior record) keeps the whole sum below `2^25 < p`, so no wraparound can
occur and the field equation transports to `ℕ` verbatim.

Neither hypothesis is optional: without `prevBound` the prior clock could be the huge representative
`p + clk_target - 1 - diff`, which satisfies every local constraint while sitting *after* the access
in `ℕ`.  That is why the bound has to ride on the bus.  (The access clock's own bound is *not* needed
— it follows, since `clk_target.val = prev_low.val + 1 + diff`.) -/
theorem prevLow_val_lt_of_accessTimestamp (clk_target prev_low diff_low_limb : ZMod p)
    (prevBound : prev_low.val < 2 ^ 24)
    (diffLow : diff_low_limb.val < 2 ^ 16)
    (diffHigh : ((clk_target - prev_low - 1 - diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8) :
    prev_low.val < clk_target.val := by
  have hp := Fact.out (p := 2 ^ 25 < p)
  set high := (clk_target - prev_low - 1 - diff_low_limb) * (65536 : ZMod p)⁻¹ with highDef
  have reconstruct : clk_target = prev_low + (1 + (diff_low_limb + high * 65536)) := by
    rw [highDef, mul_assoc, inv_mul_cancel₀ val_65536_ne_zero, mul_one]
    ring
  have highMulVal : (high * 65536).val = high.val * 65536 := by
    rw [ZMod.val_mul_of_lt (by rw [val_65536_zmod_p]; omega), val_65536_zmod_p]
  have diffVal : (diff_low_limb + high * 65536).val = diff_low_limb.val + high.val * 65536 := by
    rw [ZMod.val_add_of_lt (by rw [highMulVal]; omega), highMulVal]
  have succVal : (1 + (diff_low_limb + high * 65536)).val
      = 1 + (diff_low_limb.val + high.val * 65536) := by
    rw [ZMod.val_add_of_lt (by rw [diffVal, ZMod.val_one]; omega), diffVal, ZMod.val_one]
  have targetVal : clk_target.val = prev_low.val + (1 + (diff_low_limb.val + high.val * 65536)) := by
    rw [reconstruct, ZMod.val_add_of_lt (by rw [succVal]; omega), succVal]
  omega

/-- **The payoff, at the bus layer**: a pulled prior Memory record strictly predates the record the
row pushes for the same access — `Soundness/TouchChains.lean`'s `TouchOK.pull_lt_push`.

Both messages carry the row's own `clk_high` (SP1's register-access variant of the timestamp check
asserts the high limbs are equal, `eval_register_access_timestamp`), so the comparison reduces to the
low limbs and is settled by `prevLow_val_lt_of_accessTimestamp`.  The three inputs are exactly what a
migrated chip has on hand: the pulled record's channel guarantee, the row's timestamp-block `Spec`,
and the structural identification of the two messages' clock fields. -/
theorem memoryTimeNat_lt_of_accessTimestamp (prior pushed : MemoryMsg (ZMod p))
    (cols : Extracted.RegisterAccessTimestamp (ZMod p)) (is_real : ZMod p)
    (real : is_real = 1)
    (prevBound : MemoryMsg.ClkBound prior)
    (spec : Readers.RegisterAccessTimestamp.Spec
      ⟨cols, is_real, pushed.clk_low⟩)
    (sameHigh : prior.clk_high = pushed.clk_high)
    (priorLow : prior.clk_low = cols.prev_low) :
    MemoryMsg.timeNat prior < MemoryMsg.timeNat pushed := by
  obtain ⟨diffLow, diffHigh⟩ := spec real
  simp only [MemoryMsg.timeNat, clkNat, sameHigh, priorLow]
  have := prevLow_val_lt_of_accessTimestamp pushed.clk_low cols.prev_low cols.diff_low_limb
    (priorLow ▸ prevBound) diffLow diffHigh
  omega

variable [Fact (2 ^ 17 < p)]

/-- **Folded-`Spec` variant for decoded-row use** (the Clean "keep the child `Spec` folded" discipline —
`clean/doc/performance-problems.md`).  Takes the composed reader's `RegisterAccessCols.Spec` over
**variable** `accessCols`/`is_real`/`clk_target`, so a concrete decoded-row `RegisterAccessCols.Spec ⟨…⟩`
matches it by *pattern* on the shared head symbol — no `whnf` into the eval-struct.  All spelling
reconciliation happens on the three **scalar** bridges (`sameHigh`/`priorLow`/`targetClk`), which cross
the decoder↔circuit spelling cheaply, instead of unifying the whole `access_timestamp` struct.  This is
what lets `addChip_rowAligned` build the `prev_clk < access_clk` order straight from the chip `Spec`
without the metavariable-normalization blowup. -/
theorem memoryTimeNat_lt_of_registerAccessCols (prior pushed : MemoryMsg (ZMod p))
    (accessCols : Extracted.RegisterAccessCols (ZMod p)) (is_real clk_target : ZMod p)
    (real : is_real = 1)
    (prevBound : MemoryMsg.ClkBound prior)
    (spec : Readers.RegisterAccessCols.Spec ⟨accessCols, is_real, clk_target⟩)
    (sameHigh : prior.clk_high = pushed.clk_high)
    (priorLow : prior.clk_low = accessCols.access_timestamp.prev_low)
    (targetClk : pushed.clk_low = clk_target) :
    MemoryMsg.timeNat prior < MemoryMsg.timeNat pushed := by
  obtain ⟨diffLow, diffHigh⟩ := spec real
  simp only [MemoryMsg.timeNat, clkNat, sameHigh, priorLow, targetClk]
  have := prevLow_val_lt_of_accessTimestamp clk_target accessCols.access_timestamp.prev_low
    accessCols.access_timestamp.diff_low_limb (priorLow ▸ prevBound) diffLow diffHigh
  omega

end SP1Clean.Soundness.TimeExtraction
