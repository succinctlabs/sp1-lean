import SP1Clean.Math.Word
import SP1Clean.Extracted.MemoryAccess
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # System-table chip contracts: StateBump and MemoryBump (W3, external report Finding 2)

The `Inputs` row structs and semantic `Spec`s of the two SP1 **system tables** the drift-stable Core
ensemble carries beside the 25 instruction chips: `StateBump`
(`../sp1 crates/core/machine/src/adapter/bump.rs`) and `MemoryBump`
(`../sp1 crates/core/machine/src/memory/bump.rs`). Both are provider-segment tables — no
`ChipKind.advance`, no program fetch; their whole meaning is a bus-side canonicalization:

- **StateBump** pulls a State message whose `(clk, pc)` limbs may be **non-canonical** (an instruction
  row pushes `clk_low + 8`/`+ 264` and `pc0 + 4` without re-range-checking, so a long shard overflows
  the 24-bit low clock and a 64 KiB boundary overflows `pc0`) and pushes the same `(clk, pc)`
  re-limbed canonically: the clock's `2^24` overflow carried into `clk_high` (`is_clk`), the pc's
  `2^16` limb overflows carried up the three limbs. Without it the capstone silently covered only
  shards of ≲ `2^21` rows that never cross a pc boundary — the report's Finding 2.
- **MemoryBump** refreshes one **register** record's timestamp: it pulls the record and pushes it at
  a strictly later, canonically-limbed clock (same address, same value). SP1 needs it because an
  accessing row range-checks only the timestamp *difference* window; a record untouched for `≥ 2^24`
  ticks must be re-touched before its next genuine access.

**Spec shape — evidence, not ℕ-lifts** (the DivRem evidence-family precedent). Each `Spec` exports
the row's full local content: the pushed limbs' range facts and the exact field-level relation
between the pulled and pushed messages (binary carries/borrows with limb equations). The ℕ-level
consequences — `canon (pull) = canon (push)` for the state trail, the lexicographic timestamp
increase for the memory refresh — are **conditional on the pulled side being in range** (a pulled
limb can a priori be the huge representative `p - 1`), which is exactly what the W3 goodness-filter
pass establishes globally; they are derived where consumed (`Soundness/`), never claimed here. -/

namespace SP1Clean

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace StateBumpChip

/-- The native StateBump row — field-for-field SP1's `StateBumpCols` (`adapter/bump.rs`; the
extracted flat vector `Extracted/SystemOracle/StateBump.lean` lists the same 14 cells in this
order). `clk_high`/`clk_low`/`pc0..2` are the **pulled** (possibly non-canonical) state;
`next_clk_*` are the four canonical limbs of the pushed clock (`clk_high' = next_clk_24_32 +
next_clk_32_48 · 2^8`, `clk_low' = next_clk_0_16 + next_clk_16_24 · 2^16`); `next_pc0..2` the pushed
canonical pc limbs; `is_clk` the `2^24` clock-carry bit; `is_real` the row selector. -/
structure Inputs (F : Type) where
  next_clk_32_48 : F
  next_clk_24_32 : F
  next_clk_16_24 : F
  next_clk_0_16 : F
  clk_high : F
  clk_low : F
  next_pc0 : F
  next_pc1 : F
  next_pc2 : F
  pc0 : F
  pc1 : F
  pc2 : F
  is_clk : F
  is_real : F
deriving ProvableStruct

/-- StateBump's semantic contract. Ungated (they hold on padding rows too, as upstream):
the two selector bits are boolean, and the pc carry cascade — binary limb borrows `b0`, `b1` with
`pc = next_pc` limb-wise up to `2^16` carries and **no carry out of the top limb** — which makes the
48-bit pc value exactly preserved as a field identity. Gated on `is_real = 1`: the pushed clock
limbs are canonical (`next_clk_0_16 ≡ 1 (mod 8)` scaled 13-bit, the two middle limbs bytes, the top
limb 16-bit — SP1's clock is `≡ 1 (mod 8)` because it starts at 1 and steps by 8/264), the pushed pc
limbs are 16-bit, and the pulled clock equals the pushed clock plus the `is_clk · 2^24` carry moved
between the limbs. -/
def Spec (r : Inputs (ZMod p)) : Prop :=
  (r.is_real = 0 ∨ r.is_real = 1) ∧
  (r.is_clk = 0 ∨ r.is_clk = 1) ∧
  (∃ b0 b1 : ZMod p, (b0 = 0 ∨ b0 = 1) ∧ (b1 = 0 ∨ b1 = 1) ∧
    r.pc0 = r.next_pc0 + b0 * 65536 ∧
    b0 + r.pc1 = r.next_pc1 + b1 * 65536 ∧
    b1 + r.pc2 = r.next_pc2) ∧
  (r.is_real = 1 →
    ((r.next_clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧
    r.next_clk_16_24.val < 2 ^ 8 ∧ r.next_clk_24_32.val < 2 ^ 8 ∧
    r.next_clk_32_48.val < 2 ^ 16 ∧
    r.next_pc0.val < 2 ^ 16 ∧ r.next_pc1.val < 2 ^ 16 ∧ r.next_pc2.val < 2 ^ 16 ∧
    r.next_clk_24_32 + r.next_clk_32_48 * 256 = r.clk_high + r.is_clk ∧
    r.next_clk_0_16 + r.next_clk_16_24 * 65536 + r.is_clk * 16777216 = r.clk_low)

end StateBumpChip

namespace MemoryBumpChip

/-- The native MemoryBump row — field-for-field SP1's `MemoryBumpCols` (`memory/bump.rs`; the
extracted flat vector `Extracted/SystemOracle/MemoryBump.lean` lists the same 15 cells in this
order). `access` is the standard `MemoryAccessCols` carrier (the pulled record's value word + the
five timestamp-comparison columns, exactly as in the load/store chips); `clk_*` the four canonical
limbs of the **refreshed** timestamp the row pushes (`clk_high' = clk_24_32 + clk_32_48 · 2^8`,
`clk_low' = clk_0_16 + clk_16_24 · 2^16`); `addr` the register index; `is_real` the row selector. -/
structure Inputs (F : Type) where
  access : Extracted.MemoryAccessCols F
  clk_32_48 : F
  clk_24_32 : F
  clk_16_24 : F
  clk_0_16 : F
  addr : F
  is_real : F
deriving ProvableStruct

/-- MemoryBump's semantic contract (`is_real`-gated; ungated it proves only `is_real` boolean).
On a real row: the pulled record's received guarantees (`Word.isU64` of the value it re-pushes, and
the pulled low clock's 24-bit `ClkBound`); the four refreshed-clock limbs in range (16/8/8/16 bits,
so both recombined limbs are `< 2^24` by construction); the address a register index (`< 32`, the
byte-bus `LTU` fact); and the `eval_memory_access_timestamp` comparison evidence — `compare_low`
boolean, the high limbs equal when it selects the low comparison, and the selected refreshed limb
exceeding the selected pulled limb by exactly `1 + diff` with `diff` range-checked to 24 bits. The
ℕ-level lexicographic increase `(prev_high, prev_low) < (clk_high', clk_low')` follows only once the
pulled `prev_high` is known 24-bit — the global fact W3 derives at the trail from the per-location
Memory balance (`pushGood`/`pullGood` in `Soundness/AIR.lean`), not a row-local claim. -/
def Spec (r : Inputs (ZMod p)) : Prop :=
  (r.is_real = 0 ∨ r.is_real = 1) ∧
  (r.is_real = 1 →
    Word.isU64 r.access.prev_value ∧
    r.access.access_timestamp.prev_low.val < 2 ^ 24 ∧
    r.clk_0_16.val < 2 ^ 16 ∧ r.clk_32_48.val < 2 ^ 16 ∧
    r.clk_16_24.val < 2 ^ 8 ∧ r.clk_24_32.val < 2 ^ 8 ∧
    r.addr.val < 32 ∧
    (r.access.access_timestamp.compare_low = 0 ∨ r.access.access_timestamp.compare_low = 1) ∧
    r.access.access_timestamp.compare_low *
      (r.clk_24_32 + r.clk_32_48 * 256 - r.access.access_timestamp.prev_high) = 0 ∧
    (r.access.access_timestamp.compare_low * (r.clk_0_16 + r.clk_16_24 * 65536)
        + (1 - r.access.access_timestamp.compare_low) * (r.clk_24_32 + r.clk_32_48 * 256))
      - (r.access.access_timestamp.compare_low * r.access.access_timestamp.prev_low
        + (1 - r.access.access_timestamp.compare_low) * r.access.access_timestamp.prev_high) - 1
      = r.access.access_timestamp.diff_low_limb
        + r.access.access_timestamp.diff_high_limb * 65536 ∧
    r.access.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
    r.access.access_timestamp.diff_high_limb.val < 2 ^ 8)

end MemoryBumpChip

end SP1Clean
