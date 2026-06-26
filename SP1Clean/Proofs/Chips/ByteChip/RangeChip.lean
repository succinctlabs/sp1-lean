import SP1Clean.Model.Channels
import SP1Clean.Model.ByteTable
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Bits
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The in-circuit `RangeChip` provider (push side of SP1's variable-width range table)

SP1's `RangeChip` (`crates/core/machine/src/range/{air,columns}.rs`) is a **preprocessed** table over
all `(a, bits)` with `a < 2^bits`, `bits ≤ 16` (`RangePreprocessedCols { a, bits }`). Its AIR is a single
`receive_byte(ByteOpcode::Range(6), a, bits, 0, mult)` — on the Byte bus that *receive* is a **push** of
the valid range row `⟨6, a, bits, 0⟩`, balanced against the consumers' pulls. SP1's consumers pull this
form for `bits ∈ {8, 13, 16}` (CPUState's `clk_0_16` 13-bit check, RegisterAccessTimestamp's `< 2^16` /
`< 2^8` timestamp checks, AddOperation's limb checks).

Clean has no "trusted preprocessed table" primitive for channels, so a finished-`byteChannel` **provider
must re-prove each pushed row valid in-circuit** — the `ByteRowSpec` membership predicate
(`Model/ByteTable.lean`), here `a.val < 2^bits` via `byteRowSpec_range`. This is strictly more work than
SP1's preprocessing (where validity is definitional), but it replaces the trusted byte-bus balance
assumption (`Soundness/ByteConsistency.lean`'s `TraceByteLink`) with a Lean proof.

## Fixed-width family

SP1's `bits` is a runtime column (`≤ 16`), so a fixed `Gadgets.ToBits.rangeCheck n` does not directly
apply to the genuinely variable-width row. This module builds the **fixed-width family**: a provider
`circuit n hn` parameterized by a *compile-time* width `n` (with `2^n < p`). For each fixed `n` it is a
faithful `RangeChip` provider — it pushes exactly SP1's `⟨6, a, (n : F), 0⟩` rows for `a < 2^n`. The
named instantiations `circuit8`/`circuit13`/`circuit16` cover **every** width SP1's machine actually
pulls. The genuinely variable-`bits` provider (one circuit serving all widths at once) is a separate,
harder construction left to a follow-up.

Sibling: `Proofs/Chips/ByteChip/ByteChip.lean` (the `ByteChip` provider, opcodes 0..5 over `(b,c)`). -/

namespace SP1Clean.RangeChip

open Circuit
open SP1Clean (ByteRow ByteRowSpec)
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- `p > 2` (needed by `Gadgets.ToBits.rangeCheck`'s `Fact (p > 2)`), from `2^17 < p`. Kept **`local`** so
importing this provider (its wiring into `SP1Clean.lean`) does not leak a global `Fact (p > 2)` derived
from `Fact (2^17 < p)` — which would make downstream `omit [Fact (2^17 < p)]` clauses illegal (cf. the
`local instance : NeZero p` note in `Model/ByteTable.lean`). -/
local instance : Fact (p > 2) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

omit [Fact p.Prime] in
/-- `2^n < p` for any width `n ≤ 16` SP1's table uses (`bits ≤ 16`), from `2^17 < p`. -/
lemma two_pow_lt {n : ℕ} (h : n ≤ 16) : (2 : ℕ) ^ n < p := by
  have hp := Fact.out (p := 2 ^ 17 < p)
  have h1 : (2 : ℕ) ^ n ≤ 2 ^ 16 := Nat.pow_le_pow_right (by norm_num) h
  have h2 : (2 : ℕ) ^ 16 < 2 ^ 17 := by norm_num
  omega

/-- The committed value `a` — the `a` slot of SP1's `RangeChip` send `⟨6, a, bits, 0⟩`. The bit-width
`bits` is the compile-time parameter `n`; instantiated at the widths consumers pull (8, 13, 16). -/
structure Inputs (F : Type) where
  a : F
deriving ProvableStruct

/-- Range-checks `a < 2^n` in-circuit (Clean `rangeCheck n` — a genuine bit decomposition, *not* a byte
lookup, so the provider owes nothing to the bus it provides), witnesses a multiplicity `m` (the LogUp
lookup count), and pushes the `Range` row `⟨6, a, (n : F), 0⟩` onto `byteChannel` with multiplicity `m`. -/
def main (n : ℕ) (hn : 2 ^ n < p) (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertion (Gadgets.ToBits.rangeCheck n hn) input.a
  let m ← witnessField (fun _ => 1)
  byteChannel.pushIf m
    (⟨6, input.a, Expression.const ((n : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))

/-- The `RangeChip` provider at a fixed width `n`: pushes `⟨6, a, n, 0⟩` for an in-circuit
range-checked `a < 2^n`. `Spec` is `a.val < 2^n`; soundness derives it from the `rangeCheck` subcircuit
and discharges the push's `ByteRowSpec` requirement via `byteRowSpec_range`. -/
def circuit (n : ℕ) (hn : 2 ^ n < p) : GeneralFormalCircuit (ZMod p) Inputs unit where
  main := main n hn
  Spec input _ _ := input.a.val < 2 ^ n
  ProverAssumptions input _ _ := input.a.val < 2 ^ n
  channelsWithRequirements := [byteChannel.toRaw]
  soundness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck]
    have hnp : n < p := lt_trans Nat.lt_two_pow_self hn
    exact ⟨h_holds, fun _ _ => (byteRowSpec_range input_a hnp).mpr h_holds⟩
  completeness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck]
    exact h_assumptions

/-! ## Concrete instantiations at the widths SP1's consumers pull -/

/-- The 8-bit `Range` provider (`< 2^8`) — RegisterAccessTimestamp's `< 2^8` timestamp check. -/
def circuit8 : GeneralFormalCircuit (ZMod p) Inputs unit := circuit 8 (two_pow_lt (by norm_num))

/-- The 13-bit `Range` provider (`< 2^13`) — CPUState's shifted `clk_0_16` check. -/
def circuit13 : GeneralFormalCircuit (ZMod p) Inputs unit := circuit 13 (two_pow_lt (by norm_num))

/-- The 16-bit `Range` provider (`< 2^16`) — RegisterAccessTimestamp's `< 2^16` / AddOperation limbs. -/
def circuit16 : GeneralFormalCircuit (ZMod p) Inputs unit := circuit 16 (two_pow_lt (by norm_num))

end SP1Clean.RangeChip
