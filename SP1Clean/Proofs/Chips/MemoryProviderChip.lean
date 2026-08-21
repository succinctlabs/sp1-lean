import SP1Clean.Model.Channels
import SP1Clean.Native.Operations.WordRangeCheck
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Bits
import Clean.Gadgets.Boolean
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The in-circuit Memory-boundary provider (push side of SP1's memory init/finalize chips)

SP1's memory soundness is timestamp-ordered offline memory on a closed bus: every access `send`s the prior
value and `receive`s the new value, and the per-address chain's two unmatched endpoints (genesis prior, final
value) are materialized by the **Memory Global init/finalize** chips. On our W11-flipped Memory bus those
boundary rows are **pushes** of `MemoryMsg.isU64`-valid value words, balanced against the chips' read-prior
pulls. As with the Program ROM provider, Clean has no "trusted preprocessed table" primitive, so a
finished-`memoryChannel` **provider must re-prove each pushed value `U64` in-circuit** — `MemoryMsg.isU64`
(`Model/Channels.lean`): the 4-limb `value` word is a `U64`.

This is the in-circuit provider's push side: a single Clean `GeneralFormalCircuit` whose `main`
range-checks the whole `value` word in-circuit with one `WordRangeCheck.circuit` assertion (genuine
bit-decompositions — not lookups, so it owes nothing to a bus; `Native/Operations/WordRangeCheck.lean`),
witnesses a multiplicity `m`, and `memoryChannel.pushIf m`-pushes the boundary record; soundness discharges
the push's `MemoryMsg.isU64` requirement directly from the assertion's `Spec` (`Word.isU64 value`), and the
channel's `MemoryMsg.ClkBound` requirement from an inline `assertZero input.clk_low` gate — matching SP1's
memory-init interaction, which literally passes `Expr::zero()` for the clock limbs. W3 pins the high
limb the same way (`assertZero input.clk_high`, surfaced as the `Spec`'s third conjunct): the boundary
record's whole timestamp is zero, which is what the timestamp-premise derivation consumes. The address
fields (`addr0..2`) remain part of the key but unconstrained (the boundary record's claimed key; its
`initSpec` validity is the `MemoryProvider` predicate's job, `Proofs/Chips/MemoryProvider.lean`).

The Program-bus sibling is `Proofs/Chips/ProgramProviderChip.lean`; the byte-bus one `Chips/ByteChip`. -/

namespace SP1Clean.MemoryProviderChip

open Circuit
open SP1Clean.Channels (memoryChannel MemoryMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Range-checks the whole 4-limb `value` word (16-bit limbs, one `WordRangeCheck` assertion), witnesses a
**boolean** multiplicity `m` (inline shallow `assertZero (m*(m-1))` — the Phase-0c gate idiom, so the
capstone seam can extract mult-binarity from `ConstraintsHold.Shallow`; the field→ℤ balance translation
`isConsistentBalanced_of_balancedInteractions` needs every memory-bus multiplicity in `{-1, 0, 1}`, and
SP1's memory-global chips are one boolean-gated row per address), and pushes the memory-boundary record
`input` onto `memoryChannel` with multiplicity `m`. -/
def main (input : Var MemoryMsg (ZMod p)) : Circuit (ZMod p) Unit := do
  assertion WordRangeCheck.circuit input.value
  -- The pushed boundary clock is pinned to `0`, which is what discharges the channel's
  -- `MemoryMsg.ClkBound` requirement. This is *exactly* SP1's memory-init interaction, which passes
  -- `AB::Expr::zero(), AB::Expr::zero()` for `(clk_high, clk_low)` rather than a witnessed column
  -- (`crates/core/machine/src/memory/global.rs`, the `MemoryChipType::Initialize` branch) — so the
  -- gate is a faithfulness improvement, not an extra restriction. A shallow `assertZero` (no witness
  -- columns), so `localLength` is unchanged.
  assertZero input.clk_low
  -- W3 (external report Findings 2 and 8.2): the boundary clock's **high** limb is pinned to `0` as
  -- well — again exactly SP1's memory-init interaction (`Expr::zero()` for both
  -- `(clk_high, clk_low)`). This is what lets the trail derive every memory pull's `clk_high` bound
  -- from push-side facts alone (init `= 0`, instruction rows' state goodness, bump rows' range
  -- checks); that derivation is `pushGood`/`pullGood` in `Soundness/AIR.lean`, and it is why the
  -- capstone carries no explicit memory-timestamp-range premise.
  assertZero input.clk_high
  let m ← witnessField 1
  assertZero (m * (m - 1))
  memoryChannel.pushIf m input

/-- The Memory-boundary provider: pushes a boundary record whose value word it range-checks in-circuit
and whose access clock — both limbs — it pins to `0`. `Spec` is the memory channel's `Guarantees`
(`MemoryMsg.isU64 ∧ MemoryMsg.ClkBound`, the facts the consumers pull-and-derive) plus the W3
`clk_high = 0` boundary-time fact the timestamp-premise derivation consumes; soundness discharges the
push's requirement from the `WordRangeCheck` assertion's `Spec` and the two clock gates. -/
def circuit : GeneralFormalCircuit (ZMod p) MemoryMsg unit where
  main
  Spec input _ _ := MemoryMsg.isU64 input ∧ MemoryMsg.ClkBound input ∧ input.clk_high = 0
  ProverAssumptions input _ _ :=
    MemoryMsg.isU64 input ∧ input.clk_low = 0 ∧ input.clk_high = 0
  channelsWithRequirements := [memoryChannel.toRaw]
  soundness := by
    circuit_proof_start [WordRangeCheck.circuit, WordRangeCheck.Assumptions, WordRangeCheck.Spec,
      MemoryMsg.isU64, MemoryMsg.ClkBound]
    obtain ⟨hvalue, hclk, hclkhi, -⟩ := h_holds
    refine ⟨⟨hvalue, ?_, hclkhi⟩, fun _ _ => ⟨hvalue, ?_⟩⟩ <;>
      simp only [MemoryMsg.ClkBound, hclk, ZMod.val_zero, Nat.two_pow_pos]
  completeness := by
    circuit_proof_start [WordRangeCheck.circuit, WordRangeCheck.Assumptions, WordRangeCheck.Spec,
      MemoryMsg.isU64]
    exact ⟨h_assumptions.1, h_assumptions.2.1, h_assumptions.2.2, by simp [h_env]⟩

end SP1Clean.MemoryProviderChip
