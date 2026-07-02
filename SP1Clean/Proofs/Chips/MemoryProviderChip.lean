import SP1Clean.Model.Channels
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
(`Model/Channels.lean`): the four 16-bit value limbs.

This is the in-circuit provider's push side: a single Clean `GeneralFormalCircuit` whose `main`
range-checks `v0..v3` in-circuit with `Gadgets.ToBits.rangeCheck` (genuine bit-decomposition `assertion`s —
not lookups, so it owes nothing to a bus), witnesses a multiplicity `m`, and `memoryChannel.pushIf m`-pushes
the boundary record; soundness discharges the push's `MemoryMsg.isU64` requirement from the range checks. The
clock/address fields (`clk_high`, `clk_low`, `addr0..2`) are part of the key but unconstrained by `isU64`, so
they are pushed through unchecked (the boundary record's claimed key; its `initSpec` validity is the
`MemoryProvider` predicate's job, `Proofs/Chips/MemoryProvider.lean`).

The Program-bus sibling is `Proofs/Chips/ProgramProviderChip.lean`; the byte-bus one `Chips/ByteChip`. -/

namespace SP1Clean.MemoryProviderChip

open Circuit
open SP1Clean.Channels (memoryChannel MemoryMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- `p > 2`, needed by `Gadgets.ToBits.rangeCheck`'s `Fact (p > 2)`. `local` so it does not leak. -/
local instance : Fact (p > 2) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

omit [Fact p.Prime] in
/-- `2^16 < p` — the width bound `rangeCheck 16` needs for the value limbs. -/
lemma two_pow_sixteen_lt : (2 : ℕ) ^ 16 < p := by
  have h := Fact.out (p := 2 ^ 17 < p)
  have h2 : (2 : ℕ) ^ 16 < 2 ^ 17 := by norm_num
  omega

/-- Range-checks the four value limbs `v0..v3` (16-bit each), witnesses a multiplicity `m`, and pushes the
memory-boundary record `input` onto `memoryChannel` with multiplicity `m`. -/
def main (input : Var MemoryMsg (ZMod p)) : Circuit (ZMod p) Unit := do
  assertion (Gadgets.ToBits.rangeCheck 16 two_pow_sixteen_lt) input.v0
  assertion (Gadgets.ToBits.rangeCheck 16 two_pow_sixteen_lt) input.v1
  assertion (Gadgets.ToBits.rangeCheck 16 two_pow_sixteen_lt) input.v2
  assertion (Gadgets.ToBits.rangeCheck 16 two_pow_sixteen_lt) input.v3
  let m ← witnessField (fun _ => 1)
  memoryChannel.pushIf m input

/-- The Memory-boundary provider: pushes a boundary record whose value limbs it range-checks in-circuit.
`Spec` is `MemoryMsg.isU64` (the value well-formedness the consumers pull-and-derive); soundness discharges
the push's `isU64` requirement from the range checks. -/
def circuit : GeneralFormalCircuit (ZMod p) MemoryMsg unit where
  main
  Spec input _ _ := MemoryMsg.isU64 input
  ProverAssumptions input _ _ := MemoryMsg.isU64 input
  channelsWithRequirements := [memoryChannel.toRaw]
  soundness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck, MemoryMsg.isU64]
    obtain ⟨hv0, hv1, hv2, hv3⟩ := h_holds
    have hrow : input_v0.val < 2 ^ 16 ∧ input_v1.val < 2 ^ 16 ∧ input_v2.val < 2 ^ 16 ∧
        input_v3.val < 2 ^ 16 := ⟨hv0, hv1, hv2, hv3⟩
    exact ⟨hrow, fun _ _ => hrow⟩
  completeness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck, MemoryMsg.isU64]
    obtain ⟨hv0, hv1, hv2, hv3⟩ := h_assumptions
    exact ⟨hv0, hv1, hv2, hv3⟩

end SP1Clean.MemoryProviderChip
