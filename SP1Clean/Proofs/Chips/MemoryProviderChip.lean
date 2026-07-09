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
the push's `MemoryMsg.isU64` requirement directly from the assertion's `Spec` (`Word.isU64 value`). The
clock/address fields (`clk_high`, `clk_low`, `addr0..2`) are part of the key but unconstrained by `isU64`, so
they are pushed through unchecked (the boundary record's claimed key; its `initSpec` validity is the
`MemoryProvider` predicate's job, `Proofs/Chips/MemoryProvider.lean`).

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
  let m ← witnessField 1
  assertZero (m * (m - 1))
  memoryChannel.pushIf m input

/-- The Memory-boundary provider: pushes a boundary record whose value word it range-checks in-circuit.
`Spec` is `MemoryMsg.isU64` (the value well-formedness the consumers pull-and-derive); soundness discharges
the push's `isU64` requirement from the `WordRangeCheck` assertion's `Spec`. -/
def circuit : GeneralFormalCircuit (ZMod p) MemoryMsg unit where
  main
  Spec input _ _ := MemoryMsg.isU64 input
  ProverAssumptions input _ _ := MemoryMsg.isU64 input
  channelsWithRequirements := [memoryChannel.toRaw]
  soundness := by
    circuit_proof_start [WordRangeCheck.circuit, WordRangeCheck.Assumptions, WordRangeCheck.Spec,
      MemoryMsg.isU64]
    exact ⟨h_holds.1, fun _ _ => h_holds.1⟩
  completeness := by
    circuit_proof_start [WordRangeCheck.circuit, WordRangeCheck.Assumptions, WordRangeCheck.Spec,
      MemoryMsg.isU64]
    exact ⟨h_assumptions, by simp [h_env]⟩

end SP1Clean.MemoryProviderChip
