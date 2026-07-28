import SP1Clean.Proofs.Chips.MemoryProviderChip
import SP1Clean.Proofs.Chips.MemoryFinalizeChip
import Clean.Air.Vm

/-! # Finishing the Memory bus (boundary half) — the memory-provider segment of the `SoundEnsemble`

The push side of SP1's memory init/finalize chips, assembled into a Clean `SoundEnsemble` and used to
**finish `memoryChannel`** against the boundary provider. Once `memoryChannel` is a *finished* channel, a CPU
reader that `pullIf`s a memory read-prior (the W11 polarity flip) gets its `MemoryMsg.isU64` guarantee from
the bus balance against this provider — the guarantee becomes a verifier obligation backed by an in-circuit
provider, not the `assumeGuarantees` hand-wave the `pullIf` carries in isolation.

This mirrors `ProgramProviderEnsemble`/`ByteChip/Ensemble.lean`: `memoryChannel.Guarantees` is
`MemoryMsg.isU64`, which is **value-only / message-independent**, so the channel finishes against the single
generic `MemoryProviderChip.circuit` (the table of all `isU64`-valid value words).

**Scope (boundary half only).** This finishes `memoryChannel` among *providers* — there are no CPU chips in
this ensemble, so the read-back/write **pushes** the chips owe (`memoryChannel ∈ their channelsWithRequirements`)
are NOT yet reconciled here; that whole-machine grounding (memory as a VM channel; the `reqs_disjoint`
`addVm` seam) is the deferred Phase-5 work (`Soundness/MemoryVm.lean`). This module is the matching provider
artifact, ready to compose, exactly as `programProviderEnsemble` is. Generic over `PublicIO`. -/

namespace SP1Clean.MemoryProviderChip

open Circuit
open SP1Clean.Channels (memoryChannel)
open Air.Flat

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The Memory-bus provider segment: add the in-circuit memory-boundary provider, then **finish
`memoryChannel`**. The provider has `memoryChannel` in its `channelsWithRequirements` (it proves
`MemoryMsg.isU64` for the row it pushes) and `[]` in its `channelsWithGuarantees` (it pulls nothing), so it
adds when `finished = []` and `memoryChannel` finishes cleanly. Generic over `PublicIO`. -/
def memoryProviderEnsemble (PublicIO : TypeMap) [ProvableType PublicIO] :
    SoundEnsemble (ZMod p) PublicIO :=
  SoundEnsemble.empty (ZMod p) PublicIO
    |>.addTable ⟨circuit⟩ (by simp [circuit_norm, circuit]) (by simp [circuit_norm])
    |>.addFinishedChannel memoryChannel.toRaw

/-- `memoryChannel` is a finished channel of `memoryProviderEnsemble` — the Memory-bus `isU64` value
guarantee is now an upstream-Clean (bus-balance) obligation against the boundary provider, not the
`pullIf`'s `assumeGuarantees`. -/
@[simp] theorem memoryProviderEnsemble_finished (PublicIO : TypeMap) [ProvableType PublicIO] :
    (memoryChannel (p := p)).toRaw ∈ (memoryProviderEnsemble (p := p) PublicIO).finished := by
  simp [memoryProviderEnsemble, circuit_norm]

/-- The **full boundary** segment (Phase 4 demonstrator): the finalize *pull* table
(`MemoryFinalizeChip`) chains legally onto the finished channel — its `channelsWithGuarantees =
[memoryChannel]` ⊆ finished and its `channelsWithRequirements = []` (a pull owes nothing), so
`addTable`'s obligations close by the default recipes. Documents that the init-push/finalize-pull
boundary pair is self-consistent among providers; not load-bearing for the capstone (which composes the
tables into the plain `Ensemble` directly). -/
def memoryBoundaryEnsemble (PublicIO : TypeMap) [ProvableType PublicIO] :
    SoundEnsemble (ZMod p) PublicIO :=
  memoryProviderEnsemble (p := p) PublicIO
    |>.addTable ⟨MemoryFinalizeChip.circuit⟩
        (by simp [circuit_norm, MemoryFinalizeChip.circuit, memoryProviderEnsemble])
        (by simp [circuit_norm, MemoryFinalizeChip.circuit, memoryProviderEnsemble])

end SP1Clean.MemoryProviderChip
