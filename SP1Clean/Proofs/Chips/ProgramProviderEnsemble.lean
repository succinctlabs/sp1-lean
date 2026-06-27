import SP1Clean.Proofs.Chips.ProgramProviderChip
import Clean.Air.Vm

/-! # Finishing the Program bus — the program-provider segment of the `SoundEnsemble`

The push side of SP1's preprocessed program/decode chip, assembled into a Clean `SoundEnsemble` and used
to **finish `programChannel`**. Once `programChannel` is a *finished* channel, every CPU reader that
`pullIf`s an instruction fetch (the W11 polarity flip) gets its `ProgramMsg.RowSpec` guarantee (write-reg
index `< 32`, pc limbs `< 2^16`, `op_a_0` boolean) from the bus balance against this provider — the
guarantee is now a verifier obligation backed by an in-circuit provider, not the `assumeGuarantees`
hand-wave the `pullIf` carries in isolation.

This mirrors `ByteChip/Ensemble.lean` exactly: `programChannel.Guarantees` is `RowSpec`, which is
**program-independent** (just like `byteChannel.Guarantees = ByteRowSpec`), so the channel finishes
against the single generic `ProgramProviderChip.circuit` (the table of all `RowSpec`-valid rows). The
*program-specific* `inROM` membership (every fetch is in **this** committed ROM) is a strictly stronger,
balance-derived capstone fact — it is **not** the channel guarantee and is handled separately at the
target machine level (`Soundness/ProgramConsistency.lean` / `ProgramProviderSpike.lean`), so it is **not**
retired by this segment.

Generic over `PublicIO`: the provider does not touch the public input, so the capstone instantiates this
at `SP1PublicIO` and chains it onto the byte/state segments. -/

namespace SP1Clean.ProgramProviderChip

open Circuit
open SP1Clean.Channels (programChannel)
open Air.Flat

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The Program-bus provider segment: add the in-circuit program-ROM provider, then **finish
`programChannel`**. The provider has `programChannel` in its `channelsWithRequirements` (it must prove
`RowSpec` for the row it pushes) and `[]` in its `channelsWithGuarantees` (it pulls nothing), so it adds
when `finished = []` and `programChannel` finishes cleanly. Generic over `PublicIO`. -/
def programProviderEnsemble (PublicIO : TypeMap) [ProvableType PublicIO] :
    SoundEnsemble (ZMod p) PublicIO :=
  SoundEnsemble.empty (ZMod p) PublicIO
    |>.addTable ⟨circuit⟩
        (by simp [circuit_norm, circuit]) (by simp [circuit_norm, circuit])
    |>.addFinishedChannel programChannel.toRaw

/-- `programChannel` is a finished channel of `programProviderEnsemble` — the Program-bus `RowSpec`
guarantee is now an upstream-Clean (bus-balance) obligation, not the `pullIf`'s `assumeGuarantees`. -/
@[simp] theorem programProviderEnsemble_finished (PublicIO : TypeMap) [ProvableType PublicIO] :
    (programChannel (p := p)).toRaw ∈ (programProviderEnsemble (p := p) PublicIO).finished := by
  simp [programProviderEnsemble, circuit_norm]

end SP1Clean.ProgramProviderChip
