import SP1Clean.Proofs.Chips.ByteChip.ByteChip
import SP1Clean.Proofs.Chips.ByteChip.RangeChip
import Clean.Air.Vm

/-! # Finishing the Byte bus — the byte-provider segment of the `SoundEnsemble`

The push side of SP1's preprocessed `ByteChip`/`RangeChip`, assembled into a Clean `SoundEnsemble` and
used to **finish `byteChannel`**. Once `byteChannel` is a *finished* channel, the byte-bus soundness moves
to upstream Clean (`addVm_soundVmChannel_of_soundChannels`) — every chip that `pullIf`s a byte row gets
its `ByteRowSpec` guarantee from the bus balance against these providers, retiring the trace-level
`TraceByteLink` assumption (`Soundness/ByteConsistency.lean`).

`byteProviderEnsemble` adds the ten built byte providers (the six `ByteChip` ops `U8Range`/`MSB`/
`AND`/`OR`/`XOR`/`LTU` over `(b,c)`, plus the four `RangeChip` widths `8`/`13`/`14`/`16` the machine
actually pulls) and then `addFinishedChannel byteChannel`. Each provider has `byteChannel` in its
`channelsWithRequirements` (it must prove `ByteRowSpec` for the row it pushes) and `[]` in its
`channelsWithGuarantees` (it pulls nothing), so they add when `finished = []` and `byteChannel` finishes
cleanly (the `OrderedChannel` obligation is vacuous — no table guarantees `byteChannel` yet; the
consumers join after).

Generic over `PublicIO`: the providers don't touch the public input, so the capstone (Phase 5) instantiates
this at `SP1PublicIO` and continues chaining (`|>.addTable <program> |>.addFinishedChannel programChannel
|> …`) into the plain `Ensemble` capstone. `LTU` (op 4) is pulled by the AluX0 chip's `opcode < 29` check
and width 14 by the Jal/Jalr/Branch `next_pc` alignment checks, so both providers are built; the only
remaining unbuilt form is the genuinely variable-`bits` `RangeChip` (one circuit serving all widths at
once), which no consumer needs — every machine pull uses a fixed compile-time width. -/

namespace SP1Clean.ByteChip

open Circuit
open SP1Clean.Channels (byteChannel)
open Air.Flat

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The Byte-bus provider segment: add the ten built byte providers, then **finish `byteChannel`**.
Generic over `PublicIO` (the verifier stays `.empty`; `PublicIO` is only the ensemble's IO type), so the
capstone chains the remaining buses + the State `VmTables` onto it. -/
def byteProviderEnsemble (PublicIO : TypeMap) [ProvableType PublicIO] :
    SoundEnsemble (ZMod p) PublicIO :=
  SoundEnsemble.empty (ZMod p) PublicIO
    |>.addTable ⟨U8Range.circuit⟩ (by simp [circuit_norm, U8Range.circuit]) (by simp [circuit_norm])
    |>.addTable ⟨MSB.circuit⟩ (by simp [circuit_norm, MSB.circuit]) (by simp [circuit_norm])
    |>.addTable ⟨AndByte.circuit⟩ (by simp [circuit_norm, AndByte.circuit]) (by simp [circuit_norm])
    |>.addTable ⟨OrByte.circuit⟩ (by simp [circuit_norm, OrByte.circuit]) (by simp [circuit_norm])
    |>.addTable ⟨XorByte.circuit⟩ (by simp [circuit_norm, XorByte.circuit]) (by simp [circuit_norm])
    |>.addTable ⟨Ltu.circuit⟩ (by simp [circuit_norm, Ltu.circuit]) (by simp [circuit_norm])
    |>.addTable ⟨RangeChip.circuit8⟩
        (by simp [circuit_norm, RangeChip.circuit8, RangeChip.circuit]) (by simp [circuit_norm])
    |>.addTable ⟨RangeChip.circuit13⟩
        (by simp [circuit_norm, RangeChip.circuit13, RangeChip.circuit]) (by simp [circuit_norm])
    |>.addTable ⟨RangeChip.circuit14⟩
        (by simp [circuit_norm, RangeChip.circuit14, RangeChip.circuit]) (by simp [circuit_norm])
    |>.addTable ⟨RangeChip.circuit16⟩
        (by simp [circuit_norm, RangeChip.circuit16, RangeChip.circuit]) (by simp [circuit_norm])
    |>.addFinishedChannel byteChannel.toRaw

/-- `byteChannel` is a finished channel of `byteProviderEnsemble` — the byte-bus soundness is now an
upstream-Clean obligation, not the trace-level `TraceByteLink` assumption. -/
@[simp] theorem byteProviderEnsemble_finished (PublicIO : TypeMap) [ProvableType PublicIO] :
    (byteChannel (p := p)).toRaw ∈ (byteProviderEnsemble (p := p) PublicIO).finished := by
  simp [byteProviderEnsemble, circuit_norm]

end SP1Clean.ByteChip
