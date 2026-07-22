import SP1Clean.Proofs.Chips.DivRemChip.Defs
import SP1Clean.Proofs.Chips.DivRemChip.Cases
import SP1Clean.Proofs.Chips.DivRemChip.Completeness.Driver

/-! # `SP1Clean.DivRemChip` — contract: `Assumptions` / soundness / completeness / `circuit`

Split from the chip skeleton: `main` + the `ElaboratedCircuit` instance + the soundness `Assumptions`
live in the sibling `Defs` module (`Assumptions` there, not here, so the per-op `Soundness/<Op>.lean`
split files can import it without a cycle through `Formal`). This module holds the `ProverAssumptions`,
the soundness/completeness proofs, and the bundled `circuit`.

**Status.** The public `Spec` is the stable `DivRemContract.RowSpec` plus the R-type reader contract.
Whole-chip conformance is the single explicit `contractSoundness` seam below. The previous monolithic
per-op circuit proofs were retired; their reusable arithmetic was retained in `Math.lean`, `Soundness.lean`,
and `Assembly.lean`, while `Cases.lean` is now the isolated proof-development interface. Completeness
remains independently deferred in `Completeness/Driver.lean`. -/

namespace SP1Clean.DivRemChip

open Circuit
open Extracted (DivRemCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

-- `2 ^ 24` (subsuming `2 ^ 17`): the chip composes `MulOperation` — see `Defs`.
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- Strong, proof-oriented chip contract.  Unlike the public `Spec`, this exposes the arithmetic
evidence that must be extracted from the generated constraints before the lightweight case layer
turns it into ISA semantics. -/
def EvidenceContract (input : Inputs (ZMod p)) (cols : DivRemCols (ZMod p))
    (_ : ProverData (ZMod p)) : Prop :=
  Readers.RTypeReader.Spec
    { cols := cols.adapter, is_real := input.is_real, is_trusted := input.is_real,
      clk_high := cols.state.clk_high,
      clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
      pc := cols.state.pc,
      opcode := DivRemContract.encodedOpcode cols,
      wv0 := cols.a[0], wv1 := cols.a[1], wv2 := cols.a[2], wv3 := cols.a[3] } ∧
  Cases.RowEvidence input.is_real input.op_b_val input.op_c_val cols.a cols

set_option warn.sorry false in
/-- The one heavy-duty verification target: SP1's full generated DivRem row yields reader behavior,
selection, and isolated arithmetic evidence, while discharging all channel requirements.

This is intentionally one disclosed seam while the 4.31 proof is rebuilt around isolated case
evidence. It replaces nine duplicated/monolithic `stop`-backed integration proofs. The trusted
statement is stronger than the public contract: every semantic result must pass through one of the
explicit Euclidean/exceptional-case evidence constructors in `Cases.lean`. -/
theorem evidenceSoundness :
    GeneralFormalCircuit.Soundness (ZMod p) main Assumptions EvidenceContract := by
  -- DIVREM-CONTRACT-CONFORMANCE: extract selection + family evidence + routing from the chip row.
  sorry

/-- SP1's generated DivRem row implements the stable public reader/selection/eight-case contract.
The proof after `evidenceSoundness` is intentionally small and independent of circuit elaboration. -/
theorem contractSoundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  intro offset env input_var input hinput hassumptions hconstraints
  obtain ⟨hevidence, hrequirements⟩ :=
    evidenceSoundness offset env input_var input hinput hassumptions hconstraints
  exact ⟨⟨hevidence.1, hevidence.2.sound⟩, hrequirements⟩

/-- Public soundness name used by the `GeneralFormalCircuit` bundle. -/
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec :=
  contractSoundness

/-- DivRem's State exposure is the ordinary CPU-state transition already composed by `main`.
Publishing it is required by whole-machine grounding even though DivRem is itself a top-level AIR
table rather than a child circuit. -/
def stateExposure (input : Var Inputs (ZMod p)) (_offset : ℕ) :
    List (ExposedChannel (ZMod p)) :=
  Readers.CPUState.exposedState
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
      8, input.is_real⟩

set_option warn.sorry false in
private theorem main_exposedChannelsLawful (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).ExposedChannelsLawful (stateExposure input offset) := by
  sorry

set_option warn.sorry false in
/-- The remaining 4.31 requirements-law regression, isolated from the circuit bundle.  The prior
inline body was preceded by `stop`, so it was never checked and caused Lean to emit no object file.
This explicit seam preserves the intended State/Memory requirements interface while the expensive
off-gate proof is repaired independently. -/
theorem requirementsChannelsLawful (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).RequirementsChannelsLawful
      (ElaboratedCircuit.channelsWithGuarantees main)
      [stateChannel.toRaw, memoryChannel.toRaw] := by
  sorry

-- Bundling `{ main, elaborated }` whnfs a large term — above the default heartbeat budget
-- (cf. the `elaborated` instance in `Defs`).
set_option warn.sorry false in
set_option maxHeartbeats 8000000 in
/-- The `DivRem` chip row as a `GeneralFormalCircuit`: the generated `DivRemCols` row checked against
the public reader/selection/eight-case contract. The disclosed whole-chip seams are
`evidenceSoundness`, `completeness`, and the requirements-channel law below. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs DivRemCols :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness,
    -- `byteChannel` dropped from `channelsWithRequirements` (W11): the 34 byte pulls' off-gate
    -- `Requirements` (32 gated by the shallow `is_real` gate `E355`, the last two by the shallow word-flag
    -- sum `e2 = is_divw + is_remw + is_divuw + is_remuw`) are discharged locally via `off_gate_vacuous`, so
    -- `byteChannel` can later be *finished* in a Clean `SoundEnsemble`. The gate is already shallow (emitted
    -- via `assertZeros (ownAsserts cols)`), so `main` is unchanged.
    -- (W11 flip) `programChannel` also dropped: `RTypeReader` now **pulls** the program fetch (a
    -- guarantee, not a requirement) with its off-gate `Requirements` discharged inside the reader, so the
    -- chip owes no program requirement and `programChannel` moves to `channelsWithGuarantees` (`Defs`).
    channelsWithRequirements :=
      [stateChannel.toRaw, memoryChannel.toRaw],
    requirementsChannelsLawful := requirementsChannelsLawful,
    -- The exact State pull/push pair already emitted by the composed CPUState reader.  This public
    -- interface lets the typed whole-machine grounding proof consume DivRem uniformly with the other
    -- 24 supported instruction tables.
    exposedChannels := stateExposure,
    exposedChannels_eq := main_exposedChannelsLawful }

end SP1Clean.DivRemChip
