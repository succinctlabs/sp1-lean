import SP1Clean.Proofs.Chips.DivRemChip.Defs
import SP1Clean.Proofs.Chips.DivRemChip.Populate.Bounds
import SP1Clean.Proofs.Chips.DivRemChip.Populate.Glue
import SP1Clean.Proofs.Chips.DivRemChip.Populate.Shapes
import SP1Clean.Proofs.Chips.DivRemChip.Populate.Euclid
import SP1Clean.Proofs.Chips.DivRemChip.Soundness
import SP1Clean.Proofs.Chips.DivRemChip.Assembly
import SP1Clean.Proofs.Chips.DivRemChip.Soundness.Div
import SP1Clean.Proofs.Chips.DivRemChip.Soundness.Divu
import SP1Clean.Proofs.Chips.DivRemChip.Soundness.Divuw
import SP1Clean.Proofs.Chips.DivRemChip.Soundness.Divw
import SP1Clean.Proofs.Chips.DivRemChip.Soundness.Rem
import SP1Clean.Proofs.Chips.DivRemChip.Soundness.Remu
import SP1Clean.Proofs.Chips.DivRemChip.Soundness.Remuw
import SP1Clean.Proofs.Chips.DivRemChip.Soundness.Remw
import SP1Clean.Proofs.Chips.DivRemChip.Soundness.Reader
import SP1Clean.Proofs.Chips.DivRemChip.Completeness.Driver

/-! # `SP1Clean.DivRemChip` — contract: `Assumptions` / soundness / completeness / `circuit`

Split from the chip skeleton: `main` + the `ElaboratedCircuit` instance + the soundness `Assumptions`
live in the sibling `Defs` module (`Assumptions` there, not here, so the per-op `Soundness/<Op>.lean`
split files can import it without a cycle through `Formal`). This module holds the `ProverAssumptions`,
the soundness/completeness proofs, and the bundled `circuit`.

**Status.** The semantic `Spec` (the flag-gated RV64 `div`/`rem`/… identities on `cols.a`,
`Specs/Chip.lean`) is real and **soundness is proved** — assembled here from the eight per-conjunct
`Soundness/<Op>.lean` files (each its own `GeneralFormalCircuit.Soundness`, split out so the heavy
per-variant proofs compile in parallel). Completeness lives in `Completeness/Driver.lean` (`completeness`). -/

namespace SP1Clean.DivRemChip

open Circuit
open Extracted (DivRemCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

-- `2 ^ 24` (subsuming `2 ^ 17`): the chip composes `MulOperation` — see `Defs`.
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

set_option maxHeartbeats 4000000 in
/-- Soundness: the flag-gated RV64 `div`/`divu`/`rem`/`remu`/`divw`/`remw`/`divuw`/`remuw` identities on
the result column `cols.a`. **Pieced together** from the eight per-conjunct `Soundness/<Op>.lean` files —
each its own `GeneralFormalCircuit.Soundness` over a single-conjunct `Spec`, split out so the heavy
per-variant proofs compile in parallel — plus the shared `Operations.Requirements` tail (the same in
every variant, reused here from `SoundDiv`). `circuit_proof_start_core` only introduces the binders (no
`simp`), so the sub-theorems' raw `h_holds`/`h_input`/`h_assumptions` binders match directly. -/
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start_core
  -- The reader sub-`Spec` + `is_real`-binary come from `SoundReader` (its `.1` is the two-conjunct
  -- `RTypeReader.Spec ∧ binary`); the eight flag-gated arithmetic conjuncts and the shared `Req` tail come
  -- from the per-variant files as before.
  refine ⟨⟨(SoundReader.soundness i₀ env input_var input h_input h_assumptions h_holds).1.1,
      (SoundReader.soundness i₀ env input_var input h_input h_assumptions h_holds).1.2,
      fun hr => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩, ?_⟩
  · exact (SoundDiv.soundness   i₀ env input_var input h_input h_assumptions h_holds).1 hr
  · exact (SoundDivu.soundness  i₀ env input_var input h_input h_assumptions h_holds).1 hr
  · exact (SoundRem.soundness   i₀ env input_var input h_input h_assumptions h_holds).1 hr
  · exact (SoundRemu.soundness  i₀ env input_var input h_input h_assumptions h_holds).1 hr
  · exact (SoundDivw.soundness  i₀ env input_var input h_input h_assumptions h_holds).1 hr
  · exact (SoundRemw.soundness  i₀ env input_var input h_input h_assumptions h_holds).1 hr
  · exact (SoundDivuw.soundness i₀ env input_var input h_input h_assumptions h_holds).1 hr
  · exact (SoundRemuw.soundness i₀ env input_var input h_input h_assumptions h_holds).1 hr
  · exact (SoundDiv.soundness   i₀ env input_var input h_input h_assumptions h_holds).2

-- `main` composes the giant `MulOperation` subcircuit twice, so bundling `{ main, elaborated }` whnfs
-- a large term — above the default heartbeat budget (cf. the `elaborated` instance in `Defs`).
set_option maxHeartbeats 16000000 in
/-- The `DivRem` chip row as a `GeneralFormalCircuit`: flag-gated RV64 `div`/`divu`/`rem`/`remu`/`divw`/
`remw`/`divuw`/`remuw` semantic contract on the extracted `DivRemCols` column struct. Soundness and
completeness are both proved (completeness via `completeness`). -/
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
    requirementsChannelsLawful := fun input_var i₀ => by
      simp only [circuit_norm, main, byteChannel, stateChannel, memoryChannel, programChannel,
        AddOperation.circuit, IsEqualWordOperation.circuit, IsZeroWordOperation.circuit,
        LtOperationUnsigned.circuit, MulOperation.circuit, Readers.CPUState.circuit,
        Readers.RTypeReader.circuit, U16MSBOperation.circuit, assertZeros]
      intro env hshallow
      simp only [ownAsserts, List.forall_mem_cons] at hshallow
      obtain ⟨e13, e15, e17, e19, e20, e21, e22, e23, e29, e35, e41, e47, e48, e49, e51, e54, e57, e59,
        e61, e64, e67, e69, e70, e71, e73, e76, e79, e81, e83, e86, e89, e91, e96, e99, e103, e105, e107,
        e109, e111, e113, e115, e117, e119, e154, e157, e160, e163, e167, e171, e175, e179, e184, e189,
        e194, e199, e204, e209, e214, e219, e225, e228, e230, e232, e234, e236, e238, e240, e242, e244,
        e247, e250, e253, e256, e259, e262, e265, e268, e270, e272, e274, e276, e278, e280, e282, e284,
        e286, e288, e299, e300, e301, e302, e305, e307, e309, e311, e313, e315, e317, e319, e321, e323,
        e325, e327, e329, e331, e333, e335, e337, e339, e341, e343, e345, e347, e349, e351, e353, e355,
        e357, e359, e367, eopa0⟩ := hshallow
      simp only [circuit_norm] at e325 e327 e329 e331 e333 e335 e337 e339 e355 e367
      have hbin := bool_of_mul_pred e355
      have bd := bool_of_mul_pred e325; have bdu := bool_of_mul_pred e327
      have br := bool_of_mul_pred e329; have bru := bool_of_mul_pred e331
      have bdw := bool_of_mul_pred e333; have brw := bool_of_mul_pred e335
      have bduw := bool_of_mul_pred e337; have bruw := bool_of_mul_pred e339
      have hvs := flags_val_sum bd bdu br bru bdw brw bduw bruw (by linear_combination -e367)
      have he2 := group_binary4 bdw brw bduw bruw (by omega)
      and_intros <;>
        first
          | exact fun h1 h0 => off_gate_vacuous hbin h1 h0
          | exact fun h1 h0 => off_gate_vacuous he2 h1 h0,
    -- W11 (A2): expose the State-bus `[pulledIf is_real cur, pushedIf is_real next]` pair (pc+4, clk+8)
    -- so the chip is a `VmTables` table; descends to the composed `CPUState` subcircuit's lone pull+push.
    -- The `is_real` gate (`E355`) is already shallow (emitted via `assertZeros (ownAsserts cols)`).
    exposedChannels := fun input _ =>
      expose stateChannel
        [ pulledIf input.is_real
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536,
             input.state.pc[0], input.state.pc[1], input.state.pc[2]⟩,
          pushedIf input.is_real
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 8,
             input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]⟩ ],
    exposedChannels_eq := by
      intro input offset
      simp (maxSteps := 1000000) only [main, Readers.CPUState.circuit, Readers.CPUState.main,
        Readers.RTypeReader.circuit, Readers.RTypeReader.main,
        Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
        Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
        MulOperation.circuit, MulOperation.main,
        IsEqualWordOperation.circuit, IsEqualWordOperation.main,
        IsZeroWordOperation.circuit, IsZeroWordOperation.main,
        AddOperation.circuit, AddOperation.main,
        LtOperationUnsigned.circuit, LtOperationUnsigned.main,
        U16MSBOperation.circuit, U16MSBOperation.main,
        -- the nested gadgets the above ops compose (byte-decomp / zero-test / u16-compare cores)
        U16toU8OperationSafe.circuit, U16toU8OperationSafe.main,
        IsZeroOperation.circuit, IsZeroOperation.main,
        U16CompareOperation.circuit, U16CompareOperation.main, assertZeros,
        circuit_norm, FormalAssertion.toSubcircuit_interactions]
      -- the leftover (past the `CPUState` state pull/push) is `assertZeros (ownAsserts cols)` ++ the 34
      -- direct `byteChannel` pulls; `interactionsWith_append` splits the `++`, the map-assert lemma
      -- empties the asserts, and `byteChannel ≠ stateChannel` drops the pulls.
      simp (maxSteps := 1000000) [circuit_norm, Gadgets.Equality.main,
        Operations.interactionsWith_append, byteChannel, stateChannel] }

end SP1Clean.DivRemChip
