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
    channelsWithRequirements :=
      [byteChannel.toRaw, stateChannel.toRaw, memoryChannel.toRaw, programChannel.toRaw] }

end SP1Clean.DivRemChip
