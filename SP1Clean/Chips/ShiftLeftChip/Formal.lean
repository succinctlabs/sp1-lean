import SP1Clean.Chips.ShiftLeftChip.Defs
import SP1Clean.Chips.ShiftLeftChip.Soundness.Sll
import SP1Clean.Chips.ShiftLeftChip.Soundness.Sllw

/-! # `SP1Clean.ShiftLeftChip` — contract: soundness / completeness / `circuit`

Split from the monolithic chip file: `main` + the `ElaboratedCircuit` instance + the soundness
`Assumptions` live in the sibling `Defs` module (`Assumptions` there, not here, so the per-op
`Soundness/<Op>.lean` split files can import it without a cycle through `Formal`). This module holds the
`ProverAssumptions`, the soundness/completeness proofs, and the bundled `circuit`.

**Soundness** is assembled here from the two per-conjunct `Soundness/{Sll,Sllw}.lean` files — each its own
`GeneralFormalCircuit.Soundness` over a single-conjunct `Spec`, split out so the heavy per-variant proofs
compile in parallel — plus the shared channel-requirement tail (the same in both variants, reused here from
`SoundSll`). `circuit_proof_start_core` only introduces the binders (no `simp`), so the sub-theorems' raw
`h_holds`/`h_input`/`h_assumptions` binders match directly. Completeness remains a deferred `sorry`. -/

namespace SP1Clean.ShiftLeftChip

open Circuit
open Extracted (ShiftLeftCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

-- `Assumptions` (the operand `isU64`/register-readback contract) lives in `Defs` so the per-op
-- `Soundness/<Op>.lean` split files can import it without a cycle through `Formal`.

/-- Prover-side row well-formedness: the operand `isU64`s plus the `is_real` binary selector. (The
threaded reader-block `Spec`s would be added here when the soundness/completeness proofs are filled in.) -/
def ProverAssumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p))
    (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val ∧ (input.is_real = 0 ∨ input.is_real = 1)

set_option maxHeartbeats 4000000 in
/-- **Soundness.** The flag-gated RV64 `sll`/`sllw` identities on the result column `cols.a`. **Pieced
together** from the two per-conjunct `Soundness/{Sll,Sllw}.lean` files — each its own
`GeneralFormalCircuit.Soundness` over a single-conjunct `Spec`, split out so the heavy per-variant proofs
compile in parallel — plus the shared channel-requirement tail (the same in both variants, reused here from
`SoundSll`). `circuit_proof_start_core` only introduces the binders (no `simp`), so the sub-theorems' raw
`h_holds`/`h_input`/`h_assumptions` binders match directly. -/
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start_core
  refine ⟨fun hr => ⟨?_, ?_⟩, ?_⟩
  · exact (SoundSll.soundness  i₀ env input_var input h_input h_assumptions h_holds).1 hr
  · exact (SoundSllw.soundness i₀ env input_var input h_input h_assumptions h_holds).1 hr
  · exact (SoundSll.soundness  i₀ env input_var input h_input h_assumptions h_holds).2

/-- Completeness — deferred skeleton `sorry` (as `ShiftRightChip`/`BranchChip`); `main` witnesses the shift
column block as placeholder `0`, which contradicts the real-row `is_real`-gated binds. Honest completeness
needs a `populate`-style witness function plus the variant opcode threaded through `ProverHint`. -/
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  sorry

/-- The `ShiftLeft` chip row as a `GeneralFormalCircuit`: flag-gated RV64 `sll`/`sllw` semantic contract;
output is the extracted `ShiftLeftCols` column struct. Soundness is proved (assembled from the two per-op
`Soundness/<Op>.lean` files); completeness is a skeleton `sorry`. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs ShiftLeftCols :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness }

end SP1Clean.ShiftLeftChip
