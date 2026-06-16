import SP1Clean.Proofs.Chips.ShiftRightChip.Defs
import SP1Clean.Proofs.Chips.ShiftRightChip.Soundness.Srl
import SP1Clean.Proofs.Chips.ShiftRightChip.Soundness.Sra
import SP1Clean.Proofs.Chips.ShiftRightChip.Soundness.Srlw
import SP1Clean.Proofs.Chips.ShiftRightChip.Soundness.Sraw

/-! # `SP1Clean.ShiftRightChip` — contract: soundness / completeness / `circuit`

Split from the monolithic chip file: `main` + the `ElaboratedCircuit` instance + the soundness
`Assumptions` live in the sibling `Defs` module (`Assumptions` there, not here, so the per-op
`Soundness/<Op>.lean` split files can import it without a cycle through `Formal`). This module holds the
`ProverAssumptions`, the soundness/completeness proofs, and the bundled `circuit`.

**Soundness** is assembled here from the four per-conjunct `Soundness/{Srl,Sra,Srlw,Sraw}.lean` files —
each its own `GeneralFormalCircuit.Soundness` over a single-conjunct `Spec`, split out so the heavy
per-variant proofs compile in parallel — plus the shared `Operations.Requirements` tail (the same in every
variant, reused here from `SoundSrl`). `circuit_proof_start_core` only introduces the binders (no `simp`),
so the sub-theorems' raw `h_holds`/`h_input`/`h_assumptions` binders match directly. Completeness remains a
deferred `sorry` (as `ShiftLeftChip`/`BranchChip`). -/

namespace SP1Clean.ShiftRightChip

open Circuit
open Extracted (ShiftRightCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

-- `Assumptions` (the soundness operand-`isU64` contract) lives in `Defs` so the per-op
-- `Soundness/<Op>.lean` split files can import it without a cycle through `Formal`.

/-- Prover-side row well-formedness: the register-read `isU64`s plus the `is_real` binary selector. -/
def ProverAssumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p))
    (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.adapter.op_b_memory.prev_value ∧ Word.isU64 input.adapter.op_c_memory.prev_value ∧
    (input.is_real = 0 ∨ input.is_real = 1)

set_option maxHeartbeats 4000000 in
/-- **Soundness.** The flag-gated RV64 `srl`/`sra`/`srlw`/`sraw` identities on the result column `cols.a`.
**Pieced together** from the four per-conjunct `Soundness/{Srl,Sra,Srlw,Sraw}.lean` files — each its own
`GeneralFormalCircuit.Soundness` over a single-conjunct `Spec`, split out so the heavy per-variant proofs
compile in parallel — plus the shared `Operations.Requirements` tail (the same in every variant, reused
here from `SoundSrl`). `circuit_proof_start_core` only introduces the binders (no `simp`), so the
sub-theorems' raw `h_holds`/`h_input`/`h_assumptions` binders match directly. -/
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start_core
  refine ⟨fun hr => ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (SoundSrl.soundness  i₀ env input_var input h_input h_assumptions h_holds).1 hr
  · exact (SoundSra.soundness  i₀ env input_var input h_input h_assumptions h_holds).1 hr
  · exact (SoundSrlw.soundness i₀ env input_var input h_input h_assumptions h_holds).1 hr
  · exact (SoundSraw.soundness i₀ env input_var input h_input h_assumptions h_holds).1 hr
  · exact (SoundSrl.soundness  i₀ env input_var input h_input h_assumptions h_holds).2

/-- **Deferred (documented gap), as `BranchChip`/`ShiftLeftChip`.** `main` witnesses the shift column
block (`a`, `c_bits`, the `v_*` powers, `lower/higher_limb`, `limb_result`, `shift_u16`, the flags, the
MSBs) as placeholder `0`, which contradicts the real-row `is_real`-gated binds (the flag sum, the `v_*`
encodings, the limb splits, …). Honest completeness needs a `populate`-style witness function — computing
`c_bits` from the shift amount, the `v_*` powers, the `lower/higher_limb` bit-splits, the `limb_result`
reassembly, the `shift_u16` one-hot, and the two MSBs — plus threading the variant opcode through
`ProverHint` (it is not reconstructible from `Inputs` alone). That is a `main`-level change and a separate
workstream; left as a marked `sorry`. -/
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  sorry

/-- The `ShiftRight` chip row as a `GeneralFormalCircuit`: flag-gated RV64 `srl`/`sra`/`srlw`/`sraw`
semantic contract; output is the extracted `ShiftRightCols` column struct. Soundness is proved (assembled
from the four per-op `Soundness/<Op>.lean` files); completeness is a skeleton `sorry`. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs ShiftRightCols :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness }

end SP1Clean.ShiftRightChip
