import SP1Clean.Soundness.ChipRow

/-! # Per-chip Sail dispatch

> **FROZEN (consolidation step 0, 2026-07-09).** Legacy soundness path — scheduled for deletion at the cutover (proposal §5.6). Do NOT add new lemmas against this module; new soundness work targets the timed-grounding engine (proposal §3.2).

The reusable "every real row reaches its RISC-V Sail spec" dispatch. Each row carries its chip's
verified Sail step in `r.kind.reaches_sail`, so the dispatch is **generic** — no `cases`, no per-chip
arm; adding a chip never touches this lemma.

This is the per-row layer of the GatedVm capstone's Sail conjunct: given each row's in-circuit `Spec`
(`r.chipSpec data`), every real row's `sailEquiv` holds for any honouring Sail state. The *source* of
`h_spec` at the ensemble level — each chip table's `Spec` recovered from `witness.Constraints` via
`Component.weakSoundness`, whose `FullGuarantees` come from the gated bus balance — is the coupled
balance→guarantees bridge, supplied separately. -/

namespace SP1Clean.Soundness

namespace GatedVm

open SP1Clean
open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **Per-chip Sail dispatch.** From each row's in-circuit `Spec`, every real row reaches its RISC-V
Sail spec (for any Sail state honouring that row's register/PC/memory reads, quantified inside
`sailEquiv`). Dispatched generically through `r.kind.reaches_sail`. -/
theorem chipRows_step_sound (rows : List (ChipRow p)) (data : ProverData (ZMod p))
    (h_spec : ∀ r ∈ rows, r.chipSpec data) :
    ∀ r ∈ rows, r.is_real = 1 → ∀ s : SailState, r.sailEquiv s :=
  fun r hr h_real s => r.kind.reaches_sail r.inputs r.cols data s h_real (h_spec r hr)

/-- Single-row form (the dispatch on one row), handy when the spec quantifies rows from a trail. -/
theorem chipRow_sailEquiv (r : ChipRow p) (data : ProverData (ZMod p))
    (h_real : r.is_real = 1) (h_spec : r.chipSpec data) (s : SailState) :
    r.sailEquiv s :=
  r.kind.reaches_sail r.inputs r.cols data s h_real h_spec

end GatedVm

end SP1Clean.Soundness
