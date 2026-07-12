import SP1Clean.Soundness.ChipRow

/-! # Per-chip Sail dispatch (retired)

> **RETIRED (cutover, 2026-07-11).** The legacy per-chip Sail-step path (`chipRows_step_sound` /
> `chipRow_sailEquiv`, routing the removed `ChipKind.reaches_sail`/`sailEquiv` fields) has been deleted.
> The live soundness chain dispatches the per-chip `advance` obligation instead
> (`Soundness/AdvanceDispatch.lean` → `chipRows_advance_sound` → `TargetObligations.lift`). This module
> is kept as a stub only to preserve the import edge from `GatedVm/Capstone.lean`.

The GatedVm capstone's `GatedExecution` certificate now carries only the balance-derived transition
`trail`; the per-row Sail conjunct it used to carry (`step_sound`) is retired in favour of the target
`advance` path. -/

namespace SP1Clean.Soundness

namespace GatedVm

open SP1Clean
open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

end GatedVm

end SP1Clean.Soundness
