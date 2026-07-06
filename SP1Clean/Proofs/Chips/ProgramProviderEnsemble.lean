import SP1Clean.Proofs.Chips.ProgramProviderChip
import Clean.Air.Vm

/-! # (Retired) Program-bus provider segment — program is no longer a *finished* channel

**SC Phase 2a.** `programChannel` was flipped to a semantic `VmChannel` with `Owed := RowSpec` and
`Guarantees := ProgTruth` (= `ProgramMsg.RowSpec ∧ decodedInROM (progOf data)`). Because
`RowSpec ⇏ ProgTruth`, the channel is **not** `Consistent`/`Normal`, so it cannot be *finished* against a
provider the way the byte bus is: a pull now receives the full fetch-decode correspondence
(`decodedInROM`), and that half is grounded by the timed-channel engine (Phase 5), not by bus balance
against this segment. (`Soundness/FinishedChannels.lean` correspondingly grounds only `byteChannel`.)

The former `programProviderEnsemble` / `programProviderEnsemble_finished` — which added
`ProgramProviderChip.circuit` and then `addFinishedChannel programChannel.toRaw` to finish the Program bus
under the old "`Guarantees = RowSpec`, program-independent, finishable-like-byte" model — are retired
accordingly (nothing consumed them: `StateVm.lean` uses only `ProgramProviderChip.circuit`, the comment
references in `ValueBound`/`MemoryProviderEnsemble` are prose). The in-circuit program **push** provider
itself lives on in `ProgramProviderChip.lean` (it still range-checks and pushes each `RowSpec`-valid row,
owing `RowSpec` as its VmChannel `Owed`). This module is kept (doc-only) to preserve the import chain. -/
