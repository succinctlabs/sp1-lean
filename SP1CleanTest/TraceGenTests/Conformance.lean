import SP1Clean.Math.Word
import SP1Clean.Model.SP1Field

/-! # Shared scaffolding for the circuit-as-trace-generator layer (`TraceGenTests/`).

`TraceGenTests/` is the substrate for deriving whole trace rows *from a chip's own circuit*
(`TraceGenerator.lean` — witness columns from `main`'s witness closures, row layout from `main`'s
output struct) plus the event → input-column extraction (`EventPopulate.lean`). Its consumers are
the real-row satisfiability battery (`SP1CleanTest/NonVacuityReal.lean`) and the exporter's
per-chip `circuitTraceRowMapped` spot check.

Trace conformance against SP1's real `MachineAir::generate_trace` lives in the dump-anchored
pipeline (committed `export/sp1dump/` dumps + the fail-closed generation-time gate in
`scripts/witgenExport.lean --testdata` + the Rust interpreter differential), which replaced the
former `native_decide` vector batteries (2026-08).

The chips are field-generic over `ZMod p`; the anchors run at SP1's **concrete field**
(KoalaBear), where SP1's prover actually runs, so this file discharges the chips' `Fact`
assumptions once at that prime. The generic generators stay axiom-clean. -/

namespace SP1Clean.TraceGenTests

open SP1Clean

/-! The prime and its `Fact` instances are shared with the production library through
`Model.SP1Field`. -/

/-- Cast a single ℕ (a dumped canonical field value) into SP1's field. -/
def toField (n : ℕ) : ZMod SP1Prime := (n : ZMod SP1Prime)

end SP1Clean.TraceGenTests
