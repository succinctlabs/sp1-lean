import SP1Clean.Math.Word
import Mathlib.Tactic.NormNum.Prime

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

/-- SP1's field is KoalaBear, the prime `2^31 - 2^24 + 1`. SP1's prover runs here, so trace
conformance is checked at this concrete field. -/
abbrev SP1Prime : ℕ := 2130706433

instance instFactSP1Prime : Fact (Nat.Prime SP1Prime) := ⟨by native_decide⟩

/-- The chips' standard field-size assumption, discharged at the concrete prime (the trace anchors
instantiate whole chip `main`s, which carry `Fact (2 ^ 17 < p)`). -/
instance instFact2pow17SP1Prime : Fact (2 ^ 17 < SP1Prime) := ⟨by norm_num [SP1Prime]⟩

/-- `MulOperation.populate` / `MulChip.main` need `2 ^ 24 < p`; discharged at KoalaBear
(`2^24 = 16777216 < SP1Prime`). -/
instance instFact2pow24SP1Prime : Fact (2 ^ 24 < SP1Prime) := ⟨by norm_num [SP1Prime]⟩

/-- The AIR-relation layer (`Soundness/AIR.lean`) states `SupportedCoreNativeRelation` and the
capstone under `Fact (2 ^ 25 < p)`; discharged at KoalaBear (`2^25 = 33554432 < SP1Prime`) so the
capstone's hypothesis bundle is instantiable at the real prime (exercised by
`SP1CleanTest/Audit/JointNonVacuity.lean`). -/
instance instFact2pow25SP1Prime : Fact (2 ^ 25 < SP1Prime) := ⟨by norm_num [SP1Prime]⟩

/-- Cast a single ℕ (a dumped canonical field value) into SP1's field. -/
def toField (n : ℕ) : ZMod SP1Prime := (n : ZMod SP1Prime)

end SP1Clean.TraceGenTests
