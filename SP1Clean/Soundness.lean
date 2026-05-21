import SP1Clean.Soundness.MemoryConsistency
import SP1Clean.Soundness.MemoryConsistencyClock
import SP1Clean.Soundness.StateConsistency
import SP1Clean.Soundness.IsRealBinary
import SP1Clean.Soundness.TraceSoundness
import SP1Clean.Multiplicity

/-! # Trace-level soundness umbrella

Re-exports the four Phase A–D trace-shape modules plus the
end-to-end `trace_soundness_aggregateMemory` theorem.

Module map:
- `SP1Clean.Soundness.MemoryConsistency` (Phase A.2) —
  `aggregateMemoryAccesses`, `ChipRow.rowAccessTuples`,
  `chip_specs_admit_offline_bridge`.
- `SP1Clean.Soundness.MemoryConsistencyClock` (Phase A.3) —
  `TraceClkValid`, `aggregateMemoryAccesses_isTimestampSorted`,
  `aggregateMemoryAccesses_Notimestampdup`.
- `SP1Clean.Soundness.StateConsistency` (Phase B.2) —
  `ChipRow.stateAccess`, `aggregateStateAccesses`, `pcChainProp`,
  `TraceStateValid`, `aggregateStateAccesses_pcChain`.
- `SP1Clean.Soundness.IsRealBinary` (Phase D.1) —
  `binary_of_assertZero`, `TraceIsRealBinary`.
- `SP1Clean.Multiplicity` (Phase C) —
  `ByteOpcode_send_iff_constrain`, `ByteOpcodeSpec_of_constrain`,
  `ByteOpcode_send_imp_ByteOpcodeSpec`, `Program_send_iff_clause`.
- `SP1Clean.Soundness.TraceSoundness` (Phase D.2) —
  `trace_soundness_aggregateMemory` (the end-to-end statement). -/
