import SP1Clean.Proofs.Chips.LoadByteStaticChip.Witgen
import SP1Clean.Proofs.Chips.LoadByteChip.Complete

/-! # The existing LB/LBU event builder completes the alternative circuit -/

namespace SP1Clean.LoadByteStaticChip

open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- Constructive completeness reuses exactly the existing event inputs and honest witness. -/
theorem proverAssumptions_of_event {event : MemoryEvent} (wellFormed : event.WellFormed)
    (opcode : event.opcode = 29 ∨ event.opcode = 32)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    circuit.ProverAssumptions (event.toLoadByteInputs (p := p)) data hint :=
  LoadByteChip.proverAssumptions_of_event wellFormed opcode data hint

/-- Both implementations build literally the same physical event row. -/
theorem buildRow_event_eq_original (event : MemoryEvent) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    (component (p := p)).buildRow event.toLoadByteInputs data hint =
      LoadByteChip.component.buildRow event.toLoadByteInputs data hint :=
  buildRow_eq_original _ _ _

/-- A complete trace uses the original event builder and the alternative circuit's real witness. -/
theorem traceTable_constraints (events : List MemoryEvent) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p))
    (wellFormed : ∀ event ∈ events, event.WellFormed ∧ (event.opcode = 29 ∨ event.opcode = 32)) :
    (Air.Flat.Table.build (component (p := p)) (LoadByteChip.traceInputs events) data hint).Constraints data :=
  Air.Flat.Table.build_constraints _ _ _ _ _ computableWitnesses
    (LoadByteChip.proverAssumptions_of_mem_traceInputs wellFormed data hint)

/-- The alternative still supplies all of the existing channel guarantees. -/
theorem traceTable_guarantees (events : List MemoryEvent) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p))
    (wellFormed : ∀ event ∈ events, event.WellFormed ∧ (event.opcode = 29 ∨ event.opcode = 32)) :
    (Air.Flat.Table.build (component (p := p)) (LoadByteChip.traceInputs events) data hint).Guarantees data :=
  Air.Flat.Table.build_guarantees _ _ _ _ _ computableWitnesses
    (LoadByteChip.proverAssumptions_of_mem_traceInputs wellFormed data hint)

end SP1Clean.LoadByteStaticChip
