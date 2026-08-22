import SP1Clean.FormalModel.TraceGen.Memory
import SP1Clean.Proofs.Chips.LoadDoubleChip.Witgen
import ToClean.Air.TableBuild

/-! # `SP1Clean.LoadDoubleChip` — from trace events to a valid AIR table

`LD` through the trace-generation chain (see `LoadWordChip/Complete.lean` for the memory-family
programme and padding-contract note). The shortest chip of the family: an
8-byte load selects nothing and extends nothing, so the row's only committed columns beyond the
three shared blocks are the single `is_real` selector. Every one of the eleven conjuncts is a
citation. -/

namespace SP1Clean.TraceGen

variable {p : ℕ}

/-- The `LoadDouble` chip's committed input row for one event — a **real** row (`is_real = 1`). -/
def MemoryEvent.toLoadDoubleInputs (e : MemoryEvent) : LoadDoubleChip.Inputs (ZMod p) where
  is_real := 1
  state := cpuStateCols e.clk e.pc
  adapter := iTypeReaderCols e.toITypeEvent
  memory_access := memoryAccessCols e.prevMem e.prevTsMem (e.clk + 1)

end SP1Clean.TraceGen

namespace SP1Clean.LoadDoubleChip

open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## The chip's honest-prover contract on a built row -/

/-- **A well-formed, 8-byte-aligned memory trace event builds a row the honest prover can
complete.** `halign` is the per-instruction alignment fact (see `MemoryEvent.Aligned`); everything
else is `MemoryEvent.WellFormed` through the three shared discharges. -/
theorem proverAssumptions_of_event {e : MemoryEvent} (h : e.WellFormed) (halign : e.Aligned 8)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ProverAssumptions (e.toLoadDoubleInputs (p := p)) data hint := by
  have hi := h.toITypeWellFormed
  have haddr64 : (Word.toNat (e.toLoadDoubleInputs (p := p)).op_b_val
      + Word.toNat (e.toLoadDoubleInputs (p := p)).op_c_imm) % 2 ^ 64 = e.addr := addr_eq hi.b_lt hi.imm_lt
  have haddr48 : (Word.toNat (e.toLoadDoubleInputs (p := p)).op_b_val
      + Word.toNat (e.toLoadDoubleInputs (p := p)).op_c_imm) % 2 ^ 48 = e.addr := by
    rw [← Nat.mod_mod_of_dvd _ (show (2 : ℕ) ^ 48 ∣ 2 ^ 64 from by norm_num), haddr64,
      Nat.mod_eq_of_lt h.addr_lt]
  refine ⟨wordOfNat_isU64 _, wordOfNat_isU64 _, ?_, ?_, ?_, wordOfNat_isU64 _, Or.inr rfl,
    iTypeReaderCols_op_a_0_eq_zero hi.opA_ne_zero,
    cpuState_spec e.clk e.pc hi.clk_mod _ _ _,
    memoryAccess_spec hi.clk_mod h.clk_lt h.prevTsMem_lt,
    iTypeReader_spec hi _ _ _ _ _ _ _ _⟩
  · rw [haddr64]; exact h.addr_lt
  · intro _
    rw [haddr48]; exact h.addr_ge
  · rw [haddr48]; exact halign

/-! ## The built table -/

/-- The LoadDouble chip as a flat-AIR component: one circuit, checked independently on each row.

A plain `def`, deliberately not an `abbrev` (see `AddChip.component` for the measurement). -/
def component : Air.Flat.Component (ZMod p) := ⟨circuit⟩

/-- The event rows, before ensemble-level zero padding (see `LoadWordChip/Complete.lean`). -/
def traceInputs (events : List MemoryEvent) : List (Inputs (ZMod p)) :=
  events.map MemoryEvent.toLoadDoubleInputs

/-- Every row of a built trace satisfies the chip's honest-prover contract. -/
theorem proverAssumptions_of_mem_traceInputs {events : List MemoryEvent}
    (h : ∀ e ∈ events, e.WellFormed ∧ e.Aligned 8) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) events, ProverAssumptions input data hint := by
  intro input hin
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
  exact proverAssumptions_of_event (h e he).1 (h e he).2 data hint

/-- **A real trace builds a valid LoadDouble table.** -/
theorem traceTable_constraints (events : List MemoryEvent) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ e ∈ events, e.WellFormed ∧ e.Aligned 8) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events) data hint).Constraints :=
  Air.Flat.Table.build_constraints _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

/-- The same table satisfies its **channel guarantees**. -/
theorem traceTable_guarantees (events : List MemoryEvent) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ e ∈ events, e.WellFormed ∧ e.Aligned 8) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events) data hint).Guarantees :=
  Air.Flat.Table.build_guarantees _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

/-- The table's interaction list on a channel, in closed form. -/
theorem traceTable_interactionsWith (events : List MemoryEvent) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (channel : RawChannel (ZMod p)) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events) data
        hint).interactionsWith channel =
      (traceInputs (p := p) events).flatMap fun input =>
        (component (p := p)).operations.interactionValuesWith channel
          (Environment.fromArray ((component (p := p)).buildRow input data hint) data) :=
  Air.Flat.Table.build_interactions _ _ _ _ channel

end SP1Clean.LoadDoubleChip
