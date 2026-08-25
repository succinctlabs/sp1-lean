import SP1Clean.FormalModel.TraceGen.Memory
import SP1Clean.Proofs.Chips.StoreDoubleChip.Witgen
import ToClean.Air.TableBuild

/-! # `SP1Clean.StoreDoubleChip` — from trace events to a valid AIR table

`SD` through the trace-generation chain (see `StoreWordChip/Complete.lean` for the store family's
programme, the `op_a`-is-a-read discipline, and the padding-contract note).

The shortest chip of the family, and the one that shows what the store family really is: the RAM
write is the whole 8-byte `rs2` word, so there is no `store_value` column and no merge — the
`MemoryAccess` primitive is handed `adapter.op_a_memory.prev_value` directly. Everything below is a
citation: the address facts from `MemoryEvent.WellFormedStore` and the row's `Aligned 8`, the state
and RAM blocks from the shared reader lemmas, and the adapter from `iTypeReaderImmutable_spec`.
-/

namespace SP1Clean.TraceGen

variable {p : ℕ}

/-- The `StoreDouble` chip's committed input row for one event — a **real** row (`is_real = 1`).
Four fields and no computed column: the stored word is the `rs2` read value the adapter block
already carries. -/
def MemoryEvent.toStoreDoubleInputs (e : MemoryEvent) : StoreDoubleChip.Inputs (ZMod p) where
  is_real := 1
  state := cpuStateCols e.clk e.pc
  adapter := iTypeReaderCols e.toITypeEvent
  memory_access := memoryAccessCols e.prevMem e.prevTsMem (e.clk + 1)

end SP1Clean.TraceGen

namespace SP1Clean.StoreDoubleChip

open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## The chip's honest-prover contract on a built row -/

/-- **A well-formed, 8-byte-aligned store trace event builds a row the honest prover can
complete.** `halign` is the per-instruction alignment fact (see `MemoryEvent.Aligned`). -/
theorem proverAssumptions_of_event {e : MemoryEvent} (h : e.WellFormedStore) (halign : e.Aligned 8)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ProverAssumptions (e.toStoreDoubleInputs (p := p)) data hint := by
  have hp : 2 ^ 24 < p := Fact.out
  have haddr64 : (Word.toNat (e.toStoreDoubleInputs (p := p)).op_b_val
      + Word.toNat (e.toStoreDoubleInputs (p := p)).op_c_imm) % 2 ^ 64 = e.addr :=
    addr_eq h.b_lt h.imm_lt
  have haddr48 : (Word.toNat (e.toStoreDoubleInputs (p := p)).op_b_val
      + Word.toNat (e.toStoreDoubleInputs (p := p)).op_c_imm) % 2 ^ 48 = e.addr := by
    rw [← Nat.mod_mod_of_dvd _ (show (2 : ℕ) ^ 48 ∣ 2 ^ 64 from by norm_num), haddr64,
      Nat.mod_eq_of_lt h.addr_lt]
  refine ⟨wordOfNat_isU64 _, wordOfNat_isU64 _, ?_, ?_, ?_, Or.inr rfl,
    cpuState_spec e.clk e.pc h.clk_mod _ _ _,
    memoryAccess_spec h.clk_mod h.clk_lt h.prevTsMem_lt,
    iTypeReaderImmutable_spec h.clk_mod h.opA_lt h.prevA_x0 h.prevTsA_lt h.prevTsB_lt _ _ _ _,
    fun _ => ⟨iTypeReaderCols_op_a_val_lt h.opA_lt, (cpuStateCols_pc_val_lt e.clk e.pc).1,
      (cpuStateCols_pc_val_lt e.clk e.pc).2.1, (cpuStateCols_pc_val_lt e.clk e.pc).2.2⟩⟩
  -- the address fits in 48 bits, is above the reserved page, and is 8-byte aligned
  · rw [haddr64]; exact h.addr_lt
  · intro _
    rw [haddr48]; exact h.addr_ge
  · rw [haddr48]; exact halign

/-! ## The built table -/

/-- The StoreDouble chip as a flat-AIR component: one circuit, checked independently on each row.

A plain `def`, deliberately not an `abbrev` (see `AddChip.component` for the measurement). -/
def component : Air.Flat.Component (ZMod p) := ⟨circuit⟩

/-- The event rows, before ensemble-level zero padding (see `StoreWordChip/Complete.lean`). -/
def traceInputs (events : List MemoryEvent) : List (Inputs (ZMod p)) :=
  events.map MemoryEvent.toStoreDoubleInputs

/-- Every row of a built trace satisfies the chip's honest-prover contract. -/
theorem proverAssumptions_of_mem_traceInputs {events : List MemoryEvent}
    (h : ∀ e ∈ events, e.WellFormedStore ∧ e.Aligned 8) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) events, ProverAssumptions input data hint := by
  intro input hin
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
  exact proverAssumptions_of_event (h e he).1 (h e he).2 data hint

/-- **A real trace builds a valid StoreDouble table.** -/
theorem traceTable_constraints (events : List MemoryEvent) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ e ∈ events, e.WellFormedStore ∧ e.Aligned 8) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events) data hint).Constraints :=
  Air.Flat.Table.build_constraints _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

/-- The same table satisfies its **channel guarantees**. -/
theorem traceTable_guarantees (events : List MemoryEvent) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ e ∈ events, e.WellFormedStore ∧ e.Aligned 8) :
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

end SP1Clean.StoreDoubleChip
