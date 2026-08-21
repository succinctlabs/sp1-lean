import SP1Clean.FormalModel.TraceGen.Memory
import SP1Clean.Proofs.Chips.LoadX0Chip.Witgen
import ToClean.Air.TableBuild

/-! # `SP1Clean.LoadX0Chip` — from trace events to a valid AIR table

The `rd = x0` form of all seven loads through the trace-generation chain (see
`LoadWordChip/Complete.lean` for the memory-family programme note, including **why there is no
padding row**).

Two things are genuinely new, and both come from `x0`.

1. **The event is the `x0` one.** `MemoryEvent.WellFormedX0` replaces `WellFormed`'s "the
   destination is not `x0`" with its negation — the routing condition that puts the event on this
   chip — plus "`x0` reads as zero", which is what the immutable adapter's four
   `op_a_0 · prev_value_i = 0` gates record. `iTypeReaderImmutable_spec_x0` is the matching reader
   discharge.
2. **One chip, seven opcodes.** The row commits a selector per load variant and gates the address's
   low bits per variant (`LD` clears all three offset bits, `LW`/`LWU` the low two, `LH`/`LHU` the
   lowest). `MemoryEvent.IsLoad` carries exactly that pairing — which of the seven, and the
   alignment RISC-V requires of it — and the proof splits on it once.
-/

namespace SP1Clean.TraceGen

variable {p : ℕ}

/-- The `LoadX0` chip's committed input row for one event — a **real** row. The seven selectors are
read off the event's opcode discriminant (`Opcode::{LB,LBU,LH,LHU,LW,LWU,LD}` =
`29,32,30,33,31,34,35`), and the three offset bits are the address's low three bits. -/
def MemoryEvent.toLoadX0Inputs (e : MemoryEvent) : LoadX0Chip.Inputs (ZMod p) where
  is_lb := if e.opcode = 29 then 1 else 0
  is_lbu := if e.opcode = 32 then 1 else 0
  is_lh := if e.opcode = 30 then 1 else 0
  is_lhu := if e.opcode = 33 then 1 else 0
  is_lw := if e.opcode = 31 then 1 else 0
  is_lwu := if e.opcode = 34 then 1 else 0
  is_ld := if e.opcode = 35 then 1 else 0
  state := cpuStateCols e.clk e.pc
  adapter := iTypeReaderCols e.toITypeEvent
  memory_access := memoryAccessCols e.prevMem e.prevTsMem (e.clk + 1)
  offset_bit := #v[((e.addr % 2 : ℕ) : ZMod p), ((memLimbIndex e.addr % 2 : ℕ) : ZMod p),
                   ((memLimbIndex e.addr / 2 : ℕ) : ZMod p)]

lemma MemoryEvent.toLoadX0Inputs_offset_bit_zero (e : MemoryEvent) :
    (e.toLoadX0Inputs (p := p)).offset_bit[0] = ((e.addr % 2 : ℕ) : ZMod p) := rfl

lemma MemoryEvent.toLoadX0Inputs_offset_bit_one (e : MemoryEvent) :
    (e.toLoadX0Inputs (p := p)).offset_bit[1] = ((memLimbIndex e.addr % 2 : ℕ) : ZMod p) := rfl

lemma MemoryEvent.toLoadX0Inputs_offset_bit_two (e : MemoryEvent) :
    (e.toLoadX0Inputs (p := p)).offset_bit[2] = ((memLimbIndex e.addr / 2 : ℕ) : ZMod p) := rfl

end SP1Clean.TraceGen

namespace SP1Clean.LoadX0Chip

open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## The chip's honest-prover contract on a built row -/

/-- **A well-formed `x0`-destination load event builds a row the honest prover can complete.**
`hload` says which of the seven loads it is, and supplies that variant's alignment. -/
theorem proverAssumptions_of_event {e : MemoryEvent} (h : e.WellFormedX0) (hload : e.IsLoad)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ProverAssumptions (e.toLoadX0Inputs (p := p)) data hint := by
  have hp : 2 ^ 24 < p := Fact.out
  have haddr64 : (Word.toNat (e.toLoadX0Inputs (p := p)).op_b_val
      + Word.toNat (e.toLoadX0Inputs (p := p)).op_c_imm) % 2 ^ 64 = e.addr :=
    addr_eq h.b_lt h.imm_lt
  have haddr48 : (Word.toNat (e.toLoadX0Inputs (p := p)).op_b_val
      + Word.toNat (e.toLoadX0Inputs (p := p)).op_c_imm) % 2 ^ 48 = e.addr := by
    rw [← Nat.mod_mod_of_dvd _ (show (2 : ℕ) ^ 48 ∣ 2 ^ 64 from by norm_num), haddr64,
      Nat.mod_eq_of_lt h.addr_lt]
  have hidx : memLimbIndex e.addr < 4 := memLimbIndex_lt _
  have hone : (e.toLoadX0Inputs (p := p)).adapter.op_a_0 = 1 :=
    iTypeReaderCols_op_a_0_eq_one h.opA_eq_zero
  -- the seven-way variant split: the row is real, and each variant's own offset gates hold
  have hbranch : isReal (e.toLoadX0Inputs (p := p)) = 1
      ∧ (e.toLoadX0Inputs (p := p)).is_ld * (e.toLoadX0Inputs (p := p)).offset_bit[2] = 0
      ∧ ((e.toLoadX0Inputs (p := p)).is_lw + (e.toLoadX0Inputs (p := p)).is_lwu
          + (e.toLoadX0Inputs (p := p)).is_ld) * (e.toLoadX0Inputs (p := p)).offset_bit[1] = 0
      ∧ ((e.toLoadX0Inputs (p := p)).is_lh + (e.toLoadX0Inputs (p := p)).is_lhu
          + (e.toLoadX0Inputs (p := p)).is_lw + (e.toLoadX0Inputs (p := p)).is_lwu
          + (e.toLoadX0Inputs (p := p)).is_ld)
        * (e.toLoadX0Inputs (p := p)).offset_bit[0] = 0 := by
    rcases hload with (hop | hop) | ⟨(hop | hop), ha⟩ | ⟨(hop | hop), ha⟩ | ⟨hop, ha⟩ <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        simp only [isReal, MemoryEvent.toLoadX0Inputs_offset_bit_zero,
          MemoryEvent.toLoadX0Inputs_offset_bit_one, MemoryEvent.toLoadX0Inputs_offset_bit_two,
          show (e.toLoadX0Inputs (p := p)).is_lb = if e.opcode = 29 then 1 else 0 from rfl,
          show (e.toLoadX0Inputs (p := p)).is_lbu = if e.opcode = 32 then 1 else 0 from rfl,
          show (e.toLoadX0Inputs (p := p)).is_lh = if e.opcode = 30 then 1 else 0 from rfl,
          show (e.toLoadX0Inputs (p := p)).is_lhu = if e.opcode = 33 then 1 else 0 from rfl,
          show (e.toLoadX0Inputs (p := p)).is_lw = if e.opcode = 31 then 1 else 0 from rfl,
          show (e.toLoadX0Inputs (p := p)).is_lwu = if e.opcode = 34 then 1 else 0 from rfl,
          show (e.toLoadX0Inputs (p := p)).is_ld = if e.opcode = 35 then 1 else 0 from rfl,
          hop, memLimbIndex] <;>
        first
          | (rw [show e.addr % 2 = 0 from by omega]; norm_num)
          | (rw [show e.addr % 8 / 2 % 2 = 0 from by omega]; norm_num)
          | (rw [show e.addr % 8 / 2 / 2 = 0 from by omega]; norm_num)
          | norm_num
  -- every variant selector is built by an `if`, hence binary
  have hbin : ∀ k : ℕ, ((if e.opcode = k then (1 : ZMod p) else 0) = 0
      ∨ (if e.opcode = k then (1 : ZMod p) else 0) = 1) := by
    intro k
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  refine ⟨wordOfNat_isU64 _, wordOfNat_isU64 _, ?_, ?_, ?_, ?_, ?_, ?_, wordOfNat_isU64 _,
    hbin 29, hbin 32, hbin 30, hbin 33, hbin 31, hbin 34, hbin 35, Or.inr hbranch.1,
    hbranch.2.1, hbranch.2.2.1, hbranch.2.2.2, ?_, ?_,
    cpuState_spec e.clk e.pc h.clk_mod _ _ _,
    memoryAccess_spec h.clk_mod h.clk_lt h.prevTsMem_lt,
    iTypeReaderImmutable_spec_x0 h.clk_mod h.opA_eq_zero h.prevA_eq_zero h.prevTsA_lt
      h.prevTsB_lt _ _ _ _⟩
  -- the address fits in 48 bits and is above the reserved page
  · rw [haddr64]; exact h.addr_lt
  · rw [haddr48]; exact h.addr_ge
  -- the three offset bits decompose the address's low three bits, and are binary
  · show (((e.addr % 2 : ℕ) : ZMod p)).val + 2 * (((memLimbIndex e.addr % 2 : ℕ) : ZMod p)).val
      + 4 * (((memLimbIndex e.addr / 2 : ℕ) : ZMod p)).val = _
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega),
      ZMod.val_natCast_of_lt (by omega), haddr48, memLimbIndex]
    omega
  · show ((e.addr % 2 : ℕ) : ZMod p) = 0 ∨ ((e.addr % 2 : ℕ) : ZMod p) = 1
    rcases (by omega : e.addr % 2 = 0 ∨ e.addr % 2 = 1) with hb | hb
    · exact Or.inl (by rw [hb, Nat.cast_zero])
    · exact Or.inr (by rw [hb, Nat.cast_one])
  · show ((memLimbIndex e.addr % 2 : ℕ) : ZMod p) = 0 ∨ ((memLimbIndex e.addr % 2 : ℕ) : ZMod p) = 1
    rcases (by omega : memLimbIndex e.addr % 2 = 0 ∨ memLimbIndex e.addr % 2 = 1) with hb | hb
    · exact Or.inl (by rw [hb, Nat.cast_zero])
    · exact Or.inr (by rw [hb, Nat.cast_one])
  · show ((memLimbIndex e.addr / 2 : ℕ) : ZMod p) = 0 ∨ ((memLimbIndex e.addr / 2 : ℕ) : ZMod p) = 1
    rcases (by omega : memLimbIndex e.addr / 2 = 0 ∨ memLimbIndex e.addr / 2 = 1) with hb | hb
    · exact Or.inl (by rw [hb, Nat.cast_zero])
    · exact Or.inr (by rw [hb, Nat.cast_one])
  -- the destination-zero flag *is* the row selector: `op_a_0 = is_real = 1` on a real `x0` row
  · rw [hbranch.1, hone]; simp
  · rw [hbranch.1]; simp

/-! ## The built table -/

/-- The LoadX0 chip as a flat-AIR component: one circuit, checked independently on each row.

A plain `def`, deliberately not an `abbrev` (see `AddChip.component` for the measurement). -/
def component : Air.Flat.Component (ZMod p) := ⟨circuit⟩

/-- The rows a trace builds: one input row per event. **No padding tail** — see
`LoadWordChip/Complete.lean`. -/
def traceInputs (events : List MemoryEvent) : List (Inputs (ZMod p)) :=
  events.map MemoryEvent.toLoadX0Inputs

/-- Every row of a built trace satisfies the chip's honest-prover contract. -/
theorem proverAssumptions_of_mem_traceInputs {events : List MemoryEvent}
    (h : ∀ e ∈ events, e.WellFormedX0 ∧ e.IsLoad) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) events, ProverAssumptions input data hint := by
  intro input hin
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
  exact proverAssumptions_of_event (h e he).1 (h e he).2 data hint

/-- **A real trace builds a valid LoadX0 table.** -/
theorem traceTable_constraints (events : List MemoryEvent) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ e ∈ events, e.WellFormedX0 ∧ e.IsLoad) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events) data hint).Constraints :=
  Air.Flat.Table.build_constraints _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

/-- The same table satisfies its **channel guarantees**. -/
theorem traceTable_guarantees (events : List MemoryEvent) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ e ∈ events, e.WellFormedX0 ∧ e.IsLoad) :
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

end SP1Clean.LoadX0Chip
