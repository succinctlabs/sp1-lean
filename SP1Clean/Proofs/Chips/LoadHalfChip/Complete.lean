import SP1Clean.FormalModel.TraceGen.Memory
import SP1Clean.Proofs.Chips.LoadHalfChip.Witgen
import ToClean.Air.TableBuild

/-! # `SP1Clean.LoadHalfChip` — from trace events to a valid AIR table

`LH`/`LHU` through the trace-generation chain (see `LoadWordChip/Complete.lean` for the
memory-family programme note, including **why there is no padding row**).

The only thing new against LoadWord is the width of the selection. A half-word load picks one of
the RAM cell's **four** u16 limbs, so the row commits two offset bits (address bits 1 and 2) and
the four selection gates carry a two-factor guard each. All of that is the family's shared
`memLimb_cases` (`FormalModel/TraceGen/Memory.lean`) — the byte load selects the same limb with the
same two bits — so the whole selection is one citation and four `simp only`s. -/

namespace SP1Clean.TraceGen

variable {p : ℕ}

/-- The `LoadHalf` chip's committed input row for one event — a **real** row. The two selectors are
read off the event's opcode discriminant (`Opcode::LH = 30`, `Opcode::LHU = 33`). -/
def MemoryEvent.toLoadHalfInputs (e : MemoryEvent) : LoadHalfChip.Inputs (ZMod p) where
  is_lh := if e.opcode = 30 then 1 else 0
  is_lhu := if e.opcode = 30 then 0 else 1
  state := cpuStateCols e.clk e.pc
  adapter := iTypeReaderCols e.toITypeEvent
  memory_access := memoryAccessCols e.prevMem e.prevTsMem (e.clk + 1)
  offset_bit := #v[((memLimbIndex e.addr % 2 : ℕ) : ZMod p),
                   ((memLimbIndex e.addr / 2 : ℕ) : ZMod p)]
  selected_half := ((memLimb e.prevMem e.addr : ℕ) : ZMod p)
  msb := if e.opcode = 30 ∧ 32768 ≤ memLimb e.prevMem e.addr then 1 else 0

lemma MemoryEvent.toLoadHalfInputs_offset_bit_zero (e : MemoryEvent) :
    (e.toLoadHalfInputs (p := p)).offset_bit[0]
      = ((memLimbIndex e.addr % 2 : ℕ) : ZMod p) := rfl

lemma MemoryEvent.toLoadHalfInputs_offset_bit_one (e : MemoryEvent) :
    (e.toLoadHalfInputs (p := p)).offset_bit[1]
      = ((memLimbIndex e.addr / 2 : ℕ) : ZMod p) := rfl

lemma MemoryEvent.toLoadHalfInputs_selected_half (e : MemoryEvent) :
    (e.toLoadHalfInputs (p := p)).selected_half
      = ((memLimb e.prevMem e.addr : ℕ) : ZMod p) := rfl

lemma MemoryEvent.toLoadHalfInputs_prev_value (e : MemoryEvent) :
    (e.toLoadHalfInputs (p := p)).memory_access.prev_value = wordOfNat e.prevMem := rfl

lemma MemoryEvent.toLoadHalfInputs_is_lh (e : MemoryEvent) :
    (e.toLoadHalfInputs (p := p)).is_lh = if e.opcode = 30 then 1 else 0 := rfl

lemma MemoryEvent.toLoadHalfInputs_is_lhu (e : MemoryEvent) :
    (e.toLoadHalfInputs (p := p)).is_lhu = if e.opcode = 30 then 0 else 1 := rfl

lemma MemoryEvent.toLoadHalfInputs_msb (e : MemoryEvent) :
    (e.toLoadHalfInputs (p := p)).msb
      = if e.opcode = 30 ∧ 32768 ≤ memLimb e.prevMem e.addr then 1 else 0 := rfl

end SP1Clean.TraceGen

namespace SP1Clean.LoadHalfChip

open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## The chip's honest-prover contract on a built row -/

/-- **A well-formed, 2-byte-aligned memory trace event builds a row the honest prover can
complete.** `halign` is the per-instruction alignment fact (see `MemoryEvent.Aligned`). -/
theorem proverAssumptions_of_event {e : MemoryEvent} (h : e.WellFormed) (halign : e.Aligned 2)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ProverAssumptions (e.toLoadHalfInputs (p := p)) data hint := by
  have hp : 2 ^ 24 < p := Fact.out
  have hi := h.toITypeWellFormed
  have haddr64 : (Word.toNat (e.toLoadHalfInputs (p := p)).op_b_val
      + Word.toNat (e.toLoadHalfInputs (p := p)).op_c_imm) % 2 ^ 64 = e.addr := addr_eq hi.b_lt hi.imm_lt
  have haddr48 : (Word.toNat (e.toLoadHalfInputs (p := p)).op_b_val
      + Word.toNat (e.toLoadHalfInputs (p := p)).op_c_imm) % 2 ^ 48 = e.addr := by
    rw [← Nat.mod_mod_of_dvd _ (show (2 : ℕ) ^ 48 ∣ 2 ^ 64 from by norm_num), haddr64,
      Nat.mod_eq_of_lt h.addr_lt]
  have halign' : e.addr % 2 = 0 := halign
  have hidx : memLimbIndex e.addr < 4 := by rw [memLimbIndex]; omega
  have hval0 : (((memLimbIndex e.addr % 2 : ℕ) : ZMod p)).val = memLimbIndex e.addr % 2 :=
    ZMod.val_natCast_of_lt (by omega)
  have hval1 : (((memLimbIndex e.addr / 2 : ℕ) : ZMod p)).val = memLimbIndex e.addr / 2 :=
    ZMod.val_natCast_of_lt (by omega)
  have hlimbs := Word.lt_cases_of_isU64 (wordOfNat_isU64 (p := p) e.prevMem)
  have hselHigh_lt : memLimb e.prevMem e.addr < 2 ^ 16 := by
    rw [memLimb]; omega
  -- the four address branches: the two committed offset bits, and which limb they select
  have hsel := memLimb_cases (p := p) e.prevMem e.addr
  refine ⟨wordOfNat_isU64 _, wordOfNat_isU64 _, ?_, ?_, ?_, ?_, ?_, ?_,
    hlimbs.1, hlimbs.2.1, hlimbs.2.2.1, hlimbs.2.2.2, ?_, ?_, ?_,
    iTypeReaderCols_op_a_0_eq_zero hi.opA_ne_zero, ⟨?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_⟩,
    cpuState_spec e.clk e.pc hi.clk_mod _ _ _,
    memoryAccess_spec hi.clk_mod h.clk_lt h.prevTsMem_lt,
    iTypeReader_spec hi _ _ _ _ _ _ _ _⟩
  -- the address fits in 48 bits, is above the reserved page, and is 2-byte aligned
  · rw [haddr64]; exact h.addr_lt
  · rw [haddr48]; exact h.addr_ge
  · rw [haddr48]; exact halign'
  -- the two offset bits are binary, and decompose the address's low three bits
  · show ((memLimbIndex e.addr % 2 : ℕ) : ZMod p) = 0 ∨ ((memLimbIndex e.addr % 2 : ℕ) : ZMod p) = 1
    rcases (by omega : memLimbIndex e.addr % 2 = 0 ∨ memLimbIndex e.addr % 2 = 1) with hb | hb
    · exact Or.inl (by rw [hb, Nat.cast_zero])
    · exact Or.inr (by rw [hb, Nat.cast_one])
  · show ((memLimbIndex e.addr / 2 : ℕ) : ZMod p) = 0 ∨ ((memLimbIndex e.addr / 2 : ℕ) : ZMod p) = 1
    rcases (by omega : memLimbIndex e.addr / 2 = 0 ∨ memLimbIndex e.addr / 2 = 1) with hb | hb
    · exact Or.inl (by rw [hb, Nat.cast_zero])
    · exact Or.inr (by rw [hb, Nat.cast_one])
  · show 2 * (((memLimbIndex e.addr % 2 : ℕ) : ZMod p)).val
      + 4 * (((memLimbIndex e.addr / 2 : ℕ) : ZMod p)).val = _
    rw [hval0, hval1, haddr48, memLimbIndex]
    omega
  -- the two opcode selectors, and their sum
  · rw [MemoryEvent.toLoadHalfInputs_is_lh]; split
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rw [MemoryEvent.toLoadHalfInputs_is_lhu]; split
    · exact Or.inl rfl
    · exact Or.inr rfl
  · right
    show (e.toLoadHalfInputs (p := p)).is_lh + (e.toLoadHalfInputs (p := p)).is_lhu = 1
    rw [MemoryEvent.toLoadHalfInputs_is_lh, MemoryEvent.toLoadHalfInputs_is_lhu]
    split
    · rw [add_zero]
    · rw [zero_add]
  -- the four offset-selection gates: an equality in the selected branch, a zero factor otherwise
  · rcases hsel with ⟨h0, h1, hs⟩ | ⟨h0, h1, hs⟩ | ⟨h0, h1, hs⟩ | ⟨h0, h1, hs⟩ <;>
      simp only [MemoryEvent.toLoadHalfInputs_offset_bit_zero,
        MemoryEvent.toLoadHalfInputs_offset_bit_one, MemoryEvent.toLoadHalfInputs_selected_half,
        MemoryEvent.toLoadHalfInputs_prev_value, Nat.cast_one, h0, h1, hs, sub_self, mul_zero,
        zero_mul]
  · rcases hsel with ⟨h0, h1, hs⟩ | ⟨h0, h1, hs⟩ | ⟨h0, h1, hs⟩ | ⟨h0, h1, hs⟩ <;>
      simp only [MemoryEvent.toLoadHalfInputs_offset_bit_zero,
        MemoryEvent.toLoadHalfInputs_offset_bit_one, MemoryEvent.toLoadHalfInputs_selected_half,
        MemoryEvent.toLoadHalfInputs_prev_value, h0, h1, hs, sub_self, mul_zero,
        zero_mul]
  · rcases hsel with ⟨h0, h1, hs⟩ | ⟨h0, h1, hs⟩ | ⟨h0, h1, hs⟩ | ⟨h0, h1, hs⟩ <;>
      simp only [MemoryEvent.toLoadHalfInputs_offset_bit_zero,
        MemoryEvent.toLoadHalfInputs_offset_bit_one, MemoryEvent.toLoadHalfInputs_selected_half,
        MemoryEvent.toLoadHalfInputs_prev_value, Nat.cast_one, h0, h1, hs, sub_self, mul_zero,
        zero_mul]
  · rcases hsel with ⟨h0, h1, hs⟩ | ⟨h0, h1, hs⟩ | ⟨h0, h1, hs⟩ | ⟨h0, h1, hs⟩ <;>
      simp only [MemoryEvent.toLoadHalfInputs_offset_bit_zero,
        MemoryEvent.toLoadHalfInputs_offset_bit_one, MemoryEvent.toLoadHalfInputs_selected_half,
        MemoryEvent.toLoadHalfInputs_prev_value, h0, h1, hs, sub_self, mul_zero,
        zero_mul]
  -- LHU zero-extends: the sign bit is built as `0` unless the row is an `LH`
  · show (e.toLoadHalfInputs (p := p)).is_lhu * (e.toLoadHalfInputs (p := p)).msb = 0
    rw [MemoryEvent.toLoadHalfInputs_msb, MemoryEvent.toLoadHalfInputs_is_lhu]
    by_cases hop : e.opcode = 30
    · rw [if_pos hop, zero_mul]
    · rw [if_neg hop, if_neg (by tauto), mul_zero]
  -- the MSB gadget
  · show (e.toLoadHalfInputs (p := p)).msb = 0 ∨ (e.toLoadHalfInputs (p := p)).msb = 1
    rw [MemoryEvent.toLoadHalfInputs_msb]
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  · intro hlh
    have hop : e.opcode = 30 := by
      by_contra hne
      rw [MemoryEvent.toLoadHalfInputs_is_lh, if_neg hne] at hlh
      exact zero_ne_one hlh
    show (if e.opcode = 30 ∧ 32768 ≤ memLimb e.prevMem e.addr then (1 : ZMod p) else 0)
      = if 32768 ≤ (((memLimb e.prevMem e.addr : ℕ) : ZMod p)).val then 1 else 0
    rw [ZMod.val_natCast_of_lt (by omega)]
    by_cases hb : 32768 ≤ memLimb e.prevMem e.addr
    · rw [if_pos ⟨hop, hb⟩, if_pos hb]
    · rw [if_neg (by tauto), if_neg hb]

/-! ## The built table -/

/-- The LoadHalf chip as a flat-AIR component: one circuit, checked independently on each row.

A plain `def`, deliberately not an `abbrev` (see `AddChip.component` for the measurement). -/
def component : Air.Flat.Component (ZMod p) := ⟨circuit⟩

/-- The rows a trace builds: one input row per event. **No padding tail** — see
`LoadWordChip/Complete.lean`. -/
def traceInputs (events : List MemoryEvent) : List (Inputs (ZMod p)) :=
  events.map MemoryEvent.toLoadHalfInputs

/-- Every row of a built trace satisfies the chip's honest-prover contract. -/
theorem proverAssumptions_of_mem_traceInputs {events : List MemoryEvent}
    (h : ∀ e ∈ events, e.WellFormed ∧ e.Aligned 2) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) events, ProverAssumptions input data hint := by
  intro input hin
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
  exact proverAssumptions_of_event (h e he).1 (h e he).2 data hint

/-- **A real trace builds a valid LoadHalf table.** -/
theorem traceTable_constraints (events : List MemoryEvent) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ e ∈ events, e.WellFormed ∧ e.Aligned 2) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events) data hint).Constraints :=
  Air.Flat.Table.build_constraints _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

/-- The same table satisfies its **channel guarantees**. -/
theorem traceTable_guarantees (events : List MemoryEvent) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ e ∈ events, e.WellFormed ∧ e.Aligned 2) :
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

end SP1Clean.LoadHalfChip
