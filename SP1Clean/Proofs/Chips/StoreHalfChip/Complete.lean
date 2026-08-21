import SP1Clean.FormalModel.TraceGen.Memory
import SP1Clean.Proofs.Chips.StoreHalfChip.Witgen
import ToClean.Air.TableBuild

/-! # `SP1Clean.StoreHalfChip` — from trace events to a valid AIR table

`SH` through the trace-generation chain (see `StoreWordChip/Complete.lean` for the store family's
programme note, including the `op_a`-is-a-read discipline and **why there is no padding row**).

The only thing new against StoreWord is the width of the merge. A half-word store overwrites one of
the RAM cell's **four** u16 limbs, so the row commits two offset bits (address bits 1 and 2) and the
four read-modify-write gates carry a two-factor coefficient each. That is the family's shared
`storeLimb` / `storeLimb_cases` (`FormalModel/TraceGen/Memory.lean`) — the byte store overwrites the
same limb with the same two bits — so the whole merge is one citation and a uniform four-way split.
-/

namespace SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime]

/-- The `StoreHalf` chip's committed input row for one event — a **real** row (`is_real = 1`). The
two offset bits are address bits 1 and 2 (the same pair `LoadHalf` commits), and the written word is
the RAM cell with the selected u16 limb replaced by `rs2`'s low limb. -/
def MemoryEvent.toStoreHalfInputs (e : MemoryEvent) : StoreHalfChip.Inputs (ZMod p) where
  is_real := 1
  state := cpuStateCols e.clk e.pc
  adapter := iTypeReaderCols e.toITypeEvent
  memory_access := memoryAccessCols e.prevMem e.prevTsMem (e.clk + 1)
  offset_bit := #v[((memLimbIndex e.addr % 2 : ℕ) : ZMod p),
                   ((memLimbIndex e.addr / 2 : ℕ) : ZMod p)]
  store_value := storeLimb e.prevMem (e.prevA % 2 ^ 16) e.addr

lemma MemoryEvent.toStoreHalfInputs_offset_bit_zero (e : MemoryEvent) :
    (e.toStoreHalfInputs (p := p)).offset_bit[0]
      = ((memLimbIndex e.addr % 2 : ℕ) : ZMod p) := rfl

lemma MemoryEvent.toStoreHalfInputs_offset_bit_one (e : MemoryEvent) :
    (e.toStoreHalfInputs (p := p)).offset_bit[1]
      = ((memLimbIndex e.addr / 2 : ℕ) : ZMod p) := rfl

lemma MemoryEvent.toStoreHalfInputs_store_value (e : MemoryEvent) :
    (e.toStoreHalfInputs (p := p)).store_value
      = storeLimb e.prevMem (e.prevA % 2 ^ 16) e.addr := rfl

lemma MemoryEvent.toStoreHalfInputs_prev_value (e : MemoryEvent) :
    (e.toStoreHalfInputs (p := p)).memory_access.prev_value = wordOfNat e.prevMem := rfl

lemma MemoryEvent.toStoreHalfInputs_op_a_value (e : MemoryEvent) :
    (e.toStoreHalfInputs (p := p)).adapter.op_a_memory.prev_value = wordOfNat e.prevA := rfl

end SP1Clean.TraceGen

namespace SP1Clean.StoreHalfChip

open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## The chip's honest-prover contract on a built row -/

/-- **A well-formed, 2-byte-aligned store trace event builds a row the honest prover can
complete.** `halign` is the per-instruction alignment fact (see `MemoryEvent.Aligned`). -/
theorem proverAssumptions_of_event {e : MemoryEvent} (h : e.WellFormedStore) (halign : e.Aligned 2)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ProverAssumptions (e.toStoreHalfInputs (p := p)) data hint := by
  have hp : 2 ^ 24 < p := Fact.out
  have haddr64 : (Word.toNat (e.toStoreHalfInputs (p := p)).op_b_val
      + Word.toNat (e.toStoreHalfInputs (p := p)).op_c_imm) % 2 ^ 64 = e.addr :=
    addr_eq h.b_lt h.imm_lt
  have haddr48 : (Word.toNat (e.toStoreHalfInputs (p := p)).op_b_val
      + Word.toNat (e.toStoreHalfInputs (p := p)).op_c_imm) % 2 ^ 48 = e.addr := by
    rw [← Nat.mod_mod_of_dvd _ (show (2 : ℕ) ^ 48 ∣ 2 ^ 64 from by norm_num), haddr64,
      Nat.mod_eq_of_lt h.addr_lt]
  have halign' : e.addr % 2 = 0 := halign
  have hidx : memLimbIndex e.addr < 4 := memLimbIndex_lt _
  have hval0 : (((memLimbIndex e.addr % 2 : ℕ) : ZMod p)).val = memLimbIndex e.addr % 2 :=
    ZMod.val_natCast_of_lt (by omega)
  have hval1 : (((memLimbIndex e.addr / 2 : ℕ) : ZMod p)).val = memLimbIndex e.addr / 2 :=
    ZMod.val_natCast_of_lt (by omega)
  -- the four address branches: the two committed offset bits, and the merged word's four limbs
  have hcases := storeLimb_cases (p := p) e.prevMem (e.prevA % 2 ^ 16) e.addr
  simp only [wordOfNat_zero, wordOfNat_one, wordOfNat_two, wordOfNat_three] at hcases
  refine ⟨wordOfNat_isU64 _, wordOfNat_isU64 _, ?_, ?_, ?_, ?_, ?_, ?_, Or.inr rfl,
    ⟨?_, ?_, ?_, ?_⟩,
    cpuState_spec e.clk e.pc h.clk_mod _ _ _,
    memoryAccess_spec h.clk_mod h.clk_lt h.prevTsMem_lt,
    iTypeReaderImmutable_spec h.clk_mod h.opA_lt h.prevA_x0 h.prevTsA_lt h.prevTsB_lt _ _ _ _,
    fun _ => ⟨iTypeReaderCols_op_a_val_lt h.opA_lt, (cpuStateCols_pc_val_lt e.clk e.pc).1,
      (cpuStateCols_pc_val_lt e.clk e.pc).2.1, (cpuStateCols_pc_val_lt e.clk e.pc).2.2⟩,
    fun _ => storeLimb_isU64 _ _ (by omega)⟩
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
  -- the four read-modify-write gates: the selected limb is `rs2`'s low limb, the other three stay
  · simp only [MemoryEvent.toStoreHalfInputs_store_value, MemoryEvent.toStoreHalfInputs_prev_value,
      MemoryEvent.toStoreHalfInputs_op_a_value, MemoryEvent.toStoreHalfInputs_offset_bit_zero,
      MemoryEvent.toStoreHalfInputs_offset_bit_one, wordOfNat_zero]
    rcases hcases with ⟨h0, h1, -, hs, -, -, -⟩ | ⟨h0, h1, -, hs, -, -, -⟩
      | ⟨h0, h1, -, hs, -, -, -⟩ | ⟨h0, h1, -, hs, -, -, -⟩ <;>
      rw [h0, h1] <;> linear_combination hs
  · simp only [MemoryEvent.toStoreHalfInputs_store_value, MemoryEvent.toStoreHalfInputs_prev_value,
      MemoryEvent.toStoreHalfInputs_op_a_value, MemoryEvent.toStoreHalfInputs_offset_bit_zero,
      MemoryEvent.toStoreHalfInputs_offset_bit_one, wordOfNat_zero, wordOfNat_one]
    rcases hcases with ⟨h0, h1, -, -, hs, -, -⟩ | ⟨h0, h1, -, -, hs, -, -⟩
      | ⟨h0, h1, -, -, hs, -, -⟩ | ⟨h0, h1, -, -, hs, -, -⟩ <;>
      rw [h0, h1] <;> linear_combination hs
  · simp only [MemoryEvent.toStoreHalfInputs_store_value, MemoryEvent.toStoreHalfInputs_prev_value,
      MemoryEvent.toStoreHalfInputs_op_a_value, MemoryEvent.toStoreHalfInputs_offset_bit_zero,
      MemoryEvent.toStoreHalfInputs_offset_bit_one, wordOfNat_zero, wordOfNat_two]
    rcases hcases with ⟨h0, h1, -, -, -, hs, -⟩ | ⟨h0, h1, -, -, -, hs, -⟩
      | ⟨h0, h1, -, -, -, hs, -⟩ | ⟨h0, h1, -, -, -, hs, -⟩ <;>
      rw [h0, h1] <;> linear_combination hs
  · simp only [MemoryEvent.toStoreHalfInputs_store_value, MemoryEvent.toStoreHalfInputs_prev_value,
      MemoryEvent.toStoreHalfInputs_op_a_value, MemoryEvent.toStoreHalfInputs_offset_bit_zero,
      MemoryEvent.toStoreHalfInputs_offset_bit_one, wordOfNat_zero, wordOfNat_three]
    rcases hcases with ⟨h0, h1, -, -, -, -, hs⟩ | ⟨h0, h1, -, -, -, -, hs⟩
      | ⟨h0, h1, -, -, -, -, hs⟩ | ⟨h0, h1, -, -, -, -, hs⟩ <;>
      rw [h0, h1] <;> linear_combination hs

/-! ## The built table -/

/-- The StoreHalf chip as a flat-AIR component: one circuit, checked independently on each row.

A plain `def`, deliberately not an `abbrev` (see `AddChip.component` for the measurement). -/
def component : Air.Flat.Component (ZMod p) := ⟨circuit⟩

/-- The rows a trace builds: one input row per event. **No padding tail** — see
`StoreWordChip/Complete.lean`. -/
def traceInputs (events : List MemoryEvent) : List (Inputs (ZMod p)) :=
  events.map MemoryEvent.toStoreHalfInputs

/-- Every row of a built trace satisfies the chip's honest-prover contract. -/
theorem proverAssumptions_of_mem_traceInputs {events : List MemoryEvent}
    (h : ∀ e ∈ events, e.WellFormedStore ∧ e.Aligned 2) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) events, ProverAssumptions input data hint := by
  intro input hin
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
  exact proverAssumptions_of_event (h e he).1 (h e he).2 data hint

/-- **A real trace builds a valid StoreHalf table.** -/
theorem traceTable_constraints (events : List MemoryEvent) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ e ∈ events, e.WellFormedStore ∧ e.Aligned 2) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events) data hint).Constraints :=
  Air.Flat.Table.build_constraints _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

/-- The same table satisfies its **channel guarantees**. -/
theorem traceTable_guarantees (events : List MemoryEvent) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ e ∈ events, e.WellFormedStore ∧ e.Aligned 2) :
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

end SP1Clean.StoreHalfChip
