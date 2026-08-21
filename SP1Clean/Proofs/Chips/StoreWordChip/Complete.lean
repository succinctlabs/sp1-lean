import SP1Clean.FormalModel.TraceGen.Memory
import SP1Clean.Proofs.Chips.StoreWordChip.Witgen
import ToClean.Air.TableBuild

/-! # `SP1Clean.StoreWordChip` — from trace events to a valid AIR table (the store template)

The first chip of the **store** family through the trace-generation chain (see
`AddChip/Complete.lean` for the programme note and `LoadWordChip/Complete.lean` for the memory
family's). `StoreWord` is `LoadWord` read backwards: the same `Extracted.ITypeReader` columns, the
same `AddressOperation`, the same `MemoryAccess` primitive at the same 8-byte-aligned cell — and
three differences, each of which is where this file's real content is.

1. **`op_a` is a source read, not a destination write.** A store composes
   `Readers.ITypeReaderImmutable`, whose four `op_a_0` gates pin the *read* value of `x0` rather
   than a written value, and SP1 routes an `op_a = x0` store to the ordinary store chip rather than
   to a separate one (`Soundness/Coverage.lean`: "stores ignore rd"). So the event predicate is
   `MemoryEvent.WellFormedStore` — `WellFormed` with the load family's `rd ≠ x0` routing condition
   replaced by "`x0` reads as zero" — and the reader discharge is the general
   `iTypeReaderImmutable_spec`.
2. **The stored word is already in the record.** `op_a_memory.prev_value` *is* the value read from
   `rs2`, so the word this row stores is the event's inherited `prevA`; no new event field.
3. **The store-value mux.** Because the memory bus is word-granular, `SW` is a read-modify-write:
   the committed `store_value` column is the old cell with the `offset_bit`-selected 32-bit half
   replaced by `rs2`'s low two limbs. That column is an *input*, so the builder computes it
   (`storeWordValue`), and the chip's four merge equations hold one branch at a time.

## Why there is no padding row here

Exactly as for the loads: SP1 pads with literal zero rows, but this chip's `ProverAssumptions`
states the `AddressOperation` address facts **ungated**, and `2 ^ 16 ≤ addr` is false at the zero
row. So no zero padding row satisfies the honest-prover contract, and the theorems below are stated
over the event rows alone. The defect is inherited from `AddressOperation.Assumptions` and is shared
by all five load and all four store chips; it is reported (`docs/verification-report.md` §12), not
patched, since gating it re-opens `AddressOperation.completeness` and nine chip completeness proofs.
-/

namespace SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime]

/-! ## The StoreWord row's committed sub-word columns

Two columns SP1's `StoreWordChip::event_to_row` computes from the address, the RAM cell and the
`rs2` value. They are *inputs* to the Clean circuit (not witnesses), so the builder produces them. -/

omit [Fact p.Prime] in
/-- Bit 2 of the effective address — SP1's `offset_bit` for a 4-byte store, selecting the low (`0`)
or high (`1`) 32-bit half of the 8-byte RAM cell. The same column `LoadWord` commits. -/
def storeWordOffsetBit (addr : ℕ) : ℕ := addr % 8 / 4

/-- The word a `SW` row writes: the RAM cell `mem` with the address-selected 32-bit half replaced
by the low 32 bits of the stored register value `reg`. The word half of the read-modify-write —
the memory bus is word-granular, so the untouched half is kept verbatim. -/
def storeWordValue (mem reg addr : ℕ) : Word (ZMod p) :=
  if addr % 8 < 4 then
    #v[((reg % 2 ^ 16 : ℕ) : ZMod p), ((reg / 2 ^ 16 % 2 ^ 16 : ℕ) : ZMod p),
       ((mem / 2 ^ 32 % 2 ^ 16 : ℕ) : ZMod p), ((mem / 2 ^ 48 % 2 ^ 16 : ℕ) : ZMod p)]
  else
    #v[((mem % 2 ^ 16 : ℕ) : ZMod p), ((mem / 2 ^ 16 % 2 ^ 16 : ℕ) : ZMod p),
       ((reg % 2 ^ 16 : ℕ) : ZMod p), ((reg / 2 ^ 16 % 2 ^ 16 : ℕ) : ZMod p)]

/-- The merged word is a valid u64: every limb is a u16 residue, in both branches. -/
lemma storeWordValue_isU64 [Fact (2 ^ 24 < p)] (mem reg addr : ℕ) :
    Word.isU64 (storeWordValue (p := p) mem reg addr) := by
  have hp : 2 ^ 24 < p := Fact.out
  refine Word.isU64_of_cases ?_ ?_ ?_ ?_ <;>
    · rw [storeWordValue]
      split <;>
        · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
            List.getElem_cons_succ]
          rw [ZMod.val_natCast_of_lt (by omega)]
          omega

/-- The `StoreWord` chip's committed input row for one event — a **real** row (`is_real = 1`). The
stored register value is the event's `prevA`: `op_a` is `rs2`, read through the immutable adapter. -/
def MemoryEvent.toStoreWordInputs (e : MemoryEvent) : StoreWordChip.Inputs (ZMod p) where
  is_real := 1
  state := cpuStateCols e.clk e.pc
  adapter := iTypeReaderCols e.toITypeEvent
  memory_access := memoryAccessCols e.prevMem e.prevTsMem (e.clk + 1)
  offset_bit := ((storeWordOffsetBit e.addr : ℕ) : ZMod p)
  store_value := storeWordValue e.prevMem e.prevA e.addr

lemma MemoryEvent.toStoreWordInputs_offset_bit (e : MemoryEvent) :
    (e.toStoreWordInputs (p := p)).offset_bit
      = ((storeWordOffsetBit e.addr : ℕ) : ZMod p) := rfl

lemma MemoryEvent.toStoreWordInputs_store_value (e : MemoryEvent) :
    (e.toStoreWordInputs (p := p)).store_value
      = storeWordValue e.prevMem e.prevA e.addr := rfl

lemma MemoryEvent.toStoreWordInputs_prev_value (e : MemoryEvent) :
    (e.toStoreWordInputs (p := p)).memory_access.prev_value = wordOfNat e.prevMem := rfl

lemma MemoryEvent.toStoreWordInputs_op_a_value (e : MemoryEvent) :
    (e.toStoreWordInputs (p := p)).adapter.op_a_memory.prev_value = wordOfNat e.prevA := rfl

end SP1Clean.TraceGen

namespace SP1Clean.StoreWordChip

open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## The chip's honest-prover contract on a built row -/

/--
**A well-formed, 4-byte-aligned store trace event builds a row the honest prover can complete.**

`halign` is the per-instruction fact `MemoryEvent.WellFormedStore` cannot carry, for the same reason
`JTypeEvent.UTypeImm` is separate: the record is shared by the whole memory family, and `SB` rows
are not aligned at all.

The `data` and `hint` are arbitrary: `StoreWord`'s prover contract reads neither.
-/
theorem proverAssumptions_of_event {e : MemoryEvent} (h : e.WellFormedStore) (halign : e.Aligned 4)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ProverAssumptions (e.toStoreWordInputs (p := p)) data hint := by
  have hp : 2 ^ 24 < p := Fact.out
  -- the address the `AddressOperation` gadget sees, in both spellings its contract uses
  have haddr64 : (Word.toNat (e.toStoreWordInputs (p := p)).op_b_val
      + Word.toNat (e.toStoreWordInputs (p := p)).op_c_imm) % 2 ^ 64 = e.addr :=
    addr_eq h.b_lt h.imm_lt
  have haddr48 : (Word.toNat (e.toStoreWordInputs (p := p)).op_b_val
      + Word.toNat (e.toStoreWordInputs (p := p)).op_c_imm) % 2 ^ 48 = e.addr := by
    rw [← Nat.mod_mod_of_dvd _ (show (2 : ℕ) ^ 48 ∣ 2 ^ 64 from by norm_num), haddr64,
      Nat.mod_eq_of_lt h.addr_lt]
  have halign' : e.addr % 4 = 0 := halign
  -- the offset bit: `4 · offset_bit = addr mod 8`, and it is `0` or `1` because the row is aligned
  have hoff8 : 4 * storeWordOffsetBit e.addr = e.addr % 8 := by
    rw [storeWordOffsetBit]; omega
  have hoffval : (((storeWordOffsetBit e.addr : ℕ) : ZMod p)).val = storeWordOffsetBit e.addr := by
    rw [ZMod.val_natCast_of_lt (by rw [storeWordOffsetBit]; omega)]
  -- the two address branches, as one disjunction over the offset bit and the four merged limbs
  have hsel : (((storeWordOffsetBit e.addr : ℕ) : ZMod p) = 0
        ∧ (storeWordValue (p := p) e.prevMem e.prevA e.addr)[0] = (wordOfNat (p := p) e.prevA)[0]
        ∧ (storeWordValue (p := p) e.prevMem e.prevA e.addr)[1] = (wordOfNat (p := p) e.prevA)[1]
        ∧ (storeWordValue (p := p) e.prevMem e.prevA e.addr)[2] = (wordOfNat (p := p) e.prevMem)[2]
        ∧ (storeWordValue (p := p) e.prevMem e.prevA e.addr)[3] = (wordOfNat (p := p) e.prevMem)[3])
      ∨ (((storeWordOffsetBit e.addr : ℕ) : ZMod p) = 1
        ∧ (storeWordValue (p := p) e.prevMem e.prevA e.addr)[0] = (wordOfNat (p := p) e.prevMem)[0]
        ∧ (storeWordValue (p := p) e.prevMem e.prevA e.addr)[1] = (wordOfNat (p := p) e.prevMem)[1]
        ∧ (storeWordValue (p := p) e.prevMem e.prevA e.addr)[2] = (wordOfNat (p := p) e.prevA)[0]
        ∧ (storeWordValue (p := p) e.prevMem e.prevA e.addr)[3]
            = (wordOfNat (p := p) e.prevA)[1]) := by
    by_cases hlow : e.addr % 8 < 4
    · refine Or.inl ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [storeWordOffsetBit, Nat.div_eq_of_lt hlow, Nat.cast_zero]
      · rw [storeWordValue, if_pos hlow, wordOfNat_zero]; simp
      · rw [storeWordValue, if_pos hlow, wordOfNat_one]; simp
      · rw [storeWordValue, if_pos hlow, wordOfNat_two]; simp
      · rw [storeWordValue, if_pos hlow, wordOfNat_three]; simp
    · refine Or.inr ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [storeWordOffsetBit, show e.addr % 8 / 4 = 1 from by omega, Nat.cast_one]
      · rw [storeWordValue, if_neg hlow, wordOfNat_zero]; simp
      · rw [storeWordValue, if_neg hlow, wordOfNat_one]; simp
      · rw [storeWordValue, if_neg hlow, wordOfNat_zero]; simp
      · rw [storeWordValue, if_neg hlow, wordOfNat_one]; simp
  refine ⟨wordOfNat_isU64 _, wordOfNat_isU64 _, ?_, ?_, ?_, ?_, Or.inr rfl, ⟨?_, ?_, ?_, ?_⟩,
    cpuState_spec e.clk e.pc h.clk_mod _ _ _,
    memoryAccess_spec h.clk_mod h.clk_lt h.prevTsMem_lt,
    iTypeReaderImmutable_spec h.clk_mod h.opA_lt h.prevA_x0 h.prevTsA_lt h.prevTsB_lt _ _ _ _,
    fun _ => ⟨iTypeReaderCols_op_a_val_lt h.opA_lt, (cpuStateCols_pc_val_lt e.clk e.pc).1,
      (cpuStateCols_pc_val_lt e.clk e.pc).2.1, (cpuStateCols_pc_val_lt e.clk e.pc).2.2⟩,
    fun _ => storeWordValue_isU64 _ _ _⟩
  -- the address fits in 48 bits, is above the reserved page, and is 4-byte aligned
  · rw [haddr64]; exact h.addr_lt
  · rw [haddr48]; exact h.addr_ge
  · rw [haddr48]; exact halign'
  -- `4 · offset_bit = addr mod 8`
  · rw [MemoryEvent.toStoreWordInputs_offset_bit, hoffval, haddr48]; exact hoff8
  -- the four read-modify-write gates: in each branch the selected half is `rs2`, the other is kept
  · simp only [MemoryEvent.toStoreWordInputs_store_value, MemoryEvent.toStoreWordInputs_prev_value,
      MemoryEvent.toStoreWordInputs_op_a_value, MemoryEvent.toStoreWordInputs_offset_bit]
    rcases hsel with ⟨ho, hs, -, -, -⟩ | ⟨ho, hs, -, -, -⟩ <;> rw [ho] <;> linear_combination hs
  · simp only [MemoryEvent.toStoreWordInputs_store_value, MemoryEvent.toStoreWordInputs_prev_value,
      MemoryEvent.toStoreWordInputs_op_a_value, MemoryEvent.toStoreWordInputs_offset_bit]
    rcases hsel with ⟨ho, -, hs, -, -⟩ | ⟨ho, -, hs, -, -⟩ <;> rw [ho] <;> linear_combination hs
  · simp only [MemoryEvent.toStoreWordInputs_store_value, MemoryEvent.toStoreWordInputs_prev_value,
      MemoryEvent.toStoreWordInputs_op_a_value, MemoryEvent.toStoreWordInputs_offset_bit]
    rcases hsel with ⟨ho, -, -, hs, -⟩ | ⟨ho, -, -, hs, -⟩ <;> rw [ho] <;> linear_combination hs
  · simp only [MemoryEvent.toStoreWordInputs_store_value, MemoryEvent.toStoreWordInputs_prev_value,
      MemoryEvent.toStoreWordInputs_op_a_value, MemoryEvent.toStoreWordInputs_offset_bit]
    rcases hsel with ⟨ho, -, -, -, hs⟩ | ⟨ho, -, -, -, hs⟩ <;> rw [ho] <;> linear_combination hs

/-! ## The built table -/

/-- The StoreWord chip as a flat-AIR component: one circuit, checked independently on each row.

A plain `def`, deliberately not an `abbrev` (see `AddChip.component` for the measurement). -/
def component : Air.Flat.Component (ZMod p) := ⟨circuit⟩

/-- The rows a trace builds: one input row per event. **No padding tail** — SP1 pads with zero
rows, and this chip's `ProverAssumptions` is not satisfied there (see the module docstring). -/
def traceInputs (events : List MemoryEvent) : List (Inputs (ZMod p)) :=
  events.map MemoryEvent.toStoreWordInputs

/-- Every row of a built trace satisfies the chip's honest-prover contract. -/
theorem proverAssumptions_of_mem_traceInputs {events : List MemoryEvent}
    (h : ∀ e ∈ events, e.WellFormedStore ∧ e.Aligned 4) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) events, ProverAssumptions input data hint := by
  intro input hin
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
  exact proverAssumptions_of_event (h e he).1 (h e he).2 data hint

/-- **A real trace builds a valid StoreWord table.** Every `assertZero` of the whole flattened chip
circuit — the address gadget's carry chain and metadata gates, the memory primitive's timestamp
comparison, the two readers, and the chip's own read-modify-write and selector gates — evaluates to
zero on every built row, and no static lookup is left unchecked. -/
theorem traceTable_constraints (events : List MemoryEvent) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ e ∈ events, e.WellFormedStore ∧ e.Aligned 4) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events) data hint).Constraints :=
  Air.Flat.Table.build_constraints _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

/-- The same table satisfies its **channel guarantees** — every message it pushes onto the State,
Memory, Program and Byte channels carries the payload its channel promises. -/
theorem traceTable_guarantees (events : List MemoryEvent) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ e ∈ events, e.WellFormedStore ∧ e.Aligned 4) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events) data hint).Guarantees :=
  Air.Flat.Table.build_guarantees _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

/-- The table's interaction list on a channel, in closed form: the per-row evaluated interactions,
concatenated in row order. -/
theorem traceTable_interactionsWith (events : List MemoryEvent) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (channel : RawChannel (ZMod p)) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events) data
        hint).interactionsWith channel =
      (traceInputs (p := p) events).flatMap fun input =>
        (component (p := p)).operations.interactionValuesWith channel
          (Environment.fromArray ((component (p := p)).buildRow input data hint) data) :=
  Air.Flat.Table.build_interactions _ _ _ _ channel

end SP1Clean.StoreWordChip
