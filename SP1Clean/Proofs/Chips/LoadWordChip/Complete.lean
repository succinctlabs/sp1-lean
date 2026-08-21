import SP1Clean.FormalModel.TraceGen.Memory
import SP1Clean.Proofs.Chips.LoadWordChip.Witgen
import ToClean.Air.TableBuild

/-! # `SP1Clean.LoadWordChip` — from trace events to a valid AIR table (the memory template)

The first chip of the **memory** family through the trace-generation chain (see
`AddChip/Complete.lean` for the programme note). `LoadWord` reads the same `Extracted.ITypeReader`
adapter as `Addi`, so its register half is `iTypeReader_spec` verbatim; everything else is new, and
splits into three pieces.

1. **The RAM access.** `memoryAccess_spec` (`FormalModel/TraceGen/Memory.lean`) discharges the
   whole `Readers.MemoryAccess.Spec` from three event facts.
2. **The address.** `AddressOperation`'s four conjuncts — fits in 48 bits, above the reserved page,
   4-byte aligned, and `4 · offset_bit = addr mod 8` — come from `addr_eq` (the gadget's `ℕ` sum is
   the event's own `addr`) together with `MemoryEvent.WellFormed` and the row's `Aligned 4`.
3. **The sub-word selection.** The chip commits `offset_bit`, `selected_word` and `msb` as *input*
   columns, so the builder computes them: `offset_bit` is bit 2 of the address, `selected_word` the
   32-bit half it selects out of the RAM cell, and `msb` that half's top bit on an `LW` row (zero on
   `LWU`, which zero-extends). The four selection gates then hold by `rfl` in the selected branch
   and by `mul_zero` in the other.

## Why there is no padding row here

SP1 pads a chip's trace to a power-of-two height with literal zero bytes
(`load_word.rs`: `core::ptr::write_bytes(buffer[padding_start..], 0, padding_size)`), and the
chip's AIR is satisfied on such a row — the reserved-page inverse gate is
`inv · (value[1] + value[2]) = is_real`, which a zero row satisfies with `inv = 0`.

Its `ProverAssumptions`, however, states the address facts **ungated**, and one of them —
`2 ^ 16 ≤ (op_b_val + op_c_imm) mod 2^48`, the "address is above the reserved low 64 KiB" fact — is
*false* at the zero row. So no zero padding row satisfies this chip's honest-prover contract, and
the theorems below are stated over the event rows alone. The same conjunct appears, ungated, in all
five load chips and all four store chips, inherited from `AddressOperation.Assumptions`; gating it
(and its three neighbours) on `is_real` is a contract change that would re-open
`AddressOperation.completeness` and nine chip completeness proofs, so it is **reported, not
patched**. The register-adapter families are unaffected: their padding rows are proved in
`AddChip`/`AddiChip`/`UTypeChip`'s `proverAssumptions_padding`.
-/

namespace SP1Clean.TraceGen

variable {p : ℕ}

/-! ## The LoadWord row's committed sub-word columns

Three columns SP1's `LoadWordChip::event_to_row` computes from the address and the RAM cell. They
are *inputs* to the Clean circuit (not witnesses), so the builder has to produce them. -/

/-- Bit 2 of the effective address — SP1's `offset_bit` for a 4-byte load, selecting the low
(`0`) or high (`1`) 32-bit half of the 8-byte RAM cell. -/
def loadWordOffsetBit (addr : ℕ) : ℕ := addr % 8 / 4

/-- The `ℕ` value of the selected half's **high** u16 limb — the limb whose top bit an `LW` row
sign-extends. -/
def loadWordSelectedHigh (mem addr : ℕ) : ℕ :=
  if addr % 8 < 4 then mem / 2 ^ 16 % 2 ^ 16 else mem / 2 ^ 48 % 2 ^ 16

/-- The selected 32-bit half of the RAM cell, as the two committed u16 limbs `selected_word`. -/
def loadWordSelected (mem addr : ℕ) : fields 2 (ZMod p) :=
  if addr % 8 < 4 then
    #v[((mem % 2 ^ 16 : ℕ) : ZMod p), ((mem / 2 ^ 16 % 2 ^ 16 : ℕ) : ZMod p)]
  else
    #v[((mem / 2 ^ 32 % 2 ^ 16 : ℕ) : ZMod p), ((mem / 2 ^ 48 % 2 ^ 16 : ℕ) : ZMod p)]

/-- The `LoadWord` chip's committed input row for one event — a **real** row. The two selectors are
read off the event's opcode discriminant (`Opcode::LW = 31`, `Opcode::LWU = 34`), exactly as
`UType`'s `is_auipc` is. -/
def MemoryEvent.toLoadWordInputs (e : MemoryEvent) : LoadWordChip.Inputs (ZMod p) where
  is_lw := if e.opcode = 31 then 1 else 0
  is_lwu := if e.opcode = 31 then 0 else 1
  state := cpuStateCols e.clk e.pc
  adapter := iTypeReaderCols e.toITypeEvent
  memory_access := memoryAccessCols e.prevMem e.prevTsMem (e.clk + 1)
  offset_bit := ((loadWordOffsetBit e.addr : ℕ) : ZMod p)
  selected_word := loadWordSelected e.prevMem e.addr
  msb := if e.opcode = 31 ∧ 32768 ≤ loadWordSelectedHigh e.prevMem e.addr then 1 else 0

lemma MemoryEvent.toLoadWordInputs_state (e : MemoryEvent) :
    (e.toLoadWordInputs (p := p)).state = cpuStateCols e.clk e.pc := rfl

lemma MemoryEvent.toLoadWordInputs_adapter (e : MemoryEvent) :
    (e.toLoadWordInputs (p := p)).adapter = iTypeReaderCols e.toITypeEvent := rfl

lemma MemoryEvent.toLoadWordInputs_memory_access (e : MemoryEvent) :
    (e.toLoadWordInputs (p := p)).memory_access
      = memoryAccessCols e.prevMem e.prevTsMem (e.clk + 1) := rfl

lemma MemoryEvent.toLoadWordInputs_offset_bit (e : MemoryEvent) :
    (e.toLoadWordInputs (p := p)).offset_bit = ((loadWordOffsetBit e.addr : ℕ) : ZMod p) := rfl

lemma MemoryEvent.toLoadWordInputs_is_lw (e : MemoryEvent) :
    (e.toLoadWordInputs (p := p)).is_lw = if e.opcode = 31 then 1 else 0 := rfl

lemma MemoryEvent.toLoadWordInputs_is_lwu (e : MemoryEvent) :
    (e.toLoadWordInputs (p := p)).is_lwu = if e.opcode = 31 then 0 else 1 := rfl

lemma MemoryEvent.toLoadWordInputs_msb (e : MemoryEvent) :
    (e.toLoadWordInputs (p := p)).msb
      = if e.opcode = 31 ∧ 32768 ≤ loadWordSelectedHigh e.prevMem e.addr then 1 else 0 := rfl

lemma MemoryEvent.toLoadWordInputs_selected_word (e : MemoryEvent) :
    (e.toLoadWordInputs (p := p)).selected_word = loadWordSelected e.prevMem e.addr := rfl

end SP1Clean.TraceGen

namespace SP1Clean.LoadWordChip

open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## The chip's honest-prover contract on a built row -/

/--
**A well-formed, 4-byte-aligned memory trace event builds a row the honest prover can complete.**

`halign` is the per-instruction fact `MemoryEvent.WellFormed` cannot carry, for the same reason
`JTypeEvent.UTypeImm` is separate: the record is shared by the whole memory family, and `LB`/`LBU`
rows are not aligned at all.

The `data` and `hint` are arbitrary: `LoadWord`'s prover contract reads neither.
-/
theorem proverAssumptions_of_event {e : MemoryEvent} (h : e.WellFormed) (halign : e.Aligned 4)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ProverAssumptions (e.toLoadWordInputs (p := p)) data hint := by
  have hp : 2 ^ 24 < p := Fact.out
  have hi := h.toITypeWellFormed
  -- the address the `AddressOperation` gadget sees, in both spellings its contract uses
  have haddr64 : (Word.toNat (e.toLoadWordInputs (p := p)).op_b_val
      + Word.toNat (e.toLoadWordInputs (p := p)).op_c_imm) % 2 ^ 64 = e.addr := addr_eq hi.b_lt hi.imm_lt
  have haddr48 : (Word.toNat (e.toLoadWordInputs (p := p)).op_b_val
      + Word.toNat (e.toLoadWordInputs (p := p)).op_c_imm) % 2 ^ 48 = e.addr := by
    rw [← Nat.mod_mod_of_dvd _ (show (2 : ℕ) ^ 48 ∣ 2 ^ 64 from by norm_num), haddr64,
      Nat.mod_eq_of_lt h.addr_lt]
  have halign' : e.addr % 4 = 0 := halign
  -- the offset bit: `4 · offset_bit = addr mod 8`, and it is `0` or `1` because the row is aligned
  have hoff8 : 4 * loadWordOffsetBit e.addr = e.addr % 8 := by
    rw [loadWordOffsetBit]; omega
  have hoffval : (((loadWordOffsetBit e.addr : ℕ) : ZMod p)).val = loadWordOffsetBit e.addr := by
    rw [ZMod.val_natCast_of_lt (by rw [loadWordOffsetBit]; omega)]
  -- the selected half's high limb, and the branch-free facts about it
  have hselHigh_lt : loadWordSelectedHigh e.prevMem e.addr < 2 ^ 16 := by
    rw [loadWordSelectedHigh]; split <;> omega
  have hsw1 : (loadWordSelected (p := p) e.prevMem e.addr)[1]
      = ((loadWordSelectedHigh e.prevMem e.addr : ℕ) : ZMod p) := by
    rw [loadWordSelected, loadWordSelectedHigh]; split <;> rfl
  -- the two address branches, as one disjunction over the offset bit and the selected limbs
  have hsel : (((loadWordOffsetBit e.addr : ℕ) : ZMod p) = 0
        ∧ (loadWordSelected (p := p) e.prevMem e.addr)[0] = (wordOfNat (p := p) e.prevMem)[0]
        ∧ (loadWordSelected (p := p) e.prevMem e.addr)[1] = (wordOfNat (p := p) e.prevMem)[1])
      ∨ (((loadWordOffsetBit e.addr : ℕ) : ZMod p) = 1
        ∧ (loadWordSelected (p := p) e.prevMem e.addr)[0] = (wordOfNat (p := p) e.prevMem)[2]
        ∧ (loadWordSelected (p := p) e.prevMem e.addr)[1]
            = (wordOfNat (p := p) e.prevMem)[3]) := by
    by_cases hlow : e.addr % 8 < 4
    · refine Or.inl ⟨?_, ?_, ?_⟩
      · rw [loadWordOffsetBit, Nat.div_eq_of_lt hlow, Nat.cast_zero]
      · rw [loadWordSelected, if_pos hlow, wordOfNat_zero]; rfl
      · rw [loadWordSelected, if_pos hlow, wordOfNat_one]; rfl
    · refine Or.inr ⟨?_, ?_, ?_⟩
      · rw [loadWordOffsetBit, show e.addr % 8 / 4 = 1 from by omega, Nat.cast_one]
      · rw [loadWordSelected, if_neg hlow, wordOfNat_two]; rfl
      · rw [loadWordSelected, if_neg hlow, wordOfNat_three]; rfl
  refine ⟨wordOfNat_isU64 _, wordOfNat_isU64 _, ?_, ?_, ?_, ?_, wordOfNat_isU64 _, ?_, ?_, ?_,
    iTypeReaderCols_op_a_0_eq_zero hi.opA_ne_zero, ⟨?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_⟩,
    cpuState_spec e.clk e.pc hi.clk_mod _ _ _,
    memoryAccess_spec hi.clk_mod h.clk_lt h.prevTsMem_lt,
    iTypeReader_spec hi _ _ _ _ _ _ _ _⟩
  -- the address fits in 48 bits, is above the reserved page, and is 4-byte aligned
  · rw [haddr64]; exact h.addr_lt
  · rw [haddr48]; exact h.addr_ge
  · rw [haddr48]; exact halign'
  -- `4 · offset_bit = addr mod 8`
  · rw [MemoryEvent.toLoadWordInputs_offset_bit, hoffval, haddr48]; exact hoff8
  -- the two opcode selectors, and their sum
  · rw [MemoryEvent.toLoadWordInputs_is_lw]; split
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rw [MemoryEvent.toLoadWordInputs_is_lwu]; split
    · exact Or.inl rfl
    · exact Or.inr rfl
  · right
    show (e.toLoadWordInputs (p := p)).is_lw + (e.toLoadWordInputs (p := p)).is_lwu = 1
    rw [MemoryEvent.toLoadWordInputs_is_lw, MemoryEvent.toLoadWordInputs_is_lwu]
    split
    · rw [add_zero]
    · rw [zero_add]
  -- the four offset-selection gates: an equality in the selected branch, a zero factor in the other
  · rcases hsel with ⟨ho, hs0, -⟩ | ⟨ho, -, -⟩
    · show ((loadWordSelected (p := p) e.prevMem e.addr)[0] - (wordOfNat (p := p) e.prevMem)[0])
        * (((loadWordOffsetBit e.addr : ℕ) : ZMod p) - 1) = 0
      rw [hs0, sub_self, zero_mul]
    · show ((loadWordSelected (p := p) e.prevMem e.addr)[0] - (wordOfNat (p := p) e.prevMem)[0])
        * (((loadWordOffsetBit e.addr : ℕ) : ZMod p) - 1) = 0
      rw [ho, sub_self, mul_zero]
  · rcases hsel with ⟨ho, -, hs1⟩ | ⟨ho, -, -⟩
    · show ((loadWordSelected (p := p) e.prevMem e.addr)[1] - (wordOfNat (p := p) e.prevMem)[1])
        * (((loadWordOffsetBit e.addr : ℕ) : ZMod p) - 1) = 0
      rw [hs1, sub_self, zero_mul]
    · show ((loadWordSelected (p := p) e.prevMem e.addr)[1] - (wordOfNat (p := p) e.prevMem)[1])
        * (((loadWordOffsetBit e.addr : ℕ) : ZMod p) - 1) = 0
      rw [ho, sub_self, mul_zero]
  · rcases hsel with ⟨ho, -, -⟩ | ⟨-, hs0, -⟩
    · show ((loadWordSelected (p := p) e.prevMem e.addr)[0] - (wordOfNat (p := p) e.prevMem)[2])
        * ((loadWordOffsetBit e.addr : ℕ) : ZMod p) = 0
      rw [ho, mul_zero]
    · show ((loadWordSelected (p := p) e.prevMem e.addr)[0] - (wordOfNat (p := p) e.prevMem)[2])
        * ((loadWordOffsetBit e.addr : ℕ) : ZMod p) = 0
      rw [hs0, sub_self, zero_mul]
  · rcases hsel with ⟨ho, -, -⟩ | ⟨-, -, hs1⟩
    · show ((loadWordSelected (p := p) e.prevMem e.addr)[1] - (wordOfNat (p := p) e.prevMem)[3])
        * ((loadWordOffsetBit e.addr : ℕ) : ZMod p) = 0
      rw [ho, mul_zero]
    · show ((loadWordSelected (p := p) e.prevMem e.addr)[1] - (wordOfNat (p := p) e.prevMem)[3])
        * ((loadWordOffsetBit e.addr : ℕ) : ZMod p) = 0
      rw [hs1, sub_self, zero_mul]
  -- LWU zero-extends: the sign bit is built as `0` unless the row is an `LW`
  · show (e.toLoadWordInputs (p := p)).msb * ((e.toLoadWordInputs (p := p)).is_lw - 1) = 0
    rw [MemoryEvent.toLoadWordInputs_msb, MemoryEvent.toLoadWordInputs_is_lw]
    by_cases hop : e.opcode = 31
    · rw [if_pos hop, sub_self, mul_zero]
    · rw [if_neg hop, if_neg (by tauto), zero_mul]
  -- the MSB gadget: the bit is built from the selected high limb, and is binary either way
  · show (e.toLoadWordInputs (p := p)).msb = 0 ∨ (e.toLoadWordInputs (p := p)).msb = 1
    rw [MemoryEvent.toLoadWordInputs_msb]
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  · intro hlw
    have hop : e.opcode = 31 := by
      by_contra hne
      rw [MemoryEvent.toLoadWordInputs_is_lw, if_neg hne] at hlw
      exact zero_ne_one hlw
    show (if e.opcode = 31 ∧ 32768 ≤ loadWordSelectedHigh e.prevMem e.addr then (1 : ZMod p)
        else 0)
      = if 32768 ≤ ((loadWordSelected (p := p) e.prevMem e.addr)[1]).val then 1 else 0
    rw [hsw1, ZMod.val_natCast_of_lt (by omega)]
    by_cases hb : 32768 ≤ loadWordSelectedHigh e.prevMem e.addr
    · rw [if_pos ⟨hop, hb⟩, if_pos hb]
    · rw [if_neg (by tauto), if_neg hb]

/-! ## The built table -/

/-- The LoadWord chip as a flat-AIR component: one circuit, checked independently on each row.

A plain `def`, deliberately not an `abbrev` (see `AddChip.component` for the measurement). -/
def component : Air.Flat.Component (ZMod p) := ⟨circuit⟩

/-- The rows a trace builds: one input row per event. **No padding tail** — SP1 pads with zero
rows, and this chip's `ProverAssumptions` is not satisfied there (see the module docstring). -/
def traceInputs (events : List MemoryEvent) : List (Inputs (ZMod p)) :=
  events.map MemoryEvent.toLoadWordInputs

/-- Every row of a built trace satisfies the chip's honest-prover contract. -/
theorem proverAssumptions_of_mem_traceInputs {events : List MemoryEvent}
    (h : ∀ e ∈ events, e.WellFormed ∧ e.Aligned 4) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) events, ProverAssumptions input data hint := by
  intro input hin
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
  exact proverAssumptions_of_event (h e he).1 (h e he).2 data hint

/-- **A real trace builds a valid LoadWord table.** Every `assertZero` of the whole flattened chip
circuit — the address gadget's carry chain and metadata gates, the memory primitive's timestamp
comparison, the MSB gadget, the two readers, the register write, and the chip's own selection and
selector gates — evaluates to zero on every built row, and no static lookup is left unchecked. -/
theorem traceTable_constraints (events : List MemoryEvent) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ e ∈ events, e.WellFormed ∧ e.Aligned 4) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events) data hint).Constraints :=
  Air.Flat.Table.build_constraints _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

/-- The same table satisfies its **channel guarantees** — every message it pushes onto the State,
Memory, Program and Byte channels carries the payload its channel promises. -/
theorem traceTable_guarantees (events : List MemoryEvent) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ e ∈ events, e.WellFormed ∧ e.Aligned 4) :
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

end SP1Clean.LoadWordChip
