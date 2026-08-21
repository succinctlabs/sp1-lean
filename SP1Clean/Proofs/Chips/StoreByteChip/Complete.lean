import SP1Clean.FormalModel.TraceGen.Memory
import SP1Clean.Proofs.Chips.StoreByteChip.Witgen
import ToClean.Air.TableBuild

/-! # `SP1Clean.StoreByteChip` — from trace events to a valid AIR table

`SB` through the trace-generation chain (see `StoreWordChip/Complete.lean` for the store family's
programme note, including the `op_a`-is-a-read discipline and **why there is no padding row**).

The widest row of the family, and the only store with no alignment requirement — `SB` may target
any of the eight bytes of the RAM cell, so the row commits all three low address bits. Two things
are new against `StoreHalf`:

* **The byte split.** SP1 does not put a byte column on the memory bus; it splits the *selected u16
  limb* and the *stored register limb* into byte pairs with two inline `ByteOpcode.U8Range` pulls,
  and the row commits both low bytes. The builder commits the residues, so both `< 256` facts and
  both `· 256⁻¹` high-byte facts are computations, not demands on the trace (`highByte_eq`).
* **The increment.** Rather than a second four-way mux, the AIR adds a *signed delta* to the
  selected limb: `reg_lo - mem_lo` when address bit 0 selects the low byte, `256 · (reg_lo -
  mem_hi)` when it selects the high one. The builder therefore commits the delta as the difference
  of the merged limb and the old limb, which is what makes both branches of the identity hold.

Everything else is the shared sub-word substrate: the same `memLimbIndex` limb the loads read, the
same `storeLimb` merge, and the same `storeLimb_cases` four-way split serving both the `mem_limb`
selection gates and the read-modify-write gates.
-/

namespace SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## The byte split -/

/-- **A committed byte pair reassembles.** The high half of a u16 that a row commits as
`(value - low_byte) · 256⁻¹` is the value's own high byte — so the two `U8Range` bounds SP1's byte
bus checks are properties of the builder's residues, not facts the trace has to supply. -/
lemma highByte_eq (n : ℕ) :
    (((n : ℕ) : ZMod p) - ((n % 256 : ℕ) : ZMod p)) * (256 : ZMod p)⁻¹
      = ((n / 256 : ℕ) : ZMod p) := by
  have hcast : ((n : ℕ) : ZMod p)
      = ((n % 256 : ℕ) : ZMod p) + ((n / 256 : ℕ) : ZMod p) * 256 := by
    conv_lhs => rw [show n = n % 256 + n / 256 * 256 from by omega]
    push_cast
    ring
  rw [hcast, add_sub_cancel_left, mul_assoc, mul_inv_cancel₀ (val_256_ne_zero (p := p)), mul_one]

/-! ## The StoreByte row's committed columns -/

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- The u16 limb a `SB` row writes back: the old selected limb with the byte address bit 0 selects
replaced by `rs2`'s low byte. -/
def storeByteLimb (mem reg addr : ℕ) : ℕ :=
  if addr % 2 = 0 then memLimb mem addr / 256 * 256 + reg % 256
  else memLimb mem addr % 256 + reg % 256 * 256

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- The merged limb is a u16, in both byte positions. -/
lemma storeByteLimb_lt (mem reg addr : ℕ) : storeByteLimb mem reg addr < 2 ^ 16 := by
  have h := memLimb_lt mem addr
  rw [storeByteLimb]
  split <;> omega

/-- The `StoreByte` chip's committed input row for one event — a **real** row (`is_real = 1`). The
three offset bits are the address's low three bits (the same triple `LoadX0` commits); `mem_limb`
is the old selected u16 limb, `register_low_byte` and `mem_limb_low_byte` its and `rs2`'s low bytes,
`increment` the signed delta between the merged limb and the old one, and `store_value` the RAM cell
with that limb replaced. -/
def MemoryEvent.toStoreByteInputs (e : MemoryEvent) : StoreByteChip.Inputs (ZMod p) where
  is_real := 1
  state := cpuStateCols e.clk e.pc
  adapter := iTypeReaderCols e.toITypeEvent
  memory_access := memoryAccessCols e.prevMem e.prevTsMem (e.clk + 1)
  offset_bit := #v[((e.addr % 2 : ℕ) : ZMod p), ((memLimbIndex e.addr % 2 : ℕ) : ZMod p),
                   ((memLimbIndex e.addr / 2 : ℕ) : ZMod p)]
  mem_limb := ((memLimb e.prevMem e.addr : ℕ) : ZMod p)
  mem_limb_low_byte := ((memLimb e.prevMem e.addr % 256 : ℕ) : ZMod p)
  register_low_byte := ((e.prevA % 256 : ℕ) : ZMod p)
  increment := ((storeByteLimb e.prevMem e.prevA e.addr : ℕ) : ZMod p)
    - ((memLimb e.prevMem e.addr : ℕ) : ZMod p)
  store_value := storeLimb e.prevMem (storeByteLimb e.prevMem e.prevA e.addr) e.addr

omit [Fact (2 ^ 24 < p)] in
lemma MemoryEvent.toStoreByteInputs_offset_bit_zero (e : MemoryEvent) :
    (e.toStoreByteInputs (p := p)).offset_bit[0] = ((e.addr % 2 : ℕ) : ZMod p) := rfl

omit [Fact (2 ^ 24 < p)] in
lemma MemoryEvent.toStoreByteInputs_offset_bit_one (e : MemoryEvent) :
    (e.toStoreByteInputs (p := p)).offset_bit[1]
      = ((memLimbIndex e.addr % 2 : ℕ) : ZMod p) := rfl

omit [Fact (2 ^ 24 < p)] in
lemma MemoryEvent.toStoreByteInputs_offset_bit_two (e : MemoryEvent) :
    (e.toStoreByteInputs (p := p)).offset_bit[2]
      = ((memLimbIndex e.addr / 2 : ℕ) : ZMod p) := rfl

omit [Fact (2 ^ 24 < p)] in
lemma MemoryEvent.toStoreByteInputs_mem_limb (e : MemoryEvent) :
    (e.toStoreByteInputs (p := p)).mem_limb = ((memLimb e.prevMem e.addr : ℕ) : ZMod p) := rfl

omit [Fact (2 ^ 24 < p)] in
lemma MemoryEvent.toStoreByteInputs_mem_limb_low_byte (e : MemoryEvent) :
    (e.toStoreByteInputs (p := p)).mem_limb_low_byte
      = ((memLimb e.prevMem e.addr % 256 : ℕ) : ZMod p) := rfl

omit [Fact (2 ^ 24 < p)] in
lemma MemoryEvent.toStoreByteInputs_register_low_byte (e : MemoryEvent) :
    (e.toStoreByteInputs (p := p)).register_low_byte = ((e.prevA % 256 : ℕ) : ZMod p) := rfl

omit [Fact (2 ^ 24 < p)] in
lemma MemoryEvent.toStoreByteInputs_increment (e : MemoryEvent) :
    (e.toStoreByteInputs (p := p)).increment
      = ((storeByteLimb e.prevMem e.prevA e.addr : ℕ) : ZMod p)
        - ((memLimb e.prevMem e.addr : ℕ) : ZMod p) := rfl

omit [Fact (2 ^ 24 < p)] in
lemma MemoryEvent.toStoreByteInputs_store_value (e : MemoryEvent) :
    (e.toStoreByteInputs (p := p)).store_value
      = storeLimb e.prevMem (storeByteLimb e.prevMem e.prevA e.addr) e.addr := rfl

omit [Fact (2 ^ 24 < p)] in
lemma MemoryEvent.toStoreByteInputs_prev_value (e : MemoryEvent) :
    (e.toStoreByteInputs (p := p)).memory_access.prev_value = wordOfNat e.prevMem := rfl

omit [Fact (2 ^ 24 < p)] in
lemma MemoryEvent.toStoreByteInputs_op_a_value (e : MemoryEvent) :
    (e.toStoreByteInputs (p := p)).adapter.op_a_memory.prev_value = wordOfNat e.prevA := rfl

end SP1Clean.TraceGen

namespace SP1Clean.StoreByteChip

open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## The chip's honest-prover contract on a built row -/

/-- **A well-formed store trace event builds a row the honest prover can complete.** No alignment
hypothesis: `SB` is the one memory instruction RISC-V lets target any byte. -/
theorem proverAssumptions_of_event {e : MemoryEvent} (h : e.WellFormedStore)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ProverAssumptions (e.toStoreByteInputs (p := p)) data hint := by
  have hp : 2 ^ 24 < p := Fact.out
  have haddr64 : (Word.toNat (e.toStoreByteInputs (p := p)).op_b_val
      + Word.toNat (e.toStoreByteInputs (p := p)).op_c_imm) % 2 ^ 64 = e.addr :=
    addr_eq h.b_lt h.imm_lt
  have haddr48 : (Word.toNat (e.toStoreByteInputs (p := p)).op_b_val
      + Word.toNat (e.toStoreByteInputs (p := p)).op_c_imm) % 2 ^ 48 = e.addr := by
    rw [← Nat.mod_mod_of_dvd _ (show (2 : ℕ) ^ 48 ∣ 2 ^ 64 from by norm_num), haddr64,
      Nat.mod_eq_of_lt h.addr_lt]
  have hidx : memLimbIndex e.addr < 4 := memLimbIndex_lt _
  have hmemlt : memLimb e.prevMem e.addr < 2 ^ 16 := memLimb_lt _ _
  -- the old limb's byte split, as a field identity
  have hmemcast : ((memLimb e.prevMem e.addr : ℕ) : ZMod p)
      = ((memLimb e.prevMem e.addr % 256 : ℕ) : ZMod p)
        + ((memLimb e.prevMem e.addr / 256 : ℕ) : ZMod p) * 256 := by
    conv_lhs => rw [show memLimb e.prevMem e.addr
      = memLimb e.prevMem e.addr % 256 + memLimb e.prevMem e.addr / 256 * 256 from by omega]
    push_cast
    ring
  -- the four address branches: the offset bits, the old selected limb, and the merged word
  have hcases := storeLimb_cases (p := p) e.prevMem (storeByteLimb e.prevMem e.prevA e.addr) e.addr
  simp only [wordOfNat_zero, wordOfNat_one, wordOfNat_two, wordOfNat_three] at hcases
  refine ⟨wordOfNat_isU64 _, wordOfNat_isU64 _, ?_, ?_, ?_, ?_, ?_, ?_, Or.inr rfl,
    ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_⟩,
    cpuState_spec e.clk e.pc h.clk_mod _ _ _,
    memoryAccess_spec h.clk_mod h.clk_lt h.prevTsMem_lt,
    iTypeReaderImmutable_spec h.clk_mod h.opA_lt h.prevA_x0 h.prevTsA_lt h.prevTsB_lt _ _ _ _,
    fun _ => ⟨iTypeReaderCols_op_a_val_lt h.opA_lt, (cpuStateCols_pc_val_lt e.clk e.pc).1,
      (cpuStateCols_pc_val_lt e.clk e.pc).2.1, (cpuStateCols_pc_val_lt e.clk e.pc).2.2⟩,
    fun _ => storeLimb_isU64 _ _ (storeByteLimb_lt _ _ _)⟩
  -- the address fits in 48 bits and is above the reserved page (a byte store has no alignment)
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
  -- the four byte bounds: the two committed low bytes and the two derived high bytes
  · show (((e.prevA % 256 : ℕ) : ZMod p)).val < 256
    rw [ZMod.val_natCast_of_lt (by omega)]; omega
  · show ((((wordOfNat (p := p) e.prevA)[0] - ((e.prevA % 256 : ℕ) : ZMod p))
      * (256 : ZMod p)⁻¹)).val < 256
    rw [wordOfNat_zero, show e.prevA % 256 = e.prevA % 2 ^ 16 % 256 from by omega,
      highByte_eq, ZMod.val_natCast_of_lt (by omega)]
    omega
  · show (((memLimb e.prevMem e.addr % 256 : ℕ) : ZMod p)).val < 256
    rw [ZMod.val_natCast_of_lt (by omega)]; omega
  · show ((((memLimb e.prevMem e.addr : ℕ) : ZMod p)
      - ((memLimb e.prevMem e.addr % 256 : ℕ) : ZMod p)) * (256 : ZMod p)⁻¹).val < 256
    rw [highByte_eq, ZMod.val_natCast_of_lt (by omega)]
    omega
  -- the four `mem_limb` selection gates: the committed limb *is* the selected one
  · simp only [MemoryEvent.toStoreByteInputs_mem_limb, MemoryEvent.toStoreByteInputs_prev_value,
      MemoryEvent.toStoreByteInputs_offset_bit_one, MemoryEvent.toStoreByteInputs_offset_bit_two,
      wordOfNat_zero]
    rcases hcases with ⟨h1, h2, hml, -, -, -, -⟩ | ⟨h1, h2, hml, -, -, -, -⟩
      | ⟨h1, h2, hml, -, -, -, -⟩ | ⟨h1, h2, hml, -, -, -, -⟩ <;> rw [h1, h2] <;>
      first
        | linear_combination hml
        | linear_combination -hml
        | linear_combination
  · simp only [MemoryEvent.toStoreByteInputs_mem_limb, MemoryEvent.toStoreByteInputs_prev_value,
      MemoryEvent.toStoreByteInputs_offset_bit_one, MemoryEvent.toStoreByteInputs_offset_bit_two,
      wordOfNat_one]
    rcases hcases with ⟨h1, h2, hml, -, -, -, -⟩ | ⟨h1, h2, hml, -, -, -, -⟩
      | ⟨h1, h2, hml, -, -, -, -⟩ | ⟨h1, h2, hml, -, -, -, -⟩ <;> rw [h1, h2] <;>
      first
        | linear_combination hml
        | linear_combination -hml
        | linear_combination
  · simp only [MemoryEvent.toStoreByteInputs_mem_limb, MemoryEvent.toStoreByteInputs_prev_value,
      MemoryEvent.toStoreByteInputs_offset_bit_one, MemoryEvent.toStoreByteInputs_offset_bit_two,
      wordOfNat_two]
    rcases hcases with ⟨h1, h2, hml, -, -, -, -⟩ | ⟨h1, h2, hml, -, -, -, -⟩
      | ⟨h1, h2, hml, -, -, -, -⟩ | ⟨h1, h2, hml, -, -, -, -⟩ <;> rw [h1, h2] <;>
      first
        | linear_combination hml
        | linear_combination -hml
        | linear_combination
  · simp only [MemoryEvent.toStoreByteInputs_mem_limb, MemoryEvent.toStoreByteInputs_prev_value,
      MemoryEvent.toStoreByteInputs_offset_bit_one, MemoryEvent.toStoreByteInputs_offset_bit_two,
      wordOfNat_three]
    rcases hcases with ⟨h1, h2, hml, -, -, -, -⟩ | ⟨h1, h2, hml, -, -, -, -⟩
      | ⟨h1, h2, hml, -, -, -, -⟩ | ⟨h1, h2, hml, -, -, -, -⟩ <;> rw [h1, h2] <;>
      first
        | linear_combination hml
        | linear_combination -hml
        | linear_combination
  -- the increment identity: the delta the selected byte contributes, in both byte positions
  · simp only [MemoryEvent.toStoreByteInputs_increment,
      MemoryEvent.toStoreByteInputs_register_low_byte, MemoryEvent.toStoreByteInputs_mem_limb,
      MemoryEvent.toStoreByteInputs_mem_limb_low_byte,
      MemoryEvent.toStoreByteInputs_offset_bit_zero, highByte_eq]
    rcases (by omega : e.addr % 2 = 0 ∨ e.addr % 2 = 1) with hb | hb
    · rw [show ((e.addr % 2 : ℕ) : ZMod p) = 0 from by rw [hb, Nat.cast_zero],
        storeByteLimb, if_pos hb]
      push_cast
      linear_combination - hmemcast
    · rw [show ((e.addr % 2 : ℕ) : ZMod p) = 1 from by rw [hb, Nat.cast_one],
        storeByteLimb, if_neg (by omega)]
      push_cast
      linear_combination - hmemcast
  -- the four read-modify-write gates: the selected limb takes the increment, the others are kept
  · simp only [MemoryEvent.toStoreByteInputs_store_value, MemoryEvent.toStoreByteInputs_prev_value,
      MemoryEvent.toStoreByteInputs_increment,
      MemoryEvent.toStoreByteInputs_offset_bit_one, MemoryEvent.toStoreByteInputs_offset_bit_two,
      wordOfNat_zero]
    rcases hcases with ⟨h1, h2, hml, hs, -, -, -⟩ | ⟨h1, h2, hml, hs, -, -, -⟩
      | ⟨h1, h2, hml, hs, -, -, -⟩ | ⟨h1, h2, hml, hs, -, -, -⟩ <;> rw [h1, h2] <;>
      first
        | linear_combination hs
        | linear_combination hs + hml
  · simp only [MemoryEvent.toStoreByteInputs_store_value, MemoryEvent.toStoreByteInputs_prev_value,
      MemoryEvent.toStoreByteInputs_increment,
      MemoryEvent.toStoreByteInputs_offset_bit_one, MemoryEvent.toStoreByteInputs_offset_bit_two,
      wordOfNat_one]
    rcases hcases with ⟨h1, h2, hml, -, hs, -, -⟩ | ⟨h1, h2, hml, -, hs, -, -⟩
      | ⟨h1, h2, hml, -, hs, -, -⟩ | ⟨h1, h2, hml, -, hs, -, -⟩ <;> rw [h1, h2] <;>
      first
        | linear_combination hs
        | linear_combination hs + hml
  · simp only [MemoryEvent.toStoreByteInputs_store_value, MemoryEvent.toStoreByteInputs_prev_value,
      MemoryEvent.toStoreByteInputs_increment,
      MemoryEvent.toStoreByteInputs_offset_bit_one, MemoryEvent.toStoreByteInputs_offset_bit_two,
      wordOfNat_two]
    rcases hcases with ⟨h1, h2, hml, -, -, hs, -⟩ | ⟨h1, h2, hml, -, -, hs, -⟩
      | ⟨h1, h2, hml, -, -, hs, -⟩ | ⟨h1, h2, hml, -, -, hs, -⟩ <;> rw [h1, h2] <;>
      first
        | linear_combination hs
        | linear_combination hs + hml
  · simp only [MemoryEvent.toStoreByteInputs_store_value, MemoryEvent.toStoreByteInputs_prev_value,
      MemoryEvent.toStoreByteInputs_increment,
      MemoryEvent.toStoreByteInputs_offset_bit_one, MemoryEvent.toStoreByteInputs_offset_bit_two,
      wordOfNat_three]
    rcases hcases with ⟨h1, h2, hml, -, -, -, hs⟩ | ⟨h1, h2, hml, -, -, -, hs⟩
      | ⟨h1, h2, hml, -, -, -, hs⟩ | ⟨h1, h2, hml, -, -, -, hs⟩ <;> rw [h1, h2] <;>
      first
        | linear_combination hs
        | linear_combination hs + hml

/-! ## The built table -/

/-- The StoreByte chip as a flat-AIR component: one circuit, checked independently on each row.

A plain `def`, deliberately not an `abbrev` (see `AddChip.component` for the measurement). -/
def component : Air.Flat.Component (ZMod p) := ⟨circuit⟩

/-- The rows a trace builds: one input row per event. **No padding tail** — see
`StoreWordChip/Complete.lean`. -/
def traceInputs (events : List MemoryEvent) : List (Inputs (ZMod p)) :=
  events.map MemoryEvent.toStoreByteInputs

/-- Every row of a built trace satisfies the chip's honest-prover contract. -/
theorem proverAssumptions_of_mem_traceInputs {events : List MemoryEvent}
    (h : ∀ e ∈ events, e.WellFormedStore) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) events, ProverAssumptions input data hint := by
  intro input hin
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
  exact proverAssumptions_of_event (h e he) data hint

/-- **A real trace builds a valid StoreByte table.** -/
theorem traceTable_constraints (events : List MemoryEvent) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ e ∈ events, e.WellFormedStore) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events) data hint).Constraints :=
  Air.Flat.Table.build_constraints _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

/-- The same table satisfies its **channel guarantees** — including the two inline byte-bus pulls,
whose payloads are the committed byte splits. -/
theorem traceTable_guarantees (events : List MemoryEvent) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ e ∈ events, e.WellFormedStore) :
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

end SP1Clean.StoreByteChip
