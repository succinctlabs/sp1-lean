import SP1Clean.FormalModel.TraceGen.Memory
import SP1Clean.Proofs.Chips.LoadByteChip.Witgen
import ToClean.Air.TableBuild

/-! # `SP1Clean.LoadByteChip` — from trace events to a valid AIR table

`LB` through the trace-generation chain (see `LoadWordChip/Complete.lean` for the memory-family
programme note, including **why there is no padding row**). A byte load reuses the family's u16
limb selection (`memLimb_cases`) and then splits the selected limb with address bit 0, so the row
commits three offset bits, the limb, its low byte, the selected byte, and the sign bit — all of
them *input* columns, all of them built here.

## Why `LBU` rows are excluded

`LoadByteChip.ProverAssumptions` states the sign-bit fact **ungated**:

    (input.msb = 0 ∨ input.msb = 1) ∧ (input.msb = 1 ↔ 128 ≤ input.selected_byte.val) ∧
    input.is_lbu * input.msb = 0

On an `LBU` row that loads a byte `≥ 128` those two conjuncts are contradictory — the `↔` forces
`msb = 1` and the gate forces `msb = 0` — so **no row at all** satisfies the contract there, and
this chip's completeness is vacuous for that (perfectly ordinary) class of real rows.

The circuit is fine: SP1's AIR range-checks `msb` through a byte pull gated by `is_lb`
(`load_byte.rs`: `builder.when(local.is_lb).send_byte(MSB, …)`), and its `populate` sets
`cols.msb = byte >> 7` on an `LB` row and `cols.msb = 0` on an `LBU` row — which is exactly what
`MemoryEvent.toLoadByteInputs` builds. The chip's *soundness* proof also derives the sign-bit fact
only under `is_lb = 1` (`h_msb_fact` in `Formal.lean`). It is the `ProverAssumptions` statement
that is missing that gate, and gating it is a contract change, so this file is **scoped to `LB`
rows and reports the gap** rather than patching it.
-/

namespace SP1Clean.TraceGen

variable {p : ℕ}

/-- The byte an `LB`/`LBU` row selects out of its u16 limb: the low byte at an even address, the
high byte at an odd one (`offset_bit[0]` is address bit 0). -/
def loadByteSelected (mem addr : ℕ) : ℕ :=
  if addr % 2 = 0 then memLimb mem addr % 256 else memLimb mem addr / 256

/-- The `LoadByte` chip's committed input row for one event — a **real** row. The two selectors are
read off the event's opcode discriminant (`Opcode::LB = 29`, `Opcode::LBU = 32`), and the sign bit
is `byte >> 7` on an `LB` row and `0` on an `LBU` row, matching `load_byte.rs`'s two populate
branches. -/
def MemoryEvent.toLoadByteInputs (e : MemoryEvent) : LoadByteChip.Inputs (ZMod p) where
  is_lb := if e.opcode = 29 then 1 else 0
  is_lbu := if e.opcode = 29 then 0 else 1
  state := cpuStateCols e.clk e.pc
  adapter := iTypeReaderCols e.toITypeEvent
  memory_access := memoryAccessCols e.prevMem e.prevTsMem (e.clk + 1)
  offset_bit := #v[((e.addr % 2 : ℕ) : ZMod p), ((memLimbIndex e.addr % 2 : ℕ) : ZMod p),
                   ((memLimbIndex e.addr / 2 : ℕ) : ZMod p)]
  selected_limb := ((memLimb e.prevMem e.addr : ℕ) : ZMod p)
  selected_limb_low_byte := ((memLimb e.prevMem e.addr % 256 : ℕ) : ZMod p)
  selected_byte := ((loadByteSelected e.prevMem e.addr : ℕ) : ZMod p)
  msb := if e.opcode = 29 ∧ 128 ≤ loadByteSelected e.prevMem e.addr then 1 else 0

lemma MemoryEvent.toLoadByteInputs_offset_bit_zero (e : MemoryEvent) :
    (e.toLoadByteInputs (p := p)).offset_bit[0] = ((e.addr % 2 : ℕ) : ZMod p) := rfl

lemma MemoryEvent.toLoadByteInputs_offset_bit_one (e : MemoryEvent) :
    (e.toLoadByteInputs (p := p)).offset_bit[1]
      = ((memLimbIndex e.addr % 2 : ℕ) : ZMod p) := rfl

lemma MemoryEvent.toLoadByteInputs_offset_bit_two (e : MemoryEvent) :
    (e.toLoadByteInputs (p := p)).offset_bit[2]
      = ((memLimbIndex e.addr / 2 : ℕ) : ZMod p) := rfl

lemma MemoryEvent.toLoadByteInputs_selected_limb (e : MemoryEvent) :
    (e.toLoadByteInputs (p := p)).selected_limb
      = ((memLimb e.prevMem e.addr : ℕ) : ZMod p) := rfl

lemma MemoryEvent.toLoadByteInputs_low_byte (e : MemoryEvent) :
    (e.toLoadByteInputs (p := p)).selected_limb_low_byte
      = ((memLimb e.prevMem e.addr % 256 : ℕ) : ZMod p) := rfl

lemma MemoryEvent.toLoadByteInputs_selected_byte (e : MemoryEvent) :
    (e.toLoadByteInputs (p := p)).selected_byte
      = ((loadByteSelected e.prevMem e.addr : ℕ) : ZMod p) := rfl

lemma MemoryEvent.toLoadByteInputs_prev_value (e : MemoryEvent) :
    (e.toLoadByteInputs (p := p)).memory_access.prev_value = wordOfNat e.prevMem := rfl

lemma MemoryEvent.toLoadByteInputs_is_lb (e : MemoryEvent) :
    (e.toLoadByteInputs (p := p)).is_lb = if e.opcode = 29 then 1 else 0 := rfl

lemma MemoryEvent.toLoadByteInputs_is_lbu (e : MemoryEvent) :
    (e.toLoadByteInputs (p := p)).is_lbu = if e.opcode = 29 then 0 else 1 := rfl

lemma MemoryEvent.toLoadByteInputs_msb (e : MemoryEvent) :
    (e.toLoadByteInputs (p := p)).msb
      = if e.opcode = 29 ∧ 128 ≤ loadByteSelected e.prevMem e.addr then 1 else 0 := rfl

end SP1Clean.TraceGen

namespace SP1Clean.LoadByteChip

open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## The chip's honest-prover contract on a built row -/

/-- **A well-formed `LB` trace event builds a row the honest prover can complete.** A byte load
needs no alignment; `hlb` restricts the theorem to the signed variant, for the contract reason in
the module docstring, not for any reason coming from the trace. -/
theorem proverAssumptions_of_event {e : MemoryEvent} (h : e.WellFormed) (hlb : e.opcode = 29)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ProverAssumptions (e.toLoadByteInputs (p := p)) data hint := by
  have hp : 2 ^ 24 < p := Fact.out
  have hi := h.toITypeWellFormed
  have haddr64 : (Word.toNat (e.toLoadByteInputs (p := p)).op_b_val
      + Word.toNat (e.toLoadByteInputs (p := p)).op_c_imm) % 2 ^ 64 = e.addr := addr_eq hi.b_lt hi.imm_lt
  have haddr48 : (Word.toNat (e.toLoadByteInputs (p := p)).op_b_val
      + Word.toNat (e.toLoadByteInputs (p := p)).op_c_imm) % 2 ^ 48 = e.addr := by
    rw [← Nat.mod_mod_of_dvd _ (show (2 : ℕ) ^ 48 ∣ 2 ^ 64 from by norm_num), haddr64,
      Nat.mod_eq_of_lt h.addr_lt]
  have hlimb_lt : memLimb e.prevMem e.addr < 2 ^ 16 := memLimb_lt _ _
  have hbyte_lt : loadByteSelected e.prevMem e.addr < 256 := by
    rw [loadByteSelected]; split <;> omega
  have hidx : memLimbIndex e.addr < 4 := memLimbIndex_lt _
  have hsel := memLimb_cases (p := p) e.prevMem e.addr
  -- the sub-limb high byte the AIR forms as `(selected_limb - low_byte) · 256⁻¹`
  have hcast : ((memLimb e.prevMem e.addr : ℕ) : ZMod p)
      = ((memLimb e.prevMem e.addr % 256 : ℕ) : ZMod p)
        + ((memLimb e.prevMem e.addr / 256 : ℕ) : ZMod p) * 256 := by
    conv_lhs => rw [show memLimb e.prevMem e.addr
      = memLimb e.prevMem e.addr % 256 + memLimb e.prevMem e.addr / 256 * 256 from by omega]
    push_cast
    ring
  have hhigh : highByte (e.toLoadByteInputs (p := p))
      = ((memLimb e.prevMem e.addr / 256 : ℕ) : ZMod p) := by
    simp only [highByte, MemoryEvent.toLoadByteInputs_selected_limb,
      MemoryEvent.toLoadByteInputs_low_byte]
    rw [hcast, add_sub_cancel_left, mul_assoc, mul_inv_cancel₀ val_256_ne_zero, mul_one]
  refine ⟨wordOfNat_isU64 _, wordOfNat_isU64 _, ?_, ?_, ?_, ?_, ?_, ?_, wordOfNat_isU64 _,
    ?_, ?_, ?_, iTypeReaderCols_op_a_0_eq_zero hi.opA_ne_zero, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨?_, ?_, ?_, ?_⟩, ?_,
    cpuState_spec e.clk e.pc hi.clk_mod _ _ _,
    memoryAccess_spec hi.clk_mod h.clk_lt h.prevTsMem_lt,
    iTypeReader_spec hi _ _ _ _ _ _ _ _⟩
  -- the address fits in 48 bits and is above the reserved page (a byte load needs no alignment)
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
  · rcases hsel with ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
    · exact Or.inl h0
    · exact Or.inr h0
    · exact Or.inl h0
    · exact Or.inr h0
  · rcases hsel with ⟨-, h1, -⟩ | ⟨-, h1, -⟩ | ⟨-, h1, -⟩ | ⟨-, h1, -⟩
    · exact Or.inl h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exact Or.inr h1
  -- the two opcode selectors, and their sum
  · rw [MemoryEvent.toLoadByteInputs_is_lb, if_pos hlb]; exact Or.inr rfl
  · rw [MemoryEvent.toLoadByteInputs_is_lbu, if_pos hlb]; exact Or.inl rfl
  · right
    show (e.toLoadByteInputs (p := p)).is_lb + (e.toLoadByteInputs (p := p)).is_lbu = 1
    rw [MemoryEvent.toLoadByteInputs_is_lb, MemoryEvent.toLoadByteInputs_is_lbu, if_pos hlb,
      if_pos hlb, add_zero]
  -- the three byte-valued columns
  · show (((memLimb e.prevMem e.addr % 256 : ℕ) : ZMod p)).val < 256
    rw [ZMod.val_natCast_of_lt (by omega)]; omega
  · rw [hhigh, ZMod.val_natCast_of_lt (by omega)]; omega
  · show (((loadByteSelected e.prevMem e.addr : ℕ) : ZMod p)).val < 256
    rw [ZMod.val_natCast_of_lt (by omega)]; omega
  -- the sign bit: binary, and the high bit of the selected byte on this (`LB`) row
  · show (e.toLoadByteInputs (p := p)).msb = 0 ∨ (e.toLoadByteInputs (p := p)).msb = 1
    rw [MemoryEvent.toLoadByteInputs_msb]
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  · show (e.toLoadByteInputs (p := p)).msb = 1
      ↔ 128 ≤ (((loadByteSelected e.prevMem e.addr : ℕ) : ZMod p)).val
    rw [MemoryEvent.toLoadByteInputs_msb, ZMod.val_natCast_of_lt (by omega)]
    by_cases hb : 128 ≤ loadByteSelected e.prevMem e.addr
    · rw [if_pos ⟨hlb, hb⟩]
      exact ⟨fun _ => hb, fun _ => rfl⟩
    · rw [if_neg (by tauto)]
      exact ⟨fun hz => absurd hz zero_ne_one, fun hc => absurd hc hb⟩
  -- `LBU` would zero the sign bit; this row is an `LB`, so the gate's other factor is zero
  · show (e.toLoadByteInputs (p := p)).is_lbu * (e.toLoadByteInputs (p := p)).msb = 0
    rw [MemoryEvent.toLoadByteInputs_is_lbu, if_pos hlb, zero_mul]
  -- the four limb-selection gates
  · rcases hsel with ⟨h0, h1, hs⟩ | ⟨h0, h1, hs⟩ | ⟨h0, h1, hs⟩ | ⟨h0, h1, hs⟩ <;>
      simp only [MemoryEvent.toLoadByteInputs_offset_bit_one,
        MemoryEvent.toLoadByteInputs_offset_bit_two, MemoryEvent.toLoadByteInputs_selected_limb,
        MemoryEvent.toLoadByteInputs_prev_value, Nat.cast_one, h0, h1, hs, sub_self, mul_zero,
        zero_mul]
  · rcases hsel with ⟨h0, h1, hs⟩ | ⟨h0, h1, hs⟩ | ⟨h0, h1, hs⟩ | ⟨h0, h1, hs⟩ <;>
      simp only [MemoryEvent.toLoadByteInputs_offset_bit_one,
        MemoryEvent.toLoadByteInputs_offset_bit_two, MemoryEvent.toLoadByteInputs_selected_limb,
        MemoryEvent.toLoadByteInputs_prev_value, h0, h1, hs, sub_self, mul_zero, zero_mul]
  · rcases hsel with ⟨h0, h1, hs⟩ | ⟨h0, h1, hs⟩ | ⟨h0, h1, hs⟩ | ⟨h0, h1, hs⟩ <;>
      simp only [MemoryEvent.toLoadByteInputs_offset_bit_one,
        MemoryEvent.toLoadByteInputs_offset_bit_two, MemoryEvent.toLoadByteInputs_selected_limb,
        MemoryEvent.toLoadByteInputs_prev_value, Nat.cast_one, h0, h1, hs, sub_self, mul_zero,
        zero_mul]
  · rcases hsel with ⟨h0, h1, hs⟩ | ⟨h0, h1, hs⟩ | ⟨h0, h1, hs⟩ | ⟨h0, h1, hs⟩ <;>
      simp only [MemoryEvent.toLoadByteInputs_offset_bit_one,
        MemoryEvent.toLoadByteInputs_offset_bit_two, MemoryEvent.toLoadByteInputs_selected_limb,
        MemoryEvent.toLoadByteInputs_prev_value, h0, h1, hs, sub_self, mul_zero, zero_mul]
  -- the byte mux: address bit 0 picks the limb's high byte, its complement the low byte
  · show (e.toLoadByteInputs (p := p)).selected_byte
      = (e.toLoadByteInputs (p := p)).offset_bit[0] * highByte (e.toLoadByteInputs (p := p))
        + (1 - (e.toLoadByteInputs (p := p)).offset_bit[0])
          * (e.toLoadByteInputs (p := p)).selected_limb_low_byte
    rw [MemoryEvent.toLoadByteInputs_selected_byte, MemoryEvent.toLoadByteInputs_offset_bit_zero,
      MemoryEvent.toLoadByteInputs_low_byte, hhigh, loadByteSelected]
    by_cases hb : e.addr % 2 = 0
    · rw [if_pos hb, hb, Nat.cast_zero, zero_mul, zero_add, sub_zero, Nat.cast_one, one_mul]
    · rw [if_neg hb, show e.addr % 2 = 1 from by omega, Nat.cast_one, one_mul, sub_self, zero_mul,
        add_zero]

/-! ## The built table -/

/-- The LoadByte chip as a flat-AIR component: one circuit, checked independently on each row.

A plain `def`, deliberately not an `abbrev` (see `AddChip.component` for the measurement). -/
def component : Air.Flat.Component (ZMod p) := ⟨circuit⟩

/-- The rows a trace builds: one input row per event. **No padding tail**, and **`LB` rows only** —
see the module docstring for both. -/
def traceInputs (events : List MemoryEvent) : List (Inputs (ZMod p)) :=
  events.map MemoryEvent.toLoadByteInputs

/-- Every row of a built trace satisfies the chip's honest-prover contract. -/
theorem proverAssumptions_of_mem_traceInputs {events : List MemoryEvent}
    (h : ∀ e ∈ events, e.WellFormed ∧ e.opcode = 29) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) events, ProverAssumptions input data hint := by
  intro input hin
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
  exact proverAssumptions_of_event (h e he).1 (h e he).2 data hint

/-- **A real `LB` trace builds a valid LoadByte table.** -/
theorem traceTable_constraints (events : List MemoryEvent) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ e ∈ events, e.WellFormed ∧ e.opcode = 29) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events) data hint).Constraints :=
  Air.Flat.Table.build_constraints _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

/-- The same table satisfies its **channel guarantees**. -/
theorem traceTable_guarantees (events : List MemoryEvent) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ e ∈ events, e.WellFormed ∧ e.opcode = 29) :
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

end SP1Clean.LoadByteChip
