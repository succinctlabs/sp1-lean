import SP1Clean.FormalModel.TraceGen.Readers
import SP1Clean.Proofs.Chips.DivRemChip.Witgen
import ToClean.Air.TableBuild

/-! # `SP1Clean.DivRemChip` — from trace events to a valid AIR table

`DIV`/`DIVU`/`REM`/`REMU` and their four word forms through the trace-generation chain — the last
chip of the rollout, and `MulChip/Complete.lean`'s contract with eight variant flags instead of
five. See `AddChip/Complete.lean` for the programme note (this chip threads the very same R-type
register block) and `BitwiseChip/Complete.lean` for why a multi-opcode chip's hint is per row.

Two things are this chip's own.

**The flags are seven-plus-one, and the eighth is derived.** The `"div_rem_flags"` key carries the
*other seven* selectors and `is_divu` is whatever is left over, `1 - Σ(the seven)`
(`DivRemChip.hintFlags`). The consequence is that the one-hot **sum** is an identity
(`Populate.hintFlags_sum_eq_one`) rather than a prover assumption — so, unlike every other
hint-gated chip in the rollout, `ProverAssumptions` does not ask for it and this file does not
prove it. What the builder owes is the eight binary facts, and — the load-bearing part —
`hintFlags_toDivRemHint`: the eight slots the chip reads back are exactly the selectors of **this
event's own opcode**. That equation needs the routing condition, precisely because of the derived
slot: `1 - Σ(the seven) = 1` says "DIVU" only for an event whose opcode is one of the eight.
`divRemFlags_opcode_eq` is the check that those selectors name the event's instruction: weighted by
the chip's own reader opcode (`DivRemContract.encodedOpcode`'s eight coefficients) they recombine to
the event's opcode discriminant.

**Padding is not a zero row.** SP1's `DivRemChip::generate_trace_into` fills its padded rows with
the concrete "0 divided by 1" `DIVU` template rather than zeros (`alu/divrem/mod.rs:549-569`:
`is_divu = 1`, `op_c_memory.prev_value = Word::from(1)`, and the live columns derived from that —
SP1's own comment calls them "fake rows that don't fail on some sanity checks", the sanity check in
question being the divisor a blank row would present). `DivRemChip.ProverAssumptions` pins exactly
that template through its `is_real = 0` conjunct — that is what makes the chip's *ungated* lower
glue and its flag-gated shape asserts dischargeable off-gate — and `divRemPaddingInputs` is it: the
R-type block with `op_c`'s **read value** the word `1`, everything else zero, at the empty hint,
whose derived slot reads back as `is_divu = 1` with no special case
(`Populate.hintFlags_absent`). -/

namespace SP1Clean.TraceGen

variable {p : ℕ}

/-- The seven hinted variant selectors of a `DivRem` row, in the key's own order
(`[div, rem, remu, divw, remw, divuw, remuw]` — `is_divu` is *not* among them, the chip derives it
as `1 - Σ`), read off the executor's opcode discriminant (`Opcode::{DIV, REM, REMU} = 15, 17, 18`
and `{DIVW, REMW, DIVUW, REMUW} = 25, 27, 26, 28`). -/
def divRemHintFlags (opcode : ℕ) : Vector (ZMod p) 7 :=
  #v[if opcode = 15 then 1 else 0, if opcode = 17 then 1 else 0, if opcode = 18 then 1 else 0,
     if opcode = 25 then 1 else 0, if opcode = 27 then 1 else 0, if opcode = 26 then 1 else 0,
     if opcode = 28 then 1 else 0]

/-- The eight variant selectors the chip reads back, in its own column order (`is_div`, `is_divu`,
`is_rem`, `is_remu`, `is_divw`, `is_remw`, `is_divuw`, `is_remuw`) — the seven hinted ones with
`Opcode::DIVU = 16` restored in slot 1. These are the numbers the chip threads into its reader as
`is_divu·16 + is_remu·18 + is_div·15 + is_rem·17 + is_divw·25 + is_remw·27 + is_divuw·26 +
is_remuw·28`, which is what the Program-bus fetch checks them against. -/
def divRemFlags (opcode : ℕ) : Vector (ZMod p) 8 :=
  #v[if opcode = 15 then 1 else 0, if opcode = 16 then 1 else 0, if opcode = 17 then 1 else 0,
     if opcode = 18 then 1 else 0, if opcode = 25 then 1 else 0, if opcode = 27 then 1 else 0,
     if opcode = 26 then 1 else 0, if opcode = 28 then 1 else 0]

/-- The `DivRem` chip's committed input row for one event — a **real** row (`is_real = 1`). The
eight variant flags are *not* here: SP1 does not commit them as input columns, the circuit
witnesses them from the hint (`RTypeEvent.toDivRemHint`). -/
def RTypeEvent.toDivRemInputs (e : RTypeEvent) : DivRemChip.Inputs (ZMod p) where
  is_real := 1
  state := cpuStateCols e.clk e.pc
  adapter := rTypeReaderCols e

/-- **The row's prover hint.** The `"div_rem_flags"` key carries this row's own seven hinted
selectors, computed from **this event's opcode**; the eighth (`is_divu`) is the chip's derived
slot. This is what makes the built row mean the event: the chip's `Spec` says the result word is
the RV64 division the *flags* name. -/
def RTypeEvent.toDivRemHint (e : RTypeEvent) : ProverHint (ZMod p) :=
  flagHint "div_rem_flags" (divRemHintFlags e.opcode)

/-- The `op_c` access block of a `DivRem` padding row: the **read value** is the word `1` (SP1's
"0 divided by 1" template — `alu/divrem/mod.rs:561-563`), both timestamp columns zero, as for any
padded row. -/
def oneAccessCols : Extracted.RegisterAccessCols (ZMod p) where
  prev_value := #v[1, 0, 0, 0]
  access_timestamp := { prev_low := 0, diff_low_limb := 0 }

/-- The R-type adapter block of a `DivRem` padding row: zero everywhere except the `op_c` read
value, which is the word `1`. This is SP1's padded row verbatim — it zero-initializes the whole
row and then writes `op_c_memory.prev_value = Word::from(1)`. -/
def divRemPaddingRTypeReaderCols : Extracted.RTypeReader (ZMod p) where
  op_a := 0
  op_a_memory := zeroAccessCols
  op_a_0 := 0
  op_b := 0
  op_b_memory := zeroAccessCols
  op_c := 0
  op_c_memory := oneAccessCols

/-- The `DivRem` chip's padding row: SP1's "0 divided by 1" template — `is_real = 0`, a zero `op_b`
read, the `op_c` read value `1`, and (through the empty hint's derived slot) `is_divu = 1`. Unlike
every other chip of the rollout this is **not** an all-zero row, because the chip's
`ProverAssumptions` pins the template on every `is_real = 0` row — which is what SP1's own trace
filler writes. -/
def divRemPaddingInputs : DivRemChip.Inputs (ZMod p) where
  is_real := 0
  state := zeroCPUStateCols
  adapter := divRemPaddingRTypeReaderCols

variable [Fact p.Prime] [Fact (2 ^ 24 < p)]

omit [Fact (2 ^ 24 < p)] in
/-- Reading the built hint back at the key's own width returns the seven selectors the builder put
in. -/
lemma hintRead_toDivRemHint (e : RTypeEvent) :
    (((e.toDivRemHint (p := p)) "div_rem_flags" 7)[0]?).getD #v[0, 0, 0, 0, 0, 0, 0]
      = divRemHintFlags e.opcode := by
  have hdefault : (default : Vector (ZMod p) 7) = #v[0, 0, 0, 0, 0, 0, 0] := rfl
  rw [RTypeEvent.toDivRemHint, ← hdefault]
  exact flagHint_apply _ _

omit [Fact (2 ^ 24 < p)] in
/-- **The chip reads back exactly this event's selectors.** The seven hinted slots are the
builder's; the eighth is the chip's derived `1 - Σ`, which is `is_divu` precisely because the
routing condition says the opcode is one of the eight this chip serves. -/
lemma hintFlags_toDivRemHint {e : RTypeEvent} (hop : e.IsDivRem) :
    DivRemChip.hintFlags (e.toDivRemHint (p := p)) = divRemFlags e.opcode := by
  simp only [DivRemChip.hintFlags, hintRead_toDivRemHint]
  obtain h | h | h | h | h | h | h | h := hop <;> simp [divRemHintFlags, divRemFlags, h]

omit [Fact (2 ^ 24 < p)] in
/-- A padding row's empty hint reads back as SP1's template: `is_divu = 1`, every other selector
`0`. No special case is needed — seven absent flags are `0`, so the derived slot is `1`. -/
lemma divRemHintFlags_empty :
    DivRemChip.hintFlags (ProverHint.empty (ZMod p)) = #v[0, 1, 0, 0, 0, 0, 0, 0] :=
  DivRemChip.hintFlags_absent _ rfl

omit [Fact (2 ^ 24 < p)] in
/-- **The padding row is SP1's template, exhibited.** Exactly the three facts
`DivRemChip.ProverAssumptions` demands of an `is_real = 0` row — a zero `op_b` read, the `op_c`
read value `1`, and `is_divu = 1` — and the reason this chip's padding builder is not the shared
all-zero one. -/
lemma divRemPadding_isTemplate :
    (divRemPaddingInputs (p := p)).op_b_val = #v[0, 0, 0, 0] ∧
      (divRemPaddingInputs (p := p)).op_c_val = #v[1, 0, 0, 0] ∧
      DivRemChip.hintFlags (ProverHint.empty (ZMod p)) = #v[0, 1, 0, 0, 0, 0, 0, 0] :=
  ⟨rfl, rfl, divRemHintFlags_empty⟩

omit [Fact (2 ^ 24 < p)] in
/-- **The built flags name the event's instruction.** Weighted by the chip's own reader opcode —
`DivRemContract.encodedOpcode`'s eight coefficients, the expression `DivRemChip.main` threads into
`RTypeReader` and the Program-bus fetch checks — the selectors this builder supplies recombine to
the event's opcode discriminant. This is the statement that the hint is *this* row's, not an
arbitrary one-hot vector. -/
lemma divRemFlags_opcode_eq {e : RTypeEvent} (hop : e.IsDivRem) :
    (divRemFlags (p := p) e.opcode)[0] * 15 + (divRemFlags (p := p) e.opcode)[1] * 16
        + (divRemFlags (p := p) e.opcode)[2] * 17 + (divRemFlags (p := p) e.opcode)[3] * 18
        + (divRemFlags (p := p) e.opcode)[4] * 25 + (divRemFlags (p := p) e.opcode)[5] * 27
        + (divRemFlags (p := p) e.opcode)[6] * 26 + (divRemFlags (p := p) e.opcode)[7] * 28
      = ((e.opcode : ℕ) : ZMod p) := by
  obtain h | h | h | h | h | h | h | h := hop <;> rw [h] <;> norm_num [divRemFlags]

omit [Fact (2 ^ 24 < p)] in
/-- **The flags of a real `DivRem` row are binary.** That is all the chip's `ProverAssumptions`
asks of the hint's shape — the one-hot *sum* is an identity of the derived encoding
(`Populate.hintFlags_sum_eq_one`), not an assumption. -/
lemma divRemFlags_spec {e : RTypeEvent} (hop : e.IsDivRem) :
    ((divRemFlags (p := p) e.opcode)[0] = 0 ∨ (divRemFlags (p := p) e.opcode)[0] = 1) ∧
    ((divRemFlags (p := p) e.opcode)[1] = 0 ∨ (divRemFlags (p := p) e.opcode)[1] = 1) ∧
    ((divRemFlags (p := p) e.opcode)[2] = 0 ∨ (divRemFlags (p := p) e.opcode)[2] = 1) ∧
    ((divRemFlags (p := p) e.opcode)[3] = 0 ∨ (divRemFlags (p := p) e.opcode)[3] = 1) ∧
    ((divRemFlags (p := p) e.opcode)[4] = 0 ∨ (divRemFlags (p := p) e.opcode)[4] = 1) ∧
    ((divRemFlags (p := p) e.opcode)[5] = 0 ∨ (divRemFlags (p := p) e.opcode)[5] = 1) ∧
    ((divRemFlags (p := p) e.opcode)[6] = 0 ∨ (divRemFlags (p := p) e.opcode)[6] = 1) ∧
    ((divRemFlags (p := p) e.opcode)[7] = 0 ∨ (divRemFlags (p := p) e.opcode)[7] = 1) := by
  obtain h | h | h | h | h | h | h | h := hop <;> simp [divRemFlags, h]

/-- The `op_c` read value of a `DivRem` padding row — the word `1` — is a u64, the one operand
`isU64` a non-zero padding row still owes. -/
lemma oneWord_isU64 : Word.isU64 (#v[1, 0, 0, 0] : Word (ZMod p)) := by
  have hp : 2 ^ 24 < p := Fact.out
  haveI : Fact (1 < p) := ⟨by omega⟩
  refine Word.isU64_of_cases ?_ (by simp) (by simp) (by simp)
  rw [show (#v[1, 0, 0, 0] : Word (ZMod p))[0] = 1 from rfl, ZMod.val_one]
  norm_num

end SP1Clean.TraceGen

namespace SP1Clean.DivRemChip

open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## The chip's honest-prover contract on a built row -/

/--
**A well-formed R-type trace event builds a row the honest prover can complete, at the hint the
same event builds.** Every conjunct of `DivRemChip.ProverAssumptions` follows from
`RTypeEvent.WellFormed` and the routing condition `hop : e.IsDivRem`, with no residual side
condition: the reader half is `MulChip`'s verbatim, the eight flag binaries come from the routing
condition through `hintFlags_toDivRemHint`, and the padding pin is vacuous on a real row.

The `data` is arbitrary — the chip's prover contract does not read it — but the **hint is not**:
it is `e.toDivRemHint`, the selectors of this event's own opcode (`divRemFlags_opcode_eq`).
-/
theorem proverAssumptions_of_event {e : RTypeEvent} (h : e.WellFormed) (hop : e.IsDivRem)
    (data : ProverData (ZMod p)) :
    ProverAssumptions (e.toDivRemInputs (p := p)) data e.toDivRemHint := by
  obtain ⟨hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7⟩ := divRemFlags_spec (p := p) hop
  have hne : ¬((1 : ZMod p) = 0) := one_ne_zero
  simp only [ProverAssumptions, hintFlags_toDivRemHint hop]
  refine ⟨?_, ?_, ?_, ?_, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- the two source operands, and the value the `op_a` write displaces: committed limb-wise, so
  -- `isU64` regardless of the event
  · exact wordOfNat_isU64 _
  · exact wordOfNat_isU64 _
  · exact fun _ => wordOfNat_isU64 _
  -- the row is real
  · exact Or.inr rfl
  -- the padding pin is a statement about `is_real = 0` rows only
  · exact fun hr => absurd hr hne
  -- `rd ≠ x0`, so the `op_a_0` zeroing flag is off
  · exact rTypeReaderCols_op_a_0_eq_zero h.opA_ne_zero
  -- the shared reader contracts: the state block, then the three register accesses
  · exact cpuState_spec e.clk e.pc h.clk_mod _ _ _
  · exact registerAccessCols_spec_opA h.clk_mod h.prevTsA_lt
  · exact registerAccessCols_spec_opB h.clk_mod h.prevTsB_lt
  · exact registerAccessCols_spec_opC h.clk_mod h.prevTsC_lt
  -- the decode bounds the Program-bus fetch carries
  · exact fun _ => ⟨rTypeReaderCols_op_a_val_lt h.opA_lt, (cpuStateCols_pc_val_lt e.clk e.pc).1,
      (cpuStateCols_pc_val_lt e.clk e.pc).2.1, (cpuStateCols_pc_val_lt e.clk e.pc).2.2⟩
  -- G1: the three pulled prior records' 24-bit access clocks
  · exact fun _ => ⟨registerAccessCols_prevLow_val_lt _ _ _,
      registerAccessCols_prevLow_val_lt _ _ _, registerAccessCols_prevLow_val_lt _ _ _⟩

/-- **A padding row satisfies the same contract**, at the empty hint — and here that is a real
obligation rather than a vacuity: the row must *be* SP1's "0 divided by 1" template, since the
contract's `is_real = 0` conjunct pins the two operand words and all eight flags. It is, by
construction (`divRemPadding_isTemplate`), and the empty hint's derived slot supplies
`is_divu = 1`. What survives besides is the two operand `isU64`s (the word `1` among them) and the
`op_a_0` flag; every `is_real = 1`-gated conjunct is vacuous. -/
theorem proverAssumptions_padding (data : ProverData (ZMod p)) :
    ProverAssumptions (divRemPaddingInputs (p := p)) data (ProverHint.empty (ZMod p)) := by
  have hzero : Word.isU64 (#v[0, 0, 0, 0] : Word (ZMod p)) :=
    Word.isU64_of_cases (by simp) (by simp) (by simp) (by simp)
  have hne : ¬((0 : ZMod p) = 1) := zero_ne_one
  simp only [ProverAssumptions, divRemHintFlags_empty]
  refine ⟨hzero, oneWord_isU64, fun hr => absurd hr hne, Or.inl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, rfl, fun hr => absurd hr hne, fun hr => absurd hr hne, fun hr => absurd hr hne,
    fun hr => absurd hr hne, fun hr => absurd hr hne, fun hr => absurd hr hne⟩ <;>
    -- the eight variant selectors as the empty hint reads them back (SP1's `is_divu = 1`
    -- template), and last the template pin — this chip's one padding conjunct with real content
    first
      | exact fun _ => ⟨rfl, rfl, trivial⟩
      | simp

/-! ## The built table -/

/-- The DivRem chip as a flat-AIR component: one circuit, checked independently on each row.

A plain `def`, deliberately not an `abbrev` (see `AddChip.component` for the measurement). -/
def component : Air.Flat.Component (ZMod p) := ⟨circuit⟩

/-- The rows a trace builds: one input row **paired with its own hint** per event, then `padding`
copies of SP1's "0 divided by 1" template at the empty hint. -/
def traceInputs (events : List RTypeEvent) (padding : ℕ) :
    List (Inputs (ZMod p) × ProverHint (ZMod p)) :=
  events.map (fun e => (e.toDivRemInputs, e.toDivRemHint))
    ++ List.replicate padding (divRemPaddingInputs, ProverHint.empty (ZMod p))

/-- Every row of a built trace — event row or padding row — satisfies the chip's honest-prover
contract at its own hint, provided every event is a divide/remainder instruction. -/
theorem proverAssumptions_of_mem_traceInputs {events : List RTypeEvent} {padding : ℕ}
    (h : ∀ e ∈ events, e.WellFormed ∧ e.IsDivRem) (data : ProverData (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) events padding, ProverAssumptions input.1 data input.2 := by
  intro input hin
  rcases List.mem_append.mp hin with hin | hin
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
    exact proverAssumptions_of_event (h e he).1 (h e he).2 data
  · rw [List.eq_of_mem_replicate hin]
    exact proverAssumptions_padding data

/-- **A real trace builds a valid DivRem table.** Every `assertZero` of the whole flattened chip
circuit — the two `MulOperation` products and their glue, the overflow and divide-by-zero
comparisons, the remainder range check, the seven sign bits, the carry chain, the chip's own
assert tail, the reader glue — evaluates to zero on every built row, and no static lookup is left
unchecked. -/
theorem traceTable_constraints (events : List RTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (h : ∀ e ∈ events, e.WellFormed ∧ e.IsDivRem) :
    (Air.Flat.Table.buildHinted (component (p := p)) (traceInputs events padding)
      data).Constraints :=
  Air.Flat.Table.buildHinted_constraints _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data)

/-- The same table satisfies its **channel guarantees** — every message it pushes onto the State,
Memory, Program and Byte channels carries the payload its channel promises. -/
theorem traceTable_guarantees (events : List RTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (h : ∀ e ∈ events, e.WellFormed ∧ e.IsDivRem) :
    (Air.Flat.Table.buildHinted (component (p := p)) (traceInputs events padding)
      data).Guarantees :=
  Air.Flat.Table.buildHinted_guarantees _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data)

/-- The table's interaction list on a channel, in closed form: the per-row evaluated interactions,
concatenated in row order. -/
theorem traceTable_interactionsWith (events : List RTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (channel : RawChannel (ZMod p)) :
    (Air.Flat.Table.buildHinted (component (p := p)) (traceInputs events padding)
        data).interactionsWith channel =
      (traceInputs (p := p) events padding).flatMap fun input =>
        (component (p := p)).operations.interactionValuesWith channel
          (Environment.fromArray ((component (p := p)).buildRow input.1 data input.2) data) :=
  Air.Flat.Table.buildHinted_interactions _ _ _ channel

end SP1Clean.DivRemChip
