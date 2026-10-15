import SP1Clean.FormalModel.TraceGen.Readers
import SP1Clean.Proofs.Chips.DivRemChip.Witgen
import ToClean.Air.TableBuild

/-! # DivRem trace construction

Each event supplies its seven opcode selectors as circuit inputs. The circuit derives DIVU
as their complement; `selectorFlags_toDivRemInputs` proves that all eight flags agree with
the event's opcode when the event routes to this chip. Their sum is an identity, while their
binary values remain part of the prover contract.

Padding uses SP1's "0 divided by 1" DIVU template: zero supplied selectors, a divisor read of
one, and zero activity. The table theorems cover both real events and this padding, including
the ungated arithmetic constraints and channel guarantees. No external hint supplies selectors.
-/

namespace SP1Clean.TraceGen

variable {p : ℕ}

/-- The seven supplied selectors in DIV, REM, REMU, DIVW, REMW, DIVUW, REMUW order.
DIVU is derived by the circuit. -/
def divRemSelectors (opcode : ℕ) : Vector (ZMod p) 7 :=
  #v[if opcode = 15 then 1 else 0, if opcode = 17 then 1 else 0, if opcode = 18 then 1 else 0,
     if opcode = 25 then 1 else 0, if opcode = 27 then 1 else 0, if opcode = 26 then 1 else 0,
     if opcode = 28 then 1 else 0]

/-- The eight variant selectors the chip reads back, in its own column order (`is_div`, `is_divu`,
`is_rem`, `is_remu`, `is_divw`, `is_remw`, `is_divuw`, `is_remuw`) — the seven supplied ones with
`Opcode::DIVU = 16` restored in slot 1. These are the numbers the chip threads into its reader as
`is_divu·16 + is_remu·18 + is_div·15 + is_rem·17 + is_divw·25 + is_remw·27 + is_divuw·26 +
is_remuw·28`, which is what the Program-bus fetch checks them against. -/
def divRemFlags (opcode : ℕ) : Vector (ZMod p) 8 :=
  #v[if opcode = 15 then 1 else 0, if opcode = 16 then 1 else 0, if opcode = 17 then 1 else 0,
     if opcode = 18 then 1 else 0, if opcode = 25 then 1 else 0, if opcode = 27 then 1 else 0,
     if opcode = 26 then 1 else 0, if opcode = 28 then 1 else 0]

/-- A real DivRem input row, including selectors from the event's opcode. -/
def RTypeEvent.toDivRemInputs (e : RTypeEvent) : DivRemChip.Inputs (ZMod p) where
  is_real := 1
  state := cpuStateCols e.clk e.pc
  adapter := rTypeReaderCols e
  selectors := divRemSelectors e.opcode

/-- The `op_c` access block of a `DivRem` padding row: the **read value** is the word `1` (SP1's
"0 divided by 1" template — `alu/divrem/mod.rs:561-563`), both timestamp columns zero, as for any
padded row. -/
def oneAccessCols : Circuits.Types.RegisterAccessCols (ZMod p) where
  prev_value := #v[1, 0, 0, 0]
  access_timestamp := { prev_low := 0, diff_low_limb := 0 }

/-- The R-type adapter block of a `DivRem` padding row: zero everywhere except the `op_c` read
value, which is the word `1`. This is SP1's padded row verbatim — it zero-initializes the whole
row and then writes `op_c_memory.prev_value = Word::from(1)`. -/
def divRemPaddingRTypeReaderCols : Circuits.Types.RTypeReader (ZMod p) where
  op_a := 0
  op_a_memory := zeroAccessCols
  op_a_0 := 0
  op_b := 0
  op_b_memory := zeroAccessCols
  op_c := 0
  op_c_memory := oneAccessCols

/-- SP1's inactive "0 divided by 1" DIVU padding input. -/
def divRemPaddingInputs : DivRemChip.Inputs (ZMod p) where
  is_real := 0
  state := zeroCPUStateCols
  adapter := divRemPaddingRTypeReaderCols
  selectors := #v[0, 0, 0, 0, 0, 0, 0]

variable [Fact p.Prime] [Fact (2 ^ 24 < p)]

omit [Fact (2 ^ 24 < p)] in
/-- The derived selectors identify the routed event's own opcode, including DIVU. -/
lemma selectorFlags_toDivRemInputs {e : RTypeEvent} (hop : e.IsDivRem) :
    DivRemChip.selectorFlags (e.toDivRemInputs (p := p)).selectors = divRemFlags e.opcode := by
  obtain h | h | h | h | h | h | h | h := hop <;>
    simp [DivRemChip.selectorFlags, RTypeEvent.toDivRemInputs, divRemSelectors, divRemFlags, h]

omit [Fact (2 ^ 24 < p)] in
/-- **The padding row is SP1's template, exhibited.** Exactly the three facts
`DivRemChip.ProverAssumptions` demands of an `is_real = 0` row — a zero `op_b` read, the `op_c`
read value `1`, and `is_divu = 1` — and the reason this chip's padding builder is not the shared
all-zero one. -/
lemma divRemPadding_isTemplate :
    (divRemPaddingInputs (p := p)).op_b_val = #v[0, 0, 0, 0] ∧
      (divRemPaddingInputs (p := p)).op_c_val = #v[1, 0, 0, 0] ∧
      DivRemChip.selectorFlags (divRemPaddingInputs (p := p)).selectors = #v[0, 1, 0, 0, 0, 0, 0, 0] :=
  ⟨rfl, rfl, DivRemChip.selectorFlags_zero⟩

omit [Fact (2 ^ 24 < p)] in
/-- **The built flags name the event's instruction.** Weighted by the chip's own reader opcode —
`DivRemContract.encodedOpcode`'s eight coefficients, the expression `DivRemChip.main` threads into
`RTypeReader` and the Program-bus fetch checks — the selectors this builder supplies recombine to
the event's opcode discriminant. This is the statement that the selectors are *this* row's, not an
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
asks of the selectors — the one-hot *sum* is an identity of the derived encoding
(`DivRemChip.selectorFlags_sum_eq_one`), not an assumption. -/
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
  have : Fact (1 < p) := ⟨by omega⟩
  refine Word.isU64_of_cases ?_ (by simp) (by simp) (by simp)
  rw [show (#v[1, 0, 0, 0] : Word (ZMod p))[0] = 1 from rfl, ZMod.val_one]
  norm_num

end SP1Clean.TraceGen

namespace SP1Clean.DivRemChip

open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## The chip's honest-prover contract on a built row -/

/-- A routed, well-formed event satisfies the prover contract for arbitrary data and hints. -/
theorem proverAssumptions_of_event {e : RTypeEvent} (h : e.WellFormed) (hop : e.IsDivRem)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ProverAssumptions (e.toDivRemInputs (p := p)) data hint := by
  obtain ⟨hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7⟩ := divRemFlags_spec (p := p) hop
  have hne : ¬((1 : ZMod p) = 0) := one_ne_zero
  simp only [ProverAssumptions, selectorFlags_toDivRemInputs hop]
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

/-- The padding input satisfies the same contract, including its ungated arithmetic template. -/
theorem proverAssumptions_padding (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ProverAssumptions (divRemPaddingInputs (p := p)) data hint := by
  have hzero : Word.isU64 (#v[0, 0, 0, 0] : Word (ZMod p)) :=
    Word.isU64_of_cases (by simp) (by simp) (by simp) (by simp)
  have hne : ¬((0 : ZMod p) = 1) := zero_ne_one
  have hflags : selectorFlags (divRemPaddingInputs (p := p)).selectors =
      #v[0, 1, 0, 0, 0, 0, 0, 0] := selectorFlags_zero
  simp only [ProverAssumptions, hflags]
  refine ⟨hzero, oneWord_isU64, fun hr => absurd hr hne, Or.inl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, rfl, fun hr => absurd hr hne, fun hr => absurd hr hne, fun hr => absurd hr hne,
    fun hr => absurd hr hne, fun hr => absurd hr hne, fun hr => absurd hr hne⟩ <;>
    -- the eight variant selectors from the padding inputs (SP1's `is_divu = 1`
    -- template), and last the template pin — this chip's one padding conjunct with real content
    first
      | exact fun _ => ⟨rfl, rfl, trivial⟩
      | simp

/-! ## The built table -/

/-- The DivRem chip as a flat-AIR component: one circuit, checked independently on each row.

A plain `def`, deliberately not an `abbrev` (see `AddChip.component` for the measurement). -/
def component : Air.Flat.Component (ZMod p) := { circuit := circuit }

/-- Real event inputs followed by SP1's DIVU padding template. -/
def traceInputs (events : List RTypeEvent) (padding : ℕ) : List (Inputs (ZMod p)) :=
  events.map RTypeEvent.toDivRemInputs ++ List.replicate padding divRemPaddingInputs

/-- Every row of a built trace — event row or padding row — satisfies the chip's honest-prover
contract provided every event is a divide/remainder instruction. -/
theorem proverAssumptions_of_mem_traceInputs {events : List RTypeEvent} {padding : ℕ}
    (h : ∀ e ∈ events, e.WellFormed ∧ e.IsDivRem) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) events padding, ProverAssumptions input data hint := by
  intro input hin
  rcases List.mem_append.mp hin with hin | hin
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
    exact proverAssumptions_of_event (h e he).1 (h e he).2 data hint
  · rw [List.eq_of_mem_replicate hin]
    exact proverAssumptions_padding data hint

/-- **A real trace builds a valid DivRem table.** Every `assertZero` of the whole flattened chip
circuit — the two `MulOperation` products and their glue, the overflow and divide-by-zero
comparisons, the remainder range check, the seven sign bits, the carry chain, the chip's own
assert tail, the reader glue — evaluates to zero on every built row, and no static lookup is left
unchecked. -/
theorem traceTable_constraints (events : List RTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (h : ∀ e ∈ events, e.WellFormed ∧ e.IsDivRem) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events padding)
      data (ProverHint.empty _)).Constraints data :=
  Air.Flat.Table.build_constraints _ _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data (ProverHint.empty _))

/-- The same table satisfies its **channel guarantees** — every message it pushes onto the State,
Memory, Program and Byte channels carries the payload its channel promises. -/
theorem traceTable_guarantees (events : List RTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (h : ∀ e ∈ events, e.WellFormed ∧ e.IsDivRem) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events padding)
      data (ProverHint.empty _)).Guarantees data :=
  Air.Flat.Table.build_guarantees _ _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data (ProverHint.empty _))

/-- The table's interaction list on a channel, in closed form: the per-row evaluated interactions,
concatenated in row order. -/
theorem traceTable_interactionsWith (events : List RTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (channel : RawChannel (ZMod p)) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events padding)
        data (ProverHint.empty _)).interactionsWith data channel =
      (traceInputs (p := p) events padding).flatMap fun input =>
        (component (p := p)).operations.interactionValuesWith channel
          (Environment.fromArray ((component (p := p)).buildRow input data (ProverHint.empty _)) data) :=
  Air.Flat.Table.build_interactions _ _ _ _ _ data channel

end SP1Clean.DivRemChip
