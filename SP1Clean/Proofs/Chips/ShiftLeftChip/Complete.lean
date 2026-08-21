import SP1Clean.FormalModel.TraceGen.Readers
import SP1Clean.Proofs.Chips.ShiftLeftChip.Witgen
import ToClean.Air.TableBuild

/-! # `SP1Clean.ShiftLeftChip` — from trace events to a valid AIR table

`SLL`/`SLLW` through the trace-generation chain. Structurally `LtChip/Complete.lean`: two variant
flags witnessed from the `"shift_left_flags"` hint key, so the row's hint is built per row from
**this event's own opcode discriminant** (`Opcode::{SLL, SLLW} = 6, 21`, the numbers the chip
threads into its reader as `is_sll·6 + is_sllw·21`). See `BitwiseChip/Complete.lean` for why the
hint must be per row, and `AddwChip/Complete.lean` for the ALU-type adapter half.

`ALUTypeEvent.IsShiftLeft` is the chip's **routing** condition, and padding is satisfiable: the
empty hint reads both flags as `0`, matching `is_real = 0`.

**What is new relative to `Lt`** is the chip's explicit `imm_c` machinery — SP1's shift chips carry
the `ALUTypeReader.Spec` immediate conjuncts inline rather than demanding `imm_c = 0`:

    (is_real - 1) * imm_c = 0,   (is_real - imm_c = 0 ∨ is_real - imm_c = 1),
    imm_c * (op_c_memory.prev_value[i] - op_c[i]) = 0   (four)

On the register rows this theorem covers (`himm : e.immC = 0`) all six are `0`-multiplications. The
immediate `SLLI`/`SLLIW` rows are covered by soundness and the bridge, exactly as for `Addw`; the
builder's `aluTypeOpCCols` already models them (its immediate branch copies the committed `op_c`
word into `prev_value`, which is what the four pins ask for), so extending this theorem to them is
a follow-up, not a gap in the record. -/

namespace SP1Clean.TraceGen

variable {p : ℕ}

/-- The two variant selectors of a `ShiftLeft` row, in the chip's own column order (`is_sll`,
`is_sllw`), read off the executor's opcode discriminant (`Opcode::{SLL, SLLW} = 6, 21`). The row's
third witnessed flag `is_sllw_imm` is *derived* in-circuit as `is_sllw · imm_c`, not a hint entry. -/
def shiftLeftFlags (opcode : ℕ) : Vector (ZMod p) 2 :=
  #v[if opcode = 6 then 1 else 0, if opcode = 21 then 1 else 0]

/-- The `ShiftLeft` chip's committed input row for one event — a **real** row (`is_real = 1`). -/
def ALUTypeEvent.toShiftLeftInputs (e : ALUTypeEvent) : ShiftLeftChip.Inputs (ZMod p) where
  is_real := 1
  state := cpuStateCols e.clk e.pc
  adapter := aluTypeReaderCols e

lemma ALUTypeEvent.toShiftLeftInputs_adapter (e : ALUTypeEvent) :
    (e.toShiftLeftInputs (p := p)).adapter = aluTypeReaderCols e := rfl

/-- **The row's prover hint**: the `"shift_left_flags"` key carries the variant selectors of *this
event's* opcode. -/
def ALUTypeEvent.toShiftLeftHint (e : ALUTypeEvent) : ProverHint (ZMod p) :=
  flagHint "shift_left_flags" (shiftLeftFlags e.opcode)

/-- The `ShiftLeft` chip's padding row: every column zero, `is_real = 0` (so `imm_c = 0`, which the
ungated `(is_real - 1) * imm_c = 0` conjunct needs). -/
def shiftLeftPaddingInputs : ShiftLeftChip.Inputs (ZMod p) where
  is_real := 0
  state := zeroCPUStateCols
  adapter := zeroALUTypeReaderCols

variable [Fact p.Prime] [Fact (2 ^ 24 < p)]

omit [Fact (2 ^ 24 < p)] in
/-- The chip reads back exactly the flags the builder put in. -/
lemma hintFlags_toShiftLeftHint (e : ALUTypeEvent) :
    ShiftLeftChip.hintFlags (e.toShiftLeftHint (p := p)) = shiftLeftFlags e.opcode := by
  have hdefault : (default : Vector (ZMod p) 2) = #v[0, 0] := rfl
  rw [ShiftLeftChip.hintFlags, ← hdefault, ALUTypeEvent.toShiftLeftHint]
  exact flagHint_apply _ _

omit [Fact (2 ^ 24 < p)] in
/-- A padding row's empty hint reads back as all-zero flags. -/
lemma shiftLeftHintFlags_empty :
    ShiftLeftChip.hintFlags (ProverHint.empty (ZMod p)) = #v[0, 0] := rfl

/-- **The flags of a real `ShiftLeft` row are one-hot, and their sum is `1`.** -/
lemma shiftLeftFlags_spec {e : ALUTypeEvent} (hop : e.IsShiftLeft) :
    ((shiftLeftFlags (p := p) e.opcode)[0] = 0 ∨ (shiftLeftFlags (p := p) e.opcode)[0] = 1) ∧
    ((shiftLeftFlags (p := p) e.opcode)[1] = 0 ∨ (shiftLeftFlags (p := p) e.opcode)[1] = 1) ∧
    (shiftLeftFlags (p := p) e.opcode)[0] + (shiftLeftFlags (p := p) e.opcode)[1] = 1 := by
  obtain h | h := hop <;> simp [shiftLeftFlags, h]

end SP1Clean.TraceGen

namespace SP1Clean.ShiftLeftChip

open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## The chip's honest-prover contract on a built row -/

/--
**A well-formed register-row `ShiftLeft` trace event builds a row the honest prover can complete, at
the hint the same event builds.** Every conjunct of `ShiftLeftChip.ProverAssumptions` follows from
`ALUTypeEvent.WellFormed`, the routing condition `hop : e.IsShiftLeft`, and `himm : e.immC = 0`.
-/
theorem proverAssumptions_of_event {e : ALUTypeEvent} (h : e.WellFormed) (hop : e.IsShiftLeft)
    (himm : e.immC = 0) (data : ProverData (ZMod p)) :
    ProverAssumptions (e.toShiftLeftInputs (p := p)) data e.toShiftLeftHint := by
  obtain ⟨hf0, hf1, hsum⟩ := shiftLeftFlags_spec (p := p) hop
  have himm0 : (e.toShiftLeftInputs (p := p)).adapter.imm_c = 0 := by
    rw [ALUTypeEvent.toShiftLeftInputs_adapter, aluTypeReaderCols_imm_c, himm, Nat.cast_zero]
  simp only [ProverAssumptions, hintFlags_toShiftLeftHint]
  refine ⟨?_, ?_, ?_, ?_, hf0, hf1, hsum.symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- the `rs1` read, then the `op_c` block's committed value — a u64 in *either* row form
  · exact wordOfNat_isU64 _
  · exact aluTypeOpCCols_prev_value_isU64 e
  -- the value the `op_a` write displaces
  · exact fun _ => wordOfNat_isU64 _
  -- the row is real
  · exact Or.inr rfl
  -- `rd ≠ x0`, so the `op_a_0` zeroing flag is off
  · exact aluTypeReaderCols_op_a_0_eq_zero h.opA_ne_zero
  -- the three `imm_c` conjuncts, all `0`-multiplications on a register row
  · rw [himm0, mul_zero]
  · rw [himm0, sub_zero]
    exact Or.inr rfl
  · exact ⟨by rw [himm0, zero_mul], by rw [himm0, zero_mul], by rw [himm0, zero_mul],
      by rw [himm0, zero_mul]⟩
  -- the shared reader contracts: the state block, then the two unconditional register accesses
  · exact cpuState_spec e.clk e.pc h.clk_mod _ _ _
  · exact registerAccessCols_spec_opA h.clk_mod h.prevTsA_lt
  · exact registerAccessCols_spec_opB h.clk_mod h.prevTsB_lt
  -- the `op_c` access: on a register row the block is the ordinary `rs2` read block
  · rw [ALUTypeEvent.toShiftLeftInputs_adapter, aluTypeReaderCols_op_c_memory,
      aluTypeOpCCols_of_reg himm]
    exact registerAccessCols_spec_opC h.clk_mod (h.prevTsC_reg himm)
  -- the decode bounds the Program-bus fetch carries
  · exact fun _ => ⟨aluTypeReaderCols_op_a_val_lt h.opA_lt, (cpuStateCols_pc_val_lt e.clk e.pc).1,
      (cpuStateCols_pc_val_lt e.clk e.pc).2.1, (cpuStateCols_pc_val_lt e.clk e.pc).2.2⟩
  -- G1: the pulled prior records' 24-bit access clocks
  · exact fun _ => ⟨registerAccessCols_prevLow_val_lt _ _ _,
      registerAccessCols_prevLow_val_lt _ _ _⟩
  · exact fun _ => aluTypeOpCCols_prevLow_val_lt e

/-- **A padding row satisfies the same contract**, at the empty hint: both flags read back as `0`,
so the selector-sum conjunct is `0 = 0 + 0`, and the `imm_c` conjuncts hold because a zero row's
`imm_c` is `0`. -/
theorem proverAssumptions_padding (data : ProverData (ZMod p)) :
    ProverAssumptions (shiftLeftPaddingInputs (p := p)) data (ProverHint.empty (ZMod p)) := by
  have hzero : Word.isU64 (#v[0, 0, 0, 0] : Word (ZMod p)) :=
    Word.isU64_of_cases (by simp) (by simp) (by simp) (by simp)
  have hne : ¬((0 : ZMod p) = 1) := zero_ne_one
  simp only [ProverAssumptions, shiftLeftHintFlags_empty]
  refine ⟨hzero, hzero, fun hr => absurd hr hne, Or.inl rfl, Or.inl rfl, Or.inl rfl,
    by simp [shiftLeftPaddingInputs], rfl, by simp [shiftLeftPaddingInputs, zeroALUTypeReaderCols],
    ?_, ⟨by simp [shiftLeftPaddingInputs, zeroALUTypeReaderCols],
      by simp [shiftLeftPaddingInputs, zeroALUTypeReaderCols],
      by simp [shiftLeftPaddingInputs, zeroALUTypeReaderCols],
      by simp [shiftLeftPaddingInputs, zeroALUTypeReaderCols]⟩,
    fun hr => absurd hr hne, fun hr => absurd hr hne, fun hr => absurd hr hne, ?_,
    fun hr => absurd hr hne, fun hr => absurd hr hne, ?_⟩ <;>
    · first
        | exact Or.inl (by simp [shiftLeftPaddingInputs, zeroALUTypeReaderCols])
        | · intro hr
            rw [show (shiftLeftPaddingInputs (p := p)).is_real = 0 from rfl,
              show (shiftLeftPaddingInputs (p := p)).adapter.imm_c = 0 from rfl,
              sub_zero] at hr
            exact absurd hr hne

/-! ## The built table -/

/-- The ShiftLeft chip as a flat-AIR component: one circuit, checked independently on each row.

A plain `def`, deliberately not an `abbrev` (see `AddChip.component` for the measurement). -/
def component : Air.Flat.Component (ZMod p) := ⟨circuit⟩

/-- The rows a trace builds: one input row **paired with its own hint** per event, then `padding`
zero rows at the empty hint. -/
def traceInputs (events : List ALUTypeEvent) (padding : ℕ) :
    List (Inputs (ZMod p) × ProverHint (ZMod p)) :=
  events.map (fun e => (e.toShiftLeftInputs, e.toShiftLeftHint))
    ++ List.replicate padding (shiftLeftPaddingInputs, ProverHint.empty (ZMod p))

/-- Every row of a built trace — event row or padding row — satisfies the chip's honest-prover
contract at its own hint, provided every event is a register-register left shift. -/
theorem proverAssumptions_of_mem_traceInputs {events : List ALUTypeEvent} {padding : ℕ}
    (h : ∀ e ∈ events, e.WellFormed ∧ e.IsShiftLeft ∧ e.immC = 0) (data : ProverData (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) events padding, ProverAssumptions input.1 data input.2 := by
  intro input hin
  rcases List.mem_append.mp hin with hin | hin
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
    exact proverAssumptions_of_event (h e he).1 (h e he).2.1 (h e he).2.2 data
  · rw [List.eq_of_mem_replicate hin]
    exact proverAssumptions_padding data

/-- **A real trace builds a valid ShiftLeft table.** Every `assertZero` of the whole flattened chip
circuit evaluates to zero on every built row, and no static lookup is left unchecked. -/
theorem traceTable_constraints (events : List ALUTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (h : ∀ e ∈ events, e.WellFormed ∧ e.IsShiftLeft ∧ e.immC = 0) :
    (Air.Flat.Table.buildHinted (component (p := p)) (traceInputs events padding) data).Constraints :=
  Air.Flat.Table.buildHinted_constraints _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data)

/-- The same table satisfies its **channel guarantees** — every message it pushes onto the State,
Memory, Program and Byte channels carries the payload its channel promises. -/
theorem traceTable_guarantees (events : List ALUTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (h : ∀ e ∈ events, e.WellFormed ∧ e.IsShiftLeft ∧ e.immC = 0) :
    (Air.Flat.Table.buildHinted (component (p := p)) (traceInputs events padding) data).Guarantees :=
  Air.Flat.Table.buildHinted_guarantees _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data)

/-- The table's interaction list on a channel, in closed form: the per-row evaluated interactions,
concatenated in row order. -/
theorem traceTable_interactionsWith (events : List ALUTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (channel : RawChannel (ZMod p)) :
    (Air.Flat.Table.buildHinted (component (p := p)) (traceInputs events padding)
        data).interactionsWith channel =
      (traceInputs (p := p) events padding).flatMap fun input =>
        (component (p := p)).operations.interactionValuesWith channel
          (Environment.fromArray ((component (p := p)).buildRow input.1 data input.2) data) :=
  Air.Flat.Table.buildHinted_interactions _ _ _ channel

end SP1Clean.ShiftLeftChip
