import SP1Clean.FormalModel.TraceGen.Readers
import SP1Clean.Proofs.Chips.ShiftLeftChip.Witgen
import ToClean.Air.TableBuild

/-! # Shift-left event and table construction

Event opcodes supply the committed SLL/SLLW selectors. Register and immediate operands
share the ALU adapter contract; padding supplies zero selectors and operands. Clean's
ordinary table builder needs no per-row hints.
-/

namespace SP1Clean.TraceGen

variable {p : ℕ}

/-- The two variant selectors of a `ShiftLeft` row, in the chip's own column order (`is_sll`,
`is_sllw`), read off the executor's opcode discriminant (`Opcode::{SLL, SLLW} = 6, 21`). The row's
third witnessed flag `is_sllw_imm` is *derived* in-circuit as `is_sllw · imm_c`, not a hint entry. -/
def shiftLeftFlags (opcode : ℕ) : Vector (ZMod p) 2 :=
  #v[if opcode = 6 then 1 else 0, if opcode = 21 then 1 else 0]

/-- The `ShiftLeft` chip's committed input row for one event — a **real** row (`is_real = 1`). -/
def ALUTypeEvent.toShiftLeftInputs (e : ALUTypeEvent) : ShiftLeftChip.Inputs (ZMod p) where
  state := cpuStateCols e.clk e.pc
  adapter := aluTypeReaderCols e
  isSll := (shiftLeftFlags e.opcode)[0]
  isSllw := (shiftLeftFlags e.opcode)[1]

lemma ALUTypeEvent.toShiftLeftInputs_adapter (e : ALUTypeEvent) :
    (e.toShiftLeftInputs (p := p)).adapter = aluTypeReaderCols e := rfl

/-- The `ShiftLeft` chip's padding row: every column zero, `is_real = 0` (so `imm_c = 0`, which the
ungated `(is_real - 1) * imm_c = 0` conjunct needs). -/
def shiftLeftPaddingInputs : ShiftLeftChip.Inputs (ZMod p) where
  state := zeroCPUStateCols
  adapter := zeroALUTypeReaderCols
  isSll := 0
  isSllw := 0

variable [Fact p.Prime] [Fact (2 ^ 24 < p)]

omit [Fact (2 ^ 24 < p)] in
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
**A well-formed `ShiftLeft` trace event builds a row the honest prover can complete, for arbitrary data and hints.** Every conjunct of `ShiftLeftChip.ProverAssumptions` follows from
`ALUTypeEvent.WellFormed` and the routing condition `hop : e.IsShiftLeft`; both register and
immediate operand forms are admitted.
-/
theorem proverAssumptions_of_event {e : ALUTypeEvent} (h : e.WellFormed) (hop : e.IsShiftLeft)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ProverAssumptions (e.toShiftLeftInputs (p := p)) data hint := by
  obtain ⟨hf0, hf1, hsum⟩ := shiftLeftFlags_spec (p := p) hop
  have hreal : (e.toShiftLeftInputs (p := p)).is_real = 1 := hsum
  simp only [ProverAssumptions, hreal]
  refine ⟨?_, ?_, ?_, ?_, hf0, hf1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- the `rs1` read, then the `op_c` block's committed value — a u64 in *either* row form
  · exact wordOfNat_isU64 _
  · exact aluTypeOpCCols_prev_value_isU64 e
  -- the value the `op_a` write displaces
  · exact fun _ => wordOfNat_isU64 _
  -- the row is real
  · exact Or.inr trivial
  -- `rd ≠ x0`, so the `op_a_0` zeroing flag is off
  · exact aluTypeReaderCols_op_a_0_eq_zero h.opA_ne_zero
  -- the three `imm_c` conjuncts for the exact register/immediate split
  · simp only [sub_self, zero_mul]
  · rcases aluTypeReaderCols_imm_c_bool (p := p) h.immC_bool with h0 | h1
    · exact Or.inr (by
        rw [ALUTypeEvent.toShiftLeftInputs_adapter, h0, sub_zero])
    · exact Or.inl (by
        rw [ALUTypeEvent.toShiftLeftInputs_adapter, h1, sub_self])
  · rw [ALUTypeEvent.toShiftLeftInputs_adapter]
    exact aluTypeReaderCols_imm_copy (p := p) h.immC_bool
  -- the shared reader contracts: the state block, then the two unconditional register accesses
  · exact cpuState_spec e.clk e.pc h.clk_mod _ _ _
  · exact registerAccessCols_spec_opA h.clk_mod h.prevTsA_lt
  · exact registerAccessCols_spec_opB h.clk_mod h.prevTsB_lt
  -- the `op_c` access: an ordinary `rs2` read or the vacuous immediate block
  · rw [ALUTypeEvent.toShiftLeftInputs_adapter, aluTypeReaderCols_op_c_memory]
    exact aluTypeOpCCols_spec h.clk_mod h.immC_bool h.prevTsC_reg
  -- the decode bounds the Program-bus fetch carries
  · exact fun _ => ⟨aluTypeReaderCols_op_a_val_lt h.opA_lt, (cpuStateCols_pc_val_lt e.clk e.pc).1,
      (cpuStateCols_pc_val_lt e.clk e.pc).2.1, (cpuStateCols_pc_val_lt e.clk e.pc).2.2⟩
  -- G1: the pulled prior records' 24-bit access clocks
  · exact fun _ => ⟨registerAccessCols_prevLow_val_lt _ _ _,
      registerAccessCols_prevLow_val_lt _ _ _⟩
  · exact fun _ => aluTypeOpCCols_prevLow_val_lt e

/-- **A padding row satisfies the same contract**, for any hint: both selectors are zero,
and the `imm_c` conjuncts hold because a zero row's
`imm_c` is `0`. -/
theorem proverAssumptions_padding (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ProverAssumptions (shiftLeftPaddingInputs (p := p)) data hint := by
  have hzero : Word.isU64 (#v[0, 0, 0, 0] : Word (ZMod p)) :=
    Word.isU64_of_cases (by simp) (by simp) (by simp) (by simp)
  have hne : ¬((0 : ZMod p) = 1) := zero_ne_one
  have hreal : (shiftLeftPaddingInputs (p := p)).is_real = 0 := by simp [shiftLeftPaddingInputs]
  simp only [ProverAssumptions, hreal]
  refine ⟨hzero, hzero, fun hr => absurd hr hne, Or.inl trivial, Or.inl rfl, Or.inl rfl,
    rfl, by simp [shiftLeftPaddingInputs, zeroALUTypeReaderCols],
    ?_, ⟨by simp [shiftLeftPaddingInputs, zeroALUTypeReaderCols],
      by simp [shiftLeftPaddingInputs, zeroALUTypeReaderCols],
      by simp [shiftLeftPaddingInputs, zeroALUTypeReaderCols],
      by simp [shiftLeftPaddingInputs, zeroALUTypeReaderCols]⟩,
    fun hr => absurd hr hne, fun hr => absurd hr hne, fun hr => absurd hr hne, ?_,
    fun hr => absurd hr hne, fun hr => absurd hr hne, ?_⟩ <;>
    · first
        | exact Or.inl (by simp [shiftLeftPaddingInputs, zeroALUTypeReaderCols])
        | · intro hr
            rw [show (shiftLeftPaddingInputs (p := p)).adapter.imm_c = 0 from rfl,
              sub_zero] at hr
            exact absurd hr hne

/-! ## The built table -/

/-- The ShiftLeft chip as a flat-AIR component: one circuit, checked independently on each row.

A plain `def`, deliberately not an `abbrev` (see `AddChip.component` for the measurement). -/
def component : Air.Flat.Component (ZMod p) := { circuit := circuit }

/-- Real event inputs followed by all-zero padding inputs. -/
def traceInputs (events : List ALUTypeEvent) (padding : ℕ) : List (Inputs (ZMod p)) :=
  events.map ALUTypeEvent.toShiftLeftInputs ++ List.replicate padding shiftLeftPaddingInputs

/-- Every event or padding input satisfies the chip's prover contract. -/
theorem proverAssumptions_of_mem_traceInputs {events : List ALUTypeEvent} {padding : ℕ}
    (h : ∀ e ∈ events, e.WellFormed ∧ e.IsShiftLeft) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) events padding, ProverAssumptions input data hint := by
  intro input hin
  rcases List.mem_append.mp hin with hin | hin
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
    exact proverAssumptions_of_event (h e he).1 (h e he).2 data hint
  · rw [List.eq_of_mem_replicate hin]
    exact proverAssumptions_padding data hint

/-- **A real trace builds a valid ShiftLeft table.** Every `assertZero` of the whole flattened chip
circuit evaluates to zero on every built row, and no static lookup is left unchecked. -/
theorem traceTable_constraints (events : List ALUTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p))
    (h : ∀ e ∈ events, e.WellFormed ∧ e.IsShiftLeft) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events padding) data (ProverHint.empty _)).Constraints data :=
  Air.Flat.Table.build_constraints _ _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data (ProverHint.empty _))

/-- The same table satisfies its **channel guarantees** — every message it pushes onto the State,
Memory, Program and Byte channels carries the payload its channel promises. -/
theorem traceTable_guarantees (events : List ALUTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p))
    (h : ∀ e ∈ events, e.WellFormed ∧ e.IsShiftLeft) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events padding) data (ProverHint.empty _)).Guarantees data :=
  Air.Flat.Table.build_guarantees _ _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data (ProverHint.empty _))

/-- The table's interaction list on a channel, in closed form: the per-row evaluated interactions,
concatenated in row order. -/
theorem traceTable_interactionsWith (events : List ALUTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (channel : RawChannel (ZMod p)) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events padding)
        data (ProverHint.empty _)).interactionsWith data channel =
      (traceInputs (p := p) events padding).flatMap fun input =>
        (component (p := p)).operations.interactionValuesWith channel
          (Environment.fromArray ((component (p := p)).buildRow input data (ProverHint.empty _)) data) :=
  Air.Flat.Table.build_interactions _ _ _ _ _ data channel

end SP1Clean.ShiftLeftChip
