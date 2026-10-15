import SP1Clean.FormalModel.TraceGen.Readers
import SP1Clean.Proofs.Chips.BitwiseChip.Witgen
import ToClean.Air.TableBuild

/-! # Bitwise trace construction

Each event supplies its three selectors as circuit inputs. Their sum is activity, matching
SP1's physical row. Register and immediate operands use the same ALU adapter contract.
Padding supplies zero operands and selectors; the ordinary table builder needs no hints.
-/

namespace SP1Clean.TraceGen

variable {p : ℕ}

/-- The three variant selectors of a `Bitwise` row, in the chip's own column order (`is_xor`,
`is_or`, `is_and`), read off the executor's opcode discriminant (`Opcode::{XOR, OR, AND} = 3, 4,
5`). The same numbers appear in the chip's `cpu_opcode` expression `is_xor·3 + is_or·4 + is_and·5`,
which is what the Program-bus fetch checks them against. -/
def bitwiseFlags (opcode : ℕ) : Vector (ZMod p) 3 :=
  #v[if opcode = 3 then 1 else 0, if opcode = 4 then 1 else 0, if opcode = 5 then 1 else 0]

/-- Reader columns and selectors determined by one event's opcode. -/
def ALUTypeEvent.toBitwiseInputs (e : ALUTypeEvent) : BitwiseChip.Inputs (ZMod p) where
  state := cpuStateCols e.clk e.pc
  adapter := aluTypeReaderCols e
  isXor := (bitwiseFlags e.opcode)[0]
  isOr := (bitwiseFlags e.opcode)[1]
  isAnd := (bitwiseFlags e.opcode)[2]

/-- SP1's all-zero inactive Bitwise input. -/
def bitwisePaddingInputs : BitwiseChip.Inputs (ZMod p) where
  state := zeroCPUStateCols
  adapter := zeroALUTypeReaderCols
  isXor := 0
  isOr := 0
  isAnd := 0

variable [Fact p.Prime] [Fact (2 ^ 24 < p)]

omit [Fact (2 ^ 24 < p)] in
/-- A routed Bitwise event supplies boolean selectors with sum one. -/
lemma bitwiseFlags_spec {e : ALUTypeEvent} (hop : e.IsBitwise) :
    ((bitwiseFlags (p := p) e.opcode)[0] = 0 ∨ (bitwiseFlags (p := p) e.opcode)[0] = 1) ∧
    ((bitwiseFlags (p := p) e.opcode)[1] = 0 ∨ (bitwiseFlags (p := p) e.opcode)[1] = 1) ∧
    ((bitwiseFlags (p := p) e.opcode)[2] = 0 ∨ (bitwiseFlags (p := p) e.opcode)[2] = 1) ∧
    (bitwiseFlags (p := p) e.opcode)[0] + (bitwiseFlags (p := p) e.opcode)[1]
      + (bitwiseFlags (p := p) e.opcode)[2] = 1 := by
  obtain h | h | h := hop <;> simp [bitwiseFlags, h]

end SP1Clean.TraceGen

namespace SP1Clean.BitwiseChip

open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## The chip's honest-prover contract on a built row -/

/-- A routed, well-formed event satisfies the prover contract for arbitrary data and hints. -/
theorem proverAssumptions_of_event {e : ALUTypeEvent} (h : e.WellFormed) (hop : e.IsBitwise)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ProverAssumptions (e.toBitwiseInputs (p := p)) data hint := by
  obtain ⟨hf0, hf1, hf2, hsum⟩ := bitwiseFlags_spec (p := p) hop
  have hreal : (e.toBitwiseInputs (p := p)).is_real = 1 := hsum
  simp only [ProverAssumptions, hreal]
  refine ⟨?_, ?_, ?_, ?_, hf0, hf1, hf2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- the `rs1` read, then the `op_c` block's committed value — a u64 in *either* row form
  · exact wordOfNat_isU64 _
  · exact aluTypeOpCCols_prev_value_isU64 e
  -- the value the `op_a` write displaces
  · exact fun _ => wordOfNat_isU64 _
  -- the row is real
  · exact Or.inr trivial
  -- `rd ≠ x0`, so the `op_a_0` zeroing flag is off
  · exact aluTypeReaderCols_op_a_0_eq_zero h.opA_ne_zero
  -- exact register/immediate row form, with padding excluded by this real-row builder
  · rcases aluTypeReaderCols_imm_c_bool (p := p) h.immC_bool with h0 | h1
    · exact Or.inl h0
    · exact Or.inr ⟨trivial, h1⟩
  · exact aluTypeReaderCols_imm_copy (p := p) h.immC_bool
  -- the shared reader contracts: the state block, then the two unconditional register accesses
  · exact cpuState_spec e.clk e.pc h.clk_mod _ _ _
  · exact registerAccessCols_spec_opA h.clk_mod h.prevTsA_lt
  · exact registerAccessCols_spec_opB h.clk_mod h.prevTsB_lt
  -- the `op_c` access: an ordinary register read or the vacuous immediate block
  · simp only [ALUTypeEvent.toBitwiseInputs, aluTypeReaderCols_op_c_memory]
    exact aluTypeOpCCols_spec h.clk_mod h.immC_bool h.prevTsC_reg
  -- the decode bounds the Program-bus fetch carries
  · exact fun _ => ⟨aluTypeReaderCols_op_a_val_lt h.opA_lt, (cpuStateCols_pc_val_lt e.clk e.pc).1,
      (cpuStateCols_pc_val_lt e.clk e.pc).2.1, (cpuStateCols_pc_val_lt e.clk e.pc).2.2⟩
  -- G1: the three pulled prior records' 24-bit access clocks
  · exact fun _ => ⟨registerAccessCols_prevLow_val_lt _ _ _,
      registerAccessCols_prevLow_val_lt _ _ _, aluTypeOpCCols_prevLow_val_lt e⟩

omit [Fact (2 ^ 24 < p)] in
/-- Zero selectors and operands satisfy the complete padding contract for any hint. -/
theorem proverAssumptions_padding (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ProverAssumptions (bitwisePaddingInputs (p := p)) data hint := by
  have hzero : Word.isU64 (#v[0, 0, 0, 0] : Word (ZMod p)) :=
    Word.isU64_of_cases (by simp) (by simp) (by simp) (by simp)
  have hne : ¬((0 : ZMod p) = 1) := zero_ne_one
  have hreal : (bitwisePaddingInputs (p := p)).is_real = 0 := by simp [bitwisePaddingInputs]
  simp only [ProverAssumptions, hreal]
  refine ⟨hzero, hzero, fun hr => absurd hr hne, Or.inl trivial, Or.inl rfl, Or.inl rfl, Or.inl rfl,
    rfl, Or.inl rfl, by simp [bitwisePaddingInputs, zeroALUTypeReaderCols],
    fun hr => absurd hr hne, fun hr => absurd hr hne, fun hr => absurd hr hne, ?_,
    fun hr => absurd hr hne, fun hr => absurd hr hne⟩
  intro hr
  have h0 : (0 : ZMod p) = 1 := by rw [← sub_zero (0 : ZMod p)]; exact hr
  exact absurd h0 hne

/-! ## The built table -/

/-- The Bitwise chip as a flat-AIR component: one circuit, checked independently on each row.

A plain `def`, deliberately not an `abbrev` (see `AddChip.component` for the measurement). -/
def component : Air.Flat.Component (ZMod p) := { circuit := circuit }

/-- Real event inputs followed by all-zero padding inputs. -/
def traceInputs (events : List ALUTypeEvent) (padding : ℕ) : List (Inputs (ZMod p)) :=
  events.map ALUTypeEvent.toBitwiseInputs ++ List.replicate padding bitwisePaddingInputs

/-- Every event or padding input satisfies the chip's prover contract. -/
theorem proverAssumptions_of_mem_traceInputs {events : List ALUTypeEvent} {padding : ℕ}
    (h : ∀ e ∈ events, e.WellFormed ∧ e.IsBitwise) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) events padding, ProverAssumptions input data hint := by
  intro input hin
  rcases List.mem_append.mp hin with hin | hin
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
    exact proverAssumptions_of_event (h e he).1 (h e he).2 data hint
  · rw [List.eq_of_mem_replicate hin]
    exact proverAssumptions_padding data hint

/-- **A real trace builds a valid Bitwise table.** Every `assertZero` of the whole flattened chip
circuit evaluates to zero on every built row, and no static lookup is left unchecked. -/
theorem traceTable_constraints (events : List ALUTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p))
    (h : ∀ e ∈ events, e.WellFormed ∧ e.IsBitwise) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events padding) data (ProverHint.empty _)).Constraints data :=
  Air.Flat.Table.build_constraints _ _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data (ProverHint.empty _))

/-- The same table satisfies its **channel guarantees** — every message it pushes onto the State,
Memory, Program and Byte channels carries the payload its channel promises. -/
theorem traceTable_guarantees (events : List ALUTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p))
    (h : ∀ e ∈ events, e.WellFormed ∧ e.IsBitwise) :
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

end SP1Clean.BitwiseChip
