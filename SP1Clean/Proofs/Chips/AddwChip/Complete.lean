import SP1Clean.FormalModel.TraceGen.Readers
import SP1Clean.Proofs.Chips.AddwChip.Witgen
import ToClean.Air.TableBuild

/-! # `SP1Clean.AddwChip` — from trace events to a valid AIR table (the ALU-type template)

The first chip of the **ALU-type** family through the trace-generation chain (see
`AddChip/Complete.lean` for the programme note). `Addw` reads `Extracted.ALUTypeReader`: the
immediate-capable ALU adapter, whose `op_c` slot is a committed four-limb word *plus* an access
block, with the committed `imm_c` flag selecting which of the two forms the row is in.

What changes from the R-type template:

- the `op_c` access block is `TraceGen.aluTypeOpCCols`, which **branches** on `immC`; and
- the reader's `op_c` guarantee is gated by `is_real - imm_c` rather than by `is_real`.

Neither reaches the shared lemmas: `registerAccessCols_spec_opC` takes its `is_real` argument
arbitrarily, so the changed gate costs nothing, and the branch is resolved once by
`aluTypeOpCCols_of_reg`.

**Both ALU row forms.** `AddwChip.ProverAssumptions` now carries the exact two-form invariant:
`imm_c = 0` for register ADDW, or `is_real = 1 ∧ imm_c = 1` for ADDIW. The shared builder proves
the immediate-copy gates and the row-dependent op_c timestamp contract once, so this table theorem
covers both dispatches without an external `immC = 0` cap. -/

namespace SP1Clean.AddwChip

open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## The chip's honest-prover contract on a built row -/

/--
**A well-formed ADDW/ADDIW trace event builds a row the honest prover can complete.** Every
conjunct of `AddwChip.ProverAssumptions` at the built input row follows from
`ALUTypeEvent.WellFormed`, with no residual side condition.

The `data` and `hint` are arbitrary: `Addw`'s prover contract reads neither.
-/
theorem proverAssumptions_of_event {e : ALUTypeEvent} (h : e.WellFormed)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ProverAssumptions (e.toAddwInputs (p := p)) data hint := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- the `rs1` read, then the `op_c` block's committed value — a u64 in *either* row form, since
  -- both branches of `aluTypeOpCCols` commit a `wordOfNat`
  · exact wordOfNat_isU64 _
  · exact aluTypeOpCCols_prev_value_isU64 e
  -- the value the `op_a` write displaces
  · exact fun _ => wordOfNat_isU64 _
  -- the row is real
  · exact Or.inr rfl
  -- `rd ≠ x0`, so the `op_a_0` zeroing flag is off
  · exact aluTypeReaderCols_op_a_0_eq_zero h.opA_ne_zero
  -- the exact two-form invariant: the built row is real, so either committed selector value is legal
  · rcases aluTypeReaderCols_imm_c_bool (p := p) h.immC_bool with h0 | h1
    · exact Or.inl h0
    · exact Or.inr ⟨rfl, h1⟩
  -- immediate rows copy the committed operand into the synthetic op_c access block; register rows
  -- satisfy the same four gates because their selector is zero
  · exact aluTypeReaderCols_imm_copy (p := p) h.immC_bool
  -- the shared reader contracts: the state block, then the two unconditional register accesses
  · exact cpuState_spec e.clk e.pc h.clk_mod _ _ _
  · exact registerAccessCols_spec_opA h.clk_mod h.prevTsA_lt
  · exact registerAccessCols_spec_opB h.clk_mod h.prevTsB_lt
  -- the `op_c` access: an ordinary `rs2` read for ADDW, vacuous for ADDIW
  · rw [ALUTypeEvent.toAddwInputs_adapter, aluTypeReaderCols_op_c_memory]
    exact aluTypeOpCCols_spec h.clk_mod h.immC_bool h.prevTsC_reg
  -- the decode bounds the Program-bus fetch carries
  · exact fun _ => ⟨aluTypeReaderCols_op_a_val_lt h.opA_lt, (cpuStateCols_pc_val_lt e.clk e.pc).1,
      (cpuStateCols_pc_val_lt e.clk e.pc).2.1, (cpuStateCols_pc_val_lt e.clk e.pc).2.2⟩
  -- G1: the three pulled prior records' 24-bit access clocks (the `op_c` one holds in both row
  -- forms, so it needs no `himm`)
  · exact fun _ => ⟨registerAccessCols_prevLow_val_lt _ _ _,
      registerAccessCols_prevLow_val_lt _ _ _, aluTypeOpCCols_prevLow_val_lt e⟩

/-- **A padding row satisfies the same contract.** `is_real = 0` makes every gated conjunct
vacuous — including the `op_c` reader gate, which on a zero row is `0 - 0`. What survives is the
two operand `isU64`s and the two zero flags. -/
theorem proverAssumptions_padding (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ProverAssumptions (addwPaddingInputs (p := p)) data hint := by
  have hzero : Word.isU64 (#v[0, 0, 0, 0] : Word (ZMod p)) :=
    Word.isU64_of_cases (by simp) (by simp) (by simp) (by simp)
  have hne : ¬((0 : ZMod p) = 1) := zero_ne_one
  refine ⟨hzero, hzero, fun hr => absurd hr hne, Or.inl rfl, rfl, Or.inl rfl,
    by simp [addwPaddingInputs, zeroALUTypeReaderCols],
    fun hr => absurd hr hne, fun hr => absurd hr hne, fun hr => absurd hr hne, ?_,
    fun hr => absurd hr hne, fun hr => absurd hr hne⟩
  intro hr
  have h0 : (0 : ZMod p) = 1 := by rw [← sub_zero (0 : ZMod p)]; exact hr
  exact absurd h0 hne

/-! ## The built table -/

/-- The Addw chip as a flat-AIR component: one circuit, checked independently on each row.

A plain `def`, deliberately not an `abbrev` (see `AddChip.component` for the measurement). -/
def component : Air.Flat.Component (ZMod p) := ⟨circuit⟩

/-- The rows a trace builds: one input row per event, then `padding` zero rows. -/
def traceInputs (events : List ALUTypeEvent) (padding : ℕ) : List (Inputs (ZMod p)) :=
  events.map ALUTypeEvent.toAddwInputs ++ List.replicate padding addwPaddingInputs

/-- Every row of a built trace — ADDW, ADDIW, or padding — satisfies the chip's honest-prover
contract. -/
theorem proverAssumptions_of_mem_traceInputs {events : List ALUTypeEvent} {padding : ℕ}
    (h : ∀ e ∈ events, e.WellFormed) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) events padding, ProverAssumptions input data hint := by
  intro input hin
  rcases List.mem_append.mp hin with hin | hin
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
    exact proverAssumptions_of_event (h e he) data hint
  · rw [List.eq_of_mem_replicate hin]
    exact proverAssumptions_padding data hint

/-- **A real trace builds a valid Addw table.** Every `assertZero` of the whole flattened chip
circuit evaluates to zero on every built row, and no static lookup is left unchecked. -/
theorem traceTable_constraints (events : List ALUTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (h : ∀ e ∈ events, e.WellFormed) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events padding) data
      hint).Constraints :=
  Air.Flat.Table.build_constraints _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

/-- The same table satisfies its **channel guarantees** — every message it pushes onto the State,
Memory, Program and Byte channels carries the payload its channel promises. -/
theorem traceTable_guarantees (events : List ALUTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (h : ∀ e ∈ events, e.WellFormed) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events padding) data
      hint).Guarantees :=
  Air.Flat.Table.build_guarantees _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

/-- The table's interaction list on a channel, in closed form: the per-row evaluated interactions,
concatenated in row order. -/
theorem traceTable_interactionsWith (events : List ALUTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) (channel : RawChannel (ZMod p)) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events padding) data
        hint).interactionsWith channel =
      (traceInputs (p := p) events padding).flatMap fun input =>
        (component (p := p)).operations.interactionValuesWith channel
          (Environment.fromArray ((component (p := p)).buildRow input data hint) data) :=
  Air.Flat.Table.build_interactions _ _ _ _ channel

end SP1Clean.AddwChip
