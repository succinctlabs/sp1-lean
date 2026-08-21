import SP1Clean.FormalModel.TraceGen.Readers
import SP1Clean.Proofs.Chips.SubwChip.Witgen
import ToClean.Air.TableBuild

/-! # `SP1Clean.SubwChip` — from trace events to a valid AIR table

The third chip of the **R-type** family through the trace-generation chain (see
`AddChip/Complete.lean` for the programme note). `Subw` is a `W`-instruction — its arithmetic block
witnesses two low limbs plus a sign bit, and the word the reader writes for `rd` is the
sign-extended result — but *none of that reaches the input row*: the committed input cells are the
`is_real` selector and the same two reader blocks `Add`/`Sub` commit, and the sign extension is
computed by the chip's own witness generators. So the eleven conjuncts, and their discharges, are
identical to `SubChip`'s.

Every one of the eleven bullets is a single citation — ten of a shared lemma from
`FormalModel/TraceGen/Readers.lean`, one of `Or.inr rfl`. -/

namespace SP1Clean.SubwChip

open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## The chip's honest-prover contract on a built row -/

/--
**A well-formed trace event builds a row the honest prover can complete.** Every conjunct of
`SubwChip.ProverAssumptions` at the built input row follows from `RTypeEvent.WellFormed`, with no
residual side condition.

The `data` and `hint` are arbitrary: `Subw`'s prover contract reads neither.
-/
theorem proverAssumptions_of_event {e : RTypeEvent} (h : e.WellFormed)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ProverAssumptions (e.toSubwInputs (p := p)) data hint := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- the two source operands, and the value the `op_a` write displaces: committed limb-wise, so
  -- `isU64` regardless of the event
  · exact wordOfNat_isU64 _
  · exact wordOfNat_isU64 _
  · exact fun _ => wordOfNat_isU64 _
  -- the row is real
  · exact Or.inr rfl
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

/-- **A padding row satisfies the same contract.** `is_real = 0` makes every gated conjunct
vacuous; what survives is the two operand `isU64`s, which the zero word satisfies. -/
theorem proverAssumptions_padding (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ProverAssumptions (subwPaddingInputs (p := p)) data hint := by
  have hzero : Word.isU64 (#v[0, 0, 0, 0] : Word (ZMod p)) :=
    Word.isU64_of_cases (by simp) (by simp) (by simp) (by simp)
  have hne : ¬((0 : ZMod p) = 1) := zero_ne_one
  exact ⟨hzero, hzero, fun hr => absurd hr hne, Or.inl rfl, rfl, fun hr => absurd hr hne,
    fun hr => absurd hr hne, fun hr => absurd hr hne, fun hr => absurd hr hne,
    fun hr => absurd hr hne, fun hr => absurd hr hne⟩

/-! ## The built table -/

/-- The Subw chip as a flat-AIR component: one circuit, checked independently on each row.

A plain `def`, deliberately not an `abbrev` (see `AddChip.component` for the measurement). -/
def component : Air.Flat.Component (ZMod p) := ⟨circuit⟩

/-- The rows a trace builds: one input row per event, then `padding` zero rows. -/
def traceInputs (events : List RTypeEvent) (padding : ℕ) : List (Inputs (ZMod p)) :=
  events.map RTypeEvent.toSubwInputs ++ List.replicate padding subwPaddingInputs

/-- Every row of a built trace — event row or padding row — satisfies the chip's honest-prover
contract. -/
theorem proverAssumptions_of_mem_traceInputs {events : List RTypeEvent} {padding : ℕ}
    (h : ∀ e ∈ events, e.WellFormed) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) events padding, ProverAssumptions input data hint := by
  intro input hin
  rcases List.mem_append.mp hin with hin | hin
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
    exact proverAssumptions_of_event (h e he) data hint
  · rw [List.eq_of_mem_replicate hin]
    exact proverAssumptions_padding data hint

/-- **A real trace builds a valid Subw table.** Every `assertZero` of the whole flattened chip
circuit evaluates to zero on every built row, and no static lookup is left unchecked. -/
theorem traceTable_constraints (events : List RTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) (h : ∀ e ∈ events, e.WellFormed) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events padding) data
      hint).Constraints :=
  Air.Flat.Table.build_constraints _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

/-- The same table satisfies its **channel guarantees** — every message it pushes onto the State,
Memory, Program and Byte channels carries the payload its channel promises. -/
theorem traceTable_guarantees (events : List RTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) (h : ∀ e ∈ events, e.WellFormed) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events padding) data
      hint).Guarantees :=
  Air.Flat.Table.build_guarantees _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

/-- The table's interaction list on a channel, in closed form: the per-row evaluated interactions,
concatenated in row order. -/
theorem traceTable_interactionsWith (events : List RTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) (channel : RawChannel (ZMod p)) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events padding) data
        hint).interactionsWith channel =
      (traceInputs (p := p) events padding).flatMap fun input =>
        (component (p := p)).operations.interactionValuesWith channel
          (Environment.fromArray ((component (p := p)).buildRow input data hint) data) :=
  Air.Flat.Table.build_interactions _ _ _ _ channel

end SP1Clean.SubwChip
