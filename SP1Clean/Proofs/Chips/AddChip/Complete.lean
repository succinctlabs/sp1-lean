import SP1Clean.FormalModel.TraceGen.Readers
import SP1Clean.Proofs.Chips.AddChip.Witgen
import ToClean.Air.TableBuild

/-! # `SP1Clean.AddChip` — from trace events to a valid AIR table (the completeness pilot)

The first instance of the **trace-generation** chain, end to end: a list of well-formed R-type ALU
trace events, run through the builder of `FormalModel/TraceGen/`, produces a flat-AIR table whose
constraints and channel guarantees hold. Nothing about the *row* is hand-built — only the
`size Inputs` committed input cells come from the event; every witnessed cell is computed by the
chip circuit's own witness generators (`Air.Flat.Component.buildRow`, in
`ToClean/Air/TableBuild.lean`).

The chain, and where each link lives:

1. `RTypeEvent.WellFormed` — plain-`ℕ` execution facts (`FormalModel/TraceGen/Events.lean`);
2. `RTypeEvent.toAddInputs` — the typed input row (`FormalModel/TraceGen/Inputs.lean`);
3. `proverAssumptions_of_event` — **this file**: the row satisfies the chip's honest-prover
   contract. Ten of its eleven conjuncts are one citation each of a shared lemma from
   `FormalModel/TraceGen/Readers.lean`; the eleventh (`is_real` is binary) is `Or.inr rfl`;
4. `AddChip.computableWitnesses` — witness generation is honest (`Witgen.lean`);
5. `Air.Flat.Table.build_constraints` / `build_guarantees` — the generic keystone.

Rolling the next chip of the family into this layer is steps 2 and 3 only: a three-field `def`
beside `toAddInputs`, and a copy of `proverAssumptions_of_event` with its chip's conjunct list.
-/

namespace SP1Clean.AddChip

open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## The chip's honest-prover contract on a built row -/

/--
**A well-formed trace event builds a row the honest prover can complete.** Every conjunct of
`AddChip.ProverAssumptions` at the built input row follows from `RTypeEvent.WellFormed`, with no
residual side condition — the reader `Spec`s from the shared lemmas, the operand `isU64`s from the
limb split (which is why the event owes no range facts), and the two `is_real`-gated bundles from
the decode bounds and the committed previous-access clocks.

The `data` and `hint` are arbitrary: `Add`'s prover contract reads neither (its witness payload is
`AddOperation.populateIR` over the input cells alone). That is what lets a whole table share one
committed `ProverData`.
-/
theorem proverAssumptions_of_event {e : RTypeEvent} (h : e.WellFormed)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ProverAssumptions (e.toAddInputs (p := p)) data hint := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- the two source operands, and the value the `op_a` write displaces: committed limb-wise, so
  -- `isU64` regardless of the event (`RTypeEvent.WellFormed` owes no limb bound)
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

/-- **A padding row satisfies the same contract.** SP1 pads a chip's trace to a power-of-two
height with zero rows, and `is_real = 0` makes every gated conjunct vacuous; what survives is the
two operand `isU64`s (ungated, since the prover needs them to witness the arithmetic on *any*
row), which the zero word satisfies. -/
theorem proverAssumptions_padding (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ProverAssumptions (addPaddingInputs (p := p)) data hint := by
  have hzero : Word.isU64 (#v[0, 0, 0, 0] : Word (ZMod p)) :=
    Word.isU64_of_cases (by simp) (by simp) (by simp) (by simp)
  have hne : ¬((0 : ZMod p) = 1) := zero_ne_one
  exact ⟨hzero, hzero, fun hr => absurd hr hne, Or.inl rfl, rfl, fun hr => absurd hr hne,
    fun hr => absurd hr hne, fun hr => absurd hr hne, fun hr => absurd hr hne,
    fun hr => absurd hr hne, fun hr => absurd hr hne⟩

/-! ## The built table -/

/-- The Add chip as a flat-AIR component: one circuit, checked independently on each row.

A plain `def`, deliberately not an `abbrev`: a reducible spelling makes the elaborator compare
`component.provableInput` against the derived `ProvableType Inputs` instance structurally (a
`whnf` blow-up on `ProvableStruct.combinedSize`), where the opaque one lets it iota-reduce the
projection instead. Same shape as the perf doctrine's "make dangerous values opaque". -/
def component : Air.Flat.Component (ZMod p) := ⟨circuit⟩

/-- The rows a trace builds: one input row per event, then `padding` zero rows. Kept as a
definition so the theorems below share one spelling. -/
def traceInputs (events : List RTypeEvent) (padding : ℕ) : List (Inputs (ZMod p)) :=
  events.map RTypeEvent.toAddInputs ++ List.replicate padding addPaddingInputs

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

/--
**The pilot theorem: a real trace builds a valid Add table.** For any list of well-formed R-type
ALU events and any amount of zero padding, the table assembled by `Air.Flat.Table.build` — input
cells from the events, every witnessed cell computed by the chip's own generators, one shared
committed `ProverData` — satisfies `Air.Flat.Table.Constraints`: every `assertZero` of the whole
flattened chip circuit (gadget arithmetic, boolean gates, reader glue, chip-owned tail) evaluates
to zero on every row, and no static lookup is left unchecked.
-/
theorem traceTable_constraints (events : List RTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) (h : ∀ e ∈ events, e.WellFormed) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events padding) data
      hint).Constraints :=
  Air.Flat.Table.build_constraints _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

/-- The same table satisfies its **channel guarantees** — every message it pushes onto the State,
Memory, Program and Byte channels carries the payload its channel promises. This is the half of
the row's assertion system the bus/balance layer consumes. -/
theorem traceTable_guarantees (events : List RTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) (h : ∀ e ∈ events, e.WellFormed) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events padding) data
      hint).Guarantees :=
  Air.Flat.Table.build_guarantees _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

/-- The table's interaction list on a channel, in closed form: the per-row evaluated interactions,
concatenated in row order. Downstream ledger/balance reasoning reads this instead of unfolding the
built rows again. -/
theorem traceTable_interactionsWith (events : List RTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) (channel : RawChannel (ZMod p)) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events padding) data
        hint).interactionsWith channel =
      (traceInputs (p := p) events padding).flatMap fun input =>
        (component (p := p)).operations.interactionValuesWith channel
          (Environment.fromArray ((component (p := p)).buildRow input data hint) data) :=
  Air.Flat.Table.build_interactions _ _ _ _ channel

end SP1Clean.AddChip
