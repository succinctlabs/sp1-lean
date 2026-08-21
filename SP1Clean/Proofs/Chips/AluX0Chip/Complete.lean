import SP1Clean.FormalModel.TraceGen.Readers
import SP1Clean.Proofs.Chips.AluX0Chip.Witgen
import ToClean.Air.TableBuild

/-! # `SP1Clean.AluX0Chip` — from trace events to a valid AIR table

The `rd = x0` form of every ALU instruction through the trace-generation chain (see
`AddChip/Complete.lean` for the programme note). `AluX0` reads `Extracted.ALUTypeReader` — the same
block `Addw`/`Bitwise`/`Lt`/the shifts read — but through the **immutable** adapter: `op_a` is a
discarded source read, not a destination write, because RISC-V throws the result away.

Two things are new here, and both are the routing condition.

1. **The event class is the inverted one.** `ALUTypeEvent.WellFormed` demands `rd ≠ x0`; that is the
   condition which sends an ALU event to `Add`/`Addw`/`Bitwise`/… in the first place. An `AluX0`
   event is exactly the complement, so it needs its own predicate — `ALUTypeEvent.WellFormedX0`,
   which asserts `rd = x0` and, in its place, the fact that makes the immutable adapter's four
   `op_a_0 · prev_value_i = 0` gates hold: **`x0` reads as zero**. This is the third instance of the
   pattern `MemoryEvent.WellFormedX0` and `MemoryEvent.WellFormedStore` already record — a shared
   record's `opA ≠ 0` conjunct is a *routing* fact, never a structural one.
2. **One chip, every ALU opcode.** `AluX0` commits a single dynamic `opcode` column instead of a
   flag per variant, and range-checks it with an LTU byte pull against `Opcode::LB = 29`, the first
   non-ALU discriminant. So `WellFormedX0` carries `opcode < 29` — the other half of the routing
   condition, and the only conjunct of this chip's contract that is not shared reader machinery.

Nothing else is new: five of the six `ProverAssumptions` bullets are one citation each, and the
sixth is the built `opcode` column's cast. The chip witnesses **no** cells at all (`Witgen.lean`),
so the built row is literally its input.
-/

namespace SP1Clean.TraceGen

variable {p : ℕ}

/-- The `AluX0` chip's committed input row for one event — a **real** row (`is_real = 1`). The
committed `opcode` column is the event's own executor discriminant; the two block fields are the
shared builders. (Defined here rather than in `Inputs.lean` because `AluX0Chip.Inputs` is
Native-resident — the "Spec homing" layering exception `docs/architecture.md` records, and the same
reason `MemoryEvent.toLoadX0Inputs` sits in `LoadX0Chip/Complete.lean`.) -/
def ALUTypeEvent.toAluX0Inputs (e : ALUTypeEvent) : AluX0Chip.Inputs (ZMod p) where
  state := cpuStateCols e.clk e.pc
  adapter := aluTypeReaderCols e
  opcode := ((e.opcode : ℕ) : ZMod p)
  is_real := 1

lemma ALUTypeEvent.toAluX0Inputs_opcode (e : ALUTypeEvent) :
    (e.toAluX0Inputs (p := p)).opcode = ((e.opcode : ℕ) : ZMod p) := rfl

/-- The `AluX0` chip's padding row: every column zero, `is_real = 0`. -/
def aluX0PaddingInputs : AluX0Chip.Inputs (ZMod p) where
  state := zeroCPUStateCols
  adapter := zeroALUTypeReaderCols
  opcode := 0
  is_real := 0

end SP1Clean.TraceGen

namespace SP1Clean.AluX0Chip

open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## The chip's honest-prover contract on a built row -/

/--
**A well-formed `x0`-destination ALU event builds a row the honest prover can complete.** Every
conjunct of `AluX0Chip.ProverAssumptions` at the built input row follows from
`ALUTypeEvent.WellFormedX0`, with no residual side condition.

The `data` and `hint` are arbitrary: `AluX0`'s prover contract reads neither — it has no witness
payload at all.
-/
theorem proverAssumptions_of_event {e : ALUTypeEvent} (h : e.WellFormedX0)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ProverAssumptions (e.toAluX0Inputs (p := p)) data hint := by
  have hp : 2 ^ 24 < p := Fact.out
  have hA : e.opA = 0 := h.opA_eq_zero
  have hop : e.opcode < 29 := h.opcode_lt
  -- `rd = x0`, so the `op_a_0` flag is **on** — the inverse of every other ALU chip
  have hone : (aluTypeReaderCols (p := p) e).op_a_0 = 1 :=
    aluTypeReaderCols_op_a_0_eq_one h.opA_eq_zero
  refine ⟨Or.inr rfl, ?_, ?_, cpuState_spec e.clk e.pc h.clk_mod _ _ _, ?_, ?_⟩
  -- the two `op_a_0` forcing gates: on a real row the flag is `1`, off padding it is `0`
  · rw [show (e.toAluX0Inputs (p := p)).adapter.op_a_0 = (aluTypeReaderCols (p := p) e).op_a_0 from
      rfl, hone, sub_self, mul_zero]
  · rw [show isReal (e.toAluX0Inputs (p := p)) = 1 from rfl, sub_self, zero_mul]
  -- the immutable ALU adapter's whole contract, from the event's execution facts
  · exact aluTypeReaderImmutable_spec h.clk_mod (by omega) (fun _ => h.prevA_eq_zero) h.immC_bool
      h.prevTsA_lt h.prevTsB_lt h.prevTsC_reg _ _ _
  -- the dynamic opcode is an ALU opcode — the LTU byte pull's witness
  · intro _
    rw [ALUTypeEvent.toAluX0Inputs_opcode, ZMod.val_natCast_of_lt (by omega)]
    exact h.opcode_lt

/-- **A padding row satisfies the same contract.** `is_real = 0` makes every gated conjunct
vacuous — including both `op_a_0` forcing gates, which on a zero row read `0 · (0 - 1)` and
`(0 - 1) · 0`. Nothing survives ungated. -/
theorem proverAssumptions_padding (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ProverAssumptions (aluX0PaddingInputs (p := p)) data hint := by
  refine ⟨Or.inl rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [aluX0PaddingInputs, isReal, clkLow, zeroALUTypeReaderCols, zeroAccessCols,
      zeroCPUStateCols, Readers.CPUState.Spec, Readers.ALUTypeReaderImmutable.Spec,
      Readers.RegisterAccessCols.Spec, Readers.RegisterAccessTimestamp.Spec]

/-! ## The built table -/

/-- The AluX0 chip as a flat-AIR component: one circuit, checked independently on each row.

A plain `def`, deliberately not an `abbrev` (see `AddChip.component` for the measurement). -/
def component : Air.Flat.Component (ZMod p) := ⟨circuit⟩

/-- The rows a trace builds: one input row per event, then `padding` zero rows. -/
def traceInputs (events : List ALUTypeEvent) (padding : ℕ) : List (Inputs (ZMod p)) :=
  events.map ALUTypeEvent.toAluX0Inputs ++ List.replicate padding aluX0PaddingInputs

/-- Every row of a built trace — event row or padding row — satisfies the chip's honest-prover
contract. -/
theorem proverAssumptions_of_mem_traceInputs {events : List ALUTypeEvent} {padding : ℕ}
    (h : ∀ e ∈ events, e.WellFormedX0) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) events padding, ProverAssumptions input data hint := by
  intro input hin
  rcases List.mem_append.mp hin with hin | hin
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
    exact proverAssumptions_of_event (h e he) data hint
  · rw [List.eq_of_mem_replicate hin]
    exact proverAssumptions_padding data hint

/-- **A real trace builds a valid AluX0 table.** Every `assertZero` of the whole flattened chip
circuit evaluates to zero on every built row, and no static lookup is left unchecked. -/
theorem traceTable_constraints (events : List ALUTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (h : ∀ e ∈ events, e.WellFormedX0) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events padding) data
      hint).Constraints :=
  Air.Flat.Table.build_constraints _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

/-- The same table satisfies its **channel guarantees** — every message it pushes onto the State,
Memory, Program and Byte channels carries the payload its channel promises. -/
theorem traceTable_guarantees (events : List ALUTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (h : ∀ e ∈ events, e.WellFormedX0) :
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

end SP1Clean.AluX0Chip
