import SP1Clean.FormalModel.TraceGen.AluGenerator
import SP1Clean.Proofs.Completeness.Assembly

/-!
# The generated ALU stream reaches the chip tables

Where the fold lands. `FormalModel/TraceGen/AluGenerator.lean` turns a shard's ALU steps into an
`RTypeEvent` stream and proves every event well-formed; the R-type chips' `traceTable_constraints`
theorems turn a well-formed event list into a table that satisfies its constraint system. Composing
them is one line per chip, and the point of writing it down is the *shape of the hypotheses*: they
are all about the steps — a 48-bit pc, 64-bit register contents, a non-`x0` destination — plus the
generator's own bookkeeping invariant. Nothing about rows, limbs, ranges or witness cells survives
to this level.

That is the property the whole trace-generation layer exists to have, and it is worth being able to
read it off one statement.

The composition lives here rather than beside the fold because `Proofs/Chips/<X>/Complete.lean`
imports the trace layer; going back the other way would be a cycle. Same stratum, one direction.
-/

namespace SP1Clean.Soundness

open SP1Clean.TraceGen
open Air.Flat (Table)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- **A generated ALU stream builds a satisfying `Add` table.** -/
theorem aluEvents_addTable_constraints (g : GenState) (clk : ℕ) (steps : List AluStep)
    (hb : g.Bounded (clk + Semantics.regCOffset)) (hclk : clk % Semantics.ordinaryClkInc = 1)
    (hs : ∀ s ∈ steps, s.WellFormed) (padding : ℕ)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (Table.build (AddChip.component (p := p))
      (AddChip.traceInputs (aluEvents g clk steps) padding) data hint).Constraints :=
  AddChip.traceTable_constraints _ _ _ _ (aluEvents_wellFormed steps g clk hb hclk hs)

/-- The same table satisfies its channel guarantees, so the messages it pushes carry the payloads
the buses promise. -/
theorem aluEvents_addTable_guarantees (g : GenState) (clk : ℕ) (steps : List AluStep)
    (hb : g.Bounded (clk + Semantics.regCOffset)) (hclk : clk % Semantics.ordinaryClkInc = 1)
    (hs : ∀ s ∈ steps, s.WellFormed) (padding : ℕ)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (Table.build (AddChip.component (p := p))
      (AddChip.traceInputs (aluEvents g clk steps) padding) data hint).Guarantees :=
  AddChip.traceTable_guarantees _ _ _ _ (aluEvents_wellFormed steps g clk hb hclk hs)

/-- **`Sub` too** — the R-type family shares the adapter, so the fold serves every chip in it
without a per-chip generator. Stated for a second chip precisely to make that visible. -/
theorem aluEvents_subTable_constraints (g : GenState) (clk : ℕ) (steps : List AluStep)
    (hb : g.Bounded (clk + Semantics.regCOffset)) (hclk : clk % Semantics.ordinaryClkInc = 1)
    (hs : ∀ s ∈ steps, s.WellFormed) (padding : ℕ)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (Table.build (SubChip.component (p := p))
      (SubChip.traceInputs (aluEvents g clk steps) padding) data hint).Constraints :=
  SubChip.traceTable_constraints _ _ _ _ (aluEvents_wellFormed steps g clk hb hclk hs)

end SP1Clean.Soundness
