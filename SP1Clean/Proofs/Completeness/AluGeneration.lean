import SP1Clean.FormalModel.TraceGen.SailAlu
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


/-! ## End to end: from an execution to satisfying tables

The composition the whole phase was for. Read the ALU steps off a run, fold them into events, build
the chip tables, and every constraint holds.

Read the hypotheses, because they are the claim's real content:

* `hpc` / `hpres` — the program counter stays inside SP1's 48-bit address space. Supplied as an
  invariant the caller must show is preserved by stepping, because it is a fact about the *program*
  and not about the ISA. Nothing weaker would do: the pc limbs are three u16 columns.
* `hrd` — the decoder routes no `x0`-destination row here. A routing condition; those rows are the
  `AluX0` chip's.
* `decode` itself is a **parameter**. That is where the current program restriction lives:
  `Model/SailDecode.lean`'s witnesses are each for one hard-coded 32-bit word, so any instantiation
  inherits whatever restriction those impose. Keeping it abstract puts that restriction in the
  caller's statement, where it can be read, rather than inside the generator.

What is *not* a hypothesis is worth noting too. The three 64-bit register-content bounds are
structural (Sail registers are `BitVec 64`), the register-index bounds are structural (`BitVec 5`),
the clock discipline propagates from genesis, and the timestamp ordering is the fold's invariant. -/

/-- **Every ALU row a run generates satisfies the `Add` chip's constraint system.** -/
theorem sailRun_addTable_constraints
    {decode : SailState → Option AluDecoded} {P : SailState → Prop}
    (hpc : ∀ s, P s → ∀ v, s.regs.get? LeanRV64D.Defs.Register.PC = some v → v.toNat < 2 ^ 48)
    (hpres : ∀ s s', P s → Machine.stepOnce s = some s' → P s')
    (hrd : ∀ s d, decode s = some d → d.2.1 ≠ 0)
    (n : ℕ) (s : SailState) (hP : P s) (padding : ℕ)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (Table.build (AddChip.component (p := p))
      (AddChip.traceInputs
        (aluEvents GenState.initial 1 (aluStepsFrom decode s n)) padding) data hint).Constraints :=
  aluEvents_addTable_constraints _ _ _ initial_bounded_at_genesis (by norm_num)
    (aluStepsFrom_wellFormed hpc hpres hrd n s hP) padding data hint

/-- The same run's `Sub` table. The R-type family shares one adapter, so one generator serves it. -/
theorem sailRun_subTable_constraints
    {decode : SailState → Option AluDecoded} {P : SailState → Prop}
    (hpc : ∀ s, P s → ∀ v, s.regs.get? LeanRV64D.Defs.Register.PC = some v → v.toNat < 2 ^ 48)
    (hpres : ∀ s s', P s → Machine.stepOnce s = some s' → P s')
    (hrd : ∀ s d, decode s = some d → d.2.1 ≠ 0)
    (n : ℕ) (s : SailState) (hP : P s) (padding : ℕ)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (Table.build (SubChip.component (p := p))
      (SubChip.traceInputs
        (aluEvents GenState.initial 1 (aluStepsFrom decode s n)) padding) data hint).Constraints :=
  aluEvents_subTable_constraints _ _ _ initial_bounded_at_genesis (by norm_num)
    (aluStepsFrom_wellFormed hpc hpres hrd n s hP) padding data hint

/-- **The generated table is no taller than the run is long** — the shard-size fact. -/
theorem sailRun_rows_le (decode : SailState → Option AluDecoded) (n : ℕ) (s : SailState) :
    (aluStepsFrom decode s n).length ≤ n :=
  aluStepsFrom_length_le decode n s

end SP1Clean.Soundness
