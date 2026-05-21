# Clean Pilot — Friendly Introduction

If you've been working in `SP1Chips/` and `SP1Operations/` and you've
heard people mention "Clean" or "the pilot" or "SP1Clean" without
quite knowing what they're talking about, this is the doc for you.
The goal is to give a friendly tour of what's there now, why it
exists alongside the existing formalization, and what the people
working on it think it might unlock down the road. Once you've
read this, the roadmap (`docs/CLEAN_PILOT_ROADMAP.md`) and the
per-iteration retros (`CLEAN_PILOT_NOTES.md`, `CLEAN_PILOT_ITER2.md`
… `ITER4.md`) will read as concrete next steps rather than a
mystery vocabulary.

## The 30-second version

`SP1Clean/` is a parallel formalization of every SP1 instruction
chip, written in the **Clean DSL** ([Verified-zkEVM/clean](https://github.com/Verified-zkEVM/clean),
cloned at `../clean`). It does not replace anything in `SP1Chips/`
or `SP1Operations/` — both libraries build, both pass, and SP1's
`correct_*` Sail-equivalence theorems still flow through the original
constraint-compiler output. SP1Clean sits next to them, exporting
the same chip as a Clean `FormalAssertion` bundle and bridging back
to SP1 via per-chip `iff_sp1` lemmas.

The pilot exists to test whether Clean's modeling primitives are a
better long-term home for the constraint layer — better at catching
soundness/completeness bugs, better at exporting to a real prover
(Plonky3), and better at separating "the spec of what this chip
does" from "the column layout SP1 happens to emit." So far the
answer is: **promising on small chips, not yet proven on heavy
chips, with three identified frictions that need infrastructure
work before scaling further.**

## What "existing formalization" means in this repo

A reminder of the moving parts before contrasting them with Clean.
Every SP1 instruction follows the same three-step recipe:

```
SP1Chips/<Chip>/Constraints.lean    -- auto-generated constraint list
  ↓
SP1Chips/<Chip>Chip.lean            -- spec_<op> / sp1_<op> / correct_<op>
  ↑                                    (calls into Sail via SailM)
SP1Operations/Operation/<Op>.lean   -- reusable arithmetic fragments
SP1Operations/Reader/<Reader>.lean  -- decoder fragments (R-type, I-type, …)
```

The chip's `constraints` function is a `Vector (Fin KB) N →
SP1ConstraintList`. It's a flat list of `assertZero` / `send` /
`receive` items, one per logical AIR constraint. The compiler emits
it; we don't hand-edit between the markers; `correct_*` proves that
when those constraints hold, the chip behaves identically to the
Sail RISC-V semantics.

This works. Every chip has a `correct_*` theorem. The proofs are
sometimes hard — DivRem and ShiftLeft needed weeks of `_poly`
restructuring — but the pattern is mechanical and the scaffolding
is well understood. **Nothing in the Clean pilot changes any of
this.**

## What SP1Clean adds

SP1Clean takes the same per-chip information and re-expresses it
in a different shape. Three ingredients matter:

**1. Structured columns instead of flat indices.** SP1's `Main[k]`
indexing is a flat 33-element vector for `AddChip`. SP1Clean defines
an `AddCols` record with named fields — `op_a`, `op_b_memory_prev_value`,
`pc : Vector _ 3`, etc. — and writes the chip's `Spec` over that
record. The same data, viewed through field names instead of
hand-counted offsets. Compare:

```lean
-- SP1Chips/Add/Constraints.lean (excerpt)
[ assertZero (Main[28] + Main[15] - Main[22] * 65536⁻¹ * 65536 ...) , ...

-- SP1Clean/AddChip.lean
def Spec (cols : AddCols (ZMod p)) : Prop :=
  SP1Clean.AddOp.Spec
      cols.op_b_memory_prev_value cols.op_c_memory_prev_value
      cols.op_a_write_value ∧
  SP1Clean.CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 ∧ ...
```

A `fromMain : Vector (ZMod p) 33 → AddCols (ZMod p)` projects raw
indices into the structured view exactly once, at the bridge layer.
After that, no proof ever mentions `Main[28]` again.

**2. A pair of theorems instead of one.** SP1's `correct_*` theorem
says "if the constraints hold, the chip matches Sail." That's
**soundness only.** Clean's `FormalAssertion` bundles soundness
*and completeness* — a proof that for every input satisfying the
chip's `Spec`, you can write witnesses such that the constraints
hold. Without completeness, a chip could be vacuous (over-constrained,
never satisfiable) and `correct_*` would still pass.

SP1's existing approach doesn't surface completeness as a separate
lemma — the practical answer is "the prover generates witnesses, the
prover tests run, regressions get caught" — but the formal artifact
is missing. Clean makes it a first-class theorem with its own proof
obligation. Today, the 13 promoted chips and operations carry both
sides; the rest still rely on the SP1 side's structural correctness.

**3. A composable interaction layer.** SP1 has four interaction kinds
(`byte`, `state`, `memory`, `program`) modeled as
`AirInteraction` constructors, with multiplicities tracked
declaratively. Clean uses `lookup`-against-`Table` and (separately)
`Channel.emit`/`push`/`pull` for state-bus interactions. The pilot
chose **stateless lookups** for byte/state/program — they're enough
for the per-chip soundness story under `is_real = 1`. Memory
interactions are aggregated *trace-level* through
`Clean.Utils.OfflineMemory`, which handles the timestamp-ordering
discipline that SP1's per-row sends can't enforce locally.

If that sounds abstract: SP1's `memory` send says "I read this
address at this timestamp." Soundness over a single row says
nothing about consistency across rows. The Clean DSL provides a
machine-checked aggregator that turns per-row claims into a
trace-level "every memory access is consistent" property, with the
proof discharged once at the library level. **None** of this exists
in `SP1Chips/`'s formalization today — `SP1Chips/Soundness.lean`
sketches the analogue but the cross-row arguments are largely
informal.

## The bridge: how SP1Clean and SP1Chips stay in sync

SP1Clean isn't a fork or a rewrite — it imports the SP1 side
directly and uses its lemmas. Every promoted chip's bridge follows
the same pattern:

```lean
-- SP1Clean/AddChip.lean (Layer 2, ~50 lines)
theorem iff_sp1 (Main : Vector (ZMod p) 33) (h_is_real : Main[32] = 1) :
    (_root_.Add.constraints Main).allHold ↔ Spec (fromMain Main) := by
  simp only [fromMain, Spec, ...]
  rw [...]   -- unpack the constraint list
  rw [AddOperation.allHold_constraints_iff a b cols]   -- <- SP1 lemma reused
  rw [cpuStateSpec_iff_sp1, rtypeReaderSpec_iff_sp1]   -- <- subbridges
  -- close arithmetic
```

The key clause is the third line: `AddOperation.allHold_constraints_iff`
is **the SP1-side lemma** — proved once in
`SP1Operations/Operation/AddOperation.lean`, never re-proved in
SP1Clean. The Clean side just re-expresses the same statement in
terms of a record-valued `Spec` and calls back into the existing
proof.

This is the discipline the roadmap calls "three-layer bridging":

- **Layer 0** — SP1's `_poly` lemmas (the genuinely hard arithmetic
  proofs for DivRem, ShiftLeft, Mul). **Never duplicated.** Clean
  reuses them.
- **Layer 1** — operation-level `iff_sp1` in SP1Clean. Thin
  re-exports; usually 5–15 lines.
- **Layer 2** — chip-level `iff_sp1`. Composes Layer 1 + readers.
- **Layer 3** — `FormalAssertion.soundness`/`completeness`. Wraps
  the bridge into Clean's standard interface.

When somebody asks "doesn't the Clean pilot mean rewriting all the
hard proofs?", the answer is no. The DivRem 5-layer helper
architecture, the ShiftLeft bit-decomposition tower, the
MulOperation 16-limb carry chain — all of those live in SP1
and are reused as-is. Clean only adds the structural plumbing
around them.

## What's actually built so far

A rough mental model of "where the pilot is":

```
Mirrored:    every SP1 instruction chip (30 of them) has a parallel SP1Clean file
             every Reader (R-type, I-type, J-type, ALU-type, CPUState) has a Spec mirror

Promoted to FormalAssertion (13):
  - 10 chips: Add, Addi, Addw, Sub, Subw, Bitwise, Jal, Jalr, LoadX0, StoreByte
  - 3 fragments: AddOperation, CPUState, ProgramTable

iff_sp1-only (no completeness yet, ~12 chips + operations)
  - 7 chips have a structural Spec but no bridge yet (the 4 Loads + 3 non-byte Stores + UType)
  - Reader iff bridges are mature

True-placeholder Specs (4 chips):
  - Mul, ShiftLeft, ShiftRight, DivRem ship Spec := True
  - because their underlying operations aren't mirrored yet
  - they still appear in the trace aggregator structurally

Trace-level aggregator (stubbed, awaiting upstream fix):
  - 17 ChipRow constructors covering every chip
  - aggregateMemoryAccesses extracts per-row memory accesses
  - the OfflineMemory equivalence is parameterized until ../clean's
    OfflineMemory.lean builds clean on Lean 4.29
```

`lake build SP1Clean` is green: 0 errors, 0 warnings, 0 sorries.

The full inventory with file/line citations lives in
`CLEAN_PILOT_ROADMAP.md` §1.

## What benefits would this buy us, eventually?

Listed in roughly increasing order of how speculative they are.

**Already real (today).**

- **Completeness theorems for the 13 promoted units.** SP1 had no
  formal completeness story before; the Clean pilot gives one for
  every promoted FormalAssertion. The 4 True-placeholder chips
  and the un-bridged chips don't have it yet, but the framework is
  in place for them to inherit it once their operations are mirrored.
- **A structured spec layer that survives constraint regeneration.**
  When `update_constraints.py` shuffles `Main[k]` indices, the SP1
  side absorbs the change inside `Constraints.lean`. The SP1Clean
  side absorbs it inside the `fromMain` projection. Downstream
  proofs (`Spec`, `iff_sp1`, `FormalAssertion`) usually need only
  trivial updates because they speak in field names, not indices.
- **A second pair of eyes on every promoted chip.** Writing the
  `Spec` from scratch surfaces the *intent* of each constraint
  rather than the bytecode. The pilot caught at least one place
  during iter-4 where the SP1 `Spec` was missing a clause (it was
  trivially implied, but missing) — the Clean side made the gap
  visible.

**Likely soon (iter-5 / iter-6).**

- **CI gate against constraint-compiler drift.** A green
  `lake build SP1Clean` after every `update_constraints.py` regen
  is a single CI line. The first time it catches a silent index
  shuffle that broke the iff_sp1 RHS, it pays for itself.
- **Mechanical coverage for the 4 remaining Loads / 3 Stores / UType.**
  Their structural specs already exist; only the `iff_sp1` bridge is
  missing. Same template as `AddiChip.iff_sp1`; ~50–80 lines each.

**Realistic over the next several iterations.**

- **Promote heavy operations using SP1's `_poly` form as the bridge.**
  Because `_poly` lemmas are already field-generic (`ZMod p`-shaped),
  the operation-level `iff_sp1` in SP1Clean for MulOperation,
  DivRemOperation, ShiftLeft, ShiftRight will be one or two lines
  each. The work is in writing the *Clean Spec records* in the right
  shape — not in proving the arithmetic.
- **Gated subcircuit combinator.** A small ~80-line library addition
  (`Gated.assertion`) unblocks every chip that today carries a
  `(Op.constraints …).allHold_poly` clause multiplied by a per-row
  selector. That's `JalrChip` (two AddOp clauses), `LtChip`,
  `BranchChip` (six gated `LtOperationSigned` clauses), and the
  pattern recurs whenever an operation is conditional on `is_real`
  or an opcode flag.
- **A trace-level memory consistency theorem.** Once
  `Clean/Utils/OfflineMemory.lean` builds clean (one upstream PR
  fixes two specific decidability residues on Lean 4.29) and the
  parameterized `chip_specs_admit_offline_bridge` lemma binds to the
  real OfflineMemory predicates, every chip's individual memory
  sends compose into one repo-wide consistency claim — something
  the existing `SP1Chips/Soundness.lean` only sketches.

**Long-term, the endgame the roadmap proposes.**

- **Clean's `Assertion.main` as the source of truth.** SP1's
  auto-generated `constraints` function becomes a *validator* —
  emitted by `sp1-constraint-compiler`, diffed against a
  Clean-derived dump, fail-CI on mismatch. Each chip's constraint
  shape is defined exactly once, in Clean, and the constraint
  compiler is reduced to "a tool that double-checks our spec."
- **Plonky3 export of the verified circuits.** Clean's `backends/
  plonky3` (Rust + Cargo, currently labeled POC) takes a Clean
  Circuit and produces a Plonky3 AIR. Once promoted, our chips
  would have a path to a real prover that's been built around the
  formalism we proved against, rather than the prover-first-spec-
  later flow today.

The roadmap (`CLEAN_PILOT_ROADMAP.md`) sequences this into Phases
A → D with concrete LoC estimates.

## What's hard, what's easy

A few honest observations from the four iterations of pilot work.

**Easier than expected.**

- Reusing SP1's `_poly` lemmas as Layer-1 bridges. Anticipated as
  a major source of friction; turned out to be one-liners because
  the `_poly` migration had already made the SP1 specs field-generic.
- Per-chip Path-2 `FormalAssertion` boilerplate. About 75–115 LoC
  per chip once the recipe stabilized, fully mechanical.

**Harder than expected.**

- Clean's `circuit_proof_start` interacts oddly with `linear_combination`
  (an `id`-wrap workaround is needed). Cheap, but had to be
  discovered.
- `Expression.eval env input_var_<vec>[k]` not auto-unifying with
  the value-side `input_<vec>[k]` blocked full Path-1 promotion
  for several chips. Workaround: drop the offending Vector-indexed
  clauses from `Assertion.main` and keep them in the legacy `Spec`
  (Path-2 design). Long-term fix: a `with_bridged_lookup` tactic
  or reader-level subcircuit promotion.
- The gated-operation Tier-2 finding (`JalrChip`, `LtChip`,
  `BranchChip`). Clean's subcircuit DSL has no gate combinator.
  Tractable, but it's library work, not chip work.

**Not yet attempted.**

- Heavy operation promotion (`MulOperation`, `ShiftLeft/Right`,
  `DivRemOperation`). Estimated 200–600 LoC each, with non-trivial
  heartbeat budgets. The roadmap orders these by Lt → Sub → smalls
  → Shifts → Mul → DivRem so the heartbeat tooling gets validated
  on cheaper cases first.

## How to read the rest of the docs

Once this picture is in place, the existing docs slot in as follows:

- **`CLEAN_PILOT_ROADMAP.md`** — strategic plan; what to do next
  and why. Read after this intro.
- **`CLEAN_DSL_EVALUATION.md`** — the original cost/benefit
  evaluation that asked "should we even start?" Useful historical
  context; predates the pilot's actual findings.
- **`CLEAN_PILOT_NOTES.md`** — initial spike findings from iter-1
  (May 2026). What worked, what blocked, the upstream Misc.lean
  dedup story.
- **`CLEAN_PILOT_ITER2/3/4.md`** — per-iteration retros. ITER3 is
  the "full mirror landed" milestone; ITER4 is the FormalAssertion
  scaling round.
- **The SP1Clean files themselves** — `SP1Clean/AddChip.lean` is
  the canonical full Path-1 example. `SP1Clean/AddwChip.lean` is
  the canonical Path-2 example. `SP1Clean/AddOperation.lean` is
  the deepest operation promotion.

## TL;DR (again, for skimmers)

SP1Clean is a parallel formalization that re-expresses every SP1
chip as a Clean `FormalAssertion` over structured columns, bridged
back to the original SP1 constraint list and `correct_*` proofs by
per-chip `iff_sp1` lemmas. It doesn't replace SP1's formalization;
it adds completeness, a structured spec layer, and a path to
Plonky3 export. Today: 30 chips mirrored, 13 promoted to full
FormalAssertion, 0 sorries, blocked from full coverage by three
specific infrastructure gaps (a gating combinator, heavy operation
mirrors, upstream OfflineMemory). The roadmap sequences the next
several iterations of work.

If you want to dive in: read `SP1Clean/AddChip.lean` end-to-end
alongside `SP1Chips/AddChip.lean` and `SP1Chips/Add/Constraints.lean`.
That's the smallest non-trivial side-by-side that shows every layer
of the pilot.
