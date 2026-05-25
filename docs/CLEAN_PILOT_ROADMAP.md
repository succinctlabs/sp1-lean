# Clean Pilot — Roadmap

Status as of 2026-05-20. Supersedes the "Recommended next steps" section of
`docs/CLEAN_PILOT_NOTES.md`. Companions: per-iteration retros
`CLEAN_PILOT_ITER2.md` / `ITER3.md` / `ITER4.md`, original tradeoff doc
`CLEAN_DSL_EVALUATION.md`.

The pilot has reached a point where every SP1 instruction chip has a
parallel `SP1Clean/` mirror and 13 of those (10 chips + 3 fragments) ship
full Clean `FormalAssertion` bundles. The strategic questions left open
by the per-iter retros are:

1. What does the mirror cover, and how much?
2. What does "Clean fully models SP1" actually mean, and what concrete
   work proves it?
3. What's the path from "parallel pilot" to **Clean as the source of
   truth, SP1 constraints as a validator**?
4. How do we preserve hard SP1 proofs (DivRem, ShiftLeft, MulOperation
   `_poly` form) without rewriting them?

This doc answers all four.

---

## §1. Current state inventory

### FormalAssertion bundles (13)

| # | File | Level | Path | Iter |
|---|------|-------|------|------|
| 1 | `SP1Clean/Reader/CPUState.lean:217` | Reader | Path-1 | 3 |
| 2 | `SP1Clean/ProgramTable.lean:154` | Table | Path-1 | 3 |
| 3 | `SP1Clean/AddOperation.lean:229` | Operation | Path-1 | 3 |
| 4 | `SP1Clean/AddChip.lean:310` | Chip | Path-1 | 3 |
| 5 | `SP1Clean/AddwChip.lean:295` | Chip | Path-2 | 3 |
| 6 | `SP1Clean/BitwiseChip.lean:396` | Chip | Path-1 | 3 |
| 7 | `SP1Clean/AddiChip.lean:329` | Chip | Path-2 | 4 |
| 8 | `SP1Clean/SubChip.lean:280` | Chip | Path-2 | 4 |
| 9 | `SP1Clean/SubwChip.lean:273` | Chip | Path-2 | 4 |
| 10 | `SP1Clean/JalChip.lean:261` | Chip | Path-2 | 4 |
| 11 | `SP1Clean/JalrChip.lean:240` | Chip | Path-2 + Tier-2 probe | 4 |
| 12 | `SP1Clean/LoadX0Chip.lean:268` | Chip | Path-2 | 4 |
| 13 | `SP1Clean/StoreByteChip.lean:293` | Chip | Path-2 | 4 |

Path-1 = full mirror of the chip's `main`. Path-2 = drops bare byte
lookups + Vector-indexed assertZero gates + gated operation emissions
(see `feedback_path2_chip_promotion_recipe`).

### `iff_sp1`-only structural mirrors (13)

Every chip with a `FormalAssertion` also has an `iff_sp1` lemma; in
addition, the following files have `iff_sp1` without a FormalAssertion
bundle:

- Operation-level: `AddwOperation`, `BitwiseOperation`, `IsZeroOperation`,
  `SubOperation`, `SubwOperation`, `U16MSBOperation` (6 files).
- Reader-level: `ALUTypeReader`, `ITypeReader`, `RTypeReader`,
  `JTypeReader` (4 files; the lemma name is `<reader>Spec_iff_sp1`).

All chip-level `iff_sp1` lemmas live inside their respective `FormalAssertion`
chips listed above.

### True-placeholder Specs (4 chips)

These ship `def <chip>Spec _ : Prop := True` to compile while their heavy
operations remain un-mirrored.

| File | Line | Heavy op blocking |
|------|------|-------------------|
| `SP1Clean/MulChip.lean` | 208 | MulOperation (60+ conjunct RHS, 16-limb carry) |
| `SP1Clean/ShiftLeftChip.lean` | 166 | ShiftLeft (`maxHeartbeats 100M` in SP1) |
| `SP1Clean/ShiftRightChip.lean` | 99 | ShiftRight (mirrored: bit-decomp + sign-ext via U16MSB) |
| `SP1Clean/DivRemChip.lean` | 103 | DivRem (Mul × 2 + IsZeroWord + AddOp; 247 cols, 209 aux) |

None of the four has an `iff_sp1` — adding one is meaningless until the
Spec is real.

### No bridge yet (7 chips)

`Spec` exists, `iff_sp1` does not, FormalAssertion does not.

- All 4 LoadByte/Half/Word/Double chips (LoadByte has the most pilot
  exposure: it exercises the RAM branch of `toStateProp_poly`).
- StoreHalf/StoreWord/StoreDouble (StoreByte is promoted).
- UTypeChip (FormalAssertion friction documented; iff_sp1 is tractable).
- LtChip and BranchChip (raw `LtOperationSigned.constraints.allHold_poly`
  gated by per-row selectors — Tier-2 blocker).

### Trace-level aggregator status

`SP1Clean/Soundness/MemoryConsistency.lean`:
- **17 `ChipRow` constructors** (line 85–105) covering every mirrored chip.
- `aggregateMemoryAccesses` (line 535–544) flattens a `List (ChipRow p)`
  into the OfflineMemory 4-tuple shape.
- `chip_specs_admit_offline_bridge` (line 560–572) is **parameterized** over
  abstract `isConsistentOnline`/`isConsistentOffline` predicates because
  upstream `Clean/Utils/OfflineMemory.lean` lines 278 and 287 fail on Lean
  4.29 (`simp [filter_cons]` leaves decidability residue).

### Operations missing from SP1Clean entirely (13)

Comparing `SP1Operations/{Operation,Compare}/` to `SP1Clean/*Operation.lean`:

| Operation | SP1 source | SP1Clean | Used by |
|-----------|------------|----------|---------|
| MulOperation | `SP1Operations/Operation/MulOperation.lean` | ✗ | MulChip, DivRem |
| AddrAddOperation | `SP1Operations/Operation/AddrAddOperation.lean` | ✗ | Loads, Stores |
| AddressOperation | `SP1Operations/Operation/AddressOperation/` | ✗ | Loads, Stores |
| BitwiseU16Operation | `SP1Operations/Operation/BitwiseU16Operation.lean` | ✗ | BitwiseChip (used internally; Clean has a different `BitwiseOperation`) |
| U16toU8OperationSafe | `SP1Operations/Operation/U16toU8OperationSafe.lean` | ✗ | MulChip, DivRem |
| U16toU8OperationUnsafe | `SP1Operations/Operation/U16toU8OperationUnsafe.lean` | ✗ | Loads, Stores |
| IsEqualWordOperation | `SP1Operations/Compare/IsEqualWordOperation.lean` | ✗ | DivRem |
| IsZeroWordOperation | `SP1Operations/Compare/IsZeroWordOperation.lean` | ✗ | DivRem |
| LtOperationSigned | `SP1Operations/Compare/LtOperationSigned.lean` | ✗ | LtChip, BranchChip (×6) |
| LtOperationUnsigned | `SP1Operations/Compare/LtOperationUnsigned.lean` | ✗ | LtChip, BranchChip |
| U16CompareOperation | `SP1Operations/Compare/U16CompareOperation.lean` | ✗ | Loads, Stores |
| ShiftLeft operations | `SP1Chips/ShiftLeft/` | ✗ | ShiftLeftChip |
| ShiftRight operations | `SP1Chips/ShiftRight/` | ✗ | ShiftRightChip |

Mirrored already: `Add`, `Addw`, `Sub`, `Subw`, `Bitwise`, `IsZero`,
`U16MSB`.

---

## §2. Testing that Clean fully models SP1

"Fully models" has two layers; both must be proved.

### Layer A — structural equivalence (per-chip `iff_sp1`)

Every `SP1Clean.<Chip>.Spec` must be provably equivalent to the SP1-side
`_root_.<Chip>.constraints.allHold` via `iff_sp1`. The pattern is mature
for the 13 FormalAssertion chips; missing for 7 + the 4 True-placeholder
chips.

**Concrete gap list:**

- **4 heavy chips** (`Mul`, `ShiftLeft`, `ShiftRight`, `DivRem`) have
  `Spec := True`. An `iff_sp1` here is degenerate. Real Specs require
  the missing operations from §1 — see §3 Phase-B.
- **7 chips** have a structural `Spec` but no `iff_sp1`:
  - LoadByte, LoadHalf, LoadWord, LoadDouble (memory-read sequence,
    `ITypeReader`-based).
  - StoreHalf, StoreWord, StoreDouble (memory-write sequence; StoreByte
    is the template).
  - UTypeChip (auipc/lui; iff_sp1 is tractable, FormalAssertion is
    blocked by Vector-indexed clauses).
- **2 chips** (`Lt`, `Branch`) ship raw
  `LtOperationSigned.constraints.allHold_poly` gated by a per-row
  selector inside their `Spec`. iff_sp1 here needs the Tier-2 gating
  story (see §3 Phase-A) and the `LtOperationSigned` mirror (Phase-B).

**Iter-5 unblocked test work:**

1. `iff_sp1` for LoadByte, LoadHalf, LoadWord. Each reuses
   `SP1Chips.Load.<Width>.allHold_constraints_iff` + the existing
   `cpuStateSpec_iff_sp1` + `itypeReaderSpec_iff_sp1`. Per-chip cost
   ~50–80 lines modeled on `AddiChip.iff_sp1` (`SP1Clean/AddiChip.lean:165`).
2. `iff_sp1` for UTypeChip. Same recipe with `aluTypeReaderSpec_iff_sp1`.
   The FormalAssertion friction noted in
   `feedback_formal_assertion_friction` is about completeness goals,
   not the iff itself.

Layer A is **strictly stronger than the original SP1 `correct_*`**: the
SP1 proof asserts Sail equivalence; `iff_sp1` asserts that the *Clean
spec* says the same thing as the SP1 constraints. Once both hold, the
Clean spec ⇔ Sail equivalence follows by composition (and `correct_*`
adapts via `(iff_sp1 Main h_is_real).mpr h_spec`).

### Layer B — trace-level offline-memory consistency

`SP1Clean.Soundness.MemoryConsistency.chip_specs_admit_offline_bridge`
is currently abstract. To make it concrete:

1. **Upstream fix.** `Clean/Utils/OfflineMemory.lean` lines 278/287 fail
   on Lean 4.29 / current Mathlib (`simp [filter_cons]` decidability
   residue). The fix is a one-liner — add an explicit
   `decide`/`Decidable` synthesis step. Open a PR against
   `Verified-zkEVM/clean`. If upstream is slow, carry it on the local
   `../clean` `sp1-pilot-misc-dedup` branch.
2. **Replace stubs.** Swap the local `MemoryAccessTuple : ℕ × ℕ × ℕ × ℕ`
   abbreviation (`MemoryConsistency.lean:70`) for upstream
   `_root_.MemoryAccess`. Replace the abstract predicate parameters
   with `MemoryAccessList.isConsistentOnline_iff_isConsistentOffline`.

### CI drift gate

The biggest risk to the pilot's correctness story is constraint-compiler
drift. `update_constraints.py` regen mutates `Main[k]` indices and
operand decompositions — every chip's `iff_sp1` references those
indices. Today, regen can silently break SP1Clean and the only signal
is the next `lake build SP1Clean`.

**Mitigation:** add a single CI step running `lake build SP1Clean` after
constraint regen, and gate the PR template on a green SP1Clean build.
Lightweight (~5 lines of CI YAML); pays for itself the first time it
catches a drift.

---

## §3. Adopting Clean as the source of truth

**Long-term target:** Clean's `Assertion.main` is canonical; SP1's
auto-generated `constraints` function becomes a *validator* — checked
against the Clean source on every regen. Each instruction's constraint
shape is defined exactly once, in Clean.

This is the **D2 mode** (compare both outputs against
`sp1-constraint-compiler`'s AIR-bytecode dump) rather than D1
(generate SP1 from Clean), at least for the first iteration: it keeps
SP1's constraint compiler as the canonical *artifact* while letting
Clean be the canonical *source of truth*.

Three phases gate the transition.

### Phase-A — subcircuit gating combinator

The single biggest mechanical blocker. Today, 3+ chips and at least
1 operation carry constraint clauses of the form
`(SubOp.constraints …).allHold_poly` multiplied by a per-row selector
(`is_real`, `is_real − op_a_0`, or an opcode flag). When the multiplier
is 0, every conjunct vacuously holds; when 1, the operation's
constraints must hold.

Clean's subcircuit DSL has **no gate combinator**. Calling
`AddOp.assertion` from `JalrChip.Assertion.main` forces the carry chain
unconditionally — on `is_real = 0` padding rows or JALR `op_a = x0`
rows, completeness fails. Affected sites:

- `SP1Clean/JalrChip.lean:106–114` — two gated AddOperation clauses.
- `SP1Clean/LtChip.lean:116–118` — gated `LtOperationSigned`.
- `SP1Clean/BranchChip.lean:127–129` — gated `LtOperationSigned` ×
  6 opcode flags.

**Three approaches considered:**

- **A1.** Define `Gated.assertion : (gate : Expression) → (sub :
  FormalAssertion α β) → FormalAssertion α β`. Soundness:
  `gate * sub.constraints = 0 → gate = 0 ∨ sub.constraints = 0`.
  Completeness: pick a witness depending on `gate`. ~80 LoC of Clean
  infrastructure (either upstream or SP1Clean-local) + ~5 LoC per use
  site.
- **A2.** Encode gating in `FormalSpec`: `gate = 0 ∨ Sub.Spec`. Cheaper
  per-chip; doesn't compose with subcircuit calls.
- **A3.** Promote `is_real = 1` into a chip-level `Assumption`. Requires
  the trace aggregator to filter padding rows before chip dispatch.

**Recommend A1.** It's a single library addition that unblocks every
gated-operation site (and any future ones). Decompose `gate * carries =
0` once at the combinator level; downstream proofs see the standard
`FormalAssertion` interface.

### Phase-B — heavy operations

Each gets a Clean `<Op>.assertion : FormalAssertion (ZMod p) Inputs`,
plus an `iff_sp1` lemma. Ordering by least-cost to highest-cost:

1. **LtOperationSigned** (~150 LoC). Unblocks Lt, Branch (×6), and
   serves as Tier-2 test bed once Phase-A's `Gated.assertion` exists.
2. **SubOperation** (~80–120 LoC) — borrow→natural carry-form bridge.
   SP1 emits `d_i` borrows; SP1Clean Spec uses natural `c_i`. Already
   reconciled in `SP1Operations.Operation.SubOperation.allHold_constraints_iff_poly`
   with 4× `linear_combination * hbridge` cascade — replicate in the
   FormalAssertion proof. Unblocks Path-1 promotion for Sub/Subw chips.
3. **U16CompareOperation, U16toU8Operation{Safe,Unsafe}, IsZeroWordOperation,
   IsEqualWordOperation** (~50–100 LoC each, all share the
   AddOp-style structural shape).
4. **AddrAddOperation, AddressOperation** (~80 LoC each). Used by Loads
   and Stores. Once mirrored, all 7 Load/Store chips drop into Path-2
   FormalAssertion mechanically.
5. **ShiftLeft / ShiftRight** (~200–300 LoC each). Bit-decomposition +
   shift power chain + byte-shift one-hot + limb-shift correctness; SP1
   needed `maxHeartbeats 100M`. Budget several days each. Test the
   Phase-A heartbeat tooling here before tackling Mul.
6. **MulOperation** (~400–600 LoC). 16-limb carry chain; uses
   U16toU8 + Bitwise sub-fragments. Defer until Shifts validate the
   approach.
7. **DivRemOperation** (~400+ LoC). Composes MulOperation (×2) +
   IsZeroWord + AddOperation. Last in priority.

**Cardinal rule:** the Clean `<Op>.Spec` is **definitionally close** to
the SP1-side `<Op>.allHold_constraints_iff_poly` RHS. Never re-derive
the spec content from the constraint definition — just rename fields
and reshape into the Clean record. `iff_sp1` then becomes a one- or
two-line `simp` (`AddOperation.iff_sp1` is the template:
`SP1Clean/AddOperation.lean:78`).

### Phase-C — reader and CPU-state full FormalAssertion (parallelizable)

CPUState is promoted (`SP1Clean/Reader/CPUState.lean:217`). The other
readers are iff-only:

- `SP1Clean/Reader/ALUTypeReader.lean`
- `SP1Clean/Reader/ITypeReader.lean`
- `SP1Clean/Reader/RTypeReader.lean`
- `SP1Clean/Reader/JTypeReader.lean`

Promoting each lets the corresponding chips drop bare `lookup
ProgramTable` / `lookup MemoryAccess` calls from `Assertion.main` in
favor of subcircuit calls. This sidesteps the Path-1
`Expression.eval env input_var_<vec>[k]` friction — chip-level Vector
fields no longer have to be unified field-by-field; they flow through
the reader's subcircuit interface.

Cost per reader: ~150–200 LoC, modeled on `CPUState.assertion`.
Friction to expect: each reader emits *both* program/byte lookups
(subcircuit-friendly today) *and* memory sends (need Phase-D /
OfflineMemory bridge first). For iter-5/6, ship readers that drop
the memory sends from `FormalSpec` (Path-2 style); add them back
later once the trace bridge lands.

### Phase-D — write-back tooling

Endgame, after Phases A–C have closed the gap. A small Lean tactic or
`#eval` script consumes a `FormalAssertion.elaborated` and emits an
SP1-flavored `Vector (Fin KB) N → SP1ConstraintList`. The output is
diff-checked against `update_constraints.py`'s output as a sanity
validator.

Two paths:

- **D1.** Auto-generate the SP1 `constraints` function from the Clean
  `Assertion.main`. Most aggressive — Clean is the only source.
  Eliminates the constraint compiler.
- **D2.** Keep both. Diff the output of `sp1-constraint-compiler`
  against a Clean-derived dump. Discrepancies fail CI.

**Recommend D2 as the default.** It preserves the SP1 constraint
compiler (a useful artifact in its own right and the link to upstream
`Verified-zkEVM/sp1-constraint-compiler`'s correctness story), while
making Clean's `Assertion.main` the spec source of truth. D1 stays as
a future option if the constraint compiler atrophies.

---

## §4. Bridging hard SP1 proofs without rewriting

The hardest proofs in this repo — DivRem's 5-layer
`_poly` helper architecture, ShiftLeft's bit-decomposition tower,
MulOperation's 16-limb carry chain — must **not** be rewritten in
Clean. The pilot's existing bridge pattern shows how to reuse them.

### The three-layer bridging discipline

```
Layer 0 — SP1 _poly lemmas (genuinely hard, never touch)
   SP1Operations.<Op>.allHold_constraints_iff_poly
   SP1Chips.<Chip>.allHold_constraints_iff (via spec_<op>)
        ↑ reused by
Layer 1 — Operation-level iff_sp1 in SP1Clean (thin re-export, ~5–15 lines)
   SP1Clean.<Op>.iff_sp1 := <Op>.allHold_constraints_iff a b cols
        ↑ used by
Layer 2 — Chip-level iff_sp1 in SP1Clean (compose Layer 1 + readers, ~30–50 lines)
   SP1Clean.<Chip>.iff_sp1 :
     (_root_.<Chip>.constraints Main).allHold ↔ Spec (fromMain Main)
        ↑ wrapped by
Layer 3 — FormalAssertion.soundness/completeness in SP1Clean (~15–25 lines)
   circuit_proof_start → linear_combination / iff_sp1.mp / iff_sp1.mpr
        ↑ consumed by
SP1 correct_<op> theorems (unchanged Sail-equivalence proofs)
   (iff_sp1 Main h_is_real).mpr h_spec  →  _root_.<Chip>.correct_<op>
```

The discipline: **Layer 0 is never duplicated.** Layers 1–3 are pure
plumbing. The whole stack ensures every Clean `FormalAssertion` is
backed by an SP1 `_poly` lemma that was proved exactly once.

### Concrete bridging recipes

**Recipe 1: MulOperation → SP1Clean.MulOp.iff_sp1.**

SP1's `MulOperation.allHold_constraints_iff_poly` (in
`SP1Operations/Operation/MulOperation/Constraints.lean`) has a verified
RHS that's the hard-fought 16-limb spec. Define
`SP1Clean.MulOp.Spec` as a `def` whose body is **structurally identical**
to that RHS — field projections from `Inputs` instead of `Main[k]`
indexing, but the same arithmetic. Then:

```lean
theorem iff_sp1 (a b result : Word (ZMod p)) (cols : MulCols (ZMod p)) :
    (MulOperation.constraints a b result cols).allHold_poly ↔ Spec a b result cols :=
  MulOperation.allHold_constraints_iff_poly a b result cols
```

Iff is a single function application. No new arithmetic.

**Recipe 2: DivRemOperation → SP1Clean.DivRemOp.iff_sp1.**

SP1 already split DivRem into 5 `_poly` core lemmas (see
`project_divrem_poly`, `feedback_sll_poly_helper_pattern`). Define
`SP1Clean.DivRemOp.Spec` as a disjunction over the four variants
(div / divu / divw / divuw + rem twin), each definitionally the
matching SP1 `_poly` RHS. Compose with `_root_.DivRem.allHold_constraints_iff_poly`.

**Recipe 3: The `_poly` form is already the right shape for Clean.**

The `_poly` migration was driven by Fin-KB → ZMod-polymorphism
(`project_divrem_poly`). Side effect: every `_poly` Spec is stated over
a generic field (the `Field F` instance). Clean's `Expression.eval`
evaluates in `ZMod p`. **No `BitVec`-to-`ZMod` conversion needed at the
bridge layer.** Pure win.

### Canonical ALU-chip Layer-0/Layer-2 shape (post-AddChip refactor, 2026-05-24)

`SP1Chips/Add/Common.lean` is the reference template for chip-level
`allHold_constraints_iff` lemmas going forward. Two structural choices
matter:

1. **State both sides of the iff in `.allHold` form, not
   `List.Forall SP1Constraint.toProp`.** The two are reducibly equal,
   but `rw` doesn't unfold reducibles during pattern matching — keeping
   `.allHold` form lets downstream operation/reader `iff_sp1` lemmas
   (which all match on `.allHold`) fire directly without an inline
   form-bridge.

   ```lean
   lemma allHold_constraints_iff (Main : Vector (ZMod p) 33) :
       (constraints Main).allHold ↔
       SP1ConstraintList.allHold (AddOperation.constraints …) ∧
       SP1ConstraintList.allHold (_root_.CPUState.constraints …) ∧
       SP1ConstraintList.allHold (RTypeReader.constraints …) ∧
       <trailing assertZero gates as `e = 0` clauses> := by
     simp only [constraints, List.forall_append, List.Forall,
       SP1Constraint.toProp, and_assoc]
   ```

2. **The matching SP1Clean Layer-2 `allHold_iff_structural` collapses to
   a flat rewrite chain.** `SP1Clean/AddChip/Lemmas.lean#allHold_iff_structural`
   is the reference:

   ```lean
   rw [_root_.Add.allHold_constraints_iff Main, h_is_real,
     AddOperation.allHold_constraints_iff,
     SP1Clean.CPUState.cpuStateSpec_iff_sp1,
     SP1Clean.RTypeReader.rtypeReaderSpec_iff_sp1]
   simp [SP1Clean.AddOp.Spec, SP1Clean.CPUState.cpuStateSpec,
         SP1Clean.RTypeReader.rtypeReaderSpec, and_assoc]
   ```

   No `show … from by simp [constraints, …]` block, no manual constraint
   re-derivation, no inline `List.Forall ↔ .allHold` bridge. Every ALU
   chip's Layer-2 proof should look this clean.

Existing chip Common.lean files (Sub, Addi, Addw, Subw, Mul, Bitwise,
Branch, DivRem, Jal, Jalr, Lt, ShiftLeft, ShiftRight) still use the
older `List.Forall SP1Constraint.toProp (...)` form on both sides.
Migrate to the `.allHold` form opportunistically — when touching a
chip's Common.lean for another reason — rather than as a flag-day
sweep. **New ALU chip Commons** (whether added because a constraint
regen introduces a chip, or because a chip's Common.lean is created
for the first time, as Add just was) **should start in the canonical
shape.**

Two caveats observed during the AddChip migration that the template
silently handles but a new chip's author should know:

- **Trailing `assertZero` clauses can need `(0 : ZMod p)` / `(1 : ZMod p)`
  ascriptions** on bare literals (`0 - (Main[k] * 0 + (1 - Main[k]) * 0)
  = 0`) — Lean's left-to-right literal elaboration otherwise picks `ℕ`
  for the leading `0`/`1`, projecting `Main[k].val` and breaking the
  `simp only` close. UType/Common.lean carries this fix.
- **The `simp only` close can leave `↑48` / `↑1` cast residue** when a
  reader op-arg expression mixes `Main[k] * 48 + (1 - Main[k]) * 49`
  patterns. Append `push_cast; rfl` after the `simp only` (mirrors
  Mul/Common.lean's tail).

### Friction the bridge layer must guard against

1. **`↑↑` cast residue.** When an SP1 `_poly` RHS contains `(n : F p)`
   round-trips for byte literals, `Expression.eval` may produce
   `((n : ZMod p).val : ZMod p)` echoes in the goal. Cheap fix:
   `Fin.val_cast_of_lt` after bounding the literal. Already documented
   for `byte_decomp_128` in `SP1Foundations/Word.lean`.
2. **`simp_all` leakage.** Repo-wide hazard (commit `419ee1d`).
   Prefer targeted `simp [...] at h` over `simp_all` in any
   Layer-2/Layer-3 proof.
3. **`circuit_proof_start` `id`-wrap.** After
   `circuit_proof_start`, the goal/hypotheses are wrapped in an `id`
   that breaks `linear_combination` and `mul_eq_zero.mpr`. Fix:
   `unfold id at *` once. See `CLEAN_PILOT_NOTES.md:236–238`.
4. **`Vector.map` over `.push`.** `Vector.map (Expression.eval env)
   (v.push 0)` doesn't auto-reduce to `(input_v).push 0`. Cheap fix:
   `simp only [Vector.map_push, h_pc] at h_sub`. See
   `SP1Clean.Jal.Assertion.soundness:241`.
5. **`sub_eq_add_neg` normalization mismatch.** `circuit_proof_start`
   normalizes the goal but not the hypotheses. Bridge with
   `simp only [sub_eq_add_neg] at h_spec` after destructuring.

---

## §5. Risks and open questions

**Upstream Clean fork health.** The pilot tracks `../clean` on a local
branch (`sp1-pilot-misc-dedup`) carrying a one-line dedup patch in
`Clean/Utils/Misc.lean`. If upstream's `bump-lean-4.29` branch stalls,
who maintains the patch long-term? **Mitigation:** pin a specific
commit in `lakefile.toml` once upstream stabilizes, or fork permanently
under the SP1 org.

**Constraint-compiler drift.** Until the CI gate (§2) is added, every
`update_constraints.py` run risks silent SP1Clean breakage. **Mitigation:**
add the CI step in iter-5; no later than the next user-visible
constraint regen.

**Heartbeat budget creep.** Phases B5/B6 (Shifts, Mul) likely need
per-file `maxHeartbeats 10000000+`. The precedent from
`feedback_skipkerneltc_working_recipe` and the existing `lakefile.toml`
`synthInstance.maxHeartbeats = 1000000` shows the repo tolerates this.
Document budgets in each file's docstring (as ShiftLeftChip already
does).

**What happens to SP1Chips after Phase-D?** SP1Chips's `correct_*`
proofs prove **Sail equivalence**, which Clean doesn't directly model.
SP1Chips stays as the **Sail bridge layer**: it takes input from either
the original SP1 constraints function or a Clean-derived one (D2 makes
them identical-by-CI). The `spec_<op> / sp1_<op> / correct_<op>` triad
is independent of which constraint definition Layer-2 imports.

**Field-genericism interaction (positive risk).** The `_poly` migration
(see `project_divrem_poly`, 11 sorries in DivRem; ShiftLeft Phase A
done) is mid-stream. The migration's target — generic `Field F`
instead of `Fin KB` — is exactly Clean's natural representation
(`ZMod p`). The two efforts *reinforce* each other: every `_poly`
lemma completed in SP1Operations becomes a one-line Layer-1 import in
SP1Clean. Treat as a "win for free."

**Multiplicity tracking.** SP1 sends carry an `AirInteraction.mult`;
the Clean lookup encoding has no multiplicity. The pilot drops `mult`
under the chip-level `is_real = 1` premise. Holds today because every
constraint has a corresponding `mult ≠ 0 → P` guard discharged by
`is_real`. If a future chip introduces *fractional* multiplicities
(e.g., per-byte counters), the encoding will need extension. None of
the 30 currently-mirrored chips needs this.

---

## §6. Iter-5 concrete shortlist

Ordered by dependency + ROI. Total estimated ~500–700 LoC, 2–3
SP1Clean rebuilds (~5–10 min each).

| # | Work item | LoC | Dependency | Unblocks |
|---|-----------|-----|------------|----------|
| 1 | CI drift gate (`lake build SP1Clean` after constraint regen) | ~5 (CI YAML) | None | Catches future drift |
| 2 | Upstream `Clean/Utils/OfflineMemory.lean` 278/287 fix (PR) | ~3 | External | Layer-B trace bridge |
| 3 | `Gated.assertion` combinator | ~80 | None | Phase-B (Lt, Branch, gated AddOp re-promotion of Jalr) |
| 4 | `iff_sp1` for LoadByte / LoadHalf / LoadWord | ~50–80 each | None | §2 Layer-A coverage |
| 5 | `iff_sp1` for UTypeChip | ~80 | None | §2 Layer-A coverage |
| 6 | `LtOperationSigned.assertion` + iff_sp1 | ~150 | #3 | Lt/Branch FormalAssertion (iter-6) |

After iter-5: 30 chips mirrored, 18 with iff_sp1 (currently 11), 14
FormalAssertion bundles (currently 13), and a green CI signal on every
constraint regen.

---

## File index for verification

When auditing this roadmap, the citations point to:

| Doc claim | Source |
|-----------|--------|
| Path-1 iff_sp1 template | `SP1Clean/AddChip.lean:148–207` |
| Path-2 FormalAssertion template | `SP1Clean/AddwChip.lean:295` |
| True-placeholder examples | `SP1Clean/MulChip.lean:208`, `DivRemChip.lean:103`, `ShiftLeft/RightChip.lean:166/99` |
| Gated-op clause (Tier-2 probe) | `SP1Clean/JalrChip.lean:106–114` |
| Gated-op clause (Lt) | `SP1Clean/LtChip.lean:116–118` |
| Gated-op clause (Branch ×6) | `SP1Clean/BranchChip.lean:127–129` |
| Trace aggregator | `SP1Clean/Soundness/MemoryConsistency.lean:85–105, 535–572` |
| Layer-1 promotion template | `SP1Clean/AddOperation.lean:61–73, 171–221` |
| Origin findings | `docs/CLEAN_PILOT_NOTES.md` |
| Cumulative status (iter 3/4) | `docs/CLEAN_PILOT_ITER3.md`, `ITER4.md` |
| Tradeoff doc | `docs/CLEAN_DSL_EVALUATION.md` |
