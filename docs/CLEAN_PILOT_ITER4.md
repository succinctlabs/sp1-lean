# Clean DSL pilot — iteration 4 (scaling FormalAssertion promotions)

Status as of 2026-05-20. Companion to `docs/CLEAN_PILOT_ITER3.md`. Plan:
`~/.claude/plans/make-a-plan-to-jiggly-parasol.md`.

## TL;DR

Seven new chip-level `FormalAssertion` bundles promoted. Operation-level
`SubOperation.assertion` deferred. `lake build SP1Clean` stays at
**0 errors / 0 warnings / 0 sorries** end-to-end. FormalAssertion count
grew from 5 (Add, Addw, Bitwise, AddOperation, CPUState) to 12.

The "scaling difficulty" hypothesis from the plan — that Tier-1 chips
would each take ~50 LoC of boilerplate — held in shape but not in size:
the actual cost was **~93 LoC per chip on average** (range 75–113),
dominated by the `Assertion.main` + `FormalSpec` + `elaborated` + bundle
plumbing rather than by the soundness / completeness proofs themselves
(the proofs are ~10–25 lines each).

## What landed

| # | Chip | LoC added | Pattern | Notes |
|---|------|-----------|---------|-------|
| 1 | AddiChip       | 111 | Path-2 | Drops the 4 immediate-limb `ByteOpcodeTable` lookups (Vector-indexed bridge friction); the AddOp + CPUState + ProgramTable subcircuits + booleans remain |
| 2 | SubChip        |  91 | Path-2 | Drops `SubOp.main` entirely (no `SubOp.assertion` yet); CPUState + ProgramTable + booleans |
| 3 | SubwChip       |  78 | Path-2 | Same as SubChip; SubwOp 32-bit-with-MSB surface deferred to legacy `iff_sp1` |
| 4 | JalChip        |  90 | Path-2 | Two `AddOp.assertion` subcircuits + ProgramTable + is_real; needed `Vector.map_push` simp bridge for `pc.push 0` |
| 5 | LoadX0Chip     | 113 | Path-2 | CPUState + ProgramTable + 8 boolean asserts (7 sub-opcode + aggregate is_real); largest chip in this batch |
| 6 | StoreByteChip  |  75 | Path-2 | Smallest in this batch; drops all bare byte lookups (CPUState bytes, store memory diff, result_byte U8, selected_byte_alt U8) |
| 7 | JalrChip       |  91 | Path-2; Tier-2 probe | Two raw `AddOperation.allHold_poly` clauses NOT converted to subcircuits (see Tier-2 finding) |

**Build cost.** Incremental build of each chip after promotion: 11–15s.
Cold build: untested in this round.

**Code volume.** SP1Clean total: ~6402 LoC pre-iter-4 → 7059 LoC after
(+657 LoC). New FormalAssertion bundles concentrated in the 7 chips
above plus inheritance from the unchanged `AddOperation` / `CPUState`
/ `ProgramTable` / `AddChip` / `AddwChip` / `BitwiseChip` Assertions.

## Path-2 design choice

Every chip in this round used **Path-2 promotion** rather than the
full Path-1 (AddChip-style) promotion:

- **Path-1** (AddChip / BitwiseChip): `Assertion.main` mirrors the
  chip's `main` 1-to-1, with all byte lookups and subcircuit calls
  included; `FormalSpec` includes all corresponding clauses.
- **Path-2** (AddwChip, this round): `Assertion.main` drops bare
  byte lookups, drops Vector-indexed assertZero gates, and only
  includes promotion-ready subcircuit calls + scalar boolean gates;
  `FormalSpec` is the corresponding strict subset. Dropped clauses
  remain in the legacy chip-level `Spec` carried by `iff_sp1`.

The driver for Path-2: **two friction modes** kept biting Path-1.

1. **`Expression.eval env input_var_<field>[k]` doesn't auto-unify with
   `input_<field>[k]`.** Bare `lookup ByteOpcodeTable` calls in
   `Assertion.main` produce `Lookup.Soundness env` obligations whose
   evaluated terms have the `Expression.eval env` residue, while the
   FormalSpec goal speaks in the value-side `input` view. Bridging
   requires destructuring `h_input` (a 14–16-tuple conjunction for
   typical chips) and `subst`-ing or rewriting each field
   individually. The `circuit_proof_start` tactic does not do this
   automatically when the offending term is not buried inside a
   subcircuit call. Dropping the bare lookups sidesteps the bridge.

2. **`Vector.map` doesn't auto-distribute over `.push`.** When a chip
   passes `pc.push 0` to `AddOp.assertion` (as in `JalChip`), the
   subcircuit's Spec returns with `Vector.map (Expression.eval env)
   (input_var_pc.push 0)` instead of `input_pc.push 0`. Bridging is
   a one-line `simp only [Vector.map_push, h_pc]` — see
   `SP1Clean.Jal.Assertion.soundness:241`. Cheap when caught; nontrivial
   to spot without `lean_diagnostic_messages`.

Implication: **dropping byte-bridging surface costs accuracy of the
FormalSpec (it no longer covers limb bounds at the Assertion level)
but preserves correctness** — the legacy `iff_sp1` / `correct_*`
chain still carries the full Spec. A future iter-5 can re-introduce
those clauses with a dedicated bridge tactic.

## Tier-2 probe finding (JalrChip)

**Question:** Can raw `(AddOperation.constraints ...).allHold_poly`
clauses in a Spec be converted to `AddOp.assertion` subcircuit calls
in `Assertion.main` once the operation is promoted?

**Answer:** Only for **unconditional** constraints. JalrChip's two
AddOp clauses are gated by the SP1 constraint compiler:

```lean
(AddOperation.constraints op_b_mem_prev op_c_imm
   { value := jump_target } cols.is_real).allHold_poly ∧
(AddOperation.constraints (pc ++ [0]) [4,0,0,0]
   { value := op_a_write_value } (cols.is_real - cols.op_a_0)).allHold_poly
```

The `is_real` / `is_real - op_a_0` last arg is a per-constraint
multiplier — when 0, every conjunct becomes `0 = 0` and is vacuous.

Clean's `AddOp.assertion` has no gating: calling it from
`Assertion.main` forces the carry chain unconditionally. For
`is_real = 0` rows (padding) and for `op_a = x0` rows (JALR convention
where the destination register is the always-zero `x0` and no
return-address write happens), the carry chain doesn't naturally hold,
so completeness would fail.

This affects JalrChip, LtChip (`LtOperationSigned.allHold_poly` gated
on `is_real`), BranchChip (6 LtOperationSigned variants each gated by
a per-opcode selector), and any other chip that uses gated operation
emissions.

**Workaround paths** (not pursued in this round, listed for future
iter-5 planning):

1. Add a `Gated.assertion : gate → FormalAssertion → FormalAssertion`
   combinator at the Clean library level. Soundness: `gate * carries = 0
   → gate = 0 ∨ carries = 0`.
2. Promote a `GatedAddOp.assertion` variant whose Spec is
   `gate = 0 ∨ AddOp.Spec`. Repetitive (one per gated operation).
3. Strengthen the chip's `Assumptions` to `is_real = 1`, then the
   gating disappears at the FormalAssertion level. The downside: the
   `OfflineMemory` / trace-level aggregation would have to filter
   padding rows before invoking the chip's `assertion`.

## Why SubOperation promotion was deferred

The plan called for `SubOperation.assertion` (Phase A1) and
`LtOperationSigned.assertion` (Phase A2) alongside the chip work.

**A2 (LtOperationSigned) was dropped immediately** because no Tier-1
chip in the batch consumes it (LtChip and BranchChip are Tier-2 chips
deferred to the next round).

**A1 (SubOperation) was deferred** after investigation. The friction is
that `SubOperation.main` emits **borrow-form** carries `d_i`, while
`SubOperation.Spec` (the existing pilot Spec in `SP1Clean.SubOperation`)
states **natural-form** carries `c_i`. The two are related by
`d_i + c_i = 65536 * 65536⁻¹ = 1`, which requires a
`linear_combination ... * hbridge` cascade across all 4 carry levels in
soundness AND completeness — see how
`SP1Operations.Operation.SubOperation.allHold_constraints_iff_poly`
already does this with `set` + 4 `hdi_swap` lemmas.

Replicating that inside the FormalAssertion proof would mean:
- 4 `have hdi_swap` clauses (each is a `linear_combination * hbridge`)
- 4 case-splits on `d_i ∈ {0,1}` plus 4 case-splits on `c_i ∈ {0,1}`
- Re-tying byte lookups via `byteOpcodeSpec_range16` for the 4 result
  limbs (this part is easy; AddOp has it already)

Estimated cost: ~80–120 LoC for the FormalAssertion bundle alone, plus
heartbeat budget tuning. Skippable for this round because **Path-2
SubChip / SubwChip don't need SubOp.assertion** — they drop SubOp.main
from `Assertion.main` entirely. If a future iter-5 wants to upgrade
SubChip to Path-1 (full FormalAssertion including SubOp), SubOp would
need to be promoted then.

Comparison to `AddOperation.assertion` (which IS promoted): AddOp's
`main` uses the SAME natural-form carries as `AddOp.Spec`, so the
soundness/completeness proofs are direct (4 × `linear_combination h` per
case). No bridge required. The difference is exactly the
borrow-vs-natural form mismatch in SP1's SubOperation emission.

## FormalAssertion inventory after iter-4

| File | Type | Promoted? |
|------|------|-----------|
| `SP1Clean/AddOperation.lean` | Operation | ✓ (from iter-3) |
| `SP1Clean/Reader/CPUState.lean` | Reader | ✓ (from iter-3) |
| `SP1Clean/ProgramTable.lean` | Table | ✓ (from iter-3) |
| `SP1Clean/AddChip.lean` | Chip | ✓ (Path-1; from iter-3) |
| `SP1Clean/AddwChip.lean` | Chip | ✓ (Path-2; from iter-3) |
| `SP1Clean/BitwiseChip.lean` | Chip | ✓ (Path-1; from iter-3) |
| `SP1Clean/AddiChip.lean` | Chip | ✓ (Path-2; **iter-4**) |
| `SP1Clean/SubChip.lean` | Chip | ✓ (Path-2; **iter-4**) |
| `SP1Clean/SubwChip.lean` | Chip | ✓ (Path-2; **iter-4**) |
| `SP1Clean/JalChip.lean` | Chip | ✓ (Path-2; **iter-4**) |
| `SP1Clean/LoadX0Chip.lean` | Chip | ✓ (Path-2; **iter-4**) |
| `SP1Clean/StoreByteChip.lean` | Chip | ✓ (Path-2; **iter-4**) |
| `SP1Clean/JalrChip.lean` | Chip | ✓ (Path-2; **iter-4**) |
| `SP1Clean/SubOperation.lean` | Operation | ✗ (borrow/natural bridge deferred) |
| `SP1Clean/AddwOperation.lean` | Operation | ✗ (deferred) |
| `SP1Clean/SubwOperation.lean` | Operation | ✗ (deferred) |
| `SP1Clean/BitwiseOperation.lean` | Operation | ✗ (deferred) |
| `SP1Clean/IsZeroOperation.lean` | Operation | ✗ (deferred) |
| `SP1Clean/U16MSBOperation.lean` | Operation | ✗ (deferred) |
| `SP1Clean/LoadByteChip.lean` | Chip | ✗ (deferred) |
| `SP1Clean/LoadHalfChip.lean` | Chip | ✗ (deferred) |
| `SP1Clean/LoadWordChip.lean` | Chip | ✗ (deferred) |
| `SP1Clean/LoadDoubleChip.lean` | Chip | ✗ (deferred) |
| `SP1Clean/StoreHalfChip.lean` | Chip | ✗ (deferred) |
| `SP1Clean/StoreWordChip.lean` | Chip | ✗ (deferred) |
| `SP1Clean/StoreDoubleChip.lean` | Chip | ✗ (deferred) |
| `SP1Clean/UTypeChip.lean` | Chip | ✗ (Vector-indexing blocker; iter-3 hard case) |
| `SP1Clean/LtChip.lean` | Chip | ✗ (LtOperationSigned not promoted) |
| `SP1Clean/BranchChip.lean` | Chip | ✗ (6× LtOperationSigned not promoted) |
| `SP1Clean/MulChip.lean` | Chip | ✗ (MulOperation stubbed `True`) |
| `SP1Clean/ShiftLeftChip.lean` | Chip | ✗ (ShiftLeft stubbed `True`) |
| `SP1Clean/ShiftRightChip.lean` | Chip | ✗ (ShiftRight stubbed `True`) |
| `SP1Clean/DivRemChip.lean` | Chip | ✗ (DivRem stubbed `True`) |

## Scaling-difficulty answers (re: plan §"Success criteria")

The plan defined four questions. Answers:

1. **Is Tier-1 promotion truly ~50 LoC of boilerplate?**  
   **No — actual cost is ~93 LoC** (range 75–113). The mean is dominated
   by `Assertion.main` (10–25 lines depending on subcircuit count + drop
   list), `FormalSpec` (8–18 lines), `elaborated` instance + `Assumptions`
   stubs (5 lines), the `def assertion` bundle (5 lines), and the
   `/-! ## Full FormalAssertion promotion` scope-note docstring (10–15
   lines). The soundness + completeness theorems themselves total
   15–30 lines combined and are mechanical.

2. **Does the chip-level template transport across Load/Store?**  
   **Yes for Path-2.** LoadX0Chip and StoreByteChip are structurally
   indistinguishable from R-type chips at the Assertion level once
   Path-2's drop list is applied: their `main` does CPUState +
   ProgramTable + selector booleans. The `MemoryAccess` machinery is
   left in the legacy `Spec`; the trace-level OfflineMemory bridge
   will consume it there.  
   **Path-1 transport is untested** in this round (no Load/Store chip
   ships Path-1 today).

3. **Can raw `allHold_poly` clauses always be converted to subcircuits
   once the op is promoted?**  
   **Only for unconditional ones.** Gated clauses (multiplied by
   `is_real` / `is_real - op_a_0` / per-opcode selectors) require a
   gating combinator that Clean's subcircuit DSL currently lacks. See
   the Tier-2 probe finding above.

4. **What's the cost of a small operation-level promotion?**  
   **Skipped** for SubOperation (borrow/natural-form bridge). The cost
   of `AddOperation.assertion` (from iter-3) was ~150 LoC including the
   `byteOpcodeSpec_range16` / `byteOpcodeSpec_range16_of_lt` helpers.
   SubOperation would add another ~50–80 LoC for the borrow → natural
   bridge atop that.

## Net result

A single command verifies the round:

```bash
$ lake build SP1Clean
✔ [8540/8540] Built SP1Clean (3.0s)
Build completed successfully (8540 jobs).

$ grep -cE '^(error|warning):' build.log
0
```

Seven new chip-level FormalAssertion bundles, zero regressions, ~10 min
of incremental build time across the batch.
