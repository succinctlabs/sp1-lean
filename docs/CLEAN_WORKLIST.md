# SP1Clean canonical-pattern migration — worklist

Helper-dispatch table for the master plan
(`~/.claude/plans/make-a-plan-to-sleepy-cocke.md`). Derived from the audit
in [`docs/CLEAN_AUDIT.md`](CLEAN_AUDIT.md). Each row is a self-contained
task: read the named files, apply the recipe for the row's phase, push
to the named branch, ping main to merge.

## Coordination

- **Main owns this file.** Helpers don't write to it directly; they
  announce claims via chat ("Claiming p2-addi") and main flips the cell.
- **Status flow**: `open` → `in-progress:<helper-id>` → `merged`.
  (`merged` rows can be deleted in a future pruning pass.)
- **Branching**: commits land directly on `dtumad/clean` — no per-task
  branches. Helpers commit-and-push when work is green; main pulls.
  Reverts are by `git revert <sha>` against `dtumad/clean`.
- **Disjoint file scope**: every row's `files` column lists the exact
  files it touches. Two simultaneously-in-progress tasks must have
  disjoint file sets. Reader prereq tasks (PR-*) for Phase 3 may need to
  land first; helpers wait.
- **Reserved by main, never claimed by helpers**:
  `SP1Clean/Soundness/*`, `SP1Clean/AddChip/*`, `SP1Foundations/*`,
  `SP1Operations/*` (main absorbs `iff_sp1_full` additions there),
  `docs/MULTIPLICITY_BUS.md`, `docs/CLEAN_AUDIT.md`, this file.

## Phase order

Phase 2 (mechanical RawSpec drops) → Phase 3 (Gated reader migration) →
Phase 4 (memory routing) → Phase 5 (operation stub closure) → Phase 6
(scope-fence breadcrumbs) → Phase 7 (dead-code removal). Within a phase,
tasks parallelize. **Each phase end is a green-build sync point: main
runs `lake build SP1Clean` and verifies 0 errors and warning count
unchanged before unblocking the next phase.**

---

## Phase 2 — Mechanical FormalSpec migration

Recipe: drop `<Op>.RawSpec` / `<Op>.Spec` conjunct from chip's
`Cols.FormalSpec`; restate as `is_real = 1 → (isU64 ∧ BV)`; update
`Lemmas.allHold_iff_structural` to bridge via `<Op>.iff_sp1_full`;
re-thread `Circuit.{soundness,completeness}`; verify SailBridge
axiom-clean. Closes ~5–7 sorries.

| task-id | target | files | claim | status |
|---------|--------|-------|-------|--------|
| **p2-addi** | AddiChip | `SP1Clean/AddiChip/{Cols,Circuit,Lemmas,SailBridge}.lean` (+ AddiChip-specific shape fixes in `SP1Clean/Soundness/{IsRealBinary,MemoryConsistencyClock}.lean`) | main | merged (`4656a5d`) |
| **p2-jal** | JalChip | `SP1Clean/JalChip.lean` | helper-2 | open |
| **p2-sub** | SubChip | `SP1Clean/SubChip/{Cols,Circuit,Lemmas,SailBridge}.lean` | helper-1 | open |
| **p2-subw** | SubwChip | `SP1Clean/SubwChip/{Cols,Circuit,Lemmas,SailBridge}.lean` | helper-2 | open |
| **p2-addw** | AddwChip | `SP1Clean/AddwChip/{Cols,Circuit,Lemmas,SailBridge}.lean` | helper-1 | open |
| **p2-jalr** | JalrChip | `SP1Clean/JalrChip.lean` | helper-2 | open |
| **p2-utype** | UTypeChip (also Phase 3 — CPUState Gated promotion) | `SP1Clean/UTypeChip/{Cols,Circuit,Lemmas,SailBridge}.lean` | main | open |
| **p2-main-iff_sp1_full** (prereq for p2-sub / p2-subw / p2-addw / p2-jal / p2-jalr / p2-utype) | Add `<Op>.iff_sp1_full` + `spec_inv` to SP1Operations | `SP1Operations/Operation/{SubOperation/SubOperation,SubwOperation/SubwOperation,AddwOperation/AddwOperation}.lean` | main | open (blocks helper rows above) |
| **p2-soundness** | Trace-soundness driver shape updates | `SP1Clean/Soundness/{IsRealBinary,MemoryConsistency,MemoryConsistencyClock,StateConsistency}.lean` | main | open (after all p2-* helper rows merge) |

## Phase 3 — Reader-level Gated migration

Recipe: migrate `cpuStateSpec` / `aluTypeReaderSpec` / `rtypeReaderSpec` →
`.Gated.Assertion.Spec`; reshape `FormalSpec` as semantic-only gated on
`is_real = 1`; close SailBridge sorries. **Each row depends on the named
prereq.** Closes ~15–25 sorries.

| task-id | target | files | prereqs | claim | status |
|---------|--------|-------|---------|-------|--------|
| **p3-prereq-readers** | Audit + add missing `.Gated` reader variants if any | `SP1Clean/Reader/{ITypeReaderImmutable,...}.lean` (depending on audit) | — | main | open |
| **p3-mul** | MulChip | `SP1Clean/MulChip/{Cols,Circuit,Lemmas,SailBridge}.lean` | p3-prereq-readers, p5-mulop | helper-1 | open |
| **p3-shl** | ShiftLeftChip | `SP1Clean/ShiftLeftChip/{Cols,Circuit,Lemmas,SailBridge}.lean` | p3-prereq-readers | helper-2 | open |
| **p3-shr** | ShiftRightChip | `SP1Clean/ShiftRightChip/{Cols,Circuit,Lemmas,SailBridge}.lean` | p3-prereq-readers | helper-1 | open |
| **p3-bitwise** | BitwiseChip | `SP1Clean/BitwiseChip/{Cols,Circuit,Lemmas,SailBridge}.lean` | p3-prereq-readers | helper-2 | open |
| **p3-lt-sail** | LtChip Sail-bridge closure (chip body mostly canonical already) | `SP1Clean/LtChip/{Circuit,Lemmas,SailBridge}.lean` | — | helper-1 | open |

## Phase 4 — Memory-routing migration (Load* / Store*)

Recipe: migrate `MemoryAccess` records → `LoadMemoryAccessGated.assertion` /
`StoreMemoryAccessGated.assertion`; promote `CPUState.Assertion.Spec` →
`.Gated`; add semantic conjunct (`is_real = 1 → toBitVec64 ...`); update
`ChipRow.memoryAccesses .<chip>` to `[]`; add
`memoryAccessesValid_of_spec_<chip>` discharge in Soundness (vacuous, per
[[memoryaccesses-vacuous-for-gated-chips]]).

Two parallel tracks: helper-1 = Load*, helper-2 = Store*. Closes ~10–20
sorries (chip bodies presently sorry-free but propagating sub-circuit
sorries; gets the row count down once they're routed).

| task-id | target | files | claim | status |
|---------|--------|-------|-------|--------|
| **p4-loadbyte** | LoadByteChip | `SP1Clean/LoadByteChip.lean` | helper-1 | open |
| **p4-loadhalf** | LoadHalfChip | `SP1Clean/LoadHalfChip.lean` | helper-1 | open |
| **p4-loadword** | LoadWordChip | `SP1Clean/LoadWordChip.lean` | helper-1 | open |
| **p4-loaddouble** | LoadDoubleChip | `SP1Clean/LoadDoubleChip.lean` | helper-1 | open |
| **p4-storebyte** | StoreByteChip | `SP1Clean/StoreByteChip.lean` | helper-2 | open |
| **p4-storehalf** | StoreHalfChip | `SP1Clean/StoreHalfChip.lean` | helper-2 | open |
| **p4-storeword** | StoreWordChip | `SP1Clean/StoreWordChip.lean` | helper-2 | open |
| **p4-storedouble** | StoreDoubleChip | `SP1Clean/StoreDoubleChip.lean` | helper-2 | open |
| **p4-soundness** | Per-chip `memoryAccessesValid_of_spec_<chip>` + `ChipRow.memoryAccesses` empties (bulk) | `SP1Clean/Soundness/MemoryConsistency.lean` | main | open (after all p4-* rows merge) |

## Phase 5 — Completeness-gap / operation-stub closure

Add missing `iff_sp1_full` siblings (main-owned, in `SP1Operations/`);
close operation-level sorries that block consumer chips.

| task-id | target | files | claim | status |
|---------|--------|-------|-------|--------|
| **p5-mulop** | MulOperation iff_sp1_full + close 3 sorries | `SP1Operations/Operation/MulOperation/MulOperation.lean`, `SP1Clean/Operations/MulOperation.lean` | main | open (prereq for p3-mul) |
| **p5-addressshape** | AddressShape soundness + completeness | `SP1Clean/Operations/AddressShape.lean` | helper-1 | open |
| **p5-iszeroword** | IsZeroWordOperation proof bodies | `SP1Clean/Operations/IsZeroWordOperation.lean` | helper-2 | open |
| **p5-iseqword** | IsEqualWordOperation proof bodies | `SP1Clean/Operations/IsEqualWordOperation.lean` | helper-1 | open |
| **p5-u16cmp** | U16CompareOperation proof bodies | `SP1Clean/Operations/U16CompareOperation.lean` | helper-2 | open |
| **p5-ltsigned-bridge** | LtOperationSigned bridge body sorry | `SP1Clean/Operations/LtOperationSigned.lean` | helper-1 | open |
| **p5-bitwise-formalspec** | BitwiseOperation Spec promotion (matches Phase-3 p3-bitwise's recipe) | `SP1Clean/Operations/BitwiseOperation.lean` | helper-2 | open |

## Phase 6 — Scope-fenced complex chips

Recipe: leave current sorries; add `-- TODO[clean-master-plan-phase-6,<chip-id>]: <breadcrumb>` comment above each `sorry` token pointing at what unblocks closure. **No semantic migration in this phase.**

| task-id | target | files | claim | status |
|---------|--------|-------|-------|--------|
| **p6-divrem-breadcrumb** | DivRemChip sorry breadcrumb sweep | `SP1Clean/DivRemChip.lean`, `SP1Clean/DivRemChip/*.lean` | helper-1 | open |
| **p6-branch-breadcrumb** | BranchChip sorry breadcrumb sweep | `SP1Clean/BranchChip.lean`, `SP1Clean/Branch/Circuit.lean` | helper-2 | open |
| **p6-loadx0** | LoadX0Chip — after Phase 4 lands, port the Load*-shape with `op_a_write_value = 0` specialization | `SP1Clean/LoadX0Chip.lean` | main | open (depends on Phase 4 completion) |
| **p6-memoryglobal** | MemoryGlobalChip — author the FormalAssertion + trace-level memoryAccess discharge | `SP1Clean/MemoryGlobalChip.lean`, `SP1Clean/Soundness/MemoryConsistency.lean` | main | open |

## Phase 7 — Ungated dead-code removal

After Phases 2–6 land, scan for un-gated operation/reader decls whose only call sites were the migrated chips. Delete; build verifies.

| task-id | target | files | claim | status |
|---------|--------|-------|-------|--------|
| **p7-deadcode-sweep** | Identify + delete un-gated `<Op>.assertion` / `<Reader>.assertion` decls with zero non-test call sites | `SP1Clean/Operations/*.lean`, `SP1Clean/Reader/*.lean` | helper-1 | open (gated on all prior phases merged) |

---

## Out of this worklist (deferred to a follow-up plan)

- DivRemChip full migration to canonical (post-Phase 7 cleanup pass).
- BranchChip canonical migration (6-way selector + PC update semantics).
- Replacing `_root_.<Chip>.correct_*` invocations in SailBridge files with direct riscv-lean BitVec bridges (downstream of the FormalSpec migration; cuts the legacy SP1Chips dependency).
- `Compare/LtOperationSigned.lean` (separate from `Operations/LtOperationSigned.lean`) — audit and possibly merge.

## Helper handoff cheatsheet

1. Read the master plan (`~/.claude/plans/make-a-plan-to-sleepy-cocke.md`) for the phase recipe.
2. Read `docs/CLEAN_AUDIT.md` row for your target — gives you the D1–D5 violations to fix.
3. Read AddChip canonical reference: `SP1Clean/AddChip/{Cols,Circuit,Lemmas,SailBridge}.lean` (one example is worth a thousand recipes).
4. Read `docs/MULTIPLICITY_BUS.md` §"Operation contract template" if your task is Phase 2 or 5 (operation-level).
5. Read `MEMORY.md` for project-wide gotchas — especially `feedback_memoryaccesses_vacuous_for_gated_chips.md` if you're touching Soundness.
6. Commit directly on `dtumad/clean` (no per-task branches); push when green; ping main so the worklist row gets flipped to `merged`.
