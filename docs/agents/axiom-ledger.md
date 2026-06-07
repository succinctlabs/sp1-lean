# Axiom & trust ledger

**Generated:** 2026-06-04, by `#print axioms` over the cached build (`lake env lean` on a probe
importing `SP1Clean`). Every row here is machine-checked, not read from a comment — this
ledger exists precisely because comments and memory notes had drifted (e.g. notes claimed
`correct_jal_native` carried a `sorryAx`; it does not).

> **Snapshot — re-generate before release.** This is a point-in-time census; theorems have been added
> since (e.g. `DivRemChip.soundness`, the gated capstone). Re-run the `#print axioms` harness on a current
> green build (see `../release-audit.md` Appendix A) before citing these counts. The *current* `sorry` set is
> the five listed in `../release-audit.md` §2 / `../roadmap.md`.

## How to read the axiom sets

| Axiom | Meaning | Status in this project |
|---|---|---|
| `propext`, `Classical.choice`, `Quot.sound` | The three standard Lean/mathlib axioms | **Baseline** — "axiom-clean" = exactly these |
| `Lean.ofReduceBool`, `Lean.trustCompiler` | `bv_decide`'s trusted bit-blasting / kernel `reduceBool` | **Accepted** (used by `Word`/`BitVec` decision procedures) |
| `sys_enable_experimental_extensions` | LeanRV64D Sail model: experimental-extension enable flag | **Sail-model trust base** (not ours) |
| `load_reservation`, `match_reservation`, `plat_term_write` | LeanRV64D Sail model: LR/SC reservation + platform terminal-write hooks | **Sail-model trust base** (not ours) |
| `sorryAx` | An incomplete proof | **Project debt** — enumerated below; nothing else carries it |

The Sail-model axioms (`sys_enable_experimental_extensions`, `load_reservation`,
`match_reservation`, `plat_term_write`) are **declared in the `LeanRV64D` Sail RISC-V model**
(the `succinctlabs/sail-riscv-lean @ dtumad/clean-native` dep), not in this repo. They enter a theorem only when it reaches the Sail
spec for a control-flow or memory instruction. They are an honest part of the trust base (you are
trusting the generated RISC-V Sail model), exactly like trusting the model's `execute_*` definitions.

## Chip soundness / completeness

| Theorem | Axiom set | Verdict |
|---|---|---|
| `AddChip.soundness` | baseline | clean |
| `AddChip.completeness` | baseline | clean |
| `SubChip.soundness` | baseline | clean |
| `LtChip.soundness` | baseline | clean |
| `BitwiseChip.soundness` | baseline + bv_decide | clean (bv_decide) |
| `ShiftLeftChip.soundness` | baseline | clean |
| `ShiftLeftChip.completeness` | baseline + **sorryAx** | **incomplete** |
| `ShiftRightChip.soundness` | baseline | clean |
| `ShiftRightChip.completeness` | baseline + **sorryAx** | **incomplete** |
| `BranchChip.soundness` | baseline | clean |
| `BranchChip.completeness` | baseline + **sorryAx** | **incomplete** |
| `JalChip.soundness`, `JalrChip.soundness`, `UTypeChip.soundness` | baseline | clean |
| `LoadDoubleChip.soundness`, `StoreDoubleChip.soundness` | baseline | clean |
| `MulChip.soundness` | baseline + bv_decide | clean (bv_decide) — **but unwired** (no Bridge) |
| `MulChip.completeness` | baseline + **sorryAx** | **incomplete** |
| `DivRemChip.soundness` | baseline + **sorryAx** | **incomplete** (placeholder `main`) |
| `DivRemChip.completeness` | baseline + **sorryAx** | **incomplete** |

All 22 wired chips have **sorry-free soundness**. (Soundness was checked directly for a
representative set; the per-chip `kind`s below additionally certify the Sail-reaching path for all 22.)

## Sail bridges & ChipKind registrations

`<Chip>.kind` is what enters the chip into the capstone; its axiom set is the Sail-reaching
footprint for that chip.

| Theorem | Axiom set | Verdict |
|---|---|---|
| `AddSail.correct_add_native`, `AddSail.add_chip_reaches_sail` | baseline | clean (no Sail-platform axioms) |
| `JalSail.correct_jal_native`, `JalSail.jal_chip_reaches_sail` | baseline + bv_decide + `sys_enable_experimental_extensions` | clean (Sail-model) |
| `AddChip.kind`, `AddiChip.kind`, `AddwChip.kind`, `SubChip.kind`, `SubwChip.kind`, `BitwiseChip.kind`, `LtChip.kind`, `ShiftLeftChip.kind`, `ShiftRightChip.kind`, `UTypeChip.kind` | baseline | clean (10 ALU/U-type chips reach Sail with **no** Sail-platform axioms) |
| `JalChip.kind`, `JalrChip.kind`, `BranchChip.kind` | baseline + bv_decide + `sys_enable_experimental_extensions` | clean (Sail-model) |
| `LoadByteChip.kind`, `LoadHalfChip.kind`, `LoadWordChip.kind`, `LoadDoubleChip.kind`, `LoadX0Chip.kind` | baseline + bv_decide + `sys_enable_experimental_extensions` + `load_reservation` + `plat_term_write` | clean (Sail-model) |
| `StoreByteChip.kind`, `StoreHalfChip.kind`, `StoreWordChip.kind`, `StoreDoubleChip.kind` | baseline + bv_decide + `sys_enable_experimental_extensions` + `match_reservation` + `plat_term_write` | clean (Sail-model) |

**No bridge / kind carries `sorryAx`.** The control-flow and memory `kind`s pull Sail-model
platform axioms; loads add `load_reservation`, stores add `match_reservation`, both add
`plat_term_write` — exactly the Sail LR/SC + terminal-write hooks on those execute paths.

## Faithfulness anchors

| Theorem | Axiom set | Verdict |
|---|---|---|
| `Faithful.addcols_asserts_faithful`, `Faithful.addcols_interactions_faithful` | baseline | clean (full `↔`) |
| `Faithful.mul_asserts_faithful` | baseline | clean (forward `→` only) |
| `Faithful.branch_asserts_faithful`, `Faithful.branch_interactions_faithful` | baseline + **sorryAx** | **incomplete** |

## Capstone (bespoke multi-bus `TraceValid`) — RETIRED 2026-06-05

The bespoke `Soundness/MachineSoundness.lean` (`traceValid_of_specs_and_balance''`) +
`Soundness/MachineConsistency.lean` (`TraceMachineBalancedWith'`, the `*_of_machine'` balance derivations)
capstone, and its `traceValid_allChips''` all-chips acceptance test (plus the per-chip `traceValid_*_mixed`
examples), were **deleted** — the gated capstone below is the sole whole-machine capstone (the bespoke had
no remaining code users, and the gated path's hypotheses are a strict subset). The all-chips Sail-model
trust base it surfaced now lives in `Soundness.gatedExecution_allChips` (below).

(The bespoke *whole-program fold* layer — `WholeProgramExecution` / `trace_is_valid_execution` /
`trace_executes_program` + the `OperandBinding` oracle in `Soundness/ProgramFold.lean` — was retired
2026-06-05: its whole-program guarantee is restated by the gated `GatedExecution` / `sp1Spec` below.)

## Gated VM capstone (path b — the primary execution capstone)

Added 2026-06-05. The `Soundness/GatedVm/` modules re-derive the whole-program execution from the
**gated state-bus balance alone** (the Eulerian `exists_trail`), dropping *every* trace-shape side
condition (`clkInjective`, `clkAdvance`, the memory-ordering conditions) the bespoke `''` capstone
needs. All sorry-free.

| Theorem | Axiom set | Verdict |
|---|---|---|
| `Soundness.GatedVm.exists_trail` (balance ⇒ trail, Eulerian core) | baseline | clean |
| `Soundness.balanced_state_bus` (state bus ⇒ `GatedVm.Balanced`) | baseline | clean |
| `Soundness.state_trail_of_balance` (balance ⇒ ∃ real-row trail) | baseline | clean |
| `Soundness.GatedVm.chipRows_step_sound` (per-chip Sail dispatch) | baseline | clean |
| `Soundness.gatedExecution_of_specs_and_balance` (the capstone) | baseline | clean (generic over `rows`) |
| `Soundness.gatedExecution_allChips` (22-chip instantiation) | baseline + bv_decide + `sys_enable_experimental_extensions` + `load_reservation` + `match_reservation` + `plat_term_write` | clean (Sail-model) |
| `LookupAccessList.isConsistentBalanced_of_intCast_zero` (item-5-proper F↔ℤ bridge core) | baseline | clean |
| `Soundness.sp1FormalEnsemble` / `sp1_machine_soundness` (the final Clean `FormalEnsemble`) | baseline + Sail-model + **`sorryAx`** | **one residual `sorry`** (`sp1_gatedExecution_prereqs`) |

Same pattern as the bespoke capstone: the generic gated capstone is fully axiom-clean (abstract
`rows`/`sailEquiv`); the Sail-model platform axioms appear only in `gatedExecution_allChips`, inherited
from the 22 concrete chip `kind`s — the 22 concrete chip `kind`s' Sail-model trust base (also surfaced by
`Soundness/Coverage.lean`'s `coverage`/`routeName_eq`). The
`gatedExecution_*` results take the native state-bus balance (`isConsistentBalanced`) as a hypothesis —
the LogUp/GKR trust boundary, *identical* to the bespoke capstone's (inside `TraceMachineBalancedWith'`).
Deriving it instead from Clean's ensemble `Statement.BalancedChannels` is documented future work
(`../roadmap.md` B5) — a trust-base *reduction below* bespoke, not needed for ≥-bespoke parity.

`sp1FormalEnsemble` (`Soundness/SP1GatedVm.lean`) packages exactly that derivation into a Clean
`FormalEnsemble` with a meaningful `Spec` (a valid RISC-V-Sail execution trail from the public
`pc_start` to `next_pc`). Its `soundness` *assembly* is sorry-free — it threads the gated capstone — but
it depends on the single isolated premise `sp1_gatedExecution_prereqs` (the witness→prereqs bridge: the
Clean→native balance translation + the 22-chip witness→`ChipRow` decode), which is the one remaining
`sorryAx` in the Ensemble area (it replaces the two scaffold `sorry`s of the deleted `FlatEnsemble.lean`).

## Coverage / completeness scaffold (added 2026-06-05)

| Theorem | Axiom set | Verdict |
|---|---|---|
| `Soundness.routeName_eq` / `coverage_kinds_eq_registry` / `wiredNames_eq_registry` (the `Opcode → chip → Sail` table, tied to `allChipKinds`) | baseline + bv_decide + Sail-model | clean (Sail-model, inherited from the concrete `kind`s) |
| `Soundness.opcode_classified` / `covered_iff_routed` / `reachable_subset_wired` (covered/uncovered ledger, `by decide`) | baseline | clean |
| `Soundness.sp1_partial_completeness` / `incomplete_wired_names` (partial-VM-completeness over the 19 chips with sorry-free `circuit.completeness`) | baseline | clean |

The coverage routing (`Coverage.lean`) audits through each `ChipKind.name` (a `String`) so its guards are
`by decide`; the `kind`-level table inherits the Sail-model platform axioms from the concrete chip `kind`s
(same trust base as `gatedExecution_allChips`). The completeness scaffold (`Completeness.lean`) is fully
axiom-clean — the open step (assembling per-row witnesses into one balanced `EnsembleWitness`) is the
completeness dual of `sp1_gatedExecution_prereqs`, documented and not `sorry`'d.

## Complete `sorryAx` set (the only project-level incompleteness)

1. `MulChip.completeness`
2. `DivRemChip.soundness`
3. `DivRemChip.completeness`
4. `ShiftLeftChip.completeness`
5. `ShiftRightChip.completeness`
6. `BranchChip.completeness`
7. `Faithful.branch_asserts_faithful`
8. `Faithful.branch_interactions_faithful`
9. `Soundness.sp1_gatedExecution_prereqs` (the final-ensemble witness→prereqs bridge; replaces the two
   deleted `FlatEnsemble.lean` scaffold `sorry`s — net −1)

No `axiom` declarations, no `admit`, no `@[implemented_by]`/`native_decide` exist in
`SP1Clean/`. Every wired chip's **soundness** and **Sail bridge** are `sorryAx`-free; the
debt is concentrated in five **completeness** proofs (ShiftLeft/ShiftRight/Branch/Mul + DivRem),
DivRem **soundness** (placeholder `main`), the **Branch faithfulness** anchor, and the single
**final-ensemble** bridge `sp1_gatedExecution_prereqs` (the Clean→native balance translation + 22-chip
witness decode; its `soundness` *assembly* is sorry-free).

## Reproduce

Create a probe importing `SP1Clean` with `#print axioms <name>` lines and run
`lake env lean <probe>.lean` (the build must be current; `#print axioms` reads the cached oleans).
Do **not** rely on `grep sorry` or on `lean_verify` against a stale LSP — both gave wrong answers
during this audit.
