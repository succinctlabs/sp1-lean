> **Point-in-time snapshot — regenerate before relying on it.**

# Axiom & trust ledger

**Current green build.** Every row below is machine-checked by `#print axioms` on the cached build
(`lake env lean` on a probe importing `SP1Clean`). The ledger exists because comments and memory notes
drift (e.g. earlier notes claimed `correct_jal_native` carried a `sorryAx`; it does not).

> **Snapshot — re-generate before release.** Re-run the `#print axioms` harness on a current green build
> (see `../release-audit.md` Appendix A) before citing these counts. The *current* `sorry` set is the five
> listed in `../release-audit.md` §2 / `../roadmap.md`.

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
| `BranchChip.completeness` | baseline | clean |
| `JalChip.soundness`, `JalrChip.soundness`, `UTypeChip.soundness` | baseline | clean |
| `LoadDoubleChip.soundness`, `StoreDoubleChip.soundness` | baseline | clean |
| `MulChip.soundness` | baseline + bv_decide | clean (bv_decide) |
| `MulChip.completeness` | baseline + **sorryAx** | **incomplete** |
| `DivRemChip.soundness` | baseline | clean |
| `DivRemChip.completeness` | baseline + **sorryAx** | **incomplete** |

All 25 wired chips have **sorry-free soundness**. (Soundness was checked directly for a
representative set; the per-chip `kind`s below additionally certify the Sail-reaching path for all 25.)

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
| `Faithful.branch_asserts_faithful`, `Faithful.branch_interactions_faithful` | baseline | clean |

## Capstone (bespoke multi-bus `TraceValid`) — RETIRED

The bespoke `Soundness/MachineSoundness.lean` + `Soundness/MachineConsistency.lean` capstone were
**deleted** — the gated capstone below is the sole whole-machine capstone. The all-chips Sail-model
trust base it surfaced now lives in `Soundness.gatedExecution_allChips` (below).

## Gated VM capstone (the primary execution capstone)

The `Soundness/GatedVm/` modules derive the whole-program execution from the **gated state-bus balance
alone** (the Eulerian `exists_trail`), dropping every trace-shape side condition (`clkInjective`,
`clkAdvance`, the memory-ordering conditions) the retired bespoke capstone needed. All sorry-free.

| Theorem | Axiom set | Verdict |
|---|---|---|
| `Soundness.GatedVm.exists_trail` (balance ⇒ trail, Eulerian core) | baseline | clean |
| `Soundness.balanced_state_bus` (state bus ⇒ `GatedVm.Balanced`) | baseline | clean |
| `Soundness.state_trail_of_balance` (balance ⇒ ∃ real-row trail) | baseline | clean |
| `Soundness.GatedVm.chipRows_step_sound` (per-chip Sail dispatch) | baseline | clean |
| `Soundness.gatedExecution_of_specs_and_balance` (the capstone) | baseline | clean (generic over `rows`) |
| `Soundness.gatedExecution_allChips` (25-chip instantiation) | baseline + bv_decide + `sys_enable_experimental_extensions` + `load_reservation` + `match_reservation` + `plat_term_write` | clean (Sail-model) |
| `LookupAccessList.isConsistentBalanced_of_intCast_zero` (item-5-proper F↔ℤ bridge core) | baseline | clean |
| `Soundness.sp1FormalEnsemble` / `sp1_machine_soundness` (the final Clean `FormalEnsemble`) | baseline + bv_decide + **`sorryAx`** | **one residual `sorry`** (`sp1_gatedExecution_prereqs`) |

The generic gated capstone is fully axiom-clean (abstract `rows`/`sailEquiv`); the Sail-model platform
axioms appear only in `gatedExecution_allChips`, inherited from the 25 concrete chip `kind`s. The
`gatedExecution_*` results take the native state-bus balance (`isConsistentBalanced`) as a hypothesis —
the LogUp/GKR trust boundary. Deriving it from Clean's ensemble `Statement.BalancedChannels` is
documented future work (`../roadmap.md` B5).

`sp1FormalEnsemble` (`Soundness/SP1GatedVm.lean`) packages that derivation into a Clean `FormalEnsemble`
with a meaningful `Spec` (a valid RISC-V-Sail execution trail from the public `pc_start` to `next_pc`).
Its `soundness` assembly is sorry-free — it threads the gated capstone — but depends on one isolated
premise `sp1_gatedExecution_prereqs` (the witness→prereqs bridge: the Clean→native balance translation +
the 25-chip witness→`ChipRow` decode), the one remaining `sorryAx` in the Ensemble area. Because its
proof threads that abstract premise rather than the concrete chip dispatch, `sp1_machine_soundness`
currently inherits the bv_decide axioms but **not** the Sail-model ones; closing the premise wires the
25 concrete `kind`s (and their Sail-model footprint, per `gatedExecution_allChips`) through.

## Coverage / completeness scaffold

| Theorem | Axiom set | Verdict |
|---|---|---|
| `Soundness.routeName_eq` / `coverage_kinds_eq_registry` / `wiredNames_eq_registry` (the `Opcode → chip → Sail` table, tied to `allChipKinds`) | baseline + bv_decide + Sail-model | clean (Sail-model, inherited from the concrete `kind`s) |
| `Soundness.opcode_classified` / `covered_iff_routed` / `reachable_subset_wired` (covered/uncovered ledger, `by decide`) | baseline | clean |
| `Soundness.sp1_partial_completeness` / `incomplete_wired_names` (partial-VM-completeness over the 21 chips with sorry-free `circuit.completeness`) | baseline | clean |

The coverage routing (`Coverage.lean`) audits through each `ChipKind.name` (a `String`) so its guards are
`by decide`; the `kind`-level table inherits the Sail-model platform axioms from the concrete chip `kind`s.
The completeness scaffold (`Completeness.lean`) is fully axiom-clean — the open step (assembling per-row
witnesses into one balanced `EnsembleWitness`) is the completeness dual of `sp1_gatedExecution_prereqs`,
documented and not `sorry`'d.

## Complete `sorryAx` set (the only project-level incompleteness)

1. `MulChip.completeness`
2. `ShiftLeftChip.completeness`
3. `ShiftRightChip.completeness`
4. `DivRemChip.completeness`
5. `Soundness.sp1_gatedExecution_prereqs` (the final-ensemble witness→prereqs bridge)

No `axiom` declarations, no `admit`, no `@[implemented_by]`/`native_decide` exist in `SP1Clean/`. Every
wired chip's **soundness** and **Sail bridge** are `sorryAx`-free; the debt is concentrated in four
**completeness** proofs (ShiftLeft/ShiftRight/Mul/DivRem) and the single **final-ensemble** bridge
`sp1_gatedExecution_prereqs` (the Clean→native balance translation + 25-chip witness decode; its
`soundness` assembly is sorry-free).

## Reproduce

Create a probe importing `SP1Clean` with `#print axioms <name>` lines and run
`lake env lean <probe>.lean` (the build must be current; `#print axioms` reads the cached oleans).
Do **not** rely on `grep sorry` or on `lean_verify` against a stale LSP — both gave wrong answers
during earlier audits.
