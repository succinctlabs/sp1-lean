# Architecture consolidation — current checkpoint

**Status: implemented checkpoint, 2026-07-22.** This is the compact status board for the remediation
started by [`2026-07-architecture-consolidation.md`](2026-07-architecture-consolidation.md). The original
session log was intentionally removed from this living file; git history preserves it. Use
[`../release-audit.md`](../release-audit.md) for machine-derived proof counts and
[`../architecture.md`](../architecture.md) for the durable design.

## Landed architecture

| Area | Current state |
|---|---|
| Toolchain | Lean/mathlib 4.31; editable local Clean/Sail/RISCV migration dependencies; published immutable pins still required before release |
| Channels | four plain Clean `Channel`s with row-local guarantees; `VmChannel`, semantic channel payloads, and the parallel requirements veneer retired |
| Per-chip semantics | one `ChipKind.advance` path; all 25 registered chips prove `advance.isSome`; legacy `sailEquiv`/`reaches_sail` removed |
| Machine census | one `supportedChips` descriptor projects the circuits, semantic registry, opcode coverage, and routing tables |
| Witness identity | typed, deterministic decoding of every instruction table; the capstone cannot existentially choose unrelated rows |
| State/Program grounding | ranked exhaustive active-row order, PC walk, clock count, activity, registry membership, and committed Program decode proved |
| Dynamic grounding | typed exact-interaction adapter landed; Add has the first complete source-B/source-C Memory operand contract |
| Exact upstream AIR | v6.3.1 list-only 34-table execution + 6-table memory-boundary profiles, full public-value block, fail-closed manifest, exact natural interaction balance |
| Theorem surface | `supported_core_native_sound` is the supported-native target; `sp1_air_refinement`/`sp1_air_sound` are implemented conditional composition theorems over the exact execution cluster; execution and verifier theorems remain open |
| Verifier boundary | deterministic extraction/refinement combinator landed; ArkLib knowledge soundness remains a separate integration layer |
| Whole-chip faithfulness | generated complete Rust oracles and `ChipFaithful` proofs landed for Add and Sub |
| Operation debt | operation-level faithfulness is no longer the public boundary; all generated direct-to-circuit artifacts are gone, while transitional operation list/witness anchors remain |
| DivRem | nine old operation-shaped proof bodies removed; four-family semantic/evidence contract and routing proofs landed; one whole-chip evidence extraction seam remains |
| Completeness | ShiftRight restored with Clean's folded-boundary pattern; three 4.31-regressed chip proofs remain explicitly deferred |

## Current theorem frontier

The new path deterministically obtains exactly the active physical circuit rows, orders all of them through
the balanced State bus, grounds their Program fetches, and feeds a row-by-row Sail-chain constructor. One
live theorem remains:

```lean
supportedCore_orderedRows_dynamic
```

It must derive, for each ordered physical row at its Sail prefix:

1. timed Memory guarantees for every exact pull;
2. circuit soundness assumptions from those guarantees;
3. the circuit's semantic chip `Spec` on that exact row;
4. live register/RAM operand currency; and
5. the chip-specific `advanceReady` bundle.

`TypedInteractions.lean` and `TypedMemory.lean` now provide the generic transport. Add's instance in
`TypedMemoryContracts.lean` validates the desired chip-owned contract shape without introducing another
hand-written lookup substrate.

## Machine-checked proof debt

`scripts/run_audit.sh` gates exactly 8 syntactic deferral sites in six files:

| File / declaration | Class |
|---|---|
| `BranchChip.completeness` | chip completeness |
| `ShiftLeftChip.completeness` | chip completeness |
| `DivRemChip.completeness` | chip completeness |
| `DivRemChip.evidenceSoundness` | chip soundness |
| `DivRemChip.main_exposedChannelsLawful` | structural circuit packaging |
| `DivRemChip.requirementsChannelsLawful` | structural circuit packaging |
| `sp1_decoded_rows_sound` | frozen Eulerian-path packaging seam |
| `supportedCore_orderedRows_dynamic` | live machine-soundness seam |

The larger transitive carrier count comes from embedding full circuit records in the supported-machine
descriptor; it does not indicate one independent admission per carrier.

## Validated checkpoint

The current worktree has passed:

- `lake build SP1Clean` — 3580 jobs, no errors, warnings, or `info:` notes;
- `lake test` — 3196 jobs;
- `lake lint`; and
- `scripts/run_audit.sh` — 471 probes, 29 allowlisted transitive `sorryAx` carriers, no local
  `axiom`, no `skipKernelTC`, no main-library `native_decide`, and the exact deferral allowlist above.

## Next work, in dependency order

1. Generalize Add's exact register-operand Memory contract across the supported descriptor. Keep these
   contracts chip-local and derived from generated/native exposed interactions; do not add operation-level
   faithfulness bridges.
2. Extend timed Memory grounding to writes, RAM addresses, and repeated accesses to one location while
   preserving exact physical-row identity.
3. Derive each chip's circuit assumptions and `advanceReady` bundle from the grounded interaction facts.
4. Close `supportedCore_orderedRows_dynamic`, then re-run the capstone axiom census and remove the live
   machine-soundness admission.
5. Expand whole-chip Rust oracles/`ChipFaithful` coverage from Add/Sub across all supported chips, deleting
   obsolete operation extraction and duplicate substrates as each chip lands.
6. Instantiate `CoreAIRRefinementObligations` from the exact upstream lists and native grounding proofs;
   resolve the narrowly disclosed commit-row provenance premise.
7. Prove concrete raw-syscall handler refinements and the authenticated recursion relations (full-state
   stitching, global cumulative sums, deferred-proof authentication, and HALT).
8. Integrate the exact AIR relation with ArkLib's extractor/knowledge-soundness definitions for
   `sp1_verifier_sound`; PolyFun remains limited to useful semantic machine packaging unless a concrete
   proof obligation justifies more theory.

The three remaining chip-completeness regressions and the DivRem packaging fields can be repaired after the semantic
architecture stabilizes, unless one blocks a needed circuit or registry theorem.
