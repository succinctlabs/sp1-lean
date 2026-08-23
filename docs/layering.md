# The layering contract

*Machine-checked by `scripts/check_layering.sh` (run by `scripts/run_audit.sh` and the CI `guards`
job) against the stratum map in `scripts/layering.txt`. Exceptions live in
`scripts/layering_allowlist.txt`, each with a reason.*

## Why this exists

`docs/architecture.md`'s layer table states **topical** responsibilities — "`Faithful/` — whole-chip
comparisons against Rust". Topical rules cannot decide placement. `Interaction.toAccess` is topically
about extracted interactions and structurally about bus vocabulary, and it spent months in
`Faithful/` where the completeness layer could not reach it, *while declaring
`namespace SP1Clean.Extracted` the whole time*.

The same gap let a `Proofs → Faithful` import land in 2026-08 — the only one in the tree, against 30
going the other way. It compiled, and every other gate passed. This document is the structural rule
that topical responsibilities could not supply, and the gate is what makes it more than a convention.

## The three laws

**1. Direction.** Strata are totally ordered. A module imports only from strictly lower strata, or
within its own.

**2. Placement.** *A public declaration belongs in the lowest stratum that can state it* — the join
of the strata of the constants in its **type**, not its proof and not its first consumer.

Why the type: it makes module altitude and audit altitude the same number. For a theorem `T`,
everything in `Prf(T) \ Stmt(T)` is kernel-checked and cannot make `T` say something false, so the
risk lives entirely in `Stmt(T)` (see `docs/audit-surface.md`). A declaration sitting above its
statement vocabulary is exactly one whose audit surface is narrower than its position suggests — and,
concretely, one that a legitimate consumer below it cannot reach.

Private declarations are exempt: nothing below can cite them, so they cause no reachability harm.

**3. Namespace agreement.** A file's first `namespace SP1Clean.<Root>` must name the pillar its
stratum expects. AGENTS.md's "namespaces are decoupled from directory paths" remains true for
*sub*-namespaces; the pillar root is what must agree. This is nearly free and high-signal — it is the
check that would have caught `toAccess` on the day it was written.

Law 3 has a real exception class, and the allowlist distinguishes it: sometimes the namespace records
*intended vocabulary* rather than placement. `Model/Opcode.lean` declares `SP1Clean.Soundness`
deliberately (AGENTS.md sanctions it) because the soundness layer consumes it, while it structurally
belongs to the substrate — and `Model/` is measurably clean, with zero imports into any higher pillar.
When namespace and path disagree, one of them is wrong; deciding which requires reading the file.

## The strata

Defined in `scripts/layering.txt`, keyed on module path with globs where a directory straddles. Every
ordering below is supported by measured import counts, not by intent.

| # | Stratum | Carries |
|---|---|---|
| 0 | upstream | `ToMathlib/`, `ToClean/` — no SP1 concepts, destined for Mathlib/Clean |
| 1 | math | field-generic words, carries, bit operations |
| 2 | model | the SP1 substrate: messages, channels, buses, ledgers, Sail, schedules |
| 3 | extracted | generated Rust rows, assertion/interaction lists, manifest — plus the two hand-written modules that define the vocabulary those lists speak |
| 4 | contracts | semantic specs, public witness relations, the row view |
| 5 | operations | operation gadgets, readers, and their soundness |
| 6 | chips | chip circuits, their proofs, event→row builders |
| 7 | anchors | per-chip and list-level Rust faithfulness |
| 8 | machine | registry, ensemble, grounding, soundness capstone |
| 9 | assembly | trace record → built tables → `EnsembleWitness` |
| 10 | machine completeness | the converse capstone |
| 11 | composition | the composed exact→native artifact |

**Directories are not strata.** Four of them straddle, and the map says so with narrower rules:

- `Proofs/Chips/<X>/` holds three strata. `Defs`/`Formal` are chip-level; `Bridge.lean` needs
  `Soundness.ChipRow` and the Sail advance layer; `Contracts.lean` needs `Soundness.TypedMemory`,
  whose own closure reaches all 25 chips. The latter two already declare `namespace SP1Clean.Soundness`.
- `Soundness/` holds three. `RowView.lean` reaches nothing above stratum 3; `AIRCompleteness.lean`
  sits above `Proofs/Completeness/`; the rest is the machine.
- `Faithful/` held two until 2026-08. The composition half — the exact→native artifact — is now its
  own top-level pillar, `SP1Clean/Composition/`, so the directory names match the strata and the
  Faithful ↔ Soundness mutual pair is gone. `Faithful/SupportedMachine.lean` stayed behind: its
  content is stratum-7 faithfulness (it declares `ChipFaithfulnessAnchor` and
  `supportedChipFaithfulness`, and renaming those into a higher pillar would make them worse), and it
  reaches the machine for one thing only — `Soundness.supportedChips`, so the coverage certificate
  cannot drift from the registry. That coupling is the file's purpose, so it is an allowlist entry
  with a reason rather than a move.
- `FormalModel/` holds two — `TraceGen/` belongs with the chips.

Adding a narrower rule is always preferable to adding an allowlist entry. Splitting
`Proofs/Chips/*/{Bridge,Contracts}.lean` out removed 63 would-be exceptions at a stroke.

**The gate is only ever as sharp as the strata.** Two modules in the same stratum may import each
other freely, so a real ordering discovered *inside* a stratum should split it rather than be
tolerated. That is why strata 8–10 are separate: `Proofs/Completeness/Providers.lean` imports
`Soundness.SP1Ensemble`, and `Soundness/AIRCompleteness.lean` imports `Proofs.Completeness.Assembly`
— collapsing them would make both edges "same-stratum" and blind the gate to a future reversal.

## The seams

- **1→2** word/bitvector lemmas. **2→3** only `Model.SP1Constraint`, the extraction DSL's target.
- **2/3→4** messages, channels and generated column structures become `Spec`s and row views.
- **4→5→6** contracts, then gadgets, then chips.
- **6→7** a chip's `circuit` bundle meets its extracted oracle.
- **6/7→8** chips register into the machine. **8→9→10** ensemble, assembly, converse capstone.
- **10→11** the machine's relations are consumed by the composed artifact.

Crossing upward is a bug. Crossing several strata at once is legal but worth a glance —
`Soundness/RowView.lean` reaching `Extracted/` skips three.

## What this does *not* check, and why that matters

This contract is about **import direction and declaration placement**. It is not about whether every
module is built, and it is not about whether a theorem depends on another theorem. Three different
properties, three different gates, and conflating them is easy:

| Property | Gate | Answers |
|---|---|---|
| Every module is compiled and indexed | `check_root_index.sh` | "is this file in the build?" |
| Imports respect the order; declarations sit at their vocabulary | `check_layering.sh` | "is this file in the right place?" |
| A capstone's proof actually reaches a given module | *(the axiom census, partially)* | "does the theorem depend on it?" |

The third is what the external review's Finding 1 was about, and neither of the first two can detect
it. Every `Faithful/` module was always compiled and always imported by `SP1Clean.lean`; what was
missing was any *theorem* whose proof connected whole-chip faithfulness to the Sail capstone. The
review measured "98 of 433 modules unreachable from `Soundness/AIR.lean`" as a proxy — and note it is
only a proxy: module-import closure is necessary but not sufficient for proof dependency, since a
module can be imported without the proof term touching it. The sharp version is the constant closure.

So: a universal-import check (`lake exe mk_all`, or our `check_root_index.sh`) cannot catch Finding 1,
and this layering gate cannot either. Holding that composition in place wants a gate that *requires*
edges rather than forbidding them — asserting that named modules are in the closure of named capstone
theorems. Today it is held only by convention plus a comment at `scripts/gen_axiom_probe.py:132`.
