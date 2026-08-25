# Independent semantic and integration audit — 2026-08-12

## Purpose and status

This is a second-opinion audit of `sp1-clean-native`, performed after the 2026-08 release audit and
by a different agent from the one that authored most of the library and its prior audit. It is a
point-in-time engineering record, not a replacement for the current theorem statements in
[`verification-report.md`](../verification-report.md) or the generated gates in
[`release-audit.md`](../release-audit.md).

The audit branch is `dtumad/independent-semantic-audit-2026-08`, stacked on
`dtumad/release-audit-2026-08` at `064bee0915b8effa4d73e03e83e86bf6a43bb530`. The SP1 semantic source
remains pinned to `a630089d9ff484ec6f2feade8d0afbb1447eed11` (v6.3.1 plus eight commits).

The review concentrated on:

- broad semantic correctness and theorem-boundary modeling;
- the exact Core AIR → native grounding → official Sail chain;
- readiness for an executable verifier and ArkLib/VCVio knowledge-soundness integration;
- Clean idioms, naming, standardization, and auditability for SP1 and Clean readers; and
- comparison with OpenVM FV and S-two AIR verification.

It did not repeat a line-by-line blind derivation of all 25 chip Specs. Instead it independently
challenged the joints most likely to invalidate a correct-looking chip library: relation strength,
program commitment/decode, global bus grounding, system-table ownership, witness non-vacuity,
knowledge-extractor composition, and claim boundaries.

## Executive result

The native 25-chip foundation is strong and is a sound base to keep building on. I found no new
semantic contradiction in the implemented chip slice, no illicit operation-level Rust
correspondence, no missing current-pin row selector family, and no overclaimed unconditional
`sp1_air_sound` theorem. Whole-chip faithfulness, true Clean subcircuit composition, structural bus
messages, and the explicit boundary predicates are the right architectural choices.

The repository is not yet ready to present its exact-Core or verifier layer as closed. Three items
should be treated as release-critical for that next claim:

1. the six Core system tables still need to derive the native program/memory/timestamp boundary and
   ordered event trace;
2. application-level loader/platform/code-memory contracts must remain visible in the final theorem
   type rather than disappearing inside an “AIR refinement” bundle; and
3. ArkLib's actual knowledge-soundness API requires a same-witness target preimage, not the
   witness-type-changing post-composition previously sketched in `FormalModel/Verifier.lean`.

The third item was a concrete disagreement with the previous design sketch and is fixed on this
branch. A valid committed-window Add regression was also added to expose the exact remaining
program-decode seam.

## Finding classes and priorities

- **NEW** — not clearly recorded by the previous audit.
- **DISAGREE** — the prior statement or proposed interface was materially wrong.
- **NARROW** — the prior statement is directionally right but needs a tighter boundary.
- **CONFIRM** — independently checked and agreed.
- **P1** — must be resolved before publishing the next stronger exact-AIR/verifier claim.
- **P2** — important integration or auditability work; can coexist with the current native claim.
- **P3** — polish, standardization, or future-proofing.

## Findings

### F1 — ArkLib post-composition changed the knowledge game's witness type

**P1 · NEW + DISAGREE · fixed locally**

The former `FormalModel/Verifier.lean` sketch concluded ArkLib `knowledgeSoundness` directly for
`asSet SP1CoreShardExecutionRelation` by post-composing the AIR extractor with
`FunctionalRefinement.map`. That is not the shape of ArkLib's current definition.

At [ArkLib commit `015520d`](https://github.com/Verified-zkEVM/ArkLib/commit/015520d30bf27d918e6550db25922837f2fe78b3),
`Verifier.knowledgeSoundness` uses `WitIn` both as the straight-line extractor's result type and as
the malicious prover's private-input type. Replacing `AIRWitness` with `ExecutionWitness` therefore
changes the quantified game; it is not ordinary function post-composition.

The error-preserving adapter is:

1. retain the AIR-witness type;
2. pull the semantic relation back along `airRefinement.map`;
3. widen the source AIR relation to that target preimage; and
4. map a successfully extracted AIR witness after the knowledge game.

This branch adds `FunctionalRefinement.targetPreimage` and
`source_subset_targetPreimage`, and corrects the ArkLib sketch. A generic
`knowledgeSoundness_relIn_mono` proof was compiled against ArkLib's actual 4.31 API. It reuses the
same extractor and applies `probEvent_mono`, preserving the exact knowledge error; its axiom print is
the ordinary `[propext, Classical.choice, Quot.sound]` baseline.

Acceptance criterion: the eventual ArkLib module should prove the generic monotonicity lemma and
state its direct ArkLib theorem over `asSet airRefinement.targetPreimage`. If a user-facing theorem
returns an execution witness, it should expose the subsequent deterministic map explicitly.

### F2 — AIR-derived facts and application contracts share one opaque closure point

**P1 · NARROW**

`CoreAIRRefinementObligations.executionCase` currently packages the entire proof that an exact
execution-cluster witness yields an `EventSegmentMatches` trace. That field necessarily mixes:

- facts to derive from Program, StateBump, MemoryLocal, MemoryBump, Global,
  MemoryGlobalInit/Finalize, PublicValues, and syscall tables; and
- facts supplied by the application/loader/platform boundary, including existence of a suitable
  loaded and configured Sail state, program well-formedness, and—when the native grounding proof is
  reused—the `SailCodeMemoryCompatible` invariant reconciling immutable SP1 Program fetch with
  mutable unified Sail memory.

No current theorem is unsound: the bundle is uninstantiated and the public combinators are correctly
named `_of_obligations`. It is also legal for a future constructor theorem to take these contracts as
parameters. The risk is API ownership: the source is displayed as only
`CoreAIR.Current.Relation binds .execution`, so an unqualified theorem can look AIR-only even when
its constructor silently assumed an application contract.

Acceptance criterion: before declaring unqualified `sp1_air_refinement`/`sp1_air_sound`, introduce a
named application/environment contract or an explicit source restriction and keep it in the public
theorem type. Do not label loader existence, platform configuration, handler faithfulness, or
code-memory noninterference as consequences of the six system tables.

### F3 — the exact system-table refinement remains the central mathematical gap

**P1 · CONFIRM**

The current architecture accurately reserves the hard theorem. The exact relation contains the
34-table execution cluster and separately names the six-table memory-boundary cluster, while
`CoreAIRRefinementObligations` remains uninstantiated. The missing work is not another chip proof; it
is the global derivation of:

- provider membership and uniqueness;
- timestamp high bounds and non-wrapping order;
- State/Memory/Program grounding;
- physical execution ordering;
- ordinary 8-tick versus syscall 264-tick event scheduling; and
- public-value endpoints and syscall transcript alignment.

At the pinned SP1 semantic revision, an independent source search found no use of
`is_first_row`, `is_last_row`, or transition-window selectors under `crates/core/machine`. Thus the
current list-only exporter does not omit a separate selector-gated next-row family at this pin. The
pin guard and selector re-audit must remain fail-closed for future revisions.

Acceptance criterion: construct the exact execution decoder as a total function, prove each system
table's named contribution, then instantiate the obligation bundle without assuming natural order
from field equations or uniqueness from balance alone.

### F4 — joint native non-vacuity stops at the official generated decoder

**P2 · NEW**

`SP1CleanTest/NonVacuityReal.lean` is a valuable row-local battery, but it intentionally excludes
global channel balance, and its representative instruction PCs mostly use `4096`, below the legal
guest code window `[2^16, 2^48)`. The retained semantic example correctly uses `ADD x1, x2, x3` at
`0x10000`, but its concrete `decodedInROM` theorem was retired during the Lean 4.32.2/Sail-v5
migration.

This branch adds `SP1CleanTest/Audit/OneAddNativePremises.lean`, which:

- uses the first legal code address, `0x10000`;
- proves the complete flattened native Add circuit constraints;
- freezes all 21 evaluated Byte, State, Program, and Memory interactions; and
- proves definitionally that the SP1 Program-row projection of `ADD x1, x2, x3` is the retained
  committed row.

The only concrete Program-provider fact it does not claim is evaluation of generated
`LeanRV64D.ext_decode 0x003100B3`. An attempted direct reduction remained CPU-active for ten minutes
and was stopped; that proof style is unsuitable as a routine regression. This is a scalability issue
at the generated decoder seam, not evidence that the Add circuit or projection is wrong.

The promising upstream route is [sail-riscv PR #1861](https://github.com/riscv/sail-riscv/pull/1861),
which permits overriding the formal-backend configuration by a plain `-D` flag. (Rewritten
2026-08-19 to a per-arch `SAIL_FORMAL_CONFIG_<ARCH>` override that composes with the competing
#1879; the `DEPENDS` half split out as #1885. See `../agents/sail-model-provenance.md`.) The
generated snapshot remains an appropriate interim pin.

Acceptance criterion: restore at least one kernel-checked concrete `decodedInROM` witness using a
proof-friendly generated interface, then scale it by instruction family rather than by normalizing
the complete decoder for every word. Only after that should the one-Add test be extended to a full
`SupportedCoreNativeRelation` witness.

### F5 — `CoreAIR.Current.Relation` is a knowledge-extracted relation, not raw verifier acceptance

**P2 · NARROW**

The name “exact AIR relation” is easy to overread. Its local row constraints are exact generated
assertion lists, but `GlobalValid` also assumes:

- `Balance.Valid`, an equality of canonical **natural** multiplicities rather than the field-level
  LogUp/GKR check; and
- `PreprocessedBinding`, the PCS opening of the preprocessing commitment.

Those are deliberately documented as C2 and C1, so this is not a hidden logical gap. It does mean
the relation is the target of a cryptographic knowledge extractor, not the proposition directly
computed by the Rust verifier. Calling an ArkLib theorem “AIR extraction” without this distinction
would risk assuming its conclusion.

Acceptance criterion: the ArkLib layer should name three relations separately: raw structured proof
acceptance, algebraic/commitment openings, and the extracted exact-natural witness relation consumed
by `sp1_air_refinement`. The theorem carrying C2 must state its trace/multiplicity bounds and error
term.

### F6 — ArkLib is conceptually compatible but not currently dependency-compatible

**P2 · NEW**

The compatibility spike used:

- ArkLib main `015520d30bf27d918e6550db25922837f2fe78b3`, Lean 4.31.0, pinning VCVio `v4.31.0`; and
- [VCVio main `ea9916d`](https://github.com/Verified-zkEVM/VCV-io/commit/ea9916db809a18da16ad495eef5f8d03ca58f1b4),
  Lean 4.32.2.

The relation-widening adapter compiles in ArkLib's own toolchain, but ArkLib cannot yet be added to
this Lean 4.32.2 package as an ordinary dependency. Moreover, the imported ArkLib/VCVio closure emits
existing `sorry` warnings. That does not imply every relevant security theorem depends on those
declarations, but it means this project's release discipline cannot infer proof completeness from a
successful upstream build alone.

The generic relation-widening lemma itself is not affected by those deferrals: its axiom print is the
ordinary logical baseline. The warning is about the eventual protocol theorem's reachable closure,
which must be audited theorem-by-theorem.

Acceptance criterion: wait for or help produce an ArkLib 4.32.2 release; import the narrowest security
surface; and run `#print axioms`/ArkLib's axiom sweep on every exact theorem in the final chain. Record
upstream `sorryAx` only when it is reachable from a claimed theorem, rather than applying either a
blanket trust or a blanket rejection to the library.

### F7 — witness shape does not bind proof-system domain sizes

**P2 · NEW**

`CoreAIR.Witness.WellShaped` fixes the active table list, requires every active table to be nonempty,
and forbids hidden inactive rows. It intentionally leaves exact domain sizes as proof-system data.
This is logically conservative for a refinement theorem—proving soundness for more shapes is
stronger—but it is not yet a faithful interface to an executable verifier or an ArkLib extractor.

Acceptance criterion: add an adapter-level domain/height binding from the structured proof and
verifying key to every extracted main and preprocessed matrix. Keep it outside row semantics, but
make it part of the relation extracted from `verifyCore`; otherwise padding/domain mismatches can
fall between executable verifier agreement and AIR refinement.

### F8 — current extraction and whole-chip boundaries withstand the independent spot checks

**P3 · CONFIRM**

The following prior design decisions survived this review:

- 25 whole-chip native↔Rust anchors are the correct stable faithfulness boundary;
- retained operation/reader anchors are genuinely shared substrate, not an unfinished migration;
- native arithmetic gadgets are composed through real Clean subcircuits;
- structural channels do not smuggle reachability into row-local guarantees;
- natural ordering and uniqueness are named premises/theorems rather than inferred from field
  balance; and
- exact execution and memory-boundary clusters cannot be interchanged by type inference.

The clean baseline also passed `lake build SP1Clean`, `lake test`, `lake lint`, and
`scripts/run_audit.sh` before changes, with no main-library `native_decide`, proof deferrals, or
unexpected axioms.

### F9 — the claim ladder is correct but should become the primary reader map

**P3 · CONFIRM + suggestion**

The repository has the right claim layers, but they are spread across architecture, roadmap, and the
verification report. The following ladder is the shortest shared vocabulary for SP1, Clean, and
ArkLib readers:

| Layer | Source | Target | Current status |
|---|---|---|---|
| Whole-chip faithfulness | generated Rust assertions/interactions | native Clean chip | closed, 25/25 |
| Native semantic grounding | constrained balanced native ensemble + explicit boundary/range facts | local official-Sail segment | closed |
| Exact SP1 AIR refinement | 34 exact execution tables + extracted natural balance/bindings | eventful Sail shard | conditional on uninstantiated obligations |
| Authenticated execution | ordered authenticated shard ledger | boot-to-halt execution/output | specified, not closed |
| Cryptographic extraction | accepted Core proof | exact AIR witness, with error | planned ArkLib/VCVio layer |
| Executable agreement | Lean `verifyCore` | pinned Rust Core verifier | planned |

Use this table, or an equivalent, near the public front door. It prevents “the chips are verified,”
“the AIR is sound,” and “the verifier is sound” from being treated as synonyms.

### F10 — generated Sail/runtime pairing remains deliberate technical debt

**P3 · CONFIRM**

The generated LeanRV64D snapshot and lean-sail runtime are correctly treated as one versioned pair.
[opencompl/riscv-lean PR #59](https://github.com/opencompl/riscv-lean/pull/59) remains open at the
already-pinned head `d1d678c` and updates to Lean 4.32.2. There is no reason to replace the current
pin with an unpaired generated model. Once both upstream PRs land, the project should regenerate from
source/config and retire the fork pin in one atomic change.

## Comparison with similar work

### Clean

For a Clean audience, this project is idiomatic where it matters most: semantic Specs are separated
from circuit construction; genuine reusable gadgets are true subcircuits; elaborated output layouts
are explicit; and global meaning flows through the flat-AIR balance theorem rather than semantic
channel payloads. The bespoke SP1 timed grounding layer is large, but it addresses a real mismatch
between generic Clean VM guarantees and SP1's balance-derived Eulerian/event schedule. I agree with
the decision not to force a `VmTables` rebase merely for visual uniformity.

The next Clean-facing improvement should be restraint: do not add another abstract machine layer for
the exact tables. Reuse the existing typed interactions, grounding contracts, and event trace; make
the six system-table proofs adapters into that surface.

### OpenVM FV

The existing comparison with [Nethermind's OpenVM FV](https://github.com/NethermindEth/openvm-fv) is
substantially fair. OpenVM has broader first-class opcode/precompile coverage and strong independent
axiom-export checks. This project has a stronger shipping-SP1 correspondence story through pin-gated
generated whole-chip lists and trace conformance, and it carries more global bus semantics inside
Lean. The qualification is important: M1/M2 are visible premises today, not yet facts derived from
the exact system tables. “No paper bus axioms” is accurate only because those seams appear in theorem
statements; it does not mean the exact upstream AIR-to-boundary proof is finished.

### S-two

The comparison with the [S-two Cairo AIR verification](https://arxiv.org/abs/2606.04311) also holds.
Both use the honest existential endpoint-to-endpoint execution shape. This project has stronger
pin/extraction and official-ISA semantics; S-two currently reaches deeper into lookup-argument
soundness and has a closed whole-program AIR theorem. The practical lesson is to keep C2 quantitative
and separate: a natural multiset equality should be an extractor conclusion with a bad-event bound,
not folded into deterministic AIR semantics by naming alone.

### ArkLib and VCVio

ArkLib's straight-line extractor and VCVio's oracle/probability semantics are a natural home for the
cryptographic layer, but the integration should follow their real types rather than a schematic
analogy. The target-preimage adapter established here is small and reusable. The larger missing work
is protocol-specific: structured Core proof parsing, transcript and Fiat–Shamir agreement, PCS
openings, LogUp GKR/zero-check extraction, and the accumulated error statement. None of that should
be placed in `sp1_air_sound`.

## Recommended build order

1. Keep the current native claim frozen and passing while exact-system work proceeds.
2. Split AIR-derived obligations from named application/environment contracts in the public exact
   refinement constructor.
3. Restore a scalable generated-Sail decode bridge and complete the one-instruction joint witness.
4. Prove Program/State/Memory/Global/syscall table adapters into the existing native/event grounding
   surface; instantiate `CoreAIRRefinementObligations`.
5. Bind extracted matrix domains/heights and main/preprocessed commitments to structured Core proofs.
6. Align ArkLib to Lean 4.32.2, land the target-preimage knowledge-soundness adapter, and axiom-census
   only the reachable theorem chain.
7. Implement executable `verifyCore` and prove agreement with the pinned Rust verifier on structured
   real proofs.
8. Compose the quantitative ArkLib extractor with deterministic exact-AIR refinement and then with
   authenticated shard execution. Publish `sp1_verifier_sound` only in that probabilistic,
   knowledge-soundness-shaped form.

## Changes made by this audit

- added the committed-window one-Add circuit/interaction/projection regression;
- added `FunctionalRefinement.targetPreimage` and its source inclusion theorem;
- corrected the ArkLib integration sketch to retain the AIR-witness type;
- clarified the roadmap/report requirement that application contracts remain explicit;
- added this durable independent findings record and documentation index entry; and
- extended the disclosed test axiom census to cover all three new regression theorems.

No generated extraction file, dependency pin, Sail snapshot, chip Spec, or theorem claim was changed.
