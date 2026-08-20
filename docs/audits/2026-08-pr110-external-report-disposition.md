# Disposition of the external PR #110 adversarial report (2026-08-19, rev 2)

An independent adversarial audit of PR #110 (head `eb6f44b9`, the `dtumad/v1.0-release` branch)
was received 2026-08-19: *"SP1's Core RISC-V AIR in Lean 4: Independent Analysis and Adversarial
Audit"* (45 pp; revision 2, post its own adversarial review). Its verdict: the work is real,
high-quality, and non-vacuous, with scope materially narrower than "a verification of SP1's Core
RISC-V AIR" in four checkable ways. This document tracks every numbered finding, the confirmed
observations, and the report's ranked recommendations to a concrete disposition, and is updated as
the remediation campaign (branch `dtumad/exact-air-campaign`) lands each wave.

**Reviewed tree vs. this tree.** The report reviewed `eb6f44b9` exactly — the merge-base of this
branch. The ~66 commits since (the witness-generation cutover, the v6.4.0 extraction-pin advance,
and the PMP localization) already close some findings; those rows say so explicitly rather than
crediting the campaign.

Wave key: W0 hygiene/honesty · W1 satisfiability evidence · W2 export proved facts ·
W3 StateBump/MemoryBump soundness · W4–W5 machine completeness · W6 transport + obligations ·
W7 final docs/census.

## Findings

| # | Severity | Finding | Disposition | Status |
|---|---|---|---|---|
| 1 | HIGH | Rust-faithfulness and Sail-soundness are never composed inside Lean (`Faithful/` is a dependency-graph leaf; 98/433 modules outside the capstone's import closure) | Accepted. The transport theorem (extracted witness → native witness through the `ChipFaithful` codecs) plus the `CoreAIRRefinementObligations` instantiation is the campaign's W6; a single-chip pilot lands first to machine-check the glue shape. The README understatement (its remaining-work list omitted the instruction transport) is fixed in W0. | **open — W6** (README fix landed) |
| 2 | HIGH | StateBump omitted: shards capped at ~2²¹ rows / no 64 KiB pc-boundary crossing, and the strict clock-rank argument does not survive adding it | Accepted. W3 adds native StateBump + MemoryBump chips, reworks the trail onto a canonicalized rank (bump rows cancel from the canon'd balance; the `RankedGrounding` engine and `TimedGrounding.walk` statements survive unchanged), hardens the boundary verifier with the public-values range-check slice, and derives the timestamp premise (Finding 8.2's `MemoryPullTimestampHighBound`) — deleting a conjunct from `SupportedCoreNativeRelation`. | **open — W3** |
| 3 | MED | Joint non-vacuity unwitnessed; the only end-to-end decode witness was deleted by the PR; no `Fact (2^25 < p)` instance exists | Closed (W1, 2026-08-20), and the finding's hazard was **found live**: the decoder's MUL/DIV arms test `misa.M`, which `SailConfigured` did not pin — `decodedInROM` was unsatisfiable for all 13 M-extension opcodes, i.e. the capstone was silently vacuous for any shard containing an M instruction. Fixed by the `SailConfigured.misa_m` field. On top: per-family decode witnesses restored at **full coverage** (18/18 `instrToProgramRow` families, `Model/SailDecode.lean`, ~200 heartbeats each at default budgets vs the retired proof's 8M ceiling), end-to-end `decodedInROM` examples + all 18 hoists (`Soundness/Decode.lean`), the `Fact (2^25 < SP1Prime)` instance, and the joint anchor `SP1CleanTest/Audit/JointNonVacuity.lean` — a fully proved `SupportedCoreNativeRelation` witness (one-`JAL` statement; the report-suggested empty program is itself unsatisfiable since `WellFormed` demands a fetchable entry word; `SailCodeMemoryCompatible` proved non-vacuously via the jal advance machinery). | **closed** |
| 4 | MED | The capstone discards `TimedGrounding.walk`'s proved final-State truth and finalize-Memory truth | Closed (W2, 2026-08-20). `SupportedCoreGrounding` gains `finalStateTruth` (the public final State message is semantically true — a real chain reaches the committed final clock/pc with ROM and configuration intact) and `memoryFinalizeTruth` (every finalize record is true of the run), threaded from the walk through `supportedCore_orderedRows_dynamic{,_of_obligations}`. The memory fact is stated in an ∃-witness form (same location/value, no-later time) so the W3 MemoryBump refresh-elimination absorbs it without a statement change; today the witness is the record itself. | **closed** |
| 5 | MED | No faithfulness anchor for any provider/system table | Partially accepted. The two system tables entering the ensemble (StateBump, MemoryBump) get `ChipFaithful`-style anchors in W3. For the Byte/Range/Program providers the native tables are deliberately *not* reimplementations of upstream's preprocessed tables (they re-prove content in-circuit — the report's §7.3 calls this stronger); their upstream correspondence is established constructively by the W6 transport, which builds native provider rows from upstream table rows. That construction, not a per-table anchor, is the honest artifact for them. | **open — W3/W6** |
| 6 | MED | Upstream `RegisterAccessCols` derives `AlignedBorrow` without `#[repr(C)]` | Accepted (upstream defect, currently benign — the report's own correction confines the blast radius to positional trace tooling). A one-line `#[repr(C)]` patch plus a CI assertion that every `AlignedBorrow` struct carries it is prepared on the `dtumad/lean-extraction` SP1 branch; filing upstream is owner-gated (`docs/agents/upstream-drafts.md`). | **prepared — owner-gated** |
| 7 | MED | KoalaBear-canonical literals inside field-generic system-table oracles (`Global`, `SyscallInstrs`; curve-seed constants in `PublicValues`) | Disclosed here (the report's own measurement confirms the 25 instruction-chip oracles and readers are literal-free, and we verified StateBump/MemoryBump are too — the two tables the ensemble gains in W3). The affected tables belong to the syscall/global cluster the campaign excludes (see the drift note below); any future statement consuming their asserts at generic `p` must carry this caveat or be stated at the concrete prime. | **disclosed** |
| 8 | MED | No CI re-derives either generated artifact | Accepted for extraction: `.github/workflows/extraction_regen.yml` (W0) re-runs `update_extracted.py` against the pinned SP1 branch weekly + on dispatch and fails on drift — scheduled, never PR-blocking, preserving the no-cargo-in-PR-CI stance. The Sail snapshot stays manual (regeneration needs the sail toolchain); its generation pins and config hash are PR-gated by `check_pins.sh` (hardened 2026-08-19). | **closed (extraction) / disclosed (Sail)** |
| 9 | MED | `SailCodeMemoryCompatible` (self-modifying code excluded by assumption) thin in user-facing docs | Accepted. Named with its consequence in `docs/overview.md` § Trust and assumptions (W0); already present in the verification report and the source. | **closed** |
| 10 | LOW | The single RWX PMA region absent from the release-audit trust table | Accepted. The trust table gains a `SailConfigured` platform-state row (PMA window, PMP-off, MPRV/mseccfg/PMM, HTIF) and a two-key generated-config row; the stale "six platform-value sites" line corrected to the post-PMP-localization four (W0). | **closed** |
| 11 | LOW | The faithfulness codec covers a codimension-1 slice of the native row space for 6 flag-hinted chips | No code fix. The W6 transport constructs native rows via `deconfigure`, which sets `is_real := flag-sum` by definition — the direction any stated theorem uses; an image-forcing lemma would matter only for a native→Rust direction over arbitrary native solutions, which nothing states. Rationale to be recorded in the transport module doc (W6). | **closed by rationale — doc lands W6** |
| 12 | LOW | Several "native" constraint lists are token-for-token transcriptions of the generated lists (Addw/Subw/LtU own-asserts; DivRem own-assert tail) | Accepted as a framing correction: for those operations `ChipFaithful` is a pin-drift tripwire, not independent cross-validation (soundness content is unaffected — the semantic `Spec` is still proved from the list). Disclosed in the verification report (W0/W7 docs pass). | **accepted — disclosure in W7 report pass** |
| 13 | LOW | `ChipFaithfulnessAnchor` did not bind a table to its own theorem (a mispaired anchor would type-check) | Fixed (W0): `FaithfulPropFor : CoreProfile.Table → Prop` dispatches each table to its exact `ChipFaithful` statement and the anchor's `proof` field is typed by it — a mispairing is now a type error. | **closed** |
| 14 | LOW | Trace-generation conformance covered 10/25 chips, none memory/control-flow | **Already closed before the report was received**, by the witness-generation cutover (2026-08-17/18): conformance is now the dump-anchored pipeline — committed SP1 `generate_trace` dumps for all 25 chips, a fail-closed generation-time gate recomputing every event row cell-for-cell, a 25-chip Rust interpreter differential, and an inverted in-SP1-workspace check. Re-run in CI (`check_witgen_export.sh --regen`). Stale doc/CI wordings purged (W0). | **closed** |
| 15 | LOW | Machine-level completeness absent; the previous partial scaffold was deleted | Accepted. W4–W5 build the honest whole-shard witness generator on the witness-IR substrate and prove `supported_core_native_complete` (the shape the `Soundness/AIR.lean` completeness-boundary comment reserves), including widening the four per-chip completeness caps (Bitwise/Lt/Addw immediate forms; UType `rd = x0`). | **open — W4/W5** |
| 16 | LOW | Audit snapshots stamped off-branch; census count mismatch in the PR text | Accepted. `run_audit.sh --update` now refuses to stamp from a dirty working tree, and a content-pass whose committed stamp is not an ancestor of HEAD prints an explanatory NOTE (W0); both scopes restamped on this branch. The count drift (476 vs the live 466+37=503) was already fixed by the witgen-era doc sweep. | **closed** |
| 17 | LOW | mprotect-gated assertions outside the extraction, not gated in the pipeline | Accepted. `update_extracted.py` now runs `verify_no_mprotect` — the extraction fails if the constraint compiler's cargo feature resolution enables `mprotect` — so the profile exclusion is asserted, not incidental (W0). Disclosure already present in the verification report. | **closed** |
| 18a | LOW | Documented extraction invocation failed on a second run (overlay `Cargo.lock` re-normalization) | **Already closed** by the E1a move from overlay+patches to the committed extraction branch (its lockfile is current-cargo); regeneration has since been re-run repeatedly byte-identically. | **closed** |
| 18b | LOW | `Extracted.Interaction.toAccess`'s `.byte` arm ignored direction (hard-coded sink sign) — wrong for the system Byte/Range tables' receives | Fixed (W0): the byte arm now negates the direction sign uniformly (`signedVal (-(dir.sign mult))`) — byte-identical on every chip interaction (all sends), correct for provider receives; `toAccess_byte` restated at `.send` with a new `toAccess_byte_receive` twin. | **closed** |
| 18c | LOW | Opcode→chip routing table hand-mirrored with no extracted tripwire | **Already closed** (2026-08 release-audit wave): `FormalModel/OpcodeTable.lean` + `opcodeTable_matchesExtracted` check the hand mirror against the extracted discriminant table; the routing enum was verified arm-by-arm by the report itself. | **closed** |
| 18d | LOW | AGENTS.md "axiom-clean" slogan vs the capstone's Sail-extern footprint | The report's own §11 withdraws the documentation-defect claim (the head's AGENTS.md discloses both the platform hooks and the bv_decide constants). Its surviving observation — the Prop-valued/data-valued split of the 100 axioms — is adopted into the verification report's trust-base framing (W7). | **adopt framing — W7** |
| 18e | LOW | Part of the ISA-equivalence chain lives in a third-party fork at an unmerged PR head (`riscv-lean`, opencompl PR #59) | Disclosed already (release-audit pin table names it; repoint-on-merge is the standing plan). No action beyond tracking. | **disclosed** |
| 18f | LOW | A frozen, weaker capstone (`Soundness/GatedVm/`) remained in the tree and in the live capstone's import closure | Fixed (W0): the whole frozen Eulerian-path interface deleted — `GatedVm/` (3 files), `TargetVm.lean`, `AdvanceDispatch.lean`, the `Soundness/Decode.lean` walk half, the `SP1Ensemble.lean` legacy section, the `Walk.lean` legacy-name shims, and the legacy public-values scaffold. Live-path survivors: `Walk.lean`'s graph core, `RowEffectDefs.lean`'s interface, the decode hoists. | **closed** |
| 18g | LOW | Cold-build cost (one generated Sail module >45 min / >7 GB) and no cached-olean distribution | Acknowledged; a known property of the generated model. No campaign action (CI caches oleans per-SHA; external reproducers bear the cost once). | **acknowledged** |
| Gap 1 | MED | The bus idealisation: LogUp/GKR → exact balance is not reduced (PCS, Fiat–Shamir, fingerprint injectivity, length side-condition, digest identification) | Out of scope by design — the ArkLib layer (`FormalModel/Verifier.lean` seam). The report itself notes this gap is structural, common to every zkVM formalisation it knows, and correctly named here. | **out of scope — disclosed** |

## Confirmed observations (report §11.2)

- **Three chips' `advance` never uses the chip Spec** (AluX0/LoadX0 expected; LoadDouble's semantic
  content rides `advanceReady`) — no action; the report classifies the effect as none.
- **Shift/Bitwise Specs omit the reader sub-Spec / is_real binarity clause** — resolved by
  documentation (W2): the shape is deliberate — both facts are circuit-forced and derived where
  consumed (the reader/time facts from channel-push `Requirements` at the trace level, binarity
  from the flag-sum gate), and restating them would re-index every positional projection in the
  advance/grounding consumers for no semantic gain. Recorded on `ShiftLeftChip.Spec`'s docstring
  (`FormalModel/Contracts/Chips.lean`), covering ShiftRight and Bitwise (which already carries its
  binarity conjunct).
- **`EnsembleWitness` constrains neither row counts nor `Table.width`** — no action (the report:
  truncation only restricts a prover; row counts come from the grounding).
- **`IntoShape` skips mode-typed fields** — scope note folded into F17's gate rationale.
- **`mainWidth` not linked in Lean to the column struct's size** — the report closed it externally
  by measurement; a `width`-guard battery is a candidate W6 add-on when the transport states widths.
- **Misaligned accesses made unsatisfiable rather than trapping** — standing scope property of the
  chip Specs; disclosed in the verification report's coverage section.

## The report's ranked "what would most increase assurance" (§12.3) → campaign waves

1. Compose the two halves in Lean → **W6** (pilot early).
2. Restore an end-to-end decode witness → **W1**.
3. Export the facts already proved → **W2**.
4. Extend trace conformance to the 15 uncovered chips → **already closed** (witgen cutover).
5. State the Sail configuration deviations in one auditable place, PMA included → **closed in W0**
   (release-audit trust table).

## Not adopted

- **Reverting the native providers to upstream's preprocessed-table shape** (implicit in a maximal
  reading of Finding 5): the in-circuit re-proof of Byte/Range content is strictly stronger than a
  trusted preprocessed table, as the report's §7.3 itself concludes; the transport supplies the
  correspondence.
- **Building the Global/Syscall*/MemoryGlobal* cluster natively**: `docs/roadmap.md` (2026-08-19)
  records that SP1's internal line has replaced that cluster with a Merkle-tree architecture; the
  campaign targets the drift-stable core (owner decision, 2026-08-20) and keeps the exact lists in
  the list-level model with the memory-boundary premises named rather than derived from tables
  upstream has already dropped.
