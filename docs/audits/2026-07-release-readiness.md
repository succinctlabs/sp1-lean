# Release-readiness audit — findings log (2026-07)

Campaign log for the release-readiness pass: legacy-debt retirement (23-chip `ChipOracle` migration),
spec-level semantic audit, docs refresh, and the external verification report. Every finding cites
`file:line` at the time of discovery. Severities: **BLOCKER** (must fix before release), **WEAK-SPEC**
(statement weaker/other than intended), **STALE-DOC** (prose contradicts the tree), **COSMETIC**,
**DISCLOSED-OK** (intentional, correctly disclosed limitation — no action).

Top-of-log standing item: the four **local path dependencies** (`../clean`, `../sail-riscv-lean`,
`../riscv-lean`, `../lean-sail`; see `lakefile.toml`) are 4.31-migration checkouts. Restoring
reproducible immutable git pins is a **release blocker** tracked outside this campaign
(`docs/release-audit.md` § dependency pins). Never run bare `lake update`.

## Phase 0 — baseline and extraction preconditions

- **F-0-01 (BLOCKER, fixed).** `update_extracted.py`'s `render_chip_oracle` was the only render path
  that never applied `_preserve_raw_byte_opcodes`, so regenerating any chip oracle at the pinned
  overlay emitted byte interactions as `(.byte (ByteOpcode.ofNat 6) …)` instead of the intended raw
  `(.byte 6 …)` — reproducibly diverging from the checked-in `ChipOracle/{Add,Sub}.lean` and breaking
  the documented byte-idempotence of full regeneration. The wrapper is semantically dangerous, not
  merely cosmetic: `ByteOpcode.ofNat` maps every out-of-range value to `.Range`, so it is not an
  injective representation of the upstream AIR tuple (the reason the strip exists — see the function's
  docstring). Had the 23-chip migration proceeded on the broken renderer, every new oracle would have
  carried the non-injective encoding. Fix: one-line call added in `render_chip_oracle`
  (`update_extracted.py`), after which the complete `EXTRACT_AIR_ONLY=1` regeneration at the pinned
  overlay (`69a8377c`, patch set `a2c43cfa…`) reproduces all 62 generated modules byte-identically.
- **F-0-02 (COSMETIC, documented).** Each extractor run's `cargo` invocation rewrites the overlay's
  `Cargo.lock` (newer-cargo re-normalization of one `slop-algebra` entry), which the strict
  audited-worktree check then rejects on the next run. Operational note added to
  `docs/agents/extraction.md` (stash/restore `Cargo.lock` before each run; `--locked` cannot work).
- **F-0-03 (STALE-DOC, fixed).** `SP1Clean/Soundness/ChipRegistry.lean:32-34` still disclosed a
  4.31-migration `sorryAx` deferral (DivRem `evidenceSoundness` + Branch/ShiftLeft/DivRem
  completeness) that no longer exists — contradicted by the 2026-07-27 audit run (`run_audit.sh`
  `== AUDIT PASS ==`, zero `sorryAx`, empty allowlist) re-confirmed at this campaign's Phase-0
  baseline. Comment replaced with the accurate axiom-clean statement.
- Phase-0 baseline: G1 `lake build SP1Clean` (3626 jobs, 0 error/0 warning/0 info), G2 `lake test`,
  G3 `lake lint`, G4 `scripts/run_audit.sh` — all green before any change.

## Phase 1 — quick cleanup + docs pruning

- Deleted (only the root index imported them): `Faithful/{AddrAddOperation, AddressOperation,
  LtOperationSigned, U16toU8OperationUnsafe, ITypeReader, JTypeReader}.lean` (14 probe entries
  auto-dropped on `gen_axiom_probe.py` regeneration: 513 → 499), plus the doc-only
  `SP1Clean/Comparison.lean` (4.28-era worked-example memo; rationale lives in
  `docs/architecture.md` and the forthcoming verification report), plus the empty untracked
  `SP1Clean/Extracted/Circuit/` directory.
- Docs pruned (retrievable from git history): `docs/audits/2026-07-full-project/`, `docs/archive/`,
  `docs/snapshots/profile-baseline-2026-06-10/`, `docs/talks/`, `docs/spikes/`, `docs/upstream/`,
  `docs/agents/{capstone-seam-plan,bytechip-provider-design}.md`,
  `docs/proposals/2026-07-architecture-consolidation.md`. `docs/bus-model.md` was **kept** (with a
  strengthened HISTORICAL banner) because eight load-bearing source doc-comments cite its section
  numbers. Index files (`docs/README.md`, `docs/agents/README.md`, `AGENTS.md` docs section) updated;
  `sail-fork-delta.md` newly indexed; dangling references in `TouchChains.lean`,
  `ByteChip/Ensemble.lean`, `compile-profile.md`, `bus-model.md` repointed.

## Phase 2 — ChipOracle migration

- **Subw (pilot) — complete, all gates green, zero proof repair.** The whole migration compiled on
  the first full build (3616 jobs, 0/0/0; `lake test` green incl. both Subw `native_decide`
  anchors — the trace anchor now runs through `subwChipReconfigure`, making it a cell-for-cell
  audit of the native→Rust row map). Recipe validated; corrections recorded: EXTRACT_ONLY groups
  must be closed under *transitively* composed sub-ops (U16MSBOperation — the generator fails
  loudly), and the overlay `Cargo.lock` must be stashed before every cargo invocation including
  retries. `Faithful/Subw.lean` (per-op anchor) and `Faithful/SubwChipAnchors.lean` retired
  (anchors folded into `Faithful/SubwChip.lean` as private, Sub-style); probe −8 entries.
  Axiom census unchanged (chip circuit `[propext, Classical.choice, Quot.sound]`; advance carries
  only the disclosed Sail platform hooks).
- **Mul + DivRem — complete, all gates green.** The two heaviest chips (168 KB / multi-file
  Faithful layers). Both trace-conformance anchors now audit the reconfigure maps cell-for-cell
  against real prover dumps. Structural learnings recorded for the remaining chips: (1) shared
  operations consumed by another chip's Exact layer get one-line definitional **namespace
  bridges** in the Faithful file instead of re-pointing (avoids duplicating ~1500-line op lemma
  sets; `Extracted/MulOperation.lean` + `U16toU8OperationSafe.lean` stay — the latter is imported
  by `SystemOracle/SyscallInstrs.lean`); (2) a chip row consumed below `Contracts/Chips.lean` in
  the import order gets its own `Contracts/<Chip>Columns.lean` (DivRem — cycle avoidance);
  (3) at DivRem scale the `dsimp`-through-reconfigure pattern hits the documented
  whnf-into-giant-term kernel cliff — replaced with ~82 tiny `rfl` projection lemmas + syntactic
  rewriting (Clean doctrine); `Faithful.DivRemChip.Exact` 258s (was 95s). Retired:
  `Faithful/MulOperation.lean`. Census: `divRemChip_faithful` three-axiom clean;
  `mulChip_faithful` carries only the pre-existing disclosed `bv_decide` axioms.
  CHIP_ORACLES = {Add, Sub, Subw, Mul, DivRem} — 5/25.
- **Addi + Jalr + Jal + UType — complete, all gates green, essentially zero proof repair** (a
  handful of unused-simp-arg removals; Jal and UType compiled first try). First exercise of the
  reader-family generator config: `ITypeReader` + `JTypeReader` added to the shared-struct and
  imported-helper sets (nested register-access structs resolve via the existing STRUCT_OWNERSHIP
  pins; RTypeReader not needed in the closures). Second generator fix landed:
  `render_chip_oracle`'s namespace marker now accepts both `<Chip>Cols` and `<Chip>Columns`
  spellings (Jal/Jalr/UType use the latter — fail-loud if neither). `Extracted/AddOperation.lean`
  stays standalone (DivRem layer still imports it); each oracle embeds a private struct-stripped
  copy, and this batch's Faithful AddOperation lemmas were file-private so they re-pointed
  directly (no namespace bridges needed). Grounding files needed ZERO changes (they consume the
  chips symbolically through `directOutput_eq`/`eval_columns`).
  CHIP_ORACLES = {Add, Sub, Subw, Mul, DivRem, Addi, Jalr, Jal, UType} — **9/25**.
- **Addw + Bitwise + Lt — complete, all gates green** (one trivial fix round: a substring-level
  script replacement left one `Var BitwiseCols` ascription behind in the Bitwise Native Defs;
  every Faithful transformation compiled first try). `ALUTypeReader` joined the shared-struct and
  imported-helper sets (first ALU-adapter oracles). Three distinct retirement outcomes exercised:
  (1) **Addw** = the Subw pattern — `AddwOperation` → CHIP_ONLY, native `AddwOperation.Columns`
  (shared `Extracted.U16MSBOperation` sub-block kept), `Faithful/Addw.lean` +
  `Faithful/AddwChipAnchors.lean` retired (anchors folded in as private; the file-private
  `aluTypeAssertions` copy kept unchanged); (2) **Bitwise** = a two-level native op rewire —
  `BitwiseOperation` + `BitwiseU16Operation` both → CHIP_ONLY (importer evidence: after this
  batch their only non-retired importers were the native op files + Contracts), native
  `BitwiseOperation.Columns`/`BitwiseU16Operation.Columns` (shared `Extracted.U16toU8Operation`
  low-byte blocks kept; `U16toU8OperationUnsafe` stays standalone), `Faithful/BitwiseOperation.lean`
  + `Faithful/BitwiseU16Operation.lean` retired (their anchors had no external consumers);
  (3) **Lt** = the Mul pattern — ALL sub-ops (`LtOperationSigned`, `LtOperationUnsigned`,
  `U16CompareOperation`, `U16MSBOperation`) stay standalone (Branch/ShiftLeft/ShiftRight + the
  DivRem oracle + `Faithful/LtOperationUnsigned.lean`'s cross-file consumers still import them),
  `LtChip.Columns` keeps the shared `Extracted.LtOperationSigned` block, and the Faithful layer
  gained eight one-line `ltOracle_*_eq` namespace bridges (af067f7d pattern) so every heavy
  compare-op lemma stays stated once against the standalone modules. Bitwise/Lt native rows keep
  Rust field order (no `is_real` column — flag-sum selectors), matching the Mul precedent. All
  three whole-trace conformance anchors now audit the reconfigure maps cell-for-cell (`lake test`
  green); probe −12 entries (the retired Addw/Bitwise transitional anchors); grounding files again
  needed ZERO changes.
  CHIP_ORACLES = {Add, Sub, Subw, Mul, DivRem, Addi, Jalr, Jal, UType, Addw, Bitwise, Lt} —
  **12/25**.

## Phase 3 — audit findings

### Batch A5 — Jal / Jalr / Branch spec review (complete; no BLOCKER, no WEAK-SPEC)

Checklist C1–C9 verified per chip against the Sail `execute_JAL`/`execute_JALR`/`execute_BTYPE`
clauses (`sail-riscv-lean` @ 793034f3) and SP1's pinned Rust executor (`vm.rs` @ a630089d):
BitVec operations, sign-extension widths (21/12/13), the JALR LSB-clear
(`~~~1#64 &&& ·` = Sail `BitVec.update · 0 0#1` = Rust `& !1`), all six branch polarities,
per-chip x0 write-discard arms, `clk_inc = 8`, and immediate slot wiring (JAL→op_b,
JALR/Branch→op_c) all match. Soundness `Assumptions` are isU64-only (the six branch comparison
biconditionals live only in the completeness-side `ProverAssumptions` — no smuggling). Alignment
and LSB-clearing are proven conclusions of the in-circuit ÷4 range checks, not bridge premises.

- **F-A5-01 (DISCLOSED-OK).** All three chips enforce 4-byte target alignment as a *proven* Spec
  conjunct (`Chips.lean:738/:858/:974`), strictly stronger than Sail's LSB-only clear and than
  SP1's Rust executor (`vm.rs:364` clears only bit 0). Misaligned targets are precluded by circuit
  constraint rather than modeled as the Sail `E_Fetch_Addr_Align` exception path — sound
  (superset-safe) and consistent with the "guest programs never fault" model; the Lean models the
  stricter AIR chip, not the laxer executor. Worth one sentence in the report's limitations.
- **F-A5-02 (COSMETIC).** The outer `(is_real = 0 ∨ is_real = 1)` Spec conjunct
  (`Chips.lean:731/:850/:948`) is consumed by no bridge/advance and duplicates the reader
  sub-Spec's binary fact. Harmless redundancy; removal optional.

### Batch A8 — substrate review (complete; one item under re-verification)

Cross-checked against the pinned Rust (a630089d) with an explicit evidence table: bus-message
arities (State 5 / Memory 9 / Program 16 / Byte 4 per `interaction.rs`), the 16+8-bit clk split
(`state.rs:47-56`), Word = 4×u16 + pc = 3×u16, `CLK_INC = 8` / syscall 264 (`lib.rs:96`,
`portable/mod.rs:715`), MemoryAccessPosition offsets A=4/B=3/C=2/Mem=1, the full 0–52
`Opcode.toNat` table, syscall ids (HALT 0, COMMIT 0x10, …), `HALT_PC=1`/`ECALL_ENC=0x73`/t0=x5/
a0=x10, and the 2^24 memory-timestamp bound (`memory.rs:292-325`) — all match. The typed decoder
is anchored to the official Sail `ext_decode` (delegation, with per-class round-trip lemmas), and
the Truth predicates are correctly framed as grounding conclusions over all bus messages.

- **F-A8-01 (STALE-DOC — re-verified, downgraded from WEAK-SPEC; fix queued).** Resolved
  consistent: SP1's dedicated preprocessed `RangeChip` (`range/air.rs:20-33`) is a Byte-kind
  receiver of exactly `(Range, a, bits, 0)`, matching every sender (`state.rs:91` bits=13,
  `air/word.rs:88-96` bits=16, `memory.rs:311-317` bits=16); the Lean mirrors this precisely with
  the `RangeChip.circuit8/13/16` byteChannel providers (`Proofs/Chips/ByteChip/RangeChip.lean`,
  wired at `SP1Ensemble.lean:167`), whose own header describes SP1 correctly. The sole defect is
  the prose in `Model/ByteTable.lean:12/:58-67` claiming Range is among the ByteChip's
  `byte_table()` six ops — it is not (`byte_table()` = AND/OR/XOR/U8Range/LTU/MSB; ByteChip
  panics on Range precisely because the RangeChip owns it). Scope note (fine): Lean provides
  fixed widths 8/13/16 vs SP1's variable `bits ≤ 16` table — covers every width the supported
  slice pulls; the other widths belong to out-of-scope PageProt chips.
- **F-A8-02 (COSMETIC — re-verified, downgraded).** `byteRowSpec_u8range` (a-slot form) is used
  by zero proofs (word-boundary grep: definition + doc mentions only); the faithful b/c-slot
  `byteRowSpec_u8range_pair` carries all the weight. Dead lemma whose row shape SP1 never emits —
  cannot introduce unsoundness; delete with the F-A8-01 comment fix (queued behind the pilot's
  builds since `Model/ByteTable.lean` is deep substrate).
- **F-A8-03 (DISCLOSED-OK).** `MemoryMsg.ClkBound` bounds only `clk_low` — exactly right for the
  register-access timestamp path (equal high limbs); the general RAM high-limb path is deferred
  to `Soundness/TimeExtraction.lean` as the comment says.
- **F-A8-04 (WEAK-SPEC/DISCLOSED-OK — feeds the V-track).** No `SP1MachineModel` instance is
  constructed anywhere (47 mentions, 0 constructions), so `UsesOrdinarySchedule` satisfiability
  and the boot-loader hypotheses are unwitnessed in-repo. Matches the planned V1/V2 non-vacuity
  work: build a witness or disclose explicitly in the report.
- **F-A8-05 (DISCLOSED-OK).** `SailStep` fixes `try_step 0 false` vs the Sail driver's
  `step_no true`; verified benign (`step_no` feeds trace strings; `exit_wait` only affects the
  dead HART_WAITING arm under `SailConfigured.active`). Worth one disclosure sentence.
- **F-A8-06 (DISCLOSED-OK).** `progOf`'s committed ROM layout uses Lean-internal reserved keys —
  a shadow of SP1's program commitment, bound to reality via `StatementFor`, not claimed faithful
  at this layer.
- **F-A8-07 (COSMETIC).** `ByteTable.lean` header inconsistency ("six byte opcodes" vs the
  seven-clause `ByteRowSpec`) — the prose face of F-A8-01.

### Batch A9 — relation-level review (complete; no BLOCKER)

Verified quantifier-by-quantifier: `SupportedCoreEnsembleRelation` is ∀-tables (all 36 + the
State verifier) ∀-rows constraints ∧ ∀-channels balance (traced into Clean's
`FlatEnsemble/FlatComponent`); the conclusion chain
`SupportedCoreLocalExecutionRelation → ClosedLocalExecutionSegmentWitness → trajectory/stepOnce =
(try_step 0 false).run` contains a genuine finite run of the official LeanRV64D interpreter, with
PC/clock endpoints pinned by `LocalSegmentMatchesBoundary`. `CoreAIRRefinementObligations` is
well-typed, mutually consistent (boundary/execution guarded by `is_execution_shard` 0/1 with the
boolean supplied by `publicValuesWellFormed`), and has **no dead field** — every field is consumed
by the `_of_obligations` combinators. `Relations.lean` shapes standard; `Sound.extract` correctly
noncomputable. Cross-shard stitching requires FULL-state continuity between consecutive execution
shards; `LastExecutionHalts` targets the last execution shard with a canonical HALT;
commit-coverage honestly scoped. CoreProfile `by decide` certificates pin names + both widths +
the 160-cell PV width against the generated manifest. Opcode routing: partition proved, x0
dispatch verified with worked examples, uncovered = exactly {ECALL, EBREAK, UNIMP} routing to
`none` (syscalls are ECALL-dispatched — not misrouted). Trivial-True sweep: all 12 hits by-design.

- **F-A9-01 (COSMETIC, fix queued).** Add/Sub/Subw Specs carry a stray leading `True ∧`
  (`Contracts/Chips.lean:73/:165/:278`) that Addi omits — dead conjunct, drop for uniformity.
- **F-A9-02 (DISCLOSED-OK — feeds V-track, = F-A8-04).** No `SP1MachineModel` instance exists;
  the theorem is a real parametric conditional (not vacuous — the RHS initial state comes from
  the `SemanticBoundaryBinding` existential, `model.boot` unused), but it is never exercised
  end-to-end in-repo. V-track: construct a model witness or disclose prominently.
- **F-A9-03/04/06/07/08 (DISCLOSED-OK).** Obligations bundle uninstantiated + reserved names;
  boundary/timestamp companion premises explicit; COMMIT scoping honest; ECALL/EBREAK/UNIMP the
  only uncovered opcodes; selector-driven chips' opcode-column binding lives in proof-file
  contracts (Coverage proves routing, not per-opcode Spec faithfulness).
- **F-A9-05 (STALE-DOC minor, fix queued).** `supported_core_native_sound`'s one-line doc
  (`AIR.lean:673-676`) omits the `SupportedCoreMemoryTimestampRangeRelation` third conjunct.

The A9 report's "safe-to-quote" paragraph (two headline statements, existential/shard-local
scoping, reserved names) is the template for the external report's claim-boundary section.

### Batch A1 — Add / Addi / Addw / Sub / Subw / AluX0 (complete; no BLOCKER, no WEAK-SPEC)

Semantic equations matched against Sail `execute_RTYPE/RTYPEW/ITYPE` (quoted clause lines) and the
Rust `opcode.rs` table with the operand mapping `op_b↦rs1`, `op_c↦rs2/imm` and the
non-commutative SUB/SUBW order verified load-bearing through `RV64.sub`/`rv64_subw_eq` and the
bridge lemmas. nonX0/onlyX0 rd-discipline, `clk_inc = 8`, and Assumptions-honesty (True or
isU64-only) all verified. AluX0: Spec correctly makes NO write/arithmetic claim (x0 write is an
architectural no-op); its `opcode < 29` byte-range check provably equals exactly the 29 ALU
opcodes (LB=29 starts non-ALU). The in-flight Subw migration tree was independently checked:
coherent, semantically unchanged vs HEAD.

- **F-A1-01 (COSMETIC, = F-A9-01).** The `True ∧` dead conjunct (Add/Sub/Subw).
- **F-A1-02 (STALE-DOC, fix queued).** `AddChip.Spec` docstring says "the two reader sub-Specs"
  but the Spec carries one (`RTypeReader.Spec`) plus the vacuous True; Sub/Subw inherit the
  wording (`Chips.lean:68-69/:161`).
- **F-A1-03/04/05/06 (DISCLOSED-OK).** Immediate sign-extension pinned at the ROM-decode layer
  (Addi/ADDIW pattern); AluX0 correctness-by-no-op design; AluX0 advance's indirect Spec linkage;
  ADDIW folded under the ADDW discriminant with the `imm_c` flag (mirrors Rust).

### Batch A4 — Mul / DivRem (complete; no BLOCKER)

Full four-source trace (Spec → RV64.* → bridge → Sail execute_*, cross-checked vs Rust `vm.rs`):
all five Mul variants (incl. MULHSU rs1-signed/rs2-unsigned end-to-end) and all eight DivRem
opcodes with every corner case (÷0 per signedness, INT_MIN/−1 overflow, W-variant low-32
semantics with sign-extension of the 32-bit result even for DIVUW/REMUW, T-division rounding, REM
sign follows dividend) verified exact. **The DivRem four-family evidence contract is total (the 8
cases partition onto 4 families, one-hot selection forced) and uniquely-determining** — the
Euclidean identities are over full-precision ℕ/ℤ (not mod 2^64), which is precisely what defeats
the classic underconstrained zk-division bug; `evidenceSoundness` consumes circuit facts plus
only the two disclosed operand `isU64` assumptions.

- **F-A4-01 (WEAK-SPEC low, fix queued within budget).** Public `MulChip.Spec`
  (`Chips.lean:636-646`) omits the selector one-hot (`is_real=1 → Σflags=1`), so a real row with
  all five flags 0 satisfies the public Spec vacuously. Not a soundness hole (the circuit asserts
  `is_real = Σflags` and the one-hot reaches the bridge via `SelectorOneHot`/`advanceReady`), but
  a spec-strength asymmetry vs DivRem's `RowSpec.selection`. Fix: export the one-hot conjunct
  into the Spec (already proven from constraints — modest change).
- **F-A4-02 (DISCLOSED-OK).** DivRem's two operand-isU64 `Assumptions` (vs Mul's `True`) —
  honest range facts discharged by the Memory-bus guarantee; derivation-site difference only.
- **F-A4-03/04/05 (CONFIRMED, no defect).** MULHSU signedness; DivRem opcode numbers vs
  `opcode.rs`; W-variant unsigned result sign-extension incl. ÷0 → `u64::MAX`.
- **F-A4-06 (COSMETIC).** `MulChip.ControlSpec` is structuring documentation, not the exported
  conclusion — no drift.

### R-track — Rust-faithfulness spot checks (complete; no BLOCKER)

The edges ChipFaithful cannot see, all verified against the pinned checkouts:
- **R1 PASS** — all 36 `MachineAir::name` strings + the 34/6 cluster split independently traced to
  `riscv/mod.rs` (Global correctly in both clusters; mprotect-gated user tables correctly
  excluded; `.Perm`-based certificates make order irrelevant, matching Rust's BTreeSet).
- **R2 PASS** — EventPopulate transcriptions field-exact vs the adapter `populate` paths
  (incl. the register-variant timestamp populate); **hint circularity refuted structurally**: the
  event opcode reaches only the flag hint, the input builders forget it, and the dumped opcode is
  the decoded instruction — independent of the result.
- **R3 PASS** — all 53 opcodes route identically to `tracing.rs` (x0 splits exact; stores/
  branches/jumps have no x0 split on both sides; ECALL/EBREAK/UNIMP uncovered on both sides).
- **R4 PASS** — both extractor patches are export-only (post-`air.eval` IR rendering; the ast.rs
  change makes extraction MORE complete); digests re-verified; overlay committed delta is
  derive-lines-only, enforced by SystemExit.
- **R5 PASS** — every pin/hash/profile gate is fail-closed (SystemExit before writing);
  `Provenance.lean` pins semantic+extractor revisions + patch digest, tied by `rfl`.
- **R6 PASS** — Add oracle re-derived symbol-by-symbol from the Rust AIR source: 4-limb carry
  chain with the 2^16-inverse form, double `is_real` booleanity (faithful duplication),
  `(6, value[i], 16, 0)` range sends, `clk_inc=8`/`PC_INC=4` wiring — exact.

- **F-R-01 (WEAK-SPEC — disclosed now, reconstruction filed as follow-up).** The whole-trace
  dumper (`witness_vectors --chip`) invoked by the TraceGen writer does not exist at the pinned
  overlay 69a8377c — nor at ANY commit in the sp1 history (verified by an all-history scan). The
  10 chip trace-vector batteries were dumped from uncommitted tooling, so they are not
  reproducible from the pinned exporter (the AIR layer is unaffected — EXTRACT_AIR_ONLY
  reproduces byte-identically). The vectors' CONTENT is still independently validated (the
  native_decide anchors check them cell-for-cell against the native circuit's own trace
  generation, and R2 verified the transcriptions + data consistency), but the provenance chain to
  pinned Rust is weaker than the witness-vector layer's. Follow-up (user-confirmed direction,
  2026-07-27): the extraction tooling lives on sp1's `dtumad/clean-native` branch (the overlay
  pin is its tip); reconstruct/commit the `--chip` whole-trace mode there and re-dump to confirm
  byte-identity as part of the same follow-up that restores the reproducible dependency pins —
  not in this campaign. Disclosed in `docs/agents/extraction.md`.
- **F-R-02 (STALE-DOC, fix queued).** `extraction.md:90-96` attributes the field-generic
  `expr.rs/var.rs/shape.rs` changes to the patch files; they are in the overlay's committed
  reflection diff. Doc drift only.
- **F-R-03 (DISCLOSED-OK).** Canonicalized assert ordering + faithful booleanity duplication.

### Batch A6 — LoadByte / LoadHalf / LoadWord / LoadDouble / LoadX0 (complete; no BLOCKER, no WEAK-SPEC)

Tri-model check (Spec ↔ Sail `execute_LOAD`/`extend_value` ↔ Rust `compute_load_value`): byte-lane
selection (little-endian `addr%8`), limb→byte decomposition, and all extension widths (LB/LBU
sext8/zext8 via the inline MSB byte pull, LH/LHU, LW/LWU with the LWU `msb·(is_lw−1)=0` gate, LD
identity) verified correct on every chip. Effective address = 64-bit wrapping `rs1 + sext(imm12)`
with the imm sign-extension correctly inherited from the ROM decode (unsigned loads still
sign-extend the immediate — matches RISC-V). **Alignment is a proven AIR conclusion** (hard-wired
AddressOperation offset bits per width; explicit per-width gates on LoadX0). LoadX0 performs the
real read with full address semantics and discards the write (values existentially discarded, not
wrong). RAM read at +1, `clk_inc = 8`. Findings: F-A6-01 (DISCLOSED-OK — RAM-content binding is
relative to `MemoryPullsBound`; boundary closure = the open obligations, correctly disclosed),
F-A6-02/05 (COSMETIC placement/brittleness notes), F-A6-03/04 (DISCLOSED-OK confirmations).

**Spec-review sweep A1–A9: COMPLETE. Zero BLOCKERs across all 25 chips + substrate + relation
level.** Open fix queue: F-A4-01 (Mul one-hot Spec export — the one WEAK-SPEC-low), F-A8-01
prose + F-A8-02 dead lemma (ByteTable.lean), F-A9-01/F-A1-01 `True ∧` conjuncts, F-A1-02
docstring, F-A9-05 doc third conjunct. Disclosure items for the report: F-A2-02
(completeness-side imm variants), F-A8-04/F-A9-02 (SP1MachineModel witness — V-track), F-A5-01
(4-byte alignment stricter than executor), F-A6-01 (memory-boundary obligations).

### Batch A7 — StoreByte / StoreHalf / StoreWord / StoreDouble (complete; no BLOCKER)

The read-modify-write merge math verified byte-for-byte against the Rust AIR
(`store_byte/half/word.rs`) and Sail `execute_STORE`; **non-target-byte preservation is a proven
theorem** (`patchedCellBytes`/`RamCellUpdate` — the "silently corrupts adjacent memory" failure
mode is proven absent, not just asserted). SH/SW/SD alignment (`addr%2/4/8 = 0`) is a proven
soundness conclusion from the AddressOperation decomposition with hard-wired offset bits. All four
carry `.store` RowEffects (widths 1/2/4/8) closing `execute_STORE_reaches_width{1,2,4,8}`;
op_a-slot = rs2 read-back matches Rust `prev_a()`; RAM +1 / reg +4/+3 timestamp offsets match
`MemoryAccessPosition`. Findings all DISCLOSED-OK/COSMETIC — notably F-A7-02 (the deliberate
two-layer design: RowEffect uses rs2 directly, the merge math is separately load-bearing for the
doubleword-bus reconciliation — both proven) and F-A7-06 (SB/SH/SW state a derivable
`isU64 store_value` assumption that SD avoids; cosmetic asymmetry).

### Batch A2 — Bitwise / Lt / UType (complete; no BLOCKER)

Verified: `byteOp` table AND=0/OR=1/XOR=2 vs `opcode.rs:163` with the genuine full-64-bit
reassembly; SLT/SLTU operand order vs Sail `zopz0zI_s/_u`; the MSB-flip signed→unsigned
comparison construction; LUI/AUIPC placement + sign-extension vs `execute_UTYPE` verbatim
(AUIPC uses the current pc); immediate forms folded into base opcodes exactly as SP1;
`clk_inc = 8`; nonX0-vs-any routing matches `emit_alu_event`/`emit_utype_event` incl. the forced
`a=0` on x0 writes; chip names match `MachineAir::name`.

- **F-A2-01 (DISCLOSED-OK trust boundary).** UType assumes the immediate-decode fact
  (`toBitVec64 op_b_imm = RV64.lui (immOf adapter)`) rather than deriving the imm20<<12 placement
  in-circuit — discharged at the program-ROM/grounding layer; report-worthy disclosure.
- **F-A2-02 (WEAK-SPEC low, completeness-side only).** Bitwise/Lt `ProverAssumptions` assume
  `imm_c = 0`, so XORI/ORI/ANDI/SLTI/SLTIU have no honest-prover completeness witness (soundness
  and the Sail bridges cover them). Disclose in the report's completeness paragraph.
- **F-A2-03/04 (DISCLOSED-OK/COSMETIC).** UType x0 rows vacuous on the value (faithful to SP1's
  forced `a=0`); Bitwise selector-active fact lives at the grounding layer (selector-chip
  pattern,= F-A3-07/F-A4-01).

### Batch A3 — ShiftLeft / ShiftRight (complete; no BLOCKER, no WEAK-SPEC)

All six opcodes traced Spec → `RV64.*` → pure Sail restatement → monadic `execute_*`: mask widths
exactly right (64-bit ops rs2[5:0] via `log2_xlen−1=5`; W-ops rs2[4:0]); SRL zero-fill vs SRA
bit-63 sign-fill; the counterintuitive SRLW case (logical shift in 32, then SIGN-extension to 64)
and SRAW (sign-fill from bit 31 of the low-32) both correct; immediate variants fold into the base
opcodes exactly as SP1's executor does, with identical shamt handling; Assumptions are isU64-only.
Bridges reach the monadic Sail clauses, not just pure restatements.

- **F-A3-01..06 (DISCLOSED-OK confirmations).** As above, each with quoted Sail clause evidence.
- **F-A3-07 (COSMETIC — same pattern as F-A4-01).** The public shift Specs don't force a selector
  flag on real rows (one-hot lives in `ControlFacts.selectorLink` + `advanceReady`). Pattern
  decision at fix time: export one-hot into the Mul Spec (flagged WEAK-SPEC-low there) and
  document the selector-chip pattern once for the rest.
