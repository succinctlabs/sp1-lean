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
