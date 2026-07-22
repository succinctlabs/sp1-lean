# SP1Clean — Honest Claim & Verification Audit

**Scope.** The trust-and-verification report for a skeptical ZK / formal-methods reviewer: what the
project proves, what it assumes, how faithfully it tracks the SP1 Rust source, and what remains for a
whole-machine claim. Unlike its predecessor, **every quantitative claim in this document is
machine-derived** — by `scripts/run_audit.sh`, whose raw census output is committed at
`snapshots/axiom-census.txt`. Re-run the harness before citing any number.

**2026-07-22 architecture and audit update.** The detailed census below was regenerated after the
following extraction/full-AIR changes:

- the semantic SP1 ground truth is now unmodified `a630089d9ff484ec6f2feade8d0afbb1447eed11`
  (`v6.3.1-8-ga630089d9`); extraction uses a separately hash-checked overlay whose runtime-source delta is
  reflection metadata only;
- direct Rust-to-Clean circuit output and `Extracted/Circuit/` have been deleted. Extraction emits rows
  and ordered assertion/interaction lists only; native circuit definitions are hand-maintained;
- the extractor now fails closed on the runtime 34-table execution cluster, 6-table memory-boundary
  cluster, all row widths, and 160 public cells. A full v6.3.1 AIR-only run reproduced every pre-existing
  instruction/reader/list artifact byte-for-byte and generated the missing system/public-value anchors;
- `CoreAIR.Current.Relation binds cluster` is the concrete heterogeneous upstream witness relation,
  strengthened to exact natural interaction-multiset equality. The public capstone is explicitly pinned
  to `.execution`, so the boundary cluster cannot satisfy an execution theorem;
- `sp1_air_refinement` and `sp1_air_sound` are implemented composition theorems, but are not closed full
  soundness results: they require the field-by-field `CoreAIRRefinementObligations` bundle plus the narrow
  temporary COMMIT/COMMIT_DEFERRED row-provenance premise; and
- syscalls are modeled as raw 264-tick events with an explicit `SyscallHandler`. This is honest about the
  fact that Sail has no SP1 host handler; a concrete handler/precompile refinement is still required.

Where historical sections describe `sp1_air_sound` as merely reserved, generated circuit normalization,
the v6.2.2 pin, or baseline system tables as unmodeled, this update controls.

**Pins and census refreshed 2026-07-22.** The dependency checkouts are local
migration pins; restore published git pins before release.

| What | Value | Command |
|---|---|---|
| sp1-lean | `be5222df` + this working tree | `git rev-parse HEAD` |
| toolchain | `leanprover/lean4:v4.31.0` | `cat lean-toolchain` |
| SP1 semantic source | `a630089d9` = **`v6.3.1-8-ga630089d9`** | `git -C ../sp1 describe --tags --always` |
| SP1 extraction overlay | `69a8377c` + checked-in patch digest `a2c43cfa…` | `Extracted/Provenance.lean` |
| Clean | `8e6ce748` (local 4.31 checkout) | `git -C ../clean rev-parse HEAD` |
| LeanRV64D | `793034f3` + the disclosed SP1 platform delta | `git -C ../sail-riscv-lean rev-parse HEAD` |
| RISCV | `e65c352a` | `git -C ../riscv-lean rev-parse HEAD` |
| Sail runtime | `79b4d085` | `git -C ../lean-sail rev-parse HEAD` |
| PolyFun | `502582b4` | `git -C .lake/packages/PolyFun rev-parse HEAD` |

Do not conflate the semantic revision with the extraction overlay. `update_extracted.py` checks both
identities, the overlay-to-semantic-base source delta, each component patch hash, and the combined dirty
diff before it writes an artifact. Bump all of those together with regenerated files.

> **Read this first if you read nothing else.** The Lean 4.31 migration currently has one genuine
> chip-soundness admission: `DivRemChip.evidenceSoundness`, the whole-chip extraction of unique selection,
> explicit family arithmetic evidence, and output routing from the generated constraints. Public
> `contractSoundness` is proved from that stronger statement, but inherits its `sorryAx`. The old nine
> per-op DivRem proof stubs were deleted. Four chip-completeness proofs and two DivRem circuit-law fields
> are also deferred; they affect bundled circuit axiom censuses but do not strengthen the semantic claim.
> At machine level, `supportedCore_orderedRows_dynamic` and `sp1_decoded_rows_sound` are the disclosed
> semantic and legacy structural grounding seams; `supported_core_witness_grounding` is now a proved
> assembly of exact State ordering, PC/clock/static facts, and the dynamic seam, and
> `supported_core_native_sound` is their correctly scoped
> local-execution consumer. Every Sail bridge, including all eight DivRem variants, is proof-complete conditional on its chip
> semantic contract. Run `scripts/run_audit.sh` for the authoritative current inventory.

---

## Part I — The honest claim

### The target chain and its current frontier

The architecture targets each of the **25 wired RV64IM base chips** (Add/Addi/Addw/Sub/Subw, Bitwise, Lt, ShiftLeft/Right,
Mul, DivRem, Jal/Jalr/Branch, UType, the five loads, the four stores, and the `x0`-destination paths
LoadX0/AluX0), natively in Lean 4.31 over a generic prime field (`Fact (2^17 < p)`; the whole machine
circuits under `Fact (2^24 < p)` and the no-wrap clock capstone under `Fact (2^25 < p)`, both satisfied
by KoalaBear). The desired chain is now separated into claims that
must not be conflated:

1. **Native chip semantics.** A satisfying native Clean row entails a semantic RV64 contract gated by
   `is_real`. This is proved for 24 chips; DivRem has the single explicit
   `evidenceSoundness` admission.
2. **ISA bridge.** Every one of the 25 semantic chip contracts reaches the corresponding generated
   LeanRV64D Sail instruction semantics, conditional on its reader/decode premises.
3. **Rust whole-chip faithfulness.** The extracted Rust row's complete `assertZero` list and all four
   interaction buses agree with the native chip after one row reconfiguration. This new stable boundary
   is proved for Add and Sub. The remaining chips' older operation/fragment anchors are useful migration
   evidence but are not counted as final whole-chip faithfulness.
4. **Native machine soundness.** A program-bound, balanced 36-table Clean witness should refine a finite
   shard-local Sail segment. `supported_core_native_sound` now proves exactly that; its sole dynamic
   dependency is `supportedCore_orderedRows_dynamic`. Canonical boot reachability is a separate shard-composition
   fact. The older Eulerian State trail is a proved intermediate result,
   not zkVM soundness.
5. **Upstream AIR and verifier soundness.** `supported_core_air_sound` is reserved for extracted/native
   refinement, `sp1_air_sound` for the complete upstream shard AIR and real public values, and
   `sp1_verifier_sound` for an ArkLib knowledge-sound verifier followed by `sp1_air_sound`. These names
   are intentionally not attached to weaker placeholder relations.

### The trust base (everything the chain bottoms out on)

- **A. The Lean kernel + three standard axioms** (`propext`, `Classical.choice`, `Quot.sound`).
- **B. Decision-procedure trust.** Main-library `bv_decide` proofs carry their generated reduction
  axioms. `native_decide` is forbidden in `SP1Clean/`; all 29 source occurrences are quarantined in
  `SP1CleanTest/` for executable witness/trace conformance and therefore trust the compiler.
- **C. The `sp1-constraint-compiler`** (`../sp1 crates/core/compiler`, at the pin): renders SP1's Rust
  AIR into the Lean constraint lists under `Extracted/`. **Black box assumed correct** — no Lean proof
  it reflects the Rust `eval`. Currency is now machine-checked (§II K1). The former circuit-form
  compatibility path is historical: the audited exporter now has no circuit backend (§II TB-9).
- **D. The LeanRV64D Sail model** as ISA ground truth. Per-chip bridges pull only the platform axioms
  on their execute paths (`sys_enable_experimental_extensions`, `load_reservation`,
  `match_reservation`, `plat_term_write`). **The target theorem, stated over the full `try_step`
  interpreter, imports the model's entire platform-axiom surface (~76 axioms: the softfloat
  `riscv_f16/32/64*` hooks, `get_16_random_bits`, the reservation set)** — through the *statement*,
  not through any proof gap; see `snapshots/axiom-census.txt`. Trusting the model = trusting these
  hooks.
- **E. The `populate` conformance gap** (§III.8): witness generators are conformance-tested at
  KoalaBear, not proven equal to SP1's Rust `populate`.
- **F. The named whole-machine obligations** — no longer prose: the semantic
  `supportedCore_orderedRows_dynamic` seam, the older structural `sp1_decoded_rows_sound` seam, and
  (post-W8) one `logupGkrSound` axiom. The legacy `Target.TargetObligations` surface remains frozen as
  an intermediate and is not the native theorem's public contract.

### The meaningfulness boundary = the named obligations of `TargetVm.lean`

The per-chip Sail guarantee is conditional (each `sailEquiv` internally quantifies its register/PC-read
and decode preconditions). What used to be a prose boundary is now the explicit hypothesis list of
`sp1_target_execution` (`Target.targetSeams`):

| Obligation | Content | Discharged by |
|---|---|---|
| `OperandsBound` (parameter) | the row's committed operand columns are honoured by the Sail state at its walk position | W2 (binding from memory-bus balance) + W3 (decode from program bus / InstructionDecode-Fetch chips) |
| `TargetObligations.bound` | every refining state at every walk position satisfies `OperandsBound` | W2 + W3 |
| `TargetObligations.lift` | one real `try_step` from a refining, operand-bound state produces the row's committed effect (`RowEffect`) | W7 (per-kind interpreter reduction; consumes the existing bridges) |
| `TargetObligations.halt`/`halt_nonempty` | the walk ends at the halting ECALL with the committed exit code | W5 (ECALL/HALT chip; needs the mixed 8/264 `clk_increment` generalization of `sndKey`) |
| `SailConfigured` | the platform residue of a runnable initial state (currently the empty conjunction — the obligation lives in `lift`) | W7 |
| `RowEffect.rom` strengthening | store-replay memory instead of ROM-intactness only | W2b + W4a |
| `sp1_decoded_rows_sound` (`DecodedRowsSound`) | Clean `Statement` → facts about the deterministic typed decode: per-row Specs, binary selectors, and State-bus correspondence (`state_accesses_perm`). The balance-translation half is **proven** (`sp1_state_balance_of_balancedInteractions`) | frozen W1b/W1c trail path |
| `supportedCore_orderedRows_dynamic` | the proved exhaustive ordering of exactly `realDecodedInstructionRows` → per-position Memory guarantees, circuit assumptions, chip Spec, operands, and readiness in the evolving Sail state | current semantic capstone seam |
| `supported_core_witness_grounding` | constraints + balance + provider/public-input binding → the exact physical-row order, PC walk, static grounding, dynamic grounding, and public clock count | proved assembly; inherits only the dynamic seam above |

The honest one-liner is unchanged in substance: *"each chip computes the correct RV64 function of its
committed column operands, and the rows chain in PC order"* is **proved**; *"the trace is a correct
execution of the decoded program against ISA register/memory state, ending at the committed exit
code"* is **stated** (`sp1_target_execution`) and reduces to the table above.

### Coverage boundary

Machine-derived surface (harness §A5): SP1's `RiscvAir` enum at the pin has **122 variants**
(`awk '/pub enum RiscvAir/,/^}/' crates/core/machine/src/riscv/mod.rs | grep -cE '^\s+[A-Z]\w*\('`).
The 25 wired chips model the **Supervisor-mode halves of 25 Supervisor/User pairs = 50 variants**.
Not modeled (72 variants): `Program`/`InstructionDecode`/`InstructionFetch` (3);
`SyscallInstrs(+User)`/`TrapExec`/`TrapMem` (4); `ByteLookup`/`RangeLookup` preprocessed tables (2;
byte semantics are modeled as a Clean table, the *table commitment* is assumed); the memory/page-prot
infrastructure `MemoryGlobalInit/Final`, `PageProtGlobalInit/Final`, `MemoryLocal`, `MemoryBump`,
`PageProt`, `PageProtLocal`, `StateBump` (9); `SyscallCore(+User)`/`SyscallPrecompile(+User)`/`Global`
(5); and **49 precompile variants** (SHA-256, Keccak, Ed25519, Secp256k1/r1, BN254, BLS12-381,
Uint256, Poseidon2, Mprotect, SigReturn — out of scope, enumerated so the boundary is explicit).
Opcode routing: **50 of 53** SP1 opcodes route to a wired chip (`Coverage.lean`, `by decide`);
ECALL/EBREAK/UNIMP are uncovered until W5. The User-mode duplicates are an open decision (same AIR
shape, different bus tags — claim shared coverage with justification, or list as a gap).

DivRem registry/capstone mismatch — **resolved this audit**: `DivRemChip.circuit` is now wired into
`sp1Tables` (25 = `allChipKinds`; guards `sp1Tables_length`/`allChipKinds_length` pin both). Ensemble
soundness never consumes `completeness` proofs, so the wiring was safe despite debt item 4.

---

## Part II — Faithfulness connections & divergences

### The six trust links

| # | Connection | Mechanism | Status (this audit) |
|---|---|---|---|
| K1 | SP1 Rust AIR → extracted Lean constraints | `sp1-constraint-compiler` via `update_extracted.py` | **Trusted compiler; currency machine-checked**: full AIR-only re-extraction at the v6.3.1 overlay reproduces every pre-existing instruction/reader/list artifact **byte-identically** and emits the pinned system/public/profile anchors. The overlay revision, exact patch set, semantic merge base, and reflection-only source delta are checked before generation. |
| K2 | extracted complete chip AIR ↔ native chip | `Extracted/ChipOracle/*` + `ChipFaithful` | **Proved for Add and Sub.** Remaining legacy operation/fragment anchors are migration evidence, not the final boundary; 23 whole-chip anchors remain. |
| K3 | generated/native chip constraints → semantic spec (`toBitVec64 = RV64.op`) | chip `soundness` | **Proved for 24 wired chips; one disclosed DivRem seam.** `DivRemChip.evidenceSoundness` states the stronger row→family-evidence target; public soundness is derived from it. |
| K4 | semantic spec → RISC-V Sail spec | `Bridge.lean` / `correct_*_native` | **Proved, `sorry`-free, all 25 chips** — including Mul (5 variants) and DivRem (8 variants), which the previous roadmap wrongly listed as missing. Conditional on register/decode reads; pulls the per-path Sail platform axioms. |
| K5 | per-row Sail steps → whole-program execution | timed grounding + native execution relation | **Open at `supported_core_native_sound`.** The balance-derived trail and conditional walk induction remain proved intermediate lemmas. |
| K6 | SP1 `populate` → Lean witness | conformance battery (`native_decide`, KoalaBear) | **Tested, not proved.** Ten complete-chip trace batteries cover Add/Sub/Subw/Addw/Mul/DivRem/Bitwise/Lt/ShiftLeft/ShiftRight; 11 transitional gadget batteries remain. `lake test` rechecks both layers. |

### Trust-boundary findings

| # | Attack | Status | Evidence |
|---|---|---|---|
| TB-1 | "non-byte interaction payloads carry no per-row meaning (`toProp = True`)" | **DEFERRED-HONEST** | payload meaning is trace-level, carried by balance; the syntactic `LookupAccess` anchors (Add/Sub/Addw/Subw, all four buses) close the per-row *shape* gap chip by chip |
| TB-2 | "`Extracted/*` may be stale vs the Rust" | **CLOSED at the pin** | §A4: byte-identical regeneration; `SP1_PINNED_COMMIT` assertion; remaining: a CI re-extract-and-diff job |
| TB-3 | "Bridge RHS is a local restatement, not generated Sail" | **CLOSED** | `correct_*_native` reduce the generated Sail monads; the *target* statement now uses `try_step` itself |
| TB-4 | "`is_real` binarity assumed" | **CLOSED** | derived from `is_real·(is_real−1) = 0` |
| TB-5 | "Specs are vacuous" | **CLOSED at the statement level; DivRem proof open** | `RV64.*` ISA equations; DivRem additionally requires unique selector commitment and explicit normal/div-zero/overflow evidence |
| TB-6 | "`populate` unverified" | **OPEN (disclosed)** | K6: conformance, not correspondence |
| TB-7 | "trace links are holes dressed as hypotheses" | **NARROWED** | PC chain, offline memory, and ROM membership are *derived* from balance; the residue is the named-obligation table (Part I) |
| TB-8 | "Clean elaboration smuggles axioms" | **CLOSED** | clean-3 headline census |
| TB-9 *(new)* | "the extraction pipeline is not reproducible against the pinned toolchain" | **CLOSED; strengthened 2026-07-22** | W9 originally normalized a transient Rust-to-Clean circuit format. The current audited overlay deletes that backend entirely and emits only row shapes plus ordered assertion/interaction lists. `update_extracted.py` checks the exact overlay diff and machine manifest before writing, and a full v6.3.1 AIR-only run reproduced every pre-existing list artifact byte-for-byte. |
| TB-10 *(new)* | "the `#print axioms` story of the capstone is cleaner than reality" | **DISCLOSED** | `sp1Tables` embeds each chip's full circuit record, so the five completeness admissions and the DivRem soundness seam surface transitively on registry/coverage/capstone projections even when a theorem uses only metadata. The census allowlist names every carrier. |

### Machine-model divergence catalog (unchanged verdicts re-checked, one addition)

D1 clock split (faithful) · D2 PC limbs (faithful) · D3 state bus shape (faithful) · D4 byte-bus value
slot (faithful) · D5 JAL link gate (faithful) · D6 J-type program-bus gate, multiplicative vs additive
(deliberate, documented) · D7 memory timestamp model (faithful; balance-derived) · D8 memory subsystem
chips (deferred → W4) · D9 LogUp/GKR balance (assumed → W8 packages as one axiom) · D10 decode/fetch
chips (deferred → W3) · D11 field generality (safe over-generalization) · D12 register/operand binding
(deferred → W2; now a named obligation, not prose). **D13 *(new; resolved 2026-06-10)*:** SP1's
syscall rows add 256 ticks to `CLK_INC = 8`, advancing the clock by **264** (`SyscallInstrs`); `StateAccess` now carries a per-row
`clk_inc` and `sndKey`/`stateLookups` key on `clk_low + clk_inc` (`balanced_state_bus` and the PC-chain
layer re-proved per-access). `stateAccess` projects `clk_inc := 8` — faithful for all 25 wired chips;
the HALT chip (W5) supplies 264 via a `RowView`-level increment when it lands.

---

## Part III — The machine-checked audit

### 0. Census summary (`scripts/run_audit.sh`, 471 probes, raw output in `snapshots/axiom-census.txt`)

The 2026-07-22 audit elaborates all 471 generated probes. It finds no project `axiom` declarations,
no `skipKernelTC`, and no main-library `native_decide`. There are 9 direct deferral sites across exactly
seven allowlisted files: four chip-completeness proofs; `DivRemChip.evidenceSoundness`; two DivRem
structural channel-law fields; and the two machine seams `sp1_decoded_rows_sound` and
`supportedCore_orderedRows_dynamic`.

Exactly 31 probed declarations carry `sorryAx`, all allowlisted. This larger transitive set is expected:
the unified supported-machine descriptor embeds full circuit records, so registry, coverage, and ensemble
projections inherit admitted structure fields. It does not represent 31 independent proof holes. The
census now probes every chip's bundled `circuit`, DivRem's separately housed completeness driver, the
exact Core profile guards, and `sp1_air_refinement`/`sp1_air_sound`; this closed scanner blind spots in
both the legacy and new capstone surfaces. Every theorem in `FormalModel/Contracts/DivRem.lean` and
`Proofs/Chips/DivRemChip/Cases.lean` is now probed and has no `sorryAx`; only the
generated-row-to-evidence extraction theorem is admitted. The two new capstone declarations are also
`sorryAx`-free (their Sail platform hooks enter through their semantic target types). Any new direct
deferral file or transitive carrier fails the audit.

### 1. Method & reproducibility

`scripts/run_audit.sh` (checked in — the predecessor document's "re-create the harness as needed" gap
is closed) assumes a green `lake build SP1Clean` (3578 jobs on this snapshot), then records pins →
text inventory with gates (sorry-set, no `axiom` declarations, and the no-`skipKernelTC`
guard `scripts/check_no_skipkerneltc.sh` — also a standalone CI `guards` job) →
`scripts/gen_axiom_probe.py` (namespace-tracking declaration
scanner; self-checking — a wrong FQN fails elaboration) → `lake env lean scripts/axiom_probe.lean` →
bucket + gate. Extraction currency: `SP1_DIR=../sp1 python3 update_extracted.py && git diff
--exit-code SP1Clean/Extracted` (the witness vectors regenerate in the same run and re-verify on the
next build).

### 2. Current blocker inventory

| Declaration / field | Tier | Notes |
|---|---|---|
| `DivRemChip.evidenceSoundness` | **soundness** | sole whole-chip constraint→selection/family-evidence/routing seam; public `contractSoundness` is proved from it |
| `DivRemChip.main_exposedChannelsLawful` | structural packaging | 4.31 normalization regression in the exposed State interaction proof |
| `DivRemChip.circuit.requirementsChannelsLawful` | structural packaging | 4.31 normalization regression; not an arithmetic assumption |
| `BranchChip.completeness` | liveness | legacy witness proof; whole-chip populate conformance is the replacement target |
| `ShiftLeftChip.completeness` / `ShiftRightChip.completeness` | liveness | 4.31 regressions |
| `DivRemChip.completeness` | liveness | independent of the soundness contract conversion |
| `supportedCore_orderedRows_dynamic` | machine soundness | timed Memory/spec/operand/readiness grounding of the proved exact active-row order |
| `sp1_decoded_rows_sound` | packaging premise | older structural decode facts for the frozen Eulerian path |

(Line numbers drift with edits — the harness gates on the *file set*, and this table on declaration
names. The predecessor's line citations were already stale at audit time.)

### 3. Per-operation release-readiness matrix

| Operation | Soundness | Completeness | Bridge | Faithful anchor | Witness conformance |
|---|---|---|---|---|---|
| Add/Addi/Addw/Sub/Subw | C3 | ✓ C3 | ✓ C3 | ✓ full `↔`, syntactic interactions (4 buses) | ✓ |
| Lt | C3 | ✓ | ✓ C3 | ✓ | ✓ (unsigned) |
| Bitwise | `oRB` | ✓ | ✓ C3 | ✓ forward | ✓ |
| ShiftLeft / ShiftRight | C3 | ✗ `SRY` | ✓ C3 | ✓ forward | — |
| Mul | **`oRB`** (settled) | ✓ | ✓ C3 (5 variants) | ✓ forward; syntactic dormant (~8 min compile) | ✓ |
| DivRem | ✗ `SRY` at `evidenceSoundness`; public contract factored/proved | ✗ `SRY` | ✓ (8 variants) | — (open) | full-trace test present |
| Jal / Jalr / Branch | C3 | Jal/Jalr ✓; Branch ✗ `SRY` | ✓ C3 + Sail-model | ✓ | — |
| UType (LUI/AUIPC) | C3 | ✓ | ✓ C3 | ✓ | — |
| Loads (5) / Stores (4) | C3 | ✓ | ✓ + Sail-model + `oRB` | ✓ full `↔` | — |
| LoadX0 / AluX0 | C3 | ✓ | ✓ | ✓ | — |

`C3` clean-3 · `oRB` + `ofReduceBool`/`trustCompiler` · `SRY` `sorryAx` · Sail-model = platform axioms.

### 4. Trace-level fidelity vs the Rust verifier

What SP1's verifier checks that a per-chip statement cannot, and where the model stands:

| Mechanism | Modeled & proved | Named obligation | Unmodeled |
|---|---|---|---|
| lookup/interaction soundness | multiset core, arities (State 5 / Memory 9 / Program 16 / Byte 4), gated multiplicities | `isConsistentBalanced` (→ one `logupGkrSound` axiom after W8) | LogUp-GKR circuit, fingerprints, zerocheck/PCS/Fiat–Shamir |
| PC / state chain | **derived from balance** (Eulerian trail); boundary = the verifier's `±1` state sends | — (dropped by the gated capstone) | — |
| program ROM membership | **derivable from balance** (`ProgramProviderSpike`) | ROM = `GuestProgram.rom` tie (W3) | preprocessed-trace commitment |
| byte table | `ByteRowSpec` + provider from balance, six opcodes | — | table commitment at setup |
| memory | per-row emits + offline-consistency from balance | operand binding (W2), data addresses in `RowView` (W2b), init/final image (W4a) | shards, global clock, address disjointness, global cumulative sum (W4b) |
| decode/fetch | opcode routing table (50/53, `by decide`) | the real decode predicate (W3) | `InstructionDecode`/`InstructionFetch` chips |
| execution semantics | per-chip Sail bridges; **target skeleton: trail → `try_step` chain proved** | step-lift per kind (W7), `SailConfigured` residue | — |
| halt / public values | boundary `(clk, pc)` ×2; `exit_code` in `SP1TargetPublicIO` | the HALT chip + `clk_increment` (W5) | the other ~19 `PublicValues` fields (digests, timestamps, init/finalize addresses) |
| shards | — | — | multi-shard composition entirely (W4b) |

**The answer to "what is still needed for the whole machine-level VM"** (logUp assumed): discharge the
Part-I obligation table — concretely the roadmap critical path **W3 → W4a → W2 → W5 → glue**, with
**W7** in parallel and **W1** as the independent packaging track; then W8 reduces the crypto assumption
to one named axiom. W4b (shards) extends the single-shard statement afterwards. Precompiles, traps,
page protection, and User-mode duplicates remain documented exclusions of the claim.

### 5. Witness generation — conformance, not correspondence

Unchanged in kind: constraints are tied to SP1 field-generically for all inputs (K2); the witness
generators are hand-ported and tied by 10 complete-chip trace batteries plus 11 transitional gadget
batteries at KoalaBear, regenerated from SP1's real `populate`/`generate_trace` by
`update_extracted.py` and re-checked by `lake test`. This is
a **liveness** gap only — soundness theorems do not depend on the witness layer. The shifts/branch/
load/store generators still have no anchors; closing B1 (real completeness proofs) subsumes the need
chip by chip.

### 6. What a skeptical SP1 engineer should still push on

1. **The lookup argument is assumed** (one Prop today, one axiom after W8) — the model proves the AIR
   and semantic layers above it. This is a scope statement, not a fine print.
2. **Single-shard.** SP1's memory soundness is fundamentally multi-shard; W4b is the answer and is not
   started.
3. **The 25-chip surface is the RV64IM base** — 50 of 122 `RiscvAir` variants; no syscalls (beyond the
   planned HALT slice), traps, page protection, or precompiles.
4. **K1 is the deepest unverified link** — and TB-9 shows the extraction pipeline has a real currency
   constraint right now. The proposed hardening (an AIR analogue of the witness battery: `#guard` that
   extracted constraints accept/reject the same rows as SP1's `eval`) remains open.
5. **The Sail platform surface** — the target theorem honestly carries ~76 model axioms; anyone
   consuming the claim is trusting LeanRV64D's hooks, not just its `execute_*` clauses.
