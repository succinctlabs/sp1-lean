# SP1Clean — Honest Claim & Verification Audit

**Scope.** The trust-and-verification report for a skeptical ZK / formal-methods reviewer: what the
project proves, what it assumes, how faithfully it tracks the SP1 Rust source, and what remains for a
whole-machine claim. Unlike its predecessor, **every quantitative claim in this document is
machine-derived** — by `scripts/run_audit.sh`, whose raw census output is committed at
`snapshots/axiom-census.txt`. Re-run the harness before citing any number.

**Pins (audit of 2026-06-10).**

| What | Value | Command |
|---|---|---|
| sp1-lean | `e076768` + this audit's changes | `git rev-parse HEAD` |
| toolchain | `leanprover/lean4:v4.28.0` | `cat lean-toolchain` |
| SP1 (the oracle) | `9d249b8d4` = **`v6.2.2-20-g9d249b8d4`**, branch `dtumad/clean-native` | `git -C ../sp1 describe --tags` |
| Clean | `292b9cc3` (= PR [#398](https://github.com/Verified-zkEVM/clean/pull/398) head; re-pin to `main` on merge) | `git -C .lake/packages/Clean rev-parse HEAD` |
| LeanRV64D | `b8186950` | `git -C .lake/packages/LeanRV64D rev-parse HEAD` |

Do **not** cite the SP1 pin as "v6.2.2" unqualified — the checkout is 20 commits past the tag, on the
project's own branch (it carries the `sp1-constraint-compiler` and witness-dump tooling).
`update_extracted.py` asserts this pin (`SP1_PINNED_COMMIT`); bump it together with regenerated files.

> **Read this first if you read nothing else.** *Soundness is `sorry`-free across every wired chip* —
> each chip `soundness` theorem and each Sail bridge is axiom-clean (the three Lean axioms, plus
> `bv_decide`/`native_decide`'s two trusted axioms where used, plus Sail-model platform axioms where the
> bridge reaches the Sail spec). The only `sorry`s are **three completeness/liveness holes and one
> capstone-packaging premise** (§III.2). The machine-level *target theorem* is now **stated in Lean and
> its simulation induction proved** (`Soundness/TargetVm.lean`): what separates today's capstone from
> "the real Sail interpreter executes the guest program to the committed exit code" is exactly the
> **named obligations** of `TargetObligations` (Part I) plus the one capstone premise — each mapped to
> one roadmap work item (`roadmap.md`).

---

## Part I — The honest claim

### The headline chain (defensible today)

For each of the **25 wired RV64IM base chips** (Add/Addi/Addw/Sub/Subw, Bitwise, Lt, ShiftLeft/Right,
Mul, DivRem, Jal/Jalr/Branch, UType, the five loads, the four stores, and the `x0`-destination paths
LoadX0/AluX0), natively in Lean 4.28 over a generic prime field (`Fact (2^17 < p)`; the whole machine
under `Fact (2^24 < p)`, satisfied by KoalaBear):

1. **(faithfulness)** SP1's real per-chip AIR constraints — extracted mechanically from the Rust source
   via the `sp1-constraint-compiler` — entail the chip's structural spec (`Faithful/`);
2. **(soundness)** that structural spec entails a **semantic** spec — a RISC-V equation
   `Word.toBitVec64 result = RV64.<op>(operands)`, gated by `is_real`;
3. **(Sail bridge)** that semantic spec drives the chip's emulation to agree with the **LeanRV64D
   RISC-V Sail spec** for that instruction (`correct_<op>_native`), *conditional* on register/decode
   reads;
4. **(whole-machine capstone)** the chips compose over one shared gated bus layer into
   `sp1_machine_soundness` (`Soundness/SP1GatedVm.lean`): from the Clean ensemble `Statement`
   (per-table constraints + balanced channels) over the committed public boundary, every real row's
   RISC-V step matches its proven SP1 chip and the committed `pc_start`/`next_pc` are the endpoints of
   a valid transition trail (an Eulerian-trail argument from the state-bus balance alone);
5. **(the target, stated + skeleton-proved)** `Target.sp1_target_execution`
   (`Soundness/TargetVm.lean`): given the capstone's execution certificate and the **named
   obligations** below, the *official LeanRV64D interpreter* (`try_step`), run from **any** Sail state
   that loads the guest program (`GuestProgram`/`IsInitialState`), reaches the halting `ECALL` with the
   committed `exit_code`. The walk induction (trail → real Sail chain) is proved, axiom-clean; the
   obligations are the precisely-bounded remainder.

### The trust base (everything the chain bottoms out on)

- **A. The Lean kernel + three standard axioms** (`propext`, `Classical.choice`, `Quot.sound`).
- **B. `bv_decide`/`native_decide`'s trusted core** (`Lean.ofReduceBool`, `Lean.trustCompiler`) —
  Bitwise/Mul decision procedures, the witness-conformance battery, the memory bridges'
  `plat_clint_base`. 18 `native_decide` occurrences in 15 files (counted by the harness; the previous
  ledger's "no `native_decide`" line was wrong).
- **C. The `sp1-constraint-compiler`** (`../sp1 crates/core/compiler`, at the pin): renders SP1's Rust
  AIR into the Lean constraint lists under `Extracted/`. **Black box assumed correct** — no Lean proof
  it reflects the Rust `eval`. Currency is now machine-checked (§II K1); the circuit-form emitter
  incompatibility found in this audit is closed (§II TB-9, W9: `_normalize_circuit_api`).
- **D. The LeanRV64D Sail model** as ISA ground truth. Per-chip bridges pull only the platform axioms
  on their execute paths (`sys_enable_experimental_extensions`, `load_reservation`,
  `match_reservation`, `plat_term_write`). **The target theorem, stated over the full `try_step`
  interpreter, imports the model's entire platform-axiom surface (~76 axioms: the softfloat
  `riscv_f16/32/64*` hooks, `get_16_random_bits`, the reservation set)** — through the *statement*,
  not through any proof gap; see `snapshots/axiom-census.txt`. Trusting the model = trusting these
  hooks.
- **E. The `populate` conformance gap** (§III.8): witness generators are conformance-tested at
  KoalaBear, not proven equal to SP1's Rust `populate`.
- **F. The named whole-machine obligations** — no longer prose: the fields of
  `Target.TargetObligations` + the decode seam `sp1_witness_decode` (`SP1WitnessDecode`;
  `sp1_gatedExecution_prereqs` is now a proven assembly of that seam with the W1a balance
  translation) + (post-W8) one `logupGkrSound` axiom.

### The meaningfulness boundary = the named obligations of `TargetVm.lean`

The per-chip Sail guarantee is conditional (each `sailEquiv` internally quantifies its register/PC-read
and decode preconditions). What used to be a prose boundary is now the explicit hypothesis list of
`sp1_target_execution` (`Target.targetSeams`):

| Obligation | Content | Discharged by |
|---|---|---|
| `OperandsBound` (parameter) | the row's committed operand columns are honoured by the Sail state at its walk position | W2 (binding from memory-bus balance) + W3 (decode from program bus / InstructionDecode-Fetch chips) |
| `TargetObligations.bound` | every refining state at every walk position satisfies `OperandsBound` | W2 + W3 |
| `TargetObligations.lift` | one real `try_step` from a refining, operand-bound state produces the row's committed effect (`RowEffect`) | W7 (per-kind interpreter reduction; consumes the existing bridges) |
| `TargetObligations.halt`/`halt_nonempty` | the walk ends at the halting ECALL with the committed exit code | W5 (ECALL/HALT chip; needs the `clk_increment` 256-vs-8 generalization of `sndKey`) |
| `SailConfigured` | the platform residue of a runnable initial state (currently the empty conjunction — the obligation lives in `lift`) | W7 |
| `RowEffect.rom` strengthening | store-replay memory instead of ROM-intactness only | W2b + W4a |
| `sp1_witness_decode` (the `SP1WitnessDecode` seam) | Clean `Statement` → rows decode + per-row Specs + the State-bus decode correspondence (`state_accesses_perm`). The balance-translation half of the former monolithic premise is **proven** (`sp1_state_balance_of_balancedInteractions`, clean-3, 2026-06-10); `sp1_gatedExecution_prereqs` is its sorry-free assembly with this seam | W1b/W1c (§B5; W1a done) |

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
| K1 | SP1 Rust AIR → extracted Lean constraints | `sp1-constraint-compiler` via `update_extracted.py` | **Trusted compiler; currency machine-checked**: re-extraction at the pin reproduces all 70 `Extracted/` modules **byte-identical**. Two process findings: TB-9 (circuit-form emitter incompatibility — closed by W9) and the witness-header drift (now committed). Pin assertion added. |
| K2 | extracted constraints → chip structural spec | `Faithful/<Chip>.lean` anchors | **Proved.** Full `↔` for the Add-family/loads/stores/Branch; forward `→` for Mul/Bitwise/Shift. The Mul *syntactic* interactions anchor exists but is **dormant** (commented out — its 26-element byte-list equality costs ~8 min of kernel time; `Faithful/MulOperation.lean`). DivRem anchor still absent (folded into roadmap W-items). |
| K3 | structural spec → semantic spec (`toBitVec64 = RV64.op`) | chip `soundness` | **Proved, `sorry`-free, all 25 chips** (census: clean-3, except Bitwise/Mul in the `bv_decide` bucket). |
| K4 | semantic spec → RISC-V Sail spec | `Bridge.lean` / `correct_*_native` | **Proved, `sorry`-free, all 25 chips** — including Mul (5 variants) and DivRem (8 variants), which the previous roadmap wrongly listed as missing. Conditional on register/decode reads; pulls the per-path Sail platform axioms. |
| K5 | per-row Sail steps → whole-program execution | gated capstone + **target skeleton** | **Proved** for the trail (balance alone) and for the trail→Sail-chain induction (`sp1_target_execution`); the concrete run is conditional on `TargetObligations` (Part I). |
| K6 | SP1 `populate` → Lean witness | conformance battery (`native_decide`, KoalaBear) | **Tested, not proved**, for Add/Sub/Subw/Addw/AddrAdd/IsZero/IsZeroWord/IsEqualWord/LtUnsigned/Mul/U16Compare/U16MSB/Bitwise (13 anchors); shifts/branch/loads/stores have none. Re-checked on every build via `#guard`/`native_decide`. |

### Trust-boundary findings

| # | Attack | Status | Evidence |
|---|---|---|---|
| TB-1 | "non-byte interaction payloads carry no per-row meaning (`toProp = True`)" | **DEFERRED-HONEST** | payload meaning is trace-level, carried by balance; the syntactic `LookupAccess` anchors (Add/Sub/Addw/Subw, all four buses) close the per-row *shape* gap chip by chip |
| TB-2 | "`Extracted/*` may be stale vs the Rust" | **CLOSED at the pin** | §A4: byte-identical regeneration; `SP1_PINNED_COMMIT` assertion; remaining: a CI re-extract-and-diff job |
| TB-3 | "Bridge RHS is a local restatement, not generated Sail" | **CLOSED** | `correct_*_native` reduce the generated Sail monads; the *target* statement now uses `try_step` itself |
| TB-4 | "`is_real` binarity assumed" | **CLOSED** | derived from `is_real·(is_real−1) = 0` |
| TB-5 | "Specs are vacuous" | **CLOSED** | `RV64.*` ISA equations; clean-3 soundness |
| TB-6 | "`populate` unverified" | **OPEN (disclosed)** | K6: conformance, not correspondence |
| TB-7 | "trace links are holes dressed as hypotheses" | **NARROWED** | PC chain, offline memory, and ROM membership are *derived* from balance; the residue is the named-obligation table (Part I) |
| TB-8 | "Clean elaboration smuggles axioms" | **CLOSED** | clean-3 headline census |
| TB-9 *(new)* | "the extraction pipeline is not reproducible against the pinned toolchain" | **CLOSED (2026-06-10, W9)** | root cause refined: the compiler at the pin emits a `name`/`main`-**field** `ElaboratedCircuit` from a *transient window of Clean main* (`60665ed0`, later reworked) — no pinned Clean ever accepted it, so a Clean pin bump alone could not fix it. W9 re-pinned Clean to the PR #398 head (`292b9cc3`), deleted the custom gating, and added `update_extracted.py::_normalize_circuit_api` (parameterized instance + `pullIf`/`toRaw` names). Verified: full regen at the SP1 pin reproduces all 70 `Extracted/` modules + `WitnessTests/` **byte-identical**, and the 14 circuit-form `Operations/*/Extracted.lean` likewise (the three drifted files — Add rfl-lemma layout, the two `Lt` bodies — were re-committed at the pin's emitter formatting). |
| TB-10 *(new)* | "the `#print axioms` story of the capstone is cleaner than reality" | **DISCLOSED** | `sp1Tables` *embeds* each chip's `completeness` proof as a structure field, so the three completeness `sorry`s surface as `sorryAx` on the whole capstone chain (`sp1Tables`→`sp1_machine_soundness`) even though the soundness proofs never consume those fields. The census shows it; the fix is closing B1 (or restating `Component` without the completeness field). |

### Machine-model divergence catalog (unchanged verdicts re-checked, one addition)

D1 clock split (faithful) · D2 PC limbs (faithful) · D3 state bus shape (faithful) · D4 byte-bus value
slot (faithful) · D5 JAL link gate (faithful) · D6 J-type program-bus gate, multiplicative vs additive
(deliberate, documented) · D7 memory timestamp model (faithful; balance-derived) · D8 memory subsystem
chips (deferred → W4) · D9 LogUp/GKR balance (assumed → W8 packages as one axiom) · D10 decode/fetch
chips (deferred → W3) · D11 field generality (safe over-generalization) · D12 register/operand binding
(deferred → W2; now a named obligation, not prose). **D13 *(new; resolved 2026-06-10)*:** SP1's
syscall rows advance the clock by **256** (`SyscallInstrs`); `StateAccess` now carries a per-row
`clk_inc` and `sndKey`/`stateLookups` key on `clk_low + clk_inc` (`balanced_state_bus` and the PC-chain
layer re-proved per-access). `stateAccess` projects `clk_inc := 8` — faithful for all 25 wired chips;
the HALT chip (W5) supplies 256 via a `RowView`-level increment when it lands.

---

## Part III — The machine-checked audit

### 0. Census summary (`scripts/run_audit.sh`, 314 probes, raw output in `snapshots/axiom-census.txt`)

| Bucket | Count | Members (summary) |
|---|---|---|
| clean-3 (`propext`, `Classical.choice`, `Quot.sound`) | **236** | the large majority: chip soundness, most completeness, faithfulness anchors, ALU/UType bridges + `kind`s, the GatedVm core (`exists_trail`, `state_trail_of_balance`, `chipRows_step_sound`, `gatedExecution_of_specs_and_balance`, `isConsistentBalanced_of_intCast_zero`, and the W1a balance translation `sp1_state_balance_of_balancedInteractions`) |
| + `ofReduceBool`/`trustCompiler` | 14 | `MulChip.soundness` (**settles the previously-open bucket question: it is `bv_decide`, not clean-3**) + the 13 witness-conformance anchors |
| + Sail axioms (loads) | 21 | load bridges/`kind`s: + `sys_enable_experimental_extensions`, `load_reservation`, `plat_term_write` |
| + Sail axioms (stores) | 12 | store bridges/`kind`s: + `match_reservation` instead of `load_reservation` |
| + Sail axioms (control flow) | 9 | Jal/Jalr/Branch bridges + `kind`s: + `sys_enable_experimental_extensions` |
| + Sail axioms (aggregates) | 6 | `allChipKinds(_length)`, `gatedExecution_allChips`, `coverage_kinds_eq_registry`, `coverage_length`, `routeOf_reaches_sail` — union of the per-chip footprints |
| + `sorryAx` (capstone chain) | 7 | `sp1_witness_decode` (the seam) and its consumer `sp1_gatedExecution_prereqs` (now a proven assembly, sorried only via the seam), and, via the embedded-completeness fields (TB-10), `sp1Tables(_length)`, `sp1GatedVm`, `sp1FormalEnsemble`, `sp1_machine_soundness` |
| clean-3 + `sorryAx` | 3 | the three completeness holes (ShiftLeft, ShiftRight, DivRem) |
| `propext` only / none | 4 | the `by decide` coverage guards; `sp1Assumptions` |
| clean-3 + **full Sail platform surface** (~76 axioms) | 1 | **`Target.sp1_target_execution`** — no `sorryAx`, no `bv_decide`; the surface enters through the `try_step` statement (trust base D) |
| ditto + `ofReduceBool`/`trustCompiler` + `sorryAx` | 1 | `Target.sp1_target_soundness` — inherits the capstone chain, as documented |

Gate (enforced by the harness): `sorryAx` is reachable from **exactly** the allowlisted set above;
any new carrier fails CI for the audit script.

### 1. Method & reproducibility

`scripts/run_audit.sh` (checked in — the predecessor document's "re-create the harness as needed" gap
is closed): pins → green `lake build SP1Clean` (3630 jobs; the only warnings are the four known
`sorry`s) → text inventory with gates (sorry-set, no `axiom` declarations, and the no-`skipKernelTC`
guard `scripts/check_no_skipkerneltc.sh` — also a standalone CI `guards` job) →
`scripts/gen_axiom_probe.py` (namespace-tracking declaration
scanner; self-checking — a wrong FQN fails elaboration) → `lake env lean scripts/axiom_probe.lean` →
bucket + gate. Extraction currency: `SP1_DIR=../sp1 python3 update_extracted.py && git diff
--exit-code SP1Clean/Extracted` (the witness vectors regenerate in the same run and re-verify on the
next build).

### 2. Blocker inventory — four `sorry`s, none in soundness

(`MulChip.completeness` closed 2026-06-10 via `MulOperation.spec_populate`.)

| # | Declaration | Tier | Notes |
|---|---|---|---|
| 1 | `ShiftLeftChip.completeness` | liveness | `BranchChip.completeness` recipe |
| 2 | `ShiftRightChip.completeness` | liveness | same |
| 3 | `DivRemChip.completeness` | liveness | soundness landed, axiom-clean |
| 4 | `sp1_witness_decode` | packaging premise | the `SP1WitnessDecode` decode seam (= roadmap W1b/W1c); the only non-chip debt. Its consumer `sp1_gatedExecution_prereqs` is now a proven assembly with the clean-3 W1a translation `sp1_state_balance_of_balancedInteractions` |

(Line numbers drift with edits — the harness gates on the *file set*, and this table on declaration
names. The predecessor's line citations were already stale at audit time.)

### 3. Per-operation release-readiness matrix

| Operation | Soundness | Completeness | Bridge | Faithful anchor | Witness conformance |
|---|---|---|---|---|---|
| Add/Addi/Addw/Sub/Subw | C3 | ✓ C3 | ✓ C3 | ✓ full `↔`, syntactic interactions (4 buses) | ✓ |
| Lt | C3 | ✓ | ✓ C3 | ✓ | ✓ (unsigned) |
| Bitwise | `oRB` | ✓ | ✓ C3 | ✓ forward | ✓ |
| ShiftLeft / ShiftRight | C3 | ✗ `SRY` | ✓ C3 | ✓ forward | — |
| Mul | **`oRB`** (settled) | ✓ C3 | ✓ C3 (5 variants) | ✓ forward; syntactic dormant (~8 min compile) | ✓ |
| DivRem | C3 | ✗ `SRY` | ✓ (8 variants) | — (open) | — |
| Jal / Jalr / Branch | C3 | ✓ (Branch C3) | ✓ C3 + Sail-model | ✓ | — |
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
generators are hand-ported and tied only by the 13-anchor `native_decide` battery at KoalaBear,
regenerated from SP1's real `populate` by `update_extracted.py` and re-checked on every build. This is
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
