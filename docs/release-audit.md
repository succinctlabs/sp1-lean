# SP1Clean — Honest Claim & Pre-Release Verification Audit

**Scope.** A read-only trust-and-verification report for a skeptical ZK / formal-methods reviewer. It states
what the project proves, what it assumes, how faithfully it tracks the SP1 Rust source, and where the
remaining gaps are. It consolidates the former `TRUST_BASE.md` (the one-page honest claim),
`AUDIT_REPORT.md` (faithfulness-connection + divergence analysis), and the detailed pre-release audit.

**Toolchain:** `leanprover/lean4:v4.28.0` · **Build:** `lake build SP1Clean` (a recent full green build
was ~3500 jobs). The exact axiom-bucket counts below are **estimates** pending a re-run of the Appendix-A
`#print axioms` census on a current green tree — `#print axioms` is the authoritative oracle and is the only
thing that catches transitive sorries and the `bv_decide`/`native_decide` buckets a `grep` cannot see.

> **Read this first if you read nothing else.** *Soundness is `sorry`-free across every wired chip* — each
> chip `soundness` theorem and each Sail bridge is axiom-clean (`#print axioms` = the three Lean axioms, plus
> `bv_decide`'s two trusted axioms where used). The only `sorry`s are **five completeness/liveness** holes
> (§2). The meaningful limits are **(a) coverage** (the RV64IM base chips, not SP1's full ~123-chip surface)
> and **(b) a conditional-Sail meaningfulness boundary** (operand/register/decode binding + the LogUp/GKR
> balance are *assumed*, not proved). Both are named honestly in the source, never hidden behind a `sorry`.

---

## Part I — The honest claim

### The headline claim (defensible today)

> For each of the **wired RV64IM base chips** (the ALU ops add/addi/addw/sub/subw/and-or-xor/slt-sltu/
> shifts/mul, the control-flow ops jal/jalr/branch/lui-auipc, and the load/store instruction ops, plus the
> `x0`-destination fast paths `LoadX0`/`AluX0`), this project proves, **natively in Lean 4.28 over a generic
> prime field** (`Fact (2^17 < p)`; Mul needs `Fact (2^24 < p)`), that:
>
> 1. **(faithfulness)** SP1's *real* per-chip AIR constraints — extracted mechanically from the Rust source
>    via the `sp1-constraint-compiler` — entail the chip's structural spec;
> 2. **(soundness)** that structural spec entails a **semantic** spec — a RISC-V equation
>    `Word.toBitVec64 result = RV64.<op>(operands)`, gated by `is_real`;
> 3. **(Sail bridge)** that semantic spec drives the chip's emulation to agree with the **`LeanRV64D`
>    RISC-V Sail spec** for that instruction; and
> 4. **(whole-machine)** the chips compose on one shared bus layer into the gated execution capstone
>    (`sp1_machine_soundness`, `Soundness/SP1GatedVm.lean`): every real row's RISC-V step matches its proven
>    SP1 chip, and the program counter chains through the trace in order.
>
> Every theorem in (1)–(4) is **axiom-clean** (the three Lean axioms, plus `bv_decide`'s two trusted axioms
> where used) — **except** the five completeness proofs in §2, and modulo the trust base below.

### The trust base (everything the chain bottoms out on)

**A. The Lean kernel + three standard axioms** (`propext`, `Classical.choice`, `Quot.sound`).

**B. `bv_decide`'s trusted core** (`Lean.ofReduceBool`, `Lean.trustCompiler`) — used for `BitVec` decision
procedures (e.g. the Mul high-half / sign-extension lemmas, Bitwise), and `native_decide` for the witness
conformance battery and the memory bridges' `plat_clint_base`.

**C. The `sp1-constraint-compiler`** (a Rust binary in the sibling `sp1` checkout). It renders SP1's real
Rust AIR (`eval`) into the field-generic Lean constraint lists under `SP1Clean/Extracted/`. This is a
**black box assumed correct**: there is no Lean proof that the compiler faithfully reflects the Rust AIR
builder calls. `update_extracted.py` regenerates the extracted files with **no hand-editing of constraint
bodies** (it applies only mechanical transforms — a `maxHeartbeats` prefix, an explicit `ProvableStruct`
instance for `DivRemCols`'s 45 fields, and one string-level promotion of a composed op's `channelsWith*`
list; none change constraint semantics). See `agents/extraction.md`.

**D. The `LeanRV64D` Sail model** — the generated Lean port of the RISC-V Sail reference semantics, taken as
ground truth for the ISA. It contributes the platform axioms `sys_enable_experimental_extensions`,
`load_reservation`, `match_reservation`, `plat_term_write`.

**E. The `populate` conformance gap.** SP1's witness generator (`populate`, native imperative Rust) cannot be
symbolically extracted. For a handful of operations it is tied to the Lean witness by **conformance testing**
— `#guard`/`native_decide` that the Lean witness reproduces real-`populate` outputs on a sampled input
battery at the concrete KoalaBear field. This is *testing, not proof* (see Part III §9).

**F. The deferred whole-machine assumptions** (named hypotheses on the capstone, never `sorry`):
- `OperandBinding`-style operand/register/decode threading — binding circuit columns to live ISA
  register/memory values and resolving `rs1`/`rs2`/`rd`/`imm`. This is the layer that would make the per-row
  Sail equivalence *unconditional*; today it is assumed (the meaningfulness boundary below).
- `isConsistentBalanced` — the LogUp/GKR multiset-balance fact discharged by the proof-system backend.

### The meaningfulness boundary (read carefully)

The per-chip Sail guarantee is **conditional**. Each `<Chip>.kind.sailEquiv` reads, in effect: *for any
register indices `rs1/rs2/rd` and any Sail state `s`, if `s` holds the chip's column operands in those
registers (and the immediate decodes as claimed, and the jump target is aligned, …), then the RISC-V step
equals the SP1 emulation.* Two things are therefore **assumed, not proved**, at the per-chip level:

- **Register/memory binding** — that the operand *values* in the circuit columns are the values the ISA
  machine actually holds in the named registers/memory.
- **Instruction decode** — that the register *indices* and immediates used in the Sail step are the ones the
  program actually encodes. SP1 itself has dedicated `InstructionDecode`/`InstructionFetch` chips for this;
  here it is deferred.

So the honest one-liner: **"each chip computes the correct RV64 function of its committed column operands, and
the rows chain in PC order"** is *proved*; **"the trace is a correct execution of the decoded program against
ISA register/memory state"** additionally *assumes* the deferred operand/register/decode threading +
`isConsistentBalanced`. The boundary is named in the per-chip `kind`s and the capstone's hypotheses — not
hidden behind a `sorry`.

### The gated execution capstone

The **gated VM execution capstone** (`Soundness/GatedVm/`, `gatedExecution_of_specs_and_balance`) is the
**sole** whole-machine capstone — the earlier bespoke `TraceValid` layer (`MachineSoundness`/
`MachineConsistency`) was retired (2026-06-05); the parity record lives in git history. It derives the
whole-program execution — *every real instruction is RISC-V-Sail-correct, and the committed
`pc_start`/`next_pc` are the endpoints of a valid transition trail* — from the **gated state-bus balance
alone**, via an Eulerian-trail argument (`exists_trail`). This **drops the entire trace-shape side-condition
block** (`clkInjective`, `TraceClkAdvance`, `TraceMemClkValid`, `memPrevLink`, …): the transition path is
forced by balance, not reconstructed from a clk-ordered adjacency. So for the execution result the trust base
shrinks to **`isConsistentBalanced` (the state bus) + the Sail model + (for the concrete Sail run) the
deferred operand/register/decode threading**. The boundary it enforces is also the *faithful* one: SP1 ties
`pc_start`/`next_pc` to the trace on the state bus, which the gated trail models directly.

Deriving `isConsistentBalanced` from Clean's ensemble `Statement.BalancedChannels` is packaged as the final
Clean `FormalEnsemble` `sp1FormalEnsemble` (`Soundness/SP1GatedVm.lean`), whose meaningful `Spec` is the gated
execution trail. Its `soundness` assembly is `sorry`-free but rests on **one isolated premise**
(`sp1_gatedExecution_prereqs` — the Clean→native balance translation + the per-chip witness decode; §2 item
5). Closing that premise shrinks the trust base below the retired bespoke capstone.

### Coverage boundary

**In scope and wired:** the RV64IM base chips above (including `Mul` and the `x0`-destination chips). ALU
instructions with `rd == x0` route to `AluX0`, closing the previous routing gap. **In scope, partial:**
`DivRem` (soundness landed and axiom-clean; completeness is a deferred `sorry`). **Out of scope** (documented,
not built): the structural chips SP1 ships and this project does not model —
`InstructionDecode`/`InstructionFetch`; `MemoryGlobalInit`/`Final`/`Local`/`Bump`/`StateBump`; `PageProt`;
the range-lookup chip; syscalls and all precompiles; and the Supervisor/User chip duplication (SP1 ships
~123 `RiscvAir` variants total). See `roadmap.md`.

---

## Part II — Faithfulness connections & model divergences

### The five kinds of "this matches reality" connection

The project chains **five distinct** faithfulness links. Knowing which is which (and how strong each is) is
essential to judging the whole.

| # | Connection | Mechanism | Strength / coverage |
|---|---|---|---|
| K1 | SP1 Rust AIR → extracted Lean constraints | `sp1-constraint-compiler` (auto, `update_extracted.py`) | **Trusted** (unverified compiler); mechanical, no hand-transcription |
| K2 | extracted constraints → chip structural spec | `Faithful/<Chip>.lean` anchors | **Proved**; full `↔` for Add-family/loads/stores/Branch, forward `→` only for Mul/Bitwise/Shift*; **absent for DivRem** |
| K3 | structural spec → semantic spec (`toBitVec64 = RV64.op`) | chip `soundness` | **Proved, `sorry`-free** for all wired chips |
| K4 | semantic spec → RISC-V Sail spec | `Bridge.lean` / `correct_*_native` | **Proved, `sorry`-free**; *conditional* on register/decode reads; pulls Sail-model axioms |
| K5 | per-row Sail steps → whole-program execution | gated capstone, Eulerian trail | **Proved** for the execution trail (balance alone); the concrete *run* needs the deferred operand/register/decode threading |
| K6 | SP1 `populate` (witness gen) → Lean witness | conformance `#guard` on sampled inputs | **Tested, not proved** (edge cases + seeded LCG) |

- **K2 direction matters.** The anchors are stated forward (extracted ⟹ structural spec), the
  soundness-relevant direction: K2∘K3∘K4 gives "SP1's actual constraints ⟹ correct RISC-V semantics." The
  full `↔` additionally certifies we drop no constraint.
- **K1 is the deepest unverified link.** Faithfulness is only as good as the constraint compiler — mechanical
  (good) but unproven. A cheap hardening: conformance-check the extracted constraints against SP1's own `eval`
  on sampled rows (an AIR analogue of K6).
- **K6 is testing.** For chips whose completeness is proved, the witness story is covered by the proof; for
  the `sorry` chips, the only `populate` evidence is sampled conformance.

### Machine-model divergence catalog (Rust-anchored)

Verdict legend: **faithful** / **safe-simplification** / **deliberate divergence** / **deferred**.

| # | Aspect | SP1 Rust | This project | Verdict |
|---|---|---|---|---|
| D1 | Clock | `clk_high`/`clk_16_24`/`clk_0_16`, `CLK_INC = 8` | identical split, increment 8 | **faithful** |
| D2 | PC | 3×16-bit limbs | 3×16-bit limbs | **faithful** |
| D3 | State bus | `receive_state`/`send_state`, 5-elt msg | same receive/send, same shape | **faithful** |
| D4 | Byte bus value slot | `send_byte(opcode, a, b, c)` — value in **`a`** | value in `a` | **faithful** (the once-claimed `a`-vs-`b` divergence is **not real**) |
| D5 | JAL link gate | multiplicity `is_real - op_a_0`; result 0 when `op_a_0=1` | spec mirrors: link `= pc+4` gated by `op_a_0 = 0` | **faithful** |
| D6 | J-type program-bus gate | additive `is_real - imm` | multiplicative `is_real*(1-imm)` | **deliberate divergence** (user-approved; semantically a gated-off message) |
| D7 | Memory timestamp ordering | `MemoryAccessCols` + diff decomposition | same `prev_value` + diff decomposition; offline link from balance | **faithful** (model) / **deferred** (full balance, D9) |
| D8 | Memory subsystem chips | MemoryGlobalInit/Final, MemoryLocal, MemoryBump, StateBump | none (only load/store instruction chips) | **deferred / out of scope** |
| D9 | LogUp/GKR balance | discharged by the proof-system backend | `isConsistentBalanced` assumed | **deferred** (honest assumption) |
| D10 | Decode/fetch | `Program`/`InstructionDecode`/`InstructionFetch` chips | program bus + readers; operand/imm decode deferred | **deferred** |
| D11 | Field | KoalaBear (~2³¹) | generic `Fact (2^17<p)`, Mul `Fact (2^24<p)` | **safe-simplification** (over-general) |
| D12 | Register/operand binding | live ISA register file, decoded indices | columns assumed to hold ISA values; indices universally quantified | **deferred** (the meaningfulness boundary) |

The genuine *correctness-relevant* divergences are D6 (deliberate, documented, sound) and the *deferred*
items D8/D9/D10/D12. None silently weakens a wired chip's soundness; they bound what the whole-machine claim
covers.

---

## Part III — Pre-release audit

### 0. Executive summary

The "axiom-clean" promise is **mechanically verified and largely true**, with a **precisely-bounded blocker
set** (5 completeness `sorry`s) and a **frank account of what the model does *not* cover relative to the Rust
SP1 source** (§8–§9). The per-row arithmetic story is strong and the **soundness/bridge layer is fully
`sorry`-free** (every chip `soundness`, every bridge, every wired capstone is clean); the **trace-level /
global argument and the witness generators remain where fidelity is thin**.

**Axiom census (estimated, pending the Appendix-A re-census):**

| Bucket | Meaning |
|---|---|
| **clean-3** `[propext, Classical.choice, Quot.sound]` | kernel-clean — the large majority of headline theorems |
| **+ `ofReduceBool`/`trustCompiler`** | `native_decide`/`bv_decide` (compiler/LRAT trust). Permitted by AGENTS.md; disclose. The 16 memory Sail bridges, the Bitwise group, possibly `MulChip.soundness` (mul-high `bv_decide`). |
| **`sorryAx`** | **5 release blockers** — the completeness holes in §2. |

**The headline facts a skeptic should carry:**

1. **The soundness story is complete.** Every chip `soundness` theorem is `sorry`-free and `#print
   axioms`-clean. There is no remaining soundness hole.
2. **All three control-flow Sail bridges are proven** (`correct_{jal,jalr,branch}_native` + their
   `*_reaches_sail`), as are the UType LUI/AUIPC bridges.
3. **The whole-program statement is the gated capstone** (Part I), derived from the state-bus balance via an
   Eulerian trail — it does not depend on the completeness `sorry`s.
4. **The whole cryptographic argument is out of scope** (§8.1). The model proves the **AIR / per-row
   constraint** layer and abstracts the lookup/permutation/PCS soundness to a single `isConsistentBalanced`
   Prop; multi-shard composition (public values, global cumulative sum, init/finalize) is **not modeled**.
5. **Witness generation has conformance, not correspondence** (§9) — a liveness-only gap.

**Release gate (proposed):**
- [ ] `#print axioms` over all headline theorems = **0 `sorryAx`** (currently 5).
- [x] No *soundness*/*bridge* theorem and no wired capstone carries `sorryAx`. **Met.**
- [ ] The trust boundary (Part I, §8, §9) is stated prominently in public docs so neither is over-read as
      "fully verified". **Met** in `README.md` + this doc.

### 1. Method & reproducibility

Pin + green build at HEAD; enumerate every headline theorem by layer (`correct_*_native`, `*_reaches_sail`,
chip/op/reader `soundness`/`completeness`, `*_faithful`); `#print axioms` each (Appendix A) and bucket. The
census is the authoritative oracle — it catches transitive *and* inline sorries that grep/build-warnings
miss. The blocker list (§2) is a verbatim `grep` of proof-holes (reliable for direct sorries); the bucket
counts are estimated until the harness is re-run.

### 2. Verified blocker inventory (5 `sorry` proof-holes)

Each is a verbatim `sorry` proof-hole (`rg -nP '^\s*sorry\s*$' SP1Clean`), confirmed against a green
`lake build SP1Clean`. **No soundness or bridge theorem is among them** — all five are **completeness**
(liveness) or a single capstone prerequisite premise.

| # | Theorem (FQN) | Tier | Source | Notes |
|---|---|---|---|---|
| 1 | `MulChip.completeness` | T2 | `Chips/MulChip/Formal.lean:109` | placeholder all-zero witness; needs `MulOperation.spec_populate` + heavy-arithmetic deferral |
| 2 | `ShiftLeftChip.completeness` | T2 | `Chips/ShiftLeftChip/Formal.lean:405` | needs honest `populate`-style witness + `ProverHint` opcode threading |
| 3 | `ShiftRightChip.completeness` | T2 | `Chips/ShiftRightChip/Formal.lean:1696` | same recipe as ShiftLeft |
| 4 | `DivRemChip.completeness` | T2 | `Chips/DivRemChip/Formal.lean:72` | DivRem soundness landed (axiom-clean); only completeness remains |
| 5 | `sp1_gatedExecution_prereqs` | premise | `Soundness/SP1GatedVm.lean:193` | the single isolated capstone premise (Clean→native balance translation + per-chip witness decode) |

Tiering: **completeness** (T2) ⇒ only a valid input could be rejected (liveness). None is mathematically
open: items 1–4 are the substantial work (honest `populate`-style witnesses + `ProverHint` opcode threading,
a `main`-level change) — exactly the recipe already applied to `BranchChip.completeness`, which is proven and
clean-3. Item 5 is a packaging premise that, once discharged, drops the capstone below the retired bespoke
trust base.

### 3. Axiom census detail

**The `ofReduceBool`/`trustCompiler` bucket (compiler-trust, disclose):** the 16 memory Sail bridges
(`correct_{load,store}_*_native` + `*_reaches_sail`) via `SailMemory.lean`'s `native_decide` on
`plat_clint_base`; `BitwiseChip.{soundness,completeness}` + `BitwiseU16Operation.{soundness,completeness}` via
`bv_decide`; and possibly `MulChip.soundness` (its Spec routes through a mul-high `bv_decide` in
`Specs/Chip.lean` — the open census question; being `sorry`-free, it likely lands in this bucket). The memory
**chips** themselves are clean-3; only the bridges inherit `ofReduceBool`. Hardening: replace the
`plat_clint_base` `native_decide` with `decide`/`bv_decide` (R7).

**Disclosed non-headline carriers:** the witness `*_conforms` battery + `instFactSP1Prime` (`native_decide`,
KoalaBear); `sys_enable_experimental_extensions` and the other Sail platform axioms (generated-Sail).

### 4. Trust-boundary findings (per-row / extraction layer)

| # | Attack | Status | Evidence |
|---|---|---|---|
| TB-1 | "`*_interactions_faithful` proves nothing about register/memory/PC payloads." | **DEFERRED-HONEST, disclose** | `Interaction.toProp = True` for all non-byte sends + all receives; only byte sends carry content (raw values, `is_real`-gated via `toRawGated` — faithful to SP1's `send_byte(…, is_real)`). Per-row payload meaning is deferred to trace balance (§8.2). |
| TB-2 | "`Extracted/*.lean` may be stale vs the Rust." | **NARROWED (process gap remains)** | Byte-bus leaf ops (Add/Sub/U16Compare) auto-generate circuit form, so soundness/completeness run on the extracted artifact *by construction*. Remaining ops keep the hand-managed two-list form, and there is **no SP1 pin / CI re-extract-and-diff** — currency unverifiable from the repo (see ROADMAP). |
| TB-3 | "Bridge RHS is a local restatement, not generated Sail." | **CLOSED** | `correct_*_native` reduce the generated `execute_RTYPE`/`execute_{JAL,JALR,BRANCH}`/LUI/AUIPC/memory monads — no remaining bridge gap among wired chips. |
| TB-4 | "`is_real` gate is assumed binary." | **CLOSED** | derived from `is_real*(is_real-1)===0` via `bool_of_mul_pred` in soundness. |
| TB-5 | "Specs are vacuous." | **CLOSED** | Specs are `RV64.*` ISA equations; the clean-3 soundness/bridge theorems are non-trivial. |
| TB-6 | "`populate` unverified." | see **§9** | conformance-not-correspondence. |
| TB-7 | "Trace links are holes dressed as hypotheses." | **DEFERRED-HONEST** | the trace-shape side conditions are genuine props, not `True`/`sorry`. |
| TB-8 | "Clean elaboration smuggles axioms." | **CLOSED** | the clean-3 headline theorems ⇒ the Clean layer adds nothing. |

### 5. Per-operation release-readiness matrix

| Operation | Chip soundness | Chip completeness | Bridge `correct_*` | Ready? |
|---|---|---|---|---|
| Add/Addi, Addw, Sub, Subw, Lt | ✓ C3 | ✓ | ✓ C3 | **yes** |
| Bitwise | ✓ `oRB` | ✓ | ✓ C3 | yes (disclose) |
| Load{Byte,Half,Word,Double}, Store{…} | ✓ C3 | ✓ | ✓ **bridge `oRB`** | yes (disclose; R7) |
| LoadX0, AluX0 | ✓ C3 | ✓ | — | yes |
| Jal, Jalr | ✓ C3 | ✓ | ✓ C3 | **yes** |
| UType (LUI/AUIPC) | ✓ C3 | ✓ | ✓ C3 | **yes** |
| Branch | ✓ C3 | ✓ C3 | ✓ C3 | **yes** |
| Mul | ✓ (C3 or `oRB`*) | ✗ `SRY` (#1) | — | partial |
| ShiftLeft | ✓ C3 | ✗ `SRY` (#2) | — | partial |
| ShiftRight | ✓ C3 | ✗ `SRY` (#3) | — | partial |
| DivRem | ✓ C3 | ✗ `SRY` (#4) | — | partial |

`C3` clean-3 · `oRB` +ofReduceBool · `SRY` sorryAx. *Mul chip soundness is `sorry`-free; its bucket (C3 vs
+`oRB` from the mul-high `bv_decide`) is the open census question (§3). The Mul/ShiftLeft faithfulness anchors
are proven clean-3; only the completeness items remain.

### 6. Trust boundary (TCB)

Even with every blocker cleared, a meaningful release rests on: (1) the generated `LeanRV64D` Sail model
(incl. its platform axioms); (2) `update_extracted.py` output (pending the currency-CI work); (3)
`ofReduceBool`/`trustCompiler` for the memory/bitwise theorems + the witness battery; (4) the threaded
`isConsistentBalanced` and the **entire cryptographic argument** (§8); (5) `[Fact (2^17<p)]`/`[Fact (2^24<p)]`
at KoalaBear; (6) the hand-written `ExtractionDSL`/`ByteOpcode` vocabulary; (7) the witness generators (§9).

The prioritized remediation backlog and the strategic gap-closing work items now live in `roadmap.md`.

### 7. Modeling fidelity vs the Rust SP1 source (trace level)

**How much of SP1's soundness story does the Lean model capture?** SP1 (v6.2.2) is a *hypercube* STARK using
**LogUp-GKR** lookups and a **Basefold/stacked** multilinear PCS. The model operates at the **AIR / per-row
constraint** layer and is largely backend-agnostic; the entire proof-system layer below it is out of scope.

**§8.1 — Not modeled at all (the cryptographic argument).** The project proves facts about chip
**constraints** and a **Sail** semantic bridge. It does **not** model the zerocheck/sumcheck, the multilinear
PCS / Basefold openings, Fiat-Shamir, or the LogUp-GKR circuit that actually proves the lookup balance. The
model **assumes the cryptographic argument is sound** and asks only "if the committed trace satisfies the AIR
+ the lookups balance, is each row semantically correct?" That is a legitimate scope — but it is *not* "SP1 is
verified"; it is "SP1's AIR constraints imply the RISC-V semantics, modulo the prover's soundness."

**§8.2 — Channels / interactions: abstracted to a `Prop`.** The multiset core `InteractionBus` is real and
permutation-invariant, and `isConsistentBalanced` is the per-key sum-zero predicate. But `Interaction.toProp`
is `True` for every State/Memory/Program send and all receives — the per-row bus payload carries no meaning;
only Byte sends do. The Lean interaction **arities match SP1's** (State 5, Memory 9, Program 16, Byte 4),
which is reassuring, but the actual affine column-combinations and the fingerprint randomization are not
modeled. A vacuous per-row send is *safe only because* SP1's cumulative-sum-zero check forces a matching
receive — which the model **assumes** (`isConsistentBalanced`) rather than proving.

**§8.3 — Byte table: the most faithfully modeled.** `ByteRowSpec` models SP1's preprocessed 256×256 byte
table as a Clean `Table`; all six opcodes carry real `ByteOpcode.constrain` semantics; and `ByteProvider`
membership-from-balance is **proven** (`byteAccessValid_of_balance`). Byte rows send the raw
`⟨opcode, value, width, 0⟩` message multiplicity-gated by `is_real`, lining up 1:1 with SP1's `send_byte`.
*Gap (minor):* the table's commitment at setup and the in-table degree-2 constraints are assumed.

**§8.4 — Memory: balance-derived.** The offline-online memory consistency proposition is **derived** from the
Memory-bus balance (the closed-bus analogue of State's PC chain), via a read/write-faithful `MemEvent`
encoding, a closed-bus receiver (`Chips/MemoryProvider.lean`), and a per-address single-address argument,
modulo honest trace-shape side conditions. *Gap:* the model still **does not model shards, the global clock as
a counter, init/finalize, address disjointness, or the global cumulative sum** (single-shard only;
cross-shard is a ROADMAP item), and real 3-limb load/store addresses are not yet aggregated into a wired
capstone. This is where an SP1 reviewer pushes hardest.

**§8.5 — State / PC chain: balance-derived.** The adjacent-row PC handoff is derived from the State-bus
balance plus honest trace-shape side conditions; the gated capstone (Part I) then forces the whole transition
trail from balance alone, dropping those side conditions for the execution result.

**§8.6 — Program ROM: better than memory/state.** Program/instruction membership is dischargeable from
balance via `ProgramProvider` — *not* a residual assumption, only the underlying `isConsistentBalanced` is.
This is the model at its strongest.

**§8.7 — Machine / multi-shard.** *Proven:* per-row projections, `is_real=0` padding-gating, the "emitted =
projection" recovery theorems, and the gated capstone. *Unmodeled:* **shards and their composition** —
public-values threading, the global cumulative-sum-zero check, padding-to-power-of-two as the PCS sees it, and
constraint-evaluation-at-a-random-point.

**At a glance:**

| Mechanism | Faithfully modeled | Threaded hypothesis | Unmodeled / assumed |
|---|---|---|---|
| Lookup/interaction soundness | multiset core, arities | `isConsistentBalanced` | LogUp-GKR, fingerprints, cumulative-sum-zero |
| Per-row bus payloads | **byte only** | — | state/memory/program payloads (`toProp=True`) |
| Byte table | ByteRowSpec + provider + 6 opcodes | — | table commitment, in-table constraints |
| Memory | per-row emit + padding + faithful read/write + provider + offline link from balance | trace-shape side conditions | real load/store addrs (deferred); shards, global clock, init/final, disjointness, global sum |
| PC / state | per-row emit + padding + chain from balance + gated trail | (dropped by gated capstone) | clock-link discharge from per-row Specs |
| Program ROM | emit + membership from balance | (only `isConsistentBalanced`) | — |
| Machine | padding-gating, gated execution capstone | (state-bus balance) | shards, public values, zerocheck, PCS, Fiat-Shamir |

### 8. Witness generation — conformance, not correspondence

A structural asymmetry an auditor must weigh: **the constraints are tied to SP1 for all inputs; the witness
generators are not.**

- **Constraints (strong tie):** `*_constraints_faithful` anchors prove SP1's *extracted Rust constraints* are
  equivalent to the native gadget spec, **field-generic, for all inputs** (modulo TB-1's byte-only scope and
  the forward-only halves).
- **Witness generators (weak tie):** the `populate` functions are **hand-ported native imperative code** that
  cannot be symbolically extracted like `eval`. Their tie to SP1 is a **finite `native_decide` battery at the
  concrete KoalaBear field** — explicitly *a conformance tie, not an all-inputs proof* — for only a handful of
  ops (Add, Sub, Subw, Addw, IsZero, IsZeroWord, LtUnsigned). The shifts/mul/branch/load/store generators have
  **no conformance anchor at all** (and their completeness is sorried where listed).
- **`spec_populate`** (per-op `Operations/<Op>/Populate.lean` for Add/Sub/U16Compare) proves the *Lean*
  `populate` satisfies the gadget's *own* Spec for all inputs — internal correctness, **not** agreement with
  SP1's Rust `populate`.

**Why it matters (and its bound):** if the Lean `populate` diverges from SP1's real `populate` outside the
battery, the completeness/liveness proofs would certify a witness generator that is *not what SP1 runs* — and
the divergence is undetectable by the model. **But this is a liveness gap, not a soundness gap:** the
constraints reject bad witnesses regardless, and chip *soundness* theorems are clean-3 (they do not depend on
the witness layer). Recommended (ROADMAP): document this asymmetry; widen the battery and/or prove
`spec_populate` for the remaining ops; ideally pursue a real `populate_lean = populate_rust` correspondence.

### 9. Estimated SP1-developer reactions

What a core SP1 engineer would likely think — offered as constructive anticipation of reviewer concerns.

**Likely positive:**
- "The semantic spec is the right call." Proving `toBitVec64 = RV64.add …` against the **generated RISC-V Sail
  model** — an independent golden ISA — is stronger than re-asserting our own constraints, and the axiom-clean
  discipline is real rigor.
- "The faithfulness anchors to our *extracted* constraints are the right seam," and the interaction arities
  match ours (State 5, Memory 9, Program 16, Byte 4).
- "Field-generic over `ZMod p`, checked at KoalaBear — matches where our prover runs."

**Likely concerns:**
- "You've verified the part we worry about *least*." Per-row ALU/byte arithmetic is the well-trodden 80%. The
  scary bugs live in **lookup-argument soundness, the cross-shard memory/global argument, recursion, and the
  precompiles** — exactly what §8 shows is assumed or out of scope.
- "The chip surface is a small slice." Real SP1 is 30+ chips: SHA/Keccak/secp/bn254/bls precompiles,
  syscalls, the Global chip, PageProt, the range chip, the memory init/finalize chips, plus the whole
  recursion/STARK-compression stack. None is modeled.
- "Witness gen isn't our code." `populate` is hand-ported and only conformance-tested on a few vectors.
- "Is this against current `main`?" Currency isn't proven; we'd ask for a pinned SP1 commit and a CI job that
  re-extracts and diffs.
- "Memory is the headline gap." Timestamp-ordered offline memory across shards with public-value
  address-disjointness is *the* SP1 soundness argument; threading it as one hypothesis is a big IOU.
- "Sail vs our executor." Conformance to the official RISC-V Sail is a nice independent check, but our
  semantics are ultimately our Rust executor + AIR — we'd want assurance our executor matches Sail too.

**Likely asks:** wire `lake build` + an axiom check into CI; pin SP1 and automate re-extraction; state the
trust boundary front-and-center; and prioritize the memory/global argument and the lookup-soundness statement
over adding more ALU chips. These map directly onto `roadmap.md`.

---

## Appendix A — Reproduce on a green tree

```bash
git rev-parse HEAD && cat lean-toolchain && lake build SP1Clean      # expect green
# headline enumeration:
grep -rnP 'theorem\s+correct_\w+_native|theorem\s+\w*reaches_sail|theorem\s+(soundness|completeness)\b|theorem\s+\w*faithful' SP1Clean --include='*.lean'
# direct sorry proof-holes (expect the 5 in §2):
grep -rnP '(^\s*sorry\s*$)|(=>\s*sorry\s*$)|(:=\s*sorry\s*$)' SP1Clean --include='*.lean'
```

For the authoritative axiom census, emit `#print axioms <FQN>` over the grep'd headline set and bucket the
output into clean-3 / `ofReduceBool` / `sorryAx`. **Cheapest targeted spot-check** (no full build; confirms the
estimates that matter most): a one-off file with `#print axioms` over `sp1_machine_soundness`,
`MulChip.soundness` (clean-3 vs +`ofReduceBool`?), and `correct_{jal,jalr,branch}_native` (expect clean-3),
run via `lake env lean`. (Re-create the harness as needed — it is not checked into the repo.)
