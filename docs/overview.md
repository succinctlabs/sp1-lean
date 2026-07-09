# SP1 verified: what is proven, and how to check it

**STATUS: SKELETON (2026-07-09).** This is the north-star overview drafted against the *proposed*
end-state architecture (`docs/proposals/2026-07-architecture-consolidation.md`). Sections marked
`[PENDING: step N]` await the corresponding migration step; everything unmarked is true of the code
today. The fully-realized target version of this document — no pending markers, completed voice —
is `docs/goal-overview.md`: **the diff between these two files is the remaining work**; as claims
become true they move from there into here verbatim. The line budget (≤400) is deliberate and
enforced — if a section cannot be written inside its budget, the corresponding consolidation is
incomplete. Delete this banner at publication.

## 0. The claim, and how to read this document

SP1 is a RISC-V zkVM: a prover claims "this program, run on these inputs, exited with this code,"
and a succinct proof convinces a verifier. This repository proves, in Lean 4 with the kernel
checking every step, that SP1's constraint system actually enforces that claim: **if the verifier
accepts, the official RISC-V specification (the Sail model), executing the committed program,
really reaches that exit.** For the SP1/Rust reader: every Lean object here names its Rust
counterpart (chip names are `MachineAir::name()`, the routing table mirrors `tracing.rs`, columns
are extracted from your constraint compiler). For the Lean/Clean reader: chips are Clean circuits,
buses are Clean channels, and the top theorem is an `Ensemble.Statement → Spec` implication whose
`Spec` is external (Sail) semantics.

Vocabulary (used consistently throughout): a **chip** is one of the 25 semantic tables (SP1's
`RiscvAir` variants); a **table** is any of the 36 ensemble members (25 chips + 11 providers);
**pull/push** are Clean's bus operations — SP1's Rust `send`s where we `pull` on the Program and
Memory buses, and the interaction lists match SP1's up to that per-channel sign flip (a LogUp
symmetry, machine-checked in `Faithful/`); an **SP1 opcode** is the 53-value field-encoded
discriminant, distinct from a RISC-V **instruction** (the Sail `ast`); an **adapter** (SP1's term)
is what the Lean code calls a reader; "**trace witness**" = the prover's matrix, "**witnessed
columns**" = circuit-generated values, "**witness generator**" = the populate function.

## 1. The theorem

[PENDING: step 7 — today the claim is split across `sp1_machine_soundness` (trail form) and
`Target.sp1_target_execution` (obligation-bundle form); the fused statement below is the target.]

```lean
theorem sp1_soundness
    (prog : GuestProgram) (pi : SP1PublicIO (ZMod p))
    (h_pi : ProgramBoundary prog pi)
    (h_stmt : (sp1Ensemble prog).Statement pi) :
    ∀ s0, SP1Boot prog s0 →
      ∃ n s_f, SailChain n s0 s_f ∧ SP1Halted prog (exitCodeOf pi) s_f
```

Read: *the ensemble for the committed guest program verifies with public values `pi`* (all
per-table AIR constraints hold and all four buses balance — everything downstream of the lookup
argument) *⟹ the LeanRV64D Sail interpreter, from any state that boots the program, reaches the
halting ECALL with the committed exit code.*

Trust base — exactly six rows, machine-gated (the audit harness asserts the theorem's axiom set is
*exactly* this; `scripts/run_audit.sh` reproduces it):

| # | Trusted | Form |
|---|---|---|
| 1 | Lean kernel + `propext` / `Classical.choice` / `Quot.sound` | axioms |
| 2 | `Lean.ofReduceBool` / `trustCompiler` (bv_decide; the conformance battery) | axioms |
| 3 | `logupGkrSound` — the lookup argument | one named axiom [PENDING: W8] |
| 4 | `sailPlatformSurface` — the LeanRV64D platform bundle (~76 axioms; RV64IM integer paths touch 4) | named list, gate-enforced [PENDING: §6 gate] |
| 5 | the Rust→Lean constraint extractor | outside Lean; byte-identical regeneration gate |
| 6 | `populate` conformance | tested (native_decide @ KoalaBear), quarantined test library |

Gap ledger (open named `sorry` lemmas, one roadmap item each — never statement hypotheses):
`sp1_row_facts_decode` (witness → typed rows; W1b) · halt obligations (W5, until the HALT chip) ·
[PENDING: regenerate this table from the audit harness at publication].

## 2. The Sail side: what "really executes" means

The reference semantics is **LeanRV64D** — the Lean translation of the official RISC-V Sail model,
consumed as an external dependency, never modified. One machine step is `try_step` (the interpreter's
own top-level step: interrupt check, fetch, decode, execute, PC commit); `SailChain n s0 s` is `n`
such steps. Nothing is bypassed: the theorem's execution chain is the interpreter everyone else runs.

`SP1Boot prog s0` [PENDING: step 7 — today spread across `IsInitialState`, `ZeroRegs`, config] says
`s0` has the program image loaded at its link addresses, PC at the entry point, registers zeroed,
and the platform configured (machine mode, interrupts off — the mode SP1 executes in). It is
satisfiable by construction: `SP1Boot.canonical prog` exhibits the loader state, so the ∀-form is
not vacuous. `SP1Halted prog exit s_f` says `s_f` sits at the halting `ECALL` with syscall id HALT
in `t0` and the exit code in `a0` — the chain stops one step before executing the ECALL itself.

The decode boundary is stated once, where it is owned: `decodedInROM` (in `Model/Semantics/`) —
"the committed program row is the decode of ROM[pc]," with the decoded instruction fixed across
configured states. For any **concrete** committed program this is a *theorem*, discharged per ROM
word by direct reduction of the real decoder (`Model/SailDecode.lean`); the symbolic ∀-word form is
one named assumption in that same file — the entire decode trust surface greps to one name.
[PENDING: step 1 — hoisted ∃I∀s form.]

The platform bundle (row 4 above): the Sail model declares ~76 platform hooks (softfloat operations,
reservation sets, terminal writes) as axioms. The theorem *statement* ranges over the full
interpreter, so it imports the bundle; the RV64IM integer execution paths this project models touch
exactly 4 of them. The full list is `sailPlatformSurface`, enumerated in
`docs/snapshots/axiom-census.txt`.

## 3. The four buses

Chips communicate over four plain Clean channels; global soundness reduces to per-key balance
(LogUp). One rule governs all four: **the channel guarantee is the posted message's *hygiene* —
what the poster's byte checks establish, provable row-locally — and the bus's global meaning is a
theorem of the engine** (§5) about every balanced trace. [PENDING: steps 4–6 — this table is the
*sole* bus mechanism only after the trace-level shadow projections retire.]

| Bus | Message (arity; SP1 kind) | Channel guarantee (row-local hygiene) | The semantic theorem (engine-proved, per balanced trace) |
|---|---|---|---|
| State | `(clk, pc)` (5; State) | clk decodability bound + pc-limb bounds | `StateTruth` at every key: the committed program's execution is at this (clk, pc) |
| Program | instruction row (16; Program) | `RowSpec` (structural decode bounds) | every fetched row is the decode of ROM[pc] |
| Memory | `(addr, time, value)` (9; Memory) | `isU64` value + timestamp bound + addr shape | value currency: a read returns the most recent write at the read's timestamp |
| Byte | `(op, a, b, c)` (4; Byte) | `ByteRowSpec` (table membership) | — (already row-local: the guarantee *is* the meaning) |

**State** is SP1's execution-threading token: each row pulls "(clk, pc)" and pushes
"(clk+8, next_pc)", and balance forces every sent state to be consumed exactly once — that balance
structure is how one sequential execution decomposes across 25 tables, and the engine's
time-ordered induction turns it back into one real execution. The per-chip obligation (§4) is
exactly "my row advances it one step". **Program** rows are pushed only by the preprocessed ROM
provider, which certifies decode by construction. **Memory** carries only hygiene on the channel;
its currency theorem never appears in the final statement. **Byte** is the root of
well-formedness: every range fact bottoms out in a preprocessed-table membership.

Sign convention (once): SP1's Rust *sends* with positive multiplicity where Clean consumers *pull*
(mult −1) on Program/Memory; the emitted interaction lists equal SP1's extracted oracle up to that
negation — checked, not assumed (§6).

## 4. One chip, end to end: Add

Every chip passes the same five gates. For `AddChip` (SP1's `add_sub` AIR):

| Gate | Artifact | What it pins |
|---|---|---|
| extract | `Extracted/AddChip.lean` (auto-generated) | the column struct + assert/interaction lists, from SP1's own constraint compiler |
| faithful | `Faithful/AddChip.lean` | the circuit's constraints ⟺ the extracted asserts; emitted interactions ≐ SP1's, all four buses |
| sound | `Proofs/Chips/AddChip/Formal.lean` | constraints ⟹ `Spec`: `toBitVec64 value = RV64.add op_c op_b`, `is_real`-gated |
| decode | via the Program pull | the row's operands are the decode of ROM[pc] |
| advance | `Proofs/Chips/AddChip/Bridge.lean` | one real `try_step` from a state matching the row produces the row's committed effect |

The chip's `main` composes the shared readers (CPUState, RTypeReader, RegisterWrite) and the add
gadget as true Clean subcircuits, returning the extracted column struct — the column layout is the
single source of truth shared with SP1. The contract every chip registers
[PENDING: step 2 — today `advance` is `Option`-typed and coexists with a legacy predicate]:

```lean
advance : is_real = 1 → chipSpec → Ready r prog s → OperandCurrency r s →
    ∃ s', SailStep s s' ∧ RowEffect prog r s s'
```

`RowEffect` is the faithful per-row effect model: the PC transition, at most one register write, at
most one contiguous memory write, everything else framed — the three orthogonal axes of the Sail
machine state. `Ready` bundles the three structural side facts (adapter passthrough, routing,
pc-limb bounds) discharged once at trace level, uniformly for all chips.

## 5. The ensemble, and how the proof feeds out to chips

`sp1Ensemble prog` [PENDING: step 7 — program-parameterization] bundles 36 tables — the 25
instruction chips plus 11 providers (8 byte/range, the program ROM, memory init/finalize) — over
the four channels, with one boundary verifier that pulls the final state and pushes the initial
state committed in the public values.

The soundness engine [PENDING: steps 3–5 — today a validated spike; production =
`Soundness/TimedGrounding.lean`] grounds every pull guarantee by one well-founded induction over
the balanced buses, in time order:

> Pop the row whose state-pull carries the minimal timestamp. Balance forces that pull to equal the
> running head of the execution (no other row can match it — every other candidate sits strictly
> later in time, so around any would-be cycle timestamps strictly increase and the cycle cannot
> close). Per-address balance forces its memory pulls to equal the live frontier — the most recent
> write to each address. Its `advance` fact then fires: one real `try_step` extends the execution,
> the frontier updates, and the row's pushes become true guarantees for whoever pulls them next.
> Repeat until no rows remain; the final boundary pull now carries `StateTruth` of the committed
> final (clk, pc) — which is the theorem's conclusion.

The per-chip interface to that induction is exactly the `advance` obligation of §4 — one generic
adapter (`stepFact_of_advance`) converts it to the engine's per-row step record, so adding a chip
never touches the capstone. The witness-decode seam (`sp1_row_facts_decode`: the committed tables
decode to typed rows whose specs hold) is the one named open lemma between the Clean `Statement`
and the engine's inputs.

## 6. Faithfulness: the circuit is SP1's circuit

Two independent anchors tie the Lean circuits to SP1's Rust, per chip:

- **Constraints.** `update_extracted.py` renders SP1's constraint compiler output into
  `Extracted/` (auto-generated, hand-editing forbidden, byte-identical regeneration checked at the
  pinned SP1 commit). `Faithful/<Chip>.lean` proves the extracted assert list holds **iff** the
  native circuit's composed spec does — logical equivalence, not resemblance.
- **Interactions.** The circuit's *emitted* channel interactions and SP1's extracted interaction
  list project to the same `(kind, table, values, signed multiplicity)` tuples — a list permutation
  per chip, all four buses, no semantic interpretation. This syntactic form already caught a real
  slot-ordering bug that the earlier semantic form masked.
  [PENDING: ∥ track — 4/24 chips today; macro-driven conversion in progress. At publication this
  line reads "all chips, full equivalence" and the exceptions table is deleted.]

## 7. Witness tests: the prover side, checked against the real prover

Soundness lives entirely in §4–§6; independently, the *honest prover* path is conformance-tested:
the circuits' own witness closures, run on event batteries dumped from SP1's real Rust prover,
reproduce SP1's `generate_trace` matrices cell for cell — including column order, padding, and the
hint-driven variant flags. These checks use `native_decide` (compiler-trusted evaluation) at SP1's
production prime and are therefore quarantined in a separate test library (`SP1CleanTest`, built by
`lake test`) that the proof library never imports; `lake build SP1Clean` is `native_decide`-free by
CI gate. [PENDING: battery completion — 10/25 chips carry full-trace anchors today.]

## 8. Boundary of the claim, and how to audit it

Modeled: the 25 Supervisor-mode RV64IM instruction chips (50 of 53 SP1 opcodes; ECALL/EBREAK/UNIMP
pending the HALT chip), single shard, the four buses, the committed program/exit boundary.
**Not modeled**: multi-shard composition, precompiles, page protection, traps, the User-mode
duplicate AIRs, and the cryptographic lookup argument itself (row 3 of the trust table).

To audit: `scripts/run_audit.sh` — re-checks the toolchain pins, the `sorry` allowlist (the gap
ledger, exactly), the `native_decide`/`skipKernelTC` gates, and regenerates the axiom census that
backs §1's trust table. The extraction currency check re-renders `Extracted/` at the pinned SP1
commit and diffs byte-for-byte. Every claim in this document is either a named theorem you can
`#print axioms`, or a named gap in the ledger.

---

*Extension (separate document, +2–3 pages): per-instruction-format semantics — one master table
(format | chips | adapter | program-bus pin | Sail ast | advance effect | quirks) + ≤20 lines per
format. [PENDING: `ChipKind.format` field + per-constructor decode equations.]*
