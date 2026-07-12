# Architecture consolidation proposal — one engine, one contract, one theorem

**Status: PROPOSAL (2026-07-09), pre-PR.** Produced by a deep audit of the `dtumad/doc-arch-work`
branch (108 commits, ~19K insertions over `main`): the semantic-channels program, the uniform
per-chip `advance` contract, and their substrate. Deliberately blunt — this is the moment to be
harsh, before anything is shared. Every recommendation carries a migration cost and, where the claim
is load-bearing, a de-risk spike (§9).

**The one-sentence thesis.** The branch proved the right *model* — channels carrying execution
semantics, one uniform per-chip Sail-step obligation — but it currently runs **two parallel
soundness architectures** (the GatedVm Eulerian trail vs. the spiked timed-grounding engine), **two
parallel bus representations** (in-circuit channels vs. `*Lookups` ℤ-shadows), and **two parallel
per-chip Sail contracts** (`sailEquiv`/`reaches_sail` vs. `advance`/`advanceReady`), plus a 384-line
fork of a Clean library file. The end-state should be **one engine, one bus representation, one
per-chip contract, one theorem** — deleting ≈4–5K LOC of scaffolding, adding ≈2–3K, and ending with
a strictly *stronger* final theorem that fits on one screen.

---

## 1. Executive summary — the end-state

- **One theorem** (§3.1): `sp1_soundness : (sp1Ensemble prog).Statement pi → ∀ s0, SP1Boot prog s0 →
  ∃ n s_f, SailChain n s0 s_f ∧ SP1Halted prog (exitCodeOf pi) s_f`. The ensemble is parameterized by
  the guest program; boot is one predicate with a canonical-loader witness; the trail, the
  `TargetObligations` bundle, and the second public-IO type all disappear from the surface. Open
  seams become named, harness-gated `sorry` lemmas (a *gap ledger*), never statement hypotheses.
- **One soundness engine** (§3.2): the timed-grounding engine (productionized from
  `Spike/Engine.lean`) grounds every channel pull-guarantee in the soundness conclusion. It
  *dominates* the Eulerian trail — the trail and the walk-lift machinery (`GatedVm/`, `WalkOf`/
  `RefinesAt`/`replayVal`/`chain_to_refines`, `ValueBound.lean`) are deleted at cutover. The multi-VM
  `VmTables` re-base (roadmap W11 path A) is **rejected**; `Soundness/StateVm.lean` is deleted now.
- **One per-chip contract** (§3.3): `advance` becomes total and mandatory; `sailEquiv`/
  `reaches_sail` and the legacy dispatcher die; `advanceReady` becomes a fixed `Ready` structure.
- **Decode is fixed at its root** (§3.4): partialize `instrToProgramRow` to the decoder image and
  hoist decode-determinism into `decodedInROM` — unblocking **all four** decoder-seam chips (Mul,
  LoadDouble, LoadX0, StoreDouble) + the 2 AluX0 opcodes, deleting the 16 `decodes*` producers, and
  placing the one residual symbolic assumption in `Model/SailDecode`, the layer that owns it.
- **Channels** (§3.5, revised): all four buses on **plain coupled Clean `Channel`s** carrying only
  row-locally provable facts (`True`/`RowSpec`/`isU64`/`ByteRowSpec`); the global truths
  (`StateTruth`, decode-of-ROM) become engine theorems *about* the balanced buses. The 384-line
  `VmChannel` clone is deleted **with no upstream dependency**, along with the 25-chip
  `ProverAssumptions` semantic threading.
- **Faithfulness endgame** (§3.6): a `faithful_syntactic` macro + bundled hypotheses cut the
  per-chip syntactic anchor from ~420 to ~100–140 LOC; the 19-chip conversion becomes ≈2.5K LOC
  (vs. ≈8K naive), after which `Interaction.toProp` and the semantic anchors are deleted repo-wide.
- **Trust base packaged** (§6): the ~76 Sail platform axioms become one named, machine-gated bundle;
  the decode assumption is stated once at its owner; the audit gate asserts the fused theorem's
  axiom set *exactly*.

Net effect: ≈ −2K LOC, a stronger theorem, and a surface that fits the 5-page `docs/overview.md`
budget (§8) — which is the acceptance test for this whole proposal.

---

## 2. Brutal audit findings

Receipts included. Ordered by severity, not politeness.

### 2.1 The product claim does not exist as a single Lean statement

`sp1_machine_soundness` (`SP1Clean/Soundness/SP1Ensemble.lean:375`) concludes
`∃ rows : List (ChipRow p), GatedExecution rows …` — a bespoke intermediate type and a bespoke
Eulerian-trail certificate **leaking into the public claim**. `sp1_target_execution`
(`Soundness/TargetVm.lean:239`) has the right conclusion but takes `TargetObligations` — four
∀-quantified seams — **as a hypothesis**; to a skeptic, `sp1_target_soundness` with
`ob : ∀ rows, TargetObligations …` reads as *"assuming the hard part, the hard part follows."* The
two are glued by a second public-IO type (`SP1TargetPublicIO` + `toLegacy`) and a bare `h_entry`
pc-limb hypothesis. Nobody — Rust dev or Lean dev — can read this surface as "SP1 is sound."

### 2.2 The semantic guarantees are consumed by no soundness engine

`StateTruth`/`ProgTruth` flow only through chip `ProverAssumptions` (the completeness side) and the
boundary verifier's `ProverAssumptions` (`SP1Ensemble.lean:137-141`). The soundness path still
concludes trail-existence via GatedVm. The 25 chips × ~30 lines of `exposedChannels`/
`exposedChannels_eq` machinery is infrastructure for an engine (semantic-channels Phase 5) that
exists only as a spike. The capstone *inherits the Sail trust base through channel types* while the
truths are not yet grounded in any conclusion — disclosed in the docs, but architecturally the worst
of both worlds until the engine lands.

### 2.3 Two parallel bus representations

The in-circuit Clean channels (`Model/Channels.lean`) vs. the hand-written trace-level `*Lookups`
shadows (`Soundness/{State,Byte,Program,Memory}Consistency.lean`, ~110KB, Memory alone 57KB),
bridged by proven-but-transitional `*Lookups_eq_emitted` lemmas. `Channels.lean:16-18` admits this
is temporary. Meanwhile `docs/bus-model.md` still documents the **pre-flip** world
(`Guarantees := True` for State/Program). A doc written today must describe two bus mechanisms and
say which one is real per property.

### 2.4 Two parallel per-chip Sail contracts and two dispatchers

Every migrated chip maintains **both** the legacy `ChipKind.sailEquiv`/`reaches_sail` and the new
`advance`/`advanceReady` (`Soundness/ChipRow.lean:36-87`), dispatched by **two** generic dispatchers
(`GatedVm/SailDispatch.lean:chipRows_step_sound` vs. `Soundness/AdvanceDispatch.lean:
chipRows_advance_sound`). Retirement is blocked on 4 decoder-seam chips — which §3.4 unblocks.
`GatedVm/Bridge.lean` (65 LOC) is already-retired residue that still compiles.

### 2.5 `advanceReady` is an unbounded escape hatch

By design it "folds a chip's own preconditions," but in practice it ranges from 1 clause (Add,
`AddChip/Bridge.lean:141`) to a 27-way `(opcode, imm_c)` disjunction (AluX0,
`AluX0Chip/Bridge.lean:235-263`) to an **unmodeled ROM-disjointness seam** (StoreByte,
`StoreByteChip/Bridge.lean:190` — `GuestProgram` has no ROM/data separation to discharge it). It
re-introduces, in hypothesis position, exactly the per-chip heterogeneity the uniform `advance`
removed from conclusion position — and it makes the capstone's `h_ready` residual an opaque
monolith.

### 2.6 The decode layer re-proves the same thing 16 times and still can't finish

`Model/Semantics/Decode.lean` (1723 LOC): 16 `instrToProgramRow_inv_<t>` inversions + 16
`decodes<T>` producers, each producer re-running the inversion **twice** (once per state) to pin a
fixed instruction via `regidx_bv_inj` ×3 + `sext{12,13,20,21}_inj` — a copy-pasted 8-line block per
family. And the pattern *provably fails* where the row doesn't pin the instruction: MULHSU's phantom
record (`{High,Unsigned,Signed}`, which computes a **different value** than the real
`{High,Signed,Unsigned}`), and the width-8 non-injective `else` — permanently blocking Mul,
LoadDouble, LoadX0, StoreDouble + 2 AluX0 opcodes (`Decode.lean:1245`, `docs/chip-standardization.md`
§7). The trusted `decodedInROM` statement (∀ state, ∃ instruction) literally *permits a phantom
decode whose semantics differ from the committed row's meaning*. The double-inversion was never
extra safety; it was an incomplete determinism proof.

### 2.7 VmChannel is a 384-line fork of a 424-line Clean file

`Model/VmChannel.lean`'s genuinely novel content is ~17 lines (the 3-field struct + `toRaw` putting
`Owed` in `RawChannel.Requirements` — a slot Clean's `RawChannel` already carries independently;
only the typed `Channel.toRaw` sugar couples it, `.lake/packages/Clean/Clean/Circuit/Channel.lean:
33-42`). The other ~300 lines re-derive Clean's emitters/`expose`/`*Value`/eval-lemma surface, and
it has already churned once under an upstream rename. It also taxes `Model/Channels.lean` with ~90
lines of per-pair `= False` distinctness boilerplate (`Channels.lean:147-205`) that exist solely
because `VmChannel.toRaw` no longer unifies with `Channel.toRaw`.

### 2.8 Dead and duplicated capstone plumbing

- `Soundness/StateVm.lean` (423 LOC): a parked spike for the multi-VM `VmTables` path this proposal
  rejects. Pure carrying cost. Delete now.
- `Soundness/ValueBound.lean`: `targetObligations_full{,_of_balance}{,_via_advance}` — a 2×2 product
  of ~30-line signatures re-threading the same obligations.
- `Fact (2^24 < p)` leaks from `MulChip.kind` through 7 downstream files, each hand-rolling a
  `local instance` for `2^17`.
- TB-10: chip `circuit` bundles embed their completeness proofs as structure fields, so the 3
  completeness `sorry`s surface in the *capstone's* `#print axioms` even though soundness never
  consumes them — the census contradicts the prose.
- `StateTruth` hardcodes `clk = init + 8*n` (`Model/Semantics/Truth.lean:47`) — known-wrong the
  moment the HALT chip lands (syscall rows advance clk by 256). A statement change to the headline
  guarantee is *scheduled to happen by surprise*.
- `RowView`/`AdapterView` (`Soundness/RowView.lean`): J/I-type readers stuff `op_a_memory` into
  absent memory slots ("harmless placeholder", `RowView.lean:66-77`); `.noWrite`/`.store` rows carry
  a semantically dead `rdWrite`. Sound (gated to multiplicity 0) but the kind of convention that
  breaks silently if a projection ever reads the wrong slot.

### 2.9 The faithfulness conversion is stalled on cost

The syntactic (`LookupAccess`-list) interaction anchors — strictly stronger than the semantic
`Interaction.toProp` compat bridge, and the thing that already caught a real bug `toProp` masked —
are done for only 4 of 24 chips, at **~420 LOC each** (`Faithful/AddChip.lean` = 419). 19 chips + 3
readers remain on `toProp`, which collapses every non-byte bus to `True`. At the current cost the
conversion is ≈8K LOC of hand-written boilerplate — that's why it stalled.

### 2.10 The good news (things the audit *cleared*)

- **Op-level Sail double-bridging does not exist.** `Proofs/Operations/` has zero Sail references
  (grep-verified); gadget specs are already pure native lemmas; Sail is confined to chip
  `Bridge.lean` + `Model/Sail*` + the decode layer. The "reduce operation bridges to native lemmas,
  chip-level bridges only" goal is **already met** — no work needed.
- **Gadget freedom is already cheap and exercised.** `Native/Readers/RegisterWrite.lean` (95 LOC,
  the split-out writer) is the template: a new gadget costs a small `FormalAssertion` + one fragment
  anchor + one `assertion` line in `main`. The coupling cost of a new chip is per-instruction-shape,
  not per-gadget.
- **The faithfulness two-level structure (op fragments + chip anchors) is compositional, not
  redundant** — chip anchors are *proved by* fragment anchors via `forall_append_pair`.
- **The Eulerian core** (`GatedVm/Chain.lean`, 114 LOC) is clean generic graph theory; the
  bespokeness that matters is the packaging around it, and it dies with the trail anyway.
- **`sp1_target_execution`'s walk induction is proved and axiom-clean**; the register/memory
  replay machinery works. The engine reuses these ideas in time coordinates — the investment was
  not wasted, it just lives in the wrong coordinate system.

---

## 3. The end-state architecture

### 3.1 One theorem

```lean
/-- A Sail state that boots the guest program: image loaded, PC at entry,
    registers zeroed, platform configured. Satisfiable by construction:
    `SP1Boot.canonical prog : SP1Boot prog (bootState prog)`. -/
def SP1Boot (prog : GuestProgram) (s0 : SailState) : Prop := …

/-- **SP1 whole-machine soundness.** If the SP1 ensemble for the committed guest
    program verifies with public values `pi`, then the official RISC-V Sail
    interpreter (LeanRV64D `try_step`), run from any state that boots `prog`,
    reaches the halting ECALL with the committed exit code. -/
theorem sp1_soundness
    (prog : GuestProgram) (pi : SP1PublicIO (ZMod p))
    (h_pi : ProgramBoundary prog pi)          -- the vkey tie: pi.pc_start = prog.pc_start, …
    (h_stmt : (sp1Ensemble prog).Statement pi) :
    ∀ s0, SP1Boot prog s0 →
      ∃ n s_f, SailChain n s0 s_f ∧ SP1Halted prog (exitCodeOf pi) s_f
```

Decisions embodied here:

1. **Fuse.** `sp1_machine_soundness` + `sp1_target_execution` become internal lemmas; the doc-cited
   theorem is the flat implication above. Open seams (today: the witness decode; until W5: halt)
   become **named `sorry` lemmas gated by the audit harness allowlist** — the existing
   `sp1_witness_decode` house pattern — never hypotheses of the statement.
2. **The program is an ensemble parameter.** `sp1Ensemble (prog : GuestProgram)`; the ROM provider
   is a preprocessed constant table (the honest model of SP1's vkey-committed program table);
   `Commit.progOf data` stays internal with a proven tie. `StateTruth`/`ProgTruth` re-key to `prog`.
3. **`SP1Boot` + canonical loader.** Folds `IsInitialState ∧ ZeroRegs ∧ SailConfigured`-residue into
   one predicate; `SP1Boot.canonical` makes the ∀-form demonstrably non-vacuous (the first attack a
   skeptical reviewer mounts, dismissed in one line).
4. **One public IO.** `SP1PublicIO` absorbs `exit_code`; `SP1TargetPublicIO`/`toLegacy` deleted; the
   `h_entry` pc-limb tie becomes a `ProgramBoundary` clause (faithful: SP1's verifier does check
   public values against the vkey).

### 3.2 One soundness engine

**Recommendation: the timed-grounding engine (productionized `Spike/Engine.lean`) is THE capstone
core; the Eulerian trail is scaffolding to delete, not maintain.**

Why the trail is genuinely dead (verified in the spike source, `Spike/Engine.lean:320-338`): layer A
pops the row with **minimal state-pull time**; per-key balance forces its pull to equal the running
head — clock-uniqueness from state balance alone, which *linearizes all rows into one chain*. Around
any cycle, times strictly increase (+clk_inc per row), so **no garbage cycle can close** — whereas
`GatedExecution.trail` only ever produced a *sub-multiset* walk, leaving closed cycles of real rows
semantically unaccounted (Clean's own `Air/Vm.lean:15-23` tolerates them). The engine's conclusion
(`∀ r ∈ rows, Grounded data r`) covers every row. The trail theorem is not replaced; it is
dominated.

Why not the multi-VM `VmTables` re-base (roadmap W11 path A): **it is packaging, not proof.**
`VmTables`' engine has no concept of *time*, so it cannot express memory currency ("read = last
write at the read timestamp"), cannot kill garbage cycles, and cannot ground `StateTruth` (its own
module doc disclaims it). Even generalized, it would deliver to the seam only what the plain
`Ensemble` already delivers (constraints + balance) plus composition lemmas SP1 — one monolithic
machine — doesn't need. FemtoCairo's acknowledged read-write-memory gap is real, but the honest
upstream contribution for it is a **timed** engine, extracted *after* SP1's is production-proven.
Consequence: delete `Soundness/StateVm.lean` (the parked spike for this path) immediately.

What `sp1_machine_soundness` concludes under the engine: `StateTruth` of the final boundary pull —
i.e. the committed program's real Sail execution spans the public boundary — which composes directly
into §3.1's conclusion. The seam swaps from `SP1WitnessDecode` (ℤ `LookupAccess` permutations) to a
simpler `sp1_row_facts_decode` (typed message multisets read off `exposedChannels`/
`interactionsWith`); the sole `sorry` moves there (it is W1b-shaped work under any architecture).

**The keystone artifact, built first:** a generic `stepFact_of_advance` adapter converting
`ChipKind.advance` (premises: configured/ROM/pc-read/operands/decode/ready; conclusion:
`SailStep ∧ RowEffect`) into the engine's `StepFact`/`FrameFact` — **one lemma, not 21 re-proofs**:
`StateTruth` supplies the configured state at the right pc; engine currency + the spike's
`regEpoch`/`valueAt_shift` epoch algebra supply the operand reads; `ProgTruth` supplies the decode;
`RowEffect` yields the pushed truths and the frame. This is what makes the cutover cheap — **spike
SP-2 (§9) proved the adapter end-to-end on the real `AddChip.kind`**: the register-axis fleet
(~18 chips) migrates via the generic lemma + ~4 per-reader-shape wiring lemmas; the memory-axis
chips ride the engine's `MemLoc` generalization (three bounded work items, §9). Until the engine
capstone is proven end-to-end on the same seam, the legacy path stays compiling but **frozen** (no
new lemmas against `GatedExecution`/`reaches_sail`/`targetObligations_*`).

Retired at cutover: `GatedVm/` (5 files, 455 LOC), the TargetVm walk machinery (`WalkOf`/
`RefinesAt`/`replayVal`/`memReplayVal`/`chain_to_refines`, ~350 LOC), `ValueBound.lean` (283),
`InstructionTrace.lean` (111), `StateVm.lean` (423, now), the `*Lookups` shadow layer (~1.7K), and
the ℤ `LookupAccess`/`InteractionProjection`/`BalanceBridge` stack (~800 → replaced by a ~200-LOC
typed-multiset bridge off Clean's `BalancedInteractions`; spike SP-4). Kept and re-anchored:
`MemoryIsU64`/`MemoryGlobal` cores (the engine's genesis frontier), `FinishedChannels` (byte),
the clk/pc bit-recombination helpers (the field→ℕ time layer, spike SP-3). Deliberately **not**
used: Clean's `Utils/OfflineMemory` — its sorted-permutation shape fights time-graded currency;
documented here to preempt the review question.

Accounting: retire ≈4.1–5.1K LOC, add ≈2.1–2.9K (engine 1.2–1.8K, adapter 0.4–0.6K, bridge 0.2K,
capstone glue 0.3K). Net ≈ **−2K LOC for a strictly stronger theorem**.

### 3.3 One per-chip contract

```lean
structure ChipKind (p : ℕ) [Fact p.Prime] [Fact (2 ^ 17 < p)] where
  name : String                    -- SP1 MachineAir::name()
  format : Format                  -- R | I | Load | S | B | U | J | Sys (drives the doc tables)
  Inputs Cols : TypeMap
  view : Inputs (ZMod p) → Cols (ZMod p) → Trace.RowView (ZMod p)
  chipSpec : Inputs (ZMod p) → Cols (ZMod p) → ProverData (ZMod p) → Prop
  advance : ∀ inp cols data prog s,          -- TOTAL: every wired chip proves it
    (view inp cols).is_real = 1 → chipSpec inp cols data →
    Ready (view inp cols) prog s → OperandCurrency (view inp cols) s →
    ∃ s', SailStep s s' ∧ RowEffect prog (view inp cols) s s'
```

- **Deleted fields**: `sailEquiv`, `reaches_sail` (with the trail), `advanceReady : … → Prop`,
  the `Option (PLift …)` wrapper (a proof inside data, dispatched by `isSome`, is un-idiomatic and
  forces the `h_migrated` coverage side-condition).
- **`Ready` is a fixed structure**, not an open `Prop`: `{passthrough (cols = main-projection),
  routing (op_a ≠ 0 / active flag / op_a = 0 for x0), alignment (pc-limb bounds not in Spec)}` —
  each a `RowView`-level predicate the dispatcher discharges once from trace construction. No
  `decode_determined` field is needed: §3.4 closes that seam at the decode layer, where it belongs.
  The StoreByte ROM-disjointness clause is replaced by a real `GuestProgram.data_disjoint_rom`
  field (it was always a model gap, not a chip precondition).
- The 25 hand-rolled `exposedChannels_eq` proofs become derived/generated (they are mechanical
  consequences of reader composition; a deriving-style tactic or metaprogram closes them).
- One shared `instance [Fact (2^24 < p)] : Fact (2^17 < p)` (in `Math/`) kills the 7-file leak;
  chips keep their honest minimal bounds.

### 3.4 Decode: fix the root, at its owner

**Decision (settled with the user): Move 1 + Move 2, with the uniqueness obligation owned by the
decode/provider layer.**

> **STATUS: Move 1 + Move 2 LANDED (2026-07-12).** Move 1 = commit `98de797d`; Move 2 = `b60366fe`
> (fold `DecodeGuards` into `Decode.lean`) · `ea5da87f` (redefine) · `5ad0bfb6` (collapse the 16
> producers, −248 LOC) · `c0d92626` (hoist evidence). All axiom-clean; `run_audit.sh` PASS. One
> deviation: the `hpin`-drop for mul/load/store is deferred to the seam-chip sub-task (needs guarded
> `inv_load'`/`inv_store'`). See `consolidation-progress.md` (2026-07-12 entry) for the full record.

**Move 1 — partialize `instrToProgramRow` to the decoder image.** The real decoder's own
sub-functions emit only canonical values (`encdec_mul_op_backwards` produces exactly 4 records;
widths ∈ {1,2,4,8}; no unsigned width-8 load in RV64). Guard the `.MUL`/`.LOAD`/`.STORE` projection
arms to return `none` off that image. On the image, the projection is injective — the phantom-MULHSU
and width-8 ambiguities vanish, unblocking all four seam chips + both AluX0 opcodes. The trusted
`decodedInROM` sentence gains, implicitly, "the decoder emitted a canonical record" — same boundary,
slightly stronger sentence, proven **free** by every concrete decode reduction.

**Move 2 — hoist determinism.**

```lean
def decodedInROM (prog : GuestProgram) (row : ProgramRow (ZMod p)) : Prop :=
  ∃ w I, prog.fetchWord (pcBitsOfRow row) = some w ∧
    (∀ s, SailConfigured s → (ext_decode w).run s = .ok I s) ∧   -- ∃ I outside ∀ s
    instrToProgramRow (rowPcVec row) I = some row
```

Given Move 1, the hoisted form is derivable (the row now pins `I` in every family), so the hoist
mostly *deletes* the 16 `decodes<T>` producers (~600 LOC of per-family double-inversion) and the 5
`sext*_inj` cross-state pinning lemmas. **Spike SP-1 (§9) proved the derivability as a theorem**
(`decodedInROM_rtype_hoist`/`_mul_hoist`, side condition free) — the Move-2 trust question is
dissolved: state-independence is a consequence of the image guards, not an added assumption.

**Ownership.** The uniqueness/determinism obligation lives where the model owns it:

- For **concrete committed programs** — the only thing the final theorem is ever instantiated at —
  it is a *theorem*, discharged per ROM word by the existing `decode_ADD_example`-style branch-skip
  reduction (`Model/SailDecode.lean`), which already proves `(ext_decode w).run s = .ok I s` for
  arbitrary configured `s` with a fixed literal `I` — exactly the ∃I∀s form.
- The **symbolic ∀-word residual** is ONE named assumption stated in `Model/SailDecode` (the file
  that documents the `encdec_backwards` intractability), never per-chip `Ready` fields, never
  capstone residuals. `grep decode_assumption` finds the entire decode trust surface.

Effects: `Decode.lean` 1723 → ~1100 LOC (16 inversions stay, three arms gain `decide`-dischargeable
image guards under the `word_width = Int` kernel discipline); `advance` coverage reaches **25/25**,
unblocking full legacy-contract retirement; per-chip decode preludes drop to 2 lines
(`obtain ⟨w, I, hfetch, hdec, hproj⟩ := hdecrom` + one inversion). `ProgramMsg`, `ProgTruth`'s
shape, and the provider's `Owed = RowSpec` stay **byte-for-byte** — the faithfulness anchors and the
interactions-permutation claim are untouched. `Advance.lean` compresses ~2700 → ~2100 honestly (the
9 x0 wrappers merge into the write family via the writesReg gate; 3 load wrappers become
width-parametric; the ladder and the 20 `execute_*_reaches` are irreducible physics — anyone
promising to halve this file is selling something). Optional third move, evaluated in SP-1: P2's
`astOfRow : ProgramRow → Option ast` single-function consolidation of the 16 inversion lemmas into
per-constructor simp equations — adopt only if it doesn't introduce a second correspondence to
maintain.

### 3.5 Channels — row-local facts on the channel, global truths in the engine

**Recommendation (revised 2026-07-09 after a user design input): channels carry only row-locally
provable facts, on plain coupled Clean `Channel`s; the global execution truths become engine
theorems *about* the balanced buses. VmChannel is deleted with no upstream dependency.**

The revision was triggered by the observation — confirmed by the audit — that **chip soundness
proofs never consume the pulled `StateTruth`** (it arrives as an ignored `_h_spull` conjunct in
all 25 chips; SP-2 confirmed the real consumer is the engine at trace level, fed by the witness
decode, not by chip pulls). Its only live uses are the boundary verifier's final-pull interface and
a 25-chip `ProverAssumptions` threading burden in which each chip's honest-prover obligation
quantifies over the *global* execution — architecturally wrong for a row-local object. The polarity
analysis:

- **The raw "swap" (semantics as push-`Owed`) does not typecheck per-message.** The interaction
  polarity itself (receive `(clk,pc)` / send `(clk+8, next_pc)`) is pinned by SP1-faithfulness; a
  push obligation is a *per-message* predicate, while the certificate a chip can locally prove
  ("one step from my pull key produces my push key + effect") is *per-row* — it binds the pull key,
  which the push message cannot name, and enriching the message breaks the interactions-permutation
  constraint. The row-level certificate already has its correct home: `ChipKind.advance`, delivered
  through the witness decode.
- **Therefore the state channel should carry no execution semantics at all.** The engine maintains
  the running head internally and *proves* each pull's truth as it fires (verified against
  `Spike/Engine.lean` — the channel's Guarantees slot was never load-bearing for the induction).
  `StateTruth` becomes the engine's grounding theorem ("every balanced trace's state keys satisfy
  it"), and `sp1Spec` states `StateTruth(final)` directly as the conclusion.

The post-consolidation channel assignment — **all four buses on plain coupled Clean `Channel`s**,
with one uniform design rule (refined 2026-07-09 after user pushback + SP-3's evidence): **the
channel guarantee is the posted message's *hygiene* — everything the poster's byte checks
establish, row-locally provable on both sides — and the bus's global meaning is the engine's
theorem.** No bus is `True`-guaranteed; no bus carries execution semantics as a type.

| Bus | Message (arity; SP1 kind) | Channel `Guarantees` (row-local hygiene) | The global semantic theorem (engine-proved) |
|---|---|---|---|
| State | `(clk, pc)` (5; State) | `StateMsgHygiene`: clk ℕ-decodability bound (pushed low limb `< 2^24 + 256`, from the pusher's own byte-checked pull) + pc-limb bounds (via the program pull's `RowSpec`) | `StateTruth` at every key: the committed program's execution is at this (clk, pc) |
| Program | instruction row (16; Program) | `RowSpec` (structural decode bounds — proven by the ROM provider, consumed by chip soundness) | decode-of-ROM at every fetched key (§3.4), from balance + the preprocessed provider, which certifies decode *by construction* |
| Memory | `(addr, time, value)` (9; Memory) | `isU64` value + **timestamp bound** (SP-3's required received fact — the writer posts its own byte-checked `clk + δ`) + addr shape | value currency (read = last write at read time) — an engine theorem, never in the final statement |
| Byte | `(op, a, b, c)` (4; Byte) | `ByteRowSpec` (table membership) | — (finished channel; the guarantee is already row-local) |

**Why the state channel is not "mere bookkeeping" under this design** (the Rust dev's reading): in
SP1 the state bus is the *execution-threading token* — each row receives `(clk, pc)`, sends
`(clk+8, next_pc)`, and LogUp balance forces every sent state to be consumed exactly once; that
balance structure IS how one sequential execution decomposes across 25 tables. SP1's Rust has no
per-message-predicate slot at all, so "hygiene-only guarantees + meaning-in-balance" is the
*faithful* translation; the engine's grounding theorem is SP1's own implicit soundness argument
made explicit, and it is a theorem *about* this channel's messages. The hygiene guarantee is not
decorative either: SP-3's read-ordering lemma consumed exactly such a per-message posted bound
(the memory-row `prev_low` fact), and carrying it on the channel lets the engine read each
message's ℕ-decodability off the bus instead of threading bounds through the induction.

What this deletes beyond the previous draft: `Model/VmChannel.lean` (384 LOC) **without any
upstream PR** — the decoupling existed only to put global truths on pulls; the ~90-line
distinctness-boilerplate tax (all four buses unify back on `Channel.toRaw`); the 25-chip
`StateTruth`/`ProgTruth` `ProverAssumptions` threading (the SC-Phase-2c/2a per-chip completeness
tax — chip prover obligations become row-local again); and the CPUState/boundary-verifier
GFC conversions' semantic conjuncts. The upstream `Owed` field idea survives only as an **optional
Clean contribution** (its Vm.lean header still concedes the row-local-provability gap) — no longer
on SP1's path. Rejected alternatives: the raw per-message swap (above); restating buses on raw
`RawChannel` (ergonomics regression); keeping `StateTruth` on the pull (dead weight in soundness,
global-execution obligations in completeness, and the trust base enters through channel *types*
before the engine exists — §2.2).

Two hygiene items ride along unchanged: prove `RowSpec_of_decodedInROM` once (so the engine's
program theorem subsumes the bounds), and restate `StateTruth`'s time clause via `timeOfStep`
**now** — the hardcoded `8 * n` breaks the moment the HALT chip (clk_inc = 256) lands.

The post-consolidation channel table — which the overview doc reproduces verbatim, and which is only
*true* once the shadow layer dies:

| Bus | Message (arity; SP1 kind) | A pull receives | A push owes | Grounded by |
|---|---|---|---|---|
| State | `(clk, pc)` (5; State) | `StateTruth` — the committed program's execution is at this (clk, pc) | `True` | the engine (balance + boundary genesis) |
| Program | instruction row (16; Program) | decode-of-ROM at this pc (§3.4) | `RowSpec` (structural bounds) | preprocessed ROM provider + balance |
| Memory | `(addr, time, value)` (9; Memory) | `isU64` — *structural by decision*; currency is an engine theorem, never on the channel | `isU64` | providers + balance |
| Byte | `(op, a, b, c)` (4; Byte) | `ByteRowSpec` (table membership) | table-row correctness | preprocessed byte/range tables (finished) |

Plus the polarity footnote: SP1's Rust *sends* where we *pull* on Program/Memory; interactions match
SP1's oracle up to per-channel multiplicity negation — a LogUp sign symmetry, FV-checked in
`Faithful/`. Two hygiene fixes ride along: prove `RowSpec_of_decodedInROM` once and drop `RowSpec`
from the Program pull-guarantee (it's redundant given the decode; it survives as the provider's
`Owed`); and restate `StateTruth`'s time clause via `timeOfStep` **now** — the hardcoded `8 * n`
breaks the headline guarantee's statement the day the HALT chip (clk_inc = 256) lands.

### 3.6 Faithfulness endgame

The landed 4-chip syntactic anchors decompose as ~60% per-column `env`-eval hypothesis boilerplate +
~35% two stereotyped simp blocks + ~5% a Perm finisher. Strategy: bundle the hypotheses (one
`h_env : eval env input = inputOfCols cols` + one witness-slot fact, per-field bindings recovered by
`ProvableStruct` projection simps) and a `faithful_syntactic` tactic macro (sibling of
`faithful_chip_assert`) taking the chip's unfold list. **Spike SP-5 (§9) measured it**: 114 LOC for
a full chip section (vs 333 production, 66% reduction), transferring to SubChip and a fresh
AddiChip conversion, at the *default* heartbeat budget — per-class estimates 115–170, 19 chips
≈ 2.2–2.8K total, with Mul's byte anchor (an 8-minute *kernel*-time list equality needing a chunked
strategy) and DivRem (no anchor exists yet) carved out as named exceptions. Then delete
`Interaction.toProp` + the semantic `*_interactions_faithful` anchors + `faithful_chip_interact`
repo-wide (verified: `toProp` has no consumer outside `Faithful/` — the combined syntactic Perm
strictly subsumes it). This track is file-disjoint from the decode/engine tracks and runs in
parallel.

---

## 4. Keep / retire / replace verdicts

| Component | LOC | Verdict | Replacement / notes | Cost | Risk |
|---|---|---|---|---|---|
| `Model/VmChannel.lean` | 384 | **Delete (no upstream needed)** | plain coupled `Channel`s per §3.5 — global truths move to engine theorems; SP-8 validates the reversion | M | low |
| `Model/Channels.lean` distinctness lemmas | ~90 | Shrink to one flavor | all four buses back on `Channel.toRaw`; per-pair rewrites stay (simp needs closed forms) | S | none |
| 25-chip `StateTruth`/`ProgTruth` ProverAssumptions threading | ~25×small | **Delete** | chip prover obligations become row-local (§3.5) | M (mech. sweep) | low |
| `Soundness/StateVm.lean` | 423 | **Delete now** | de-risked a rejected path; pure carrying cost | S | none |
| Multi-VM `VmTables` re-base (W11 path A) | 0 | **Reject** | plain `Ensemble` + engine; timed engine is the honest upstream story later | 0 | none |
| `GatedVm/` (trail, dispatch, capstone, bridge) | 455 | Retire at cutover | engine walk; `Chain.lean` optionally parked in `Math/` | S–M | low |
| `Spike/Engine.lean` | 508 | **Promote** | `Soundness/TimedGrounding.lean` (~1.2–1.8K): MemLoc keys, clk_inc-general, intra-row touches, field→ℕ time | L | med-high (spikes SP-2/3/6) |
| TargetVm walk machinery + `RowEffectDefs` replay | ~500 | Retire at cutover | `StateTruth`/engine subsume `RefinesAt`/`replayVal`; statement-layer defs (`SP1Halted`, boot) survive | M | low |
| `ValueBound.lean` (2×2 assembly defs) | 283 | **Delete** (not consolidate) | — | S | none |
| `*Lookups` shadows + `eq_emitted` bridges | ~1.7K | Retire into engine end-state | typed-multiset facts off `exposedChannels`; skip the intermediate re-pointing (two migrations) | L | med |
| ℤ bus stack (`InteractionBus`/`Projection`/`BalanceBridge`/`Recovery`) | 913 | Retire ~800 | ~200-LOC `Multiset` bridge off Clean `BalancedInteractions` (small upstream candidate: Multiset corollaries of `Air/Balance`) | M | low |
| Dual Sail contract + legacy dispatcher | ~1–2K | Retire | `advance` total; `correct_*_native` cores stay (they feed advance) | M | low |
| `advanceReady` open Prop / `Option (PLift)` | — | **Replace** | structured `Ready`; total `advance`; no decode field (owned at §3.4) | M | low |
| 16 `decodes<T>` producers + 5 `sext*_inj` | ~600 | **Delete** (Move 2) | `decodedInROM` hoist; inversions stay with image guards | M | low (SP-1) |
| `Fact (2^24)` leak | ~20 | Replace | one implication instance in `Math/` | S | none |
| `FinishedChannels`, providers, boundary verifier, `SP1Ensemble` shell | — | **Keep** | seam swap only | — | — |
| `MemoryIsU64`/`MemoryGlobal` cores | 475 | Keep, re-anchor | engine genesis frontier | M | low |
| Sail semantic layer (`Model/Sail*`, `Semantics/`, `Proofs/Sail`) | ~7K | **Keep** | domain content, not framework | — | — |
| Readers, chips, `Extracted/`, `Faithful/`, tests | — | **Keep** | the SP1-faithful surface — the point of the project | — | — |
| `Interaction.toProp` + semantic anchors | — | Delete after conversion | `faithful_syntactic` macro sweep | M (19 chips) | low (SP-5) |
| `docs/bus-model.md` | — | Mark historical | superseded by `docs/overview.md` | S | none |

What genuinely stays bespoke, each defensible to a Clean maintainer in one sentence: the Sail
semantic layer (RISC-V domain content); the timed engine (grounds circular VM guarantees via
timestamps — vocabulary Clean's channel layer lacks, upstreamable only after SP1 proves the shape);
`ChipKind`/`ChipRow`/`Coverage` (per-row semantic dispatch across 25 heterogeneous chip types is
SP1's routing problem); the SP1-column-faithful circuit surface; the boundary/provider tables (SP1's
actual protocol, in stock Clean primitives); the ~200-LOC typed-multiset balance bridge.

---

## 5. Migration plan (ordered to avoid double-migration)

Principle: fix the per-chip interface and the seam target shape **before** touching volume; freeze
the legacy path immediately; substrate work rides whenever upstream permits.

0. **Now (S):** delete `StateVm.lean`; freeze GatedVm/TargetVm-walk/`targetObligations_*` (module
   docstrings; no new lemmas); land the `Fact` implication instance; land the `timeOfStep` fix to
   `StateTruth`.
1. **Decode (M):** Moves 1+2 (SP-1-gated); land the seam-chip advances (Mul, LoadDouble, LoadX0,
   StoreDouble + AluX0 29/29 — their `op`+`hpin`-parameterized machinery is already written and
   waiting); **`advance` coverage 25/25**.
2. **Contract (M):** structured `Ready` + total `advance`; delete `sailEquiv`/`reaches_sail` +
   `SailDispatch`; rewrite `AdvanceDispatch`. (Pre-engine work that survives the engine unchanged.)
3. **Adapter (M–L):** `stepFact_of_advance`/`frameFact_of_advance` (SP-2-hardened) — the keystone.
4. **Engine (L):** productionize `TimedGrounding` (MemLoc keys, general clk_inc, intra-row ordered
   touches per SP-6, field→ℕ time per SP-3).
5. **Seam swap (L):** `sp1_row_facts_decode` replaces `sp1_witness_decode`; typed-multiset bridge
   (SP-4) replaces `BalanceBridge`. The sole `sorry` moves here — this is W1b under any architecture.
6. **Cutover (M):** new capstone conclusion; delete GatedVm, walk machinery, `ValueBound`,
   `InstructionTrace`, shadows, ℤ stack. One PR series; legacy path deleted only after the engine
   capstone is green on the same seam.
7. **Statement (M):** fused `sp1_soundness` + `SP1Boot` + canonical loader + program-parameterized
   ensemble + one `SP1PublicIO` + the axiom-set gate (§6).
∥. **Faithfulness track** (parallel throughout): SP-5 macro infra, then 19 chips in batches; delete
   `toProp` at the end.
∥. **Channel reversion track** (SP-8-gated, best folded into step 6's cutover): revert
   `stateChannel`/`programChannel` to plain coupled `Channel`s; delete `VmChannel.lean` + the
   distinctness tax + the 25-chip ProverAssumptions threading. (The upstream `Channel.Owed` PR is
   now an *optional* Clean contribution, off SP1's path — SP-7 demoted accordingly.)
Post-cutover: W5 HALT chip against the engine; vkey/program commitment into the public IO.

LOC: retire ≈4.1–5.1K, add ≈2.1–2.9K. Marginal cost of a future chip: ~450–750 LOC (from 550–900);
of a new decode shape: ~45 (from ~85 + producer).

---

## 6. Trust base & disclosures

The fused theorem's trust base, as the overview doc will state it (6 rows, machine-backed):

| # | Trusted | Form |
|---|---|---|
| 1 | Lean kernel + `propext`/`Classical.choice`/`Quot.sound` | axioms |
| 2 | `Lean.ofReduceBool`/`trustCompiler` (bv_decide; conformance battery) | axioms |
| 3 | `logupGkrSound` — the lookup argument (post-W8) | one named axiom |
| 4 | `sailPlatformSurface` — the LeanRV64D platform bundle (~76 axioms; the RV64IM integer paths touch 4) | named `List Name`, gate-enforced |
| 5 | the Rust→Lean constraint extractor | outside Lean; byte-identical regen gate |
| 6 | `populate` conformance | tested (native_decide @ KoalaBear), quarantined test lib |

Enforcement: extend `scripts/gen_axiom_probe.py` to assert `axiomsOf sp1_soundness ⊆ clean3 ∪
{oRB, tC, logupGkrSound} ∪ sailPlatformSurface` **exactly** — a machine-gated bundle can be cited as
one object; an un-gated list of 76 cannot. Fix TB-10 (close the 3 completeness sorries, or split the
soundness-only `Component` so completeness fields stop leaking into the capstone census).

**The decode disclosure** (decision 4): `decodedInROM` is the single decode trust boundary. Its
sentence includes decoder-image canonicity (Move 1) and state-independence (Move 2). For every
concrete committed program it is *discharged as a theorem* per ROM word by the branch-skip
reduction; the symbolic ∀-word residual is one named assumption in `Model/SailDecode`. Until the
seams close, the gap ledger (one table row per allowlisted `sorry`, one roadmap item each) is part
of the overview's §1 — strictly more honest than gaps living partly in a `sorry` and partly in
hypotheses of a different theorem.

---

## 7. Options deliberately kept open

1. **Dedicated S/B/U-type readers.** The design review recommends against *new reader circuits*:
   SP1's Rust has no S/B adapter columns (a new reader is a third name for the same
   `Extracted.ITypeReader` block with zero new proof power); new circuits would invalidate the 3
   landed reader syntactic anchors; post-§3.4 the format distinction arrives via the program-bus
   guarantee + one inversion, which is where it belongs; Branch and the stores are already migrated
   through `ITypeReaderImmutable`. **Kept on the table per user decision** in the weaker form worth
   evaluating during step 2: a *Spec-level format veneer* — named per-format wrappers
   (`STypeView`/`BTypeView`) over the existing extracted blocks, giving the doc and the `Format`
   field a first-class name without touching circuits, columns, or anchors. Decide when the
   `ChipKind.format` field lands; zero cost to defer.
2. **`astOfRow` consolidation** (P2's C6): fold the 16 inversion lemmas into one total
   `ProgramRow → Option ast` function + per-constructor simp equations. Evaluate inside SP-1; adopt
   only if it doesn't create a second ast↔row correspondence to maintain alongside
   `instrToProgramRow`.
3. **The optional Clean `Owed` contribution**: no longer on SP1's path (§3.5 deletes VmChannel by
   reverting to coupled channels), but Clean's Vm.lean still concedes the row-local-provability gap
   a decoupled channel would fill — worth offering upstream on its own merits if the maintainers
   want it; zero SP1 dependency either way.

---

## 7.5 Upstream currency (checked 2026-07-09)

The Clean pin (`2c20f7f0`, 2026-06-25, Lean 4.28) is **105 commits behind `main`** (clean ancestor,
no divergence), and upstream has **left Lean 4.28**: the toolchain bump to **v4.30.0** (+ mathlib
v4.30.0) merged 2026-07-06 (PR #370, with a long 4.30 proof-fix tail across Clean's gadgets and
PR #425's `elaborate_circuit` reduction improvements). The 4.28-compatible remainder of the delta
(54 commits, up to `4ac92696`, 2026-07-03) is dominated by the **Witgen IR framework** (PRs
#403/#413): `Operation.witness` now holds a deep-embedded IR instead of Lean closures (`<==` emits
IR; the closure API is renamed `*Native`; JSON exportability layer), plus one `circuit_norm`
normal-form change (`x + -1*y → x - y`).

**Disposition:**
- **Do not re-pin mid-consolidation.** The 4.28-compatible delta lands squarely on the witness
  surface this project depends on (`TraceGenTests` seeds `FlatOperation.dynamicWitnesses` with
  `main`'s witness closures; `update_extracted.py` emits the circuit witness forms) — absorbing
  that churn concurrently with the cutover doubles the moving parts.
- **Track the Lean 4.30 migration as a named strategic item** (post-cutover): staying current with
  Clean now *requires* it, and it entails coordinated toolchain bumps of the two succinctlabs Sail
  forks + lean-sail. The consolidation itself is the best preparation — plain coupled `Channel`s,
  no VmChannel, no ℤ stack, fewer bespoke layers touching Clean's API — so the migration surface
  shrinks before the jump. The longer the 4.28 pin stands, the larger the jump grows.
- **Opportunity to evaluate at re-pin time**: the Witgen IR's exportable witness representation may
  strengthen the witness-conformance story (§ tests) and reduce long-term `native_decide` reliance;
  PR #425's `elaborate_circuit` improvements bear directly on the `ElaboratedCircuit`
  field-obligation recipe this project uses.

**The succinctlabs Sail forks (checked 2026-07-09).** Both are droppable in principle — the deltas
are tiny — but their 4.28 toolchain pins are currently load-bearing (opencompl `sail-riscv-lean` +
`lean-sail` are on 4.29, Clean main on 4.30, this project on 4.28: no common toolchain exists
across unforked deps today). The facts: `succinctlabs/sail-riscv-lean @ dtumad/clean-native` = **4
changed lines in 2 files** (CLINT off, sig off, `sys_pmp_count` 16→0 — SP1 platform config) + the
toolchain pin, 65 commits behind opencompl (which regenerates the model *daily* — so any re-pin is
a proof-churn event against the symbolically-reduced generated internals, fork or no fork);
`succinctlabs/riscv-lean` = 5 toolchain/dep chores and is **ahead** of opencompl main, which is
stale on `nightly-2026-01-22`; `lean-sail` is already unforked. Disposition, riding the 4.30
migration: (a) PR the `riscv-lean` chores to opencompl → drop that fork outright; (b) for
`sail-riscv-lean`, ask opencompl for build-time platform-config parameterization in the Lean
backend's emitted output (the C backend already has runtime config; the hardcoded `def`s admit no
project-side override) — a genuine upstream improvement serving every downstream user — and until
then keep the fork as the rebase-thin 3-commit branch it already is (near-zero carrying cost).

## 8. The north-star doc (`docs/overview.md`) — outline and acceptance test

Budget ≤400 lines. Each section lists the change that makes its budget real; **writing this doc is
the acceptance test for the proposal** — if a section blows its budget, the corresponding
consolidation is incomplete. Written today the material runs ≈750+ lines (two capstones, two bus
mechanisms, two chip contracts, four consistency mechanisms).

| § | Section | Lines | Depends on |
|---|---|---|---|
| 0 | The claim + reading guide + vocabulary dictionary | 25 | — |
| 1 | The theorem (verbatim) + 6-row trust table + gap ledger | 45 | steps 6–7, §6 gate |
| 2 | Sail assumptions: LeanRV64D, `SP1Boot` + canonical loader, `SailChain`, `SP1Halted`, platform bundle | 50 | step 7 |
| 3 | The four buses: the §3.5 table + one paragraph each + polarity footnote | 50 | steps 4–6 (shadow layer dead) |
| 4 | One chip end to end (Add): extract → faithful → sound → decode → advance, `Spec` + `advance` verbatim | 60 | steps 1–2 (single contract) |
| 5 | Ensemble + proof strategy: `sp1Ensemble prog`, the engine's 3-layer induction in ~15 lines of prose, `advance` as *the* interface | 60 | steps 3–5 |
| 6 | Faithfulness: extractor + regen gate, two anchor families, sign symmetry, counts | 45 | ∥ track (counts, not exceptions) |
| 7 | Witness tests: conformance battery, native_decide quarantine, coverage | 30 | battery completion |
| 8 | Boundary + how to audit (`run_audit.sh`) | 35 | — |

The +2–3 page per-instruction-format extension is one master table (format | chips | adapter |
program-bus pin | Sail ast | advance effect | quirks) + ≤20 lines per format — table-driven only
once `ChipKind.format`, the per-constructor decode equations, and exactly-one-generic-advance-per-
format exist. Vocabulary dictionary resolves: chip vs table vs component; push/pull vs send/receive
(the sign convention, stated once); `SP1Opcode` vs Sail `ast`; reader vs adapter; the three senses
of "witness"; protocol- vs circuit-soundness/completeness.

A skeleton of this doc (with `[PENDING: step N]` markers) is drafted alongside this proposal as
`docs/overview.md`.

---

## 9. De-risk spikes

Scratch/quarantined files only; every artifact `lean_verify`-checked axiom-clean; no `native_decide`,
no `skipKernelTC`; shared-file edits reverted after evidence capture. Results get appended here.

**Tier 1 — gate the central claims:**

| # | Question answered | Effort | Gates |
|---|---|---|---|
| SP-1 | Do the `.MUL`/`.LOAD`/`.STORE` image guards survive `split`+`decide` under the `word_width = Int` kernel discipline? Does the LOAD arm truly never emit `(isU, width=8)`? Does the ∃I∀s `decodedInROM` round-trip (`decodedInROM_addRow` + `advance_of_rtype` re-proved, axiom-clean)? Is the hoist *derivable* from Move 1 (dissolving the trust delta)? Does the LoadX0 no-write-load core close? | 2–3d | step 1; §3.4 |
| SP-2 | Does generic `stepFact_of_advance` close for Add (register axis) *and* StoreWord (memory axis) from the spike's `regEpoch`/`valueAt_shift` algebra + one RAM epoch lemma? If yes, the 21-chip engine migration is free; if it needs per-chip help, the §3.2 costing changes materially. | ~1w | steps 3–4 |
| SP-3 | Can the engine's ℕ-time hypotheses (pull < push, +8/+256 increments, read-window bounds) be derived from in-field clk columns + byte-bus range facts (no wraparound), for one Add row and one syscall-shaped row? The biggest seam unknown. | 3–5d | step 5 |

**Tier 2 — inform costing:**

| # | Question | Effort |
|---|---|---|
| SP-4 | Typed-multiset balance (`init ::ₘ pushes = fin ::ₘ pulls` per key) from Clean `BalancedInteractions` + {−1,0,1} mults, on a 2-table toy ensemble — confirms the ℤ stack can go | 2–3d |
| SP-5 | `faithful_syntactic` macro derives SubChip's 4 anchors from bundled hypotheses — measure LOC **and heartbeats** | 2–3d |
| SP-6 | Intra-row same-location touches (rs1 = rs2, op_a = op_b): does an ordered micro-time touch list preserve the layer-B induction? (the spike's `locs_nodup` excludes real traces) | ~1w |
| SP-7 | *(demoted — optional Clean contribution, off SP1's path per §3.5)* upstream `Owed` dry-run | 2d |
| SP-8 | Channel reversion dry-run (§3.5): restate `stateChannel` as a plain coupled `Channel` with the hygiene guarantee (clk decodability + pc-limb bounds — check both are dischargeable in 2 representative chips' soundness from their byte/program pulls) + delete the StateTruth ProverAssumptions conjunct; confirm soundness/completeness re-close and the capstone interface restates as the engine conclusion — measures the 25-chip sweep + VmChannel-deletion cost | 2–3d |

### Spike results

**SP-1 (2026-07-09): PASSED — all four questions YES, machine-checked, axiom-clean.** Scratch
evidence: `SpikeDecodeGuards.lean` (scratchpad; elaborates 0 errors / 0 warnings under
`lake env lean`).

1. **Image guards work.** `mulOpCanonical` / `loadWidthOK` / `storeWidthOK` guards land;
   `instrToProgramRow_inv_mul'` proved **without `hpin`** via a 64-case `mulOp_canonical_inj`
   (`cases ×6 <;> first | rfl | absurd … (by decide)`); both previously-blocked corollaries derived
   (`_inv_mulhsu` — the Phase-4 Mul blocker — and `_inv_mul_low`). No kernel recursion on the MUL
   path; the `word_width = Int` trap avoided by keeping guard discharges in the
   `beq_self_eq_true`/`if_neg (by decide)` style (never `decide` on a whole `loadOpcode` literal).
2. **No LDU.** The single `.LOAD`-constructing decoder arm (`InstsEnd.lean:904-968`) is gated by
   `valid_load_encdec width is_unsigned` (width < 8 any sign; width 8 signed only — no LDU arm
   exists); `valid_load_encdec 8 true = false` by `decide`. `loadOpcode_inj_on_valid` +
   `storeOpcode_inj_on_valid` + the previously-"impossible" `storeOpcode_pin_eight` (SD) all proved
   axiom-clean.
3. **∃I∀s round-trip.** `decodedInROM'` defined; the concrete anchor `decodedInROM'_addRow`
   re-proved with the witness hoisting **verbatim** (decode reductions are state-independent
   literals); consumption producers collapse to ~4 lines each, using each inversion **once** —
   the ~20-line double-inversion + `regidx_bv_inj` pinning block vanishes from all 16 families,
   and the `s0/hs0` parameters disappear from every advance adapter's prelude. Axiom set identical
   to production `decodesRType` (the one Sail constant is inherited from `ext_decode` in the
   statement).
4. **The hoist is DERIVABLE from Move 1** (per-family): `decodedInROM_rtype_hoist` and
   `decodedInROM_mul_hoist` proved, with the one side condition `∃ s, SailConfigured s` available
   unconditionally (2-line corollary of `isInitialState_nonvacuous`). **The Move-2 trust delta
   dissolves**: determinism is a theorem given the image guards, not an added assumption — the
   production provider should certify the ∃I∀s form directly (sidestepping the 16-family hoist
   sweep), and the §6 disclosure simplifies accordingly.
5. **Bonus (LoadX0):** `execute_LOAD_reaches_width1`'s conclusion already carries the `rd = 0#5`
   branch in the exact shape `advance_alu_x0_core.hexec` wants; the only gap is a memory-frame
   antecedent the core already establishes internally but doesn't pass through — a ~5-line variant
   core (`advance_load_x0_core`), no new `wX_bits` machinery.

Production notes from the spike: inline the guards into the three projection arms (keep the
`if guard then <existing record> else none` arm shape so the 16 `inv_*` split-proofs need only a
per-guarded-arm tweak); the `hpin` parameters and their `storeOpcode_pin_*` feeders become
deletable; StoreDouble/LD become reachable. **Consequence for §3.4 and §6: adopted — Move 1+2
validated with zero design deviation; the decode trust sentence reduces to the image-canonicity
guards (Move 1), with state-independence a per-family theorem.**

**SP-2 (2026-07-09): PASSED (CONDITIONAL YES) — the generic adapter is fully PROVED, not just
stated, and instantiated end-to-end on the real `AddChip.kind`.** Scratch evidence:
`sp2_stepfact_of_advance.lean` (scratchpad, 499 lines, elaborates clean; every theorem
`#print axioms`-checked — no sorryAx, no ofReduceBool; the Sail-touching decls carry exactly the
platform base `sp1_machine_soundness` already has).

- `stepFact_of_advance` + `frameFact_of_advance` + the dispatcher-shaped `engineFacts_of_kind` all
  close **generically** — all seven register-axis crux steps (StateTruth → chain state; currency →
  `ValueOperandsBound` via the epoch algebra; fire advance; chain extension; push StateTruth; new
  `ValueAt` at t+4; FrameFact both `writesReg` cases). `addRow_engineFacts` runs a genuine Add row
  through the pipeline with `hmig := rfl` — zero Add-specific Sail reasoning.
- **The one statement-design discovery**: the adapter needs a per-row `RowWiring` structure (11
  fields, message↔view correspondence, mostly `rfl`/bound extractions) including a `write_push`
  field — *the op_a write push must be present in the row's push multiset* — a
  completeness-of-emission fact the balance layer doesn't force. Wiring is **per-reader-shape, not
  per-chip**: `rowWiring_rtype` proved (~100 lines) purely from in-circuit numeric bounds
  (`[propext, Classical.choice, Quot.sound]` exactly); ~4 shape lemmas cover the register-axis fleet.
- **Refined costing of the "21 chips free" claim**: ~18 register-axis chips migrate via
  `engineFacts_of_kind` + the 4 shape lemmas + per-chip extraction of bounds their `Spec` already
  contains (hours each, mechanical). The memory-axis chips (loads/stores) wait on three bounded
  items: a `RamWriteReassembly` byte→word bookkeeping lemma (~60–120 lines, no Sail content —
  the RAM epoch lemmas themselves were proved in this spike, ~25 lines), pinning RAM read
  micro-times at δ = 0 (the register read-window convention doesn't transfer), and generalizing
  the engine's `BitVec 5` keys to `MemLoc` (mechanical, whole-file, 1–2 sessions).
- Known residuals unchanged (no new debt): `h_migrated`/`h_decode`/`h_ready` are the same three
  named residuals the existing `AdvanceDispatch` carries; `Fact (2^24 < p)` is needed for field→ℕ
  time decoding (already required by the TargetVm dispatcher); the engine's current scope
  restrictions (register-only pulls, `locs_nodup` — same-register rows like `add x3, x3, x4` are
  excluded by the *engine's* `RowOK`, not the adapter; SP-6's question).

**Consequence for §3.2: adopted with one refinement** — step 3's adapter is validated and cheap;
step 4 (production engine) must include the `MemLoc` key generalization + `RamWriteReassembly` +
the δ = 0 RAM read convention as named work items, and the loads/stores migrate in step 4, not
step 3.

**SP-3 (2026-07-09): PASSED (YES with one named static field bound) — the engine's ℕ-time
hypotheses are derivable from circuit facts.** Scratch evidence: `SP3_TimeExtraction.lean`
(scratchpad; 11 declarations, 0 errors, all axiom sets ⊆ `[propext, Classical.choice, Quot.sound]`
— Sail-free statements).

- **The +8 fact is fully row-local**: `timeNat push = timeNat pull + 8` (and the +256 syscall
  variant) proved from CPUState's two byte-bus facts alone (the 13-bit *shifted* Range on
  `(clk_0_16 − 1)·8⁻¹` — which pins `clk_0_16 ≡ 1 (mod 8)` — plus the U8Range on `clk_16_24`),
  consumed straight off the production `Readers.CPUState.Spec`. **No carry witnesses, no
  execution-length bound, no canonicity constraints**: the danger is field wrap, not limb wrap —
  the push low limb may legitimately cross `2^24` and `clkNat`'s non-canonical `hi·2^24 + lo`
  decoding absorbs it. (Side observation: a crossed-over push can never match a successor's
  byte-checked pull — a trace-*completeness* question, not an engine soundness gap.)
- **The named cost**: the standing `Fact (2^17 < p)` is insufficient (`clk_16_24 · 65536` alone
  wraps a 2^17 field). The lemmas need `2^24 + 256 < p` (state axis) / `2^25 + 2^17 < p` (memory
  axis) — satisfied with huge margin by BabyBear/KoalaBear, precedented by Mul's existing
  `Fact (2^24 < p)`. Fold into the §3.3 shared-instance cleanup: the machine level standardizes on
  one `Fact (2^25 < p)`-class bound.
- **The memory read-ordering fact lands exactly on the engine's interface**:
  `RegisterAccessTimestamp`'s byte-checked `(clk − prev − 1)` decomposition yields
  `clkNat prev < clkNat clk` = the spike engine's `TouchOK.pull_before`, verbatim — with one
  per-message received bound (`prev_low.val < 2^24 + 8`, posted by the writer as its own
  byte-checked clock) that the engine threads through the memory channel; the intra-row `+δ`
  micro-time bridge is also proved.

**Consequence for §3.2/§5: adopted** — the field→ℕ seam (step 5's typed-multiset bridge inputs) is
validated; add the `2^25`-class field bound to the step-0 `Fact` instance cleanup and the
`prev_low` received bound to the engine's memory-channel threading (step 4).

**SP-4 (2026-07-09): PASSED — the ℤ stack's replacement is a ~230-LOC typed-multiset bridge, proved
sorry-free over Clean's REAL types.** Scratch evidence: `SP4_MultisetBalance.lean` (scratchpad, 326
lines incl. docs, 0 errors; all six theorems `[propext, Classical.choice, Quot.sound]` exactly).

- `multiset_balance_of_balancedInteractions`: from Clean's `BalancedInteractions` (whose
  length-vs-char side condition is carried *inside* it — no extra count hypothesis downstream) +
  mults ∈ {−1,0,1} (the same input the existing ℤ bridge already requires) + `(1:F) ≠ −1` (genuine
  — char-2 double-counts; free at SP1's field from `Fact (2^17 < p)`), conclude
  `pushMsgs = pullMsgs` as `Multiset` equality. The boundary variant
  (`init ::ₘ pushes = fin ::ₘ pulls`) is pure list algebra on top.
- **Three reality-check fits, all sorry-free**: `ensemble_channel_multiset_balance` against Clean's
  real `Ensemble.Statement`/`BalancedChannels`; `typed_multiset_balance` recovering typed
  `Message F` multisets (via `fromElements_toElements` injectivity) in **exactly the engine's
  `h_sbal` shape** (`Spike/Engine.lean:303-305`); and the SP1-realistic gated variant
  (`pushedIfValue`/`pulledIfValue` under binary `is_real`, concluding over the enabled sublists).
- Discovered simplification: the toy abstraction was unnecessary — the lemma proves directly over
  `Interaction F`, so there is no abstraction seam to maintain. Remaining production wiring (not
  blockers): normalize real per-channel flatMap lists via Clean's own `balancedInteractions_of_perm`;
  discharge `h_bin` per chip from `is_real` booleanness (existing input); a one-liner key-indexed
  filter split for the per-register `h_mbal`.

**Consequence for §3.2/§4: adopted** — the `InteractionBus`/`InteractionProjection`/`BalanceBridge`
ℤ stack (~800 LOC) retires as planned; the bridge is simpler than estimated (no `signedVal`/
`LookupKey`/`Int` divisibility machinery) and lands directly on the engine's input shape with no
intermediate ℤ-balance step.

**SP-5 (2026-07-09): PASSED with measured numbers — ~420 → 114 LOC/chip is real for the ALU class;
REVISED to ~115–170 by class; two named exceptions.** Scratch evidence: `Probe1–11` +
timing/axiom controls (scratchpad); all sorryAx-free, axiom sets identical to production.

- **Hypothesis bundling proved**: the 26-hypothesis Memory theorem collapses to 2 (`h_env : eval env
  input = ⟨cols.is_real, cols.state, cols.adapter⟩` + one witness-slot fact); a derivability theorem
  shows every production per-column hypothesis falls out of the bundle via `provable_struct_simp` +
  two 5-line `vecN_eq_iff` infra lemmas. (Dead-ends documented: `mk.injEq` stalls on projection
  RHSs; the split must run before the kernel `have`s.)
- **Macro prototype works and transfers**: four `faithful_syntactic_<bus>` macros (~130 lines
  one-time infra, next to the existing `faithful_chip_*`); full SubChip section (all 4 buses +
  combined) = **114 LOC vs production 333**; a FRESH AddiChip (I-type) conversion passed with one
  1-line Perm-finisher addition — the predicted per-adapter-class cost. A reader-class keyword
  would drop ~48 lines of repeated unfold lists → ~80 LOC/chip (obvious follow-up).
- **The timeout risk is dead**: every bundled proof passes at the default 200K heartbeats
  (production's 4M bumps are precautionary here); macro form ~1.7× slower per theorem — seconds,
  not minutes.
- **Sweep estimate by class**: I-type/no-write ALU ~115 (0.5–1 d); multi-op flag ~120–140;
  control-flow ~120–150 (~1 d); loads/stores ~130–160 (1–1.5 d); shifts ~140–170 (measure the
  byte-pull kernel cost first). **Exceptions**: **Mul** — its dormant op-level byte anchor costs
  ~8 min of KERNEL time on a 26-element list equality (kernel cost, untouched by bundling); needs a
  chunked list-equality strategy (per-block closes composed by `congr`) — separate engineering.
  **DivRem** — no Faithful anchor exists at all (fragment anchors must be built first; expect
  Mul-class byte walls; 1–2 weeks or keep deferred).
- Measurement correction to §3.6's decomposition claim: hypothesis plumbing is ~36% (not 60%),
  stereotyped proofs ~32%, Perm tails ~1%, statements/docs the rest — direction right, magnitudes
  off; the conclusion (fully mechanizable) holds.

**Consequence for §3.6: adopted with revised numbers** — 19-chip sweep ≈ 2.2–2.8K LOC (per-class
115–170), Mul-byte + DivRem carved out as named exceptions with their own strategies; `toProp`
deletion still lands at the end of the sweep for the 17 macro-able chips, with Mul/DivRem's byte
anchors as the last two items.

---

## Appendix A — pain-point → resolution index

Every pain point named in the audit request, with its disposition:

| Pain point | Resolution |
|---|---|
| Bespoke VmChannel vs RawChannel | §3.5: upstream `Owed`; veneer = fallback (§4 row 1) |
| Bespoke machinery generally | §4 verdict table; net −2K LOC |
| Channel semantics could be stronger | §3.2: the engine grounds `StateTruth`/`ProgTruth` in the *soundness conclusion* (today: completeness-side only); §3.5 table |
| Chip unification / iterative accretion | §3.3: one total contract, structured `Ready`, no legacy fields |
| Top-level statement legible to both audiences | §3.1 + §8 |
| Abstracting Sail details out of readers / decode pain | §3.4: chips consume a pinned instruction in 2 lines; format lives in decode inversion + per-format cores |
| Reader types vs Sail instruction types | §3.4 + §7.1 (`Format` field; S/B/U evaluation kept open) |
| RowView reconsideration | keep (typed-sum redesign rejected — heterogeneous traces need one row type; the bus/refinement split already exists inside the struct); document the placeholder conventions (§2.8) |
| Gadget freedom / op bridges → native lemmas | **already met** (§2.10); `RegisterWrite` is the gadget template |
| Columns match SP1 / asserts equivalent / interactions permutation | preserved byte-for-byte throughout (§3.4, §3.6) |
| Faithfulness / interaction equivalence | §3.6 macro endgame; `toProp` deleted |
| Witness tests | unchanged, quarantined; §8 row 7 |
| Fishy/unnatural inventory | §2, receipts included |
