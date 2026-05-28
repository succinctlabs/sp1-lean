# SP1Clean — three-track parallel work split (overnight sessions)

This doc partitions the open SP1Clean verification work into **three file-disjoint, logically
decoupled tracks** that three machines can run in parallel overnight. It is derived from
`CLEAN_VERIFICATION_STATUS.md` (the status of record) and exists to coordinate parallel effort —
who owns which files, what to attack first, and where the tracks join back up later.

## Context

`CLEAN_VERIFICATION_STATUS.md` (snapshot 2026-05-28) records: 0 axioms, ~82 genuine `sorry`s across
~32 files, 6 chips fully closed and axiom-clean. Its central new finding (§4) is that
**"FormalAssertion-complete" ≠ "actually complete"** for chips with free combinatorial witnesses
(Mul, Shift{L,R}, DivRem, Lt, Bitwise): their real completeness *is* the witness-generation problem,
currently routed around by weakening the Spec to a structural `AssertionGated.Spec` form. The doc
names three frontiers, which become the three tracks here:

1. **Witness generation** (§4) — boundary-A operation backward lemmas + the witnessed `FormalCircuit`
   pilot, sitting under the combinatorial ALU chips.
2. **Non-ALU chips** (control + memory) and the open questions about how to model them.
3. **Final aggregation** (§3) — the trace soundness chain, reframed *in light of §4* (the
   conditional trace theorem → unconditional liveness via a Lean reference generator).

**Verified decoupling (the reason this parallelizes).** The three tracks are file-disjoint with
**zero logical coupling for overnight progress**:

- Heavy ALU chips close *structurally* via the proven `LtChip`/`AddwChip` `AssertionGated.Spec`
  recipe. They import the operation modules for *types and forward specs only* — **not** the
  backward `iff_sp1_full.mpr` witness lemmas. So chip structural closure does **not** wait on
  witness generation.
- Control/memory chips compose only already-closed ops (`AddOp`, `AddrAddOp`, `LtSignedOp` —
  `LtSignedOp.assertionGated` already landed). No ALU or witness-gen imports.
- `trace_soundness_aggregateMemory` / `trace_soundness_with_boundary`
  (`SP1Clean/Soundness/TraceSoundness.lean:65,90`) are **already proven conditionally** (sorry-free).
  The Soundness sorries are per-chip `memoryAccessesValid_of_spec_*` / `cpuStateSpec_of_spec_*`
  lemmas that take the chip `Spec` as a *hypothesis* — they need each chip's `ChipRow`/`Spec`
  *structure* (which exists today), never the chip's closed Circuit proof.

The **future join points** (post-overnight, not blockers): Track 1's boundary-A lemmas unlock
Track 3's `genRow` constructive completeness for combinatorial chips and the chips' *actual*
completeness; Track 1+2 chip closures eventually discharge Track 3's `h_specs` (currently assumed).

> Operational rule (CLAUDE.md): "passing" = **0 errors AND 0 warnings**; `sorry`s register as
> warnings. Closure checks use `#print axioms` via `lake env lean` (the `lean_verify` MCP returns
> empty here — missing ripgrep — do **not** trust its `[]`). Build budget: ≤2–3 concurrent `lake`
> builds; `ps -ef | grep -E "lake|lean" | grep -v lsp` before spawning; heavy chips (DivRem/Mul)
> are 17–40 min / 5–15 GB — extract the proof under edit into a helper file importing
> `…/Constraints.lean` to iterate in 3–4 min.

---

## Track 1 — Witness generation + combinatorial-ALU closure (the §4 frontier)

**Owns (file-disjoint):**
`SP1Operations/Operation/MulOperation/MulOperation.lean`,
`SP1Operations/Operation/BitwiseU16Operation/BitwiseU16Operation.lean`,
`SP1Operations/Compare/LtOperationSigned/LtOperationSigned.lean`,
`SP1Clean/Operations/*`, and the combinatorial ALU chip subtrees
`SP1Clean/Chips/ALU/{MulChip,ShiftLeftChip,ShiftRightChip,DivRemChip,UTypeChip}/*` +
`SP1Clean/Chips/ALU/BitwiseChip/SailBridge.lean`.

This track has **two work-streams**; a single machine should pick by strength and burn both as time
allows. Stream A burns sorry-count mechanically; Stream B is the genuinely novel frontier.

### Stream A — structural chip closure (mechanical, high sorry-burn)

Apply the **closed `LtChip` recipe** (`SP1Clean/Chips/ALU/LtChip/Circuit.lean` — composes
`<SubOp>.assertionGated`, reader/CPU `Gated.assertion`, selector-binarity gates; completeness closes
via `subcircuit_specs_of_formalSpec` unbundling, **not** `iff_sp1_full.mpr`). The per-chip sorries
are all `allHold_iff_structural` / `formalSpec_of_subcircuit_specs` / `soundness` / `completeness`
plus mirrored `Aggregate`/`Multiplicity` copies.

Recommended order (light → heavy build cost):
1. **ShiftLeft** then **ShiftRight** — shift is inline (no separate Operation module); sorries at
   `…/ShiftLeftChip/Circuit.lean:79,83`, `Lemmas.lean:28,34`, `Aggregate.lean`, `Multiplicity/*`,
   `SailBridge.lean`. Lightest builds; close one end-to-end, then clone to the sibling.
2. **UType** (`…/UTypeChip/Circuit.lean:125,137`) + **Bitwise SailBridge**
   (`…/BitwiseChip/SailBridge.lean`) — mechanical envelope reshapes (mirror UType's documented
   pattern); quick wins.
3. **Mul** (`…/MulChip/{Circuit.lean:84,90,94, Lemmas.lean:31,38, Aggregate.lean:573,579,583,
   Multiplicity/*}`) — composes `MulOperation` *forward* specs only.
4. **DivRem** last (heaviest build; composes Mul/IsZeroWord/Add) — `…/DivRemChip/{Circuit,Lemmas}`.

### Stream B — boundary-A witness construction (deep, the real §4 work)

Order smallest → hardest:
1. **Complete the witnessed pilot** `SP1Clean/Operations/BitwiseU16OperationWitnessed.lean` — close
   the 2 real sorries: `soundness` (~line 150) and `completeness` (~line 164). It's an island
   (validated skeleton, `Inputs := {b,cc,opcode}`, `localLength := 16`, 8 `ByteOpcodeTable` lookups).
   Templates: `Clean/Gadgets/Xor/Xor64.lean` (from-scratch `FormalCircuit`),
   `SP1Clean/Operations/IsZeroOperation.lean:38` (proof shape), and `AddOperation.spec_inv`'s ZMod
   byte-eval technique (`(b[j]−b_low[j])·256⁻¹ = b[j].val/256` via `Nat.div_add_mod`). This is the
   reference witness-gen implementation that the chip-propagation step will later consume.
2. `BitwiseU16Operation.iff_sp1_full.mpr` (`…/BitwiseU16Operation.lean:536`, ~150–300 LoC byte-witness).
3. `LtOperationSigned.iff_sp1_full.mpr` (`…/LtOperationSigned.lean:529`, ~300–500 LoC; reconstruct
   `comparison_limbs`/`u16_flags`/`not_eq_inv`/msb witnesses).
4. `MulOperation.iff_sp1_full.mpr` (`…/MulOperation.lean:42`, ~500–1000 LoC, 16-limb carry+product
   chain, needs `Fact (2^24 < p)`) — hardest; do last.
5. Cluster mop-up: `SP1Clean/Operations/{IsZeroWordOperation,IsEqualWordOperation,U16CompareOperation,
   MulOperation}.lean` — mechanical wrappers that reduce to the above. (`LtOperationSigned.lean:288`
   is a doc-comment, not an open goal.)

**Overnight target:** close ShiftLeft+ShiftRight structurally (Stream A) **and/or** finish the
Bitwise witnessed pilot (Stream B) — either is a clean, citable deliverable.

**Build note:** editing `SP1Operations/*` forces heavy downstream rebuilds — when iterating Stream B,
build `SP1Operations` targets, not full chips. Keep DivRem/Mul builds to the helper-file workflow.

---

## Track 2 — Non-ALU chips: control + memory (modeling)

**Owns (file-disjoint):** `SP1Clean/Chips/Control/{JalChip,BranchChip,JalrChip}/*`,
`SP1Clean/Chips/Memory/*`. Self-contained: uses `AddOp`/`AddrAddOp`/`LtSignedOp` (all closed) and the
gated readers; no ALU or witness-gen imports.

Recommended order:
1. **Jal** (quick, mechanical — mirrors UType envelope reshape). Close `Circuit.lean:131` (soundness),
   `Circuit.lean:140` (completeness), `Lemmas.lean:119` (`allHold_iff_structural`). `SailBridge.lean`
   already proven; sub-ops (`CPUState.Gated`, two `AddOp`, `JTypeReader.Gated`, `byteOpcodeGated`) all
   closed.
2. **Branch** — close the 4 sorries (`Multiplicity/Circuit.lean:281,285` + 2). Core blocker: prove
   `is_blt + is_bge ∈ {0,1}` for `LtSignedOp.AssertionGated.Assumptions`. Recipe (≈50–100 LoC, field
   characteristic): `(is_blt+is_bge)·(is_blt+is_bge−1) = 2·is_blt·is_bge` → reduce to `is_blt·is_bge=0`
   → case-bash; the hard `is_blt=is_bge=1` case forces `sum∈{2..6}` (ℕ) and `k(k−1)≠0` in `ZMod p`
   under `Fact (2^17 < p)`. Two refactor alternatives that avoid the case-bash are documented inline
   (use `is_real·is_signed` as the U16MSB sub-multiplicity, or emit an extra chip-level binarity gate).
3. **Memory — LoadByteChip** (`SP1Clean/Chips/Memory/LoadByteChip.lean:491`): close the 1 soundness/
   completeness sorry as the **canonical memory-access-routing pilot** (`AddrAddOp` + program-bus +
   byte lookups + `LoadMemoryAccessGated` contract-marker). Then propagate the pattern to the width
   variants (LoadHalf/Word/Double, Store*, LoadX0 — already follow this template).
4. **MemoryGlobalChip** (`MemoryGlobalChip.lean`, 4 sorries) — lower priority (boundary chip, deeper
   modeling): Phase-4.5 expansion of the address-monotonicity `LtUnsignedOp` subcircuit (the current
   `lt_cols : Vector T 6` is missing 2 `comparison_limbs` fields), IsZero arms, and range checks.

**Open modeling questions to resolve or explicitly document this track (the "how to model them"
part):**
- **Jalr** — `Multiplicity/Circuit.lean` is already **closed (0 sorries)**, but there is **no
  `SailBridge.lean`** and only an aggregate-only baseline. Decide the modeling: add
  `JalrChip/SailBridge.lean` reusing `SP1Chips.Jalr.*correct_*`, and/or downstream the `Aggregate`
  proof into the newer Multiplicity form. This is the cleanest novel deliverable on this track.
- **Branch** — how the six-way selector encoding composes with the signed-vs-unsigned `LtSignedOp`
  multiplicity (`is_signed = is_blt + is_bge`).
- **Memory timestamps** — `LoadMemoryAccessGated`'s clock-page agreement and 65536-base timestamp
  decomposition currently sit in Assumptions (Phase-1 contract-marker). Open: do `flag`/`diff`
  witnesses follow constructively from prior-access state, or need an external generator (Boundary B)?

**Overnight target:** Jal fully closed + Branch closed (or its case-bash alternative landed) + a
decision/scaffold for the Jalr SailBridge.

---

## Track 3 — Final aggregation / soundness end-to-end (greenfield-first, §4 reframing)

**Owns (file-disjoint):** `SP1Clean/Soundness/*`, `SP1Clean/SP1Lookup.lean`, and a **new**
`Sail.execute_trace` executor + `genRow` reference generator (location: a new file under
`SP1Clean/Soundness/`, e.g. `ExecuteTrace.lean`). Imports chip `Circuit`/`Aggregate` files for
*types only*. Lightest builds in the repo (Soundness rebuilds ~3 s once chip oleans are cached).

Lead with the greenfield §4 reframing, then close the sorries to feed it.

1. **`execute_trace` executor (~50 LoC, greenfield — none exists today).** Recursive Sail executor
   over `rows`, lifting each chip's `SP1Chips.*.correct_*` to the clean side and threading the
   per-instruction `SailM` step. `ChipRow` is defined at `MemoryConsistency.lean:82–114` (24
   constructors); `ChipRow.Spec` at `:582–662` (a definition, not a sorry).
2. **Reference generator `genRow : InstrContext → ChipRow` (greenfield).** This *is* §4-step-2's
   trace-level witness generator. Define `InstrContext`; prove `ChipRow.Spec (genRow ctx)` and the
   trace-shape bundles (`TraceClkValid` / `TraceStateValid`) for valid contexts — these are the
   hypotheses the conditional aggregator already assumes.
3. **Unconditional theorem (scaffold).** Feed `genRow`'s constructive discharge into
   `trace_soundness_with_boundary` (`TraceSoundness.lean:90`, already proven conditionally) to state
   `∃ s_final, Sail.execute_trace s₀ rows.length = some s_final` matching the bus history.
   **In light of §4:** for chips with no free witnesses (Add/Addi/Sub) this closes *now*; for
   combinatorial chips (Mul/Shift/DivRem/Bitwise/Lt) `genRow`'s row construction stays **conditional
   on Track 1's boundary-A lemmas** — mark those rows with a clearly-named hypothesis (the explicit
   join point) rather than a `sorry`, and **document the SP1 Rust generator as trusted (Boundary B
   open)**, per §4's recommended interim stance.
4. **Close the 15 Soundness sorries** (recipe-driven Gated-unwinding) to feed the above:
   - `MemoryConsistency.lean` — 6 substantive `memoryAccessesValid_of_spec_{bitwise:776, lt:786,
     mul:886, shiftLeft:896, shiftRight:904, divRem:914}` (extract operand accesses from
     `<Reader>.Gated.Assertion.Spec`). The `add/sub/addw/store*/load*` variants are already proven
     (vacuous `simp`) — leave them.
   - `MemoryConsistencyClock.lean` — 6 substantive `cpuStateSpec_of_spec_{bitwise:194, divRem:209,
     lt:271, mul:280, shiftLeft:287, shiftRight:293}` (extract `CPUState.cpuStateSpec` from
     `CPUState.Gated.Assertion.Spec` via `_iff_sp1` + `is_real = 1`).
   - `SP1Lookup.lean:62` is a **doc-comment**, not an open goal — the main theorem is proven; no work.

`StateConsistency.lean` and `IsRealBinary.lean` are already sorry-free.

**Overnight target:** `execute_trace` + `genRow` + the unconditional-liveness theorem scaffold landed
(conditional on the named Track-1 join hypothesis for combinatorial chips), with as many of the 15
Gated-unwinding sorries closed as time allows.

---

## Cross-track coordination

- **No git conflicts:** the three file sets above are disjoint. Each machine works its own subtree
  (its own branch, merged later).
- **No overnight blocking:** verified — see Context. The only dependencies (Track 1 boundary-A →
  Track 3 combinatorial-chip `genRow`; Track 1/2 chip closures → Track 3 `h_specs`) are *future*
  joins; Track 3 carries them as named hypotheses tonight, not `sorry`s.
- **Build budget is shared if these run on one host** — they should run on *separate* machines.
  If sharing: Track 1 (DivRem/Mul) is the build hog; Track 3 is nearly free; gate Track 1's heavy
  builds behind the ≤2–3-concurrent rule.

## Verification (per track)

- **Track 1:** `lake build SP1Clean.Chips.ALU.ShiftLeftChip.Circuit` (etc.); for Stream B,
  `lake build SP1Operations` + `lake env lean SP1Clean/Operations/BitwiseU16OperationWitnessed.lean`
  (expect only the closed sorries to disappear). Confirm closure with
  `#print axioms <decl>` showing only `propext/Classical.choice/Quot.sound` (calibrate against a
  known sorry, e.g. `MulOperation.iff_sp1_full`).
- **Track 2:** `lake build SP1Clean.Chips.Control.JalChip.Circuit` / `…BranchChip.Multiplicity.Circuit`
  / `…Memory.LoadByteChip`; `#print axioms` on the newly-closed `soundness`/`completeness`.
- **Track 3:** `lake build SP1Clean.Soundness` (fast); `#print axioms` on `execute_trace`, `genRow`,
  the unconditional theorem, and each closed `memoryAccessesValid_of_spec_*` / `cpuStateSpec_of_spec_*`.
- **Whole-repo gate (any track, end of session):** `lake build SP1Clean` then
  `grep -cE '^(error|warning):' build.log` — both counts trending toward zero. Always finish a phase
  with a real `lake build <Module>` (a bare `lake env lean` exits 0 even on stack overflow).
