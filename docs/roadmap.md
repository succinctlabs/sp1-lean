# Roadmap — open work

Two orthogonal axes of remaining work, consolidated from the former coverage and sound-model checklists:

- **Axis A — coverage breadth:** how many of SP1's chips/operations are modeled, and which faithfulness
  connections exist.
- **Axis B — sound-model depth:** how *meaningful/sound* the covered part is — closing the remaining `sorry`s,
  shrinking the trust base, and tightening the model toward SP1's real machine.

For what is *already proven* and the full trust boundary, see [`release-audit.md`](release-audit.md). For the
machine-checked axiom set, see [`agents/axiom-ledger.md`](agents/axiom-ledger.md).

Legend: `[ ]` open · `[~]` partial · `[x]` done.

---

## The project debt at a glance — five `sorry`s

All `sorry`s are **completeness/liveness** (or one capstone-packaging premise). Soundness is `sorry`-free.
Closing items 1–4 follows the recipe already applied to `BranchChip.completeness` (honest `populate`-style
witness + `ProverHint` opcode threading, a `main`-level change).

1. `MulChip.completeness` — `Chips/MulChip/Formal.lean:109` — emit the full `MulCols` witness; needs
   `MulOperation.spec_populate`.
2. `ShiftLeftChip.completeness` — `Chips/ShiftLeftChip/Formal.lean:405` — witness shift-amount/flag/limb
   columns from a real `populate`-style function.
3. `ShiftRightChip.completeness` — `Chips/ShiftRightChip/Formal.lean:1696` — same shape as ShiftLeft.
4. `DivRemChip.completeness` — `Chips/DivRemChip/Formal.lean:72` — DivRem soundness has landed (axiom-clean);
   only completeness remains.
5. `sp1_gatedExecution_prereqs` — `Soundness/SP1GatedVm.lean:193` — the single isolated capstone premise (see
   Axis B B5 item-5-proper); a packaging premise, not a chip debt.

---

## Axis A — coverage breadth

### A1. Finish the two heavy ALU chips (Mul, DivRem)

- [~] **Mul** — soundness proven and axiom-clean (`MulChip.soundness`, via `bv_decide`), but:
  - [ ] write `Chips/MulChip/Bridge.lean`: `correct_mul_native` over the 5 variants
    (MUL/MULH/MULHU/MULHSU/MULW) + `mul_chip_reaches_sail` + `MulChip.kind`. The semantic lemmas already
    exist in `Specs/Chip.lean` (`rv64_mul_eq`, `rv64_mulh_eq`, …) — the bridge consumes them as
    `correct_add_native` does.
  - [ ] carry the `Fact (2^24 < p)` bound through the `kind`/capstone (the rest is `Fact (2^17 < p)`).
    KoalaBear satisfies `2^24 < p`, so it is sound to require.
  - [ ] close `MulChip.completeness` (debt item 1; see Axis B B1).
  - [ ] add a `Faithful/MulChip.lean` full `↔` (today forward-`→` only).
- [~] **DivRem** — soundness has landed (axiom-clean), but:
  - [ ] close `DivRemChip.completeness` (debt item 4).
  - [ ] write `Chips/DivRemChip/Bridge.lean` (`correct_divrem_native` + `kind`) and `Faithful/DivRemChip.lean`
    (8 variants div/divu/rem/remu + w-variants).

### A2. Complete the faithfulness-anchor coverage (K2) for wired chips

The constraint↔structural-spec anchors (`Faithful/<Chip>.lean`) exist for the wired chips, with these gaps:
- [ ] **DivRem** — add `Faithful/DivRemChip.lean` (folded into A1).
- [ ] Optional strengthening (lower priority): Mul, Bitwise, ShiftLeft anchors are forward-`→` only; promote
  to full `↔` to also certify no SP1 constraint is dropped (Add-family/loads/stores/Branch are already `↔`).

### A3. Structural chips SP1 ships and this project does not model (decide: model or document-as-excluded)

Deliberately out of scope for the current deliverable; listed so the boundary is explicit, not accidental.
Each is a real SP1 `RiscvAir` variant (`riscv/mod.rs`).

- [ ] `InstructionDecode` / `InstructionFetch` — the decode/fetch chips. Modeling these is the natural home
  for discharging the decode half of the operand binding (Axis B B2).
- [ ] `MemoryGlobalInit` / `MemoryGlobalFinal` — global memory init/finalize tables.
- [ ] `MemoryLocal` / `MemoryBump` / `StateBump` — local memory + timestamp-bump tables.
- [ ] `PageProt` — page-protection table.
- [ ] Range-lookup chip — SP1 has a dedicated range chip; here range is folded onto the byte bus. Decide
  whether to model it separately or document the fold as faithful.
- [ ] Syscalls + precompiles (sha256/keccak/ed25519/field ops/…): ~dozens of chips — **out of scope**;
  document as such in any external claim.
- [ ] Supervisor/User chip duplication: SP1 ships both variants of most chips (~123 total). Decide whether the
  single-variant coverage is claimed to cover both (and justify) or noted as a gap.

### A4. Coverage-claim hygiene

- [ ] Keep `allChipKinds_length` and the `Soundness/Coverage.lean` guards (`coverage_kinds_eq_registry`,
  `coverage_length`, the covered/uncovered `by decide` partition) in sync as chips are added — `Coverage.lean`
  is the auditable `Opcode → chip → Sail` census, and `coverage_kinds_eq_registry` pins it to the registry.
- [ ] In any external/headline statement, cite the coverage figure (the RV64IM base chips of SP1's ~123
  `RiscvAir` variants) and the explicit exclusion list (A3) so "verifies SP1" is never implied beyond the
  base instruction chips.

---

## Axis B — sound-model depth

### B1. Close the remaining completeness `sorry`s (the only chip-level debt)

The five debt items above. Each is a *deferred completeness* (or the one capstone premise), not a trust
shortcut; closing items 1–4 removes all `sorryAx` from the wired chips. `BranchChip.completeness` and both
Branch faithfulness-forward anchors are **done** (proven clean-3, 2026-06-05, via honest `ProverHint` flag
witnesses + the shared dispatch in `Chips/BranchChip/Decision.lean`) — that is the template.

### B2. The meaningfulness boundary — operand/register/decode threading (the big open soundness item)

The per-chip Sail guarantee is *conditional* on register/memory binding + instruction decode (the deferred
operand/register/decode threading — see `release-audit.md` Part I "meaningfulness boundary"). This is the gap
between "each chip computes the right RV64 function of its columns" (proved) and "the trace executes the
decoded program against ISA state" (assumed). Discharging it is the highest-leverage sound-model work.

- [ ] **Register/memory binding**: derive, from the memory-bus balance + the register adapters' `prev_value`
  columns, that a row's committed operand columns equal the live ISA register/memory values. (Shifts/branches/
  jalr already read operands off `adapter.*_memory.prev_value`, the right hook.)
- [ ] **Instruction decode**: derive `rs1`/`rs2`/`rd`/`imm` for each row from the program-bus fetch, instead
  of universally quantifying the indices in `sailEquiv`. Natural home: model SP1's
  `InstructionDecode`/`InstructionFetch` chips (A3) and connect them to the program bus.
- [ ] Then strengthen the gated execution capstone to *construct* the operand binding from the bus balance
  rather than take it as a hypothesis — making the whole-program run unconditional.

### B3. Shrink the remaining whole-machine assumptions (named hypotheses, not `sorry`)

- [ ] **`isConsistentBalanced` (LogUp/GKR)** — currently assumed. Reduce "the crypto is assumed" to one named
  axiom and prove the algebra above it: (a) add one documented `axiom logupGkrSound` in
  `Foundations/InteractionBus.lean` ("a verifying GKR+PCS transcript ⟹ fingerprinted cumulative sum = 0") —
  the named cryptographic boundary; (b) prove the non-crypto half (fingerprinted-sum-zero ⟹ send/receive
  multiset equality, via LogUp / Schwartz-Zippel). **Done when** `isConsistentBalanced` is a theorem from the
  fingerprinted sum + the single axiom, and the TCB cites one crypto axiom instead of "balance assumed."
- [x] **Memory & state links derived from bus balance.** Both the PC chain (State bus) and offline memory
  consistency (Memory bus) are now *derived* from balance, not threaded as hypotheses; the gated capstone then
  forces the whole transition trail from the state-bus balance alone, dropping the trace-shape side-condition
  block for the execution result.

### B4. Model shards & lock currency (the strategic gap-closing items)

- [ ] **Multi-shard composition.** The capstone is single-shard; SP1's memory soundness is fundamentally
  multi-shard (Local/Global chips, public-value boundaries, the global cumulative sum). Add a
  `Soundness/ShardComposition.lean` with a `ShardBoundary` structure (pc_start→pc_next, init/final memory
  boundary, cumulative-sum carry) and prove a `machineValid_of_shards` chaining boundaries + memory
  address-disjointness. **Done when** a multi-shard capstone exists and the memory link is stated over the
  shard sequence, not one trace.
- [ ] **Harden the unproven trust links K1, K6, and lock currency.**
  - [ ] **K1 (constraint compiler)** — no proof that `sp1-constraint-compiler` reflects SP1's Rust `eval`.
    Cheapest hardening: an AIR analogue of the `populate` conformance check — `#guard` that each
    `Extracted/<chip>.asserts`/`interactions` accepts/rejects the same as SP1's own `eval` on a sampled row
    battery.
  - [ ] **K6 (`populate` conformance)** — for chips whose completeness remains `sorry`, the only witness
    evidence is sampled conformance; once B1 lands, completeness subsumes it. Prove `spec_populate` for the
    ops lacking it and widen the KoalaBear battery.
  - [ ] **Currency / CI** — pin SP1 to a commit in `update_extracted.py`, add a CI job that re-extracts and
    `git diff`s `Extracted/*` per-PR, wire `lake build SP1Clean` + a `#print axioms` census gating
    **0 `sorryAx`** over a defined released set, and migrate the remaining ops to the auto-generated circuit
    form. **Done when** CI is green-gated and the extraction diff is empty against a pinned SP1.
  - [ ] Document the `update_extracted.py` string-level `channelsWith*` promotion as a reviewed,
    semantics-preserving step (or replace it with a compiler-side fix).

### B5. Whole machine as a Clean `FormalEnsemble` (largely landed)

The whole-machine soundness now rides Clean's general whole-machine primitives via our **own gated
abstraction** (`Soundness/GatedVm/`), not bespoke project plumbing. All seven `GatedVm/` modules are in the
build and `sorry`-free: `GatedVm`/`toEnsemble`, `exists_trail` (the Eulerian core), `state_trail_of_balance`,
`chipRows_step_sound`, `gatedExecution_of_specs_and_balance` (the capstone), `gatedExecution_allChips`, and
the final Clean `FormalEnsemble` `sp1FormalEnsemble`/`sp1_machine_soundness` (`Soundness/SP1GatedVm.lean`)
with a meaningful `Spec` (a valid RISC-V-Sail execution trail from public `pc_start` to `next_pc`).

Remaining:
- [~] **item-5-proper — derive balance from Clean's `Statement.BalancedChannels`** (the sole residual premise
  `sp1_gatedExecution_prereqs`, debt item 5). The first brick is landed and axiom-clean:
  `LookupAccessList.isConsistentBalanced_of_intCast_zero` (`Soundness/GatedVm/BalanceMod.lean`). Still needed:
  (a) the representation translation (Clean `BalancedInteractions` → the `hmod` form); (b) the per-chip
  witness↔chipRows correspondence + verifier (the biggest piece); (c) `weakSoundness`'s byte-table
  `FullGuarantees` from the same balance. Closing it makes `sp1FormalEnsemble` axiom-clean (Sail-model only)
  with no further structural work — the assembly already threads it into the gated capstone.

### B6. Documentation hygiene (cheap, do alongside)

- [x] Correct stale source comments the audit caught (anything implying `correct_jal_native` carries a
  `sorry`; "no bridge yet" for Branch/Shift/UType; "~10 faithful anchors") — largely done.
- [ ] Keep the "what we prove vs assume" pointer (`release-audit.md`) at the top of `Soundness/SP1GatedVm.lean`
  current as the model evolves.
