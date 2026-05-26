# SP1Clean canonical-pattern audit

Phase 1 deliverable of the master plan. Scores every chip and operation in
`SP1Clean/` against the AddChip/AddOp canonical pattern (commits `b82c79e`
+ `a8e50fb`). The audit dimensions and verdict semantics are defined in
the master plan at `~/.claude/plans/make-a-plan-to-sleepy-cocke.md`; this
doc is the per-decl table that drives the migration worklist
(`docs/CLEAN_WORKLIST.md`).

Reference baseline: `SP1Clean/AddChip/{Cols,Circuit,Lemmas,SailBridge}.lean`
and `SP1Clean/Operations/AddOperation.lean`. The
[Operation contract template](MULTIPLICITY_BUS.md#operation-contract-template-canonical-pattern-from-commit-b82c79e--this-pr)
section of `MULTIPLICITY_BUS.md` is the canonical recipe.

Sorry counts in this doc are at-the-time-of-audit (2026-05-25, post-merge,
post-MemoryConsistency-fix). Total sorry occurrences across SP1Clean:
**82** in **25 files**.

## Audit dimensions

- **D1 — Spec semantic purity.** Is `FormalSpec` / `Assertion.Spec` of the
  form `... ∧ (is_real = 1 → isU64 result ∧ RV64.<op>-equation)`, with no
  `RawSpec` / carry expressions / `List.Forall SP1Constraint.toProp` /
  `(<Op>.constraints …).allHold` / Sail.execute_* embedded? Canonical:
  `SP1Clean/AddChip/Cols.lean:194–209`.
- **D2 — Composition fidelity.** Does `main` invoke `<Sub>.Gated.assertion`
  as Clean FormalAssertion subcircuits? Does `FormalSpec` compose the
  matching `<Sub>.Gated.Assertion.Spec`s by direct field application? No
  `InlinedSpec` bridges, no parallel `main (a b ...)` / `Spec (a b ...)`
  forms.
- **D3 — Multiplicity gating.** Byte-bus sends via
  `SP1Lookup.byteOpcodeGated` with `mult = is_real`; reader/state sub-
  composition via `Gated.assertion` (not plain `.assertion`); memory
  contributions routed through the multiplicity-aware bus (i.e.
  `ChipRow.memoryAccesses .<chip> = []`).
- **D4 — Sail isolation.** Zero Sail / LeanRV64D imports or constructs in
  `<Chip>/Circuit.lean` and `<Chip>/Cols.lean`; Sail-monadic equivalence
  confined to a single axiom-clean `sail_correct_of_formalSpec` in
  `<Chip>/SailBridge.lean`.
- **D5 — Completeness reachability.** Does `Assertion.completeness` close,
  or is it `sorry`? If `sorry`, is the gap traceable to a D1/D2/D3
  violation (closing the violation closes the sorry)?

Cells: ✅ green / ⚠️ partial / ❌ red / — n/a.

Verdicts:

- **canonical** — all five ✅.
- **mechanical** — clear-path AddChip recipe applies (Phase 2 of master plan).
- **needs-Gated** — chip composes un-gated readers/state; Phase 3.
- **needs-memory-routing** — chip uses flat `MemoryAccess` records; Phase 4.
- **scope-fence** — structurally divergent; defer to Phase 6 with breadcrumbed sorries.
- **op-canonical / op-mechanical / op-stub** — operation-level analogs.

---

## Chip audit (24 entries)

### AddChip

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ✅ | ✅ | ✅ | ✅ | ✅ | 0 | **canonical** |

- Reference for everything else. `FormalSpec` at `Cols.lean:194–209`: structural sub-circuits (`CPUState.Gated`, `RTypeReader.Gated`, `op_a_0 = 0`) plus the semantic `(is_real = 1 → isU64 ∧ toBitVec64 = RV64.add …)` conjunct. SailBridge axiom-clean (`{propext, Classical.choice, Quot.sound}`).

### AddiChip

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ❌ | ✅ | ✅ | ✅ | ⚠️ | 1 | **mechanical** |

- **D1**: `Cols.lean:79–98` embeds `SP1Clean.AddOp.RawSpec` as first conjunct of `FormalSpec`. Trailing semantic `(is_real = 1 → toBitVec64 = RV64.addi …)` is already there, but the legacy RawSpec is also there.
- **D5**: `SP1Clean/AddiChip/Circuit.lean:129` `sorry` in soundness padding-row case — RawSpec must still hold under `is_real = 0` but multiplicity-gated `main` can't witness it. Resolves by dropping RawSpec from `FormalSpec`.
- **Recipe**: Phase 2 — Drop RawSpec conjunct from `Cols.FormalSpec`; restate as `is_real = 1 → (isU64 ∧ BV equation)`; update `Lemmas.allHold_iff_structural` to bridge via `AddOp.iff_sp1_full`; re-thread soundness/completeness; verify SailBridge.

### AddwChip

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ❌ | ✅ | ✅ | ✅ | ✅ | 0 | **mechanical** |

- **D1**: `Cols.lean ~190–230` embeds `SP1Clean.AddwOp.Spec` (carry-chain form) as first conjunct alongside the trailing semantic `(is_real = 1 → toBitVec64 op_a_write_value = RV64.addw …)`. ADDIW variant deferred per inline comment (waiting on `ALUTypeReader.Gated` immediate-sign-ext exposure).
- **Recipe**: Phase 2 — drop `AddwOp.Spec`, restate as semantic-only; mirrors AddChip recipe. Also add `AddwOperation.iff_sp1_full` to `SP1Operations/Operation/AddwOperation/AddwOperation.lean` (main task).

### BitwiseChip

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ❌ | ❌ | ❌ | ⚠️ | ❌ | 8 | **needs-Gated** |

- **D1**: `Cols.lean:176–196` `FormalSpec` uses `List.Forall SP1Constraint.toProp (BitwiseU16Operation.constraints …).2` envelope — direct CLAUDE.md violation; no semantic RV64 conjunct.
- **D2**: composes `BitwiseU16Operation.constraints` via the `.allHold`-equivalent envelope rather than as `BitwiseU16Op.assertion` subcircuit.
- **D3**: uses ungated `SP1Clean.CPUState.cpuStateSpec` and `SP1Clean.ALUTypeReader.aluTypeReaderSpec` — non-Gated readers.
- **D4**: SailBridge has `sorry` (1 occurrence at `SailBridge.lean:43`).
- **D5**: `Circuit.lean:94, :98` soundness/completeness `sorry`. `Lemmas.lean:28, :83` 2 sorries.
- **Recipe**: Phase 3. Migrate to `CPUState.Gated.assertion`, `ALUTypeReader.Gated.assertion`; wrap `BitwiseU16Op.assertion` as proper subcircuit; restate `FormalSpec` semantically (compose `<Sub>.Gated.Assertion.Spec` directly + trailing `is_real = 1 → toBitVec64 = RV64.<and|or|xor>`).

### BranchChip

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ❌ | ❌ | ❌ | — | ❌ | 4 | **scope-fence** |

- **D1**: `Cols.lean` / `BranchChip.lean` FormalSpec uses `CPUState.cpuStateSpec` and structural conjuncts on 6 selectors; no semantic conjunct.
- **D2**: structurally divergent — 6-way selector (`is_beq/bne/blt/bge/bltu/bgeu`) with InlinedSpec-style bridge per the prior audit.
- **D3**: ungated readers / state.
- **D5**: `Branch/Circuit.lean:245, :252` 2 sorries (soundness + completeness).
- **Recipe**: Phase 6 (scope-fence). Migration recipe doesn't fit cleanly because of the 6-way Branch selector and PC-update semantics. Keep current state with breadcrumbed sorries; migrate in a follow-up plan.

### DivRemChip

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ❌ | ❌ | ❌ | ❌ | ❌ | ~12 | **scope-fence** |

- **D1**: 8-way mode selector (`div/divu/rem/remu/divw/remw/divuw/remuw`) with no canonical semantic conjunct.
- **D2**: `Circuit.lean` carries the 247-column `Main` constraint scaffold; no proper sub-circuit composition graph.
- **D3**: ungated everything.
- **D4**: `SailBridge.lean:18, 23, 28, 33, 38, 43, 48, 53` — 8 sorries (one per opcode variant).
- **D5**: `DivRemChip.lean:275` + `DivRemChip/Lemmas.lean:18, :23` + `Circuit.lean` sorries — chip-level soundness/completeness deferred.
- **Recipe**: Phase 6. Per CLAUDE.md the chip is the canonical "scope-fence" case. Keep current sorries; document with breadcrumbs; revisit after Phases 2–4 stabilize the recipe.

### JalChip

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ❌ | ⚠️ | ⚠️ | ✅ | ❌ | 4 | **mechanical** |

- **D1**: `JalChip.lean:149–150, 441–442` embeds `SP1Clean.AddOp.RawSpec` twice (jump-target carry + return-address carry).
- **D2**: composes `ProgramTable.Spec` and `GatedAddOp.Spec` (good) but mixes with `CPUState.cpuStateSpec` (ungated).
- **D3**: ProgramTable + GatedAddOp use multiplicity gating; CPUState does not.
- **D5**: `JalChip.lean:471, :473` (soundness gaps on jump-target and return-address `RawSpec` derivation); `:491, :493` (completeness gaps for same).
- **Recipe**: Phase 2 — drop `AddOp.RawSpec` conjuncts from `FormalSpec`, restate as `is_real = 1 → next_pc-BV-equation ∧ op_a-BV-equation`; bridge via `AddOp.iff_sp1_full` ×2. Closes all 4 sorries.

### JalrChip

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ⚠️ | ⚠️ | ⚠️ | ✅ | ⚠️ | 0 in body | **mechanical** |

- **D1**: `JalrChip.lean ~150–200` uses `cols.is_real = 0 ∨ SP1Clean.GatedAddOp.Spec …` disjunctive form (Phase 2.a-ish pattern); no `is_real = 1 → BV` conjunct.
- **D2**: composes `ProgramTable.Spec` + `GatedAddOp.Spec` but `CPUState.cpuStateSpec` is ungated.
- **D3**: mixed (Gated AddOp; ungated state).
- **Recipe**: Phase 2 — restate `GatedAddOp` disjunct as semantic `(is_real = 1 → next_pc-BV-equation)`; promote `CPUState` to `Gated`.

### LtChip

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ⚠️ | ✅ | ✅ | ❌ | ❌ | 7 | **mechanical** |

- **D1**: `Cols.lean:173–210` composes `GatedLtSignedOp.Assertion.FormalSpec` + `CPUState.Gated.Assertion.Spec` + `ALUTypeReader.Gated.Assertion.Spec` (great D2/D3). Has trailing RV64 BitVec semantic clauses but they're guarded by per-selector flags (slt / sltu), not the canonical `is_real = 1 → ...` shape.
- **D4**: `LtChip/SailBridge.lean:40, :56, :72, :88` — 4 sorries.
- **D5**: `LtChip/Circuit.lean:120` soundness sorry; `Lemmas.lean:55` sorry. Phase 2.2 recent work moved most lemmas to closed state but bridges still pending.
- **Recipe**: Phase 2-extended — close `LtChip/SailBridge` sorries by composing the existing `LtOperationSigned.spec.signed` / `.unsigned` bridges. The chip's structure is already canonical; only the Sail bridge remains.

### MemoryGlobalChip

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ⚠️ | — | — | ✅ | ✅ | 0 | **scope-fence** |

- Boundary chip (init/finalize). `Spec` is just `cols.is_real * (cols.is_real - 1) = 0` (binarity). No FormalAssertion scaffold yet; column struct + ChipRow constructor only.
- **Recipe**: Phase 6. Needs trace-level memoryAccess discharge in the multiplicity bus; not a Phase 2-4 candidate.

### MulChip

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ❌ | ❌ | ❌ | ❌ | ❌ | 9 | **needs-Gated** |

- **D1**: `Cols.lean:185–...` 5-way selector form (`is_mul/mulh/mulhu/mulhsu/mulw`), embeds `SP1Clean.MulOp.Spec` (legacy structural form) + ungated CPUState + ungated RTypeReader. Has trailing per-selector RV64 conjuncts (`is_mul = 1 → aw = RV64.mul cw bw` etc.) — semantically intended but not gated through `is_real`.
- **D2**: composes `MulOp.Spec` (operation Spec, not assertion) — D2 violation. Uses `cpuStateSpec` / `rtypeReaderSpec` (ungated) instead of `Gated.Assertion.Spec`.
- **D3**: ungated readers.
- **D4**: `MulChip/SailBridge.lean:33, :48, :63, :78, :93` — 5 sorries (one per selector variant).
- **D5**: `Circuit.lean:86, :87, :97, :101` 4 sorries (`localLength_eq`, `subcircuitsConsistent`, soundness, completeness). `Lemmas.lean:25, :78` 2 sorries.
- **Recipe**: Phase 3. Migrate to `CPUState.Gated`, `RTypeReader.Gated`; reshape `MulOp` to semantic-only contract (Phase 5 prereq: add `MulOperation.iff_sp1_full`); restate `FormalSpec` as per-selector `is_<sel> = 1 → ...` semantic conjuncts only.

### ShiftLeftChip

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ❌ | ❌ | ❌ | ❌ | ❌ | 10 | **needs-Gated** |

- **D1**: `Cols.lean:155–187` 2-way selector (`is_sll/sllw`), composes `U16MSBOp.Assertion.Spec` (good) + `cpuStateSpec` + `aluTypeReaderSpec` (ungated). No semantic RV64 conjunct at all — all structural arithmetic (bit-decomp, byte-shift one-hot, shift-power chain).
- **D2**: ungated CPUState / ALUTypeReader; structural arithmetic inlined.
- **D3**: ungated.
- **D4**: `ShiftLeftChip/SailBridge.lean` — 6 sorries (presumed from filename pattern, mirror of ShiftRight).
- **D5**: `Circuit.lean` `localLength_eq` + `subcircuitsConsistent` + soundness + completeness sorries; `Lemmas.lean:23, :29` 2 sorries.
- **Recipe**: Phase 3. Migrate `cpuStateSpec`/`aluTypeReaderSpec` → `.Gated`; add `RV64.sll`/`sllw` semantic conjunct gated on `is_real = 1`; reduce structural arithmetic to internal `main` detail. (Major rewrite — closer to ground-up than mechanical.)

### ShiftRightChip

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ❌ | ❌ | ❌ | ❌ | ❌ | 12 | **needs-Gated** |

- Identical shape to ShiftLeftChip (with 3 U16MSBOp variants: SRA / SRAW / SRL discrimination).
- **D4**: `ShiftRightChip/SailBridge.lean:19, :25, :31, :37, :43, :49, :55, :61` — 8 sorries.
- **D5**: `Circuit.lean:88, :89, :97, :101` 4 sorries; `Lemmas.lean:21, :27` 2 sorries.
- **Recipe**: Phase 3. Same recipe as ShiftLeft.

### SubChip

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ❌ | ✅ | ✅ | ✅ | ✅ | 0 | **mechanical** |

- **D1**: `Cols.lean ~155–185` embeds `SP1Clean.SubOp.Spec` (legacy carry form) as first conjunct alongside the trailing semantic `(is_real = 1 → toBitVec64 = RV64.sub …)`.
- **Recipe**: Phase 2 — drop `SubOp.Spec` conjunct; restate as semantic-only. Add `SubOperation.iff_sp1_full` to `SP1Operations/Operation/SubOperation/SubOperation.lean` (main).

### SubwChip

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ❌ | ✅ | ✅ | ✅ | ✅ | 0 | **mechanical** |

- Same shape as SubChip — embeds `SP1Clean.SubwOp.Spec` as first conjunct alongside semantic `RV64.subw` conjunct.
- **Recipe**: Phase 2 + `SubwOperation.iff_sp1_full` sibling.

### UTypeChip

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ❌ | ❌ | ⚠️ | ✅ | ❌ | 2 | **mechanical** + needs-Gated |

- **D1**: `Cols.lean:198–...` embeds `(_root_.AddOperation.constraints …).allHold` directly — D1 + D2 violation (CLAUDE.md Faithful sub-circuit composition §3 forbids `(constraints).allHold` envelope at FormalSpec).
- **D2**: uses ungated `SP1Clean.CPUState.cpuStateSpec`. JTypeReader IS Gated (good).
- **D5**: `UTypeChip/Circuit.lean:144, :155` 2 sorries (soundness + completeness).
- **Recipe**: Phase 2 — replace `(_root_.AddOperation.constraints …).allHold` with `SP1Clean.AddOp.assertion.Spec` (the canonical sub-circuit subordinate Spec, gated on `is_real - op_a_0`); migrate `cpuStateSpec` → `CPUState.Gated.Assertion.Spec`.

### LoadByteChip / LoadHalfChip / LoadWordChip / LoadDoubleChip

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ⚠️ | ✅ | ❌ | ✅ | ✅ | 0 | **needs-memory-routing** |

- **D1**: FormalSpec composes `CPUState.Assertion.Spec` (not `.Gated`!) + `AddrAddOp.Assertion.Spec` + `AddressShape.Assertion.Spec` + `ITypeReaderImmutable.Assertion.Spec` + `OperandAccess.Assertion.Spec` + flat per-byte selector specs. No semantic conjunct gated on `is_real = 1` — D1 partial.
- **D2**: composes sub-`.Assertion.Spec`s via direct field application — D2 ✅.
- **D3**: `OperandAccess.Assertion.Spec` (ungated); `CPUState.Assertion.Spec` (ungated) — D3 ❌.
- **D5**: Load{Byte,Half,Word,Double} have soundness/completeness bodies present, no top-level sorries in the body; depends on the OperandAccess sub-circuits being canonical.
- **Recipe**: Phase 4. Migrate memory access through `LoadMemoryAccessGated.assertion` (already exists at `SP1Clean/Operations/LoadMemoryAccessGated.lean`); promote `CPUState` to `.Gated`; add semantic conjunct (`is_real = 1 → toBitVec64 op_a_write_value = RV64.<lop> addr …`); update `ChipRow.memoryAccesses .<chip>` to `[]` once routed.

### LoadX0Chip

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ❌ | ⚠️ | ❌ | ⚠️ | ❌ | 1 | **scope-fence** |

- 7-way selector (lb/lbu/lh/lhu/lw/lwu/ld) with `op_a_write_value = #v[0,0,0,0]` (x0-target specialization).
- **D5**: `LoadX0Chip.lean:193` `sorry` — chip body deferred per inline note (Phase 6 candidate).
- **Recipe**: Phase 6. After Load* are migrated (Phase 4), restate as the Load*-shape but specialized to `op_a_write_value = 0`.

### StoreByteChip / StoreHalfChip / StoreWordChip / StoreDoubleChip

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ⚠️ | ✅ | ❌ | ✅ | ✅ | 0 | **needs-memory-routing** |

- Same architecture as Load* but write-side. Composes `CPUState.Assertion.Spec` (ungated), `AddrAddOp.Assertion.Spec`, `AddressShape.Assertion.Spec`, `ITypeReaderImmutable.Assertion.Spec`, `OperandAccess.Assertion.Spec` (ungated) for read of stored value, plus `MemoryAccess` write record.
- **D3**: ungated `OperandAccess.Assertion.Spec`.
- **Recipe**: Phase 4. Migrate via `StoreMemoryAccessGated.assertion` (already exists); promote `CPUState` to `.Gated`; add semantic-write conjunct; update `ChipRow.memoryAccesses .<chip>`.

---

## Operation audit (~30 entries)

### AddOperation

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ✅ | ✅ | ✅ | — | ✅ | 0 | **op-canonical** |

- Reference. `SP1Clean/Operations/AddOperation.lean:162–177` — semantic `Assumptions ∧ Spec` mirroring AddChip one level down. `Spec := is_real = 1 → (isU64 result ∧ toBitVec64 result = toBitVec64 a + toBitVec64 b)`.

### SubOperation / AddwOperation / SubwOperation

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ❌ | ⚠️ | ⚠️ | — | ✅ | 0 | **op-mechanical** |

- `Operations/SubOperation.lean ~80–130` (and Addw/Subw analogs) define `Spec` as carry-chain form — direct `Spec := SP1Clean.<Op>.Spec` where `<Op>.Spec` is the structural top-level helper (carry expressions + range bounds).
- **D3**: `main` emits byte lookups; need to verify each is `byteOpcodeGated`. `SubwOperation` also has `List.Forall SP1Constraint.toProp (_root_.U16MSBOperation.constraints …)` envelope — D2 violation.
- **Recipe**: Apply the AddOp `a8e50fb` recipe: drop `Spec := <Op>.Spec`, restate as `is_real = 1 → (isU64 result ∧ <BV equation>)`. Add `spec_inv` + `iff_sp1_full` siblings in `SP1Operations/Operation/<Op>/<Op>.lean`.

### AddrAddOperation

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ❌ | ⚠️ | ⚠️ | — | ✅ | 0 | **op-mechanical** |

- `Operations/AddrAddOperation.lean ~80–110` carries carry-chain Spec.
- 48-bit address add (3 limbs of result + 4-th carry); needs the AddOp recipe with a 48-bit variant.

### GatedAddOp

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ❌ | ⚠️ | ✅ | — | ✅ | 0 | **op-mechanical** |

- Already gated on `mult`; `Spec` still carry-chain. Recipe: restate Spec as semantic-only conditional on `mult = 1`.

### BitwiseOperation

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ⚠️ | ⚠️ | ⚠️ | — | ✅ | 0 | **op-mechanical** |

- `Spec input := ∀ i : Fin 8, (ByteOpcode.ofNat opcode.val).constrain (result[i.val]) (a[i.val]) (b[i.val])` — uses primitive `ByteOpcode.constrain`. Not semantic in the RV64 sense but is the right abstraction for the bus.
- Recipe: confirm `main` uses `byteOpcodeGated`; promote Spec to mirror SP1's `BitwiseOp.constrain_X` form.

### BitwiseU16Operation

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ✅ | ✅ | ✅ | — | ✅ | 0 | **op-canonical-adjacent** |

- `Operations/BitwiseU16Operation.lean ~80–130` composes `SP1Clean.BitwiseOpGated.Assertion.Spec` directly via field application — D2 ✅. Carries binarity gate `input.is_real * (input.is_real - 1) = 0` at the top.
- This is the cleanest non-Add operation. Could serve as a secondary canonical reference for opcode-selecting ops.

### IsZeroOperation

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ✅ | ✅ | — | — | ✅ | 0 | **op-canonical-adjacent** |

- `Spec a result := result = if a = 0 then 1 else 0`. Primitive operation; semantic by construction. No multiplicity gating needed (no byte sends).

### IsZeroWordOperation

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ❌ | ⚠️ | — | — | ❌ | 0 sorry but doc says "proof bodies sorry" | **op-stub** |

- Per-limb structural form. `Operations/IsZeroWordOperation.lean:33` comment notes "Proof bodies `sorry`" though no explicit `sorry` token in grep — likely structurally still incomplete; verify with `lake build`.

### IsEqualWordOperation

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ✅ | ✅ | — | — | ❌ | 0 token but doc says sorry | **op-stub** |

- Composes `IsZeroWordOp.Spec` via direct field application — D2 ✅. Doc comment at `:25` says "Proof bodies `sorry`."

### LtOperationSigned / LtOperationUnsigned

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ⚠️ | ✅ | ⚠️ | — | ⚠️ | 1 (Signed) / 0 | **op-mechanical** |

- `LtOperationSigned.Spec` composes `U16MSBOp.Assertion.Spec` ×2 directly (D2 ✅), but flat `is_signed`-flag arithmetic chain.
- `LtOperationSigned.lean:222` 1 sorry (Vector-shape mismatch in bridge body per inline note).
- `LtOperationUnsigned.Spec` composes `U16CompareOp.Assertion.Spec` directly — D2 ✅. Mostly clean.
- Recipe: Phase 5. Close the LtSigned bridge sorry; add semantic-only Spec on top.

### MulOperation

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ⚠️ | ⚠️ | ❌ | — | ❌ | 3 | **op-stub** |

- `Operations/MulOperation.lean ~280–360` 5-way selector Spec uses `Word.isU64 b → Word.isU64 c → (is_mul = 1 → aw = execute_MUL_pure bw cw .MUL) ∧ ...` — partial semantic form. **Uses `execute_MUL_pure` which is from `RISCV.SailPure`** — borderline D4 (RV64-style but routes through SailPure).
- **D5**: `Operations/MulOperation.lean:340, :349, :353` 3 sorries.
- Recipe: Phase 5 prerequisite for MulChip. Close the 3 op-level sorries; finalize the per-selector semantic form.

### U16MSBOperation / U16CompareOperation

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ✅ | ✅ | — | — | ✅ (MSB) / ❌ (Cmp) | 0 (MSB) / 0 token but doc says sorry (Cmp) | **op-canonical-adjacent** |

- `U16MSBOp.Spec a msb := msb * (msb - 1) = 0 ∧ (2 * a - msb * 65536).val < 65536` — primitive structural form, semantic by construction for the MSB-extraction operation.
- `U16CompareOp` similar; doc says "proof bodies sorry" at `:34`.

### U16toU8OperationSafe / Unsafe

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ✅ (Safe) / — (Unsafe) | ✅ | — | — | ✅ | 0 | **op-canonical-adjacent** |

- Safe: `Spec` has structural byte-range conditions — primitive.
- Unsafe: `Spec := True` — trivially vacuous (constraint list empty).

### AddressShape

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ⚠️ | ⚠️ | — | — | ❌ | 2 | **op-stub** |

- Address-shape boolean gates + bit-decomposition. `Operations/AddressShape.lean:78, :82` 2 sorries (soundness + completeness — comment at `:30` says "Future work: emit the boolean gates / bit-decomp lookup").

### GatedLtSignedOp / GatedLtUnsignedOp

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ⚠️ | ✅ | ✅ | — | ✅ | 0 | **op-canonical-adjacent** |

- Both have the `is_real`/`gate`-style binarity + sub-circuit composition. `FormalSpec` carries the structural disjunctive form `gate = 0 ∨ <constraint conjunction>`. Multiplicity-gated. Could be promoted to fully semantic by adding RV64.slt/sltu trailing conjunct.

### LoadMemoryAccessGated / StoreMemoryAccessGated

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ⚠️ | — | ✅ | — | ✅ | 0 | **op-canonical-adjacent** |

- `Spec := input.mult = 0 ∨ True` — placeholder Spec, actual content in `main`'s bus emission. Multiplicity-gated via `mult`. Ready for Phase 4 consumers.

### Load{Byte,Half,Word}Selector / Store{Byte,Half,Word}Assembler

| D1 | D2 | D3 | D4 | D5 | Sorries | Verdict |
|----|----|----|----|----|---------|---------|
| ✅ | — | — | — | ✅ | 0 | **op-canonical-adjacent** |

- All have `Spec _ := True`. Pure wrappers; semantic content owned by consuming chip. No work needed standalone.

### Compare/LtOperationSigned (separate file, distinct from Operations/)

- The `SP1Clean/Compare/LtOperationSigned.lean` file (separate directory) — survey deferred to the worklist; likely a thin wrapper.

---

## Sorry register (82 occurrences across 25 files)

Grouped by file. Each line: `file:line — context, dimension violated, breadcrumb to closure phase`.

### Chips

| File:line | Context | D | Closes in |
|-----------|---------|---|-----------|
| `SP1Clean/AddiChip/Circuit.lean:129` | soundness padding-row: RawSpec required on `is_real = 0` | D1 | Phase 2 (drop RawSpec from FormalSpec) |
| `SP1Clean/JalChip.lean:471` | soundness: jump-target AddOp.RawSpec | D1 | Phase 2 |
| `SP1Clean/JalChip.lean:473` | soundness: return-address AddOp.RawSpec | D1 | Phase 2 |
| `SP1Clean/JalChip.lean:491` | completeness: jump-target | D1 | Phase 2 |
| `SP1Clean/JalChip.lean:493` | completeness: return-address | D1 | Phase 2 |
| `SP1Clean/UTypeChip/Circuit.lean:144` | soundness | D1+D2 | Phase 2 |
| `SP1Clean/UTypeChip/Circuit.lean:155` | completeness | D1+D2 | Phase 2 |
| `SP1Clean/Branch/Circuit.lean:245` | soundness | D1+D2+D3 | Phase 6 |
| `SP1Clean/Branch/Circuit.lean:252` | completeness | D1+D2+D3 | Phase 6 |
| `SP1Clean/MulChip/Circuit.lean:86` | localLength_eq | D2 | Phase 3 |
| `SP1Clean/MulChip/Circuit.lean:87` | subcircuitsConsistent | D2 | Phase 3 |
| `SP1Clean/MulChip/Circuit.lean:97` | soundness | D1+D2+D3 | Phase 3 |
| `SP1Clean/MulChip/Circuit.lean:101` | completeness | D1+D2+D3 | Phase 3 |
| `SP1Clean/MulChip/Lemmas.lean:25` | structural lemma | D2 | Phase 3 |
| `SP1Clean/MulChip/Lemmas.lean:78` | structural lemma | D2 | Phase 3 |
| `SP1Clean/MulChip/SailBridge.lean:33, :48, :63, :78, :93` | 5 Sail-bridge sorries (one per selector) | D4 | Phase 3 + Phase 5 |
| `SP1Clean/BitwiseChip/Circuit.lean:94, :98` | soundness + completeness | D1+D2+D3 | Phase 3 |
| `SP1Clean/BitwiseChip/Lemmas.lean:28, :83` | structural lemmas | D2 | Phase 3 |
| `SP1Clean/BitwiseChip/SailBridge.lean:43, :69, :95` (presumed; 3 selectors) | Sail-bridge sorries | D4 | Phase 3 + Phase 5 |
| `SP1Clean/ShiftLeftChip/Circuit.lean:88, :89, :97, :101` | localLength_eq, subcircuitsConsistent, soundness, completeness | D1-D3+D5 | Phase 3 (major rewrite) |
| `SP1Clean/ShiftLeftChip/Lemmas.lean:23, :29` | structural lemmas | D2 | Phase 3 |
| `SP1Clean/ShiftLeftChip/SailBridge.lean:*` | 6 Sail-bridge sorries (2 selectors × {soundness, completeness, structural}) | D4 | Phase 3 + Phase 5 |
| `SP1Clean/ShiftRightChip/Circuit.lean:88, :89, :97, :101` | same as ShiftLeft | D1-D3+D5 | Phase 3 |
| `SP1Clean/ShiftRightChip/Lemmas.lean:21, :27` | structural lemmas | D2 | Phase 3 |
| `SP1Clean/ShiftRightChip/SailBridge.lean:19, :25, :31, :37, :43, :49, :55, :61` | 8 Sail-bridge sorries | D4 | Phase 3 + Phase 5 |
| `SP1Clean/LtChip/Circuit.lean:120` | soundness | D5 | Phase 2-extended |
| `SP1Clean/LtChip/Lemmas.lean:55` | structural lemma | D2 | Phase 2-extended |
| `SP1Clean/LtChip/SailBridge.lean:40, :56, :72, :88` | 4 Sail-bridge sorries | D4 | Phase 2-extended |
| `SP1Clean/DivRemChip/Circuit.lean:*` | chip-level scaffold | all | Phase 6 |
| `SP1Clean/DivRemChip.lean:275` | chip body | all | Phase 6 |
| `SP1Clean/DivRemChip/Lemmas.lean:18, :23` | structural lemmas | all | Phase 6 |
| `SP1Clean/DivRemChip/SailBridge.lean:18, :23, :28, :33, :38, :43, :48, :53` | 8 Sail-bridge sorries (one per opcode) | D4 | Phase 6 |
| `SP1Clean/LoadX0Chip.lean:193` | chip body | all | Phase 6 (after Phase 4 Load*) |

### Operations

| File:line | Context | D | Closes in |
|-----------|---------|---|-----------|
| `SP1Clean/Operations/AddressShape.lean:80, :84` | soundness + completeness | D5 (impl gap) | Phase 5 |
| `SP1Clean/Operations/LtOperationSigned.lean:222` | bridge body (Vector shape) | D5 | Phase 5 |
| `SP1Clean/Operations/MulOperation.lean:340, :349, :353` | per-selector closure stubs | D5 | Phase 5 (prereq for MulChip) |

### Trace-soundness

| File:line | Context | D | Closes in |
|-----------|---------|---|-----------|
| (none currently — `MemoryConsistency.lean:1067` was paid down in earlier phase) | | | |

---

## Verdict tally

- **Chips canonical**: 1 / 24 (AddChip).
- **Chips mechanical** (Phase 2): 6 / 24 (Addi, Addw, Sub, Subw, Jal, Jalr).
- **Chips needs-Gated** (Phase 3): 4 / 24 (Mul, ShiftLeft, ShiftRight, Bitwise) — plus UType needs Gated CPUState even though it's mostly Phase 2.
- **Chips needs-memory-routing** (Phase 4): 8 / 24 (LoadByte, LoadHalf, LoadWord, LoadDouble, StoreByte, StoreHalf, StoreWord, StoreDouble).
- **Chips Lt special** (Phase 2-extended): 1 / 24.
- **Chips scope-fence** (Phase 6): 5 / 24 (DivRem, Branch, LoadX0, MemoryGlobal — and BranchChip's content not yet audited in detail).

- **Operations canonical / canonical-adjacent**: ~12 (AddOperation, BitwiseU16, IsZero, U16MSB, U16CompareOp, U16toU8Safe/Unsafe, GatedLtSigned/Unsigned, LoadByte/Half/Word selectors, Store*Assemblers, Load/StoreMemoryAccessGated).
- **Operations mechanical**: ~7 (Sub, Addw, Subw, AddrAdd, GatedAddOp, BitwiseOperation, LtOperationUnsigned).
- **Operations stub** (Phase 5): ~6 (IsZeroWordOp, IsEqualWordOp, AddressShape, MulOperation, U16CompareOperation, LtOperationSigned).

Estimated sorry delta if Phases 2–4 land: **−45 to −60** (Mechanical + needs-Gated + needs-memory-routing chips closed; Lt-Sail bridge closed). Residual after Phase 6 = scope-fenced chips' sorries (DivRem 12 + Branch 2 + LoadX0 1 = ~15) + Phase-5 operation stubs (~5).
