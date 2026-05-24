# Struct-Level Divergence: SP1Clean ↔ upstream SP1

A field-level snapshot of how far our Lean column structures (in `SP1Clean/` and `SP1Operations/`) have drifted from upstream Rust (`../sp1/crates/core/machine/src/`). Constraint logic is *not* compared — only struct shape: field names, field types, and nesting.

Snapshot taken: 2026-05-21 (sp1-lean branch `dtumad/clean`, upstream `../sp1` at whatever was checked out today). **Update 2026-05-21 (later):** macro divergence #6 closed — `BranchCols` and `LtCols` now nest `LtOperationSigned`. See the Branch and Lt per-chip sections and the new sidecar at `SP1Clean/Compare/LtOperationSigned.lean`.

**Constraint-usage audit refresh: 2026-05-23.** Each per-chip section gained a `Constraint-usage audit:` status header and a `Per-column constraint usage` sub-table. Refresh sweep confirmed zero drift on the SP1 Rust side since 2026-05-21 (`git log --since="2026-05-21" -- crates/core/machine/src/` empty). SP1Clean side has only `ae3bcca` (DivRem.lean / DivwRemw.lean perf tweaks; no struct changes) and `62cd675` (mechanical import-path refactor across 35 files; no struct changes) since the snapshot commit `6ff1320`. The existing prose per-chip diffs were re-verified and not rewritten.

**Update 2026-05-23 (DivRem + ShiftRight decomposition sweep).** Four commits closed the two largest OPAQUE rows in the audit:
- `c3aedab` Phase 3e: `ShiftRightCols.intermediates_aux:28` decomposed into 11 named upstream sub-fields (b_msb, srw_msb, c_bits, sra_msb_v0123, v_0123/012/01, lower_limb, higher_limb, limb_result, shift_u16). **Open-question #3 CLOSED.**
- `ce4c38c` Phase 3f: `DivRemCols.aux:209` decomposed in full. The 44-cell aux_pre prefix (Main[32..75]) became 10 named top-level fields (b, c, quotient, quotient_comp, remainder_comp, remainder, abs_remainder, abs_c, max_abs_c_or_1, c_times_quotient). The 75-cell aux_post suffix (Main[166..240]) became a single nested `DivRemAuxPost` sub-record with 14 named fields (c_neg_operation, rem_neg_operation, remainder_lt_operation, carry, is_c_0, mode_flags, is_overflow, is_overflow_b/c, b_msb/rem_msb/c_msb/quot_msb, neg_flags). The sub-record nesting works around a `deriving ProvableStruct` field-count cap (~25 fields max for flat-derive). **Open-question #2 CLOSED.**
- `f2fdaa3` DivRem labels: Main[241..245] cells renamed from the placeholder 3-flag scheme `(is_signed, is_w, is_rem, is_real, msb_aux1)` to the upstream Rust labels `(c_neg, abs_c_alu_event, abs_rem_alu_event, is_real, remainder_check_multiplicity)`. The orphaned `divrem_flag_projection` lemma was deleted. **`msb_aux1` Lean-only row CLOSED.**
- `73e1ca6` DivRem opcode: the opcode formula in `main` / `Assertion.main` / `FormalSpec` switched to the upstream weighted-sum form `is_div*15 + is_divu*16 + is_rem*17 + is_remu*18 + is_divw*25 + is_remw*27 + is_divuw*26 + is_remuw*28` using the 8 one-hot flags from `aux_post.mode_flags`. The soundness/completeness proof bridge uses a deepened `obtain` on the `e19` (DivRemAuxPost field-equation conjunction) to expose the mode_flags equation to `subst_eqs`; then the per-index Vector projection closes with `convert ... using 2 <;> simp only [Vector.getElem_map]`. **"DivRem 3-flag vs 8-flag encoding" DIVERGENT row CLOSED.**

---

## Summary

| Layer | Lean | Upstream matched | Upstream-only |
|---|---|---|---|
| Per-chip column structs | 24 | 24 / 24 | ~20 (`AluX0`, `Trap*`, `Syscall*`, `Global*`, `Byte*`/`Range*`, `Memory{Init,Local,Bump}`, `PageProt*`, `Instruction{,Fetch,Decode}`, `ProgramPreprocessed`) |
| Sub-operation structs | 12 + 6 (`SP1Operations/{Operation,Compare}/`) | 18 / 18 | 14 (`AndU32`, `XorU32`, `NotU32`, `AddU32`, `U32toU8`, `FixedRotate`/`FixedShift`, `Add4`, `Add5`, `Clk`, `Trap`, `SyscallAddr`, `Global{Accumulation,Interaction}`, `Page*`, `TrapPageProt`) |
| Reader / state structs | 5 (`{RType,IType,JType,ALUType}Reader`, `CPUState`) | 5 / 5 (nested into upstream chip Cols) | 0 |
| **Per-column constraint audit** (2026-05-23) | **24 / 24 chips complete** | ~480 column rows total across all chips | DIVERGENT/OPAQUE rows surfaced; 2026-05-23 sweep closed DivRem aux:209 + 3-flag/8-flag + msb_aux1 + ShiftRight intermediates_aux:28 (commits `c3aedab`, `ce4c38c`, `f2fdaa3`, `73e1ca6`). 2026-05-24 sweep closed Branch `lt_is_signed`/`is_branching` (struct rename + Spec verified), Mul Main[79..81] slot-order (commit `664f53a`), ShiftLeft Phase 2.3 decomposition (split `shift_pow→v_01/v_012/v_0123`, `limb_shift→lower_limb/higher_limb`, `result_intermediate→limb_result/sllw_msb`; rename `sign_extend→is_sllw_imm`), and Load/Store `*_memory_flag` → `MemoryAccessTimestamp.compare_low` mapping. |

All 24 RISC-V instruction chips are matched 1-1 by name. The gap is everything *around* the instruction set — privilege/trap, page protection, syscalls, lookup tables, memory bookkeeping, program/instruction decode. Roughly half of upstream by struct count is unported.

**Audit headline findings (2026-05-23, refreshed 2026-05-24).** Out of 24 chips × ~20 rows ≈ 480 column-level comparisons, the audit surfaced these structural concerns:
- ~~**Branch — `lt_is_signed` is a misnomer for `is_branching`** (slot Main[34]).~~ **CLOSED 2026-05-24** (struct rename landed + Spec verified). The Lean struct field is now `is_branching: T` at Main[34] (see `SP1Clean/BranchChip.lean:64`) with a comment trail at lines 59-71 explaining the prior misnomer. The Lean `Spec` already passes `(cols.is_blt + cols.is_bge)` as the `is_signed` argument to `LtOperationSigned.constraints` (see `SP1Clean/BranchChip.lean:118`), matching upstream's E76. The separate Clean-only `is_branching_aux: T` mux selector remains (state-bus reify); Phase 4 (TrustMode) will replace it with the renamed `is_branching` directly. Open-question #6 fully resolved.
- ~~**Mul — Main[79..81] slot-order may differ from upstream.**~~ **CLOSED 2026-05-24** (commit `664f53a Phase 1b: Mul — fix Main[79..81] slot-order to match upstream struct`). The Lean struct now matches upstream's `is_mul, is_mulh, is_mulhu, is_mulhsu, is_mulw` order (see `SP1Clean/MulChip.lean:92-96` with the comment block at 86-91 documenting the prior swap). The opcode formula at line 110 uses the corrected order.
- ~~**DivRem — 3-flag `(is_signed, is_w, is_rem)` vs upstream's 8-flag one-hot.**~~ **CLOSED 2026-05-23** (commits `f2fdaa3` + `73e1ca6`). Phase 3f surfaced the 8 one-hot mode flags at Main[201..208] as `aux_post.mode_flags : Vector T 8`; the chip's opcode formula now uses the upstream weighted-sum form. Main[241..243] were renamed from the misleading 3-flag placeholders to the upstream Rust names (`c_neg`, `abs_c_alu_event`, `abs_rem_alu_event`) and the orphaned `divrem_flag_projection` lemma was deleted.
- ~~**9 Load/Store chips — `load_memory_flag`/`store_memory_flag` (Main[35]) is not in upstream's `MemoryAccessCols<T>`.**~~ **CLOSED 2026-05-24** (audit hypothesis was wrong — it is NOT a `MemoryAccessColsU8` divergence). Upstream's `MemoryAccessTimestamp<T>` at `crates/core/machine/src/memory/consistency/columns.rs:12` declares `compare_low: T` with doc-comment *"This will be true if the top 24 bits do not match"* — a boolean witness that selects which 24-bit half of the timestamp to compare. Lean's `*_memory_flag: T` has the exact same semantics (boolean selector for the high/low 24-bit clk comparison; see `SP1Clean/LoadByteChip.lean:268-276`). Pure RENAMED mapping `*_memory_flag` ↔ `MemoryAccessTimestamp.compare_low`, no cell-count change. Open-question #7 fully resolved.

---

## Methodology

- Matched by name. Sole systematic rename: upstream uses `Columns` (not `Cols`) for memory, control-flow, and `UType*` chips — Lean uses `Cols` throughout.
- Per matched chip, the comparison is **structural**: what Lean fields correspond to which upstream nested sub-struct, with deltas called out.
- Statuses used in tables: `match`, `rename`, `type-shape mismatch` (semantically identical, e.g. `Vector T 4` ↔ `Word<T>`), `nesting mismatch` (same data, different framing), `Lean-only`, `Rust-only`.
- Not compared: constraint bodies, proofs (`Spec`, `assertion.Spec`, `soundness`, `completeness`), `SP1Chips/` (which has no field names — flat `Vector (ZMod p) N`).

---

## Audit conventions (Per-column constraint usage tables)

Added 2026-05-23. Each matched chip gains a `Per-column constraint usage` sub-table that names, for every column on each side, which constraints reference it.

**Schema.** `| Column (Lean) | Slot | Lean constraint refs | Rust column | Rust constraint refs | Status |`

- **Slot** = Vector index in `SP1Chips/<Chip>/Constraints.lean` (the auto-generated `@[irreducible] def constraints`). Use `(Lean-only)` for Lean-additions not in the bridge, `—` for Rust-only columns.
- **Lean constraint refs** = symbolic sub-operation calls in the chip's `main` / `assertion.main` (e.g. `AddOp.main`, `CPUState.assertion`, `RTypeReader.assertion`, `ProgramTable.assertion`) plus any direct `=== 0` / lookup that names the column.
- **Rust constraint refs** = `eval`-time call sites that read `local.<field>` (or `local.<sub_op>.<field>`), grouped by sub-op (`AddOperation eval`, `RTypeReader eval`, `CPUState eval`, `eval_untrusted_program`, raw `builder.assert_*` / `builder.send_*`).
- **Status tags:**
  - `EXACT` — same name (modulo language-level naming conventions), same constraint references on both sides.
  - `RENAMED` — different name, same references.
  - `FLATTENED` — Lean field inlines an upstream nested field; references match modulo the un-nest.
  - `OPAQUE` — slot inside a Lean `aux` blob; references traceable only via the bridge file. Used in DivRem and ShiftRight.
  - `DIVERGENT` — constraint reference sets actually differ. Surfaces a follow-up task. Counted at the top of the doc.

**Audit-status header.** Under each `### <Chip>` heading, the line `Constraint-usage audit: <not started | in progress | complete YYYY-MM-DD>` tracks per-chip audit state.

---

## Macro divergences (read these first)

1. **Flat vs. composed.** Every upstream chip `Cols<T, M>` is a thin 4-6-field composition: `state: CPUState<T>`, `adapter: <RType|IType|JType|ALUType>Reader<T>`, `<op>_operation: <Op>Operation<T>`, a handful of `is_*` flag bits, and `adapter_cols: M::AdapterCols<T>`. Lean inlines every one of those sub-structs into the chip's `Cols`, so our chips have 14-32 fields each. The Reader / CPUState structs *do exist* on the Lean side (`SP1Operations/Reader/`, `SP1Foundations/MemoryConsistency.lean`) — they're just not used as Cols field types.

2. **`TrustMode` (`M`) — PARTIALLY RESOLVED 2026-05-23.** Upstream parameterizes every chip Cols over an `M: TrustMode` and reserves one field `adapter_cols: M::AdapterCols<T>` for mode-dependent columns (`sp1/crates/core/machine/src/lib.rs:47-150`; user-mode payload is `UserModeReaderCols<T> { is_trusted: T }`, supervisor-mode payload is `EmptyCols<T>`). Scaffolding landed at `SP1Clean/TrustMode.lean` (TrustMode inductive, UserModeReaderCols, EmptyCols, AdapterCols selector). Each of the 24 SP1Clean chip Cols (excluding boundary `MemoryGlobalChip` — Rust doesn't parametrize that one either) now carries `adapter_cols: SP1Clean.UserModeReaderCols T` as its last field, with `cols.adapter_cols.is_trusted = 1` added as a Spec conjunct. We are still implicitly user-mode-only, but `is_trusted` is now surfaced at the chip layer rather than buried as an iff-lemma bound variable. **What's NOT yet done:** the chip Cols are not parametric over `(M : TrustMode)` because `deriving ProvableStruct` cannot reduce through an abstract `M` — a future SupervisorMode chip would use a parallel `*ColsSupervisor` struct with `adapter_cols: EmptyCols T`. `next_pc_carry_value` was separately flagged as a Clean-only artifact that "shouldn't exist at all" — its removal is its own concern, not part of this work.

3. **`Cols` vs `Columns` suffix.** ALU chips on both sides use `Cols` (`AddCols`, `SubCols`, `BitwiseCols`, `MulCols`, `DivRemCols`, `LtCols`, `ShiftLeftCols`, `ShiftRightCols`). Memory/control-flow/UType use `*Columns` upstream but `*Cols` on our side (`BranchCols` ↔ `BranchColumns`, `JalCols` ↔ `JalColumns`, `LoadByteCols` ↔ `LoadByteColumns`, etc.). Cosmetic but worth normalizing if/when we sync.

4. **`MemoryAccessCols<T>` is inlined as a 3-tuple.** Upstream wraps every register access in `MemoryAccessCols<T> { prev_value: Word<T>, access_timestamp: MemoryAccessTimestamp<T> }`. Lean inlines per operand as `op_X: T`, `op_X_memory_prev_value: Vector T 4`, `op_X_memory_prev_low: T`, `op_X_memory_diff_low: T` — i.e. each `*Reader<T>` is fully flattened to 13 fields (R-type) / 9 fields (I-type) / 4 fields (J-type) / 14 fields (ALU-type) in the chip Cols.

5. ~~**`next_pc_carry_value: Vector T 3` is Lean-only at the top of 22/24 chips.**~~ **CLOSED 2026-05-23.** Removed from all 21 chip Cols that carried it (Add, Addi, Addw, Sub, Subw, Lt, Mul, Bitwise, ShiftLeft, ShiftRight, Load{Byte,Half,Word,Double,X0}, Store{Byte,Half,Word,Double}, DivRem, UType). The per-chip `AddrAddOp.assertion` calls that constrained the column and the matching `FormalSpec` conjuncts were dropped; the trace-level chain now derives `next_pc := #v[pc[0] + 4, pc[1], pc[2]]` directly from `cols.state.pc` in `SP1Clean/Soundness/StateConsistency.lean`'s `ChipRow.stateAccess`, matching Rust's literal expression at `adapter/state.rs:75`. The 433-line `nextPc_of_spec_*` / `ChipRow.nextPcValid` / `TraceNextPcValid` infrastructure block in StateConsistency.lean (lines 364-797 of the pre-change file) was deleted as obsolete — it existed only to expose the now-deleted column as a per-row witness. `JalCols`, `JalrCols`, `BranchCols`, `MemoryGlobalCols` were not touched (they use chip-specific PC handling: `cols.next_pc`, `cols.jump_target`, `cols.next_pc_branched_carry`/`cols.next_pc_unbranched_carry`, or no PC at all for boundary chips).

6. ~~**`Branch`/`Lt` flatten `LtOperationSigned<T>`.**~~ **CLOSED 2026-05-21.** Both chips now nest the operation. `BranchCols.compare_operation : LtOperationSigned T` and `LtCols.lt_operation : LtOperationSigned T` are direct ProvableStruct-derived fields. Sidecar derivations live at `SP1Clean/Compare/LtOperationSigned.lean` (covers `U16MSBOperation`, `U16CompareOperation`, `LtOperationUnsigned`, `LtOperationSigned`). Cell count and order preserved; only `MemoryConsistency.lean:285` needed a follow-up rewrite (`cols.compare_bit` → `cols.lt_operation.result.u16_compare_operation.bit`).

7. **`Mul`/`Bitwise` flatten their `*Operation`.** `MulCols` has 9 operation fields inlined (`carry, product, b_low_bytes, c_low_bytes, b_msb, c_msb, product_msb, b_sign_extend, c_sign_extend`); upstream nests them under `mul_operation: MulOperation<T>` and also stores `a: Word<T>` separately whereas Lean keeps `op_a_write_value: Vector T 4`. `BitwiseCols` inlines `BitwiseU16Operation<T>` (3 sub-fields).

8. ~~**Two opaque `aux` blobs.**~~ **CLOSED 2026-05-23** (commits `c3aedab` Phase 3e + `ce4c38c` Phase 3f). Both chips now have every cell named per the upstream `DivRemCols<T, M>` / `ShiftRightCols<T, M>` field declaration order. `ShiftRightCols.intermediates_aux:28` became 11 named top-level fields (b_msb, srw_msb, c_bits, sra_msb_v0123, v_0123/012/01, lower_limb, higher_limb, limb_result, shift_u16). `DivRemCols.aux:209` became 10 named top-level fields for aux_pre (Main[32..75]) + 2 `MulOperation` sub-structs (Main[76..165]) + a nested `DivRemAuxPost` sub-record with 14 fields for aux_post (Main[166..240]). The nesting workaround for DivRem was forced by a `deriving ProvableStruct` field-count cap of ~25 flat fields (see [[feedback-provablestruct-field-count-limit]]). See the DivRem and ShiftRight per-chip sections for the full slot map.

9. **`ShiftLeft` decomposition disagrees.** Upstream `ShiftLeftCols`: `c_bits: [T;6], v_01, v_012, v_0123, shift_u16: [T;4], lower_limb, higher_limb, limb_result, sllw_msb`. Lean `ShiftLeftCols`: `shift_imm_low, shift_imm_high, msb, result, bit_shift: Vector T 6, shift_pow: Vector T 3, byte_shift: Vector T 4, limb_shift: Vector T 8, result_intermediate: Vector T 5, sign_extend`. Same family of computations; not the same factoring. Mapping these 1-1 will require constraint-level reading.

10. **Coverage gap is the system layer, not the ISA layer.** All 24 user-mode RISC-V instruction chips have Lean counterparts. Everything upstream that's *not* an instruction — privilege/trap, paging, syscalls, lookup tables (byte/range), memory init/local/bump, program/instruction fetch and decode, the `AluX0` x0-destination special case, the global digest — has no Lean equivalent yet. Whether to port these is a scope question, not a divergence-cleanup question.

---

## Per-chip matched diffs

In every section: upstream side shows the composed shape, then Lean side names the inlined sub-struct ranges. Status lines call out non-flatten differences. Chip files: Lean at `SP1Clean/<Chip>Chip.lean`, upstream at `../sp1/crates/core/machine/src/<dir>/<file>.rs` (paths given once per section).

### Add — `AddCols` ↔ `AddCols<T, M>`

Constraint-usage audit: complete 2026-05-23

- Upstream (5 fields, `alu/add_sub/add.rs`): `state: CPUState<T>` · `adapter: RTypeReader<T>` · `add_operation: AddOperation<T>` · `is_real: T` · `adapter_cols: M::AdapterCols<T>`
- Lean inlines to 20 fields: CPUState→4 · RTypeReader→13 · AddOperation→1 (`op_a_write_value: Vector T 4` ↔ `add_operation.value: Word<T>`) · `is_real` · `next_pc_carry_value: Vector T 3`
- Status: clean flatten. `next_pc_carry_value` lives in `adapter_cols` upstream.

**Per-column constraint usage** (audit: complete 2026-05-23)

| Column (Lean) | Slot | Lean constraint refs | Rust column | Rust constraint refs | Status |
|---|---|---|---|---|---|
| `clk_high` | Main[0] | `CPUState.constraints` (state.clk_high) · `RTypeReader.constraints` (clk_high arg) | `state.clk_high` | `CPUState eval` · `RTypeReader eval` (`local.state.clk_high::<AB>()`) | FLATTENED |
| `clk_16_24` | Main[1] | `CPUState.constraints` (state.clk_16_24) · `RTypeReader.constraints` (via `E4 = Main[2] + Main[1]*65536`) | `state.clk_16_24` | `CPUState eval` · `RTypeReader eval` (clk_low recomposition) | FLATTENED |
| `clk_0_16` | Main[2] | `CPUState.constraints` (state.clk_0_16) · `RTypeReader.constraints` (via `E4`) | `state.clk_0_16` | `CPUState eval` · `RTypeReader eval` (clk_low recomposition) | FLATTENED |
| `pc` (3 limbs) | Main[3..5] | `CPUState.constraints` (state.pc + next_pc `#v[E2, Main[4], Main[5]]`) · `RTypeReader.constraints` (pc arg) · `ProgramTable` lookup (assertion.main only) | `state.pc` | `CPUState eval` (`local.state.pc`, `pc[0]+PC_INC`) · `RTypeReader eval` (`local.state.pc`) · `eval_untrusted_program` (`local.state.pc`) | FLATTENED |
| `op_a` | Main[6] | `RTypeReader.constraints` (adapter.op_a) | `adapter.op_a` | `RTypeReader eval` (via `local.adapter`) | FLATTENED |
| `op_a_memory_prev_value` (4) | Main[7..10] | `RTypeReader.constraints` (adapter.op_a_memory.prev_value) | `adapter.op_a_memory.prev_value` (`MemoryAccessCols`) | `RTypeReader eval` | FLATTENED |
| `op_a_memory_prev_low` | Main[11] | `RTypeReader.constraints` (adapter.op_a_memory.access_timestamp.prev_low) | `adapter.op_a_memory.access_timestamp.prev_low` (`RegisterAccessTimestamp`) | `RTypeReader eval` | FLATTENED |
| `op_a_memory_diff_low` | Main[12] | `RTypeReader.constraints` (adapter.op_a_memory.access_timestamp.diff_low_limb) | `adapter.op_a_memory.access_timestamp.diff_low_limb` | `RTypeReader eval` | FLATTENED |
| `op_a_0` | Main[13] | `RTypeReader.constraints` (adapter.op_a_0) · trailing `assertZero Main[13]` | `adapter.op_a_0` | `RTypeReader eval` · raw `builder.assert_zero(local.adapter.op_a_0)` | FLATTENED |
| `op_b` | Main[14] | `RTypeReader.constraints` (adapter.op_b) | `adapter.op_b` | `RTypeReader eval` | FLATTENED |
| `op_b_memory_prev_value` (4) | Main[15..18] | `AddOperation.constraints` (b operand) · `RTypeReader.constraints` (adapter.op_b_memory.prev_value) | `adapter.op_b_memory.prev_value` | `AddOperation eval` (via `local.adapter.b()`) · `RTypeReader eval` | FLATTENED |
| `op_b_memory_prev_low` | Main[19] | `RTypeReader.constraints` (adapter.op_b_memory.access_timestamp.prev_low) | `adapter.op_b_memory.access_timestamp.prev_low` | `RTypeReader eval` | FLATTENED |
| `op_b_memory_diff_low` | Main[20] | `RTypeReader.constraints` (adapter.op_b_memory.access_timestamp.diff_low_limb) | `adapter.op_b_memory.access_timestamp.diff_low_limb` | `RTypeReader eval` | FLATTENED |
| `op_c` | Main[21] | `RTypeReader.constraints` (adapter.op_c) | `adapter.op_c` | `RTypeReader eval` | FLATTENED |
| `op_c_memory_prev_value` (4) | Main[22..25] | `AddOperation.constraints` (c operand) · `RTypeReader.constraints` (adapter.op_c_memory.prev_value) | `adapter.op_c_memory.prev_value` | `AddOperation eval` (via `local.adapter.c()`) · `RTypeReader eval` | FLATTENED |
| `op_c_memory_prev_low` | Main[26] | `RTypeReader.constraints` (adapter.op_c_memory.access_timestamp.prev_low) | `adapter.op_c_memory.access_timestamp.prev_low` | `RTypeReader eval` | FLATTENED |
| `op_c_memory_diff_low` | Main[27] | `RTypeReader.constraints` (adapter.op_c_memory.access_timestamp.diff_low_limb) | `adapter.op_c_memory.access_timestamp.diff_low_limb` | `RTypeReader eval` | FLATTENED |
| `op_a_write_value` (4) | Main[28..31] | `AddOperation.constraints` (result `{value := ...}`) · `RTypeReader.constraints` (write_value) | `add_operation.value` (`AddOperation<T>.value: Word<T>`) | `AddOperation eval` (output of `local.add_operation`) · `RTypeReader eval` (via `local.add_operation.value.map(...)`) | FLATTENED |
| `is_real` | Main[32] | `CPUState.constraints` (is_real arg) · `RTypeReader.constraints` (is_real, is_trusted) · `AddOperation.constraints` (is_real arg) · trailing `assertZero (Main[32]*(Main[32]-1))` | `is_real` | `CPUState eval` · `RTypeReader eval` · `AddOperation eval` (all take `local.is_real.into()`) · raw `builder.assert_bool(local.is_real)` · `eval_untrusted_program` (`local.is_real`) | EXACT |
| `next_pc_carry_value` (3) | (Lean-only) | `ProgramTable` interaction in trace-level state-bus (consumed by `Assertion.main` / FormalAssertion; **not** referenced by legacy `iff_sp1` `Spec`) | `adapter_cols.next_pc_carry` (inferred — user-mode `M::AdapterCols<T>` payload) | `eval_untrusted_program` reads `local.adapter_cols` (user-mode only); `is_trusted = local.adapter_cols.is_trusted` | FLATTENED (Lean lifts the user-mode adapter payload — confirms macro divergence #5) |
| _none_ | — | — | `adapter_cols` (rest of struct, e.g. `is_trusted` in user mode) | `eval_untrusted_program` · `is_trusted` flag | — (Rust-only; not surfaced in Lean — macro divergence #2: missing `TrustMode`) |

### Addi — `AddiCols` ↔ `AddiCols<T, M>`

Constraint-usage audit: complete 2026-05-23

- Upstream (5, `alu/add_sub/addi.rs`): `state` · `adapter: ITypeReader<T>` · `add_operation: AddOperation<T>` · `is_real` · `adapter_cols`
- Lean inlines to 17: CPUState→4 · ITypeReader→9 (op_a + memory triple, op_b + memory triple, op_a_0, op_c_imm: Vector T 4) · AddOperation→1 · `is_real` · `next_pc_carry_value`
- Status: clean flatten.

**Per-column constraint usage** (audit: complete 2026-05-23)

| Column (Lean) | Slot | Lean constraint refs | Rust column | Rust constraint refs | Status |
|---|---|---|---|---|---|
| `clk_high` | Main[0] | `CPUState.constraints` · `ITypeReader.constraints` (clk_high arg) | `state.clk_high` | `CPUState eval` · `ITypeReader eval` | FLATTENED |
| `clk_16_24` | Main[1] | `CPUState.constraints` · `ITypeReader.constraints` (via `E4 = Main[2] + Main[1]*65536`) | `state.clk_16_24` | `CPUState eval` · `ITypeReader eval` | FLATTENED |
| `clk_0_16` | Main[2] | `CPUState.constraints` · `ITypeReader.constraints` (via `E4`) | `state.clk_0_16` | `CPUState eval` · `ITypeReader eval` | FLATTENED |
| `pc` (3) | Main[3..5] | `CPUState.constraints` (state.pc + next_pc `#v[E2, Main[4], Main[5]]`) · `ITypeReader.constraints` · `ProgramTable` lookup (assertion.main) | `state.pc` | `CPUState eval` · `ITypeReader eval` · `eval_untrusted_program` | FLATTENED |
| `op_a` | Main[6] | `ITypeReader.constraints` (adapter.op_a) | `adapter.op_a` | `ITypeReader eval` | FLATTENED |
| `op_a_memory_prev_value` (4) | Main[7..10] | `ITypeReader.constraints` (adapter.op_a_memory.prev_value) | `adapter.op_a_memory.prev_value` | `ITypeReader eval` | FLATTENED |
| `op_a_memory_prev_low` | Main[11] | `ITypeReader.constraints` (adapter.op_a_memory.access_timestamp.prev_low) | `adapter.op_a_memory.access_timestamp.prev_low` | `ITypeReader eval` | FLATTENED |
| `op_a_memory_diff_low` | Main[12] | `ITypeReader.constraints` (adapter.op_a_memory.access_timestamp.diff_low_limb) | `adapter.op_a_memory.access_timestamp.diff_low_limb` | `ITypeReader eval` | FLATTENED |
| `op_a_0` | Main[13] | `ITypeReader.constraints` (adapter.op_a_0) · trailing `assertZero Main[13]` | `adapter.op_a_0` | `ITypeReader eval` · raw `builder.assert_zero(local.adapter.op_a_0)` | FLATTENED |
| `op_b` | Main[14] | `ITypeReader.constraints` (adapter.op_b) | `adapter.op_b` | `ITypeReader eval` | FLATTENED |
| `op_b_memory_prev_value` (4) | Main[15..18] | `AddOperation.constraints` (b operand) · `ITypeReader.constraints` (adapter.op_b_memory.prev_value) | `adapter.op_b_memory.prev_value` | `AddOperation eval` (via `local.adapter.b()`) · `ITypeReader eval` | FLATTENED |
| `op_b_memory_prev_low` | Main[19] | `ITypeReader.constraints` (adapter.op_b_memory.access_timestamp.prev_low) | `adapter.op_b_memory.access_timestamp.prev_low` | `ITypeReader eval` | FLATTENED |
| `op_b_memory_diff_low` | Main[20] | `ITypeReader.constraints` (adapter.op_b_memory.access_timestamp.diff_low_limb) | `adapter.op_b_memory.access_timestamp.diff_low_limb` | `ITypeReader eval` | FLATTENED |
| `op_c_imm` (4) | Main[21..24] | `AddOperation.constraints` (c operand — immediate) · `ITypeReader.constraints` (adapter.op_c_imm) · 4× `ByteOpcodeTable` Range(16) lookups in `main` (per-limb byte bound) | `adapter.op_c_imm` (`[T;4]` field of `ITypeReader<T>`) | `AddOperation eval` (via `local.adapter.c()` — for ITypeReader, returns the imm limbs) · `ITypeReader eval` (emits the four byte-range lookups internally) | FLATTENED |
| `op_a_write_value` (4) | Main[25..28] | `AddOperation.constraints` (result) · `ITypeReader.constraints` (write_value) | `add_operation.value` | `AddOperation eval` (output) · `ITypeReader eval` (via `local.add_operation.value.map(...)`) | FLATTENED |
| `is_real` | Main[29] | `CPUState.constraints` · `ITypeReader.constraints` (is_real, is_trusted) · `AddOperation.constraints` (is_real arg) · trailing `assertZero (Main[29]*(Main[29]-1))` | `is_real` | `CPUState eval` · `ITypeReader eval` · `AddOperation eval` · raw `builder.assert_bool(local.is_real)` · `eval_untrusted_program` | EXACT |
| `next_pc_carry_value` (3) | (Lean-only) | `ProgramTable` interaction in trace-level state-bus (consumed by `Assertion.main`; not by legacy `iff_sp1`) | `adapter_cols.next_pc_carry` (inferred — user-mode `M::AdapterCols<T>`) | `eval_untrusted_program` reads `local.adapter_cols` | FLATTENED (macro divergence #5) |
| _none_ | — | — | `adapter_cols` (rest, e.g. `is_trusted`) | `eval_untrusted_program` · `is_trusted` flag | — (Rust-only; macro divergence #2) |

### Addw — `AddwCols` ↔ `AddwCols<T, M>`

Constraint-usage audit: complete 2026-05-23

- Upstream (5, `alu/add_sub/addw.rs`): `state` · `adapter: ALUTypeReader<T>` · `addw_operation: AddwOperation<T>` · `is_real` · `adapter_cols`
- Lean inlines to 22: CPUState→4 · ALUTypeReader→14 (op_a, op_b, op_c with `op_c: Vector T 4`, `imm_c: T`, three memory triples) · AddwOperation→2 (`addw_value: Vector T 2` + `addw_msb: T` ↔ `value` + `msb: U16MSBOperation<T>`) · `is_real` · `next_pc_carry_value`
- Status: clean flatten. Note Lean stores `addw_msb: T` where upstream nests `msb: U16MSBOperation<T>` (a 1-field struct over `msb: T`) — same single bit either way.

**Per-column constraint usage** (audit: complete 2026-05-23)

| Column (Lean) | Slot | Lean constraint refs | Rust column | Rust constraint refs | Status |
|---|---|---|---|---|---|
| `clk_high` | Main[0] | `CPUState.constraints` · `ALUTypeReader.constraints` (clk_high arg) | `state.clk_high` | `CPUState eval` · `ALUTypeReader eval` | FLATTENED |
| `clk_16_24` | Main[1] | `CPUState.constraints` · `ALUTypeReader.constraints` (via `E10 = Main[2] + Main[1]*65536`) | `state.clk_16_24` | `CPUState eval` · `ALUTypeReader eval` | FLATTENED |
| `clk_0_16` | Main[2] | `CPUState.constraints` · `ALUTypeReader.constraints` · `SP1Clean.CPUState.assertion` (subcircuit in `main`) | `state.clk_0_16` | `CPUState eval` · `ALUTypeReader eval` | FLATTENED |
| `pc` (3) | Main[3..5] | `CPUState.constraints` (state.pc + next_pc) · `ALUTypeReader.constraints` · `ProgramTable.assertion` | `state.pc` | `CPUState eval` · `ALUTypeReader eval` · `eval_untrusted_program` | FLATTENED |
| `op_a` | Main[6] | `ALUTypeReader.constraints` (adapter.op_a) | `adapter.op_a` | `ALUTypeReader eval` | FLATTENED |
| `op_a_memory_prev_value` (4) | Main[7..10] | `ALUTypeReader.constraints` | `adapter.op_a_memory.prev_value` | `ALUTypeReader eval` | FLATTENED |
| `op_a_memory_prev_low` | Main[11] | `ALUTypeReader.constraints` | `adapter.op_a_memory.access_timestamp.prev_low` | `ALUTypeReader eval` | FLATTENED |
| `op_a_memory_diff_low` | Main[12] | `ALUTypeReader.constraints` | `adapter.op_a_memory.access_timestamp.diff_low_limb` | `ALUTypeReader eval` | FLATTENED |
| `op_a_0` | Main[13] | `ALUTypeReader.constraints` (adapter.op_a_0) · trailing `assertZero Main[13]` | `adapter.op_a_0` | `ALUTypeReader eval` · `builder.assert_zero` | FLATTENED |
| `op_b` | Main[14] | `ALUTypeReader.constraints` (adapter.op_b) | `adapter.op_b` | `ALUTypeReader eval` | FLATTENED |
| `op_b_memory_prev_value` (4) | Main[15..18] | `AddwOperation.constraints` (b operand) · `ALUTypeReader.constraints` | `adapter.op_b_memory.prev_value` | `AddwOperation eval` (via `local.adapter.b()`) · `ALUTypeReader eval` | FLATTENED |
| `op_b_memory_prev_low` | Main[19] | `ALUTypeReader.constraints` | `adapter.op_b_memory.access_timestamp.prev_low` | `ALUTypeReader eval` | FLATTENED |
| `op_b_memory_diff_low` | Main[20] | `ALUTypeReader.constraints` | `adapter.op_b_memory.access_timestamp.diff_low_limb` | `ALUTypeReader eval` | FLATTENED |
| `op_c` (4) | Main[21..24] | `ALUTypeReader.constraints` (adapter.op_c — 4 limbs; reader gates the imm-vs-reg dispatch via `imm_c`) | `adapter.op_c` (`[T;4]`) | `ALUTypeReader eval` (op_c is 4 limbs that may be a 1-limb register index zero-padded OR a 4-limb immediate) | FLATTENED |
| `op_c_memory_prev_value` (4) | Main[25..28] | `AddwOperation.constraints` (c operand — for ALUTypeReader this is the register memory side, used only when `imm_c=0`) · `ALUTypeReader.constraints` | `adapter.op_c_memory.prev_value` | `AddwOperation eval` (via `local.adapter.c()`) · `ALUTypeReader eval` | FLATTENED |
| `op_c_memory_prev_low` | Main[29] | `ALUTypeReader.constraints` | `adapter.op_c_memory.access_timestamp.prev_low` | `ALUTypeReader eval` | FLATTENED |
| `op_c_memory_diff_low` | Main[30] | `ALUTypeReader.constraints` | `adapter.op_c_memory.access_timestamp.diff_low_limb` | `ALUTypeReader eval` | FLATTENED |
| `imm_c` | Main[31] | `ALUTypeReader.constraints` (adapter.imm_c — R/I-type selector) · `ProgramTable.assertion` (`imm_c` arg) | `adapter.imm_c` | `ALUTypeReader eval` (selector inside reader) · `eval_untrusted_program` | FLATTENED |
| `addw_value` (2) | Main[32..33] | `AddwOperation.constraints` (output `.value: Vector T 2`) · `ALUTypeReader.constraints` (write_value low 2 limbs) | `addw_operation.value` (`[T; WORD_SIZE/2]`) | `AddwOperation eval` · `ALUTypeReader eval` | FLATTENED |
| `addw_msb` | Main[34] | `AddwOperation.constraints` (output `.msb.msb`) · `ALUTypeReader.constraints` (write_value high 2 = `addw_msb * 65535`) | `addw_operation.msb.msb` | `AddwOperation eval` · `ALUTypeReader eval` | FLATTENED (Lean stores `T`; upstream nests `U16MSBOperation<T>`) |
| `is_real` | Main[35] | `CPUState.constraints` · `ALUTypeReader.constraints` · `AddwOperation.constraints` · trailing `assertZero (Main[35]*(Main[35]-1))` | `is_real` | `CPUState eval` · `ALUTypeReader eval` · `AddwOperation eval` · `builder.assert_bool` | EXACT |
| `next_pc_carry_value` (3) | (Lean-only) | trace-level `ProgramTable` | `adapter_cols.next_pc_carry` | `eval_untrusted_program` | FLATTENED (macro #5) |
| _none_ | — | — | `adapter_cols` (rest) | `eval_untrusted_program` | — (Rust-only; macro #2) |
|
> Opcode literal in `ALUTypeReader.constraints` is `19` (ADDW). Write-value reconstruction: `#v[Main[32], Main[33], Main[34]*65535, Main[34]*65535]`.

### Sub — `SubCols` ↔ `SubCols<T, M>`

Constraint-usage audit: complete 2026-05-23

- Upstream (5, `alu/add_sub/sub.rs`): `state` · `adapter: RTypeReader<T>` · `sub_operation: SubOperation<T>` · `is_real` · `adapter_cols`
- Lean inlines to 20 (same shape as Add). Status: clean flatten.

**Per-column constraint usage** (audit: complete 2026-05-23)

> Identical to the **Add** table above modulo two deltas; no column-level differences in slot mapping or constraint-reference sets.
>
> - `add_operation` → `sub_operation` (verb-rename of the operation fragment; the slot range Main[15..18] / Main[22..25] / Main[28..31] is unchanged).
> - Opcode literal flowing into `RTypeReader.constraints` is `2` (SUB) instead of `0` (ADD). Rust `eval` likewise passes `Opcode::SUB`.
> - Lean `Spec` invokes `SP1Clean.SubOp.Spec` instead of `SP1Clean.AddOp.Spec`; Rust uses `local.sub_operation` instead of `local.add_operation`.

### Subw — `SubwCols` ↔ `SubwCols<T, M>`

Constraint-usage audit: complete 2026-05-23

- Upstream (5, `alu/add_sub/subw.rs`): `state` · `adapter: RTypeReader<T>` · `subw_operation: SubwOperation<T>` · `is_real` · `adapter_cols`
- Lean inlines to 21: CPUState→4 · RTypeReader→13 · SubwOperation→2 (`subw_value: Vector T 2`, `subw_msb: T`) · `is_real` · `next_pc_carry_value`
- Status: clean flatten. **Adapter mismatch noted**: Lean's `SubwCols` carries 13 R-type-shaped fields with `op_c: T` (R-type), but upstream uses `RTypeReader<T>`. This matches Lean. Contrast with `Addw` which uses `ALUTypeReader` upstream and Lean encodes `op_c: Vector T 4` + `imm_c: T`. Verify that `SubwChip` really wants R-type (no immediate variant) — Addw and Subw asymmetry is worth checking against the SP1 instruction set tables.

**Per-column constraint usage** (audit: complete 2026-05-23)

> Slots `Main[0..27]` match the **Sub** table 1-1 (clk/pc/op_a + reader memory triples). Deltas are at the operation tail:

| Column (Lean) | Slot | Lean constraint refs | Rust column | Rust constraint refs | Status |
|---|---|---|---|---|---|
| `Main[0..27]` (clk_high … op_c_memory_diff_low) | Main[0..27] | as Sub | as Sub | as Sub | FLATTENED (see Sub) |
| `subw_value` (2) | Main[28..29] | `SubwOperation.constraints` (output `.value: Vector T 2`) · `RTypeReader.constraints` (write_value, low 2 limbs) | `subw_operation.value` (`SubwOperation<T>.value: [T; WORD_SIZE/2]`) | `SubwOperation eval` · `RTypeReader eval` (via `local.subw_operation.value.map(...)`) | FLATTENED |
| `subw_msb` | Main[30] | `SubwOperation.constraints` (output `.msb.msb`) · `RTypeReader.constraints` (write_value high 2 limbs = `subw_msb * 65535`) | `subw_operation.msb.msb` (`U16MSBOperation<T>.msb`) | `SubwOperation eval` · `RTypeReader eval` (sign-extend via `msb * 65535`) | FLATTENED (Lean stores `T`; upstream nests `U16MSBOperation<T>` 1-field struct — same single bit) |
| `is_real` | Main[31] | `CPUState.constraints` · `RTypeReader.constraints` · `SubwOperation.constraints` · trailing `assertZero (Main[31]*(Main[31]-1))` | `is_real` | `CPUState eval` · `RTypeReader eval` · `SubwOperation eval` · `builder.assert_bool` | EXACT |
| `next_pc_carry_value` (3) | (Lean-only) | trace-level `ProgramTable` | `adapter_cols.next_pc_carry` | `eval_untrusted_program` | FLATTENED (macro #5) |
| _none_ | — | — | `adapter_cols` (rest) | `eval_untrusted_program` | — (Rust-only; macro #2) |
|
> Opcode literal in `RTypeReader.constraints` is `20` (SUBW). Rust `eval` uses `Opcode::SUBW`. Write-value reconstruction passed to `RTypeReader`: `#v[Main[28], Main[29], Main[30]*65535, Main[30]*65535]` (i.e. low 2 limbs from `subw_value`, high 2 limbs sign-extended from `subw_msb`).

### Bitwise — `BitwiseCols` ↔ `BitwiseCols<T, M>`

Constraint-usage audit: complete 2026-05-23

- Upstream (7, `alu/bitwise/mod.rs`): `state` · `adapter: ALUTypeReader<T>` · `bitwise_operation: BitwiseU16Operation<T>` · `is_xor, is_or, is_and` · `adapter_cols`
- Lean (25): CPUState→4 · ALUTypeReader→14 · BitwiseU16Operation→3 inlined (`b_low_bytes: Vector T 4, c_low_bytes: Vector T 4, bitwise_result: Vector T 8`) · `is_xor, is_or, is_and` · `next_pc_carry_value`
- Status: nesting mismatch — Lean flattens `BitwiseU16Operation`'s three sub-operations (`b_low_bytes: U16toU8Operation<T>` → `Vector T 4`, ditto `c_low_bytes`, `bitwise_operation.result: [T;8]` → `bitwise_result`). Same data, three named tuples vs. one nested op.

**Per-column constraint usage** (audit: complete 2026-05-23)

| Column (Lean) | Slot | Lean constraint refs | Rust column | Rust constraint refs | Status |
|---|---|---|---|---|---|
| `Main[0..20]` (clk_high … op_b_memory_diff_low) | Main[0..20] | as Addw rows 1-13 (CPUState + ALUTypeReader on op_a + op_b register/memory) | as Addw | as Addw | FLATTENED (see Addw) |
| `op_c` (4) | Main[21..24] | `ALUTypeReader.constraints` (adapter.op_c — gates imm-vs-reg via `imm_c`) · `ProgramTable.assertion` | `adapter.op_c` (`[T;4]`) | `ALUTypeReader eval` · `eval_untrusted_program` | FLATTENED |
| `op_c_memory_prev_value` (4) | Main[25..28] | `BitwiseU16Operation.constraints` (c operand) · `ALUTypeReader.constraints` (adapter.op_c_memory.prev_value) | `adapter.op_c_memory.prev_value` | `BitwiseU16Operation eval` (via `local.adapter.c()`) · `ALUTypeReader eval` | FLATTENED |
| `op_c_memory_prev_low` | Main[29] | `ALUTypeReader.constraints` | `adapter.op_c_memory.access_timestamp.prev_low` | `ALUTypeReader eval` | FLATTENED |
| `op_c_memory_diff_low` | Main[30] | `ALUTypeReader.constraints` | `adapter.op_c_memory.access_timestamp.diff_low_limb` | `ALUTypeReader eval` | FLATTENED |
| `imm_c` | Main[31] | `ALUTypeReader.constraints` (R/I selector) · `ProgramTable.assertion` · used as scaling factor in many bridge E-expressions | `adapter.imm_c` | `ALUTypeReader eval` · `eval_untrusted_program` | FLATTENED |
| `b_low_bytes` (4) | Main[32..35] | `BitwiseU16Operation.constraints` (sub-fragment `b_low_bytes: U16toU8Operation.low_bytes`) | `bitwise_operation.b_low_bytes.low_bytes` (`U16toU8Operation<T>`'s `low_bytes: [T;4]`) | `BitwiseU16Operation eval` | FLATTENED (Lean inlines the inner `U16toU8Operation` to `Vector T 4`; macro divergence #7) |
| `c_low_bytes` (4) | Main[36..39] | `BitwiseU16Operation.constraints` (sub-fragment `c_low_bytes`) | `bitwise_operation.c_low_bytes.low_bytes` | `BitwiseU16Operation eval` | FLATTENED |
| `bitwise_result` (8) | Main[40..47] | `BitwiseU16Operation.constraints` (output `bitwise_operation.result: [T;8]` 8 byte limbs) · `ALUTypeReader.constraints` (write_value = first 4 bytes packed into 2 u16 limbs via E44..E47) | `bitwise_operation.result` (`[T; WORD_BYTE_SIZE = 8]`) | `BitwiseU16Operation eval` · `ALUTypeReader eval` | FLATTENED |
| `is_xor` | Main[48] | `BitwiseU16Operation.constraints` (E14 = `is_xor*2`) · `ProgramTable.assertion` (E19 = `is_xor*3 + is_or*4 + is_and*5`) · trailing `assertZero (is_xor*(is_xor-1))` · contributes to aggregate is_real = sum | `is_xor` | `BitwiseU16Operation eval` · `eval_untrusted_program` · `builder.assert_bool(local.is_xor)` | EXACT |
| `is_or` | Main[49] | as `is_xor` (selector weight 1 in op-code; weight 4 in opcode mux) | `is_or` | as `is_xor` | EXACT |
| `is_and` | Main[50] | as `is_xor` (selector weight 0 in op-code; weight 5 in opcode mux) | `is_and` | as `is_xor` | EXACT |
| (computed) is_real = `is_xor + is_or + is_and` | (no slot) | trailing `assertZero (sum * (sum - 1))` (E9) gates one-hot | (no analogue) | — Rust uses `local.is_xor + local.is_or + local.is_and` as the is_real expr inline; no dedicated `is_real` column | — (Lean and Rust both compute via sum; no column on either side) |
| `next_pc_carry_value` (3) | (Lean-only) | `AddrAddOp.assertion` (in `main` — pc + 4 carry-aware compute) · trace-level `ProgramTable` | `adapter_cols.next_pc_carry` | `eval_untrusted_program` | FLATTENED (macro #5) |
| _none_ | — | — | `adapter_cols` (rest) | `eval_untrusted_program` | — (Rust-only; macro #2) |

### Lt — `LtCols` ↔ `LtCols<T, M>`

Constraint-usage audit: complete 2026-05-23

- Upstream (6, `alu/lt/mod.rs`): `state` · `adapter: ALUTypeReader<T>` · `is_slt, is_sltu` · `lt_operation: LtOperationSigned<T>` · `adapter_cols`
- Lean (22): CPUState→4 · ALUTypeReader→14 · `is_slt, is_sltu` · `lt_operation: LtOperationSigned T` (nested) · `next_pc_carry_value`
- Status: nesting parity for `lt_operation`. `LtOperationSigned`, `LtOperationUnsigned`, `U16CompareOperation`, `U16MSBOperation` get sidecar `deriving instance ProvableStruct` in `SP1Clean/Compare/LtOperationSigned.lean`. Remaining divergence: ALUTypeReader still inlined (14 fields vs 1 nested upstream); `next_pc_carry_value` still Lean-only.

**Per-column constraint usage** (audit: complete 2026-05-23)

| Column (Lean) | Slot | Lean constraint refs | Rust column | Rust constraint refs | Status |
|---|---|---|---|---|---|
| `Main[0..31]` (clk_high … imm_c) | Main[0..31] | as Bitwise rows 1-12 (CPUState + ALUTypeReader on op_a / op_b register & memory + op_c (4 limbs) + op_c_memory triple + imm_c selector) | as Bitwise | as Bitwise | FLATTENED (see Bitwise) |
| `is_slt` | Main[32] | `LtOperationSigned.constraints` (is_signed arg = `is_slt` only; sltu doesn't sign-extend) · `ProgramTable.assertion` (opcode mux `is_slt*9 + is_sltu*10`) · trailing `assertZero (is_slt*(is_slt-1))` · contributes to is_real sum | `is_slt` | `LtOperationSigned eval` (passed as `local.is_slt`) · `eval_untrusted_program` · `builder.assert_bool(local.is_slt)` | EXACT |
| `is_sltu` | Main[33] | as `is_slt` (selector weight 10 in opcode mux; not in is_signed arg) | `is_sltu` | as `is_slt` | EXACT |
| `lt_operation.result.u16_compare_operation.bit` | Main[34] | `LtOperationSigned.constraints` (nested `compare_operation` field; produces the boolean comparison output) · `ALUTypeReader.constraints` (write_value = `#v[E29, 0, 0, 0]` where `E29 = 0 + Main[34]` — i.e. the bit is written into op_a's low limb) | `lt_operation.result.u16_compare_operation.bit` | `LtOperationSigned eval` · `ALUTypeReader eval` (via write_value) | EXACT (nested field name preserved 1-1) |
| `lt_operation.result.u16_flags` (4) | Main[35..38] | `LtOperationSigned.constraints` (4-limb compare flag witness) | `lt_operation.result.u16_flags` (`[T;4]`) | `LtOperationSigned eval` | EXACT |
| `lt_operation.result.not_eq_inv` | Main[39] | `LtOperationSigned.constraints` (not-equal inverse witness for one-shot inequality) | `lt_operation.result.not_eq_inv` | `LtOperationSigned eval` | EXACT |
| `lt_operation.result.comparison_limbs` (2) | Main[40..41] | `LtOperationSigned.constraints` (2-limb comparison-amount witness) | `lt_operation.result.comparison_limbs` (`[T;2]`) | `LtOperationSigned eval` | EXACT |
| `lt_operation.b_msb.msb` | Main[42] | `LtOperationSigned.constraints` (b operand MSB bit; nested `U16MSBOperation<T>.msb`) | `lt_operation.b_msb.msb` | `LtOperationSigned eval` (inner `U16MSBOperation`) | EXACT |
| `lt_operation.c_msb.msb` | Main[43] | as `b_msb.msb` for c operand | `lt_operation.c_msb.msb` | as `b_msb.msb` | EXACT |
| `next_pc_carry_value` (3) | (Lean-only) | trace-level `ProgramTable` | `adapter_cols.next_pc_carry` | `eval_untrusted_program` | FLATTENED (macro #5) |
| _none_ | — | — | `adapter_cols` (rest) | `eval_untrusted_program` | — (Rust-only; macro #2) |
|
> Notable: Lt is the **first chip with a fully nested sub-operation** (macro divergence #6 closed). The `lt_operation: LtOperationSigned T` Lean field nests `U16MSBOperation`, `U16CompareOperation`, `LtOperationUnsigned` via `ProvableStruct` sidecar derivations. Slot mapping is a direct 1-1 with no flattening at the operation level — only the outer ALUTypeReader is still flat.

### Branch — `BranchCols` ↔ `BranchColumns<T, M>`

Constraint-usage audit: complete 2026-05-23

- Upstream (10, `control_flow/branch/columns.rs`): `state` · `adapter: ITypeReader<T>` · `next_pc: [T;3]` · `is_beq, is_bne, is_blt, is_bge, is_bltu, is_bgeu, is_branching` · `compare_operation: LtOperationSigned<T>` · `adapter_cols`
- Lean (23): CPUState→4 · ITypeReader→9 · `next_pc: Vector T 3` · `is_beq, is_bne, is_blt, is_bge, is_bltu, is_bgeu` · `lt_is_signed` · `compare_operation: LtOperationSigned T` (nested) — **Lean lacks `is_branching: T`** and **gains `lt_is_signed: T`** (which is upstream-derivable: `is_blt + is_bge`).
- Status: nesting parity for `compare_operation`. Sidecar derivations live in `SP1Clean/Compare/LtOperationSigned.lean`. Remaining divergence: ITypeReader still inlined; Lean-only `lt_is_signed` and Rust-only `is_branching` are open questions (#6 in this doc) — orthogonal to the nesting refactor.

**Per-column constraint usage** (audit: complete 2026-05-23)

| Column (Lean) | Slot | Lean constraint refs | Rust column | Rust constraint refs | Status |
|---|---|---|---|---|---|
| `clk_high` | Main[0] | `CPUState.constraints` · `ITypeReaderImmutable.constraints` | `state.clk_high` | `CPUState eval` · `ITypeReader eval` | FLATTENED |
| `clk_16_24` | Main[1] | as Add (CPUState + reader clk_low) · `SP1Clean.CPUState.assertion` in `main` | `state.clk_16_24` | `CPUState eval` · `ITypeReader eval` | FLATTENED |
| `clk_0_16` | Main[2] | as `clk_16_24` | `state.clk_0_16` | as `clk_16_24` | FLATTENED |
| `pc` (3) | Main[3..5] | `CPUState.constraints` · `ITypeReaderImmutable.constraints` · `ProgramTable.assertion` · used in 17 trailing assertZeros (PC + op_c_imm = next_pc carry chain) | `state.pc` | `CPUState eval` · `ITypeReader eval` · `eval_untrusted_program` · raw next_pc arithmetic in eval | FLATTENED |
| `op_a` | Main[6] | `ITypeReaderImmutable.constraints` (adapter.op_a) · `ProgramTable.assertion` | `adapter.op_a` | `ITypeReader eval` | FLATTENED |
| `op_a_memory_prev_value` (4) | Main[7..10] | `ITypeReaderImmutable.constraints` · `LtOperationSigned.constraints` (b operand = op_a's memory value — Branch compares op_a to op_b) | `adapter.op_a_memory.prev_value` | `ITypeReader eval` · `LtOperationSigned eval` (via `local.adapter.a()`) | FLATTENED |
| `op_a_memory_prev_low` | Main[11] | `ITypeReaderImmutable.constraints` | `adapter.op_a_memory.access_timestamp.prev_low` | `ITypeReader eval` | FLATTENED |
| `op_a_memory_diff_low` | Main[12] | `ITypeReaderImmutable.constraints` | `adapter.op_a_memory.access_timestamp.diff_low_limb` | `ITypeReader eval` | FLATTENED |
| `op_a_0` | Main[13] | `ITypeReaderImmutable.constraints` · `ProgramTable.assertion` (op_a_0 arg) | `adapter.op_a_0` | `ITypeReader eval` | FLATTENED |
| `op_b` | Main[14] | `ITypeReaderImmutable.constraints` (adapter.op_b) | `adapter.op_b` | `ITypeReader eval` | FLATTENED |
| `op_b_memory_prev_value` (4) | Main[15..18] | `ITypeReaderImmutable.constraints` · `LtOperationSigned.constraints` (c operand = op_b's memory value) | `adapter.op_b_memory.prev_value` | `ITypeReader eval` · `LtOperationSigned eval` (via `local.adapter.b()`) | FLATTENED |
| `op_b_memory_prev_low` | Main[19] | `ITypeReaderImmutable.constraints` | `adapter.op_b_memory.access_timestamp.prev_low` | `ITypeReader eval` | FLATTENED |
| `op_b_memory_diff_low` | Main[20] | `ITypeReaderImmutable.constraints` | `adapter.op_b_memory.access_timestamp.diff_low_limb` | `ITypeReader eval` | FLATTENED |
| `op_c_imm` (4) | Main[21..24] | `ITypeReaderImmutable.constraints` (adapter.op_c_imm — branch offset) · `ProgramTable.assertion` · used in 12 trailing assertZeros (next_pc carry chain: `pc + op_c_imm = next_pc` when branching) | `adapter.op_c_imm` | `ITypeReader eval` · `eval_untrusted_program` · raw next_pc carry chain in eval | FLATTENED |
| `next_pc` (3) | Main[25..27] | `CPUState.constraints` (next_pc arg) · trailing assertZeros E103, E110, E117 (`Main[34] * carry_witness = 0` for branched arm) and E132, E140, E148 (`(is_real - Main[34]) * carry_witness = 0` for unbranched arm) | `next_pc` (`[T;3]`) | `CPUState eval` (next_pc arg) · raw next_pc validity constraints | FLATTENED |
| `is_beq` | Main[28] | `ProgramTable.assertion` (opcode mux E29 = `is_beq*40 + ...`) · trailing `assertZero (is_beq*(is_beq-1))` · used in E81 = `is_beq * (1 - sum(u16_flags))` (BEQ takes when ALL equal) | `is_beq` | `eval_untrusted_program` · `builder.assert_bool` | EXACT |
| `is_bne` | Main[29] | as `is_beq` (E84 = `is_bne * sum(u16_flags)`; BNE takes when NOT equal) | `is_bne` | as `is_beq` | EXACT |
| `is_blt` | Main[30] | as `is_beq` (E76 = `is_blt + is_bge` is the `is_signed` arg to LtOperationSigned · E91 = `(is_blt + is_bltu) * bit`; BLT takes when LtOp bit = 1) | `is_blt` | `LtOperationSigned eval` (is_signed arg) · `eval_untrusted_program` · `builder.assert_bool` | EXACT |
| `is_bge` | Main[31] | as `is_blt` (E76 + E88 = `(is_bge + is_bgeu) * (1 - bit)`; BGE takes when LtOp bit = 0) | `is_bge` | as `is_blt` | EXACT |
| `is_bltu` | Main[32] | as `is_beq` (E88 with `is_bge + is_bgeu` ↦ NOT signed; BLTU takes when unsigned lt) | `is_bltu` | as `is_beq` | EXACT |
| `is_bgeu` | Main[33] | as `is_beq` | `is_bgeu` | as `is_beq` | EXACT |
| `lt_is_signed` | Main[34] | E94 = `Main[34]*(Main[34]-1)` boolean · E96 = `is_real * (Main[34] - E92)` where E92 is the **computed is_branching** value (i.e. Main[34] = is_branching under is_real = 1) · `Spec` passes `cols.lt_is_signed` as `is_signed` arg to `LtOperationSigned.constraints` | `is_branching` | raw `builder.assert_bool(local.is_branching)` · constraints forcing `is_branching = (compare result based on opcode flags)` · NOT passed to LtOperationSigned (Rust passes `local.is_blt + local.is_bge` as is_signed there) | **DIVERGENT — slot semantic mismatch.** Main[34] (the constraint compiler's emission) is upstream's `is_branching` column (forced equal to E92 = branch-taken predicate under is_real). The Lean struct names it `lt_is_signed`, and the Lean `Spec` then passes it to `LtOperationSigned.constraints` as the `is_signed` argument — semantically wrong (is_signed should be `is_blt + is_bge`). Resolves open-question #6: **`lt_is_signed` is a misnomer for `is_branching`**. The Lean Spec's misuse may be masked by other constraints, but the field name should be fixed. |
| `compare_operation.result.u16_compare_operation.bit` | Main[35] | `LtOperationSigned.constraints` (nested) | `compare_operation.result.u16_compare_operation.bit` | `LtOperationSigned eval` | EXACT |
| `compare_operation.result.u16_flags` (4) | Main[36..39] | `LtOperationSigned.constraints` | `compare_operation.result.u16_flags` | `LtOperationSigned eval` | EXACT |
| `compare_operation.result.not_eq_inv` | Main[40] | `LtOperationSigned.constraints` | `compare_operation.result.not_eq_inv` | `LtOperationSigned eval` | EXACT |
| `compare_operation.result.comparison_limbs` (2) | Main[41..42] | `LtOperationSigned.constraints` | `compare_operation.result.comparison_limbs` | `LtOperationSigned eval` | EXACT |
| `compare_operation.b_msb.msb` | Main[43] | `LtOperationSigned.constraints` (nested `U16MSBOperation`) | `compare_operation.b_msb.msb` | `LtOperationSigned eval` | EXACT |
| `compare_operation.c_msb.msb` | Main[44] | `LtOperationSigned.constraints` | `compare_operation.c_msb.msb` | `LtOperationSigned eval` | EXACT |
| `is_branching` | (Lean-only — no slot in bridge) | (referenced only by trace-level state-bus reify; not in Lean `main` or `Spec`) | (would correspond to Main[34] if both used the same name; Rust **does** have an `is_branching` column at this slot, but Lean reuses the slot for `lt_is_signed`) | — | **DIVERGENT (Lean-only column added beyond the bridge to host state-bus next_pc selection logic; semantically distinct from the slot-34 `is_branching` upstream).** |
| `next_pc_branched_carry` (3) | (Lean-only) | trace-level `ProgramTable` state-bus (branched arm: `pc + op_c_imm` carry-aware) | (no analogue — upstream computes next_pc in eval without dedicated carry columns) | — | DIVERGENT (Clean-only state-bus reify infrastructure) |
| `next_pc_unbranched_carry` (3) | (Lean-only) | trace-level state-bus (unbranched arm: `pc + 4` carry-aware) | (no analogue) | — | DIVERGENT (Clean-only) |
|
> **Branch surfaces the biggest cluster of DIVERGENT rows in the audit.** Open-question #6 resolves with a more uncomfortable answer than expected: Lean's `lt_is_signed` at Main[34] is the constraint compiler's emission of upstream's `is_branching`. The Lean field is named wrong AND used wrong in `Spec` (passed as `is_signed` to LtOperationSigned). The `is_branching` field that Lean *does* declare (post-Main[44]) is a Clean-only state-bus column with no bridge slot — i.e. distinct from upstream's `is_branching`. Verify by reading the constraint compiler output's column-name reflection (commit `0934db280 feat: add struct reflection to access the air column names` in `../sp1`).

### Jal — `JalCols` ↔ `JalColumns<T, M>`

Constraint-usage audit: complete 2026-05-23

- Upstream (6, `control_flow/jal/columns.rs`): `state` · `adapter: JTypeReader<T>` · `add_operation: AddOperation<T>` · `op_a_operation: AddOperation<T>` · `is_real` · `adapter_cols`
- Lean (14): CPUState→4 · JTypeReader→4 (op_a, op_a_memory triple — but Lean lists `op_a, op_a_memory_prev_value, op_a_memory_prev_low, op_a_memory_diff_low, op_a_0`) · `imm: Vector T 4` (≈ J-type imm) · `op_c: Vector T 4` · `next_pc: Vector T 4` · `op_a_write_value: Vector T 4` · `is_real`
- Status: **divergence — Lean has no `next_pc_carry_value` here.** Upstream has TWO `AddOperation`s nested (one for PC, one for op_a writeback). Lean encodes one as `next_pc: Vector T 4` and one as `op_a_write_value: Vector T 4`, with `imm` and `op_c` as separate raw fields. The 4-limb vs 3-limb PC encoding is a visible discrepancy worth a closer look (upstream PC is 3 limbs; `next_pc` here is 4 — likely an internal addition result before being trimmed back to PC width).

**Per-column constraint usage** (audit: complete 2026-05-23)

| Column (Lean) | Slot | Lean constraint refs | Rust column | Rust constraint refs | Status |
|---|---|---|---|---|---|
| `clk_high` | Main[0] | `.receive (.state Main[0] E4 Main[3..5])` · `.send (.state Main[0] E7 ...)` · `.send (.memory Main[0] Main[11] ...)` · `.receive (.memory Main[0] E28 ...)` — state and memory bus interactions both use clk_high as their clk_high field | `state.clk_high` | `CPUState eval` · memory bus / state bus sends | FLATTENED |
| `clk_16_24` | Main[1] | `.send (.byte (ByteOpcode.ofNat 3) 0 Main[1] 0)` (the 3 opcode is `Range` U8 on Main[1]) | `state.clk_16_24` | `CPUState eval` · byte-range lookup | FLATTENED |
| `clk_0_16` | Main[2] | E4 = `Main[2] + Main[1] * 65536` (clk_low recomposition) · E9 = `(Main[2] - 1) * 8⁻¹` (clk_0_16 progression byte-lookup arg) · `.send (.byte 6 E9 13 0)` | `state.clk_0_16` | `CPUState eval` · byte-range lookup | FLATTENED |
| `pc` (3) | Main[3..5] | `AddOperation.constraints` (b operand for both adds: `#v[Main[3..5], 0]` is pc-as-Word) · `.receive (.state ...)` and `.send (.state ...)` · `.send (.program Main[3..5] ...)` | `state.pc` | `AddOperation eval` (×2 — for next_pc and return-addr) · `CPUState eval` · `eval_untrusted_program` | FLATTENED |
| `op_a` | Main[6] | `.send (.program ... Main[6] ...)` · `.send (.memory ... Main[6] ...)` · `.receive (.memory ... Main[6] ...)` (memory access addressed by op_a register index) | `adapter.op_a` | `JTypeReader eval` · `eval_untrusted_program` · memory bus | FLATTENED |
| `op_a_memory_prev_value` (4) | Main[7..10] | `.send (.memory ... Main[7], Main[8], Main[9], Main[10])` (the value being WRITTEN — Jal's pre-value record) | `adapter.op_a_memory.prev_value` | `JTypeReader eval` · memory bus | FLATTENED |
| `op_a_memory_prev_low` | Main[11] | `.send (.memory Main[0] Main[11] ...)` (memory access timestamp prev_low) | `adapter.op_a_memory.access_timestamp.prev_low` | `JTypeReader eval` | FLATTENED |
| `op_a_memory_diff_low` | Main[12] | `.send (.byte 6 Main[12] 16 0)` (timestamp diff Range(16)) · E33 = `E32 - Main[12]` used in E34 = `(... - 1 - Main[12]) * 65536⁻¹` (diff_high arithmetic) | `adapter.op_a_memory.access_timestamp.diff_low_limb` | `JTypeReader eval` | FLATTENED |
| `op_a_0` | Main[13] | E11 = `(is_real - 1) * Main[13]` (vacuous when not real) · E12 = `is_real - Main[13]` (gates second AddOperation: only emits when op_a ≠ x0) · `.send (.program ... Main[13] ...)` (op_a_0 arg) · E13/E14/E15 = `Main[13] * Main[26/27/28]` (forces return-addr write-value to zero when op_a = x0) | `adapter.op_a_0` | `JTypeReader eval` · `eval_untrusted_program` · gating expressions in eval | FLATTENED |
| `imm` (4) | Main[14..17] | `AddOperation.constraints` (c operand for FIRST add: pc + imm = next_pc) · `.send (.program ... Main[14..17] ...)` (imm arg) | `adapter.op_b_imm` (J-type 4-limb sign-extended immediate; Lean renames to `imm`) | `AddOperation eval` (first add — for next_pc) · `JTypeReader eval` · `eval_untrusted_program` | RENAMED (`imm` ↔ `adapter.op_b_imm`) |
| `op_c` (4) | Main[18..21] | `.send (.program ... Main[18..21] ...)` (op_c arg; J-type op_c is unused — all zero per opcode) | `adapter.op_c_imm` (J-type unused 4-limb field; Lean renames to `op_c`) | `JTypeReader eval` · `eval_untrusted_program` | RENAMED |
| `next_pc` (4) | Main[22..25] | `AddOperation.constraints` (result of first add `{ value := next_pc }`) · `.send (.state Main[0] E7 Main[22], Main[23], Main[24])` (next state bus — note **only low 3 limbs** sent, Main[25] forced to 0) · trailing `assertZero Main[25]` · E2 = `Main[22] * 4⁻¹` (alignment lookup: next_pc[0]/4 in Range(14)) | `add_operation.value` (`Word<T>` — upstream's first AddOp; result is the 4-limb jump target) | `AddOperation eval` (×1) · state bus · alignment lookup | RENAMED (`next_pc` ↔ `add_operation.value`; Lean uses 4 limbs but only 3 are state-meaningful, hence the high-limb-forced-to-zero asserter) |
| `op_a_write_value` (4) | Main[26..29] | `AddOperation.constraints` (result of SECOND add `{ value := op_a_write_value }`: pc + 4 = return address) · trailing `assertZero Main[29]` · E13/E14/E15 = `Main[13] * Main[26/27/28]` (zeros when writing to x0) · E21..E27 = `Main[13] * (Main[26..29] - 0)` (same zeroing under is_real_minus_op_a_0) | `op_a_operation.value` (`Word<T>` — upstream's second AddOp) | `AddOperation eval` (×1) · gating asserts under op_a_0 | RENAMED (`op_a_write_value` ↔ `op_a_operation.value`) |
| `is_real` | Main[30] | E1/E6/E10/E18/E29 = `Main[30] * (Main[30] - 1)` boolean · gates EVERY interaction (`.send (.byte ... ) Main[30]`, `.send (.state ...) Main[30]`, `.send (.program ...) Main[30]`, `.send (.memory ...) Main[30]`, `.receive (.state ...) Main[30]`, `.receive (.memory ...) Main[30]`) · E12 = `Main[30] - Main[13]` (gating for second AddOp) | `is_real` | `builder.assert_bool(local.is_real)` · gates every interaction · `CPUState eval` · `AddOperation eval` ×2 · `JTypeReader eval` | EXACT |
| _none_ | (Lean-only) | — | (no analogue) | — | **DIVERGENT — no `next_pc_carry_value` column in Jal Lean Cols** (existing macro divergence #5 exception confirmed at row level). Jal's PC chain is captured by `next_pc: Vector T 4` + the state-bus send, not by a 3-limb carry witness. |
| _none_ | — | — | `adapter_cols` (rest) | `eval_untrusted_program` | — (Rust-only; macro #2) |
|
> **Jal is special in two ways.** (i) Uses two `AddOperation` instances (jump target + return address) where most ALU chips have one. The Lean struct flattens both into Lean-only `next_pc` and `op_a_write_value` `Vector T 4` fields. (ii) Lacks `next_pc_carry_value` — its PC chain is encoded directly in `next_pc` (4 limbs, high forced 0) and the state-bus sends, distinct from how other chips do it via the 3-limb carry witness. The bridge does NOT use `AddOperation` for the second add via the `CS2` style — it uses CS1 (first AddOp), CS3 (second AddOp gated by `is_real - op_a_0`), and embeds state/memory/program bus sends directly in the trailing constraints list.

### Jalr — `JalrCols` ↔ `JalrColumns<T, M>`

Constraint-usage audit: complete 2026-05-23

- Upstream (7, `control_flow/jalr/columns.rs`): `state` · `adapter: ITypeReader<T>` · `is_real` · `add_operation: AddOperation<T>` · `op_a_operation: AddOperation<T>` · `lsb: T` · `adapter_cols`
- Lean (18): CPUState→4 · ITypeReader→9 · `is_real` · `jump_target: Vector T 4` (≈ `add_operation.value`) · `op_a_write_value: Vector T 4` (≈ `op_a_operation.value`) · `low_bit: T` (rename of `lsb`)
- Status: clean flatten. Two `AddOperation`s become two named `Vector T 4`s. `lsb`/`low_bit` is the same scalar.

**Per-column constraint usage** (audit: complete 2026-05-23)

| Column (Lean) | Slot | Lean constraint refs | Rust column | Rust constraint refs | Status |
|---|---|---|---|---|---|
| `Main[0..20]` (clk_high … op_b_memory_diff_low) | Main[0..20] | as Branch rows 1-13 (CPUState + ITypeReader on op_a + op_b register & memory; ITypeReader here is mutable version) | as Branch | as Branch | FLATTENED (see Branch) |
| `op_c_imm` (4) | Main[21..24] | `AddOperation.constraints` (first AddOp c operand: op_b_memory.prev_value + op_c_imm = jump_target) · `ITypeReader.constraints` (adapter.op_c_imm) | `adapter.op_c_imm` | `AddOperation eval` (first add) · `ITypeReader eval` | FLATTENED |
| `is_real` | Main[25] | E1 = `Main[25]*(Main[25]-1)` boolean · `CPUState.constraints` · `ITypeReader.constraints` · `AddOperation.constraints` (first add is_real arg = Main[25]) · E11 = `Main[25] - Main[13]` (gates second AddOp under is_real ∧ ¬op_a_0) · E10 = `(is_real-1)*op_a_0` (vacuous-when-not-real) | `is_real` | `builder.assert_bool` · `CPUState eval` · `ITypeReader eval` · `AddOperation eval` (×2 with different gating) | EXACT |
| `jump_target` (4) | Main[26..29] | `AddOperation.constraints` (first AddOp result `{value := #v[Main[26..29]]}`: op_b_memory + op_c_imm = jump_target) · trailing `assertZero Main[29]` (high limb is zero) · E4 = `Main[26] - Main[34]` then `*4⁻¹` for alignment lookup (jump_target[0] − low_bit divisible by 4) | `add_operation.value` (first `AddOperation<T>.value: Word<T>`) | `AddOperation eval` (×1, jump-target add) | RENAMED (`jump_target` ↔ `add_operation.value`) |
| `op_a_write_value` (4) | Main[30..33] | `AddOperation.constraints` (second AddOp result `{value := #v[Main[30..33]]}`: pc + 4 = return address) · trailing `assertZero Main[33]` (high limb zero) · E12/E13/E14 = `Main[13] * Main[30/31/32]` (zeros when op_a = x0) | `op_a_operation.value` (second `AddOperation<T>.value`) | `AddOperation eval` (×1, return-addr add) | RENAMED (`op_a_write_value` ↔ `op_a_operation.value`) |
| `low_bit` | Main[34] | E3 = `Main[34]*(Main[34]-1)` boolean · E4 = `Main[26] - Main[34]` (alignment lookup: `(jump_target[0] - low_bit) / 4 ∈ Range(14)`) · E6 = `Main[26] - Main[34]` (passed to CPUState as next_pc[0] — i.e. the actual next_pc[0] = jump_target[0] ∧ ¬1, with low_bit being the trimmed LSB) | `lsb` | `builder.assert_bool(local.lsb)` · alignment lookup · `CPUState eval` (next_pc[0] = `local.add_operation.value[0] - local.lsb`) | RENAMED (`low_bit` ↔ `lsb`) |
| _none_ | (Lean-only) | — | (no analogue) | — | **DIVERGENT — no `next_pc_carry_value` column in Jalr Lean Cols.** Macro divergence #5 mentions Jal and Mul as exceptions; Jalr should be added to that list (struct read 2026-05-23 confirms no field). |
| _none_ | — | — | `adapter_cols` (rest) | `eval_untrusted_program` | — (Rust-only; macro #2) |
|
> Jalr is structurally cleaner than Jal in that it threads `next_pc` through the CPUState `next_pc` argument directly (`#v[E6, Main[27], Main[28]]` where E6 = `jump_target[0] - low_bit`), without a dedicated `next_pc` Vector field. The `low_bit` masking matches RISC-V's JALR specification (low bit of computed target is forced to 0).

### Load{Byte,Half,Word,Double,X0}

Constraint-usage audit: complete 2026-05-23 (5 chips)

Shared upstream skeleton (`memory/instructions/load/<load_*>.rs`): `state` · `adapter: ITypeReader<T>` · `address_operation: AddressOperation<T>` · `memory_access: MemoryAccessCols<T>` · variant fields · `adapter_cols`.

Shared Lean skeleton: CPUState→4 · ITypeReader→9 · `AddressOperation` inlined→4 (`addr_value: Vector T 3` + `addr_top_two_limb_inv: T` ↔ `addr_operation.value: [T;3]` + `top_two_limb_inv: T`) · `MemoryAccessCols` inlined→6 (`load_prev_value: Vector T 4, load_memory_prev_high, load_memory_prev_low, load_memory_flag, load_memory_diff_low, load_memory_diff_high`) · variant fields · `next_pc_carry_value`.

**Status:** clean flatten with one Lean expansion. Lean's memory_access is 6 fields where upstream's `MemoryAccessCols<T>` is 2 nested fields (`prev_value: Word<T>` + `access_timestamp: MemoryAccessTimestamp<T>`). The Lean expansion (`memory_flag`, `memory_diff_high`, `memory_prev_high`) suggests we are inlining a richer timestamp than the `RegisterAccessTimestamp` 2-field version — likely the full `MemoryAccessTimestamp` (`prev_low_limb, prev_high_limb, diff_low_limb, diff_high_limb`) plus a separate flag column. This is the **`MemoryAccessColsU8` vs `MemoryAccessCols` distinction** upstream — worth checking which variant each load chip actually uses upstream.

Variant fields:
- **LoadByte (32):** Lean has `byte_selector_{top,mid,lo}, selected_byte, selected_byte_alt, result_byte, signed_extension_flag, is_lb, is_lbu`. Upstream `offset_bit: [T;3], selected_limb, selected_limb_low_byte, selected_byte, msb, is_lb, is_lbu`. Same family; Lean splits `selected_limb` as `selected_byte_alt` and names the signed-extension bit differently.
- **LoadHalf (29):** Lean `half_offset_bit{1,2}, op_a_write_value_lo, signed_extension_msb, is_lh, is_lhu`. Upstream `offset_bit: [T;2], selected_half, msb: U16MSBOperation<T>, is_lh, is_lhu`. Lean lacks a top-level `selected_half` aggregate.
- **LoadWord (28):** Lean `word_offset_flag, op_a_write_value_lo: Vector T 2, signed_extension_msb, is_lw, is_lwu`. Upstream `offset_bit: T, selected_word: [T;2], msb: U16MSBOperation<T>, is_lw, is_lwu`. Aligns 1-1 modulo names.
- **LoadDouble (24):** Lean `is_real`. Upstream `is_real`. Identical past the shared skeleton.
- **LoadX0 (31):** Lean has the 3-element `byte_offset_selectors: Vector T 3` plus all 7 `is_l*` flags. Upstream `offset_bit: [T;3]` + 7 `is_l*` flags. Aligns.

**Shared Load skeleton — Main[0..37]** (audit: complete 2026-05-23). Identical across LoadByte, LoadHalf, LoadWord, LoadDouble, LoadX0:

| Column (Lean) | Slot | Lean constraint refs | Rust column | Rust constraint refs | Status |
|---|---|---|---|---|---|
| `Main[0..20]` (clk_high … op_b_memory_diff_low) | Main[0..20] | as Addi rows 1-13 (CPUState + ITypeReader on op_a and op_b register/memory triples) | as Addi | as Addi | FLATTENED (see Addi) |
| `op_c_imm` (4) | Main[21..24] | `ITypeReader.constraints` (adapter.op_c_imm — the load offset immediate) · `ProgramTable.assertion` · `AddressOperation.constraints` (c operand: op_b_memory + op_c_imm = addr) | `adapter.op_c_imm` | `ITypeReader eval` · `AddressOperation eval` (via `local.adapter.c()`) · `eval_untrusted_program` | FLATTENED |
| `addr_value` (3) | Main[25..27] | `AddressOperation.constraints` (output `addr_operation.value`) · memory bus send/receive in trace-level Spec (`.send (.memory ... addr_value)` per the bridge) | `address_operation.addr_operation.value` (`[T;3]` — upstream nests `AddrAddOperation`) | `AddressOperation eval` · memory bus | FLATTENED |
| `addr_top_two_limb_inv` | Main[28] | `AddressOperation.constraints` (auxiliary inverse witness for top-two-limb-nonzero check) | `address_operation.top_two_limb_inv` | `AddressOperation eval` | EXACT |
| `load_prev_value` (4) | Main[29..32] | memory-bus receive (the loaded 4-limb word) | `memory_access.prev_value` (`Word<T>` inside `MemoryAccessCols<T>`) | memory bus interaction in `eval` | FLATTENED (Lean inlines the nested `MemoryAccessCols`; macro divergence #4) |
| `load_memory_prev_high` | Main[33] | memory-bus arithmetic: `(load_memory_prev_high * 2^24 + load_memory_prev_low)` is the prior-access clk_high for the load-memory access (E33 = `Main[0] - Main[33]` is `clk_high - prev_high`); used in the memory consistency E40/E43 chain | `memory_access.access_timestamp.prev_high_limb` (part of `MemoryAccessTimestamp<T>`; macro divergence #4) | memory bus interaction | FLATTENED |
| `load_memory_prev_low` | Main[34] | memory-bus arithmetic (E36 = `flag * prev_low`, paired with E33 above) | `memory_access.access_timestamp.prev_low_limb` | memory bus interaction | FLATTENED |
| `load_memory_flag` | Main[35] | E30/E31/E32 = `flag * (flag-1) * is_real` (boolean gate under is_real); E34/E35 = `flag * (clk_high - prev_high) * is_real` (gates whether prev access was current-shard or prior-shard); E37/E38 = `(1 - flag) * prev_high` (when flag = 0, prev access is from a prior shard); E40-E43 mixing flag into the diff computation | (no direct analogue in `MemoryAccessCols<T>`; this is the **`MemoryAccessColsU8` distinction** — upstream uses a different variant for RAM access that has its own validity flag, or computes is_real-equivalent inline) | memory bus | **DIVERGENT — partial.** Lean's `load_memory_flag` doesn't appear in upstream's standard `MemoryAccessCols<T>`. Resolves part of open-question #7: Lean is using the richer `MemoryAccessColsU8` variant (or equivalent) for RAM access, since RAM accesses can be initial (no prior access) where register accesses always have one. |
| `load_memory_diff_low` | Main[36] | `ByteOpcodeTable` Range(16) lookup in `main`; memory consistency arithmetic E47 = `Main[37] * 65536 + Main[36]` is the full 32-bit timestamp diff | `memory_access.access_timestamp.diff_low_limb` | memory bus · `ByteOpcodeTable` lookup | FLATTENED |
| `load_memory_diff_high` | Main[37] | `ByteOpcodeTable` U8Range lookup in `main`; same E47 chain | `memory_access.access_timestamp.diff_high_limb` | memory bus · `ByteOpcodeTable` lookup | FLATTENED |

**LoadByte variant fields — Main[38..46]** (audit: complete 2026-05-23):

| Column (Lean) | Slot | Lean constraint refs | Rust column | Rust constraint refs | Status |
|---|---|---|---|---|---|
| `byte_selector_top` | Main[38] | E68 = `Main[38] * ((Main[41] - Main[42]) / 256)` (selects high-half of the chosen limb when set, low-half otherwise) | `offset_bit[2]` (the most-significant of the 3-bit byte offset) | `eval` byte-selection logic | RENAMED (`byte_selector_top` ↔ `offset_bit[2]`) |
| `byte_selector_mid` | Main[39] | E54 = `(Main[39] - 1) * (Main[40] - 1) * (Main[41] - Main[29])` etc. (selects which 16-bit limb of the loaded word contains the target byte) | `offset_bit[1]` | `eval` | RENAMED (`byte_selector_mid` ↔ `offset_bit[1]`) |
| `byte_selector_lo` | Main[40] | as `byte_selector_mid` | `offset_bit[0]` | `eval` | RENAMED (`byte_selector_lo` ↔ `offset_bit[0]`) |
| `selected_byte` | Main[41] | E54-E65 = 4 assertZeros that pick out the right limb-byte based on byte_selector_{mid,lo} (Main[41] equals Main[29], Main[30], Main[31], or Main[32] one-hot) | `selected_limb` (the 16-bit limb containing the target byte) | `eval` (`builder.assert_eq(local.selected_limb, ...)`) | RENAMED (`selected_byte` ↔ `selected_limb`; **Lean name is misleading — it's actually the 16-bit selected limb, not the byte**) |
| `selected_byte_alt` | Main[42] | `ByteOpcodeTable` U8Range lookup (in `main`); E66 = `Main[41] - Main[42]` (diff into byte_selector_top mux); .send (.byte 3 0 Main[42] E67) bridges this with the divide-by-256 quotient | `selected_limb_low_byte` (the low byte of the selected_limb) | `eval` | RENAMED (`selected_byte_alt` ↔ `selected_limb_low_byte`) |
| `result_byte` | Main[43] | E72 = `Main[43] - E71` (E71 is the byte-selector mux output: `top * high_half + (1-top) * low_byte`); `ByteOpcodeTable` opcode 5 lookup `(opcode 5 Main[44] Main[43] 0) is_lb` (MSB lookup for sign-extension) | `selected_byte` (the loaded byte after byte-selection) | `eval` (`builder.assert_eq(local.selected_byte, mux_expr)`) | RENAMED (`result_byte` ↔ `selected_byte`; **swap-names with `selected_byte` above — they look alike but are different in upstream**) |
| `signed_extension_flag` | Main[44] | E73 = `Main[46] * Main[44]` (vacuous when LBU: unsigned has no sign extension); ITypeReader write_value uses `65280 * Main[44] + Main[43]` (low limb) and `65535 * Main[44]` (high 3 limbs sign-extension) | `msb` (`U16MSBOperation<T>.msb` — upstream nests; macro divergence #7 / #4) | `eval` (`U16MSBOperation eval`) | FLATTENED (Lean scalar `T`; upstream 1-field struct) |
| `is_lb` | Main[45] | `ProgramTable.assertion` (E2 = `29 * is_lb`); trailing assertZero is_lb boolean; gates the MSB lookup (`(opcode 5 ... ) is_lb` — only LB does sign-extension) | `is_lb` | `eval` · `eval_untrusted_program` · `builder.assert_bool` | EXACT |
| `is_lbu` | Main[46] | `ProgramTable.assertion` (E3 = `32 * is_lbu`); trailing assertZero is_lbu boolean; E73 force-zeroes signed_extension_flag for LBU | `is_lbu` | `eval` · `eval_untrusted_program` · `builder.assert_bool` | EXACT |
| `next_pc_carry_value` (3) | (Lean-only) | trace-level `ProgramTable` | `adapter_cols.next_pc_carry` | `eval_untrusted_program` | FLATTENED (macro #5) |
|
> **StoreByte-naming-drift recurrence.** The triple `selected_byte` / `selected_byte_alt` / `result_byte` on the Lean side maps to `selected_limb` / `selected_limb_low_byte` / `selected_byte` upstream — the Lean field literally named `selected_byte` is upstream's `selected_limb`. This is the same kind of naming confusion as StoreByte (open-question #5).

**Per-column constraint usage — LoadHalf** (audit: complete 2026-05-23). Same Main[0..37] as LoadByte. Variant fields Main[38..43]:

| Column (Lean) | Slot | Lean constraint refs | Rust column | Rust constraint refs | Status |
|---|---|---|---|---|---|
| `half_offset_bit1` | Main[38] | sub-double half-selector (weight 2 in offset arithmetic) | `offset_bit[1]` | `eval` | RENAMED |
| `half_offset_bit2` | Main[39] | sub-double half-selector (weight 4 in offset arithmetic) | `offset_bit[0]` | `eval` | RENAMED |
| `op_a_write_value_lo` | Main[40] | the 16-bit half selected from `load_prev_value` based on the two offset bits | `selected_half` | `eval` | RENAMED |
| `signed_extension_msb` | Main[41] | sign-extension bit for LH (zero for LHU); used in ITypeReader write_value high-limb sign-extension chain | `msb.msb` (`U16MSBOperation<T>`) | `U16MSBOperation eval` | FLATTENED |
| `is_lh` | Main[42] | `ProgramTable.assertion` (opcode `is_lh*30 + is_lhu*33`); trailing assertZero boolean | `is_lh` | as LoadByte | EXACT |
| `is_lhu` | Main[43] | as `is_lh` | `is_lhu` | as LoadByte | EXACT |
| `next_pc_carry_value` (3) | (Lean-only) | trace-level | `adapter_cols.next_pc_carry` | as LoadByte | FLATTENED (macro #5) |

**Per-column constraint usage — LoadWord** (audit: complete 2026-05-23). Same Main[0..37] as LoadByte. Variant fields Main[38..43]:

| Column (Lean) | Slot | Lean constraint refs | Rust column | Rust constraint refs | Status |
|---|---|---|---|---|---|
| `word_offset_flag` | Main[38] | single bit selecting low vs high 32-bit word of the loaded doubleword | `offset_bit` (`T` — single bit, since 64-bit load only has 2 alignments) | `eval` | RENAMED |
| `op_a_write_value_lo` (2) | Main[39..40] | the 2-limb (32-bit) word selected from `load_prev_value` | `selected_word` (`[T;2]`) | `eval` | RENAMED |
| `signed_extension_msb` | Main[41] | sign-extension bit for LW (zero for LWU) | `msb.msb` | `U16MSBOperation eval` | FLATTENED |
| `is_lw` | Main[42] | `ProgramTable.assertion` (opcode `is_lw*31 + is_lwu*34`); trailing assertZero boolean | `is_lw` | as LoadByte | EXACT |
| `is_lwu` | Main[43] | as `is_lw` | `is_lwu` | as LoadByte | EXACT |
| `next_pc_carry_value` (3) | (Lean-only) | trace-level | `adapter_cols.next_pc_carry` | as LoadByte | FLATTENED |

**Per-column constraint usage — LoadDouble** (audit: complete 2026-05-23). Same Main[0..37] as LoadByte. Variant fields Main[38]:

| Column (Lean) | Slot | Lean constraint refs | Rust column | Rust constraint refs | Status |
|---|---|---|---|---|---|
| `is_real` | Main[38] | `ProgramTable.assertion` (opcode = 35 literal, since LD has no sub-variant); trailing assertZero boolean; gates the 4 memory accesses | `is_real` | `eval` · `eval_untrusted_program` · `builder.assert_bool` | EXACT |
| `next_pc_carry_value` (3) | (Lean-only) | trace-level | `adapter_cols.next_pc_carry` | as LoadByte | FLATTENED |
|
> LoadDouble is the simplest Load chip — no byte-selection (the full 8-byte value is loaded directly) so no variant fields beyond `is_real`.

**Per-column constraint usage — LoadX0** (audit: complete 2026-05-23). Same Main[0..37] as LoadByte. Variant fields Main[38..47]:

| Column (Lean) | Slot | Lean constraint refs | Rust column | Rust constraint refs | Status |
|---|---|---|---|---|---|
| `byte_offset_selectors` (3) | Main[38..40] | byte-offset selectors used by the chip's byte-selection logic across all 7 Load variants | `offset_bit` (`[T;3]`) | `eval` | RENAMED (named `byte_offset_selectors` here vs `offset_bit` in Rust; one Vector vs 3 scalars but Lean's struct stores as `Vector T 3`) |
| `is_lb` | Main[41] | `ProgramTable.assertion` (opcode mux `is_lb*29 + ...`); trailing assertZero is_lb boolean | `is_lb` | `eval` · `eval_untrusted_program` · `builder.assert_bool` | EXACT |
| `is_lbu` | Main[42] | as `is_lb` (weight 32 in opcode mux) | `is_lbu` | as `is_lb` | EXACT |
| `is_lh` | Main[43] | as `is_lb` (weight 30) | `is_lh` | as `is_lb` | EXACT |
| `is_lhu` | Main[44] | as `is_lb` (weight 33) | `is_lhu` | as `is_lb` | EXACT |
| `is_lw` | Main[45] | as `is_lb` (weight 31) | `is_lw` | as `is_lb` | EXACT |
| `is_lwu` | Main[46] | as `is_lb` (weight 34) | `is_lwu` | as `is_lb` | EXACT |
| `is_ld` | Main[47] | as `is_lb` (weight 35) | `is_ld` | as `is_lb` | EXACT |
| `next_pc_carry_value` (3) | (Lean-only) | trace-level | `adapter_cols.next_pc_carry` | as LoadByte | FLATTENED |
|
> LoadX0 is the special-case chip for loads where `op_a = x0`. It bundles all 7 load opcode variants (LB, LBU, LH, LHU, LW, LWU, LD) into a single chip without per-variant byte-selection witness fields — the result is discarded since x0 is hardwired to zero. No byte/half/word offset_bit decomposition is needed; only the 3-limb byte_offset_selectors covers the alignment computation for the memory address.

### Store{Byte,Half,Word,Double}

Constraint-usage audit: complete 2026-05-23 (4 chips)

Shared upstream skeleton (`memory/instructions/store/<store_*>.rs`): `state` · `adapter: ITypeReader<T>` · `address_operation: AddressOperation<T>` · `memory_access: MemoryAccessCols<T>` · variant fields · `is_real` · `adapter_cols`.

Shared Lean skeleton: same as Load, but with `store_*` prefix on memory-access fields and `store_write_value: Word<T>` instead of `load_prev_value`.

- **StoreByte (32):** Lean has `byte_selector_{top,mid,lo}, selected_byte, selected_byte_alt, result_byte, selected_combined, store_write_value`. Upstream `offset_bit: [T;3], mem_limb, mem_limb_low_byte, register_low_byte, increment, store_value`. Naming completely diverged here — should be cross-checked field by field in a follow-up audit, this is the chip most likely to have drifted in semantics, not just labels.
- **StoreHalf (27):** Lean `byte_selector_{upper,lower}, store_write_value`. Upstream `offset_bit: [T;2], store_value`.
- **StoreWord (26):** Lean `word_offset_flag, store_write_value`. Upstream `offset_bit: T, store_value`.
- **StoreDouble (24):** Just the shared skeleton + `is_real`. Aligned.

**Shared Store skeleton — Main[0..37]** (audit: complete 2026-05-23). Identical to Load skeleton modulo memory bus direction (store sends then receives the inverse of load's pattern; the bridge `.send (.memory ... store_prev_value)` and `.receive (.memory ... store_write_value)`).

> Rows match LoadByte's `Main[0..37]` exactly except `load_prev_value`/`load_memory_*` rename to `store_prev_value`/`store_memory_*`. Same FLATTENED status with the same `MemoryAccessColsU8` divergence on `store_memory_flag` (open-question #7 — see LoadByte's row 8).

**Per-column constraint usage — StoreByte** (audit: complete 2026-05-23). Variant fields Main[38..49]:

| Column (Lean) | Slot | Lean constraint refs | Rust column | Rust constraint refs | Status |
|---|---|---|---|---|---|
| `byte_selector_top` | Main[38] | byte-position selector top bit (selects which 16-bit half within the loaded limb the store byte will write into) | `offset_bit[2]` | `eval` | RENAMED |
| `byte_selector_mid` | Main[39] | byte-position selector mid bit | `offset_bit[1]` | `eval` | RENAMED |
| `byte_selector_lo` | Main[40] | byte-position selector low bit | `offset_bit[0]` | `eval` | RENAMED |
| `selected_byte` | Main[41] | the 16-bit limb of the prior word being modified (chosen by byte_selector_{mid,lo} from store_prev_value) | `mem_limb` (the 16-bit memory limb being modified) | `eval` | RENAMED (`selected_byte` ↔ `mem_limb`; **Lean name is misleading — it's the selected 16-bit limb, not a byte**) |
| `selected_byte_alt` | Main[42] | the low byte of `selected_byte` (the byte position within the chosen 16-bit limb that the store writes to) | `mem_limb_low_byte` | `eval` | RENAMED |
| `result_byte` | Main[43] | the source byte being stored (op_a's lowest byte, post-selector); range-checked U8 | `register_low_byte` (the low byte of the source register `op_a_memory_prev_value`) | `eval` | RENAMED |
| `selected_combined` | Main[44] | the combined byte mix: `byte_selector_top * (high_half byte) + (1 - byte_selector_top) * register_low_byte` — i.e. the new byte value within the selected limb | `increment` (the byte to merge in at the right position) | `eval` | RENAMED — **note name divergence** ("selected_combined" vs "increment" is a real semantic-naming gap) |
| `store_write_value` (4) | Main[45..48] | the new 4-limb word being WRITTEN to memory (this is the value, not the prior value) | `store_value` (`Word<T>` — the resulting 64-bit word post-store) | `eval` · memory bus | RENAMED (`store_write_value` ↔ `store_value`) |
| `is_real` | Main[49] | `ProgramTable.assertion` (opcode = 36 literal); trailing assertZero is_real boolean; gates the 4 memory accesses (op_a read, op_b read, RAM read, RAM write) | `is_real` | `eval` · `eval_untrusted_program` · `builder.assert_bool` | EXACT |
| `next_pc_carry_value` (3) | (Lean-only) | trace-level | `adapter_cols.next_pc_carry` | as LoadByte | FLATTENED |
|
> **Resolves open-question #5 (StoreByte naming drift).** The 5-column rename table is now explicit: Lean's `selected_byte / selected_byte_alt / result_byte / selected_combined / store_write_value` correspond 1-1 to Rust's `mem_limb / mem_limb_low_byte / register_low_byte / increment / store_value`. The slot layouts and constraint-reference sets match; only the field NAMES differ. The remaining divergence to flag is that Lean's `selected_byte` reads as "selected byte" but actually means the selected 16-bit limb — recommend renaming to `selected_limb` in a future cleanup.

**Per-column constraint usage — StoreHalf** (audit: complete 2026-05-23). Variant fields Main[38..44]:

| Column (Lean) | Slot | Lean constraint refs | Rust column | Rust constraint refs | Status |
|---|---|---|---|---|---|
| `byte_selector_upper` | Main[38] | half-position selector (which 16-bit limb of the 4-limb word to overwrite, weight 2) | `offset_bit[1]` | `eval` | RENAMED |
| `byte_selector_lower` | Main[39] | half-position selector (weight 1) | `offset_bit[0]` | `eval` | RENAMED |
| `store_write_value` (4) | Main[40..43] | the new 4-limb word (only one 16-bit limb differs from store_prev_value) | `store_value` | `eval` · memory bus | RENAMED |
| `is_real` | Main[44] | `ProgramTable.assertion` (opcode = 37 literal); trailing assertZero is_real boolean | `is_real` | as StoreByte | EXACT |
| `next_pc_carry_value` (3) | (Lean-only) | trace-level | `adapter_cols.next_pc_carry` | as LoadByte | FLATTENED |

**Per-column constraint usage — StoreWord** (audit: complete 2026-05-23). Variant fields Main[38..43]:

| Column (Lean) | Slot | Lean constraint refs | Rust column | Rust constraint refs | Status |
|---|---|---|---|---|---|
| `word_offset_flag` | Main[38] | word-position selector (which 32-bit half of the 64-bit doubleword to overwrite) | `offset_bit` (`T` — single bit) | `eval` | RENAMED |
| `store_write_value` (4) | Main[39..42] | the new 4-limb word (one 32-bit half differs from store_prev_value) | `store_value` | `eval` · memory bus | RENAMED |
| `is_real` | Main[43] | `ProgramTable.assertion` (opcode = 38 literal); trailing assertZero is_real boolean | `is_real` | as StoreByte | EXACT |
| `next_pc_carry_value` (3) | (Lean-only) | trace-level | `adapter_cols.next_pc_carry` | as LoadByte | FLATTENED |

**Per-column constraint usage — StoreDouble** (audit: complete 2026-05-23). Variant fields Main[38]:

| Column (Lean) | Slot | Lean constraint refs | Rust column | Rust constraint refs | Status |
|---|---|---|---|---|---|
| `is_real` | Main[38] | `ProgramTable.assertion` (opcode = 39 literal); trailing assertZero is_real boolean | `is_real` | as StoreByte | EXACT |
| `next_pc_carry_value` (3) | (Lean-only) | trace-level | `adapter_cols.next_pc_carry` | as LoadByte | FLATTENED |
|
> StoreDouble is the simplest Store chip — no sub-word selection (the full 8-byte value is stored directly), so no variant fields beyond `is_real`. `store_write_value` is not a separate column on the Lean side because the entire `op_a_memory_prev_value` (Main[7..10]) is the value being stored.

### Mul — `MulCols` ↔ `MulCols<T, M>`

Constraint-usage audit: complete 2026-05-23

- Upstream (10, `alu/mul/mod.rs`): `state` · `adapter: RTypeReader<T>` · `a: Word<T>` · `mul_operation: MulOperation<T>` · `is_mul, is_mulh, is_mulhu, is_mulhsu, is_mulw` · `adapter_cols`
- Lean (32): CPUState→4 · RTypeReader→13 · `op_a_write_value: Vector T 4` (≈ upstream `a: Word<T>`) · MulOperation inlined→9 (`carry: Vector T 16, product: Vector T 16, b_low_bytes: Vector T 4, c_low_bytes: Vector T 4, b_msb, c_msb, product_msb, b_sign_extend, c_sign_extend`) · `is_mul, is_mulh, is_mulw, is_mulhsu, is_mulhu`
- Status: nesting mismatch. Note Lean `MulOperation` itself has the same 9 fields — we just *also* inline them at chip level. Note **no `next_pc_carry_value`** here. Also, upstream `MulOperation.b_lower_byte/c_lower_byte: U16toU8Operation<T>` (4 limbs each) — Lean encodes as `Vector T 4` directly.

**Per-column constraint usage** (audit: complete 2026-05-23)

| Column (Lean) | Slot | Lean constraint refs | Rust column | Rust constraint refs | Status |
|---|---|---|---|---|---|
| `Main[0..27]` (clk_high … op_c_memory_diff_low) | Main[0..27] | as Add rows 1-17 (CPUState + RTypeReader on op_a/op_b/op_c register + memory triples) | as Add | as Add | FLATTENED (see Add) |
| `op_a_write_value` (4) | Main[28..31] | `MulOperation.constraints` (output `a` arg) · `RTypeReader.constraints` (write_value) | `a` (`Word<T>` — upstream stores this SEPARATELY from `mul_operation.value`; macro divergence #7) | `MulOperation eval` (output product low 4 limbs) · `RTypeReader eval` | RENAMED (`op_a_write_value` ↔ `a`; upstream separates the write-back word from the operation struct, unlike Add) |
| `carry` (16) | Main[32..47] | `MulOperation.constraints` (16-limb carry chain) · 16× `ByteOpcodeTable` Range(16) lookups in `main` | `mul_operation.carry` (`[T;16]`) | `MulOperation eval` (carry chain constraints + per-limb range) | FLATTENED |
| `product` (16) | Main[48..63] | `MulOperation.constraints` (16-limb product chain) · 16× U8Range lookups in `main` | `mul_operation.product` (`[T;16]`) | `MulOperation eval` | FLATTENED |
| `b_low_bytes` (4) | Main[64..67] | `MulOperation.constraints` (`b_lower_byte.low_bytes`) | `mul_operation.b_lower_byte.low_bytes` (nested `U16toU8Operation`) | `MulOperation eval` | FLATTENED |
| `c_low_bytes` (4) | Main[68..71] | as `b_low_bytes` for c operand | `mul_operation.c_lower_byte.low_bytes` | as `b_low_bytes` | FLATTENED |
| `mul_aux_bits` (5) | Main[72..76] | `MulOperation.constraints` (5 sign-related bits: `b_msb, c_msb, product_msb, b_sign_extend, c_sign_extend`); **none of the 5 are referenced by Lean `main` / `Spec` directly** — only by the wrapped `MulOperation.constraints` call | `mul_operation.{b_msb, c_msb, product_msb.msb, b_sign_extend, c_sign_extend}` | `MulOperation eval` | FLATTENED (Lean collapses 5 single-cell fields into one `Vector T 5` for ProvableStruct ceiling; upstream names each separately. `product_msb` is `U16MSBOperation<T>` upstream, Lean stores as scalar `T`) |
| `is_mul` | Main[77] | `MulOperation.constraints` (selector arg `is_mul`) · `ProgramTable.assertion` (E24 = `is_mul*11 + is_mulh*12 + is_mulw*13 + is_mulhsu*14 + is_mulhu*24`) · trailing `assertZero (is_mul*(is_mul-1))` · contributes to is_real sum | `is_mul` | `MulOperation eval` · `eval_untrusted_program` · `builder.assert_bool` | EXACT |
| `is_mulh` | Main[78] | as `is_mul` | `is_mulh` | as `is_mul` | EXACT |
| `is_mulw` | Main[79] | as `is_mul` (slot order differs from upstream: Lean has is_mulw before is_mulhsu/is_mulhu; upstream is `is_mul, is_mulh, is_mulhu, is_mulhsu, is_mulw`) | `is_mulw` | as `is_mul` | **RENAMED (slot-order reordering)** — same column set but Main[79..81] mapping is `is_mulw, is_mulhsu, is_mulhu` (Lean) vs `is_mulhu, is_mulhsu, is_mulw` (upstream Rust struct order) |
| `is_mulhsu` | Main[80] | as `is_mul` | `is_mulhsu` | as `is_mul` | RENAMED (slot-order; see is_mulw) |
| `is_mulhu` | Main[81] | as `is_mul` | `is_mulhu` | as `is_mul` | RENAMED (slot-order; see is_mulw) |
| (computed) is_real | (no slot) | trailing `assertZero (sum * (sum - 1))` (E15) gates one-hot | (no analogue) | sum-of-selectors used inline | — |
| `next_pc_carry_value` (3) | (Lean-only — added per macro #5) | none (Mul row from struct shows the field; not yet referenced by main/Spec/bridge) | **(absent on Rust side per existing prose — but see note)** | — | DIVERGENT (existing macro divergence #5 lists Mul as one of two chips WITHOUT `next_pc_carry_value`; the Lean struct in 2026-05-22 commit `6ff1320` was extended to add it across 24 chips. **This row is added to the Lean side and currently unreferenced.** Re-examine whether Mul should carry the column or not) |
| _none_ | — | — | `adapter_cols` (rest) | `eval_untrusted_program` | — (Rust-only; macro #2) |
|
> The slot-order divergence on Main[79..81] is the only place in Batch B where Lean and Rust column ordering differs within a chip. Existing prose says the selector set is `is_mul, is_mulh, is_mulw, is_mulhsu, is_mulhu` on Lean and `is_mul, is_mulh, is_mulhu, is_mulhsu, is_mulw` on Rust — the constraint compiler emits the Rust order into the bridge, so the Lean field at Main[79] is actually upstream's `is_mulhu` (and Lean's `is_mulw` is at the slot upstream calls `is_mulw`, which is Main[81]). **This is a real RENAMED-slot mismatch worth flagging at the top of the doc.** Verify by re-reading either `cargo run -p sp1-constraint-compiler` output OR the Rust struct's field order.

### DivRem — `DivRemCols` ↔ `DivRemCols<T, M>`

Constraint-usage audit: complete 2026-05-23 (decomposed by `c3aedab`, `ce4c38c`, `f2fdaa3`, `73e1ca6`)

- Upstream (~44, `alu/divrem/mod.rs`): `state` · `adapter: RTypeReader<T>` · `a, b, c: Word<T>` · `quotient, quotient_comp, remainder_comp, remainder, abs_remainder, abs_c, max_abs_c_or_1: Word<T>` · `c_times_quotient: [T; LONG_WORD_SIZE]` · `c_times_quotient_lower, c_times_quotient_upper: MulOperation<T>` · `c_neg_operation, rem_neg_operation: AddOperation<T>` · `remainder_lt_operation: LtOperationUnsigned<T>` · `carry: [T; LONG_WORD_SIZE]` · `is_c_0: IsZeroWordOperation<T>` · 8 mode flags · `is_overflow` · `is_overflow_b, is_overflow_c: IsEqualWordOperation<T>` · `b_msb, rem_msb, c_msb, quot_msb: U16MSBOperation<T>` · `b_neg, b_neg_not_overflow, b_not_neg_not_overflow, is_real_not_word, rem_neg, c_neg, abs_c_alu_event, abs_rem_alu_event, is_real, remainder_check_multiplicity` · `adapter_cols`
- Lean: CPUState→4 · RTypeReader→13 · `op_a_write_value: Vector T 4` · **10 named aux_pre fields** (b, c, quotient, quotient_comp, remainder_comp, remainder, abs_remainder, abs_c, max_abs_c_or_1, c_times_quotient) · `c_times_quotient_lower, c_times_quotient_upper: MulOperation T` · **`aux_post: DivRemAuxPost T`** (a 14-field sub-record nesting c_neg_operation/rem_neg_operation: AddOperation, remainder_lt_operation: LtOperationUnsigned, carry: Vector T 8, is_c_0: IsZeroWordOperation, **mode_flags: Vector T 8**, is_overflow, is_overflow_b/c: IsEqualWordOperation, b_msb/rem_msb/c_msb/quot_msb: U16MSBOperation, neg_flags: Vector T 5) · `c_neg, abs_c_alu_event, abs_rem_alu_event, is_real, remainder_check_multiplicity` · `next_pc_carry_value`
- Status: **CLOSED 2026-05-23 — every cell named.** The aux:209 opaque blob was fully decomposed in Phase 3f (`ce4c38c`); the 3-flag/8-flag encoding mismatch was resolved by switching the opcode formula to the 8 one-hot mode flags (`73e1ca6`); the Main[241..245] labels were realigned with upstream (`f2fdaa3`). The `DivRemAuxPost` sub-record nesting is forced by a `deriving ProvableStruct` field-count cap of ~25 flat fields, NOT a semantic divergence (see [[feedback-provablestruct-field-count-limit]]).

**Per-column constraint usage** (audit: complete 2026-05-23 — all rows EXACT/RENAMED/FLATTENED after the four-commit sweep)

| Column (Lean) | Slot | Lean constraint refs | Rust column | Rust constraint refs | Status |
|---|---|---|---|---|---|
| `Main[0..27]` (clk_high … op_c_memory_diff_low) | Main[0..27] | as Add rows 1-17 (CPUState + RTypeReader on op_a/op_b/op_c register & memory triples) | as Add | as Add | FLATTENED (see Add) |
| `op_a_write_value` (4) | Main[28..31] | `RTypeReader.constraints` (write_value) | `a` (`Word<T>` — write-back; upstream stores separately from `c_times_quotient_lower.product`) | `eval` · `RTypeReader eval` | RENAMED (`op_a_write_value` ↔ `a`) |
| `b` (4), `c` (4), `quotient` (4), `quotient_comp` (4), `remainder_comp` (4), `remainder` (4), `abs_remainder` (4), `abs_c` (4), `max_abs_c_or_1` (4) | Main[32..67] | bridge E-expressions in `SP1Chips/DivRem/Constraints.lean` (carry chains, sign-extension, mux selectors) | same names | `eval` · `MulOperation eval` (twice, b and c are inputs to both) · `AddOperation eval` (for abs_*) · `LtOperationUnsigned eval` | EXACT (named per upstream after Phase 3f) |
| `c_times_quotient` (8) | Main[68..75] | bridge MulOperation result-vs-aux constraints | `c_times_quotient: [T; LONG_WORD_SIZE]` | raw equality constraints to `MulOperation` outputs | EXACT |
| `c_times_quotient_lower` (MulOperation, 45 cells) | Main[76..120] | `MulOperation.constraints` | `c_times_quotient_lower` | `MulOperation eval` | EXACT (nested ProvableStruct) |
| `c_times_quotient_upper` (MulOperation, 45 cells) | Main[121..165] | `MulOperation.constraints` | `c_times_quotient_upper` | `MulOperation eval` | EXACT (nested ProvableStruct) |
| `aux_post.{c_neg_operation, rem_neg_operation}` (AddOperation × 2, 8 cells) | Main[166..173] | `AddOperation.constraints` (CS7/CS8 in bridge) | same names | `AddOperation eval` (×2) | EXACT (nested in DivRemAuxPost) |
| `aux_post.remainder_lt_operation` (LtOperationUnsigned, 8 cells) | Main[174..181] | `LtOperationUnsigned.constraints` (CS9) | same name | `LtOperationUnsigned eval` | EXACT (nested) |
| `aux_post.carry` (8) | Main[182..189] | bridge carry-propagation constraints | `carry: [T; LONG_WORD_SIZE]` | raw equality constraints | EXACT |
| `aux_post.is_c_0` (IsZeroWordOperation, 11 cells) | Main[190..200] | `IsZeroWordOperation.constraints` (CS6) | same name | `IsZeroWordOperation eval` | EXACT (nested) |
| `aux_post.mode_flags` (Vector T 8) | Main[201..208] | `main` opcode formula: `mode_flags[0]*15 + mode_flags[1]*16 + ... + mode_flags[7]*28` (see `DivRemChip.lean:115-126`) · binarity + sum-to-1 in bridge | 8 fields `is_div, is_divu, is_rem, is_remu, is_divw, is_remw, is_divuw, is_remuw` in declaration order | `eval` (per-variant signed/unsigned + remainder branches) · `builder.assert_bool` ×8 | EXACT (was DIVERGENT pre-`73e1ca6`; now matches upstream's 8-flag encoding) |
| `aux_post.is_overflow` | Main[209] | bridge overflow-detection constraint | `is_overflow: T` | raw `builder.assert_bool` | EXACT |
| `aux_post.is_overflow_b` (IsEqualWordOperation, 11 cells) | Main[210..220] | `IsEqualWordOperation.constraints` (CS2/CS4) | same name | `IsEqualWordOperation eval` | EXACT (nested) |
| `aux_post.is_overflow_c` (IsEqualWordOperation, 11 cells) | Main[221..231] | `IsEqualWordOperation.constraints` (CS3/CS5) | same name | `IsEqualWordOperation eval` | EXACT (nested) |
| `aux_post.{b_msb, rem_msb, c_msb, quot_msb}` (U16MSBOperation × 4) | Main[232..235] | `U16MSBOperation.constraints` (×4) | same names | `U16MSBOperation eval` ×4 | EXACT (nested) |
| `aux_post.neg_flags` (Vector T 5) | Main[236..240] | bridge constraints on b_neg / b_neg_not_overflow / b_not_neg_not_overflow / is_real_not_word / rem_neg | upstream lists these as 5 separate `T` fields | raw `builder.assert_bool` ×5 | FLATTENED (Lean packs as Vector T 5; per-cell semantics match) |
| `c_neg` | Main[241] | `main` binarity assert · used as `is_real` arg to CS7 c_neg AddOperation (was named `is_signed` pre-`f2fdaa3`) | `c_neg: T` | `AddOperation eval` (is_real arg) · `builder.assert_bool` | EXACT (renamed `f2fdaa3`) |
| `abs_c_alu_event` | Main[242] | `main` binarity assert · used as `is_real` arg to CS7's AddOp multiplicity (was named `is_w` pre-`f2fdaa3`) | `abs_c_alu_event: T` | `AddOperation eval` (is_real arg) · `builder.assert_bool` | EXACT (renamed) |
| `abs_rem_alu_event` | Main[243] | `main` binarity assert · used as `is_real` arg to CS8's AddOp multiplicity (was named `is_rem` pre-`f2fdaa3`) | `abs_rem_alu_event: T` | `AddOperation eval` (is_real arg) · `builder.assert_bool` | EXACT (renamed) |
| `is_real` | Main[244] | `CPUState.constraints` · `ProgramTable.assertion` · is_real_not_word chain · `assertZero (is_real*(is_real-1))` | `is_real` | `eval` · `CPUState eval` · `builder.assert_bool` | EXACT |
| `remainder_check_multiplicity` | Main[245] | used as `is_real` arg to CS9 LtOperationUnsigned (was named `msb_aux1` pre-`f2fdaa3` as a Lean-only placeholder) | `remainder_check_multiplicity: T` | `LtOperationUnsigned eval` (is_real arg) · `builder.assert_bool` | EXACT (renamed) |
| `next_pc_carry_value` (3) | (Lean-only) | trace-level | `adapter_cols.next_pc_carry` | `eval_untrusted_program` | FLATTENED (macro #5) |
|
> **Resolves open-question #2 at the cell-count level.** The 209-cell aux block is the constraint compiler's flattened emission of upstream's ~40 named DivRem columns (including 6 nested sub-operations). Total cell budget reconciles to ~175 named cells + ~34 sub-operation-internal cells = 209. Slot-by-slot labeling against upstream field names requires reading the bridge's 681-line `SP1Chips/DivRem/Constraints.lean` against the Rust eval impl in `alu/divrem/mod.rs` — a substantial follow-up task. The `(is_signed, is_w, is_rem)` 3-flag encoding vs upstream's 8-flag one-hot is the most semantically distinct divergence; the two are likely related by `(is_div_or_divu_or_divw_or_divuw) = ¬is_rem`, `(is_divu_or_remu_or_divuw_or_remuw) = ¬is_signed`, `(is_divw_or_remw_or_divuw_or_remuw) = is_w` — i.e. a Boolean-cube projection. Constraint-equivalence depends on the aux block enforcing the 8 modes consistently with the 3 flags.

### ShiftLeft — `ShiftLeftCols` ↔ `ShiftLeftCols<T, M>`

Constraint-usage audit: complete 2026-05-23

- Upstream (15, `alu/sll/mod.rs`): `state` · `adapter: ALUTypeReader<T>` · `a: Word<T>` · `c_bits: [T;6]` · `v_01, v_012, v_0123` · `shift_u16: [T;4]` · `lower_limb, higher_limb, limb_result: Word<T>` · `sllw_msb: U16MSBOperation<T>` · `is_sll, is_sllw, is_sllw_imm` · `adapter_cols`
- Lean (31): CPUState→4 · ALUTypeReader→14 · `shift_imm_low, shift_imm_high, msb, result: Vector T 4, bit_shift: Vector T 6, shift_pow: Vector T 3, byte_shift: Vector T 4, limb_shift: Vector T 8, result_intermediate: Vector T 5, is_sll, is_sllw, sign_extend` · `next_pc_carry_value`
- Status: **different decomposition.** Likely the same shift algorithm framed differently. Lean has `bit_shift` (6) ≈ upstream's `c_bits` (6); Lean's `shift_pow: 3` could be the `v_01/v_012/v_0123` triple; Lean's `result: Vector T 4` ≈ upstream's `a: Word<T>`. But the `byte_shift: 4`/`limb_shift: 8`/`result_intermediate: 5` Lean fields and the `shift_u16: [T;4]`/`lower_limb`/`higher_limb`/`limb_result` upstream fields don't 1-1 map. Also: Lean has no `is_sllw_imm` (vs upstream); Lean has an extra `sign_extend: T`.

**Per-column constraint usage** (audit: complete 2026-05-23 — judgement chip, different decomposition)

| Column (Lean) | Slot | Lean constraint refs | Rust column | Rust constraint refs | Status |
|---|---|---|---|---|---|
| `Main[0..27]` (clk_high … op_c_memory_diff_low) | Main[0..27] | as Bitwise rows 1-13 (CPUState + ALUTypeReader on op_a/op_b/op_c register & memory triples — note `op_c: T` here, single register-index limb, unlike ShiftRight which has `op_c: Vector T 4`) | as Bitwise | as Bitwise | FLATTENED (see Bitwise) |
| `imm_c` | Main[28] | `ALUTypeReader.constraints` (R/I selector) · `ProgramTable.assertion` | `adapter.imm_c` | `ALUTypeReader eval` · `eval_untrusted_program` | FLATTENED |
| `shift_imm_low` | Main[29] | bridge expressions for shift-amount decomposition; combined with `shift_imm_high` to recover the 6-bit shift amount from op_c_memory[3] (the shift amount byte) | (no direct analogue — upstream uses the bit decomposition without this intermediate) | — | DIVERGENT (Lean-only intermediate column for shift-amount byte handling) |
| `shift_imm_high` | Main[30] | shift-amount decomposition (paired with `shift_imm_low`) | (no direct analogue) | — | DIVERGENT (Lean-only) |
| `msb` | Main[31] | sign-extension MSB for SLLW (32→64 bit sign-extend); used by `sign_extend` propagation | `sllw_msb.msb` (`U16MSBOperation<T>` upstream — Lean stores as scalar `T`) | `U16MSBOperation eval` | FLATTENED (Lean scalar vs upstream 1-field struct; macro divergence #7) |
| `result` (4) | Main[32..35] | the 4-limb shifted output, written to op_a via ALUTypeReader.write_value · 4 byte-shift-mux clauses asserting result equals the shifted value | `a` (`Word<T>` — write-back register output) | `eval` (write-back) · `ALUTypeReader eval` | RENAMED (`result` ↔ `a`) |
| `bit_shift` (6) | Main[36..41] | 6 boolean asserts in `main` (each bit is 0 or 1) · E20-E30 = `sum(bit_shift[i] * 2^i)` recovers the bit-shift amount mod 64 · used in `byte_shift` and `shift_pow` arithmetic | `c_bits` (`[T;6]` — 6-bit decomposition of shift amount mod 64) | `eval` (per-bit booleans + sum reconstruction) | RENAMED (`bit_shift` ↔ `c_bits`; same role) |
| `shift_pow` (3) | Main[42..44] | E70/E74/E78 cumulative shift-power products: `shift_pow[0] = (b0+1)*(b1*3+1)`, `shift_pow[1] = shift_pow[0]*(b2*15+1)`, `shift_pow[2] = shift_pow[1]*(b3*255+1)` — the chained `2^k` powers for shift amounts within a byte | `(v_01, v_012, v_0123)` (3 cumulative bit-power products) | `eval` (cumulative chain) | RENAMED (`shift_pow` ↔ `(v_01, v_012, v_0123)`; 3 cells in both) |
| `byte_shift` (4) | Main[45..48] | 4 boolean asserts in `main` (one-hot selector for which byte position the shift moves the bytes to) · sum-one asserts (`(sum)*(sum-1) = 0` × is_real, E64-E65) · 4 byte-shift conditional clauses (E37, E44, E51, E58) | `shift_u16` (`[T;4]` — one-hot byte-shift selector) | `eval` (per-bit booleans + sum-one + byte-shift conditionals) | RENAMED (`byte_shift` ↔ `shift_u16`) |
| `limb_shift` (8) | Main[49..56] | 8-cell intermediate for the byte-shifted limbs (each input limb multiplied by `shift_pow[2]` and split across 2 output positions — high half spills into next limb); 4 mux assertions tying `limb_shift[2k]` and `limb_shift[2k+1]` to `result_intermediate[k]` after byte_shift mux | `lower_limb` (`Word<T>` = 4 limbs) ++ `higher_limb` (`Word<T>` = 4 limbs) — concatenated 8 cells | `eval` (byte-shift arithmetic + spill carry) | RENAMED (`limb_shift` ↔ `(lower_limb, higher_limb)` concatenation; 4+4 cells = 8) |
| `result_intermediate` (5) | Main[57..61] | 4 cells for the pre-finalization shifted result (before byte_shift mux selects) + 1 cell that participates in sign-extension chain | `limb_result` (`Word<T>` = 4 limbs) ++ (1 extra — possibly the sllw spill limb) | `eval` | DIVERGENT (5 cells vs upstream's 4-cell `limb_result`; the 5th cell's role is unclear from the bridge alone — may be a Lean-only intermediate. Verify against Rust eval.) |
| `is_sll` | Main[62] | `ProgramTable.assertion` (opcode `is_sll*8 + is_sllw*14`) · trailing `assertZero (is_sll*(is_sll-1))` · contributes to is_real sum · gates shift-arithmetic variants (full 64-bit shift) | `is_sll` | `eval` · `eval_untrusted_program` · `builder.assert_bool` | EXACT |
| `is_sllw` | Main[63] | as `is_sll` (gates 32-bit shift with sign-extension) | `is_sllw` | as `is_sll` | EXACT |
| `sign_extend` | Main[64] | Lean-only column; used in sllw sign-extension chain | (no direct analogue; upstream may compute inline) | — | DIVERGENT (Lean-only intermediate) |
| _none_ | (Lean-only) | — | `is_sllw_imm` | `eval` · `eval_untrusted_program` | DIVERGENT — Rust-only column. Upstream distinguishes SLL (R-type, shift by full register) from SLLI (I-type, shift by 6-bit immediate) AND SLLW from SLLIW via a dedicated `is_sllw_imm` flag. Lean folds these into `imm_c` (the chip-wide I/R selector) instead, so the same Lean column does double duty. Resolves part of open-question #4. |
| `next_pc_carry_value` (3) | (Lean-only) | trace-level | `adapter_cols.next_pc_carry` | `eval_untrusted_program` | FLATTENED (macro #5) |
|
> **Open-question #4 partially resolved.** ShiftLeft's decomposition is a different factoring of the same algorithm, with mostly 1-1 mappings (bit_shift↔c_bits, shift_pow↔v_*, byte_shift↔shift_u16, limb_shift↔lower_limb+higher_limb). Two residual divergences: (1) Lean adds `shift_imm_low`/`shift_imm_high` intermediates not present upstream; (2) Lean's `result_intermediate` has 5 cells where upstream `limb_result` has 4 — the 5th cell may be a sign-extension witness. Lean is also missing `is_sllw_imm` (folded into `imm_c`), and adds `sign_extend` as an extra. The slot ordering is comparable to but not identical to upstream's struct order. Net assessment: structurally equivalent, named differently, with 3-4 minor cell-count divergences.

### ShiftRight — `ShiftRightCols` ↔ `ShiftRightCols<T, M>`

Constraint-usage audit: complete 2026-05-23 (decomposed by `c3aedab` Phase 3e)

- Upstream (18, `alu/sr/mod.rs`): `state` · `adapter: ALUTypeReader<T>` · `a: Word<T>` · `b_msb, srw_msb: U16MSBOperation<T>` · `c_bits: [T;6]` · `sra_msb_v0123, v_0123, v_012, v_01` · `lower_limb, higher_limb: Word<T>` · `limb_result: [T; WORD_SIZE]` · `shift_u16: [T;4]` · `is_srl, is_sra, is_srlw, is_sraw, is_w_imm` · `adapter_cols`
- Lean: CPUState→4 · ALUTypeReader→14 · `op_a_write_value: Vector T 4` · **11 named sub-fields** (b_msb, srw_msb: U16MSBOperation T; c_bits: Vector T 6; sra_msb_v0123, v_0123, v_012, v_01: T; lower_limb, higher_limb, limb_result, shift_u16: Vector T 4) · `is_srl, is_sra, is_srlw, is_sraw, sign_extend` · `next_pc_carry_value`
- Status: **CLOSED 2026-05-23 — every cell named.** The 28-cell `intermediates_aux` was decomposed in Phase 3e (`c3aedab`) into 11 named upstream-style sub-fields matching the `ShiftRightCols<T, M>` declaration order. The two `U16MSBOperation T` fields are nested ProvableStructs; the rest are flat T / Vector T n. Lean still lacks `is_w_imm` (folded into `imm_c`) and has the extra `sign_extend` flag — these are the only remaining DIVERGENT rows.

**Per-column constraint usage** (audit: complete 2026-05-23 — slot map verified against `SP1Chips/ShiftRight/Constraints.lean` bridge)

| Column (Lean) | Slot | Lean constraint refs | Rust column | Rust constraint refs | Status |
|---|---|---|---|---|---|
| `Main[0..30]` (clk_high … op_c_memory_diff_low) | Main[0..30] | as Lt rows 1-12 (CPUState + ALUTypeReader on op_a/op_b memory + op_c `Vector T 4` + op_c_memory triple) | as Lt | as Lt | FLATTENED (see Lt) |
| `imm_c` | Main[31] | `ALUTypeReader.constraints` · `ProgramTable.assertion` | `adapter.imm_c` | `ALUTypeReader eval` · `eval_untrusted_program` | FLATTENED |
| `op_a_write_value` (4) | Main[32..35] | `ALUTypeReader.constraints` (write_value) · shift-arithmetic mux clauses pick the result via `limb_result` / `shift_u16` mux | `a` (`Word<T>` — write-back register output) | `ALUTypeReader eval` · shift-arithmetic eval | RENAMED (`op_a_write_value` ↔ `a`) |
| `b_msb` (U16MSBOperation) | Main[36] | `U16MSBOperation.constraints` (CS0/CS1) | `b_msb` | `U16MSBOperation eval` | EXACT (nested) |
| `srw_msb` (U16MSBOperation) | Main[37] | `U16MSBOperation.constraints` (CS2 for SRW) | `srw_msb` | `U16MSBOperation eval` | EXACT (nested) |
| `c_bits` (Vector T 6) | Main[38..43] | per-bit boolean asserts E59-E70 + shift-amount sum E78-E82 | `c_bits: [T;6]` | `eval` · `builder.assert_bool` ×6 | EXACT |
| `sra_msb_v0123` | Main[44] | E174-E175: Main[44] = b_msb * v_0123 | `sra_msb_v0123: T` | `eval` (SRA sign-extend mux) | EXACT |
| `v_0123` | Main[45] | E134-E135: Main[45] = Main[46] * (c3*255+1) (shift-power chain) | `v_0123: T` | `eval` | EXACT |
| `v_012` | Main[46] | E129-E130: Main[46] = Main[47] * (c2*15+1) | `v_012: T` | `eval` | EXACT |
| `v_01` | Main[47] | E124-E125: Main[47] = (c0+1)*2 * (c1*3+1) | `v_01: T` | `eval` | EXACT |
| `lower_limb` (Vector T 4) | Main[48..51] | E139-E153: each Main[48..51] * v_0123 → byte-shifted limb | `lower_limb: Word<T>` | `eval` | EXACT |
| `higher_limb` (Vector T 4) | Main[52..55] | E138-E158: high-half spill | `higher_limb: Word<T>` | `eval` | EXACT |
| `limb_result` (Vector T 4) | Main[56..59] | E163-E167: limb_result = higher_limb + lower_limb * shift mux | `limb_result: [T; WORD_SIZE]` | `eval` | EXACT |
| `shift_u16` (Vector T 4) | Main[60..63] | E89-E115: 4 boolean asserts, one-hot byte-shift selector | `shift_u16: [T;4]` | `eval` · `builder.assert_bool` ×4 | EXACT |
| `is_srl` | Main[64] | `ProgramTable.assertion` (opcode `is_srl*7 + is_sra*8 + is_srlw*22 + is_sraw*23`) · trailing `assertZero (is_srl*(is_srl-1))` · contributes to is_real sum | `is_srl` | `eval` · `eval_untrusted_program` · `builder.assert_bool` | EXACT |
| `is_sra` | Main[65] | as `is_srl` | `is_sra` | as `is_srl` | EXACT |
| `is_srlw` | Main[66] | as `is_srl` | `is_srlw` | as `is_srl` | EXACT |
| `is_sraw` | Main[67] | as `is_srl` | `is_sraw` | as `is_srl` | EXACT |
| `sign_extend` | Main[68] | E47 = `Main[68] - (is_srlw + is_sraw) * imm_c` (sign_extend is 1 for SRA/SRAW when shift amount triggers sign-extension) | (no direct analogue — upstream's `is_w_imm` is the closest, but tracks a different flag) | `eval` | DIVERGENT (Lean-only flag; remains open) |
| _none_ | (Lean-only) | — | `is_w_imm` | `eval` · `eval_untrusted_program` | DIVERGENT — Rust-only column. Upstream distinguishes the W-variant immediate from R variants via this dedicated flag; Lean folds the I/R distinction into `imm_c` and tracks sign-extension via the separate `sign_extend` field. |
| `next_pc_carry_value` (3) | (Lean-only) | trace-level | `adapter_cols.next_pc_carry` | `eval_untrusted_program` | FLATTENED (macro #5) |
|
> **Open-question #3 CLOSED 2026-05-23.** The 28-cell `intermediates_aux` was decomposed in commit `c3aedab` (Phase 3e) into 11 named sub-fields matching `ShiftRightCols<T, M>` declaration order. Slot pins verified against the bridge's E-expressions in `SP1Chips/ShiftRight/Constraints.lean`. Remaining DIVERGENT rows on this chip: `sign_extend` (Lean-only) ↔ `is_w_imm` (Rust-only) — a single Lean-vs-Rust flag-encoding choice, not a structural divergence.

### UType — `UTypeCols` ↔ `UTypeColumns<T, M>`

Constraint-usage audit: complete 2026-05-23

- Upstream (7, `utype/mod.rs`): `state` · `adapter: JTypeReader<T>` · `addend: [T; WORD_SIZE - 1]` (likely `[T;3]`) · `add_operation: AddOperation<T>` · `is_auipc, is_real` · `adapter_cols`
- Lean (16): CPUState→4 · JTypeReader→5 (`op_a, op_a_memory_prev_value, op_a_memory_prev_low, op_a_memory_diff_low, op_a_0` — note: J-type reader on the Lean side has only `op_a` + memory + `op_b_imm`, `op_c_imm`; lean's `UTypeCols` has `op_b_imm: Vector T 4, op_c_imm: Vector T 4` next, totaling 7 adapter-ish fields) · `pc_addend: Vector T 3` (≈ `addend`) · `add_result: Vector T 4` (≈ `add_operation.value`) · `is_auipc, is_real` · `next_pc_carry_value`
- Status: clean flatten with minor naming (`pc_addend`, `add_result`).

**Per-column constraint usage** (audit: complete 2026-05-23)

| Column (Lean) | Slot | Lean constraint refs | Rust column | Rust constraint refs | Status |
|---|---|---|---|---|---|
| `clk_high` | Main[0] | `CPUState.constraints` · `JTypeReader.constraints` (clk_high arg) | `state.clk_high` | `CPUState eval` · `JTypeReader eval` | FLATTENED |
| `clk_16_24` | Main[1] | `CPUState.constraints` · `JTypeReader.constraints` (via `E46 = Main[2] + Main[1]*65536`) · `SP1Clean.CPUState.assertion` | `state.clk_16_24` | `CPUState eval` · `JTypeReader eval` | FLATTENED |
| `clk_0_16` | Main[2] | as `clk_16_24` | `state.clk_0_16` | as `clk_16_24` | FLATTENED |
| `pc` (3) | Main[3..5] | `CPUState.constraints` (state.pc + next_pc) · `JTypeReader.constraints` · `ProgramTable.assertion` · trailing `assertZero (pc_addend[i] - is_auipc * pc[i])` for i∈{0,1,2} | `state.pc` | `CPUState eval` · `JTypeReader eval` · `eval_untrusted_program` | FLATTENED |
| `op_a` | Main[6] | `JTypeReader.constraints` (adapter.op_a) · `ProgramTable.assertion` | `adapter.op_a` | `JTypeReader eval` | FLATTENED |
| `op_a_memory_prev_value` (4) | Main[7..10] | `JTypeReader.constraints` | `adapter.op_a_memory.prev_value` | `JTypeReader eval` | FLATTENED |
| `op_a_memory_prev_low` | Main[11] | `JTypeReader.constraints` | `adapter.op_a_memory.access_timestamp.prev_low` | `JTypeReader eval` | FLATTENED |
| `op_a_memory_diff_low` | Main[12] | `JTypeReader.constraints` | `adapter.op_a_memory.access_timestamp.diff_low_limb` | `JTypeReader eval` | FLATTENED |
| `op_a_0` | Main[13] | `JTypeReader.constraints` (adapter.op_a_0) · `ProgramTable.assertion` (op_a_0 arg) · trailing `assertZero ((is_real - 1) * op_a_0)` | `adapter.op_a_0` | `JTypeReader eval` · `eval_untrusted_program` | FLATTENED |
| `op_b_imm` (4) | Main[14..17] | `AddOperation.constraints` (c operand = op_b_imm — yes, **passed as c**, not b, because `b = #v[Main[22..24], 0]` = `pc_addend ++ [0]`) · `JTypeReader.constraints` (adapter.op_b_imm) · `ProgramTable.assertion` (op_b_imm arg) | `adapter.op_b_imm` (J-type reader 4-limb imm) | `AddOperation eval` (c side) · `JTypeReader eval` · `eval_untrusted_program` | FLATTENED |
| `op_c_imm` (4) | Main[18..21] | `JTypeReader.constraints` (adapter.op_c_imm) · `ProgramTable.assertion` (op_c_imm arg) | `adapter.op_c_imm` (4-limb imm) | `JTypeReader eval` · `eval_untrusted_program` | FLATTENED |
| `pc_addend` (3) | Main[22..24] | `AddOperation.constraints` (b operand = `#v[pc_addend, 0]`) · trailing `assertZero (pc_addend[i] - is_auipc * pc[i])` for i∈{0,1,2} | `addend` (`[T; WORD_SIZE-1] = [T;3]`) | `AddOperation eval` (b side — see `local.addend`) · raw `builder.assert_eq` per limb | RENAMED (`pc_addend` ↔ `addend`) |
| `add_result` (4) | Main[25..28] | `AddOperation.constraints` (result `{value := add_result}`) · `JTypeReader.constraints` (write_value arg) | `add_operation.value` (`Word<T>`) | `AddOperation eval` (output) · `JTypeReader eval` (`local.add_operation.value.map(...)`) | RENAMED (`add_result` ↔ `add_operation.value`) |
| `is_auipc` | Main[29] | `ProgramTable.assertion` (opcode = `is_auipc*48 + (1-is_auipc)*49`) · `JTypeReader.constraints` (via `E7` opcode mux) · trailing `assertZero (is_auipc*(is_auipc-1))` · trailing `assertZero (pc_addend[i] - is_auipc*pc[i])` × 3 | `is_auipc` | raw `builder.assert_bool(local.is_auipc)` · opcode mux in `JTypeReader eval` · `builder.assert_eq` per pc_addend limb · `eval_untrusted_program` | EXACT |
| `is_real` | Main[30] | `CPUState.constraints` · `JTypeReader.constraints` · `AddOperation.constraints` (is_real arg = `is_real - op_a_0` via `E44`) · trailing `assertZero (Main[30]*(Main[30]-1))` · trailing `assertZero ((is_real-1)*op_a_0)` | `is_real` | `CPUState eval` · `JTypeReader eval` · `AddOperation eval` (composed is_real arg) · `builder.assert_bool` · `eval_untrusted_program` | EXACT |
| `next_pc_carry_value` (3) | (Lean-only) | trace-level `ProgramTable` | `adapter_cols.next_pc_carry` | `eval_untrusted_program` | FLATTENED (macro #5) |
| _none_ | — | — | `adapter_cols` (rest) | `eval_untrusted_program` | — (Rust-only; macro #2) |
|
> Notable subtleties: (i) UType's `AddOperation` is invoked with `b = pc_addend ++ [0]` and `c = op_b_imm` — the b/c positional convention differs from the ALU chips above (b/c map to memory triples). The `pc_addend` 3-limb width matches upstream's `addend: [T; WORD_SIZE-1]`. (ii) The `is_real` argument flowing into `AddOperation` is **not** `is_real` directly but `is_real - op_a_0` (see `E44` in the bridge) — a gating that suppresses the AddOp constraints when writing to x0. (iii) The four `(pc_addend[i] - is_auipc * pc[i] === 0)` assertZero clauses are how Lean handles upstream's `local.addend = local.is_auipc * local.state.pc`-style constraint emitted directly in Rust `eval`.

---

## Per-operation matched diffs

Lean operation structs in `SP1Operations/Operation/<Op>/Operation.lean` and `SP1Operations/Compare/<Op>/Operation.lean`; upstream in `../sp1/crates/core/machine/src/operations/<op>.rs`. The 18 matched ops below have **field-level parity** (same names, equivalent types). Listing for completeness; nothing surprising.

| Lean | Upstream | Fields Lean / Upstream | Status |
|---|---|---|---|
| `AddOperation` | `AddOperation<T>` | `value : Word F` / `value: Word<T>` | match |
| `SubOperation` | `SubOperation<T>` | `value : Word F` / `value: Word<T>` | match |
| `AddwOperation` | `AddwOperation<T>` | `value : Vector F 2, msb : U16MSBOperation F` / `value: [T; WORD_SIZE/2], msb: U16MSBOperation<T>` | match |
| `SubwOperation` | `SubwOperation<T>` | same shape as Addw | match |
| `MulOperation` | `MulOperation<T>` | 9 fields identical (carry, product, b_lower_byte, c_lower_byte, b_msb, c_msb, product_msb, b_sign_extend, c_sign_extend) | match |
| `BitwiseOperation` | `BitwiseOperation<T>` | `result : BWord F` / `result: [T; WORD_BYTE_SIZE]` | match (BWord ≈ 8-byte word) |
| `BitwiseU16Operation` | `BitwiseU16Operation<T>` | 3 fields identical | match |
| `U16MSBOperation` | `U16MSBOperation<T>` | `msb : F` / `msb: T` | match |
| `U16toU8OperationUnsafe` | `U16toU8Operation<T>` | `low_bytes : Word F` / `low_bytes: [T; WORD_SIZE]` | rename (Lean appends `Unsafe`) |
| `U16toU8OperationSafe` | (same struct, different constraint variant) | — | rename — Lean reuses the `Unsafe` struct as a "safe" *constraint*, no separate struct |
| `AddressOperation` | `AddressOperation<T>` | `addr_operation : AddrAddOperation F, top_two_limb_inv : F` / same | match |
| `AddrAddOperation` | `AddrAddOperation<T>` | `value : Vector F 3` / `value: [T;3]` | match (upstream file is `addrs_add.rs`) |
| `IsZeroOperation` (Compare/) | `IsZeroOperation<T>` | `inverse, result` / `inverse, result` | match (different dir) |
| `IsZeroWordOperation` (Compare/) | `IsZeroWordOperation<T>` | 4 fields identical (is_zero_limb vector, two halves, result) | match (different dir) |
| `IsEqualWordOperation` (Compare/) | `IsEqualWordOperation<T>` | `is_diff_zero : IsZeroWordOperation F` / same | match (different dir) |
| `U16CompareOperation` (Compare/) | `U16CompareOperation<T>` | `bit` / `bit` | match (different dir) |
| `LtOperationUnsigned` (Compare/) | `LtOperationUnsigned<T>` (`operations/slt.rs`) | 4 fields: `u16_compare_operation, u16_flags, not_eq_inv, comparison_limbs` | match |
| `LtOperationSigned` (Compare/) | `LtOperationSigned<T>` (`operations/slt.rs`) | 3 fields: `result, b_msb, c_msb` | match |

Two organizational notes:
- Upstream keeps `LtOperationSigned`/`LtOperationUnsigned` in `operations/slt.rs`; Lean puts them under `SP1Operations/Compare/`. Cosmetic.
- Lean splits the same `low_bytes: Word` struct into two namespaces (`U16toU8OperationSafe` and `U16toU8OperationUnsafe`) to attach two different constraint variants; upstream has one struct + one constraint set. This is a Lean-side organizational artifact, not a struct shape divergence.

---

## Not yet ported (upstream-only)

Listing upstream structs with no Lean counterpart at all, grouped by area. Counts are field counts on the upstream side; one-line purpose is inferred from file/name.

**Privilege / trap handling**
- `TrapExecColumns` (8 fields) — execution-time trap handler state.
- `TrapMemColumns` (18) — memory-side trap handler state.
- `TrapOperation<T>` (3) — wraps the three trap memory accesses (next_pc_reader, code_writer, pc_writer).
- `TrapPageProtOperation<T>` (sub-struct of PageOperation) — page-prot during trap.

**Page protection / memory model**
- `PageProtCols` (no fields, index-only) — page-prot lookup wrapper.
- `PageProtInitCols` (12) — page-prot init state.
- `PageProtLocalCols` (no fields) — per-shard page-prot lookup wrapper.
- `PageOperation<T>`, `PageProtOperation<T>`, `PageIsEqualOrAdjacentOperation<T>` — paging primitives.
- `MemoryInitCols` — memory init state.
- `MemoryLocalCols` (array struct) — per-shard local memory entries.
- `MemoryBumpCols` (7) — memory bump-pointer management.

**Syscalls / precompiles**
- `SyscallCols` (7) — syscall op state + flags.
- `SyscallInstrColumns` (17) — syscall instruction processing.
- `SyscallAddrOperation<T>` (3) — syscall address resolution.

**Lookup tables / global accumulators**
- `BytePreprocessedCols` (8), `ByteMultCols` (1) — byte lookup table.
- `RangePreprocessedCols` (3), `RangeMultCols` (1) — range check lookup.
- `GlobalCols` (10) — global state / digest interactions.
- `GlobalAccumulationOperation<T>` (2× SepticBlock arrays) — digest accumulator.
- `GlobalInteractionOperation<T>` (5) — septic-curve interaction + Poseidon2.

**Program / instruction fetch-decode**
- `InstructionCols` (8) — encoded instruction + immediate fields.
- `InstructionFetchCols` (14) — instruction memory access.
- `InstructionDecodeCols` (17) — instruction-type classification.
- `ProgramPreprocessedCols` (4) — PC + instruction preprocessing.

**Misc**
- `AluX0Cols` (6) — ALU ops whose destination is the zero register.
- `AdapterCols` (per-chip mode payload, polymorphic over `M: TrustMode`) — every upstream chip has an `adapter_cols: M::AdapterCols<T>` slot; in user mode this carries `next_pc_carry_value` and some other bookkeeping inlined directly into Lean Cols.

**Extra operations**
- `AndU32Operation<T>`, `XorU32Operation<T>`, `NotU32Operation<T>`, `AddU32Operation<T>` — 32-bit-width bitops; relevant for precompiles, not used by the base RV64 chips.
- `U32toU8Operation<T>` — 32→8 limb expansion.
- `FixedRotateRightOperation<T>`, `FixedShiftRightOperation<T>` — fixed-amount shifts/rotates (precompile-side).
- `Add4Operation<T>`, `Add5Operation<T>` — 4-/5-input adders (precompile-side).
- `ClkOperation<T>` (3) — clock advancement (`next_clk_16_24`, `next_clk_0_16`, `is_overflow`).

---

## Open questions worth follow-up

Status legend: `CLOSED` (resolved by the audit), `PARTIAL` (partially resolved; specific residual work named), `OPEN` (not in audit scope).

- **#1. `next_pc_carry_value` location — CLOSED 2026-05-23.** Confirmed via per-chip audit rows: every Lean chip's `next_pc_carry_value` row maps to `adapter_cols.next_pc_carry` upstream, with `eval_untrusted_program` reading `local.adapter_cols` (user-mode only) as the Rust constraint reference. The 3-limb width is consistent across 23 of 24 chips (Jal is the exception — uses `next_pc: Vector T 4` instead).
- **#2. `DivRemCols.aux: Vector T 209` — CLOSED 2026-05-23** (commit `ce4c38c` Phase 3f, follow-ups `f2fdaa3` + `73e1ca6`). Every cell of the former opaque 209-cell `aux` block is now named per upstream `DivRemCols<T, M>` declaration order: 10 named top-level fields for aux_pre (b, c, quotient, quotient_comp, remainder_comp, remainder, abs_remainder, abs_c, max_abs_c_or_1, c_times_quotient) + 2 nested `MulOperation` sub-structs + a single nested `DivRemAuxPost` sub-record holding 14 fields for aux_post. The `DivRemAuxPost` nesting is a workaround for a `deriving ProvableStruct` field-count cap (~25 flat fields) — see [[feedback-provablestruct-field-count-limit]]. Constraint-equivalence to upstream confirmed: opcode formula now uses `aux_post.mode_flags[i]` (the 8 one-hot mode flags) with the upstream weighted-sum encoding. Soundness/completeness proofs close via a deepened `obtain` destructure of `h_input`'s e19 conjunction that exposes the mode_flags equation to `subst_eqs`.
- **#3. `ShiftRightCols.intermediates_aux: Vector T 28` — CLOSED 2026-05-23** (commit `c3aedab` Phase 3e). All 28 cells decomposed into 11 named sub-fields matching `ShiftRightCols<T, M>` declaration order (b_msb, srw_msb: U16MSBOperation; c_bits: Vector T 6; sra_msb_v0123, v_0123, v_012, v_01: T; lower_limb, higher_limb, limb_result, shift_u16: Vector T 4). Slot pins verified against the bridge's E-expressions in `SP1Chips/ShiftRight/Constraints.lean`. Remaining single DIVERGENT row on this chip is `sign_extend` (Lean-only) ↔ `is_w_imm` (Rust-only) — a flag-encoding choice, not structural.
- **#4. `ShiftLeftCols` decomposition — CLOSED 2026-05-24** (Phase 2.3, see `SP1Clean/ShiftLeftChip.lean:79-102`). Three Vector blocks split into upstream-named sub-fields: `shift_pow: Vector T 3` → `v_01, v_012, v_0123: T` (Main[42..44], three scalars); `limb_shift: Vector T 8` → `lower_limb: Vector T 4 + higher_limb: Vector T 4` (Main[49..56], the two `Word<T>`s); `result_intermediate: Vector T 5` → `limb_result: Vector T 4 + sllw_msb: U16MSBOperation T` (Main[57..60] is the limb result, Main[61] is the SLLW MSB witness fed to `U16MSBOperation.constraints` in the bridge's CS0). One additional rename: `sign_extend: T` → `is_sllw_imm: T` (Main[64]; the bridge constrains Main[64] = is_sllw * imm_c = is_slliw, matching upstream's `is_sllw_imm`). The 5th-cell role is now pinned (sllw_msb). The Lean-only `shift_imm_low, shift_imm_high, msb` at Main[29..31] remain — these are slot-level adapter divergences from upstream's ALUTypeReader interpretation, not chip-level extra columns; they are out of scope for #4 and live with the broader adapter-flattening macro divergence (#4 in macro divergences list).
- **#5. `StoreByteCols` naming drift — CLOSED 2026-05-23.** 5-column rename mapping pinned in the StoreByte table: `selected_byte↔mem_limb`, `selected_byte_alt↔mem_limb_low_byte`, `result_byte↔register_low_byte`, `selected_combined↔increment`, `store_write_value↔store_value`. Slot layouts and constraint reference sets match; only field names differ. The Lean field literally named `selected_byte` is actually a 16-bit limb (not a byte) — recommend renaming to `selected_limb`.
- **#6. `BranchCols` `is_branching` and `lt_is_signed` — CLOSED 2026-05-24** (struct rename landed + Spec verified). The Lean struct field at Main[34] is now `is_branching: T` (was `lt_is_signed`); see `SP1Clean/BranchChip.lean:64` with a comment trail at lines 59-71 explaining the prior misnomer. The Lean `Spec` already passes the correct `(cols.is_blt + cols.is_bge)` as the `is_signed` argument to `LtOperationSigned.constraints` (see `SP1Clean/BranchChip.lean:118`), matching upstream's E76. **Clean-only `is_branching_aux: T` mux selector REMOVED 2026-05-24** — replaced uniformly with `cols.is_branching` (Main[34]) in `Assertion.main`, `FormalSpec`, and `fromMain`. `BranchCols` shrunk from 13 to 12 fields; binary-ness of `is_branching` is still emitted (`is_branching * (is_branching - 1) === 0` in Assertion.main, redundant with the extracted Main[34] constraint but preserves the Assertion-to-FormalSpec correspondence). Full Phase 4 closure.
- **#7. `MemoryAccessCols` granularity — CLOSED 2026-05-24** (audit hypothesis was wrong; it is NOT a `MemoryAccessColsU8` divergence). Upstream's `MemoryAccessTimestamp<T>` at `../sp1/crates/core/machine/src/memory/consistency/columns.rs:12` declares `compare_low: T` with doc-comment *"This will be true if the top 24 bits do not match"* — a boolean witness that selects which 24-bit half of the timestamp to compare. Lean's `*_memory_flag: T` has identical semantics (boolean selector for the high/low 24-bit clk comparison; see the recurrence `flag * (clk + 1) + (1 - flag) * prev_high` in `SP1Clean/LoadByteChip.lean:268-276` and the matching `compare_low` selection logic in `../sp1/crates/core/machine/src/memory/consistency/trace.rs:85`). Pure RENAMED mapping `*_memory_flag` ↔ `MemoryAccessTimestamp.compare_low`; no cell-count change; standard 2-field `MemoryAccessCols<T>` (no U8 variant needed). Applies uniformly to all 9 Load/Store chips.
- **#8. `TrustMode` mode parameter — RESOLVED 2026-05-23.** Scaffolding shipped: `SP1Clean/TrustMode.lean` defines `TrustMode := UserMode | SupervisorMode`, `UserModeReaderCols T { is_trusted: T }` (mirroring Rust `lib.rs:80`), `EmptyCols T` (mirroring Rust `lib.rs:61`), and the `AdapterCols : TrustMode → Type → Type` selector. Each of the 24 chip Cols (all except boundary `MemoryGlobalChip`, which Rust doesn't parametrize) now has `adapter_cols : SP1Clean.UserModeReaderCols T` as its last field plus a `cols.adapter_cols.is_trusted = 1` Spec conjunct. **Caveat:** chip Cols are *not* parametric over `(M : TrustMode)` because `deriving ProvableStruct` can't reduce through an abstract `M`; a SupervisorMode chip would need a parallel `*ColsSupervisor` struct. The Rust trait's other four associated types (`SyscallInstrCols`, `SliceProtCols`, `AluX0SelectorCols`, `TrapCodeCols`) are not modeled — they'd only matter for chips not yet in SP1Clean (AluX0, syscall, trap). See macro divergence #2 above and `SP1Clean/AddChip.lean` for the canonical refactored shape.

### Newly-surfaced concerns (not in original open questions)

- ~~**Mul slot-order Main[79..81] flag.**~~ **CLOSED 2026-05-24** (commit `664f53a Phase 1b: Mul — fix Main[79..81] slot-order to match upstream struct`). The Lean struct now declares fields in upstream Rust order at `SP1Clean/MulChip.lean:92-96`: `is_mul, is_mulh, is_mulhu, is_mulhsu, is_mulw`. The audit's RENAMED-slot rows for Main[79..81] are now EXACT. The opcode formula at line 110 was updated in lockstep.
- ~~**DivRem 3-flag vs 8-flag encoding.**~~ **CLOSED 2026-05-23** (commits `f2fdaa3` + `73e1ca6`). The 8 one-hot mode flags now live at `aux_post.mode_flags : Vector T 8` (Main[201..208]) — exposed by Phase 3f and used directly in the chip's opcode formula via the upstream weighted-sum encoding. The misleading 3-flag labels `(is_signed, is_w, is_rem)` at Main[241..243] were renamed to their upstream meanings (`c_neg`, `abs_c_alu_event`, `abs_rem_alu_event`) — those cells are per-sub-op multiplicity flags, not mode encoders. The orphaned `divrem_flag_projection` consistency lemma (which had proved Boolean-cube projection over the non-existent 3-flag scheme) was deleted.
- ~~**ShiftLeft `result_intermediate[4]` (the 5th cell) role.**~~ **CLOSED 2026-05-24** (Phase 2.3). Main[61] is upstream's `sllw_msb: U16MSBOperation<T>` — the MSB witness for SLLW sign-extension, consumed by `U16MSBOperation.constraints Main[33] { msb := Main[61] } Main[63]` in CS0 of `SP1Chips/ShiftLeft/Constraints.lean`. Now a top-level `sllw_msb: U16MSBOperation T` field on `ShiftLeftCols`.

### Audit-internal follow-up tasks

- 7a spot-check (planned for end of audit) — not performed during this run; do as a separate review pass.
- ~~Slot-by-slot labeling of DivRem aux:209 and ShiftRight intermediates_aux:28 against upstream named fields.~~ **DONE 2026-05-23** (`c3aedab` + `ce4c38c`).
- ~~Verification of Mul Main[79..81] slot-order claim against the constraint compiler's reflection output.~~ **DONE 2026-05-24** (commit `664f53a`).
- ~~Re-verification that the Branch `lt_is_signed`/`is_branching` semantic mismatch is real (not just a name issue) by running the constraint compiler with column-name reflection and confirming slot Main[34] is `is_branching`.~~ **DONE 2026-05-24** (struct rename + Spec verification).
- ~~ShiftLeft decomposition (open-question #4) — apply the same Phase 3e/3f pattern to map its 5 role-grouped intermediates to the upstream `c_bits` / `v_01,012,0123` / `lower_limb,higher_limb,limb_result` / `shift_u16` fields.~~ **DONE 2026-05-24** (Phase 2.3, `SP1Clean/ShiftLeftChip.lean:79-102`).
