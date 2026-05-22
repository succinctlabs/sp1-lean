# Struct-Level Divergence: SP1Clean ↔ upstream SP1

A field-level snapshot of how far our Lean column structures (in `SP1Clean/` and `SP1Operations/`) have drifted from upstream Rust (`../sp1/crates/core/machine/src/`). Constraint logic is *not* compared — only struct shape: field names, field types, and nesting.

Snapshot taken: 2026-05-21 (sp1-lean branch `dtumad/clean`, upstream `../sp1` at whatever was checked out today). **Update 2026-05-21 (later):** macro divergence #6 closed — `BranchCols` and `LtCols` now nest `LtOperationSigned`. See the Branch and Lt per-chip sections and the new sidecar at `SP1Clean/Compare/LtOperationSigned.lean`.

---

## Summary

| Layer | Lean | Upstream matched | Upstream-only |
|---|---|---|---|
| Per-chip column structs | 24 | 24 / 24 | ~20 (`AluX0`, `Trap*`, `Syscall*`, `Global*`, `Byte*`/`Range*`, `Memory{Init,Local,Bump}`, `PageProt*`, `Instruction{,Fetch,Decode}`, `ProgramPreprocessed`) |
| Sub-operation structs | 12 + 6 (`SP1Operations/{Operation,Compare}/`) | 18 / 18 | 14 (`AndU32`, `XorU32`, `NotU32`, `AddU32`, `U32toU8`, `FixedRotate`/`FixedShift`, `Add4`, `Add5`, `Clk`, `Trap`, `SyscallAddr`, `Global{Accumulation,Interaction}`, `Page*`, `TrapPageProt`) |
| Reader / state structs | 5 (`{RType,IType,JType,ALUType}Reader`, `CPUState`) | 5 / 5 (nested into upstream chip Cols) | 0 |

All 24 RISC-V instruction chips are matched 1-1 by name. The gap is everything *around* the instruction set — privilege/trap, page protection, syscalls, lookup tables, memory bookkeeping, program/instruction decode. Roughly half of upstream by struct count is unported.

---

## Methodology

- Matched by name. Sole systematic rename: upstream uses `Columns` (not `Cols`) for memory, control-flow, and `UType*` chips — Lean uses `Cols` throughout.
- Per matched chip, the comparison is **structural**: what Lean fields correspond to which upstream nested sub-struct, with deltas called out.
- Statuses used in tables: `match`, `rename`, `type-shape mismatch` (semantically identical, e.g. `Vector T 4` ↔ `Word<T>`), `nesting mismatch` (same data, different framing), `Lean-only`, `Rust-only`.
- Not compared: constraint bodies, proofs (`Spec`, `assertion.Spec`, `soundness`, `completeness`), `SP1Chips/` (which has no field names — flat `Vector (ZMod p) N`).

---

## Macro divergences (read these first)

1. **Flat vs. composed.** Every upstream chip `Cols<T, M>` is a thin 4-6-field composition: `state: CPUState<T>`, `adapter: <RType|IType|JType|ALUType>Reader<T>`, `<op>_operation: <Op>Operation<T>`, a handful of `is_*` flag bits, and `adapter_cols: M::AdapterCols<T>`. Lean inlines every one of those sub-structs into the chip's `Cols`, so our chips have 14-32 fields each. The Reader / CPUState structs *do exist* on the Lean side (`SP1Operations/Reader/`, `SP1Foundations/MemoryConsistency.lean`) — they're just not used as Cols field types.

2. **`TrustMode` (`M`) is missing.** Upstream parameterizes every chip Cols over an `M: TrustMode` and reserves one field `adapter_cols: M::AdapterCols<T>` for mode-dependent columns. Lean has no `M`, so the user-mode adapter's contents (in particular `next_pc_carry_value: Vector T 3` and possibly memory-bump-related bookkeeping) are inlined as concrete fields. We are implicitly user-mode-only.

3. **`Cols` vs `Columns` suffix.** ALU chips on both sides use `Cols` (`AddCols`, `SubCols`, `BitwiseCols`, `MulCols`, `DivRemCols`, `LtCols`, `ShiftLeftCols`, `ShiftRightCols`). Memory/control-flow/UType use `*Columns` upstream but `*Cols` on our side (`BranchCols` ↔ `BranchColumns`, `JalCols` ↔ `JalColumns`, `LoadByteCols` ↔ `LoadByteColumns`, etc.). Cosmetic but worth normalizing if/when we sync.

4. **`MemoryAccessCols<T>` is inlined as a 3-tuple.** Upstream wraps every register access in `MemoryAccessCols<T> { prev_value: Word<T>, access_timestamp: MemoryAccessTimestamp<T> }`. Lean inlines per operand as `op_X: T`, `op_X_memory_prev_value: Vector T 4`, `op_X_memory_prev_low: T`, `op_X_memory_diff_low: T` — i.e. each `*Reader<T>` is fully flattened to 13 fields (R-type) / 9 fields (I-type) / 4 fields (J-type) / 14 fields (ALU-type) in the chip Cols.

5. **`next_pc_carry_value: Vector T 3` is Lean-only at the top of 22/24 chips.** This is almost certainly upstream's `adapter_cols: M::AdapterCols<T>` payload for the user-mode adapter, surfaced explicitly because we have no `M`. The exceptions are `JalCols` and `MulCols` (no `next_pc_carry_value` — they have their own PC handling).

6. ~~**`Branch`/`Lt` flatten `LtOperationSigned<T>`.**~~ **CLOSED 2026-05-21.** Both chips now nest the operation. `BranchCols.compare_operation : LtOperationSigned T` and `LtCols.lt_operation : LtOperationSigned T` are direct ProvableStruct-derived fields. Sidecar derivations live at `SP1Clean/Compare/LtOperationSigned.lean` (covers `U16MSBOperation`, `U16CompareOperation`, `LtOperationUnsigned`, `LtOperationSigned`). Cell count and order preserved; only `MemoryConsistency.lean:285` needed a follow-up rewrite (`cols.compare_bit` → `cols.lt_operation.result.u16_compare_operation.bit`).

7. **`Mul`/`Bitwise` flatten their `*Operation`.** `MulCols` has 9 operation fields inlined (`carry, product, b_low_bytes, c_low_bytes, b_msb, c_msb, product_msb, b_sign_extend, c_sign_extend`); upstream nests them under `mul_operation: MulOperation<T>` and also stores `a: Word<T>` separately whereas Lean keeps `op_a_write_value: Vector T 4`. `BitwiseCols` inlines `BitwiseU16Operation<T>` (3 sub-fields).

8. **Two opaque `aux` blobs.** `DivRemCols.aux: Vector T 209` and `ShiftRightCols.intermediates_aux: Vector T 28` are unnamed packed-vector witnesses on our side. Upstream gives each constituent a name (DivRem has 40+ named fields including `quotient`, `remainder`, `c_times_quotient_lower: MulOperation<T>`, etc.). These two chips are where the structural picture is least transparent — any deep audit should start by labeling the entries of these `aux` vectors against the upstream field list.

9. **`ShiftLeft` decomposition disagrees.** Upstream `ShiftLeftCols`: `c_bits: [T;6], v_01, v_012, v_0123, shift_u16: [T;4], lower_limb, higher_limb, limb_result, sllw_msb`. Lean `ShiftLeftCols`: `shift_imm_low, shift_imm_high, msb, result, bit_shift: Vector T 6, shift_pow: Vector T 3, byte_shift: Vector T 4, limb_shift: Vector T 8, result_intermediate: Vector T 5, sign_extend`. Same family of computations; not the same factoring. Mapping these 1-1 will require constraint-level reading.

10. **Coverage gap is the system layer, not the ISA layer.** All 24 user-mode RISC-V instruction chips have Lean counterparts. Everything upstream that's *not* an instruction — privilege/trap, paging, syscalls, lookup tables (byte/range), memory init/local/bump, program/instruction fetch and decode, the `AluX0` x0-destination special case, the global digest — has no Lean equivalent yet. Whether to port these is a scope question, not a divergence-cleanup question.

---

## Per-chip matched diffs

In every section: upstream side shows the composed shape, then Lean side names the inlined sub-struct ranges. Status lines call out non-flatten differences. Chip files: Lean at `SP1Clean/<Chip>Chip.lean`, upstream at `../sp1/crates/core/machine/src/<dir>/<file>.rs` (paths given once per section).

### Add — `AddCols` ↔ `AddCols<T, M>`
- Upstream (5 fields, `alu/add_sub/add.rs`): `state: CPUState<T>` · `adapter: RTypeReader<T>` · `add_operation: AddOperation<T>` · `is_real: T` · `adapter_cols: M::AdapterCols<T>`
- Lean inlines to 20 fields: CPUState→4 · RTypeReader→13 · AddOperation→1 (`op_a_write_value: Vector T 4` ↔ `add_operation.value: Word<T>`) · `is_real` · `next_pc_carry_value: Vector T 3`
- Status: clean flatten. `next_pc_carry_value` lives in `adapter_cols` upstream.

### Addi — `AddiCols` ↔ `AddiCols<T, M>`
- Upstream (5, `alu/add_sub/addi.rs`): `state` · `adapter: ITypeReader<T>` · `add_operation: AddOperation<T>` · `is_real` · `adapter_cols`
- Lean inlines to 17: CPUState→4 · ITypeReader→9 (op_a + memory triple, op_b + memory triple, op_a_0, op_c_imm: Vector T 4) · AddOperation→1 · `is_real` · `next_pc_carry_value`
- Status: clean flatten.

### Addw — `AddwCols` ↔ `AddwCols<T, M>`
- Upstream (5, `alu/add_sub/addw.rs`): `state` · `adapter: ALUTypeReader<T>` · `addw_operation: AddwOperation<T>` · `is_real` · `adapter_cols`
- Lean inlines to 22: CPUState→4 · ALUTypeReader→14 (op_a, op_b, op_c with `op_c: Vector T 4`, `imm_c: T`, three memory triples) · AddwOperation→2 (`addw_value: Vector T 2` + `addw_msb: T` ↔ `value` + `msb: U16MSBOperation<T>`) · `is_real` · `next_pc_carry_value`
- Status: clean flatten. Note Lean stores `addw_msb: T` where upstream nests `msb: U16MSBOperation<T>` (a 1-field struct over `msb: T`) — same single bit either way.

### Sub — `SubCols` ↔ `SubCols<T, M>`
- Upstream (5, `alu/add_sub/sub.rs`): `state` · `adapter: RTypeReader<T>` · `sub_operation: SubOperation<T>` · `is_real` · `adapter_cols`
- Lean inlines to 20 (same shape as Add). Status: clean flatten.

### Subw — `SubwCols` ↔ `SubwCols<T, M>`
- Upstream (5, `alu/add_sub/subw.rs`): `state` · `adapter: RTypeReader<T>` · `subw_operation: SubwOperation<T>` · `is_real` · `adapter_cols`
- Lean inlines to 21: CPUState→4 · RTypeReader→13 · SubwOperation→2 (`subw_value: Vector T 2`, `subw_msb: T`) · `is_real` · `next_pc_carry_value`
- Status: clean flatten. **Adapter mismatch noted**: Lean's `SubwCols` carries 13 R-type-shaped fields with `op_c: T` (R-type), but upstream uses `RTypeReader<T>`. This matches Lean. Contrast with `Addw` which uses `ALUTypeReader` upstream and Lean encodes `op_c: Vector T 4` + `imm_c: T`. Verify that `SubwChip` really wants R-type (no immediate variant) — Addw and Subw asymmetry is worth checking against the SP1 instruction set tables.

### Bitwise — `BitwiseCols` ↔ `BitwiseCols<T, M>`
- Upstream (7, `alu/bitwise/mod.rs`): `state` · `adapter: ALUTypeReader<T>` · `bitwise_operation: BitwiseU16Operation<T>` · `is_xor, is_or, is_and` · `adapter_cols`
- Lean (25): CPUState→4 · ALUTypeReader→14 · BitwiseU16Operation→3 inlined (`b_low_bytes: Vector T 4, c_low_bytes: Vector T 4, bitwise_result: Vector T 8`) · `is_xor, is_or, is_and` · `next_pc_carry_value`
- Status: nesting mismatch — Lean flattens `BitwiseU16Operation`'s three sub-operations (`b_low_bytes: U16toU8Operation<T>` → `Vector T 4`, ditto `c_low_bytes`, `bitwise_operation.result: [T;8]` → `bitwise_result`). Same data, three named tuples vs. one nested op.

### Lt — `LtCols` ↔ `LtCols<T, M>`
- Upstream (6, `alu/lt/mod.rs`): `state` · `adapter: ALUTypeReader<T>` · `is_slt, is_sltu` · `lt_operation: LtOperationSigned<T>` · `adapter_cols`
- Lean (22): CPUState→4 · ALUTypeReader→14 · `is_slt, is_sltu` · `lt_operation: LtOperationSigned T` (nested) · `next_pc_carry_value`
- Status: nesting parity for `lt_operation`. `LtOperationSigned`, `LtOperationUnsigned`, `U16CompareOperation`, `U16MSBOperation` get sidecar `deriving instance ProvableStruct` in `SP1Clean/Compare/LtOperationSigned.lean`. Remaining divergence: ALUTypeReader still inlined (14 fields vs 1 nested upstream); `next_pc_carry_value` still Lean-only.

### Branch — `BranchCols` ↔ `BranchColumns<T, M>`
- Upstream (10, `control_flow/branch/columns.rs`): `state` · `adapter: ITypeReader<T>` · `next_pc: [T;3]` · `is_beq, is_bne, is_blt, is_bge, is_bltu, is_bgeu, is_branching` · `compare_operation: LtOperationSigned<T>` · `adapter_cols`
- Lean (23): CPUState→4 · ITypeReader→9 · `next_pc: Vector T 3` · `is_beq, is_bne, is_blt, is_bge, is_bltu, is_bgeu` · `lt_is_signed` · `compare_operation: LtOperationSigned T` (nested) — **Lean lacks `is_branching: T`** and **gains `lt_is_signed: T`** (which is upstream-derivable: `is_blt + is_bge`).
- Status: nesting parity for `compare_operation`. Sidecar derivations live in `SP1Clean/Compare/LtOperationSigned.lean`. Remaining divergence: ITypeReader still inlined; Lean-only `lt_is_signed` and Rust-only `is_branching` are open questions (#6 in this doc) — orthogonal to the nesting refactor.

### Jal — `JalCols` ↔ `JalColumns<T, M>`
- Upstream (6, `control_flow/jal/columns.rs`): `state` · `adapter: JTypeReader<T>` · `add_operation: AddOperation<T>` · `op_a_operation: AddOperation<T>` · `is_real` · `adapter_cols`
- Lean (14): CPUState→4 · JTypeReader→4 (op_a, op_a_memory triple — but Lean lists `op_a, op_a_memory_prev_value, op_a_memory_prev_low, op_a_memory_diff_low, op_a_0`) · `imm: Vector T 4` (≈ J-type imm) · `op_c: Vector T 4` · `next_pc: Vector T 4` · `op_a_write_value: Vector T 4` · `is_real`
- Status: **divergence — Lean has no `next_pc_carry_value` here.** Upstream has TWO `AddOperation`s nested (one for PC, one for op_a writeback). Lean encodes one as `next_pc: Vector T 4` and one as `op_a_write_value: Vector T 4`, with `imm` and `op_c` as separate raw fields. The 4-limb vs 3-limb PC encoding is a visible discrepancy worth a closer look (upstream PC is 3 limbs; `next_pc` here is 4 — likely an internal addition result before being trimmed back to PC width).

### Jalr — `JalrCols` ↔ `JalrColumns<T, M>`
- Upstream (7, `control_flow/jalr/columns.rs`): `state` · `adapter: ITypeReader<T>` · `is_real` · `add_operation: AddOperation<T>` · `op_a_operation: AddOperation<T>` · `lsb: T` · `adapter_cols`
- Lean (18): CPUState→4 · ITypeReader→9 · `is_real` · `jump_target: Vector T 4` (≈ `add_operation.value`) · `op_a_write_value: Vector T 4` (≈ `op_a_operation.value`) · `low_bit: T` (rename of `lsb`)
- Status: clean flatten. Two `AddOperation`s become two named `Vector T 4`s. `lsb`/`low_bit` is the same scalar.

### Load{Byte,Half,Word,Double,X0}
Shared upstream skeleton (`memory/instructions/load/<load_*>.rs`): `state` · `adapter: ITypeReader<T>` · `address_operation: AddressOperation<T>` · `memory_access: MemoryAccessCols<T>` · variant fields · `adapter_cols`.

Shared Lean skeleton: CPUState→4 · ITypeReader→9 · `AddressOperation` inlined→4 (`addr_value: Vector T 3` + `addr_top_two_limb_inv: T` ↔ `addr_operation.value: [T;3]` + `top_two_limb_inv: T`) · `MemoryAccessCols` inlined→6 (`load_prev_value: Vector T 4, load_memory_prev_high, load_memory_prev_low, load_memory_flag, load_memory_diff_low, load_memory_diff_high`) · variant fields · `next_pc_carry_value`.

**Status:** clean flatten with one Lean expansion. Lean's memory_access is 6 fields where upstream's `MemoryAccessCols<T>` is 2 nested fields (`prev_value: Word<T>` + `access_timestamp: MemoryAccessTimestamp<T>`). The Lean expansion (`memory_flag`, `memory_diff_high`, `memory_prev_high`) suggests we are inlining a richer timestamp than the `RegisterAccessTimestamp` 2-field version — likely the full `MemoryAccessTimestamp` (`prev_low_limb, prev_high_limb, diff_low_limb, diff_high_limb`) plus a separate flag column. This is the **`MemoryAccessColsU8` vs `MemoryAccessCols` distinction** upstream — worth checking which variant each load chip actually uses upstream.

Variant fields:
- **LoadByte (32):** Lean has `byte_selector_{top,mid,lo}, selected_byte, selected_byte_alt, result_byte, signed_extension_flag, is_lb, is_lbu`. Upstream `offset_bit: [T;3], selected_limb, selected_limb_low_byte, selected_byte, msb, is_lb, is_lbu`. Same family; Lean splits `selected_limb` as `selected_byte_alt` and names the signed-extension bit differently.
- **LoadHalf (29):** Lean `half_offset_bit{1,2}, op_a_write_value_lo, signed_extension_msb, is_lh, is_lhu`. Upstream `offset_bit: [T;2], selected_half, msb: U16MSBOperation<T>, is_lh, is_lhu`. Lean lacks a top-level `selected_half` aggregate.
- **LoadWord (28):** Lean `word_offset_flag, op_a_write_value_lo: Vector T 2, signed_extension_msb, is_lw, is_lwu`. Upstream `offset_bit: T, selected_word: [T;2], msb: U16MSBOperation<T>, is_lw, is_lwu`. Aligns 1-1 modulo names.
- **LoadDouble (24):** Lean `is_real`. Upstream `is_real`. Identical past the shared skeleton.
- **LoadX0 (31):** Lean has the 3-element `byte_offset_selectors: Vector T 3` plus all 7 `is_l*` flags. Upstream `offset_bit: [T;3]` + 7 `is_l*` flags. Aligns.

### Store{Byte,Half,Word,Double}
Shared upstream skeleton (`memory/instructions/store/<store_*>.rs`): `state` · `adapter: ITypeReader<T>` · `address_operation: AddressOperation<T>` · `memory_access: MemoryAccessCols<T>` · variant fields · `is_real` · `adapter_cols`.

Shared Lean skeleton: same as Load, but with `store_*` prefix on memory-access fields and `store_write_value: Word<T>` instead of `load_prev_value`.

- **StoreByte (32):** Lean has `byte_selector_{top,mid,lo}, selected_byte, selected_byte_alt, result_byte, selected_combined, store_write_value`. Upstream `offset_bit: [T;3], mem_limb, mem_limb_low_byte, register_low_byte, increment, store_value`. Naming completely diverged here — should be cross-checked field by field in a follow-up audit, this is the chip most likely to have drifted in semantics, not just labels.
- **StoreHalf (27):** Lean `byte_selector_{upper,lower}, store_write_value`. Upstream `offset_bit: [T;2], store_value`.
- **StoreWord (26):** Lean `word_offset_flag, store_write_value`. Upstream `offset_bit: T, store_value`.
- **StoreDouble (24):** Just the shared skeleton + `is_real`. Aligned.

### Mul — `MulCols` ↔ `MulCols<T, M>`
- Upstream (10, `alu/mul/mod.rs`): `state` · `adapter: RTypeReader<T>` · `a: Word<T>` · `mul_operation: MulOperation<T>` · `is_mul, is_mulh, is_mulhu, is_mulhsu, is_mulw` · `adapter_cols`
- Lean (32): CPUState→4 · RTypeReader→13 · `op_a_write_value: Vector T 4` (≈ upstream `a: Word<T>`) · MulOperation inlined→9 (`carry: Vector T 16, product: Vector T 16, b_low_bytes: Vector T 4, c_low_bytes: Vector T 4, b_msb, c_msb, product_msb, b_sign_extend, c_sign_extend`) · `is_mul, is_mulh, is_mulw, is_mulhsu, is_mulhu`
- Status: nesting mismatch. Note Lean `MulOperation` itself has the same 9 fields — we just *also* inline them at chip level. Note **no `next_pc_carry_value`** here. Also, upstream `MulOperation.b_lower_byte/c_lower_byte: U16toU8Operation<T>` (4 limbs each) — Lean encodes as `Vector T 4` directly.

### DivRem — `DivRemCols` ↔ `DivRemCols<T, M>`
- Upstream (~44, `alu/divrem/mod.rs`): `state` · `adapter: RTypeReader<T>` · `a, b, c: Word<T>` · `quotient, quotient_comp, remainder_comp, remainder, abs_remainder, abs_c, max_abs_c_or_1: Word<T>` · `c_times_quotient: [T; LONG_WORD_SIZE]` · `c_times_quotient_lower, c_times_quotient_upper: MulOperation<T>` · `c_neg_operation, rem_neg_operation: AddOperation<T>` · `remainder_lt_operation: LtOperationUnsigned<T>` · `carry: [T; LONG_WORD_SIZE]` · `is_c_0: IsZeroWordOperation<T>` · `is_div, is_divu, is_rem, is_remu, is_divw, is_remw, is_divuw, is_remuw, is_overflow, is_real_not_word, rem_neg, c_neg, abs_c_alu_event, abs_rem_alu_event, is_real, remainder_check_multiplicity, b_neg, b_neg_not_overflow, b_not_neg_not_overflow, msb_aux1` (`msb_aux1` is Lean — see below) · `is_overflow_b, is_overflow_c: IsEqualWordOperation<T>` · `b_msb, rem_msb, c_msb, quot_msb: U16MSBOperation<T>` · `adapter_cols`
- Lean (25): CPUState→4 · RTypeReader→13 · `op_a_write_value: Vector T 4` · `aux: Vector T 209` (opaque) · `is_signed, is_w, is_rem, is_real, msb_aux1` · `next_pc_carry_value`
- Status: **major divergence — `aux: Vector T 209` collapses ~40 named upstream columns into one packed vector.** This is the single most opaque spot in the divergence; meaningful struct comparison requires labeling the 209 entries. Lean's `is_signed, is_w, is_rem` are mode selectors that upstream spells out as 8 separate `is_div/divu/rem/remu/divw/remw/divuw/remuw` flags — these decompositions are likely equivalent under a fixed encoding but should be verified.

### ShiftLeft — `ShiftLeftCols` ↔ `ShiftLeftCols<T, M>`
- Upstream (15, `alu/sll/mod.rs`): `state` · `adapter: ALUTypeReader<T>` · `a: Word<T>` · `c_bits: [T;6]` · `v_01, v_012, v_0123` · `shift_u16: [T;4]` · `lower_limb, higher_limb, limb_result: Word<T>` · `sllw_msb: U16MSBOperation<T>` · `is_sll, is_sllw, is_sllw_imm` · `adapter_cols`
- Lean (31): CPUState→4 · ALUTypeReader→14 · `shift_imm_low, shift_imm_high, msb, result: Vector T 4, bit_shift: Vector T 6, shift_pow: Vector T 3, byte_shift: Vector T 4, limb_shift: Vector T 8, result_intermediate: Vector T 5, is_sll, is_sllw, sign_extend` · `next_pc_carry_value`
- Status: **different decomposition.** Likely the same shift algorithm framed differently. Lean has `bit_shift` (6) ≈ upstream's `c_bits` (6); Lean's `shift_pow: 3` could be the `v_01/v_012/v_0123` triple; Lean's `result: Vector T 4` ≈ upstream's `a: Word<T>`. But the `byte_shift: 4`/`limb_shift: 8`/`result_intermediate: 5` Lean fields and the `shift_u16: [T;4]`/`lower_limb`/`higher_limb`/`limb_result` upstream fields don't 1-1 map. Also: Lean has no `is_sllw_imm` (vs upstream); Lean has an extra `sign_extend: T`.

### ShiftRight — `ShiftRightCols` ↔ `ShiftRightCols<T, M>`
- Upstream (18, `alu/sr/mod.rs`): `state` · `adapter: ALUTypeReader<T>` · `a: Word<T>` · `b_msb, srw_msb: U16MSBOperation<T>` · `c_bits: [T;6]` · `sra_msb_v0123, v_0123, v_012, v_01` · `lower_limb, higher_limb: Word<T>` · `limb_result: [T; WORD_SIZE]` · `shift_u16: [T;4]` · `is_srl, is_sra, is_srlw, is_sraw, is_w_imm` · `adapter_cols`
- Lean (26): CPUState→4 · ALUTypeReader→14 · `op_a_write_value: Vector T 4` · `intermediates_aux: Vector T 28` (opaque) · `is_srl, is_sra, is_srlw, is_sraw, sign_extend` · `next_pc_carry_value`
- Status: **opaque-blob divergence**, similar to DivRem. Audit will need to identify which upstream column corresponds to which slot in `intermediates_aux`. Lean has no `is_w_imm`.

### UType — `UTypeCols` ↔ `UTypeColumns<T, M>`
- Upstream (7, `utype/mod.rs`): `state` · `adapter: JTypeReader<T>` · `addend: [T; WORD_SIZE - 1]` (likely `[T;3]`) · `add_operation: AddOperation<T>` · `is_auipc, is_real` · `adapter_cols`
- Lean (16): CPUState→4 · JTypeReader→5 (`op_a, op_a_memory_prev_value, op_a_memory_prev_low, op_a_memory_diff_low, op_a_0` — note: J-type reader on the Lean side has only `op_a` + memory + `op_b_imm`, `op_c_imm`; lean's `UTypeCols` has `op_b_imm: Vector T 4, op_c_imm: Vector T 4` next, totaling 7 adapter-ish fields) · `pc_addend: Vector T 3` (≈ `addend`) · `add_result: Vector T 4` (≈ `add_operation.value`) · `is_auipc, is_real` · `next_pc_carry_value`
- Status: clean flatten with minor naming (`pc_addend`, `add_result`).

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

- **`next_pc_carry_value` location.** Confirm that upstream stashes this in `adapter_cols: M::AdapterCols<T>` for the user-mode adapter, and that the 3-limb width matches. If yes, this is the cleanest single re-org win on our side.
- **`DivRemCols.aux: Vector T 209`.** Define a labeled mapping from the 209-slot vector to upstream's named fields. This is the prerequisite for any DivRem-side structural audit.
- **`ShiftRightCols.intermediates_aux: Vector T 28`.** Same as DivRem.
- **`ShiftLeftCols` decomposition.** Verify Lean's `byte_shift`/`limb_shift`/`shift_pow`/`result_intermediate` is the same algorithm as upstream's `c_bits`/`v_*`/`shift_u16`/`lower_limb`/`higher_limb`/`limb_result`. Lean is missing `is_sllw_imm`.
- **`StoreByteCols` naming drift.** `selected_byte_alt`, `result_byte`, `selected_combined` vs upstream `mem_limb`, `mem_limb_low_byte`, `register_low_byte`, `increment`. Could be the same set of witnesses under different names, but the naming gap is large enough to warrant a constraint-level read-through before assuming parity.
- **`BranchCols` `is_branching` and `lt_is_signed`.** Check whether Lean derives `is_branching` from the six condition flags inside the constraint, or whether it should be a column.
- **`MemoryAccessCols` granularity.** Lean inlines 6 fields per memory access; upstream `MemoryAccessCols<T>` is 2 fields nesting `MemoryAccessTimestamp<T>`. Worth checking if Lean is using the `MemoryAccessTimestamp` (4 sub-fields) or the `MemoryAccessColsU8` variant.
- **`TrustMode` mode parameter.** Decision needed before any system-layer chips are ported: do we mirror the polymorphic `M: TrustMode` design, or commit to user-mode-only and hardcode? Affects every existing chip Cols if we adopt later.
