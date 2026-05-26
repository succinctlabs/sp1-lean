# SP1Clean/Chips/Spec.lean — per-`FormalSpec` audit

Snapshot of `SP1Clean/Chips/Spec.lean` classified into four categories.
The audit asks, for every `def FormalSpec`: is the Spec a minimal
pure-semantic form, an internals-exposing form with an RV64 wrapper, a
faithful constraint mirror without RV64, or still incomplete relative
to chip `main` / upstream Rust?

This is a snapshot — re-run the rubric below whenever
`SP1Clean/Chips/Spec.lean` or a chip's `main` changes shape. The
verdict table reflects the repo at branch `dtumad/clean` (2026-05-26),
incorporating in order: the Phase 1 (d)-resolution pass (ungated
`*.AssertionGated` phantom rows for Control chips removed — the audit
conflated them with the single `Assertion` form, which IS already the
gated form per project direction; `MemoryGlobal` promoted from absent
to a partial scaffold of 10 range-check lookups + `IsZeroOp.Assertion`
×2 + value decomp, with `LtUnsignedOp` + bit/x0 asserts deferred to
Phase 4.5); the `Subw` (c)→(b) promotion via the
`rv64_subw_eq_of_subwop_spec` bridge adding an `RV64.subw` trailing
conjunct to `FormalSpec`; and the subsequent AddwChip + UTypeChip
phase-(b)→(a) migration that closed those two entries of the (b) tier.

## Classification rubric

For each `def FormalSpec` (and `AssertionGated.FormalSpec`):

- **(a)** *Minimal semantic*. Pure semantic top layer:
  `is_real = 1 → isU64 result ∧ toBitVec64 result = RV64.<op> …`,
  composed with flag-threaded `<Reader>.Gated.Assertion.Spec` +
  `CPUState.Gated.Assertion.Spec`. **No** chip-internal carry/MSB/byte
  columns surfaced.
- **(b)** *Internals + RV64*. Exposes chip-internal columns
  (carry chains, low-byte limbs, MSB sign bits, 32-bit intermediates)
  **and** closes with a pure-BitVec `RV64.<op>` clause.
- **(c)** *Faithful mirror, no RV64*. Sub-circuit composition matches
  the chip's `main` and upstream Rust constraint count, but no
  `RV64.*` semantic conjunct exists yet. Sail `execute_*_pure*`
  escape hatches count as "no RV64" — record under (c) and flag the
  available `RV64.*` candidate.
- **(d)** *Incomplete*. Either the Spec drops sub-circuits that
  `main` emits, the chip's `main` itself drops sub-circuits that the
  upstream Rust emits, or the chip is absent from `Spec.lean`
  entirely.

### Decision order

1. If the chip has no Spec entry at all → **(d)**.
2. If the chip's `main` emits subcircuits the Spec drops → **(d)**.
3. If the chip's `main` itself omits subcircuits the upstream Rust
   composes → **(d)** (Spec can't be ahead of `main`).
4. If the Spec uses Sail `execute_*_pure*` or has no semantic top
   layer → **(c)**.
5. If the Spec closes with `RV64.<op>` and exposes chip internals →
   **(b)**.
6. Otherwise (Spec closes with `RV64.<op>` and is internals-free) →
   **(a)**.

## Verdict table

### ALU chips

| Namespace | Verdict | Justification |
|---|---|---|
| `SP1Clean.Add` | **(a)** | `CPUState.Gated` + `RTypeReader.Gated` + `op_a_0 = 0` + `is_real = 1 → isU64 ∧ toBitVec64 = RV64.add …`. |
| `SP1Clean.Addi` | **(a)** | Same shape, `ITypeReader.Gated` + `RV64.addi`. |
| `SP1Clean.Sub` | **(a)** | Same shape, `RV64.sub`. |
| `SP1Clean.Addw` | **(a)** | Same shape, `ALUTypeReader.Gated` + `RV64.addw` (uniform across `imm_c ∈ {0, 1}` since the reader supplies `op_c_memory.prev_value` correctly for both ADDW and ADDIW). `AddwOp.Spec` internals exposure dropped (2026-05-26 migration); the carry chain is reconstructed on demand via `addwOp_spec_iff_rv64_addw` (`SP1Clean/Chips/ALU/AddwChip/Lemmas.lean`) which inverts the sign-extension via `BitVec.setWidth_signExtend_eq_self`. |
| `SP1Clean.Subw` | **(b)** | `SubwOp` internals (`subw_value`, `subw_msb`) + Sail `execute_RTYPEW_pure_32_w` 32-bit BV identity + `RV64.subw` 64-bit clause. The BV32 triple is retained as the internals exposure (completeness drives `SubwOperation.iff_sp1_full.mpr` from it to witness `subw_value`/`subw_msb`); the BV64 conjunct is derived inline via `rv64_subw_eq_of_subwop_spec`. |
| `SP1Clean.UType` | **(a)** | `CPUState.Gated` + `AddOp.Assertion.Spec` (gated by `is_real - op_a_0`) + `JTypeReader.Gated` + 5 scalar gates + `is_real = 1 → op_a_0 = 0 → isU64 add_result ∧ toBitVec64 = if is_auipc then RV64.auipc imm pc else RV64.lui imm`. 2026-05-26 migration dropped the raw `AddOperation.constraints.allHold` envelope and `cpuStateSpec → CPUState.Gated.Assertion.Spec`; the sign-extension identity comes from `Opcode.trusted_instr` for opcodes 48 (AUIPC) and 49 (LUI). |
| `SP1Clean.Mul` | **(c)** | `MulOp.Spec` internals + `RTypeReader.Gated`. Matches `MulChip/Aggregate.lean:520 main`. `RV64.mul/mulh/mulhu/mulhsu/mulw` available. |
| `SP1Clean.DivRem` | **(c)** | MulOp×2 + IsEqualWordOp×4 + IsZeroWordOp + AddOp×2 + LtUnsignedOp + U16MSBOp×7. Matches `DivRemChip/Aggregate.lean:189 main`. `RV64.div/divu/divw/divuw/rem/remu/remw/remuw` available. |
| `SP1Clean.Bitwise` | **(d)** | Spec matches the gated `main` at `BitwiseChip/Aggregate.lean:316`, but **both** drop `BitwiseU16Operation` + `ALUTypeReader` that upstream Rust `alu/bitwise/mod.rs` emits. Self-flagged in the doc comment. `RV64.and/or/xor` available. |
| `SP1Clean.ShiftLeft` | **(d)** | Spec matches `ShiftLeftChip/Aggregate.lean:379 main`; both omit the shift-power lookup + `ALUTypeReader` from Rust `alu/sll/mod.rs`. `RV64.sll/sllw` available. |
| `SP1Clean.ShiftRight` | **(d)** | Same as ShiftLeft; both omit `MSBOperation`-derived shift sub-ops from Rust `alu/sr/mod.rs`. `RV64.srl/sra/srlw/sraw` available. |
| `SP1Clean.Lt` | **(d)** | Spec matches `LtChip/Aggregate.lean:286 main` but both omit `LtOperationSigned` that upstream `alu/lt/mod.rs` composes. `RV64.slt/sltu` available. |

### Control chips

Branch/Jal/Jalr each expose a single full gated form: `Assertion.main`
+ `assertion : FormalAssertion` at the top of their `Aggregate.lean`.
There is **no separate `AssertionGated.main`** — the Memory chips' two-
tier (`Assertion` partial / `AssertionGated` full) split exists because
those chips defer the `load_mem/+1` access; Control chips have no
analogous deferral. Per the project direction that ungated forms are
transitional and going away, the `Assertion.FormalSpec` block in
`Spec.lean` is the canonical gated mirror for each.

| Namespace | Verdict | Justification |
|---|---|---|
| `SP1Clean.Branch.Assertion` | **(c)** | `GatedAddOp.Spec` ×2 + `next_pc[i]` range bounds + `OperandAccess` ×2. Matches `BranchChip/Aggregate.lean:316 main`. No `RV64.<branch>` wrapper (branch sem is `Bool`, non-trivial upgrade). |
| `SP1Clean.Jal.Assertion` | **(c)** | Raw `toBitVec64 next_pc = pc + op_b_imm` + `toBitVec64 op_a_write_value = pc + 4` (no `RV64.jal` exists). Has `OperandAccess` ×1 + `ProgramTable.Spec`. Matches `JalChip/Aggregate.lean:371 main`. |
| `SP1Clean.Jalr.Assertion` | **(c)** | `GatedAddOp.Spec` + `OperandAccess` ×2 + scalar gates. Matches `JalrChip/Aggregate.lean:260 main`. |

### Memory chips

Each Load/Store chip has both an `Assertion.FormalSpec` (deliberately
partial — drops `load_mem/+1` etc.) and an `AssertionGated.FormalSpec`
(full sub-circuit composition).

| Namespace | Verdict | Justification |
|---|---|---|
| `SP1Clean.LoadByte.Assertion` | **(d)** | Partial pre-stage (doc: "load_mem/+1 access is deferred"). Matches `Assertion.main` but `main` itself omits `AddrAddOp` / `AddressShape` / `LoadMemoryAccessGated` / `LoadByteSelector` vs upstream. |
| `SP1Clean.LoadByte.AssertionGated` | **(c)** | Full mirror: `CPUState` + `AddrAddOp` + `AddressShape` + `ITypeReader` + `LoadMemoryAccessGated` + `LoadByteSelector` + gates. Matches `AssertionGated.main`. |
| `SP1Clean.LoadHalf.Assertion` | **(d)** | Partial pre-stage. |
| `SP1Clean.LoadHalf.AssertionGated` | **(c)** | Full mirror with `LoadHalfSelector`. |
| `SP1Clean.LoadWord.Assertion` | **(d)** | Partial pre-stage. |
| `SP1Clean.LoadWord.AssertionGated` | **(c)** | Full mirror with `LoadWordSelector`. |
| `SP1Clean.LoadDouble.Assertion` | **(d)** | Partial pre-stage. |
| `SP1Clean.LoadDouble.AssertionGated` | **(c)** | Full mirror (no selector — 8-byte aligned load). |
| `SP1Clean.LoadX0.Assertion` | **(d)** | Partial pre-stage (multi-variant: `is_lb + is_lbu + is_lh + is_lhu + is_lw + is_lwu + is_ld`). |
| `SP1Clean.LoadX0.AssertionGated` | **(c)** | Full mirror; `op_a_0 = 1` (x0 destination). |
| `SP1Clean.StoreByte.Assertion` | **(d)** | Partial pre-stage. |
| `SP1Clean.StoreByte.AssertionGated` | **(c)** | Full mirror with `StoreByteAssembler` + `StoreMemoryAccessGated`. |
| `SP1Clean.StoreHalf.Assertion` | **(d)** | Partial pre-stage. |
| `SP1Clean.StoreHalf.AssertionGated` | **(c)** | Full mirror with `StoreHalfAssembler`. |
| `SP1Clean.StoreWord.Assertion` | **(d)** | Partial pre-stage. |
| `SP1Clean.StoreWord.AssertionGated` | **(c)** | Full mirror with `StoreWordAssembler`. |
| `SP1Clean.StoreDouble.Assertion` | **(d)** | Partial pre-stage. |
| `SP1Clean.StoreDouble.AssertionGated` | **(c)** | Full mirror (no assembler — 8-byte aligned store). |
| `SP1Clean.MemoryGlobal.Assertion` | **(d)** *partial* | Phase 1 scaffold (`MemoryGlobalChip.lean:Assertion.main` + `Spec.lean:MemoryGlobal.Assertion.FormalSpec`): 10 u16 range-check lookups + value third-limb decomp + 2 u8 range lookups + 2× `IsZeroOp.Assertion.assertion` + `is_comp`/`is_real` boolean gates. **Deferred to Phase 4.5**: `LtUnsignedOp` monotonicity + bit assertion + x0-case zero asserts (require `MemoryGlobalCols.lt_cols : Vector T 6` to be expanded to 8 fields to hold `LtUnsignedOp.Inputs`'s `comparison_limbs`). Soundness / completeness are `sorry`. |

## Counts

| Category | Count | Members |
|---|---|---|
| **(a)** | 5 | Add, Addi, Sub, **Addw** (post-2026-05-26), **UType** (post-2026-05-26) |
| **(b)** | 1 | Subw (post-`rv64_subw_eq_of_subwop_spec` bridge) |
| **(c)** | 14 | Mul, DivRem, Branch.Assertion, Jal.Assertion, Jalr.Assertion, 9× Memory `AssertionGated` |
| **(d)** | 14 | 4× ALU (Bitwise, ShiftLeft, ShiftRight, Lt), 9× Memory `Assertion` partial, MemoryGlobal partial scaffold |

Total: 34 entries (5 + 1 + 14 + 14). The original audit's "28" header
count was off; the actual table has always had more rows than that.

## Highest-leverage gaps

Ordered by how much faithfulness they unlock per unit of work:

1. **`MemoryGlobal` Phase 4.5 closure** — Phase 1 landed a partial
   scaffold (range checks + value decomp + `IsZeroOp.Assertion` ×2 +
   `is_comp`/`is_real` gates), but `LtUnsignedOp` monotonicity +
   `when(is_comp).bit = 1` + x0-case zero asserts are deferred.
   Closure requires expanding `MemoryGlobalCols.lt_cols : Vector T 6`
   to 8 fields (to hold `LtUnsignedOp.Inputs.comparison_limbs`), then
   composing `SP1Clean.LtUnsignedOp.assertion` with 3→4 limb padding
   on `prev_addr.push 0` / `addr.push 0`. The `soundness` /
   `completeness` `sorry`s in `MemoryGlobalChip.lean:Assertion` close
   at the same time. Promotes from (d) partial to (c).
2. **Bitwise / ShiftLeft / ShiftRight / Lt** — chip `main` is behind
   upstream Rust. Each needs `BitwiseU16Operation` /
   `ALUTypeReader.Gated` / shift-power lookup / `LtOperationSigned`
   added to `main`, then the corresponding `Spec.lean` conjuncts.
   Promotes these from (d) to (c). `ShiftLeft` needs a spike first —
   the "shift-power lookup" missing piece hasn't been located in the
   codebase.
3. **Memory `.Assertion` partials (9 chips)** — each chip's
   `Assertion.main` deliberately drops `load_mem/+1` and related
   memory-bus content (doc-commented as deferred). Closure path:
   introduce the flag-aware `LoadOperandAccess` variant mentioned in
   `SP1Clean/Chips/Memory/LoadByteChip.lean:398-403`, then extend
   each `Assertion.main` + matching `Assertion.FormalSpec` to include
   the deferred RAM access. Promotes from (d) partial to (c).
4. **Mul / DivRem** — closest to (b). Each has a matching
   `RV64.<op>` available; add the semantic trailing conjunct.
   (Subw landed (c)→(b) via `rv64_subw_eq_of_subwop_spec` —
   the same recipe applies, but each needs its own bridge lemma.)
5. ~~**Addw `imm_c = 1`** — already in (b).~~ **CLOSED 2026-05-26.**
   AddwChip promoted to (a) by dropping `AddwOp.Spec` from FormalSpec
   and using a uniform `RV64.addw` clause (no `imm_c` conditional
   needed — the reader supplies `op_c_memory.prev_value` correctly
   for both ADDW and ADDIW). UTypeChip similarly promoted to (a) and
   its 2 outstanding sorries closed in the same migration.

## Available but unused `RV64.*` names

The catalog of `RV64.<op>` symbols in `.lake/packages/RISCV/RISCV/Instructions.lean`
contains ~66 entries. Currently `Spec.lean` references 7 (`add`,
`addi`, `addw`, `auipc`, `lui`, `sub`, `subw`) — `addiw` was dropped
from the references when AddwChip switched to a uniform `RV64.addw`
clause that covers both ADDW (R-type, `imm_c = 0`) and ADDIW (I-type,
`imm_c = 1`) via the reader's `op_c_memory.prev_value` field. The 58+
unused names that map onto SP1 chips are:

- Arithmetic: `mul`, `mulh`, `mulhu`, `mulhsu`,
  `mulw`, `div`, `divu`, `divw`, `divuw`, `rem`, `remu`, `remw`,
  `remuw`.
- Bitwise: `and`, `or`, `xor`, `andi`, `ori`, `xori`, `andn`, `orn`,
  `xnor`.
- Shifts: `sll`, `slli`, `slliw`, `slliuw`, `sllw`, `sra`, `srai`,
  `sraiw`, `sraw`, `srl`, `srli`, `srliw`, `srlw`.
- Compare: `slt`, `slti`, `sltu`, `sltiu`.
- Other (not currently mapped to a chip — Zbb/Zba/Zbs extensions):
  `adduw`, `bclr*`, `bext*`, `binv*`, `bset*`, `clz*`, `ctz*`, `li`,
  `max*`, `min*`, `pack*`, `rol*`, `ror*`, `sextb`, `sexth`, `sh1add*`,
  `sh2add*`, `sh3add*`, `zexth`.

## Sail-only semantics currently in `Spec.lean`

`SP1Clean.Subw.FormalSpec` still carries `execute_RTYPEW_pure_32_w`,
but as the *internals* exposure (the BV32 triple that
`SubwOperation.iff_sp1_full` produces). The chip is in (b) because
its trailing conjunct is a pure `RV64.subw` 64-bit identity. The
BV32 clause is retained because completeness drives
`iff_sp1_full.mpr` from it to witness `subw_value` / `subw_msb` —
dropping it would force a costly BV64↔(BV32+msb) inversion in the
chip's `allHold_iff_structural` backward arm.
`SP1Foundations/SailM.lean` defines 12+ `execute_*_pure*` helpers
that could appear if more (c)-class Specs gain semantic clauses
without `RV64.*` counterparts; none are currently in `Spec.lean`
besides the Subw retention.
