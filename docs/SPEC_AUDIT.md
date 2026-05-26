# SP1Clean/Chips/Spec.lean — per-`FormalSpec` audit

Snapshot of `SP1Clean/Chips/Spec.lean` (1302 lines, 28 spec entries
across 25 chip namespaces), classified into four categories. The audit
asks, for every `def FormalSpec`: is the Spec a minimal pure-semantic
form, an internals-exposing form with an RV64 wrapper, a faithful
constraint mirror without RV64, or still incomplete relative to chip
`main` / upstream Rust?

This is a snapshot — re-run the rubric below whenever
`SP1Clean/Chips/Spec.lean` or a chip's `main` changes shape. The
verdict table reflects the repo at branch `dtumad/clean` commit
`8409e59` (2026-05-26).

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

## Verdict table (28 entries)

### ALU chips

| Namespace | Verdict | Justification |
|---|---|---|
| `SP1Clean.Add` | **(a)** | `CPUState.Gated` + `RTypeReader.Gated` + `op_a_0 = 0` + `is_real = 1 → isU64 ∧ toBitVec64 = RV64.add …`. |
| `SP1Clean.Addi` | **(a)** | Same shape, `ITypeReader.Gated` + `RV64.addi`. |
| `SP1Clean.Sub` | **(a)** | Same shape, `RV64.sub`. |
| `SP1Clean.Addw` | **(b)** partial | `AddwOp.Spec` internals (`addw_value`, `addw_msb`) + `RV64.addw`. `imm_c = 1` branch (`RV64.addiw`) intentionally deferred per doc comment. |
| `SP1Clean.Subw` | **(c)** | `SubwOp` internals + Sail `execute_RTYPEW_pure_32_w`. `RV64.subw` exists in `RISCV/Instructions.lean` — upgrade candidate to (b). |
| `SP1Clean.UType` | **(b)** | Raw `AddOperation.constraints.allHold` (internals `addend`, `add_result`) + `RV64.auipc` / `RV64.lui`. |
| `SP1Clean.Mul` | **(c)** | `MulOp.Spec` internals + `RTypeReader.Gated`. Matches `MulChip/Aggregate.lean:520 main`. `RV64.mul/mulh/mulhu/mulhsu/mulw` available. |
| `SP1Clean.DivRem` | **(c)** | MulOp×2 + IsEqualWordOp×4 + IsZeroWordOp + AddOp×2 + LtUnsignedOp + U16MSBOp×7. Matches `DivRemChip/Aggregate.lean:189 main`. `RV64.div/divu/divw/divuw/rem/remu/remw/remuw` available. |
| `SP1Clean.Bitwise` | **(d)** | Spec matches the gated `main` at `BitwiseChip/Aggregate.lean:316`, but **both** drop `BitwiseU16Operation` + `ALUTypeReader` that upstream Rust `alu/bitwise/mod.rs` emits. Self-flagged in the doc comment. `RV64.and/or/xor` available. |
| `SP1Clean.ShiftLeft` | **(d)** | Spec matches `ShiftLeftChip/Aggregate.lean:379 main`; both omit the shift-power lookup + `ALUTypeReader` from Rust `alu/sll/mod.rs`. `RV64.sll/sllw` available. |
| `SP1Clean.ShiftRight` | **(d)** | Same as ShiftLeft; both omit `MSBOperation`-derived shift sub-ops from Rust `alu/sr/mod.rs`. `RV64.srl/sra/srlw/sraw` available. |
| `SP1Clean.Lt` | **(d)** | Spec matches `LtChip/Aggregate.lean:286 main` but both omit `LtOperationSigned` that upstream `alu/lt/mod.rs` composes. `RV64.slt/sltu` available. |

### Control chips

Each of Branch/Jal/Jalr has both an `Assertion.main` and an
`AssertionGated.main` in its `Aggregate.lean`. Only the
`Assertion.FormalSpec` form is present in `Spec.lean` — the gated
counterpart is missing.

| Namespace | Verdict | Justification |
|---|---|---|
| `SP1Clean.Branch.Assertion` | **(c)** | `GatedAddOp.Spec` ×2 + `next_pc[i]` range bounds + `OperandAccess` ×2. Matches `BranchChip/Aggregate.lean:316 main`. No `RV64.<branch>` wrapper (branch sem is `Bool`, non-trivial upgrade). |
| `SP1Clean.Branch.AssertionGated` | **(d)** *missing* | `AssertionGated.main` exists in `BranchChip/Aggregate.lean` but no `SP1Clean.Branch.AssertionGated` namespace in `Spec.lean`. |
| `SP1Clean.Jal.Assertion` | **(c)** | Raw `toBitVec64 next_pc = pc + op_b_imm` + `toBitVec64 op_a_write_value = pc + 4` (no `RV64.jal` exists). Has `OperandAccess` ×1 + `ProgramTable.Spec`. Matches `JalChip/Aggregate.lean:371 main`. |
| `SP1Clean.Jal.AssertionGated` | **(d)** *missing* | `AssertionGated.main` exists with 2× `AddOp.assertion`; no Spec namespace. |
| `SP1Clean.Jalr.Assertion` | **(c)** | `GatedAddOp.Spec` + `OperandAccess` ×2 + scalar gates. Matches `JalrChip/Aggregate.lean:279 main`. |
| `SP1Clean.Jalr.AssertionGated` | **(d)** *missing* | `AssertionGated.main` exists; no Spec namespace. |

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
| `SP1Clean.MemoryGlobal` | **(d)** *severe* | No namespace in `Spec.lean`. `MemoryGlobalChip.lean` has zero `def main` — only a column struct stub. Upstream `memory/global.rs` composes `LtOperationUnsigned` with ~4 constraints. |

## Counts

| Category | Count | Members |
|---|---|---|
| **(a)** | 3 | Add, Addi, Sub |
| **(b)** | 2 | Addw (partial RV64), UType |
| **(c)** | 16 | Subw, Mul, DivRem, Branch.Assertion, Jal.Assertion, Jalr.Assertion, 9× Memory `AssertionGated` |
| **(d)** | 17 | 4× ALU (Bitwise, ShiftLeft, ShiftRight, Lt), 3× Control `AssertionGated` missing, 9× Memory `Assertion` partial, MemoryGlobal absent |

## Highest-leverage gaps

Ordered by how much faithfulness they unlock per unit of work:

1. **`MemoryGlobal`** — most severe (d). No `main`, no Spec, only a
   struct stub at `SP1Clean/Chips/Memory/MemoryGlobalChip.lean`.
   Closing this needs both a `main` composition (`LtOperationUnsigned`
   primarily) and a matching `FormalSpec` block. The upstream Rust is
   small (~4 constraints in `memory/global.rs`) so this is a
   well-scoped Phase-1 add.
2. **Bitwise / ShiftLeft / ShiftRight / Lt** — chip `main` is behind
   upstream Rust. Each needs `BitwiseU16Operation` /
   `ALUTypeReader.Gated` / shift-power lookup / `LtOperationSigned`
   added to `main`, then the corresponding `Spec.lean` conjuncts.
   Promotes these from (d) to (c).
3. **Branch / Jal / Jalr `AssertionGated.FormalSpec`** — `main` is
   already complete in code. Just add the three missing
   `AssertionGated.FormalSpec` blocks to `Spec.lean`, mirroring the
   `Memory.*.AssertionGated` pattern. Promotes from (d) to (c).
4. **Subw / Mul / DivRem** — closest to (b). Each has a matching
   `RV64.<op>` available; add the semantic trailing conjunct.
   `Subw` is the easiest: replace `execute_RTYPEW_pure_32_w` with
   `RV64.subw`. Promotes from (c) to (b).
5. **Addw `imm_c = 1`** — already in (b). Add the
   `cols.is_real = 1 → cols.adapter.imm_c = 1 → … = RV64.addiw …`
   clause to complete RV64 coverage. Closes the doc-comment-flagged
   deferral.

## Available but unused `RV64.*` names

The catalog of `RV64.<op>` symbols in `.lake/packages/RISCV/RISCV/Instructions.lean`
contains ~66 entries. Currently `Spec.lean` references only 7
(`add`, `addi`, `addiw`, `addw`, `auipc`, `lui`, `sub`). The 59 unused
names that map onto SP1 chips are:

- Arithmetic: `subw` (for Subw), `mul`, `mulh`, `mulhu`, `mulhsu`,
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

One: `execute_RTYPEW_pure_32_w` inside `SP1Clean.Subw.FormalSpec`.
`SP1Foundations/SailM.lean` defines 12+ `execute_*_pure*` helpers
that could appear if more (c)-class Specs gain semantic clauses
without `RV64.*` counterparts; none are currently in `Spec.lean`
besides this one.
