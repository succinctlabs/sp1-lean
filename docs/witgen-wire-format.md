# The witgen wire format (`version: 1`)

The contract between the Lean-verified witness generators and any external consumer —
first among them the Rust reference interpreter in `rust/witgen-interp/`. The committed
artifacts under `export/witgen/` are instances of this format; `scripts/witgenExport.lean`
is their only writer, and `scripts/check_witgen_export.sh` gates them.

**Normative source.** This document is descriptive. The format is defined by the Clean
pin's serializer — `Clean/Circuit/WitnessExport.lean` and `Clean/Circuit/Json.lean` at
the rev recorded in `lakefile.toml` (currently `2dad7788`, fork `dtumad/clean`) — and the
evaluation semantics by `Clean/Circuit/WitnessIR.lean` (`FExpr.eval` and friends) and
`Clean/Circuit/WitnessGeneration.lean` (`Circuit.witgen`). On any disagreement, the Lean
code wins and this file gets fixed.

## The envelope

One payload per chip, `export/witgen/<Chip>.witgen.json`:

```json
{"version": 1, "localLength": N, "operations": [ ... ]}
```

- `version` — the wire version; this document describes exactly `1`.
- `localLength` — the total number of witness cells the program appends (the sum of the
  `witness` fields below).
- `operations` — the chip's complete flattened operation list, in emission order, with
  all subcircuits inlined (names erased). Four operation forms:

| form | shape |
|---|---|
| witness | `{"witness": m, "code": {"steps": [...], "output": <VExpr>}}` |
| assert | `{"assert": <Expression>}` — the constraint `<Expression> = 0` |
| lookup | `{"lookup": {"table": <string>, "entry": [<Expression>, ...]}}` |
| interact | `{"interact": {"channel": <string>, "multiplicity": <Expression>, "message": [<Expression>, ...]}}` |

A **witness interpreter evaluates only the `witness` operations** and skips the rest;
they are carried so one artifact describes the whole chip (constraints and bus
interactions included) for consumers that want them.

## What the payload does *not* carry — the manifest

The wire format records neither the field, the input width, the chip name, nor the hint
schema. `export/witgen/<Chip>.manifest.json` fills the gap:

```json
{
  "wireVersion": 1,
  "witgenFile": "DivRem.witgen.json",
  "name": "DivRem",
  "lean": "SP1Clean.DivRemChip.circuit",
  "localLength": 217,
  "inputWidth": 29,
  "operationCounts": {"witness": 30, "assert": 321, "lookup": 0, "interact": 135},
  "hints": [{"table": "div_rem_flags", "width": 7, "rowsRead": [0], "colsRead": [0,1,2,3,4,5,6]}],
  "hintPolicy": "a missing table, wrong width, or out-of-range row reads as the all-zero vector; padding rows rely on this default",
  "data": [],
  "field": {"name": "KoalaBear", "modulus": 2130706433}
}
```

The hint/data schemas are *derived* from the serialized payload (a walk for
`hintGet`/`dataGet` nodes), never hand-maintained. `export/witgen/index.json` lists all
chips with their `inputWidth`/`localLength`, in the registry order of
`SP1Clean/Soundness/SupportedMachine.lean` (a public witness-format matter).

## Variable indexing and the evaluation loop

A `GeneralFormalCircuit`'s input row occupies absolute variable indices
`0 .. inputWidth - 1`; the circuit's own cells begin at `inputWidth`. The evaluation
loop is a transcription of `Circuit.witgen` / `witgenStep`:

1. Seed a growing cell array with the `inputWidth` input values.
2. Fold over `operations` in order. On `{"witness": m, "code": {steps, output}}`:
   evaluate `steps` left to right into a locals array (each step sees only the locals
   before it), then evaluate `output` and append **exactly `m`** field elements to the
   cell array. Skip `assert`/`lookup`/`interact`.
3. The final array has length `inputWidth + localLength`.

An out-of-range cell read yields `0`.

## The four expression sorts — parse by slot, not by tag

`type` tags **collide across sorts** (`const`, `add`, `mul`, `ite`, `localVar`, `and`
each appear in two or three vocabularies), so a deserializer must be sort-directed by
the parent slot. The sorts:

**`Expression`** — the circuit-constraint AST. Tags: `var {index}` (an **absolute** cell
index), `const {value}`, `add {lhs, rhs}`, `mul {lhs, rhs}`. Appears in: `assert`,
`lookup.entry[]`, `interact.multiplicity`, `interact.message[]`, and inside `FExpr`'s
`expr` node.

**`FExpr`** — field-sorted witness expressions:

| tag | fields | semantics |
|---|---|---|
| `expr` | `expr: <Expression>` | evaluate against the cell array |
| `const` | `value: ℕ` | the field element with that canonical value |
| `localVar` | `index: ℕ` | step-local reference (a `field`-sorted step) |
| `add`, `mul` | `lhs, rhs: FExpr` | field arithmetic |
| `inv` | `arg: FExpr` | field inverse, **with `0⁻¹ = 0`** |
| `ofU64` | `arg: U64Expr` | lift: the field element with value `arg` (mod p) |
| `ite` | `cond: BExpr; then, else: FExpr` | conditional |
| `listGet` | `items: [FExpr]; index: U64Expr` | item at index, **`0` if out of range** |
| `dataGet` | `table, width, row: U64Expr, col` | committed prover data read (unused by SP1's 25 chips) |
| `hintGet` | `table, width, row: U64Expr, col` | prover hint read; **missing table/row reads as `0`** |

**`U64Expr`** — u64-sorted, everything wraps mod 2⁶⁴ like Rust's `u64`:

| tag | semantics |
|---|---|
| `const {value}` | literal |
| `val {arg: FExpr}` | the field element's canonical value, **truncated** to 64 bits |
| `idx {}` | the innermost enclosing `mapRange` index (`0` outside) |
| `localVar {index}` | step-local reference (a `u64`-sorted step) |
| `add`, `mul` | wrapping arithmetic |
| `div`, `mod` | **Lean semantics: `x / 0 = 0`, `x % 0 = x`** (Rust `/`/`%` panic — guard) |
| `and`, `or`, `xor` | bitwise |
| `shiftLeft`, `shiftRight` | **shift amount masked mod 64** (`wrapping_shl`/`wrapping_shr`) |
| `ite {cond, then, else}` | conditional |

**`BExpr`** — conditions. ⚠ Three wire tags disagree with the Lean constructor names;
**the wire tags are authoritative**, and an implementation should name its cases after
them:

| tag | operands | semantics |
|---|---|---|
| `true`, `false` | — | literals |
| `eq` | FExpr | field equality |
| `u64Eq` | U64Expr | u64 **equality** (the Lean ctor is confusingly named `neq`) |
| `u64Lt` | U64Expr | u64 `<` (the Lean ctor is named `lt`) |
| `lt` | FExpr | canonical-value `<` on **field** elements (the Lean ctor is named `flt`) |
| `bit {arg: FExpr, bit: ℕ}` | | bit `i` of the canonical value is set |
| `not {arg}` | BExpr | negation |
| `and {lhs, rhs}` | BExpr | conjunction — **there is no `or` node** (De Morgan) |

There are also no subtraction or negation nodes in any sort: `x - y` is encoded as
`x + (p-1)·y`, so constants like `2130706432` (= p − 1) are common.

**`steps`** — a list of `{"sort": "field"|"u64", "value": <FExpr|U64Expr>}` let-bindings,
referenced positionally by `localVar` in the matching sort. **A sort-mismatched or
out-of-range `localVar` reads as `0`** (this is total-evaluation semantics, not an
error). Steps evaluate at `idx = 0`.

**`output`** (`VExpr`) — the vector former producing the witness cells:

| tag | semantics |
|---|---|
| `elements {elements: [FExpr]}` | a literal cell list |
| `mapRange {n, body: FExpr}` | `n` cells, the body re-evaluated with `idx = 0..n-1` |
| `envRange {n, offset}` | `n` consecutive cells read from **absolute** index `offset` |
| `bitsOf {n, arg: FExpr}` | the `n` low bits of the canonical value (field-level: `n` may exceed 64) |
| `append {left, right}` | concatenation |

## Field arithmetic

SP1's field is KoalaBear, `p = 2³¹ − 2²⁴ + 1 = 2130706433`. Field elements serialize as
their canonical value (`0 ≤ v < p`). The required operations: `+`, `·`, inverse with
`0⁻¹ = 0`, canonical value (for `val`, `lt`, `bit`, `bitsOf`), and value-to-element
(for `ofU64`; on a prime field this is just `n mod p`). `p < 2³¹`, so products fit in
`u64` — no Montgomery form is needed for a reference interpreter.

## Sharing (`steps`) and the size guarantee

Authored witness programs are deeply shared terms, and the serializer would otherwise
expand every shared subterm into a fresh copy — SP1's DivRem chip serializes to
**1.22 GB** that way. The committed payloads are therefore produced through
`Operations.witgenJsonShared?`, which rebuilds each witness program with every distinct
non-trivial scalar subterm interned as a `let`-step (`WitgenIR.share`). The
transformation is **proven evaluation-preserving** (`WitgenIR.eval_share`, axiom-clean),
so consumers may treat shared and unshared payloads as the same program; the committed
DivRem payload is 1.04 MB and the whole 25-chip export ~2.3 MB. An interpreter gets the
same win at evaluation time: cost is proportional to distinct subterms, provided each
step is evaluated once into the locals array (the loop above does exactly that).

## Determinism and byte stability

JSON object key order is code-determined (descending by key name) and the exporter
embeds no timestamps or revisions, so regeneration is byte-stable: the CI `test` job
diffs a fresh export against the committed tree (`check_witgen_export.sh --regen`)
on every run, which also catches wire-format drift on a Clean pin bump. To refresh
deliberately after an intended change:

```
lake build SP1CleanTest.Exportable
scripts/check_witgen_export.sh --regen --update   # inspect and commit the delta
```

## Row maps (`export/witgen/<Chip>.rowmap.json`)

The payload generates witness *cells*; a full trace **row** is the circuit's output
struct pushed through the audited native→Rust layout map (`ChipFaithful`'s
`reconfigure`). Those maps are fully polymorphic struct re-wirings, so applying them at
the `Expression` level yields the complete symbolic Rust row, exported per chip as:

```json
{"wireVersion": 1, "name": "Add", "rustWidth": 33,
 "row": [{"type": "var", "index": 1}, ..., <Expression>]}
```

one `Expression` (over absolute cell indices) per Rust column. Evaluating `row` after
the witgen pass reproduces the chip's SP1 trace row exactly — the reference interpreter
does this and checks it against every fixture `expectedRow`. With the payload's
`assert` operations (each the constraint `expr = 0`, checkable on the completed cells)
and `interact` operations (bus multiplicities/messages, evaluable per row for
dependency accounting), the three artifacts together contain everything needed to
generate and self-check complete SP1 trace rows.

## Differential fixtures (`export/testdata/<Chip>.trace.json`)

The same writer's `--testdata` mode produces per-chip differential fixtures for external
interpreters:

```json
{
  "wireVersion": 1, "chip": "DivRem", "field": {...},
  "inputWidth": 29, "localLength": 217,
  "provenance": {"events": "...names the SP1 dump and the generation-time gate...",
                 "synthetic": "..."},
  "rows": [
    {"kind": "event", "anchored": true, "inputs": [...29 values...],
     "hints": {"div_rem_flags": {"width": 7, "rows": [[1,0,0,0,0,0,0]]}},
     "expectedWitness": [...217 values...], "expectedRow": [...246 values...]},
    {"kind": "padding", "anchored": true, "inputs": [...],
     "hints": {"div_rem_flags": {"width": 7, "rows": []}},
     "expectedWitness": [...], "expectedRow": [...]},
    {"kind": "synthetic", "anchored": false, "seed": 1010, "inputs": [...],
     "hints": {...}, "expectedWitness": [...]}
  ]
}
```

The contract per row: seed the cell array with `inputs`, supply `hints`, run the chip's
witness operations; the appended cells must equal `expectedWitness` (canonical values).
Row provenance is honest:

- `"event"` (`anchored: true`) — one row per executor event of the committed SP1 trace
  dump (`export/sp1dump/<Chip>.dump.json`, produced by the `chip_traces` binary at the
  pinned extraction branch; the `provenance.events` string names the dump file and its
  `sp1Commit`). The inputs are recovered from the dumped row itself through the
  symbolic row map (every native input cell is a bare `var` column of the Rust row,
  except `is_real` on the six flag-hinted chips — Bitwise, Branch, Lt, Mul, ShiftLeft,
  ShiftRight — which is `1` on event rows); the hint tables are derived from the
  event's opcode discriminant (Branch additionally derives its `branch_branching` bit
  from the operand values, mirroring SP1's own populate). `expectedRow` is the dumped
  SP1 `generate_trace` row verbatim. **The generation-time gate**: before anything is
  written, the exporter recomputes every event row — `FlatOperation.witgen` over the
  shared operations, then the symbolic row map evaluated at the resulting cells — and
  requires cell-for-cell equality with the dump, plus a value-level
  `circuitTraceRowMapped` spot check on event row 0. Present for **all 25 chips**.
- `"padding"` — the empty-hint row, inputs recovered from the dumped padding row.
  `anchored: true` only where SP1 *derives* its padding rows by running populate
  (ShiftLeft, ShiftRight, and DivRem — whose `expectedRow` is SP1's non-zero
  "0 divided by 1" template, reproduced from the absent hint key); these are gated
  like event rows. The remaining chips zero-fill their padding without running
  populate — the exporter asserts their dumped padding is all-zero and emits the row
  as a plain differential vector (`anchored: false`).
- `"synthetic"` (`anchored: false`) — deterministic seeded inputs (witness generation
  is total, so every input is valid), with 0/1-valued seeded hint rows for the
  declared tables. All 25 chips carry these.

`expectedWitness` is always the Lean reference evaluation (`FlatOperation.witgen`) over
the **shared** operation list — the same programs the wire carries
(`WitgenIR.eval_share`).

## SP1-specific facts a consumer may rely on

- All 25 chips use `hintGet` only — `data` schemas are empty (`dataGet` support in an
  interpreter is still recommended; the node is part of the format).
- Every hint read is at constant row `0`; the eight hint tables and widths are in the
  manifests (`lt_flags` 2, `bitwise_flags` 3, `branch_flags` 6, `branch_branching` 1,
  `mul_flags` 5, `shift_left_flags` 2, `shift_right_flags` 4, `div_rem_flags` 7).
- The zero-default of a missing hint table **is** the padding-row semantics: chips
  derive their SP1 padding template from the absent key (DivRem's `is_divu = 1`
  template is the worked example).
