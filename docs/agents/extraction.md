# Legacy Rust → Lean extraction

This pipeline preserves migration evidence for the pinned SP1 release. Native circuits and
semantic proofs are handwritten; the extractor emits Rust row layouts and ordered assertion /
interaction lists. The intended replacement is [Clean’s direct Rust export](../export.md).
Retire this pipeline only after its live types, proofs and independent comparison coverage move.

## Reproduce

Use a clean checkout of the extraction revision in [provenance.json](../../scripts/provenance.json):

```sh
SP1_DIR=/path/to/extraction-checkout python3 update_extracted.py
SP1_DIR=/path/to/extraction-checkout scripts/update_sp1_dumps.sh --check
lake build --wfail --iofail SP1Clean SP1CleanTest
python3 scripts/check_witgen_export.py
python3 scripts/run_sp1_conformance.py --sp1-dir /path/to/extraction-checkout \
  --export-dir .lake/witgen-export/run.EXAMPLE
```

`EXTRACT_ONLY=Add,AddOperation,CPUState,RTypeReader` can narrow AIR regeneration to a closed
helper group. Profile and opcode extraction still run. A full regeneration is required when
changing the compiler, shared layout ownership or supported inventory. Inspect every reported
skip; optional operation discovery is not a full Rust-AIR coverage claim.

The generator checks ancestry from the semantic pin, a clean checkout, and the extraction branch’s
machine-source delta. Allowed machine changes are reflection imports/derives only. The compiler,
shape reflection and printer are separate trusted tooling; the restricted machine diff does not
prove them correct. `SP1_ALLOW_UNPINNED=1` is a local exploration escape hatch, not a release mode.
Never relabel old generated files with a new semantic revision.

## Outputs and independent inputs

| Output | Source and consumer |
|---|---|
| `SP1Clean/Extracted/ChipOracle/` | Complete instruction rows and AIR lists from Rust `Air::eval`; consumed by whole-chip `ChipFaithful` proofs |
| `SP1Clean/Extracted/SystemOracle/` | Flat non-instruction rows and the machine public-value block |
| `SP1Clean/Extracted/CoreAIRManifest.lean` | Actual `RiscvAir::machine()` cluster names and widths, checked by `FormalModel.CoreProfile` |
| `SP1Clean/Extracted/OpcodeTable.lean` | Executor opcode names/discriminants read at the semantic revision, checked against the Lean alphabet |
| `SP1Clean/Extracted/Provenance.lean` | Semantic and extractor revisions verified before generation |
| `export/sp1dump/` | Deterministic events and full padded SP1 `generate_trace` matrices; written separately by `scripts/update_sp1_dumps.sh` |
| `.lake/witgen-export/run.*/` | Fresh native witness programs, symbolic row maps and checked fixtures; written by `scripts/witgenExport.lean`, validated by `scripts/check_witgen_export.py` |

`Faithful` maps native rows to exact Rust rows and proves assertion-list equality and projected
interaction agreement. System/provider transport can require additional named premises; see
[assurance](../assurance.md). Do not infer machine equivalence from instruction-chip agreement.

The fixture writer recovers native input cells from SP1 rows, derives event hints, executes the
native witness programs and refuses to write mismatching reconstructed rows. The Rust interpreter
repeats that comparison from serialized bytes. The driver prints the fresh output directory;
substitute it for `run.EXAMPLE` above. The opt-in SP1 driver verifies its source/artifact hashes
and stages the pinned checker with those exports under `.lake`. Its source and lockfile remain
unchanged; only Cargo dependency paths are relocated.

## Emission boundaries and limitations

The compiler supplies field-generic Lean. Python discovers struct ownership, requests
`--reuse-struct`, adds imports and embeds chip-private helper definitions. Canonical reader
helpers are imported once. No Rust-generated executable Clean circuit is maintained.

Shared columns are handwritten under `SP1Clean/Circuits/Types/`. Before reuse, the discovery pass
checks names, field order, nesting and vector widths against Rust output. A full regeneration
must encounter every shared native column type. The extractor never rewrites native types;
an upstream layout change requires an explicit migration of those types and their consumers.

Two reviewed printer adaptations matter: raw byte opcodes must remain field expressions
(the old enum coercion collapsed unknown values), and the large Global table’s shared let chains
are hoisted into private definitions to keep elaboration linear. Large `ProvableStruct` derives
have a local explicit-instance workaround. Their implementations and measured exceptions live
in `update_extracted.py`; generated files are never edited directly.

The profile gate requires the selected execution/memory clusters and public-value width, and
Lean checks the generated manifest against its hand-maintained profile. This is narrower than
all SP1 configurations. Mode-associated fields are omitted by legacy shape reflection, so the
generator explicitly rejects the `mprotect` feature. Static optional columns and full inventory
coverage are tracked in [#112](https://github.com/dtumad/sp1-lean/issues/112).

On a source change, regenerate the AIR and dumps, rebuild all faithfulness consumers, then rerun
fresh native exports and both Rust comparisons. Keep unsupported configurations explicit until
the direct-export comparison replaces them.
