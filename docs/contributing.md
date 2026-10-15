# Contributing

Install the Lean toolchain named in [lean-toolchain](../lean-toolchain), Git and Python 3.9 or newer.
Lake resolves the checked-in dependency graph. The example runners require prepared dependency
checkouts and never download or update them implicitly.

```sh
lake exe cache get
lake build --wfail --iofail
lake test
lake build --wfail --iofail SP1Clean SP1CleanTest ToClean ToMathlib ToPolyFun backendGadgets
lake lint
scripts/run_audit.sh
python3 scripts/check_examples.py
```

The default build is the core. The full build adds machine/alignment proofs; the separate test
library is the only home of native_decide. PR CI runs both scopes automatically, with no
alignment label required. Warnings and stray info diagnostics fail the build.

## Change a circuit or proof

Read the pinned Clean proving and performance guides first. Start with an existing feature's
semantic contract, bundled circuit and soundness/completeness proofs. Add a positive or adversarial
executable fixture when it exercises a meaningful semantic or process boundary; theorem proofs
already check ordinary implementation details.

Use narrow imports. Register a new module in the full root and, when core, the core root.
Keep To* additions independent of SP1 and write their upstream gap in the module docstring.
Complete consumer migrations without compatibility wrappers.

`lake env lean` does not rebuild dependencies and may exit zero on a stack overflow.
Use built dependencies and finish a Lean phase with the strict full build. Do not silence
kernel checking or add elaboration-budget escapes. Before performance changes, read
[proof patterns](agents/proof-patterns.md) and [profiling](agents/build-profiling.md);
measure the affected downstream consumer, not just the edited file.

## Validate the relevant boundaries

| Change | Additional check |
|---|---|
| Documentation/tooling | `python3 scripts/check_current_docs.py`; `python3 -m unittest discover -s scripts/tests` |
| Source organization | Root-index and layering guards; strict full build and lint |
| Public semantic targets | Compiled capstone contract review; explicit reviewed manifest update only for intended changes |
| Pins, ToClean, witness/export APIs | Fresh witgen/ensemble generation, Rust differential and relevant backend checks |
| Generated Sail | Regeneration identity, paired runtime compatibility, strict full build and trust scans |
| Trust tooling | Both compiled-library scopes and `lake env python3 scripts/test_trust_integration.py` |

The [assurance guide](assurance.md) explains what these checks do and do not establish.
Build artifacts and timings belong under .lake or in CI/PR evidence, not as maintained source reports.

## Dependencies and generators

Lean dependency values have one owner: lakefile.toml and its resolved manifest; the toolchain has
its own file. External SP1/Sail revisions and generated fingerprints live in
[provenance.json](../scripts/provenance.json). Run `scripts/check_pins.py` after changing them.
Documentation links to these sources rather than copying their hashes.

Update one Lake requirement at a time. Never run bare lake update, commit path dependencies or
use moving branch pins. A pinned commit must be reachable from a published branch/tag.
[Dependency notes](agents/lean-sail-notes.md) explain the Sail runtime/generator pairing.
Regenerate through the owned scripts; do not hand-edit generated Lean.

Keep disposable outputs under `.lake/build`; Rust targets, Node dependencies and compiler caches
are ignored throughout the tree. Required generated Sail/AIR sources and conformance fixtures
remain versioned until their consumers have a reproducible replacement. `.gitattributes` marks
those trees as generated for GitHub statistics and diffs; this does not reduce checkout size.
Do not ignore lockfiles, provenance or reviewed contract snapshots.

Before starting another heavy build, check for existing build workers. Never switch branches
while a build is reading that checkout. Preserve the measured concurrency settings and never kill
the Lean language server to stop a build.

## Documentation and review

Describe the final behavior and why it matters, with the checks actually run. Link current work
to its [tracking issue](roadmap.md). Durable policy belongs in the guides or source docstrings;
temporary restrictions name their owner and exit. Historical audits are dated records.
[AGENTS.md](../AGENTS.md) is the concise agent brief, not another architecture report.
