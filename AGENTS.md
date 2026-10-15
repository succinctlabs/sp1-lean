# Working on sp1-clean-native

This library specifies and proves native Clean circuits for SP1's RISC-V execution model.
Lean owns the circuit definitions and semantic proofs. The intended integration is Clean's
built-in Lean → Rust AIR/witness export, compared with a pinned SP1 release in Rust.
The existing Rust → Lean oracles and faithfulness proofs remain migration evidence until their
live type/proof consumers and conformance coverage have been replaced.

## Current work and scope

The post-talk consolidation takes priority over finishing the mixed-execution capstone.
Complete migrations may change APIs: there are no downstream users requiring compatibility
wrappers. Migrate all in-repository consumers and delete superseded implementations.

- [Architecture campaign #16](https://github.com/dtumad/sp1-lean/issues/16) owns module boundaries
  and model consolidation; [#33](https://github.com/dtumad/sp1-lean/issues/33) owns module mode.
- [Capstone #12](https://github.com/dtumad/sp1-lean/issues/12) owns remaining semantic obligations.
  Cleanup does not close them. Its complete Sail/host/clock contract stays explicit.
- [Export #28](https://github.com/dtumad/sp1-lean/issues/28) and
  [Rust comparison #29](https://github.com/dtumad/sp1-lean/issues/29) own integration.
- [#6](https://github.com/dtumad/sp1-lean/issues/6) owns the generated Sail workaround;
  [#41](https://github.com/dtumad/sp1-lean/issues/41) owns measured build hotspots.

Keep progress in those issues and PRs. Documentation describes durable contracts, current
limitations and temporary choices with exit conditions; it is not a development log.

## Architecture and upstream policy

Organize towards Semantics / Circuits / Machine / Export, with pure contracts below circuit
implementations and feature-local proofs. Follow Clean's Specs / Types / Gadgets / Air / Backends
separation where it applies. See [architecture](docs/architecture.md) for the current layout.

`ToClean`, `ToPolyFun` and `ToMathlib` mean **To Upstream**. Keep additive APIs there, in upstream
namespaces, with a module docstring describing the missing upstream capability. They may not
import SP1Clean: ToMathlib imports Mathlib; ToPolyFun imports PolyFun; ToClean imports Clean and
may use the other two. Delete the local addition and repoint imports when upstream supplies it.
A fork is justified only for a necessary change to an existing upstream declaration that an
extension cannot express. Keep the patch minimal and document its upstream exit.

Reuse Clean's extraction IR, lowering, Rust emitter and witness machinery. Do not introduce a
parallel emitter, expression format, interpreter or scheduler. Upstream witness generation does
not by itself prove completeness or final-data agreement.

Use one complete execution transition and PolyFun trace vocabulary. Finite snapshots and their
realized Sail states are different useful representations; Memory and host boundaries are
projections. Reuse the canonical Clean ledger and typed physical inventory. Derived views must
preserve repeated keys, zero-multiplicity occurrences and count bounds.

## Proof and assurance discipline

- All released proofs must be kernel checked: no sorry, project axioms, proof deferrals or
  kernel-check bypass. Do not raise elaboration budgets to hide structural problems.
- Production code never uses native_decide. Executable checks using it belong only in
  SP1CleanTest. Existing Sail extern and bitvector trust exceptions are explicitly scoped in
  [the trust policy](docs/assurance.md); never widen them as a cleanup shortcut.
- Specs state semantic meaning, not copies of constraints. Compose bundled Clean subcircuits
  through their circuit interfaces. A reusable proof boundary is a FormalCircuit,
  GeneralFormalCircuit or FormalAssertion; an unbundled Circuit is not a substitute.
- Start soundness/completeness proofs with circuit_proof_start. Pass explicit elaborated
  metadata into factored bundles. Prefer upstream default obligation tactics, supplying missing
  circuit_norm lemmas rather than duplicating plumbing.
- Preserve the full capstone domain: arbitrary bounded local segments, complete authenticated
  boundaries and all eight host calls. Do not add caller-supplied readiness, grounding, provider
  validity, syscall inactivity or conservative compiler footprints to close a target.
- Native semantic correctness, agreement with SP1, correctness of code generation and
  cryptographic verifier soundness are distinct claims. Rust comparisons are tests, not a
  formal lowering proof. Do not claim deterministic verifyCore acceptance implies execution
  without the cryptographic assumptions and error bound.

Read the pinned Clean documentation before nontrivial proof work:
`.lake/packages/Clean/AGENTS.md`, `doc/proving-guide.md`, `doc/performance-problems.md`,
`doc/witgen-authoring.md` and `Clean/Air/README.md`. Local
[proof notes](docs/agents/proof-patterns.md) cover SP1-specific pitfalls. The approved API-breaking
migration supersedes their historical compatibility-preservation guidance.

## Build and validation

```sh
lake build --wfail --iofail
lake build --wfail --iofail SP1Clean SP1CleanTest ToClean ToMathlib ToPolyFun
lake test
lake lint
scripts/run_audit.sh
```

The default target is the core; the full target includes alignment/machine proofs. New modules
must be indexed by SP1Clean.lean and, if core, SP1Clean/Core.lean. Root coverage and import
boundaries are checked by scripts/check_root_index.sh and scripts/check_layering.sh.
Use the same package options locally and in CI. Passing means no errors, warnings or stray info
messages. Do not add linter debt; documented site-specific exceptions must have a concrete reason.
The existing scripts/nolints.json and package opt-outs are a burn-down list, not a precedent.

`lake env lean` does not rebuild dependencies and can exit zero on a stack overflow. Build the
changed dependency closure first and finish a Lean phase with the strict full build. Process
runners must check complete expected output as well as exit status. Inspect both main and test
compiled trust scopes; public/private visibility must not hide transitive dependencies.

Check running builds before starting another. Never switch branches or overwrite sources read by
an active build. Avoid concurrent heavy builds; LEAN_NUM_THREADS controls Lake's pool (there is no
Lake -j option). Preserve the measured child-lean settings in lakefile.toml. Never kill lean --server
or lake serve; stale lean --worker processes are distinct from build workers.

Performance changes need measurements of affected consumers, not just the edited proof.
Keep expensive values opaque, hypothesis types folded and shared expressions shared. Dropping
`by exact` can remove useful proof opacity. Do not repeat failed performance experiments without
new evidence. Keep timing transcripts with PR artifacts.

## Pins and generated files

Lean dependencies are owned by lean-toolchain, lakefile.toml and lake-manifest.json.
External SP1/Sail generator revisions and output fingerprints are owned by
[scripts/provenance.json](scripts/provenance.json). `scripts/check_pins.py` checks them against
actual inputs/outputs; hashes are not copied into this guide.

No path dependencies or moving branch pins. Update one Lake requirement at a time; never run bare
lake update. Read [dependency notes](docs/agents/lean-sail-notes.md) before a pin change. A revision
must be reachable from a published branch/tag so a fresh clone works.

LeanRV64D and the Sail runtime move as a compatible pair. Generate LeanRV64D through
scripts/sail-config/generate_lean_rv64d.sh; never hand-edit it. The separate RvfiDii Lake library
is a temporary elaboration workaround owned by #6. SP1Clean/Extracted is likewise generated only
by update_extracted.py while that migration pipeline remains. Do not silently repin old generated
oracles to a newer SP1 release.

For pin/ToClean/export changes, run fresh witness and ensemble export regeneration and the
applicable Rust/backend comparisons, in addition to the full Lean checks. Preserve independent
source-side comparison: a generated inventory cannot authenticate itself.
