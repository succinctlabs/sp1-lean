# Clean extensions and upstream integration

The active Clean revision is owned by lakefile.toml and lake-manifest.json. Local additions live
under ToClean in the namespaces they would occupy upstream, with their missing upstream capability
described in each module docstring. No SP1 imports are permitted there.

Prefer an extension to a fork. Fork only when a canonical declaration must change and downstream
additions cannot express the required behavior. Keep that patch minimal, tied to its upstream
proposal, and delete it when a compatible upstream version supplies the change. Do not maintain
duplicate implementations or compatibility wrappers after consumers migrate.

## Existing gaps

| Addition | Purpose |
|---|---|
| AgreesBelowWithData / WitnessGenerationData | Data/hint-preserving witness construction; agreement of cells alone does not justify dataGet/hintGet |
| TableBuild / EnsembleBuild | Typed row/table/ensemble construction with actual ledger and verifier proofs |
| EnsembleCheck / FiniteLookup | Authenticated finite lookup inventory and executable raw-witness acceptance |
| Realizes / CompleteEnsemble / EnsembleCompiler | Machine interpretation and constructive equivalence interfaces |
| Receipt / PublicVerifier / projection helpers | Preserve original circuit/ledger behavior across actual composed consumers |

These are reusable additions, not alternate SP1 semantics. Their concrete consumers determine
whether an abstraction earns its place. When upstream accepts an API, migrate imports and delete
the local copy.

Clean #450 addresses canonical data/hint agreement. Its counterexample explains why strengthening
the original computability predicate can require an upstream modification. The current local
extension states its stronger obligation explicitly without changing Clean's existing theorems.
The construction fork proposed in SP1 PR #111 was closed during consolidation; useful proof work
remains in its linked history rather than adding that broad fork pin.

## Built-in Rust export

Clean #445/#446 supply direct generated Rust AIR/witness programs, fixed columns and runtime
prover inputs. The selected version must be reconciled with this repository's toolchain and module
system. Prefer those APIs over extending the legacy JSON emitter/interpreter.

Representation changes to canonical Component/Ensemble/Witgen objects may need an upstream patch;
new adapters and supporting lemmas belong in ToClean. Scheduler support is not scheduler
completeness or final-data agreement. Preserve those proof obligations explicitly.

See [export](../export.md) and #28/#29 for the live migration. Upstream submissions are separate
from maintaining reproducible reviewed code in this fork; issue/PR history owns submission status.
