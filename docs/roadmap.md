# Roadmap

The immediate priority is post-talk consolidation, with Lean-native circuits and Clean's
Lean → Rust export as the end state. Complete in-repository migrations may change public APIs;
there is no compatibility layer to preserve for downstream users.

The durable [semantic contract](semantics.md), [architecture](architecture.md) and
[assurance boundaries](assurance.md) are separate from current progress:

| Owner | Scope |
|---|---|
| [#16](https://github.com/dtumad/sp1-lean/issues/16) | Native-owned types, Semantics/Circuits/Machine/Export organization, model and inventory consolidation |
| [#33](https://github.com/dtumad/sp1-lean/issues/33) | Lean module system and public visibility, including generated Sail |
| [#28](https://github.com/dtumad/sp1-lean/issues/28) | Clean built-in export, final facade and executable data-only compiler |
| [#29](https://github.com/dtumad/sp1-lean/issues/29) | New SP1 release, Rust comparison, verified replacements and costs |
| [#12](https://github.com/dtumad/sp1-lean/issues/12) | Complete mixed endpoint, all eight calls, resources, total compiler and closed Realizes |
| [#6](https://github.com/dtumad/sp1-lean/issues/6) | Durable replacement of the generated RvfiDii elaboration workaround |
| [#112](https://github.com/dtumad/sp1-lean/issues/112) | Released SP1 upgrade, configuration coverage and Rust comparison |
| [#113](https://github.com/dtumad/sp1-lean/issues/113) | Docs, provenance and example/audit consolidation |
| [#41](https://github.com/dtumad/sp1-lean/issues/41) | Measured residual build hotspots |

Order: close existing PRs and reconcile issues; establish native type/module ownership; integrate
upstream/module APIs; consolidate model consumers; migrate SP1/Rust comparison; retire superseded
code and docs. Proof work takes priority within that sequence when it is a concrete blocker.

Completion requires strict build/test/lint and compiled trust checks, accurate scope claims,
independent Rust comparison, migrated consumers and deletion of obsolete implementations.
Capstone completeness stays open until its actual targets are inhabited. CI/build reports and
historic progress belong to their PRs and issue history.

Lint findings and package suppressions remain debt. Fix them while migrating their owners;
measure proof performance rather than hiding new warnings or raising elaboration budgets.
