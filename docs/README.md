# Documentation

Start with the [repository README](../README.md). The maintained guides have distinct jobs:

- [Semantics and scope](semantics.md): durable execution contract and current theorem boundaries.
- [Architecture](architecture.md): ownership, dependency direction and migration boundaries.
- [Contributing](contributing.md): setup, changes and validation.
- [Assurance](assurance.md): logical trust, semantic review and independent evidence.
- [Export and integration](export.md): library consumers, backends and Rust comparison.
- [Examples](examples.md): reproducible concrete witnesses and a small complete machine.

[The roadmap](roadmap.md) links to current tracking issues; it does not duplicate their progress
logs. [Contributor notes](agents/README.md) hold specialized proof, generation and profiling
procedures. Historical independent reviews under [audits](audits/) are dated evidence, not the
current status or architecture.

Source module docstrings describe individual APIs. Keep temporary restrictions explicit and
attach an owning issue and an exit condition. Keep build reports, performance measurements and
example output in ignored artifacts or the PR that uses them.
