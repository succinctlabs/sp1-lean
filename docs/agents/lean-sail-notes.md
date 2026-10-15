# Lean and Sail dependencies

The authoritative Lean graph is lakefile.toml, lake-manifest.json and lean-toolchain.
External generator inputs are in [provenance.json](../../scripts/provenance.json).
No path dependencies or moving branches; update one Lake requirement at a time.

A commit must be reachable from a published branch/tag: a warm local git object can hide a pin
that a fresh Lake clone cannot fetch. Validate a changed pin in a clean checkout.

The generated LeanRV64D model and Sail runtime are a compatible pair. Updating one can invalidate
generated namespaces, memory result types and every symbolically reduced proof. Regenerate through
[the owned pipeline](sail-model-provenance.md), never by editing generated Lean.

## Temporary choices

| Choice | Reason | Exit |
|---|---|---|
| lean-sail fork pin | Fully qualifies an ambiguous PreSail open that otherwise warns under the strict build | Consume upstream rems-project/lean-sail#14 in a compatible runtime |
| LeanRV64DRvfi library / legacy do | Avoids exponential discarded-action elaboration in generated RvfiDii | #6: pinned Lean/backend fix, regenerated/validated model and measured build |
| Non-module SP1/Sail consumers | Generated Sail and its runtime are not yet migrated together | #33: generation-time module support, then complete consumer migration |
| Current toolchain | The pinned Clean/PolyFun/Sail graph is validated together | Deliberate coordinated compatibility review; never bare lake update |

## Useful proof details

Sail.ConcurrencyInterfaceV1 owns the sequential state and monad. Prefer generated LeanRV64D
shims where available; some def shims still need their underlying PreSail form for simplification.
Narrow imports keep generic arithmetic independent of the full Sail/Mathlib closure.

Sail's global integer tokens can capture adjacent identifiers beginning with i: write a space
after arithmetic operators. Lean module mode does not justify changing arithmetic meaning to
avoid a parsing issue.

Memory proofs require explicit configured-state hypotheses, including disabled pointer masking,
MPRV and PMP entries. These are semantic assumptions, not axioms to add to the trust policy.
The generated device configuration and its rationale are documented with the pipeline.

After a dependency change, finish with the strict full library/test build and compiled trust
checks. A standalone lake env lean invocation does not refresh dependent oleans.
