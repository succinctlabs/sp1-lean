# Import boundaries

[`scripts/layering.txt`](../scripts/layering.txt) assigns modules to ordered strata.
[`scripts/check_layering.sh`](../scripts/check_layering.sh) enforces the map in CI and the
release audit. Responsibilities and the migration direction are in [architecture](architecture.md).

## Enforced rules

1. A module imports from its own stratum or a lower one. Every project module must have a
   mapping; the longest matching path/glob wins.
2. Pillar namespaces agree with their mapped responsibility, subject to the named exceptions.
3. `SP1Clean/Core.lean` indexes all handwritten modules in strata 0–6. The separate root-index
   check verifies complete library coverage and rejects dangling or duplicate imports.
4. Native circuits under `Native/` and `Circuits/` have no transitive import of `Extracted/`.
   Shared column types are native-owned; Rust comparison code sits above them.

Exceptions live in [layering_allowlist.txt](../scripts/layering_allowlist.txt), with reasons.
A recurring exception usually calls for a more precise stratum or an ownership move. Existing
exceptions are migration work, not a requirement to preserve the current API or file placement.

## Current strata

| Stratum | Contents |
|---|---|
| 0 | To-Upstream additions, independent of SP1 |
| 1 | Arithmetic and word foundations |
| 2 | Pure semantic Specs, execution/model vocabulary and native column types |
| 3 | Legacy Rust oracles and their interaction adapters |
| 4 | Semantic contracts and row views |
| 5 | Readers, operation gadgets and their proofs |
| 6 | Instruction chips, local proofs and event-to-row builders |
| 7 | Rust faithfulness |
| 8 | Registration, machine grounding and soundness |
| 9 | Physical table construction and completeness assembly |
| 10 | Completeness capstones |
| 11 | Exact-Rust-to-native composed artifacts |

Some directories straddle strata: chip `Bridge`/`Contracts` files depend on machine grounding,
and the converse capstones depend on table construction. The map describes those dependencies
explicitly. Directory cleanup should preserve the ordering while improving the names.

## Representation ownership

Full Sail/host/clock execution and finite snapshots live in `Model/Core/`; the shard contract
uses those same objects. Legacy event/exact-Core views lack the complete evolving host and need
explicit compatibility results before replacement. PolyFun traces, access schedules and physical
row inventories are derived views, not independent execution semantics.

Instruction identity/order and routing have one Model owner. Use the canonical Clean ledger and
retain physical occurrences when projecting it: repeated keys, disabled interactions and count
bounds are part of the contract. See [semantics](semantics.md).

Keep pure semantic contracts below circuit implementations. Colocate feature-specific arithmetic
with its consumer when it has no broader use; move a declaration when a real lower-level consumer
needs it. A theorem’s type alone does not determine the best file for its proof.

## Limits of these checks

Import reachability does not establish theorem dependence or semantic agreement. A file can be
compiled and imported without a capstone using any of its proofs. The compiled trust check audits
permitted axioms; the capstone manifest audits statement/definition dependencies. Required proof
composition still needs explicit composition theorems and review. These checks support the
[assurance boundary](assurance.md); none substitutes for it.
