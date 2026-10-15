# Architecture

The library separates execution meaning from circuit implementations, machine assembly and
backend integration. Specifications should be readable without unfolding witness generation,
and a chip should be understandable with its local correctness proofs.

## Current ownership

| Area | Current source | Responsibility |
|---|---|---|
| Semantics | `SP1Clean/Semantics/`, `SP1Clean/Math/`, `SP1Clean/Model/` | Pure contracts, arithmetic, official Sail adapters, complete execution, snapshots, host effects and resources |
| Contracts | `SP1Clean/FormalModel/` | Semantic Specs and checked relation/capstone targets |
| Circuits | `SP1Clean/Circuits/`, `SP1Clean/Native/`, `SP1Clean/Proofs/Chips/`, `SP1Clean/Proofs/Operations/` | Native columns/readers/gadgets/chips, witnesses and local soundness/completeness |
| Machine | `SP1Clean/Soundness/`, `SP1Clean/Proofs/Completeness/`, `SP1Clean/Alignment/` | Registration, assembly, grounding, Sail bridges and physical compiler |
| Legacy Rust alignment | `SP1Clean/Extracted/`, `SP1Clean/Faithful/`, `SP1Clean/Composition/` | Generated pinned oracles and exact-to-native comparison evidence |
| Upstream additions | `ToClean/`, `ToPolyFun/`, `ToMathlib/` | Reusable missing APIs in upstream namespaces, independent of SP1 |
| Tests | `SP1CleanTest/` | Executable examples, non-vacuity, adversarial witnesses and native computation |

The current import rules are encoded in [layering.txt](../scripts/layering.txt);
[the layering guide](layering.md) describes their mechanical enforcement.
The core index is [SP1Clean/Core.lean](../SP1Clean/Core.lean); the full index is
[SP1Clean.lean](../SP1Clean.lean). Tests never feed production imports.

Execution memory retains newest-write history. Fixed intervals normalize memory or the program's
protection mask to sorted, bounded nonzero entries, preserving every in-range read. Each interval
table has at most twice its live-entry count plus one rows, independently of redundant writes and
explicit zeros. Byte and word reads take only an address; their selected intervals and comparison
columns are internal witnesses generated through Clean's built-in IR. Word reads authenticate all
eight bytes and require the complete footprint to fit in native memory. Final RAM validation
takes the complete memory record directly, retaining its clock and value in the receipt ledger.

## Consolidation direction

[#16](https://github.com/dtumad/sp1-lean/issues/16) moves ownership into purpose-oriented
**Semantics / Circuits / Machine / Export** areas, guided by Clean's Specs, Types, Gadgets,
Air and Backends organization. This is an in-progress migration, not a description of a completed
directory move.

Contracts stay below implementations. Feature directories colocate definitions, witness generation
and local proofs; machine-specific grounding stays in Machine. Lean module visibility supplies
public entry points and private implementation details, with exposed definitions only where
consumers need reduction. [#33](https://github.com/dtumad/sp1-lean/issues/33) owns that migration,
including generated Sail prerequisites.

The field/word zero tests, word equality, 16-bit comparison/high-bit and signed/unsigned word comparison
gadgets follow this boundary:
`Semantics/Specs/` owns their inputs, semantic relations and result interpretations;
`Circuits/Gadgets/` owns their witness
generation, circuits and bundled proofs. Legacy faithfulness imports the gadgets and their
structural assertion relations from above.

The unsigned comparison contract describes the selected limb and whole-word order. It also
preserves inactive-row certificates with a nonzero selector: the selected limb and all lower
limbs must agree. Equivalence with the AIR equations is proved inside the gadget; consumers
do not need those equations to interpret the result.

Signed comparison selects unsigned order with zero sign columns, or active signed order with
the operands' high bits recorded. The latter compares sign-biased words through the unsigned
contract. Its public result gives whole-word order and detects equality in either mode, so branch
decisions need no separate mode condition for equality. Padding retains the unsigned contract's
complete certificate domain.

The bitwise arithmetic, bus message types, byte predicates and channel declarations also use
module mode. They remain below the gadgets and contain no Sail or generated-oracle dependency.
The shared reader, operation and chip contracts use module mode as well. Operation contracts
depend only on word arithmetic and native column types; chip contracts explicitly compose the
independent reader and operation contracts. Consumers import feature specifications directly.

DivRem's public row contract lives in `Semantics/Specs/DivRem`, with the pure RV64 functions in
`Semantics/ISA/RV64` and its native row in `Circuits/Types/DivRem`. Comparison and product-cluster
contracts live under `Circuits/Gadgets/DivRem`: they describe implementation evidence, including
the intermediate raw assertions, and are not dependencies of the public semantic contract.
The multiplication gadget takes the caller's result word and owns its selector-gated placement
checks. Mul and DivRem consume that bundled contract directly; no separate placement equations
are needed at the chip boundary. Disabled interactions retain the supplied result limbs.
Mul supplies its five opcode selectors as inputs and derives activity from their sum; it needs
no external selector hints or separate activity cell.
Its row types and basic evaluation lemmas live in `Circuits/Types/Mul`; the reader/ISA contract
lives in `Semantics/Specs/Chips/Mul`. The native implementation imports this feature contract
directly, independently of the shared chip-contract aggregate.
The multiplication gadget lives under `Circuits/Gadgets/Mul`, with arithmetic certificates, witness
construction and constraints below its bundled proofs. Its operand/result interpretation and the
safe byte-decomposition contract live under `Semantics/Specs`. Byte decomposition, the carry-chain
helpers and DivRem's product-cluster evidence also use module mode. The complete product certificate
and its semantic readout live in the arithmetic layer, so DivRem's product contract does not import
multiplication constraints, witness construction or bundled proofs. The certificate retains intermediate
witness and padding obligations; the semantic readout describes the selected product slice.

Bitwise byte and word gadgets share native columns in `Circuits/Types/Bitwise` and pure contracts
in `Semantics/Specs/BitwiseBytes` and `Semantics/Specs/Bitwise`. The word contract retains the complete
byte certificate and derives operand/result ranges and whole-word semantics. Its bundled gadget
requires a valid opcode and binary activity; byte lookups establish operand bounds on active rows.
Honest witness construction retains its bounded-input requirements. Byte decomposition is a pure
projection, with no separate empty assertion gadget. The whole-chip input and output types live
in `Circuits/Types/BitwiseChip`, with their public contract in `Semantics/Specs/Chips/Bitwise`.
Three explicit opcode selectors determine activity; Clean witnesses only the sixteen byte cells.
Ordinary table construction needs no per-row flag hints. The 51-cell physical row matches SP1's
supervisor layout after permuting inputs and witnesses. Generated Rust-to-Lean oracles remain
migration evidence until their remaining consumers are replaced.

Lt likewise owns its row types in `Circuits/Types/LtChip` and its reader/ISA contract in
`Semantics/Specs/Chips/Lt`. Two explicit SLT/SLTU selectors determine activity; Clean witnesses
only the ten comparison cells. The resulting 44-cell row uses SP1's supervisor column layout.
Soundness still requires bounded operand words, and honest construction retains reader, clock
and timestamp obligations. Its table builder uses ordinary inputs with no selector hints.

ShiftLeft and ShiftRight own their row types in `Circuits/Types` and RV64 contracts in
`Semantics/Specs/Chips`. Their two/four explicit selectors determine activity; Clean generates
31/33 witnesses, giving SP1's 65/69-cell supervisor layouts. Zero inputs generate the required
nonzero padding powers. Ordinary table builders need no hints; bounded operands and reader/clock
obligations remain.

Branch owns its row types in `Circuits/Types/BranchChip` and its reader/RV64 contract in
`Semantics/Specs/Chips/Branch`. Six explicit selectors determine activity. Clean generates ten
comparison cells, the branch decision and three next-PC limbs, giving SP1's 45-cell supervisor
layout. Honest construction retains operand, reader, clock and target bounds; it derives the
decision's binary and semantic properties. All 25 instruction chips now use empty prover hints.
Providers may still require external witness data under their own contracts.

Complete API migrations replace old objects and all in-repository consumers. There is no external
compatibility requirement. Prefer one transition/trace, one interpretation/Realizes boundary,
one complete finite state with projections, and one typed physical inventory. Retain distinctions
that express different meanings: finite versus realized state, event versus physical row, semantic
limit versus witness capacity, and raw ledger versus a derived accounting view.

## Proof boundaries

A semantic `Spec` describes the intended relation; it does not repeat assertions. A bundled
Clean circuit is the compositional proof boundary. Parents invoke child `circuit` interfaces
rather than inline the implementation or reconstruct its soundness proof.

Channels carry actual field tuples and multiplicities. Global execution truth is derived from
raw constraints, complete balance, authenticated boundaries and ranked chronology; it is not
smuggled into a channel payload. Keep occurrence lists through transformations: equal keys do
not identify occurrences, and disabled interactions still affect characteristic bounds.

Source and target register/RAM authentication use separate fixed membership channels. Clean's
fixed-column programs own register rows and normalized sparse-memory intervals, including zero
gaps, eligibility and padding; only counts are prover-owned. Source RAM reads authenticate eight
bytes before emitting one Memory occurrence. Target reads retain the complete final receipt.
Global balance and fixed prefixes establish membership without caller-supplied provider validity.
Projected ledgers retain every fixed row, including unused intervals and zero-count padding.

A projected witness derives canonical data from its retained physical rows. Prove row-layout,
lookup and channel-guarantee transport at the actual two data environments; dropping tables or
truncating rows does not preserve the complete data function. Public-verifier guarantees are
separate from physical-table constraints. Install public assertion checks after assembling the
complete inventory so their fresh channels account for every extension's traffic.

Semantic grounding takes its program and initial clock from the statement. Raw ensemble validity
binds the public input to that statement; the external Program-provider contract binds active rows
to its program. Canonical table data supplies the physical evaluation environment and does not
implicitly authenticate ROM, entry-point or clock metadata. The legacy program encoder remains
for generation inputs and fixtures until those consumers use semantic objects directly.

SP1 grounding needs an exhaustive ordered execution path. Clean verifier guarantees alone do
not supply it, so adopting VmTables is justified only when it removes the existing obligation.
Generalize authentication, ordering or resource arguments when a real consumer demonstrates
the abstraction.

Native readers and operations own their shared column types under `Circuits/Types`. These modules
and the word foundation use Lean module mode. The import gate rejects any transitive dependency
from native circuits back into `Extracted`. Legacy Rust oracles reuse the native types only after
the generator checks their field layouts against independent Rust reflection output; the
assertion and interaction definitions remain generated migration evidence.

## Upstream and generated boundaries

To* means “To Upstream”: additions belong in the namespace they would have upstream and state
the missing capability in their module documentation. ToMathlib imports Mathlib; ToPolyFun imports
PolyFun; ToClean imports Clean and may use those two. None imports SP1Clean.

Prefer additions over dependency forks. A fork is reserved for a required modification of a
canonical declaration that cannot be expressed at an extension layer. Its patch and exit remain
explicit. Built-in Clean export is the integration owner; thin SP1 adapters should not become
another emitter, expression IR, interpreter or scheduler.

Generated Sail output is owned by its pinned generator/runtime pair. Legacy Rust oracles are owned
by their generator until migration. See [provenance](../scripts/provenance.json),
[export](export.md) and [assurance](assurance.md) for the distinct trust boundaries.
