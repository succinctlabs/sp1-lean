# Semantics and scope

The durable target is soundness and constructive completeness of native Clean AIR for **bounded
local execution segments**, with complete source and target states and all eight constrained
host calls. A segment may continue, halt, or be empty; boot-to-HALT is a corollary.

```text
nativeEnsemble(context, source, target).Statement(canonicalHeader)
  ↔ ∃ events, boundedNativeExecution(context, source, target, events)
```

This is a target, not an instantiated theorem. Its checked definitions are
[Shard.Executes](../SP1Clean/FormalModel/Shard.lean) and the
[soundness/compiler targets](../SP1Clean/Soundness/Shard/Contract.lean).
[#12](https://github.com/dtumad/sp1-lean/issues/12) owns their remaining obligations.

## State and execution

[Core execution](../SP1Clean/Model/Core/Execution.lean) relates complete Sail state, concrete
host state and clock. [ExecutionPath](../SP1Clean/Model/Core/ExecutionPath.lean) composes those
steps; finite [snapshots](../SP1Clean/Model/Core/ExecutionSnapshot.lean) describe their boundaries.
Memory snapshots are projections, not an alternative execution model. Complete comparison
includes register-map presence, sparse RAM, simulator runtime, nextPC/retirement bookkeeping,
host queues, outputs, commitment banks, requests/replies and optional exit.

Ordinary steps execute the official Sail interpreter. Host calls use one evolving concrete
host/clock, with the exact ECALL word checked in both committed code and Sail memory.
ENTER, HALT, COMMIT, COMMIT_DEFERRED, HINT_LEN, HINT_READ, WRITE and VERIFY belong to the
semantic domain. The older fixed-handler ordinary/HALT view has an adapter for that fragment;
it is not equivalent to arbitrary mixed host execution.

Semantic events, elapsed ticks and physical AIR rows are different quantities. Ordinary
instructions cost eight ticks and host scheduling uses the explicit 264-tick window.
Refreshes and padding are implementation rows, not extra semantic instructions. An empty
identity preserves incoming observations, including optional nextPC and the increment flag.
A stopped source permits only an identity.

## Platform policy

The supported native profile is RV64 integer/multiply-divide execution on SP1's configured
platform. Unsupported instructions, compressed ISA/alignment mode, floating point, other
privilege profiles, user/mprotect AIR and cryptographic precompiles are not silently covered.

- Source validation supplies initialized architectural state and the generated SP1 platform
  configuration. The Sail model disables unsupported devices through generation-time settings;
  MPRV, pointer masking, relevant extension state and PMP/platform hypotheses remain explicit.
- Compressed alignment mode is excluded by `misa.C = 0`, not just by refusing compressed words.
- Committed code is readable from official Sail memory at each executed PC. A final PC need not
  be fetchable unless another step executes.
- Ordinary writes cannot touch protected code bytes, including same-value writes. Permission
  uses the decoded SB/SH/SW/SD byte span, not the enclosing eight-byte memory cell.
- Sail can normally retire misaligned accesses on this platform. Any narrower native AIR
  alignment restriction must appear in the semantic profile or be proved by its adapter;
  retirement alone is insufficient.
- Register x0, aliases, partial-cell writes and absent sparse keys retain their semantic meaning.
  Presence of a zero-valued register can matter at a complete boundary.

These are model choices and explicit compatibility boundaries. They must not be confused with
temporary missing proofs or with exact equality to upstream SP1's AIR.

## Resources and host effects

The concrete domain uses data-only `ResourceLimits` and `nativeProfile` computed from the existing
execution path. Limits describe semantic work, intermediate occupancy, encoding ranges and
boundary sizes. AIR soundness must derive them, and completeness must prove the full physical
construction fits them. Independent per-table or per-channel `p - 1` ceilings do not establish
a bound on their combined expansion. A conservative estimate may justify numeric parameters;
it must not become a per-execution readiness condition in the public equivalence.

Host effects include padding writes, peak queue/output/request resources, ordered byte streams
and fresh allocation history. Popping a hint does not authorize reusing its node.
WRITE must distinguish exact 64-bit descriptor branches from low32 branches and authenticate
x12, buffer reads, output, hints and hook replies. VERIFY authenticates both 32-byte reads,
overlap and the request-bound reply interface; it does not prove cryptographic verification.
Mutable executor commitment banks are distinct from fixed digest checks in the exact Rust AIR.

## What is currently proved

| Surface | Result and limit |
|---|---|
| 25 instruction chips | Native soundness/completeness and Sail bridges; whole-chip Rust faithfulness on reconstructed rows in the codec image |
| Execution model | Complete steps/paths, finite boundaries, split/join, semantic boot/HALT, independent ROM/frame/fetch preservation and PolyFun connections |
| Ordinary construction | Deterministic 55-table compiler on an explicitly narrower admissible domain; readiness/capacity restrictions remain local to it |
| Ordinary soundness | `supported_core_native_sound` assumes native algebra, semantic boundary binding and an inactive syscall table with a physical Halt table |
| Installed host assembly | Six calls: HALT, ENTER, COMMIT, COMMIT_DEFERRED, HINT_LEN and HINT_READ; genuine replay and endpoint observations are derived |
| Complete Memory boundary | Installed target values and untouched-location coverage imply the finite comparison; the complete Memory ensemble retains its separate public verifier |
| Sail boundary | Static target checks, protected ordinary receipts and ordered observation are proved; combined dynamic supplied-target equality remains open |
| Concrete examples | Accepted ADD and compiler-derived BEQ assemblies; LoadByte fixed-table replacement with occurrence-preserving transport |
| Exact upstream AIR | A paired 34+6-table relation with a 160-cell public-value block and conditional refinement combinators; no closed exact-Core theorem |

Current Rust evidence is tied to the semantic/extractor revisions in
[provenance](../scripts/provenance.json). A release upgrade must review loader/host behavior as
well as AIR equations; it cannot be achieved by changing a version string.

The full mixed target equality, private terminal cursor/facade, fresh allocation authentication,
WRITE/VERIFY installation, complete resource enforcement, compatible capacity and total mixed
compiler remain open. No caller-supplied grounding, provider validity, syscall inactivity or
compiler-success premise may replace those obligations.

## Separate long-term claims

The native proof establishes AIR-to-execution meaning. Rust differential comparison establishes
tested agreement for a declared profile; formal code-generation correctness is another theorem.

A future SP1 verifier program has three layers: executable Core verifier agreement, cryptographic
knowledge soundness yielding an AIR witness with an error bound, and AIR-to-Sail refinement.
Core, Compressed, Plonk and Groth16 are distinct targets. An unconditional deterministic
`verifyCore = true → execution` theorem is not the intended cryptographic claim.
