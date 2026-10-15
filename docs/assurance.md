# Assurance

Kernel-checked proofs, semantic review, generated-source provenance and independent executable
comparisons answer different questions. No one check substitutes for the others.

## Logical trust

[trust_policy.json](../scripts/trust_policy.json) is the reviewed authority. It permits:

- Lean's logical baseline: propext, Classical.choice and Quot.sound.
- Named external operations in the generated Sail interface. These are model inputs; occurrence
  in the interpreter relation does not imply a supported execution invokes the operation.
- Named existing bv_decide proof owners, including those inherited from pinned Clean. Their
  native certificate evaluation adds compiled-computation trust.
- Test-scope native_decide/bv_decide only; production may not acquire test-native dependencies.

sorryAx and unknown axioms fail in both scopes. There is no automatic policy update.
Generated axiom counter suffixes are normalized, but a new proof owner requires explicit review.

```sh
lake build --wfail --iofail SP1Clean SP1CleanTest ToClean ToMathlib ToPolyFun
python3 scripts/check_trust.py
lake env python3 scripts/test_trust_integration.py
scripts/run_audit.sh
```

The scanner follows declaration types and bodies, including private declarations and mutual
families. Source-discovered module coverage and root-index checks prevent omission. Reports in
.lake/build/trust record source state, dependency graph, policy digest and classified dependencies.
Incomplete output, missing modules and scanner failures reject; old reports cannot stand in for
a current run. The scanner checks compiled environments, not anonymous examples or unused field
defaults, and cannot make stale oleans current. Source guards and a fresh build remain necessary.

## Semantic review

A theorem can be axiom-clean and state the wrong claim. Review the actual predicates and
quantifiers at these boundaries:

| Surface | Review question |
|---|---|
| [Shard.Executes](../SP1Clean/FormalModel/Shard.lean) | Complete source/target equality, real Sail/host execution, permissions and independently defined resource limits? |
| [Shard targets](../SP1Clean/Soundness/Shard/Contract.lean) | Raw acceptance on the AIR side, total data-only construction on the semantic side, no hidden readiness premises? |
| [Chip contracts](../SP1Clean/FormalModel/Contracts/Chips.lean) | Semantic arithmetic and architectural effects rather than copied constraint equations? |
| [Reader contracts](../SP1Clean/FormalModel/Contracts/Readers.lean) | Live operand/address/clock observations, explicit assumptions and channel requirements? |
| [Complete execution](../SP1Clean/Model/Core/Execution.lean) | One evolving complete Sail/host/clock state? |
| [Memory snapshots](../SP1Clean/Model/Core/MemorySnapshot.lean) | Untouched locations, absent keys and full boundary changes covered? |
| [Core AIR relation](../SP1Clean/FormalModel/CoreAIRRelation.lean) | Exact pinned table/public-value scope distinguished from the native model? |
| [Realizes](../ToClean/Air/Realizes.lean) | The intended public language rather than a vacuous profile? |

`python3 scripts/check_capstone_contract.py` builds the checked roots and compares their types
and semantic definition dependencies with the [reviewed manifest](snapshots/capstone-contract.json).
An intentional semantic change needs review before `--update`; changing trust policy does not
update this record. Declaration-name presence in prose is not a semantic check.

## Provenance and executable evidence

[Lake's manifest](../lake-manifest.json) resolves Lean dependencies.
[External provenance](../scripts/provenance.json) records SP1/Sail inputs and generated output
fingerprints. `scripts/check_pins.py` checks actual values, including repository URLs, generated
Sail/config hashes, the Lean semantic revision and dump pin. Regeneration CI independently
compares fresh output with the checked-in trees.

The legacy Rust extractor checks the clean pinned checkout, semantic ancestor and derive-only
machine-source changes. Its compiler and serializer remain trusted. Whole-chip faithfulness
proves equality of specified assertion/interaction systems on reconstructed rows; it does not
prove the extractor implementation correct or close exact-Core-to-Sail refinement.

Real-row non-vacuity, accepted and adversarial assemblies, SP1 dump comparison, Rust evaluation and
independent WASM/R1CS witnesses supply distinct tests. The shared example runner rejects malformed
or incomplete JSON, mismatched expectations and Lean diagnostics even after a zero exit.
Repeated and zero-multiplicity occurrences, provider demand, padding and alternate valid witnesses
must survive fixture consolidation.

## Current and future claims

See [semantics](semantics.md) for the exact proved/open boundary. Native ROM/host strengthening
does not automatically agree with Rust. The Lean → Rust migration will replace reverse extraction
with independently sourced Rust comparisons for declared profiles. It will not turn tests into
a formal lowering theorem.

Cryptographic knowledge soundness, transcript/PCS assumptions, extraction error bounds and
Core/Compressed/Plonk/Groth16 distinctions remain separate from AIR-to-execution correctness.
Dated reports under audits are historical evidence; use current builds and predicates for a new claim.
