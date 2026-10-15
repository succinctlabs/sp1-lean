# Generated Sail model

LeanRV64D/ and LeanRV64D.lean are generated, never hand-edited. The pinned Sail compiler and
sail-riscv sources run with the checked-in SP1 platform configuration. Inputs, base snapshot,
OCaml version and output fingerprints have one owner:
[provenance.json](../../scripts/provenance.json). Lake's Sail dependency records the runtime.

## Semantic configuration

[sp1-overlay.json](../../scripts/sail-config/sp1-overlay.json) disables two devices SP1 does not
implement: CLINT and the simple interrupt generator. Their stock address windows lie inside the
native memory interval. Leaving them enabled would route permitted RAM accesses through MMIO and
make the memory-bridge lemmas false as stated.

The two keys affect four generated sites: plat_have_clint / plat_have_sig in PlatformConfig, and
clint_supported / sig_supported in ValidateConfig. Other platform restrictions remain explicit
configured-state hypotheses. In particular PMP uses the stock 16 entries with every entry OFF
as a Lean state condition, not a generator patch. Moving a condition from configuration to Lean
makes it visible; it does not remove the assumption.

## Reproduce

The [generator](../../scripts/sail-config/generate_lean_rv64d.sh) requires opam, CMake, Z3,
Python and Git. Its work directory defaults to ~/.cache/sp1-sail-gen; SAIL_GEN_DIR overrides it.

| Mode | Action |
|---|---|
| --deps | Prepare the pinned OCaml/Sail toolchain |
| --make-config | Deep-merge stock generated configuration with the SP1 overlay |
| --stock | Regenerate and require byte identity with the pinned base snapshot |
| --sp1 | Regenerate with SP1 configuration and require identity with the checked-in model |
| --install | Regenerate and replace the checked-in model |

The SP1-config path currently copies the configuration into the upstream build and checks its
hash before/after generation. Replace that workaround when the selected upstream build supports
an equivalent config override without changing model identity.

## Update the pair

1. Select compatible compiler, model, base snapshot and runtime revisions. Update provenance and
   the single Lake requirement deliberately; do not run bare lake update.
2. Verify --stock, regenerate the configuration, inspect the platform delta and run --install.
3. Review the generated diff and update generatedTreeSha256, generatedFiles and configSha256.
   scripts/check_pins.py uses a deterministic path/content tree hash; import its tree_hash helper
   when recording a newly reviewed snapshot.
4. Run --sp1, strict full build/tests, conformance and compiled trust checks. Expect proof updates
   where Sail internals changed; do not paper over them with new assumptions.
5. Record commands and generator environment with the PR evidence.

Sail regeneration CI independently checks configuration and byte identity. The fast pin check
detects generated edits before that expensive job. Fingerprints authenticate the reviewed
snapshot; fresh regeneration supplies the independent evidence.

The narrow RvfiDii legacy-do Lake library is a temporary elaboration workaround (#6), not a
generated-source modification. Coordinate its replacement with module-system support (#33);
both require a compatible runtime/generator pairing.
