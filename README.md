<div align="center">

![SP1 Lean](./.github/assets/header.png)

Verified RISC-V circuits in Lean, built with the public Clean DSL

</div>

This library gives SP1-style RISC-V chips semantic specifications, native Clean implementations,
soundness and completeness proofs, and bridges to the generated RISC-V Sail model. It also
contains the execution model, authenticated memory/host boundaries, and whole-machine proof
infrastructure needed to assemble those chips.

The 25 supported instruction chips are proved. The complete arbitrary mixed-execution capstone
is still open: complete supplied-target equality, WRITE/VERIFY installation, resource enforcement
and the total mixed compiler remain [tracked obligations](https://github.com/dtumad/sp1-lean/issues/12).
The existing ordinary-shard soundness/completeness results have explicit boundary, syscall and
readiness restrictions. They do not establish that capstone.

## Use and explore

```sh
lake build --wfail --iofail
lake test
lake build --wfail --iofail SP1Clean SP1CleanTest
python3 scripts/check_examples.py
```

The examples check an ADD assembly, a compiler-derived taken branch, and a verified LoadByte
fixed-table replacement, with malformed witnesses that must reject. A small
[counter machine](SP1CleanTest/Alignment/Examples/Counter.lean) illustrates a closed semantics-to-AIR
equivalence without the full SP1 proof stack. See [contributing](docs/contributing.md) for setup
and full validation, and [examples](docs/examples.md) for the precise claims.

## Read the library

| Document | Purpose |
|---|---|
| [Semantics and scope](docs/semantics.md) | Execution contract, supported domain, proved results and limitations |
| [Architecture](docs/architecture.md) | Module ownership, public boundaries and consolidation direction |
| [Contributing](docs/contributing.md) | Build, tests, proof workflow and dependency changes |
| [Assurance](docs/assurance.md) | Trust policy, semantic review and reproducible checks |
| [Export and integration](docs/export.md) | Existing backends and the Clean-native Rust migration |

Lean is the implementation source. The integration direction is Clean's built-in Lean → Rust
AIR/witness export, with comparison against a pinned SP1 release in Rust. The current
Rust → Lean oracles and whole-chip faithfulness proofs remain migration evidence; they are not
the permanent export architecture. [Tracking issues](docs/roadmap.md) distinguish this work from
the remaining semantic proofs and eventual cryptographic verifier.

Pins live in [Lake's manifest](lake-manifest.json), [the toolchain](lean-toolchain) and
[external provenance](scripts/provenance.json). Do not run bare `lake update`.
Proofs are kernel checked; the [assurance guide](docs/assurance.md) discloses generated Sail hooks
and the narrowly permitted native proof dependencies. No cryptographic verifier soundness or
formally verified Rust lowering is claimed.

Dual-licensed under [Apache-2.0](LICENSE-APACHE) or [MIT](LICENSE-MIT), at your option.
