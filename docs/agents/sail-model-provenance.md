# Sail model provenance — the generated `Lean_RV64D` snapshot and its config

`Lean_RV64D` is pinned to `succinctlabs/sail-riscv-lean@df1acf57` (branch
`sp1/config-generated-4.32.2`, tag `sp1-rv64d-v1.0`). The snapshot is **generator output, not a
hand-edited fork**: the pinned Sail compiler run over the pinned `riscv/sail-riscv` sources with
the SP1 platform configuration `scripts/sail-config/sp1_rv64d_cfg.json`. It equals the opencompl
daily snapshot **`11d8fa21`** everywhere except the six platform-value sites the config sets.
The maintained object is therefore a four-key config delta plus four pins — not patched Lean.

The full provenance record (compiler SHA, model SHA, config hash, invocation, environment,
verification) lives in the snapshot's own commit message; the pins are also recorded in
`docs/release-audit.md`'s table and re-checked by `scripts/check_pins.sh`.

## Why the SP1 configuration is required

Not for convenience — for soundness of the statements. SP1's address chips bound every memory
access to `[2^16, 2^48)`. Two upstream device windows lie **inside** that range:

- CLINT: `[0x0200_0000, 0x020C_0000)`
- signature: `[0x0C00_0000, 0x0C00_0020)`

With `plat_have_clint = true`, a Sail access in the CLINT window is routed to the device rather
than to RAM, so the memory-bridge lemmas in `SP1Clean/Model/SailMemory.lean` are **false as
stated** — not merely unproved. Recovering them would need a disjointness hypothesis that SP1's
AIR does not derive, i.e. a new trust assumption. Turning the devices off is what makes the
existing statements true.

The values are disclosed to the audit surface as `rfl` lemmas in `Model/SailMemory.lean`.

## The configuration (four keys → six generated sites)

`scripts/sail-config/sp1-overlay.json` is the whole semantic delta from the stock rv64d config:

```json
{ "platform": { "clint":                      { "supported": false },
                "simple_interrupt_generator": { "supported": false } },
  "memory":   { "pmp": { "count": 0, "usable_count": 0 } } }
```

The generator constant-folds these into six definition sites (match on the `def` name — line
numbers drift on every regeneration):

| Generated site | Config key | Stock → SP1 | Meaning |
|---|---|---|---|
| `PlatformConfig.lean` `plat_have_clint` | `platform.clint.supported` | `true → false` | CLINT (core-local interrupt timer) off — SP1 has no timer device |
| `PlatformConfig.lean` `plat_have_sig` | `platform.simple_interrupt_generator.supported` | `true → false` | Signature output off — SP1 has no test-signature region |
| `PmpRegs.lean` `sys_pmp_count` | `memory.pmp.count` | `16 → 0` | No PMP entries — SP1 runs unprotected M-mode. The declared Sail type is `{0, 16, 64}`; 0 is a sanctioned value |
| `PmpRegs.lean` `sys_pmp_usable_count` | `memory.pmp.usable_count` | `16 → 0` | Upstream's `check_pmp` rejects `usable_count > count`, so the pair moves together |
| `ValidateConfig.lean` `clint_supported` | `platform.clint.supported` (re-read) | `true → false` | Config validator's CLINT check |
| `ValidateConfig.lean` `sig_supported` | `platform.simple_interrupt_generator.supported` (re-read) | `true → false` | Config validator's signature check |

Because the six sites are images of four config keys, the old hand-maintenance invariant ("all
six must move together or the platform is incoherent") is now structural: the generator reads
each key everywhere it is consumed.

Downstream consumers, unmodified and listed for review: `Platform.lean` guards on
`plat_have_clint`; `SysControl.lean` / `PmpControl.lean` guard on `sys_pmp_count`;
`plat_sig_base` / `plat_sig_size` sit next to `plat_have_sig` in `PlatformConfig.lean`;
`ValidateConfig.lean` consumes all six.

## The pipeline

`scripts/sail-config/generate_lean_rv64d.sh` carries the four pins at its top (Sail compiler
SHA, sail-riscv SHA, the opencompl base snapshot, the published SP1 snapshot) and four modes:

- `--deps` — one-time toolchain: an OCaml 5.2.1 opam switch (matching the opencompl nightly) and
  the pinned Sail compiler built from source. The opam release of sail is **not** sufficient —
  the Lean backend and the JSON-comment handling in the pinned compiler postdate it.
- `--make-config` — regenerate `sp1_rv64d_cfg.json` = the stock generated
  `build/config/rv64d_v256_e64.json` (comments stripped) deep-merged with the overlay.
- `--stock` — regenerate with the stock config and diff against the opencompl base. **Expected:
  byte-identical.** This is the pin-verification run; it also proves the generator's output is
  OS-independent (verified macOS vs the nightly's ubuntu, 2026-08-06).
- `--sp1` — regenerate with the SP1 config; diff vs the base must show exactly the six sites,
  and diff vs the published SP1 snapshot must be identical (the script's exit gate).

Publishing a new snapshot is deliberate and manual: branch the fork repo from the target
opencompl base, replace `LeanRV64D/` + `LeanRV64D.lean` + `lakefile.toml` + `lean-toolchain`
with the generated output (keep the snapshot's resolved `lake-manifest.json` — it records the
lean-sail pairing), commit with the provenance template (see `df1acf57`), tag, push, and pin by
SHA here. A rev must be reachable from a branch or tag, or Lake's clone fails on cold machines.

What the config cannot express stays where it was: `h_mseccfg_pmm` (pointer masking has no
config toggle) remains a `SailConfigured` hypothesis, the platform-hook `axiom`s remain trust
item T2, and dynamic register state remains the boot predicate's business.

## The runtime/model pairing rule

⚠ **The generated model and the `lean-sail` runtime must move together.** A v4-generated
snapshot against `lean-sail` v5 fails with `unknown namespace Sail.ConcurrencyInterfaceV2` — v5
deleted that namespace and replaced it with `Sail.ArchSem.*`, while older generated models still
emit `LeanRV64D.ConcurrencyInterfaceV2` shims that reference it.

There is no way to dodge this by choosing a base: upstream `f700c484` is a *single* daily
regeneration that both removed the V2 shims **and** changed `MemoryOpResult`'s error arm from
`ExceptionType` to `physaddr × ExceptionType`. Every v5-compatible base carries the memory
refactor.

## Re-pinning against a new base

opencompl regenerates the model *daily*, so any re-pin is a proof-churn event against the
symbolically-reduced generated internals, independently of the config:

1. Update `SAIL_SHA`/`SAIL_RISCV_SHA`/`BASE_SNAPSHOT` in the generation script to the new
   pairing (opencompl's nightly clones both at head; recover its inputs by commit-time window if
   needed — that is how the current pins were discovered).
2. `--stock` until byte-identical vs the new base; then `--make-config` (the stock config may
   have gained keys) and `--sp1`; audit that the base diff is still exactly the six sites.
3. Publish + tag + pin as above, and refresh the pin table in `docs/release-audit.md`.
4. Expect churn in `Model/SailMemory.lean` and the `Proofs/Sail/` decode-reduction lemmas that
   pattern-match generated internals. The `11d8fa21` base carried a substantial such event: 158
   files, +2333/−1040 over the previous `793034f3` pin — beyond the `MemoryOpResult` change it
   moved `pmaCheck` to `Result Phys_Mem_Access_Info ExceptionType`, rewrote `VmemUtils`
   (`plat_misaligned_exception` went monadic → pure), added fields to `PMA` and a *leading*
   field to `pma_check_opts` (breaking positional constructors), and restricted
   `plat_{me,mi}deleg_delegatable_bits` from all-ones to masks. `try_step`, `fetch`,
   `ext_decode`, and the `execute_*` functions were unchanged.

An upstream `SAIL_FORMAL_CONFIG` CMake option (riscv/sail-riscv PR #1861) will replace the
script's config-overwrite step with a plain `-D` flag when it lands.

The sibling `succinctlabs/riscv-lean` fork is only toolchain/dependency chores; it is pinned at
`d1d678c6`, the head of the open opencompl PR #59 ("chore: update to v4.32.2"). Repoint
`lakefile.toml` to opencompl once that merges and drop the fork outright.
