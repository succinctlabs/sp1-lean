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

The two **platform-device** keys are required for soundness of the statements; the two **PMP**
keys are not, and the distinction is worth stating precisely (audited 2026-08-19).

**CLINT and the interrupt generator — soundness- and faithfulness-necessary.** SP1's address
chips bound every memory access to `[2^16, 2^48)`, and two upstream device windows lie **inside**
that range: CLINT at `[0x0200_0000, 0x020C_0000)` and the simple interrupt generator at
`[0x0C00_0000, 0x0C00_0020)`. With the devices enabled, a Sail access in either window routes to
the device rather than to RAM, and `run_within_mmio_readable_mmio` /
`run_within_mmio_writable_mmio` (`Model/SailMemory.lean`) are then **false as stated** — they
quantify over `reg_val`, `offset` and `width` with no range side-condition and conclude
`.ok false s`, so `reg_val := 0x0200_0000` refutes them. Not merely unproved. Their fan-out is
not confined to the memory chips: through `run_checked_mem_read_four_bytes_fetch_of_isInitialized`
they reach the **instruction-fetch** reduction and hence every chip's `advance` obligation, all 25,
up to `Soundness/AdvanceDispatch.lean`'s `chipRows_advance_sound`. Recovering them would need a
per-access disjointness hypothesis that SP1's AIR does not derive — a new trust assumption — and
would exclude guest programs that legitimately touch those addresses. Independently, SP1
implements neither device: `clint`, `mtimecmp`, `pmpcfg` and `pmpaddr` appear **nowhere** in its
Rust tree, and its only `Interrupt` type is a synchronous trap code. Verifying against a
CLINT-enabled model would be verifying a different machine.

**`memory.pmp.count = 0` — provability, not soundness.** It is consumed by exactly one lemma,
`run_pmpCheck_none` (`Model/SailMemory.lean`), at three call sites, all of which instantiate
`priv := Privilege.Machine`. Under stock (`sys_pmp_count = 16`) with all `pmpcfg` entries OFF,
`pmpMatchAddr` returns `PMP_NoMatch` for every entry and the M-mode tail yields `none` — the same
answer. So every downstream conclusion stays **true**; only the helper needs restating, with
`priv := Machine`, a `pmpcfg_n = 0` field added to `isValidMemConfig` (one register of type
`Vector (BitVec 8) 64`, so one hypothesis), and a 16-iteration `SailME` loop peel. Estimated a few
hundred lines and a heartbeat-heavy peel — and it is the same *kind* of unconstrained-boot-register
assumption `isValidMemConfig` already carries for `mstatus.MPRV`, `mseccfg` and
`htif_tohost_base`, not a new class of trust. There is also a faithfulness leg (stock defines 16
`pmpcfg*`/`pmpaddr*` CSRs, so a guest `csrw pmpcfg0` would succeed there and trap here), but SP1
implements no CSR instructions and no current proof covers one, so that leg is unexercised.

**`memory.pmp.usable_count = 0` — no proof consumes it.** Its disclosure lemma
`sys_pmp_usable_count_eq_zero` is deliberately not `@[simp]` and has zero uses outside its own
declaration; its consumers in the model are the CSR-write paths and the config validator, neither
of which any proof reaches. It is kept because upstream's own `check_pmp` rejects
`usable_count > count`, so shipping `count = 0` with `usable_count = 16` would be a config the
model itself reports invalid.

The four top-level generated values (`plat_have_clint`, `plat_have_sig`, `sys_pmp_count`,
`sys_pmp_usable_count`) are disclosed to the audit surface as `rfl` lemmas in
`Model/SailMemory.lean`; the other two generated sites are `let`-bindings inside
`ValidateConfig` (config validation only) and are not addressable as lemmas.

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
| `PlatformConfig.lean` `plat_have_sig` | `platform.simple_interrupt_generator.supported` | `true → false` | The MMIO device that injects external interrupts, off — SP1 has no such device and no external interrupts. (`sig` is *simple interrupt generator*, not "signature": `sig_load` returns a version word, `sig_store` sets the external-interrupt-pending bits) |
| `PmpRegs.lean` `sys_pmp_count` | `memory.pmp.count` | `16 → 0` | No PMP entries — SP1 runs unprotected M-mode. The declared Sail type is `{0, 16, 64}`; 0 is a sanctioned value |
| `PmpRegs.lean` `sys_pmp_usable_count` | `memory.pmp.usable_count` | `16 → 0` | Upstream's `check_pmp` rejects `usable_count > count`, so the pair moves together |
| `ValidateConfig.lean` `clint_supported` | `platform.clint.supported` (re-read) | `true → false` | Config validator's CLINT check |
| `ValidateConfig.lean` `sig_supported` | `platform.simple_interrupt_generator.supported` (re-read) | `true → false` | Config validator's interrupt-generator check |

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

An upstream CMake option will replace the script's config-overwrite step with a plain `-D` flag
when it lands: **riscv/sail-riscv [#1861](https://github.com/riscv/sail-riscv/pull/1861)**, since
2026-08-19 reduced to a per-arch `SAIL_FORMAL_CONFIG_<ARCH>` override (see below). It and the
related #1879 are **open and unmerged**; upstream `master` (`8f91355e`, 2026-08-14) has neither, so
the `cp $CFG` + hash-guard pipeline stays as documented and nothing here is blocked on either.

**Why the generated package must keep the name `Lean_RV64D` / `LeanRV64D`** (checked 2026-08-19,
prompted by pmundkur asking on #1861 whether #1879 covers our use case). #1879 — "Refactor cmake
build to enable custom Lean builds", a Lean-only alternative that hoists the per-backend blocks
into `add_{rocq,lean,lem}_targets` functions and adds `CUSTOM_LEAN_CONFIG` + `CUSTOM_LEAN_ARCH` —
derives both the output directory and the module name from `CUSTOM_LEAN_ARCH`
(`string(TOUPPER …)`, `-o "Lean_${arch_uppercase}"`) **and forbids the only value we can use**:

```cmake
if ((${CUSTOM_LEAN_ARCH} STREQUAL "rv32d") OR (${CUSTOM_LEAN_ARCH} STREQUAL "rv64d"))
    message(FATAL_ERROR "The value of CUSTOM_LEAN_ARCH (...) cannot be 'rv32d' or 'rv64d'.")
```

Any other value renames the package. That is not cosmetic: `.lake/packages/RISCV/lakefile.toml`
(the `riscv-lean` dependency) transitively requires package **`Lean_RV64D`** from
`opencompl/sail-riscv-lean` at floating `rev = "main"`, and our root `lakefile.toml` requires it
by that same real package name precisely so Lake **dedups onto our one configured copy**. Rename
ours to `Lean_SP1` and Lake satisfies `Lean_RV64D` from opencompl `main` *as well* — two
incompatible copies of the model namespace, one of them the stock CLINT-enabled build this
config exists to disable. Renaming would also touch 994 `LeanRV64D` occurrences across the 161
generated files and destroy the `--stock` / `--sp1` byte-identity gates below, which are the
evidence for "four config keys, not patched Lean".

So the ask upstream is narrow: let a custom config **replace** the `rv64d` family (as #1861 does
by deriving the arch from the config stem), or decouple output name from arch name with a third
variable. #1879 also uses `set(CACHE{VAR} …)`, added in **CMake 4.2** (confirmed in
`cmake --help-command set`), while the repo's baseline is 3.20 and its own CI runs 3.20.0 / 4.1.2 —
on those, `CUSTOM_LEAN_ARCH` gets no default and a config-only invocation should fail to configure
on the `STREQUAL` line; CI is green only because no job exercises the custom path. (Inferred from
the docs — only CMake 4.3.2 was available locally, where the custom path configures fine.)

**The case-sensitivity loophole does not work — tested.** The guard is `STREQUAL "rv64d"`, which is
case-sensitive, so `-DCUSTOM_LEAN_ARCH=RV64D` passes it and `TOUPPER` still yields the wanted
`Lean_RV64D`. But the default `foreach (xlen IN ITEMS 32 64)` loop is unconditional and already
claims that output. Configuring #1879's head (`e37a7ad4`) with
`-DCUSTOM_LEAN_ARCH=RV64D -DCUSTOM_LEAN_CONFIG=…` fails with four errors, the first being

```
CMake Error at model/CMakeLists.txt:303 (add_custom_command):
  Attempt to add a custom rule to output
    …/model/Lean_RV64D/LeanRV64D.lean.rule
```

### Additive vs substitutive — the actual difference between the two PRs

`riscv-lean` is not being inflexible; it consumes the *stock* model under the name upstream derives
for it (`arch = rv64d` → `string(TOUPPER)` → `Lean_RV64D` / `LeanRV64D`), and `open
LeanRV64D.Functions` / `LeanRV64D.readReg` follow from that. The unusual party is us: we do not
want a *new* model, we want the *same* model *differently configured*, dropped in under the same
name so every consumer picks it up unchanged. **The package name is the substitution seam.**

- **#1879 is additive** — "build a custom Lean model *alongside* the standard ones". Its
  `FATAL_ERROR` is not an oversight, it enforces that worldview; the collision test above shows it
  is guarding something real.
- **#1861 is substitutive** — the override *replaces* the default arch list, so nothing collides,
  and the arch name comes from the config file's stem.

There is no way to express substitution inside #1879's model. So we express it *outside* CMake.

### The plan: get the substitution knob upstream, then delete the config hack

**Chosen approach** (2026-08-19, revised the same day). Rather than absorb the renaming locally, ask
for the ~10 lines upstream that make it unnecessary. #1861 was rewritten to exactly that and the
`DEPENDS` half split out as [#1885](https://github.com/riscv/sail-riscv/pull/1885):

```cmake
    string(TOUPPER ${arch} arch_uc)
    set(SAIL_FORMAL_CONFIG_${arch_uc} "" CACHE FILEPATH
        "Configuration JSON the ${arch} formal backends are generated from instead of the default.")
    if (SAIL_FORMAL_CONFIG_${arch_uc})
        set(config_file "${SAIL_FORMAL_CONFIG_${arch_uc}}")
        message(STATUS "Formal backends: ${arch} uses ${config_file}")
    endif()
```

It sits in the default `foreach (xlen …)` loop, which already funnels every formal backend through
one `config_file`, so it covers SMT/rmem/Rocq/Lean/Lem at once, adds no targets, renames nothing,
and is **inert unless set** — so it applies to `master` as-is *and* unchanged on top of #1879's
refactor. **Verified locally at master `8f91355e`**: configuring without the flag leaves the build
rules unchanged; with it, the `generated_lean_rv64d` rule becomes
`sail … --config /abs/path/to/config.json --lean … -o Lean_RV64D` — our config, upstream's name,
upstream's target.

When it lands, `--sp1` becomes one `-D` flag and the `cp` + `H0`/`H1` hash guard are deleted
outright: `OUT`, the target name, the output path and the published package name are all unchanged,
so there is no rename step and no downstream churn. **Expect one objection** — substitution means an
artifact labelled `rv64d` need not come from the stock `rv64d` config, which is presumably why
#1879 guards the standard names. It is opt-in behind an explicit `-D` and logged at configure time.

**The alternatives we are not taking.** *Renaming our architecture to `Lean_SP1`* — the 161
generated files would be free (the generator emits the new name consistently) and our own 586
references across 64 files are a mechanical sed, but `riscv-lean` names `LeanRV64D` in 4 of its own
files (118 refs: `Skeleton`, `SailToRV64`, `SailPureToInstructions`, `SailPure`) and requires the
package by that name, so we would have to fork it **permanently**; opencompl will not import an
SP1-specific model. That fork is currently disposable chores, pinned at opencompl PR #59 and slated
for deletion when #59 merges. *Generating as `SP1` and renaming the emitted tree back* — measured
and it works (on the real 171-file snapshot the rename leaves zero residue in either direction and
round-trips byte-identically), but a find-and-replace across generated output is a maintenance
hazard we would own forever, and it weakens the "generated, never hand-edited" provenance story.
Both stay on the shelf in case upstream declines substitution outright; the fallback of first
resort is simply keeping the `cp` + hash guard, which works.

The sibling `succinctlabs/riscv-lean` fork is only toolchain/dependency chores; it is pinned at
`d1d678c6`, the head of the open opencompl PR #59 ("chore: update to v4.32.2"). Repoint
`lakefile.toml` to opencompl once that merges and drop the fork outright.
