# The Sail fork delta — the exact `succinctlabs/sail-riscv-lean` changes, and how to drop them

`Lean_RV64D` is pinned to `succinctlabs/sail-riscv-lean@579d9de4` (branch `dtumad/clean-native-4.32.2`),
which is the opencompl upstream generated snapshot **`11d8fa21`** plus **six platform-configuration
values across three files**. Nothing else differs: no generated-code edits, no `lean-toolchain` edit.

This doc records the delta so it can be re-applied mechanically against a future base, or retired.

## Why the fork is required

Not for convenience — for soundness of the statements. SP1's address chips bound every memory access to
`[2^16, 2^48)`. Two upstream device windows lie **inside** that range:

- CLINT: `[0x0200_0000, 0x020C_0000)`
- signature: `[0x0C00_0000, 0x0C00_0020)`

With `plat_have_clint = true`, a Sail access in the CLINT window is routed to the device rather than to
RAM, so the memory-bridge lemmas in `SP1Clean/Model/SailMemory.lean` are **false as stated** — not merely
unproved. Recovering them would need a disjointness hypothesis that SP1's AIR does not derive, i.e. a new
trust assumption. Turning the devices off is what makes the existing statements true.

The three values are disclosed to the audit surface as `rfl` lemmas in `Model/SailMemory.lean`.

## The delta (SP1 platform config)

Match on the `def` name, not the line — line numbers drift on every regeneration.

| File | `def` (upstream value) | Fork value | Meaning |
|---|---|---|---|
| `LeanRV64D/PlatformConfig.lean` (~L11022) | `plat_have_clint : Bool := true` | `false` | CLINT (core-local interrupt timer) off — SP1 has no timer device |
| `LeanRV64D/PlatformConfig.lean` (~L11030) | `plat_have_sig : Bool := true` | `false` | Signature output off — SP1 has no test-signature region |
| `LeanRV64D/PmpRegs.lean` (~L224) | `sys_pmp_count : Int := 16` | `0` | No PMP entries — SP1 runs unprotected M-mode |
| `LeanRV64D/PmpRegs.lean` (~L228) | `sys_pmp_usable_count : Nat := 16` | `0` | Must track `sys_pmp_count` — see below |
| `LeanRV64D/ValidateConfig.lean` (~L845) | `clint_supported : Bool := true` | `false` | Config validator's CLINT check |
| `LeanRV64D/ValidateConfig.lean` (~L851) | `sig_supported : Bool := true` | `false` | Config validator's signature check |

**The last three are not optional.** Upstream's own `ValidateConfig.check_pmp` rejects
`sys_pmp_usable_count > sys_pmp_count`, and its CLINT/signature checks assert the corresponding windows
lie within configured PMA memory. Setting `sys_pmp_count := 0` alone therefore describes a configuration
that upstream itself considers invalid. All six must move together for the fork to describe a coherent
platform.

Downstream consumers, unmodified and listed for review: `Platform.lean` guards on `plat_have_clint`;
`SysControl.lean` / `PmpControl.lean` guard on `sys_pmp_count`; `plat_sig_base` / `plat_sig_size` sit
next to `plat_have_sig` in `PlatformConfig.lean`; `ValidateConfig.lean` consumes all six.

### Not part of the delta any more

- **The `noncomputable section` removal from `Defs.lean` is dropped.** It was a workaround for Lean issue
  #14125 (an LCNF panic cascade over computable declarations), fixed in Lean 4.32.0. Stock unpatched
  source now builds a 34 MB olean and 9.5 MB of generated C.
- **The `lean-toolchain` edit is dropped.** Lake does not enforce a dependency's own toolchain file.

## The runtime/model pairing rule

⚠ **The generated model and the `lean-sail` runtime must move together.** A v4-generated snapshot against
`lean-sail` v5 fails with `unknown namespace Sail.ConcurrencyInterfaceV2` — v5 deleted that namespace and
replaced it with `Sail.ArchSem.*`, while older generated models still emit `LeanRV64D.ConcurrencyInterfaceV2`
shims that reference it.

There is no way to dodge this by choosing a base: upstream `f700c484` is a *single* daily regeneration
that both removed the V2 shims **and** changed `MemoryOpResult`'s error arm from `ExceptionType` to
`physaddr × ExceptionType`. Every v5-compatible base carries the memory refactor.

## Re-applying against a new generated base

opencompl regenerates the model *daily*, so any re-pin is a proof-churn event against the
symbolically-reduced generated internals, independently of the fork.

1. Branch from the target opencompl `sail-riscv-lean` commit.
2. Set the six `def`s/`let`s above to the fork values (grep by name; ignore line drift).
3. Push to `succinctlabs/sail-riscv-lean` and pin by SHA in `lakefile.toml`.
4. Verify `LeanRV64D` builds, then expect churn in `Model/SailMemory.lean` and the
   `Proofs/Sail/` decode-reduction lemmas that pattern-match generated internals.

The `11d8fa21` base carried a substantial such event: 158 files, +2333/−1040 over the previous
`793034f3` pin. Beyond the `MemoryOpResult` change it moved `pmaCheck` to
`Result Phys_Mem_Access_Info ExceptionType`, rewrote `VmemUtils` (`plat_misaligned_exception` went
monadic → pure), added fields to `PMA` and a *leading* field to `pma_check_opts` (breaking positional
constructors), and restricted `plat_{me,mi}deleg_delegatable_bits` from all-ones to masks. `try_step`,
`fetch`, `ext_decode`, and the `execute_*` functions were unchanged.

## Dropping the fork

The C backend already exposes these as *runtime* config; the Lean backend hardcodes them as `def`s that
admit no project-side override.

**The durable fix is to regenerate from a Sail configuration JSON** rather than patch generated Lean. All
six values are first-class Sail config parameters — `sys_pmp_count`'s declared Sail type is literally
`{0, 16, 64}` — so a generation-time config file expresses the SP1 platform directly and the fork
disappears. This is post-v1.0 follow-up work, not a release blocker.

The upstream ask, if a config file proves insufficient: have opencompl's Lean backend emit the platform
config as overridable (a config structure, or an `opaque` with a default). That serves every downstream
user.

The sibling `succinctlabs/riscv-lean` fork is only toolchain/dependency chores; it is pinned at
`d1d678c6`, the head of the open opencompl PR #59 ("chore: update to v4.32.2"). Repoint `lakefile.toml`
to opencompl once that merges and drop the fork outright.
