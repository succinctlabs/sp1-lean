# The Sail fork delta — the exact `succinctlabs/sail-riscv-lean` changes, and how to drop them

**Purpose (task K1).** We pin `LeanRV64D` (sail-riscv-lean) to the `succinctlabs @ dtumad/clean-native`
fork. The fork's *semantic* delta over upstream `opencompl/sail-riscv-lean` is **three config lines in
two files** (plus a `lean-toolchain` pin). This doc records them exactly so the delta can be
(a) re-applied mechanically against any future base (e.g. the Lean 4.30 regen), or (b) retired entirely
once opencompl accepts build-time platform-config parameterization (task K3). See the consolidation
proposal §7.5 for the disposition and `lean-sail-notes.md` for the surrounding dep environment.

## The delta (SP1 platform config)

The fork flips three RISC-V platform constants to match SP1's execution platform (no CLINT timer, no
signature dump, no PMP entries). Line numbers are against the **opencompl upstream baseline** and drift
whenever the model is regenerated — match on the `def` name, not the line.

| File | `def` (upstream value) | Fork value | Meaning |
|------|------------------------|------------|---------|
| `LeanRV64D/PlatformConfig.lean` (~L11006) | `plat_have_clint : Bool := true` | `false` | CLINT (core-local interrupt timer) off — SP1 has no timer device |
| `LeanRV64D/PlatformConfig.lean` (~L11012) | `plat_have_sig : Bool := true` | `false` | Signature output off — SP1 has no test-signature region |
| `LeanRV64D/PmpRegs.lean` (~L219) | `sys_pmp_count : Int := 16` | `0` | No physical-memory-protection entries — SP1 runs unprotected M-mode |

Plus: the fork's `lean-toolchain` is pinned to the project toolchain (`leanprover/lean4:v4.28.0`)
rather than upstream's (currently v4.29.0 on opencompl `main`).

Downstream consumers of these constants (unmodified, listed for review): `Platform.lean` guards on
`plat_have_clint`; `SysControl.lean`/`PmpControl.lean` guard on `sys_pmp_count`; `plat_sig_base`/
`plat_sig_size` sit next to `plat_have_sig` in `PlatformConfig.lean`.

## Re-applying against a new base (the 4.30 regen — task K4)

opencompl regenerates the model *daily*, so any re-pin is a proof-churn event against the
symbolically-reduced generated internals regardless of the fork. To re-apply:

1. Check out the target opencompl `sail-riscv-lean` commit (fresh copy at `../sail-riscv-lean`).
2. Set the three `def`s above to the fork values (grep by name; ignore line drift).
3. Set `lean-toolchain` to the project toolchain.
4. Regenerate/verify LeanRV64D builds; expect proof-churn in the SP1 decode-reduction lemmas that
   pattern-match generated internals.

## Dropping the fork (task K3 — the real fix)

The C backend already exposes these as *runtime* config; the Lean backend hardcodes them as `def`s
that admit no project-side override. The upstream ask: have opencompl's Lean backend emit the platform
config as overridable (a config structure / `opaque` with a default, or a generation-time flag). That
serves every downstream user and lets us drop the `sail-riscv-lean` fork to a plain opencompl pin. Until
then the fork is a rebase-thin 3-line branch (near-zero carrying cost).

The sibling `succinctlabs/riscv-lean` fork (task K2) is only toolchain/dep chores and is *ahead* of
opencompl `main` (stale on `nightly-2026-01-22`) — PR the chores upstream and drop that fork outright.
