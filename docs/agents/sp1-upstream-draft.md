# The SP1-side draft PR — prepared, NOT pushed

**Standing rule: nothing here gets pushed or filed without the owner's explicit approval.** The
branch described below exists **only in the local `../sp1` checkout**. Filing target is
`succinctlabs/sp1-private` (the internal repo), not public `succinctlabs/sp1`.

## The branch

`dtumad/lean-extraction-clean` — **5 commits based directly on the `v6.4.0` tag**, rebuilt from the
10-commit working series so each piece is born in its final shape (no test→bin→standalone churn, no
non-conventional `compiler:` prefixes). **Verified: `git diff dtumad/lean-extraction
dtumad/lean-extraction-clean` is empty** — identical trees, so the rebuild changed no content.

| # | commit | what |
|---|---|---|
| 1 | `feat(derive): IntoShape reflection metadata for core chip column structs` | derive extension + the 26 derive-line edits (imports/`#[derive]` only — no AIR equation, no populate) |
| 2 | `feat(hypercube): field-generic Lean emission in the constraint IR` | `F` instead of `Fin KB` at every emission site; the two-list assert/interaction split |
| 3 | `feat(compiler): whole-chip Lean extraction — column struct, asserts, interactions, manifest` | the extraction modes + the machine-shape manifest; never emits a circuit |
| 4 | `feat(compiler): deterministic per-chip trace batteries and the chip_traces CLI` | the conformance library (batteries + `generate_rows`) + thin CLI; `--elf` covers all 25 families |
| 5 | `test(compiler): witgen conformance check against Lean-verified witness generators` | the standalone opt-in package + vendored interpreter + `testdata/lean-witgen/` (+79k, generated) |

Verified at this branch: `cargo build -p sp1-constraint-compiler`, clippy 0 warnings, `cargo fmt
--check` clean, the conformance check passes **25/25**, and `cargo metadata` reports **no**
witgen/conformance workspace members (so `cargo build` / `cargo test --workspace` build and run
none of it).

## Base: `v6.4.0`, deliberately

`v6.4.0` is in `sp1-private`'s own history, so a branch based on it is a legitimate PR base there;
GitHub will diff against the merge base. **Do not rebase onto `sp1-private/main` before filing.**
Rebasing applies textually clean but does not build, and the reason is architectural rather than
mechanical: `sp1-private` has replaced the global-accumulation memory architecture with a
Merkle-tree one (9 `RiscvAir` chips removed, 5 added; 6 `InteractionKind` variants removed, 3
added). See `docs/agents/extraction.md` § "Upstream architecture drift". Our 25 instruction chips
are untouched by that change; the system/boundary tables are not. Raising this *in the PR
conversation* is more useful than silently rebasing over it.

## Filing (when approved)

```sh
cd ../sp1
git push private dtumad/lean-extraction-clean          # `private` remote = succinctlabs/sp1-private
gh pr create --draft --repo succinctlabs/sp1-private \
  --base main --head dtumad/lean-extraction-clean \
  --title "feat(compiler): Lean-verified witness-generation extraction and conformance check" \
  --body-file <this file's PR body section>
```

`pr_lint.yml` enforces Conventional Commit titles there, and the title above conforms. Their PR
template wants Motivation / Solution / PR Checklist; the body below is written to it.

---

## PR body

**Motivation**

There is a Lean 4 formal verification of SP1's Core RISC-V AIR (`succinctlabs/sp1-lean`): 25
instruction chips with machine-checked soundness against the RISC-V Sail specification, whole-chip
faithfulness proofs against SP1's own extracted constraint and interaction lists, and a
machine-level soundness theorem. Two things were missing to connect it to the prover:

1. the AIR had to be extracted from SP1 rather than transcribed by hand, and
2. nothing checked that SP1's *trace generation* agrees with the verified witness generators.

This branch adds both, with no effect on the prover, the workspace build, or CI.

**Solution**

Commits 1–3 are the extraction path: a derive extension so chip column structs report their own
layout, field-generic Lean emission in the constraint IR, and extraction modes that emit — per
table — the complete column structure, the ordered `assertZero` list, and the ordered interaction
list, plus a machine-shape manifest. Extraction never emits an executable circuit, so it cannot
manufacture the implementation the verification is supposed to be checking.

Commits 4–5 are the conformance path. A library module builds a deterministic executor-event
battery per chip (respecting the populate-path invariants: `clk ≡ 1 (mod 8)`, 24-bit timestamp
windows plus one deliberate cross-window access, `[2^16, 2^48)` addresses, exact RV64IM operand
semantics) and runs the chip's own `generate_trace`. The check then recovers each event row's
native inputs from the trace row itself through the verified symbolic row map, derives prover hints
from the actual events (opcode one-hots; the branch-taken bit computed exactly as `branch/trace.rs`
does), re-runs the exported witness programs with a small reference interpreter, and requires the
reconstructed row to equal the prover's row **cell for cell**, with every exported AIR constraint
evaluating to zero on it. All 25 chips pass in ~11s; corrupting one vendored cell fails with a
named chip, row, and column.

Witness generation is completeness-side — a wrong generator makes a prover fail, it can never make
a false proof verify — so this is a conformance oracle, not a trusted component.

**Zero CI footprint, by construction.** `conformance-check` is its own cargo workspace, excluded
from SP1's, as is the vendored interpreter it depends on. Nothing in `cargo build` or `cargo test
--workspace` builds or runs either; the check runs only when invoked explicitly. Promoting it into
CI is a deliberate later step once the artifact-sync protocol is agreed — the exit code is already
CI-shaped.

**Note on `testdata/lean-witgen/`** (+79k lines in commit 5): generated, deterministic, and
byte-stable — the exported witness programs, symbolic row maps, and manifests for all 25 chips,
plus a provenance sidecar naming the producing revisions. sp1-lean's `vendor_witgen_artifacts.sh`
regenerates and byte-checks it.

**Base note:** branched from `v6.4.0`. Rebasing onto current `main` is not mechanical — the
Merkle-tree memory redesign removes the `Global`/`MemoryGlobal*`/`PageProtGlobal*`/`Syscall*` tables
the extraction currently names, and changes six `InteractionKind` variants. The 25 instruction
chips are unaffected. Happy to do that rebase as a follow-up; it also tells the formal side exactly
which parts of its system-table work carry forward.

**PR Checklist**

- [x] Added Tests — the conformance check itself (25 chips), plus 19 unit tests in the interpreter
- [x] Added Documentation — module docs on every new file; the integration story is
      `docs/rust-integration-memo.md` in sp1-lean
- [x] Breaking changes — none. No runtime code path changes; all additions are behind
      out-of-workspace packages or extraction-only modes.
