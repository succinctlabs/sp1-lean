---
name: lake-env-lean-silent-lies-on-stack-overflow
description: "`lake env lean <file>` exits 0 on Lean stack overflow; use `lake build <module>` for honest validation in this repo"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: c1d3b541-3a7d-4af5-a66d-5206bc5544f5
---

**Rule:** `lake env lean SP1Chips/Foo.lean` is **not reliable** for verifying that a file compiles. When Lean's elaborator hits an internal stack overflow ("Stack overflow detected. Aborting."), the lake wrapper still returns exit code 0, and grep checks for embedded errors (e.g. `grep -cE '^(error|warning):'`) miss the failure because Lean error lines start with the file path (`SP1Chips/Foo.lean:line:col: error:`), not with `error:`. Combined with the pre-existing `.lake/build/lib/lean/.../foo.olean` cache from before the edit, downstream `lake env lean` checks see the stale olean and report "success" on what is actually a broken file.

**Why:** discovered 2026-05-14 during DivRem _poly phase 1.2-1.4 work. Multiple successive "builds completed exit 0, no errors" reports for spec.divuw_poly / spec.remuw_poly / spec.divw_poly / spec.remw_poly / spec.div_poly / spec.rem_poly were all stack-overflow false-positives. A single `lake build SP1Chips.DivRemChip` exposed the truth: errors at line 1401 of DivuwRemuw.lean and similar elsewhere — the closer chains never actually closed.

**How to apply:** 
- For honest validation, run `lake build <Module>` (e.g. `lake build SP1Chips.DivRemChip`). It respects exit codes, surfaces dependency-graph failures, and uses ✔/✖ markers per module.
- If using `lake env lean <file>`, **always** also `tail -5` the log and look for `Stack overflow detected. Aborting.` AND `grep ': error:'` (the colon-prefixed form). Don't trust the exit code alone, don't trust an `error:`-anchored grep.
- The build cost of `lake build` is roughly the same as `lake env lean` if dependencies are cached (Lake's replay is fast). The extra confidence is worth it.
- Per-file `lake env lean` is fine for fast iteration during proof writing — just **always** finish with a `lake build` validation before claiming a phase done.
