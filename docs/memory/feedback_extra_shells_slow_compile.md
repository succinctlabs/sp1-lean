---
name: Extra shells / lagging builds slow compilation on this machine
description: Background `lake build` / `lake env lean` processes left running compete for CPU + 6-15 GB RSS each. Always kill stale builds before starting new ones, and avoid keeping the lean LSP server alive when running heavy `lake build`s.
type: feedback
---

When running heavy `lake build` jobs (e.g., `SP1Chips.DivRem.Constraints` at
17+ min wall clock and 12-15 GB RSS), any lingering background processes from
prior builds significantly slow throughput on this machine. Specifically:

1. **Stale `lake build` / `lake env lean` processes** from killed Bash
   `run_in_background` jobs sometimes survive `pkill` if the parent shell
   died first; the lean child gets reparented to init and keeps running. Each
   one consumes 5-15 GB RSS and a full CPU core.
2. **The lean LSP server** (`lean --server` invoked by `uvx lean-lsp-mcp`)
   keeps a project-wide elaboration context warm in memory; even idle it
   holds several GB and competes for CPU when the project's elaboration
   touches the files it has open.

**Why:** This is a 16 GB / 8 core machine — with even one active build at
12 GB and the LSP at 5 GB, the system is in heavy memory pressure / swap.
Build wall clock can stretch from 17 min to 25+ min and tactic timing
becomes unpredictable.

**How to apply:** Before every `lake build`:

1. `ps aux | grep -E "lean|lake" | grep -v grep | grep -v lsp` — identify
   any active builds.
2. `pkill -f "lake env lean SP1Chips" ; pkill -f "lake build SP1Chips" ;
   pkill -f "lean SP1Chips/.*\.lean"` — kill any stragglers (each is safe;
   live builds you want to keep should be tracked by their PID).
3. Verify only the LSP server (PID stable across the day) and your active
   build remain.

If iterating heavily on a single file, prefer extracting it to a small
helper file that imports `SP1Chips.DivRem.Constraints` — once Constraints'
olean is cached (one 17-18 min build), the helper file can be rebuilt in
~3-4 min per iteration. (Note: extraction can hit subtle elaboration
differences for proofs that rely on specific in-file context; see
`feedback_divrem_core_port_blockers.md` for the 2026-05-08 attempt that
ran into `clear *-` / `set` interaction issues. For h_abs-style follow-up
work the more reliable strategy is to extract just the witness as its own
top-level lemma with explicit hypothesis arguments.)
