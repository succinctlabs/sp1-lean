---
name: never-spawn-a-lake-build-while-another-is-running
description: "lake build on this repo takes 17-40 min and uses 5-15 GB RSS per process; running ≥2 concurrently degrades wall clock superlinearly and contributed to a session crash on 2026-05-11. Cap is 2-3 concurrent builds, and that's an upper bound not a target."
metadata: 
  node_type: memory
  type: feedback
  originSessionId: d4968a37-de55-4bfa-8be8-6d2398c19757
---

When iterating on Lean changes, do not start a new `lake build` until
the previous one either finished or has been killed. Each build is
5–15 GB RSS / one full core; on a 16 GB / 8 core machine, two
overlapping builds put the system into swap and wall-clock per
iteration goes from 17 min → 25–40 min.

**Why:** prior session (2026-05-11) ran 4+ `lake build`s concurrently
during the `is_trusted` cascade sync and crashed the machine before
the work could be verified green. There is no upside to keeping a
stale build alive while editing — its olean output is invalidated by
the edit anyway.

**How to apply:** Before any `lake build` / `lake env lean SP1Chips/...`
invocation:

1. `ps -ef | grep -E "lake|lean" | grep -v lsp | grep -v grep` — list
   live builds (the lean-lsp-mcp process is fine; ignore it).
2. If a build for the file you care about is already running, **wait
   for it** — use `ScheduleWakeup` / `Monitor` / `Bash run_in_background`
   with completion notification. Do not race it.
3. If a stale build is running but irrelevant, kill it explicitly
   (`pkill -f "lake build SP1Chips"` or by PID) before starting the
   new one.
4. Cap concurrent builds at **2–3 total** (including any
   lean-lsp-mcp compilation passes). That's a hard ceiling, not a goal —
   most of the time, **one** is right.

Pairs with [[project_is_trusted_readd_cascade]] (the cascade whose
unverified state this rule was learned from) and the in-repo
`docs/memory/feedback_extra_shells_slow_compile.md` (longer-form
discussion + per-process RSS figures).
