---
name: DivRem.Constraints build cost
description: Realistic timing for `lake build SP1Chips.DivRem.Constraints` cycles — much higher than the CLAUDE.md "17–21 min" estimate suggests when upstream changes
type: reference
originSessionId: caa2556b-4a1f-4fb4-974c-e8f4426ced0c
---
`lake build SP1Chips.DivRem.Constraints` measured on 2026-05-09:

- **Warm cache, edit only inside DivRem.Constraints.lean**: ~20 min (1245s observed)
- **Cold or MulOperation.Constraints upstream churn**: ~42 min (2518s observed)

The plan file's "17–21 min" estimate is for the warm case; budget for ~40 min when iterating through upstream `_poly` shim additions because every edit to `SP1Operations/Operation/MulOperation/Constraints.lean` invalidates the DivRem.Constraints olean.

Practical implication: each iteration on `DivRem.Constraints` proof attempts costs ~20 min; do not fire off speculative builds. Use lean-lsp diagnostics for fast feedback when possible, but be aware the file's size (6700+ lines) often exceeds the LSP timeout.
