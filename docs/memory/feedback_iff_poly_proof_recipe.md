---
name: Fin KB iff_constraints recipe transports to _poly, but trim trailing intros+repeat congr!
description: The Fin KB `simp + iterate rw eq_comm + intros + repeat congr!` recipe DOES transport to `_poly` if you drop the trailing intros+repeat (over-closes; the simp + 2× iter rw + rw + simp tail already closes)
type: feedback
originSessionId: caa2556b-4a1f-4fb4-974c-e8f4426ced0c
---
When porting an `allHold_constraints_iff` lemma from Fin KB to `_poly`, the Fin KB recipe IS the right approach — but stop after the 5th tactic, not 7th.

**Why:** observed on 2026-05-11 closing `DivRem.allHold_constraints_iff_poly`. The earlier prognosis (2026-05-09 memory) was wrong — the recipe transports cleanly, but the prior session's failure mode ("no goals" at line 1322) was misread as "stuck" when in fact it meant the first 5 tactics already closed the goal and the trailing 2 lines were running on an empty proof state.

**Correct recipe** (verified on `DivRem.allHold_constraints_iff_poly`, 246-column row, 105s build):

```
simp [constraints, sub_eq_zero, and_assoc]
iterate 3 rw [eq_comm (a := _ * (Main[201] + Main[203] + Main[205] + Main[206]))]
iterate 3 rw [eq_comm (a := (1 : ZMod p))]
rw [eq_comm (a := _ * _) (b := Main[245])]
simp [neg_eq_zero]
```

The Fin KB version's trailing `intros; repeat (congr! ...; exact neg_eq_zero)` is dead code at `_poly`; remove it.

**How to apply:** when porting a chip's `allHold_constraints_iff_*` to `_poly`, copy the Fin KB recipe verbatim, swap `(1 : Fin KB)` → `(1 : ZMod p)`, and TRIM the trailing closer. If you see "no goals to be solved" at tactic N, count: tactics 1..N-1 already closed everything. The 5-tactic prefix is the minimal closer for the 246-column DivRem layout.
