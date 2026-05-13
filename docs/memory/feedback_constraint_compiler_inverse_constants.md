---
name: hand-synced-inverse-constants-in-iff-rhs-desync-when-constraint-compiler-renormalizes
description: "If the iff RHS hand-references a numeric inverse constant (e.g. `2097414145` = inverse of 64 in Fin KB), a regen that switches the autogen to a symbolic form (e.g. `((64 : F)⁻¹)`) silently breaks the iff — simp can't unify the two forms and any `tauto` patch will spin forever"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 51ad6372-1698-413f-9547-eda28c134e63
---

When the SP1 constraint compiler changes how a multiplicative inverse is emitted (e.g. `64` was added to `KNOWN_BASES` on 2026-05-11, switching `2097414145 → ((64 : F)⁻¹)`), any hand-written `allHold_constraints_iff` RHS that mirrors the old literal must be hand-updated to match.

**Why:** `simp [constraints, sub_eq_zero]` unfolds the LHS using the new autogen form. If the RHS still has the old literal, the residue is a term-level `((... * ((64 : Fin KB)⁻¹)).val < 1024) ↔ ((... * 2097414145).val < 1024)` — propositionally true but syntactically unequal. Reaching for `tauto` papers over a real desync without ever closing: observed on 2026-05-11 with ShiftLeft.Constraints and ShiftRight.Constraints `tauto` calls spinning for 43+ minutes each before being killed. Replacing the stale literal in the iff RHS (and dropping `tauto`) brought elaboration to 21s/26s.

**How to apply:** After any `update_constraints.py` regen, grep the SP1Chips/ tree for hex/decimal multiplicative-inverse literals (`grep -rE '\* [0-9]{7,10}'`) and cross-check each against the corresponding autogen block. If the autogen now emits `((<base> : F)⁻¹)` but the hand-written iff still has the old decimal literal, replace the literal in the iff to match. The pre-regen full-build green status doesn't survive the renormalization — every iff that mirrored a constant is potentially affected.

Specifically: if you see a chip's iff close with `simp [constraints, ...]; tauto` and the build hangs on that file, the iff RHS is almost certainly out of sync with the autogen normalization, not a `tauto`-search depth issue. Fix the literal, drop `tauto`.

Related: [[feedback_build_concurrency]] (heavy `tauto` calls compound build wall-clock).
