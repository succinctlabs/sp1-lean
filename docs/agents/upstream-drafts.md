# Upstream drafts — prepared, NOT posted

**Standing rule: nothing here gets filed without the owner's explicit approval.** This file
brings the Clean-side package to one-command readiness; the branches are pushed to the fork
(`dtumad/clean`) only. Filing state and the queue live in `clean-upstream.md` (U11, U1).

The prepared branch: `dtumad/clean@witgen-share`, **4 commits** off upstream base `0e53b9f2`
(no AgreesBelow contamination):

| commit | content |
|---|---|
| `410ffba8` | `WitgenIR.share` — intern distinct subterms as let-steps |
| `4a9c2c7b` | prove eval-preservation of `WitgenIR.share` |
| `86f35a74` | scoped canonical-value `Hashable` instance (`Witgen.instHashableOfVal`) so `witgenJsonShared?` is callable stock |
| `d8a2dc36` | `doc/witgen-wire-format.md` — the wire-format spec (upstream has none; also fixes `witgen-authoring.md`'s dangling design-history pointer) |

---

## Draft 1 — issue on Verified-zkEVM/clean

**Title:** Witgen serialization expands shared subterms — production-scale programs need a sharing pass

**Body:**

The witgen wire format supports sharing — a program is `steps` (let-bindings) referenced
by `localVar`, so serialized programs can be DAGs — but nothing *produces* steps from a
tree-shaped payload: authored programs naturally build deeply shared Lean terms, and
`WitgenIR.toJson?` expands every shared subterm into a fresh copy.

On the gadgets in this repo the effect is invisible. On production-scale witnesses it is
not. Data point from formally verifying SP1's RISC-V chips on Clean (sp1-lean): the
64-bit DivRem chip's witness programs — whose `c · quotient` block and carry chain
reference the same 128-bit product machinery at every limb — serialize to **1.22 GB** of
JSON (two single witness ops at 552 MB each) for an authoring DAG of a few thousand
nodes. A Rust interpreter (#404) evaluating the unshared tree would pay the same blowup
at evaluation time, so this bites exactly the consumer the export exists for.

We wrote the missing pass and would be happy to PR it: `WitgenIR.share`, a bottom-up
hash-consing rebuild that interns every distinct non-trivial `FExpr`/`U64Expr` node as a
`let`-step (BExpr has no step sort and is recursed through; `mapRange` bodies re-bind
`idx` and are reference-remapped only; original steps are themselves shared and
renumbered). It comes with the eval-preservation theorem

```
theorem WitgenIR.eval_share (ir : WitgenIR F m) (env : ProverEnvironment F) :
    ir.share.eval env = ir.eval env
```

axiom-clean (`[propext, Classical.choice, Quot.sound]`), so a serializer can apply it
unconditionally (`Operations.witgenJsonShared?`). With the pass, the DivRem payload is
1.04 MB (1143×), and interpreter evaluation cost becomes proportional to distinct
subterms. The proof also caught a genuine subtlety worth recording: an original
`.letU .idx` step (value 0, steps evaluate at `idx = 0`) must not be substituted
symbolically into a `mapRange` body, which re-binds `idx` — the pass rewrites `.idx` to
`.const 0` in shared positions.

Downstream validation: we run a self-contained Rust reference interpreter of the wire
format (one dependency, no SP1 types) over the shared exports of all 25 SP1 chips —
~857 fixture rows reproduce the Lean reference evaluation exactly, including full-trace-
row reconstruction against SP1's real `generate_trace` output and per-row checks that
every serialized `assert` evaluates to zero. Relevant to #404: we would be glad to
contribute that interpreter as the format's reference implementation.

Branch: `dtumad/clean@witgen-share` (4 commits on top of `0e53b9f2`).

---

## Draft 2 — PR from dtumad/clean:witgen-share → Verified-zkEVM/clean:main

**Title:** Witgen IR: `WitgenIR.share` — intern distinct subterms as let-steps, with proven eval-preservation

**Body:**

Closes the serialization-size gap described in <issue link>: the wire format has
`steps`/`localVar` sharing but nothing produced it, so shared subterms serialize (and
would evaluate externally, cf. #404) as full copies — 1.22 GB for SP1's DivRem witness
programs; 1.04 MB with this pass.

**What's here**

- `Clean/Circuit/WitnessShare.lean` —
  - `WitgenIR.share`: bottom-up hash-consing; every distinct non-trivial
    `FExpr`/`U64Expr` node becomes a `let`-step referenced by `localVar`. `BExpr` (no
    step sort) is recursed through; `mapRange` bodies are reference-remapped only
    (they re-bind `idx`); original steps are shared and renumbered, with dead
    references (out of range / wrong sort — both `0` under the total semantics)
    replaced by `const 0`; `.idx` in shared positions becomes `.const 0` (steps
    evaluate at `idx = 0`; keeping it symbolic would re-bind under `mapRange` — a bug
    the proof caught).
  - `WitgenIR.eval_share : ir.share.eval env = ir.eval env` — axiom-clean. The memo is
    an untrusted cache (hits re-verified by `beq` against the steps array), so the
    proof never reasons about `Std.HashMap` internals.
  - Hand-written `beq`/`hashCode` for the three scalar sorts (the deriving handlers do
    not apply to this mutual + nested block) with `beq_eq` soundness.
  - `Witgen.instHashableOfVal` — a **scoped** canonical-value `Hashable` for any
    `FiniteField`, so `witgenJsonShared?` is callable without a consumer-side
    instance (scoped to never shadow a type-specific instance downstream).
- `Clean/Circuit/WitnessExport.lean` — `Operations.witgenJsonShared?` (applies the pass
  per witness op at serialization) plus a behavior-preserving factoring of
  `witgenJson?` through `FlatOperation.witgenJsonList?`. Existing golden tests are
  unchanged and pass.
- `doc/witgen-wire-format.md` — the serialized contract had no spec
  (`doc/witgen-authoring.md` covers the authoring surface only): the envelope, the four
  operation forms, the per-sort tag tables (including the three wire tags that differ
  from the Lean constructor names), the total-evaluation semantics, the evaluation
  loop, and sharing. Written against the serializer as normative; also repoints
  `witgen-authoring.md`'s dangling `witgen-ir-plan.md` reference.

**Numbers** (SP1's 25 RISC-V chips, KoalaBear): DivRem 1.22 GB → 1.04 MB; Mul 1.86 MB →
201 KB; full 25-chip export ~2.5 MB total (programs + row maps + manifests); output
byte-stable across regenerations. Validated end-to-end by a self-contained Rust
reference interpreter over ~857 fixture rows, including full SP1 trace-row
reconstruction and per-row constraint checks.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

---

## Notes for the owner

- Filing is: file the issue first, then
  `gh pr create --repo Verified-zkEVM/clean --head dtumad:witgen-share ...` with the
  issue linked — or fold the issue text into the PR body if you prefer one artifact.
- Mentioning #404 connects it to their open request for a Rust interpreter; the
  interpreter offer (its differential is green across all 25 chips) is written into
  both drafts. Check #404's live state before posting — nothing about it is recorded
  here beyond the branch-map note.
- The reader-facing integration story (what SP1 gains, the inversion plan) is
  `docs/rust-integration-memo.md`; it can accompany any SP1-side conversation.
- U1 (`agreesbelow-data-hint`, 2 commits) remains a separate prepared PR — orthogonal
  to this one, file in either order.
- After U11 merges upstream: re-pin per `clean-upstream.md`'s exit condition, switch
  `scripts/witgenExport.lean` to `open scoped Witgen` (dropping its local `Hashable`
  instance), and repoint `docs/witgen-wire-format.md`'s normative-source paragraph at
  upstream.
