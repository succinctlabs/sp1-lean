# Upstream drafts — prepared, NOT posted

**Standing rule: nothing here gets filed without the owner's explicit approval.** Filing state and
the queue live in `clean-upstream.md`; the reasoning behind *what* we file lives in its
"Clean's direction (2026-08)" section, which this file assumes.

**What changed on 2026-08-19.** The U1/`AgreesBelow` drafts that used to live here are gone: that
PR is **filed as [#450](https://github.com/Verified-zkEVM/clean/pull/450), approved, and pending
merge**. And the witgen-sharing pitch was rewritten after reading the maintainer's live branch:
upstream is retiring the JSON *interpreter* (#446) while keeping the witness IR and building a
Lean-emits-Rust codegen path that renders each `Witgen.Step` one-for-one as a Rust `let` — with no
CSE anywhere. So the pass is pitched on **generated-Rust size and speed**, the wire-format doc
rider is withdrawn, and the #404 interpreter offer is withdrawn.

---

## Draft 1 — comment on PR #450 (nudge)

> This is approved and mergeable; happy to rebase whenever it is convenient.
>
> Two notes to make #426's life easier whichever way this goes:
>
> - **Conjunct order differs.** #426 defines `AgreesBelow` as `(∀ i < n, …) ∧ hint ∧ data`; this PR
>   has `… ∧ data ∧ hint`. Whichever lands second is a two-conjunct swap. This PR also adds the
>   `.get_eq` / `.data_eq` / `.hint_eq` accessors and `agreesBelow_rfl`, and leaves `AgreesBelow`
>   opaque rather than unfolding it under `circuit_norm`/`grind` — happy to drop either if #426's
>   shape is preferred.
> - **`Clean/Examples/DataWitness.lean` is only here.** It carries
>   `not_computable_from_cells_alone`, which *proves* the old obligation was false for any generator
>   reading `hintGet`/`dataGet` — not merely awkward. That example seems worth keeping in the tree
>   independently of which PR carries the definitional change.

---

## Draft 2 — PR: `WitgenIR.share` (subterm sharing), rebased onto the codegen line

**Target:** `dtumad/clean:witgen-share-rebased` → `Verified-zkEVM/clean:agent/fixed-columns-prover-data`
(re-target `main` if #446 lands first). **Draft.** Record the exact base sha in the body.

**Title:** `Witgen IR: intern shared subterms as let-steps, with proven eval-preservation`

**Body sketch** (final text written when the rebase is done, since the numbers below must be
regenerated against their IR):

> Witness programs are authored as deeply shared Lean terms, but nothing in the pipeline preserves
> that sharing: `Lower.lean` passes `steps`/`output` through verbatim and `Rust.lean` prints every
> other node as a tree, so a subterm occurring *n* times is emitted *n* times and evaluated *n*
> times at prove time. `stepsToRust` already renders each `Witgen.Step` as `let local_N: F = …`, so
> the fix is a pass that *creates* those steps.
>
> This adds `WitgenIR.share`: bottom-up hash-consing that interns every distinct non-trivial
> `FExpr`/`U64Expr` node as a `let`-step referenced by `localVar`, with
>
> ```
> theorem WitgenIR.eval_share (ir : WitgenIR F m) (env : ProverEnvironment F) :
>     ir.share.eval env = ir.eval env
> ```
>
> axiom-clean (`[propext, Classical.choice, Quot.sound]`). The memo is an **untrusted cache** — hits
> are re-verified by `beq` against the steps array — so the proof never reasons about `Std.HashMap`
> internals. `BExpr` (no step sort) is recursed through; `mapRange` bodies are reference-remapped
> only, since they re-bind `idx`; original steps are themselves shared and renumbered, with
> references that were already dead under the total semantics replaced by `const 0`.
>
> **Evidence.** [To regenerate against this branch: generated-Rust line count and prover wall-clock
> on a duplication-heavy gadget from the tree, before/after.] From the downstream project that
> motivated it (a Lean verification of SP1's RISC-V AIR, 25 chips on Clean): the DivRem chip's
> witness programs expand to **1.22 GB** serialized without sharing and **1.04 MB** with it
> (~1143×); Mul 1.86 MB → 201 KB.
>
> **Integration.** `share` is called in `Lower.lean`'s `lowerWitness` before the existing
> `witnessProgramWellFormed` check, which then simply re-runs on the shared program — so the
> integration adds no new proof obligation, and `WitnessBlock.wellFormed` is re-established by the
> same decidable check as before.
>
> **Placement question for review:** the pass is a `WitgenIR → WitgenIR` transformation whose proof
> is about IR semantics, so it currently sits in `Clean/Circuit/` next to the IR. If you would
> rather keep optimization out of the core library, it moves to `Clean/Air/Extraction/` over
> `WitnessBlock` — happy either way.
>
> Also relevant to `doc/witgen-authoring.md`'s note about sharing behind an opaque program prefix
> ("the signal to add a locals-boundedness lawfulness class"): a post-hoc pass sidesteps that
> entirely, since it runs after the proofs are done.

**Rebase work this PR requires** (tracked in `clean-upstream.md` U11): the three new `FExpr`
constructors (`.index`, `.listGetAtIndex`, `.proverInputGet`) through `shareF`/`remapF`/`beq`/
`hashCode` and their spec cases; `evalSteps`'s new `idx`/`proverInput` parameters through the step
lemmas and `eval_share`; and a sound answer to the `idx` question for `RowProgram`s (whose steps
evaluate at `idx := row`, unlike `WitgenIR`'s `idx = 0`).

---

## Held deliberately (recorded so it is a decision, not an oversight)

- **`doc/witgen-wire-format.md`** — stays in this repo. Upstream keeps `WitnessExport.lean` as a
  diagnostic ("JSON may remain as an optional diagnostic or build-time manifest, but it must not be
  the runtime constraint evaluator"), and every Rust consumer of that JSON was deleted in #446.
  Specifying it upstream would promote a debug printer to a versioned external interface.
- **`rust/witgen-interp` as an answer to #404** — stays ours. #404 has had 0 comments since
  2026-06-11 and its instructions reference `tests/helpers/lean_runner.rs`, which #446 deletes.
  The copy-of-record is the SP1-vendored copy.
- **`ToClean/Circuit/WitgenBridge`** — never file; #426 falsifies its premise. Retire locally at
  the pin bump.
- **`ToClean/Circuit/WitgenEval`** — only the `gateFE`/`iteFE` half is file-able, and only after
  #426 (which renames `ofFExprs` → `ofCompositeFExpr`). The rest is superseded by #448.
- **`ToClean/Circuit/WitnessCombinator`** — file the one-attribute `size_fields` ask instead, and
  only after reproducing a stall (U10).

## Notes for the owner

- Cross-fork filing:
  `gh pr create --draft --repo Verified-zkEVM/clean --head dtumad:<branch> --base <base>`.
- Never force-push or delete `sp1-integration` (Lake pin reachability).
- After U11 merges upstream: re-pin per `clean-upstream.md`'s exit condition, switch
  `scripts/witgenExport.lean` to `open scoped Witgen` (dropping its local `Hashable` instance), and
  plan the #426/#448/#451 migration recorded in "Clean's direction".
