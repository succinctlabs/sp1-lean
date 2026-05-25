# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this repo is

Formal verification in Lean 4 that SP1 Hypercube's AIR constraints correctly implement RISC-V. For each instruction, we prove a `correct_*` theorem stating that given the chip's constraints hold on a trace row and the initial `SailState` matches the row's register/memory reads, the SP1 operation produces the same `SailM ExecutionResult` as the Sail RISC-V spec.

## Build

- Full build: `lake build` (defaults to `SP1Operations` and `SP1Chips`).
- Single library: `lake build SP1Chips` / `lake build SP1Foundations` / `lake build SP1Operations`.
- Single file: `lake env lean SP1Chips/Add/AddChip.lean` (builds deps via cache, then elaborates the file).
- **Build concurrency.** `lake build` jobs on heavy chips (`SP1Chips.DivRem.Constraints` etc.) take 17–40 min and consume 5–15 GB RSS each. Before starting any new `lake build`, **either let the running build finish or kill it explicitly** (`pkill -f "lake build"` / `pkill -f "lake env lean SP1Chips"`). Hard cap: **2–3 builds at once, full stop** — never start a fourth speculative build. A `run_in_background` build whose parent shell died gets reparented to init and survives session boundaries; check with `ps -ef | grep -E "lake|lean" | grep -v lsp` before spawning a new one. See `docs/memory/feedback_extra_shells_slow_compile.md` for the why.
- Toolchain is pinned in `lean-toolchain` (`leanprover/lean4:v4.29.0`). Matching Mathlib pin (`v4.29.0`) is in `lakefile.toml`. The `Lean_RV64D` dep now tracks `opencompl/sail-riscv-lean` `main` (moved upstream from the old `succinctlabs/sail-riscv-lean @ sp1-lean-air-verification` fork during this PR). Sail v4 renamed/removed many v2 helpers — see `docs/LEAN_AND_SAIL_NOTES.md` for the full list and the new platform-read axioms (`update_elp_state_of_isInitialized`, `jump_to_of_mod4_eq_zero`, `jump_to_of_mask_mod4_eq_zero`). Common touchpoints: `bool_to_bits` → `bool_to_bit`, `bool_bits_forwards` → `bool_bit_forwards`; `shift_right_arith`, `check_misaligned`, `default_write_acc`, `force_pc_eq` are gone; `Sail.BitVec.toNatInt` now appears explicitly in goals — add it to the `simp [...]` list whenever you see `↑BitVec.toNat` residue.
- `--tstack=400000` and `synthInstance.maxHeartbeats = 1000000` are already set in `lakefile.toml` — some proofs legitimately need this. If you see instance-synth or stack failures, that's expected scale, not a bug to fix.
- There are no unit tests; correctness lives in the `correct_*` theorems themselves. "Test" = it elaborates.
- **`lake build` is considered "passing" only when both `^error:` and `^warning:` counts are zero** (`grep -cE '^(error|warning):' build.log`). The mathlib standard linter set is enabled via `weak.linter.mathlibStandardSet = true` and the repo has driven warnings to zero; a green build that emits new warnings is a regression. Common fix patterns used in the repo:
  - `show <goal>` used to reshape the actual elaboration target → `change <goal>`; `show X from Y` inside term-level `simp only [...]` is NOT a tactic and must stay `show`.
  - `set_option maxHeartbeats N in <decl>` requires a preceding `-- <why>` comment line *between* the `set_option` and the declaration (not before the `set_option`, not trailing on the same line — both forms interact badly with the `emptyLine` linter).
  - File-wide `set_option maxHeartbeats N` is preceded by a `set_option linter.style.setOption false` line on its own.
  - `. <tac>` bullets → `· <tac>` (U+00B7). Only at bullet position; never inside expressions like `Foo.bar`.
  - `2^N` → `2 ^ N` (mathlib spacing). `{ a b c : T }` → `{a b c : T}`.
  - Blank lines inside a `by ...` block or any `set_option ... in` wrapped command trigger `linter.style.emptyLine` — delete them.
  - Already disabled globally in `lakefile.toml`: `linter.flexible`, `linter.unusedSimpArgs`. Per-file disables for `linter.style.multiGoal` in 12 files with imbalanced-goal-tree proofs (DivRem/Constraints + DivRem/{Common,DivRem,DivuRemu,DivwRemw,DivuwRemuw}, ShiftRight/Constraints, ShiftLeft/Constraints, Mul/Constraints, MulOperation/Constraints, BitwiseU16Operation, LtOperationSigned). `linter.style.longLine` is enabled globally but every Lean source file with a hand-written `have h : T := by …` or large nested struct expression that doesn't wrap cleanly carries a file-level `set_option linter.style.longLine false` near the top (paired with `set_option linter.style.setOption false`). The 38 `Constraints.lean` files inherit the same pragma above the `section constraints` splice — `update_constraints.py` only edits between the markers, so the pragma survives regeneration.

## Architecture

Three libraries, strict dependency order `SP1Foundations → SP1Operations → SP1Chips`:

- **`SP1Foundations`** — the `SP1Constraint` / `AirInteraction` datatype (`Constraint.lean`), the KoalaBear field (`Field.lean`, abbreviated `KB`), `Word`/`BitVec` helpers, the `SailM` monad bridge to `LeanRV64D`, and shared tactics.
- **`SP1Operations`** — reusable constraint fragments: `Operation/*` (arithmetic: `Add`/`Addw`/`Sub`/`Subw`/`Mul`/`AddrAdd`/`Address`/`Bitwise`/`BitwiseU16`/`U16MSB`/`U16toU8{Safe,Unsafe}`), `Compare/*` (`IsZero`, `IsZeroWord`, `IsEqualWord`, `LtSigned`, `LtUnsigned`, `U16Compare`), `Reader/*` (instruction decoders: `RTypeReader`, `ITypeReader`, `ITypeReaderImmutable`, `JTypeReader`, `ALUTypeReader`, plus `CPUState` for clk/pc bookkeeping). `SP1Operations.lean` is the full import index.
- **`SP1Chips`** — one subdirectory per instruction chip. The top-level `<Chip>Chip.lean` contains `spec_*`, `sp1_*`, and `correct_*`; it imports `<Chip>/Constraints.lean`, which contains the auto-generated `constraints` function. Load and Store fan out: `Load/{LoadByte,LoadDouble,LoadHalf,LoadWord,LoadX0}/Constraints.lean` and `Store/{StoreByte,StoreDouble,StoreHalf,StoreWord}/Constraints.lean`, with matching top-level `Load<Width>Chip.lean` / `Store<Width>Chip.lean` (no top-level chip for `LoadX0` — constraints only). A single `<Chip>Chip.lean` may also prove several variants in one file (e.g. `BitwiseChip`, `BranchChip`, `DivRemChip` each bundle 6–7 `correct_*` theorems). `DivRem/` is further split for build-time tractability: `Constraints.lean` keeps just the autogen block plus the Fin KB / polymorphic `allHold_constraints_iff{,_poly}` lemmas; `Common.lean` holds shared helpers (`single_op`, `register_bounds`, `ops_U64_b_c`, `op_a_is_0`, `sp1_op_{a,b,c}`, auxiliaries, plus their `_poly` siblings); and each of `DivRem.lean` / `DivuRemu.lean` / `DivwRemw.lean` / `DivuwRemuw.lean` holds one opcode pair's bare lemma, `spec.<variant>` wrappers, and `_poly` core.

### The per-chip pattern

Read `SP1Chips/Add/AddChip.lean` + `SP1Chips/Add/Constraints.lean` as the canonical template. Every chip has:

1. `constraints : Vector (Fin KB) N → SP1ConstraintList` — a flat list combining `Operation`, `Reader`, `CPUState` sub-constraint lists plus a trailing `assertZero` for the `is_real * (is_real - 1)` gate. Marked `@[irreducible]`; unfold with `simp [constraints]` at the start of proofs.
2. `sp1_op_a / sp1_op_b / sp1_op_c` — register-index projections from the `Main` row vector.
3. `spec_<op> : ... → SailM ExecutionResult` — advances `nextPC` then calls the appropriate `execute_*` from Sail.
4. `sp1_<op> : SailM ExecutionResult` — the SP1 implementation: writes `nextPC` and result register from `Main` columns.
5. `correct_<op>` — the equivalence theorem, stated as `(spec_<op> ...).run s = (sp1_<op> Main).run s` under:
   - `h_cstrs : (constraints Main).allHold` (propositional constraints)
   - `state_cstrs : (constraints Main).initialState s` (register/memory reads agree with `s`)
   - `h_is_real : Main[N-1] = 1` (the last column is the is-real flag)

The proof skeleton is: unfold `constraints`, destructure the conjunction, specialize the `CPUState`/Reader `allHold_constraints_iff_is_real` lemmas, extract initial-state facts, then rewrite the monadic forms via `simp [spec_*, sp1_*, execute, execute_<TYPE>']` and close with arithmetic lemmas from the corresponding `Operation`.

Most chips ship a `<Chip>/Common.lean` with a polymorphic `allHold_constraints_iff` that splits the flat constraint list into sub-`.allHold` conjuncts. **For ALU chips, the canonical shape going forward is the one used in `SP1Chips/Add/Common.lean` — both sides of the iff in `.allHold` form (not `List.Forall SP1Constraint.toProp`), so the matching SP1Clean Layer-2 `allHold_iff_structural` (see `SP1Clean/AddChip/Lemmas.lean`) collapses to a flat `rw` chain.** Existing chip Commons (Sub, Addi, etc.) still use the older `List.Forall` form — migrate opportunistically. See `docs/CLEAN_PILOT_ROADMAP.md` §4 "Canonical ALU-chip Layer-0/Layer-2 shape" for the full template and the two literal-elaboration caveats it carries.

### Constraints datatype

`SP1Constraint` is `assertZero (x : Fin KB) | send interaction mult | receive interaction mult`. `toProp` turns propositional constraints (arithmetic, lookup multiplicities) into `Prop`; `toStateProp s` turns interactions about initial register/memory state into facts about a `SailState`. A chip's constraint list has both layers, so proofs consume both `h_cstrs.allHold` and `state_cstrs.initialState s`.

## Regenerated code — do not hand-edit

The body of every `constraints` definition between `section constraints` and `end constraints` markers is auto-generated by `update_constraints.py`, which shells out to `cargo run -p sp1-constraint-compiler` in an external SP1 checkout (path in the `SP1_DIR` env var) and splices the Lean output back in. If you need to change the constraint layout, regenerate — don't patch. Everything outside those markers (spec/sp1/correct, helper lemmas) is hand-written and fair game.

**Never edit `Main[k]` indices, opcode literals, or any other content inside `section constraints ... end constraints`.** This block reflects the constraint compiler's current output verbatim. If indices in this block look wrong, the right fix is to re-run `SP1_DIR=… python3 update_constraints.py` (you can run this yourself), then update the *hand-written* helpers (iff lemma RHS, `set` aliases, `is_real`, `sp1_op_*` defs, etc.) to match. Hand-editing the generated block silently desyncs it from the SP1 source of truth and any later regeneration will overwrite the changes — exactly the failure mode that occurred when the iff RHS, `set` aliases, and the constraints def all went out of sync after a manual `−1` shift was applied across the whole file.

## docs/ pointers

Topical guides live in `docs/`. See `docs/README.md` for the index. Skim the relevant one when you hit a matching surface:

- `docs/LEAN_AND_SAIL_NOTES.md` — Lean 4.29 quirks (instance priority, `simp_all` regression, `BitVec.ofNat` ordering) plus the Sail v4 rename/removal table and new platform-read axioms. Ends with a "what to look for on the next upgrade" rubric.
- `docs/CONSTRAINT_REGEN.md` — playbook to follow the next time the constraint compiler adds or drops a column. Reusable across "is_trusted"-style cascades. Includes the Fin-KB deletion-sweep template used after `_poly` migrations.
- `docs/FIELD_GENERIC.md` — current state of the field-genericization effort, polymorphic proof patterns, KB-specific literal blockers, the DivRem worked example, and the recipe for instantiating at a different prime field (e.g. BabyBear). Includes the compressed timeline + decisions log.
- `docs/PROOF_PATTERNS.md` — performance wins, tactic anti-patterns (`nlinarith` past ~4 limbs, `simp_all` leakage, etc.), kernel + elaboration landmines (deep recursion on `2^N`, `bitVec_sshiftright_eq` normalization), and build-validation gotchas (`lake env lean` silent-success bug). Add new entries when a landmine takes more than an hour to diagnose.

## Constraint-shape cascades

If the SP1 constraint compiler ever adds or drops a column, follow `docs/CONSTRAINT_REGEN.md` for the regen + index-shift + iff-lemma update sequence.

## Custom tactics (`SP1Foundations/Tactics.lean`)

- `get_elem_tactic` is rebound to `norm_num1` — array/vector indexing side conditions are discharged numerically rather than by `decide`, which matters for the large `Vector (Fin KB) N` row terms (N is chip-specific: 31 for Addi, 34 for Add, 37 for Addw, 46 for Branch, 52 for Bitwise, up to 247 for DivRem).
- `bv_amicus_kerneli [w N] [at loc]` is a kernel-friendly normalization pass for `BitVec`s (default width 64). Use it instead of heavy `bv_decide`/`decide` when you need to push toward `Nat` arithmetic without exploding the kernel.

## Proof-style notes

- `simp_all` in this repo can leak into unrelated hypotheses; commit `419ee1d` ("temp patch for leaky simp_all") is an active workaround. Prefer targeted `simp [...] at h` over `simp_all` when practical, and be suspicious if a `simp_all` closes more than you expect.
- `aesop`, `omega`, and `norm_num` are the standard closers for side conditions (bounds, field arithmetic, 32/65536 comparisons). `KoalaBear.*` lemmas handle carry/overflow into the PC.
- Main vector elements are `Fin KB` — when reasoning about them as `Nat`s you usually need the `.val < KB` bound; `aesop` typically finds it from context.
- The `is_real` column (last index of `Main`) gates most reader/CPU-state lemmas via `allHold_constraints_iff_is_real`; most proofs `rw [h_is_real] at *` early.
- `bv_decide` (Lean 4.29) silently chokes on `↑↑` (the `ℕ → Fin KB → ℕ` round-trip introduced when a literal of `ℕ` flows into a `Vector (Fin KB) n` slot). The symptom is "potentially spurious counterexample" with `BitVec.ofNat 128 ↑↑(...).toNat` listed as opaque variables. Strip the cast first with `Fin.val_cast_of_lt` (when you can prove the value `< KB`, e.g. byte slices are `< 256`), then call `bv_decide`. See `byte_decomp_128` in `SP1Foundations/Word.lean` for the canonical fix.
- `simp` on `BitVec.setWidth (BitVec.extractLsb …)` normalizes to `BitVec.ofNat _ (… .toNat >>> _)` form — the LHS that `bitVec_sshiftright_eq` literally produces. Code that does `simp [bitVec_sshiftright_eq]` then later `apply bitVec_sshiftright_eq` will fail at the apply because the simp normalized away the syntactic match. Either rewrite once and close with the unfolded equation (see `exec_RTYPEW_pure_bv_to_w`'s SRAW case in `SP1Foundations/SailM.lean`), or `simp [BitVec.extractLsb, BitVec.setWidth_eq, BitVec.extractLsb', BitVec.toNat_setWidth]` to match the new normal form.
- `DecidableEq` synthesis for `regidx` (defined in `LeanRV64D.Defs`) used to close with `by simp; infer_instance` since the inner type `BitVec (if false then 4 else 5)` reduces to `BitVec 5`. In 4.29 that path no longer finds the instance; use `decidable_of_iff (v = v') (by simp)` instead (see `SP1Foundations/Register.lean:32`).
- `simp_all` no longer derives `Main[i] = 1` from a long conjunction of disjuncts in 4.29, even when one of them is `(... ∨ -1 = 0)` (which is False in `Fin KB`). The brittle pattern `have h : Main[i] = 1 := by simp_all [sub_eq_zero]` now leaves an unsolved goal. Replace with direct conjunction projection: `(h_cstrs.2.2…1).resolve_right (by decide)` then `omega`/`sub_eq_zero` to recover the equation. See `op_a_lt32_of_constraints` in `SP1Chips/Jal/JalChip.lean` for the canonical pattern.

## MCP servers

`.mcp.json` declares `lean-lsp` (live goal/tactic state from the Lean LSP). It launches via `uvx`, so `uv` must be on `PATH` — if it's missing, install with `curl -LsSf https://astral.sh/uv/install.sh | sh` (puts `uv`/`uvx` in `~/.local/bin`). Local enable/disable is in `.claude/settings.local.json` (gitignored; `enableAllProjectMcpServers: true` opts this project in). Restart Claude Code after installing or toggling. (An earlier `LeanExplore` server was dropped from `.mcp.json`; if you need Mathlib semantic search, add it back locally.)
