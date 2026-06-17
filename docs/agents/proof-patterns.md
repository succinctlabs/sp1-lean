# Proof patterns & landmines

Concrete, build-verified patterns for the witnessed-`FormalCircuit` gadgets in `Operations/`.
Reference templates: `AddOperation.lean` (carry chain), `IsZeroOperation.lean` (tiny witness
gadget), `BitwiseU16Operation.lean` (byte/opcode), `IsZeroWordOperation.lean` (composed subcircuits).

## The witnessed-`FormalCircuit` recipe

Each `Operations/<Op>.lean` exposes, in order:

1. **`RawSpec`** — the literal meaning of SP1's extracted constraint list at `is_real = 1` (carry-bool +
   range form, or per-byte form, or a composition of sub-gadget `RawSpec`s). Anchored to the extracted
   constraints in `Faithful/<Op>.lean`.
2. **`Assumptions`** — operand preconditions (`Word.isU64`, limb `< 2^16`, opcode booleanity, …).
3. **`Spec`** — *semantic*, e.g. `Word.toBitVec64 value = …` or an `if … then 1 else 0` indicator.
4. **a core lemma** (`<sem>_of_<raw>` / `<raw>_of_<sem>`) re-deriving `RawSpec ↔ Spec` natively.
5. **`main`** — witness the result columns, range-check them, assert the constraints (or
   `subcircuit <Sub>.circuit` for composition).
6. **`elaborated : ElaboratedCircuit`** — `localLength` + the `*_eq`/`subcircuitsConsistent`/
   `channelsLawful` obligations.
7. **`soundness` / `completeness`** — `circuit_proof_start` first, then wire `h_holds`/`h_env` to the
   core lemma.
8. **`circuit : FormalCircuit`** — bundle.

After each: confirm `#print axioms` (or the `lean_verify` MCP tool) shows only
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

## Discharging the `elaborated` obligations for a composed `main`

When `main` uses `subcircuit <Sub>.circuit …` (e.g. `IsZeroWordOperation` composing four
`IsZeroOperation`s), discharge the obligations with the sub-circuit's own `circuit`/`elaborated`
unfolded:

```lean
localLength_eq := by
  simp +arith [circuit_norm, main, <Sub>.circuit, <Sub>.elaborated]
subcircuitsConsistent := by
  simp only [circuit_norm, main, <Sub>.circuit, <Sub>.elaborated]
  try omega          -- closes the `offset + k = k + offset` residue
channelsLawful := by
  simp [circuit_norm, main, <Sub>.circuit, <Sub>.elaborated]
```

A flat compose of several sub-circuits discharges fine this way — there is no "elaboration wall" for
the Operations layer (that wall is a chip-layer phenomenon; see the memory note).

## Soundness / completeness wiring for a composed gadget

- **Soundness.** `h_holds` hands you, per sub-circuit, `<Sub>.Assumptions (eval x) → <Sub>.Spec (eval x) <subcols>`.
  Apply each with `trivial` when its `Assumptions = True`, `simp only [<Sub>.circuit, <Sub>.Spec, …] at`
  to expose the sub-Spec, then feed the core lemma. The goal carries trailing
  `channelsWithRequirements = [] ∨ <Sub>.Assumptions …` conjuncts — discharge each with `Or.inr trivial`.
- **Completeness.** `h_env` gives the sub-circuit completeness facts and the witnessed-vector values
  (`hw_i := hw ⟨i, by norm_num⟩`). The goal is the *constraint gates* themselves (boolean gate, gluing
  equalities) — not the Spec. Discharge subcircuit `Assumptions` (= `True`) with `trivial` and the gluing
  gates from the honest witnesses.

## The `FormalAssertion` + `populate` demotion (generalizing the Add worked example)

For ops whose witnessed columns are **pinned by the semantic `Spec`** (see `../architecture.md`
"Assertion vs `FormalCircuit`"), the op is a *witnessless* `FormalAssertion` and the **chip** owns the
witnessing. Template: `Operations/{AddOperation,SubOperation,AddwOperation,SubwOperation}/` (3-file split
`RawSpec`/`Elaborated`/`Formal`) and `Operations/{U16MSBOperation,U16CompareOperation}.lean` (single file).

- **`Inputs`** gains the result/witness columns + `is_real` (e.g. `⟨a, b, value, is_real⟩`); `Spec` is
  `is_real = 1 → <semantic eq>` (gated); `Assumptions` gains `(is_real = 0 ∨ is_real = 1)`.
- **`main` witnesses nothing** (`localLength 0`): each range check becomes a gated byte pull
  `byteChannel.pullIf input.is_real ⟨6, input.is_real * value[i], const 16, 0⟩`, each assert is
  `is_real`-gated (`input.is_real * (cᵢ * (cᵢ - 1)) === 0`).
- **`elaborated`**: `localLength 0`, `output _ _ := ()`, `channelsWith{Guarantees,Requirements} :=
  [byteChannel.toRaw]`, plus the three `@[circuit_norm]` rfl-lemmas (`channelsWith*_eq`, `localLength_eq`).
- **`populate`** (in `Elaborated`) computes the witness; **`spec_populate`** proves `Spec ⟨…, populate …⟩` —
  the chip uses it to discharge the `assertion …circuit`'s completeness obligation (`Assumptions ∧ Spec`).
- **Soundness**: byte ranges from the pull `Guarantees` (`byteRowSpec_range`), carry-bools from the gated
  asserts (`bool_of_mul_pred`), fed to `<sem>_of_<raw>`; plus a byte *padding requirement* per receive
  (`intro h; rw [gate_zero_of_ne hbin h, zero_mul, ← c16]; exact (byteRowSpec_range 0 h16p).mpr (by simp)`).
- **Chip side** (`Proofs/Chips/AddChip.lean`): `let value ← witnessVector n (fun env => <Op>.populate …)`;
  `assertion <Op>.circuit ⟨…, value, is_real⟩`. Soundness feeds the op's `Assumptions`
  (`(h_op ⟨ha,hb,h_bin⟩ hr).2`); the channel tail gains `Or.inr ⟨ha, hb, h_bin⟩`. Completeness reconstructs
  per-limb `#v[eval input_var[i]]_i = input_word` (`Vector.ext; interval_cases i`), then `rw [hval]; exact
  <Op>.spec_populate …`.

### The converse core — for an assertion that composes a sub-`assertion`

When a demoted op (Addw/Subw) composes another (U16MSB) as a sub-`assertion`, its **completeness** must
reconstruct the sub's `Spec` from its own semantic `Spec`. That needs the *converse* of the forward keystone:
`carries_of_addwSemantics : … → toBitVec64 (resultWord) = signExtend(…) → RawSpec ∧ (msb = if … then 1 else 0)`
(`Native/Operations/AddwOperation/RawSpec.lean`). **Landmine:** make `M := (m*65535).val` an *opaque* variable via
`obtain ⟨M, hMdef⟩ : ∃ M, (m*65535).val = M := ⟨_, rfl⟩` — a `set`/`let` lets the kernel reduce `(m*65535).val`
through `ZMod`'s `Nat.rec` multiply → "**(kernel) deep recursion detected**". (Symbolic `2^48`/`2^64` in
`omega` are *fine*; the recursion was *only* the unfolded `M`.) The msb falls out by
`m*65535 = m'*65535 → m = m'` (`mul_right_cancel₀ c65535_ne_zero`).

### U16MSB's `Assumptions` are gated

`U16MSBOperation.Assumptions := (input.is_real = 1 → input.a.val < 2^16) ∧ (input.is_real ∈ {0,1})`. The
composer only bounds `a` via its own `is_real`-gated byte pull, so on padding the bound is unavailable but
the `Spec` is vacuous. An *un*gated `a.val < 2^16` is undischargeable on padding. The sub-assertion's
`Assumptions` surface as a real conjunct in the parent's soundness *and* in its completeness (`Assumptions ∧
Spec`) — feed `⟨fun _ => bound, Or.inr rfl⟩` (+ `rfl` for the `is_real = 1 →` Spec gate).

### Aux-column ops composing a demoted sub-op (stay `FormalCircuit`, fix only the composition)

Lt/Mul keep witnessing their aux columns (FormalCircuit) but swap `subcircuit U16X.circuit a` for
`let w ← witnessVector 1 (fun env => #v[U16X.populate_… (env a)]); assertion U16X.circuit ⟨a, w[0], 1⟩`
(gate `1`, ungated — `mult = -1` pure receive, no padding requirement); use `w[0]` for the old `.msb`.
**Place the `witnessVector` at the same offset the old subcircuit's first column occupied** so
offset-dependent proofs survive (LtUnsigned/Mul soundness reference only columns *before* the U16X). The op
now emits byteChannel → declare `[byteChannel.toRaw]` + the rfl-lemmas + import `Model.Channels`. **Bind
`let bm : Expression _ := w[0]`** before using it — `(is_signed - 1) * w[0] === 0` otherwise defaults the `1`
to `ℕ` (`HSub (Expression _) ℕ` synth failure).

### Bit-shift chip soundness (the `ShiftRight` SRL dispatch)

`ShiftRight`/`ShiftLeft` have **no operation gadget** — SP1 inlines the limb decomposition of the register
read into the chip asserts, so the chip is a skeleton (asserts + byte pulls in `main`, semantic `Spec` in
`FormalModel/Contracts/Chips.lean`). The native arithmetic is ported verbatim from sp1-lean `ShiftRight/Common.lean` into
`Native/Operations/ShiftRightMath.lean` (the `srl/sra/srlw/sraw_close_su16_*_case` lemmas + `is_mod_64`,
`cancel_mul_65536`, the `srl_within_byte_shift*` division identities, a local `HWord`). Port landmines: the
early lemmas rely on a section `variable [Fact (Nat.Prime p)] [Fact (2^17<p)]` + a `local instance : NeZero
p`; file-level `set_option maxHeartbeats 100000000` + `linter.unusedVariables false`; sed range-extraction
drops `section`/`end` markers and `/--` openers (strip/restore them).

- **Spec on the register read, not a ghost operand.** The asserts decompose
  `adapter.op_b_memory.prev_value` (rs1) and read the shift amount from `op_c_memory.prev_value[0]` (rs2),
  and `main` never touches a separate `op_b_val`. So the `Spec` must shift `rs1 := adapter.op_b_memory
  .prev_value` by `rs2 := adapter.op_c_memory.prev_value` (like `BranchChip`), and `Assumptions` bound
  `isU64` of *those reads* — otherwise the operand is disconnected from everything the circuit constrains
  and soundness is unprovable. (Contrast Add/Lt, which pass `op_b_val` *into* an operation gadget.)
- **Kernel `2^64` deep-recursion → lift the conversion + `skipKernelTC`.** `BitVec.toNat_ushiftRight` at
  `BitVec 64` plants `2^64` (via `BitVec.ushiftRight`'s `@[expose]` body), tripping the kernel re-check even
  under `lake build`'s `--tstack`. The split-into-bare-`rw` (sp1-lean PROOF_PATTERNS §3 #8) was **not**
  enough here. Fix: lift the `toBitVec64 cols.a = RV64.srl rs2 rs1 ⟸ (toBitVec64 cols.a).toNat = rs1.toNat
  / 2^(c0.val%64)` conversion into a `private` helper (`srl_div_to_bitvec`) so the trigger is isolated, and
  put `set_option debug.skipKernelTC true in` on it (the doc-acknowledged **axiom-clean** escape — only
  skips re-verifying the known `2^64` shape). Lemma name is `BitVec.extractLsb'_toNat` (not
  `toNat_extractLsb'`); `extractLsb 5 0 = extractLsb' 0 6`, `.toNat = x.toNat % 2^6`.
- **`simp only [id_eq]` before `linear_combination`/`ring` over field elements.** Clean wraps field
  elements as `id (ZMod p)`, which blocks `ring`'s instance synthesis (`IsRightCancelAdd (id (ZMod p))`).
  `clear_value` does **not** fix it; `simp only [id_eq] at h ⊢` does (the `BranchChip` L510 pattern).
  `linarith` never works on `ZMod p` (no order) — use `linear_combination`.
- **Pervasive form bridges.** The ported close lemmas use `((N:ℕ):ZMod p)` casts and `cb_i * (2:ℕ)`-cast
  exponents while the asserts/byte-pulls use ZMod literals (`N`, `cb_i * 2`); bridge each with `push_cast;
  ring` / a one-shot `have hXY : … = … := by push_cast; ring; rw [hXY]`. `norm_num at h` *distributes*
  negations (breaking later `rw` matches) — use a targeted `rw [show (2:ℕ)^10 = 1024 from by norm_num]`.
- **Stage A (shared prerequisites) shape** (`Proofs/Chips/ShiftRightChip.lean` `soundness` SRL bullet): `set`
  column aliases with the **exact** `env.get (i₀+4+1+1+…)` forms (Lean does not reduce the index
  arithmetic) + `clear_value`; `single_flag` (one flag = 1 ⇒ others 0, via a `ZMod.val_add_of_lt` chain);
  `b_msb = 0` ⇒ no sign fill; an `hbyte_fact` extractor folding `sum*v → v` (on the real row `sum = 1`) +
  `byteRowSpec_range_val` (symbolic-width `Range` extraction) for the limb ranges; eval bridges from
  `h_input`; the v-encodings + de-gated limb splits; `is_mod_64` to normalise the shift count.
- **The 4×16 leaf dispatch** (SRL conjunct, fully proven): `rcases b_cb5 <;> rcases b_cb4` (4 byte-shifts),
  then per byte-shift: zero the off-selectors, substitute `a[j] = limb_result[j]` from the output-placement
  asserts (`h_o*`), expand via the limb_result decomposition, then `rcases b_cb0..3 <;> first | exact
  srl_close_su16_{bs}_case S … | …` over the 16-entry S/M/N table.
  - **`ring1`, never `ring`, in the leaf `by`-blocks.** `ring` falls back to `ring_nf` on a wrong
    alternative (leaving `256 = 65536` unsolved), which `first` reports as an error it can't backtrack past;
    `ring1` fails cleanly so `first` moves on to the matching `S/M/N`.
  - **`mul_eq_zero` does NOT fire on `ZMod p`** (neither as `.mp` nor as a `simp only` lemma — the
    `Nat.rec` Mul-instance quirk). Extract the one-hot selectors via `simp at hh` (full `simp` *does* apply
    it) then a uniform `first | exact hh | exact hh.resolve_right (by norm_num [hne2, hne3])` (full `simp`
    sometimes closes clean, sometimes leaves a `suX = 0 ∨ <numeric> = 0` disjunction — the `norm_num`
    needs the `hneN : (N:ZMod p) ≠ 0` facts). Suppress `linter.unusedTactic`/`unreachableTactic` for the
    dead `resolve_right` branch.
  - The 16 alternatives differ only in `S/M/N`; **generate them** (and byte-shifts 1–3) with a script over
    the table rather than hand-typing. Watch the replace span doesn't swallow the following `· sorry`
    bullets.
- **SRA/SRLW/SRAW** add a `b_msb`/`srw_msb` sign-fill on top. SRA: derive `b_msb = if op_b[3].val ≥ 32768
  then 1 else 0` from the `U16MSBOperation` gadget `Spec` (apply `h_msb1 ⟨…, bool_of_mul_pred h_sra_b⟩`),
  case-split on `op_b[3].val ≥ 32768` (BitVec msb via `ShiftRightMath.toBitVec64_msb_eq_b3_ge`). The msb=0
  arm reuses the SRL dispatch (`sra_div_to_bitvec_false` → `srl_close`); the msb=1 arm uses
  `sra_div_to_bitvec_true` → `sra_close_su16_*_case` with `sraFill = 65536 − v0123`. Both conversion
  helpers carry `skipKernelTC` (the `2^64` trigger). SRLW/SRAW are the 32-bit (2-limb `HWord`) analogs,
  `signExtend 64`-packaged via `toBitVec64_signExtend_word`.

## Landmines

### Gadget-level (arithmetic, `Operations/`)

- **`circuit_proof_start` must be the FIRST tactic** in soundness/completeness. Any
  `haveI`/`set_option`/`have hp` goes *after* it, or it errors "can only be used on Soundness/Completeness"
  (put `set_option … in` on the theorem instead). (`circuit_proof_start` lives in `Clean.Utils.Tactics`.)
- **Imports before the module doc-comment.** A `/-! … -/` header before the `import` lines makes the package
  `-D linter.flexible` flag get rejected on the (now zero-imports) header. Imports first, then the doc-comment.
- **`a + -b` vs `a - b` is not syntactically equal.** Lookup `.Spec` results and `=== 0` gates surface
  as `… + -…`, but `RawSpec`/`Spec` are written with `-`. Before matching, `rw [← sub_eq_add_neg] at <hyps>`
  (or add `sub_eq_add_neg` to the `simp only`). Forgetting this gives "type mismatch … + -… vs … - …".
- **`mul_eq_zero` won't fire on `ZMod p`** (a `Nat.rec` Mul-instance quirk). To get `x = 0 ∨ x = 1` from
  `x * (x - 1) = 0`, go through `inv_mul_cancel₀` / a `bool_of_mul_pred`-style lemma, not `mul_eq_zero`.
- **`Word` is an `abbrev` for `Vector`** — `w.toBitVec64` dot-notation fails. Write `Word.toBitVec64 w`.
- **Fin-indexed env reads:** use `h_env ⟨k, by norm_num⟩`, not `h_env k` — the latter inserts a non-reducing
  `↑(k : Fin n)` coercion.
- **`#v[…]` field selectors need the right simp set.** To turn `(#v[a,b,c,d])[k]`-style hyps into the
  bare entries use `simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
  List.getElem_cons_succ, Nat.add_zero]` — but only include the lemmas that actually fire (the
  `unusedSimpArgs` linter is an error under the project's `-D` flags).
- **Helper lemmas over a structured `cols` won't unify with loose `env.get` terms.** State shared cores
  (e.g. `result_collapse`) over **loose field variables** with the gluing hyps as explicit equalities,
  so the same lemma applies to both a structured `cols` and the soundness goal's `env.get (i₀+k)` terms.
  Pin the equality args by passing `eq_of_sub_eq_zero <gate>` (its concrete type fixes the metavars).
- **Extract a heavy case-dispatch shared by soundness + completeness into a sibling module.** When a chip's
  soundness and completeness both run the *same* expensive case analysis in opposite directions (e.g. a
  one-hot opcode dispatch: soundness derives `flag=1 → (br=1 ↔ cond)` from `br = decision`, completeness the
  converse), don't inline it twice under the giant `circuit_proof_start` goal — there each `omega`/
  `linear_combination`/`simp` drags the whole chip context and the proof needs a 16M-heartbeat ceiling. Lift
  it to two directional lemmas over **loose `ZMod p` field variables** in a `Chips/<Op>Chip/Decision.lean`
  sibling (imported by `Formal`): they elaborate at the **default** heartbeat ceiling (small context), and
  soundness/`completeness` collapse to one `exact (…).mp`/`linear_combination (…).mpr` call apiece. State the
  lemma conclusions **verbatim** in the chip `Spec`'s shape (incl. `Word.toBitVec64`/`.slt`/`.ult` forms) so
  the call sites need no goal-bridging. `BranchChip` did this (16M→8M soundness, 16M→4M completeness, ~540-line
  `Formal` + a 3.5 s `Decision`); cf. the `Native/Operations/ShiftBounds.lean` `nlinarith` dedup. The `id (ZMod p)`
  field-carrier landmine bites at the seam: `simp only [id_eq] at <gate-hyp>` to strip it before feeding the
  loose-`ZMod p` lemma (see the `id_eq` note above).
- **`maxHeartbeats` floors.** `toBitVec64`/`asm8` rw chains are whnf-heavy: `set_option maxHeartbeats 2000000 in`
  for soundness/completeness; the carry lemmas (`addSemantics_of_carries` etc.) need up to `16000000`.
- **`omit [Fact (2^17 < p)] in` placement** — it goes *before* the doc-comment, not between the doc-comment and
  the theorem.
- **`omit [Fact …] in` errors with "cannot omit referenced section variable"** when the instance is
  actually used (e.g. via a `ZMod` cast). Drop the `omit`; silence the unused-section-var linter with
  `set_option linter.unusedSectionVars false in` only when the var is genuinely unused.
- **`ZMod.val_natCast_of_lt (by omega)` — never inline it.** Inlined, the `by omega` elaborates against a
  metavar goal `?a < ?n` with no `p` in scope and fails. Instead write a separate `have hX : (… : ZMod p).val =
  … := ZMod.val_natCast_of_lt (by omega : x % 256 < p)` with a **concrete type ascription**, so `omega` sees the
  prime bound. Also feed `omega` the numeric forms (`have e8 : (2:ℕ)^8 = 256 := by norm_num`; rewrite
  `2^17 < p` to `131072 < p`) since it doesn't evaluate exponentials.
- **`high_byte`-style div/mod lemmas:** prove `(low%256) + 256*(u/256) = u.val` first, lift to `ZMod`
  via a `calc … ZMod.natCast_zmod_val`, then `linear_combination` it — do **not** `rw` the lifted
  equation, which also rewrites inside `u.val`.
- **Opcode case split** `o = 0 ∨ 1 ∨ 2` from `o.val`: build it via
  `calc o = ↑(o.val) := (ZMod.natCast_zmod_val _).symm; _ = ↑(0:ℕ) := by rw [h]; _ = 0 := by norm_num`. **Not**
  `ZMod.val_injective` (takes the modulus explicitly), and **not** `rw [key]` (loops on the val).
- **`add_comm` / BitVec instance quirk** — same family as the `mul_eq_zero` quirk. Match the gadget's operand
  order (`op_b + op_c`) in the chip Spec and let the Sail bridge `add_comm` to `execute_RTYPE`'s convention,
  rather than rewriting inside the gadget.
- **Don't leave `ring`'s `info:` note.** On goals like `x - x = 0` after `rw`, `ring` runs `ring1`, fails,
  prints `Try this: ring_nf`, and closes via fallback — leaking an `info:` note that fails the
  clean-build bar. Use `simp` (or `ring_nf` / the explicit lemma) instead.
- **`simp_all` leaks** into unrelated hypotheses — prefer targeted `simp [...] at h`.
- **Named-implicit-arg syntax `(u := …)` can be rejected by `lake` even when the LSP accepts it.** Make
  such lemma args **explicit** and pass positionally.
- **`linear_combination` / `interval_cases`** need explicit `import Mathlib.Tactic.LinearCombination` /
  `Mathlib.Tactic.IntervalCases`.
- **`limb_lift` (`Math/Word.lean`) takes 5 explicit value args first:**
  `limb_lift _ _ _ _ _ ha hb hv hc_in hc_out h_eq`.
- **W-instruction sign extension — reuse `Word.toBitVec64_signExtend_word`, don't re-derive.** For a 32→64
  sign-extended result word `#v[v0, v1, m·65535, m·65535]` (SLLW, ADDW, SUBW), the native
  `Word.toBitVec64_signExtend_word R X m …` closes `Word.toBitVec64 R = X.signExtend 64` given `m = if
  R[1].val ≥ 32768 then 1 else 0` and `X.toNat = R[0].val + R[1].val·2^16`. The `m`-form is exactly what
  `U16MSBOperation.Spec` hands you, so the SLLW subcase lemmas (`Native/Operations/ShiftLeftCore.sllw_subcase_cb4_*`)
  skip sp1-lean's `HWord.sign_extend_32_to_64_msb` / `sllw_a2_a3_eq_msb_byte` entirely. The new
  `Math/HWord.lean` then only needs `isU32`/`toBitVec32`/`toBitVec32_toNat`.
- **SLLW shift amount is 5 bits, not 6.** `RV64.sllw` masks `rs2` to bits 4-0 (`is_mod_64`'s `%64` result
  projects to `%32` via `c0_mod32_of_mod64`, splitting `cbsum6 = cbsum5 + cb5·32`); and with `is_sll = 0` the
  byte-shift `cb4 + cb5·2·is_sll` collapses to `cb4` ⇒ **2-way** dispatch (vs SLL's 4). Bridge `RV64.sllw` to
  the `HWord` form via a top-level `sllw_rv64_eq` (`extractLsb' 0 32`/`0 5` → `setWidth`, kernel-checked once,
  off the inline soundness path — same `2^N`-recursion reason `sll_rv64_eq`/`toBitVec64_toNat_mod64` exist).
- **`linear_combination` sign for `a = m·k` from a `m·k - a = 0` gate.** A `cols.X·c - a[j]` constraint
  surfaces as `X·c - a = 0`; to prove `a = X·c` you need **`linear_combination -hgate`** (coefficient −1),
  not `linear_combination hgate` (which leaves `2a − 2X·c ≠ 0` and "ring expressions not equal").

### Chip / reader composition (`Chips/`, `Native/Readers/`)

- **Struct-output `FormalCircuit` completeness — witness via `fromElements #v[…]`, not the struct literal.**
  A reader/gadget whose `Output` is a *nested* `ProvableStruct` (e.g. `Extracted.RTypeReader`: 22 cols across
  `RegisterAccessCols`/`Word`/`RegisterAccessTimestamp`) should witness with
  `ProvableType.witness (fun env => fromElements (M := <Struct>) (#v[…] : Vector _ (size <Struct>)))`, **not**
  with the explicit `⟨…, ⟨…⟩, …⟩` struct literal. The witness's flat op is `fun env => toElements (compute env)`;
  with the `fromElements` form that reduces by `ProvableType.toElements_fromElements` to the bare `#v[…]`, so the
  completeness extraction `have hk : env.get (…) = v := by simpa using h_env ⟨k, by decide⟩` is cheap. With the
  explicit struct literal, `toElements ⟨…⟩` is a tower of nested `Vector.append`s and the `simpa` **times out at
  `whnf` even at 16 M heartbeats**. (The circuit's *output* is `varFromOffset` either way — soundness/`output_eq`
  are unaffected; only the completeness witness values differ.) Match the goal's index forms (`i₀ + 1 + 4`,
  `i₀ + 1 + [4, [1, 1].sum].sum`, …) verbatim in the `have`s; `simpa` closes the residual `↑⟨k,_⟩` ↔ literal and
  offset-assoc gaps by defeq. **For a *deeply*-nested struct (`Extracted.RTypeReader`'s 22 cols) prefer
  the next entry — factor it into composed sub-circuits so no single circuit witnesses the whole tower at
  all; the `fromElements` form stays the tool for a circuit that must witness a *modest* multi-field
  struct directly (e.g. `Native/Readers/RegisterAccessTimestamp.lean`'s 2-col block).**
- **`simp [circuit_norm]`, not `simp only`, when the goal carries a witnessed-block projection tower.** If a goal
  reduces to `Expression.eval env (fromElements (Vector.cast … (mapRange n …).drop … .take …))`, `circuit_norm`
  has *no* rewrite for the `cast/drop/take/mapRange` tower, so `simp only [circuit_norm]` makes no progress and the
  closing `exact` falls back to raw `whnf` defeq (8 M+ heartbeats). Plain `simp [circuit_norm]` adds mathlib's
  default `Vector`/`getElem` lemmas, which rewrite the tower to `env.get (…)` cheaply. **Better fix:** compose the
  block as a subcircuit returning its extracted struct so the projection is a direct output field and the tower
  never appears (this is why the readers are `FormalCircuit`s, not chip-witnessed `fromElements` blocks).
- **A chip composing subcircuits keeps the *default* `output`** (do not set `output := varFromOffset <Chip> i0`).
  The chip's `main` returns a struct of subcircuit outputs at non-contiguous offsets, so `(main).output ≠
  varFromOffset`; the default `output := (main).output` is correct (and `output_eq` is `rfl`). Overriding it makes
  `output_eq`'s `rfl` time out.
- **Don't hand-write the chip's `ElaboratedCircuit` obligations — let the defaults fire.** Leaving
  `localLength_eq`/`subcircuitsConsistent`/`channelsLawful` *unspecified* uses the class defaults (`rfl` /
  `simp only [circuit_norm]; …` / `dsimp only [ChannelsLawful]; simp only [circuit_norm, seval]; …`,
  `Clean/Circuit/Basic.lean:218-249`), which close cheaply because they treat each `subcircuit` as a black box.
  Writing them explicitly as `simp +arith [circuit_norm, main, X.circuit, X.elaborated, …]` is what's slow: passing
  the subcircuits' `.circuit`/`.elaborated` forces `circuit_norm` to crack open their internals (the 22-col
  `RTypeReader` witness especially), which is what made `AddChip`'s instance need `maxHeartbeats 16000000` and ~4
  min. With the defaults it elaborates in **~1.7 s, no bump** (provide only `localLength _ := <concrete value>`).
- **In a composition soundness proof, `simp [circuit_norm] at <subcircuit-spec hyps>` BEFORE the final
  `refine`/`exact`.** A subcircuit's soundness hypothesis (e.g. `hclk13 : ((eval env (varFromOffset CPUState …))
  .clk_0_16 - 1) * 8⁻¹).val < 2^13`) is *defeq* to the goal conjunct but not syntactically equal; `exact ⟨…,
  hclk13, …⟩` makes the elaborator bridge that gap by raw `whnf` (slow → wants a heartbeat bump). A cheap
  `simp [circuit_norm] at hclk13 hclk8` normalizes both to `env.get …` first, so `refine ⟨…, hclk13, hclk8⟩`
  matches by `rfl`. Same root cause as the `simp only`/`whnf` finding above — pushing unnormalized terms into a
  defeq check. See `Proofs/Chips/AddChip.lean`.
- **Compose a chip `Spec` from its sub-circuits' `Spec`s (direct sub-calls), don't restate them inline.**
  Mirror sp1-lean's `SP1Chips` `allHold_constraints_iff` shape: the chip `Spec` is a conjunction of
  `<Reader>.Spec <reader-input-rebuilt-from-cols> cols.<block>` sub-calls (ungated — the readers' range checks
  are unconditional), the **proven** `is_real`-binary fact, and the `is_real`-gated arithmetic identity. In
  soundness each sub-call is discharged by the matching `h_<sub> trivial` from `h_holds` — it matches the
  conjunct *directly* (no per-bound `circuit_norm`), which is both cleaner and far cheaper than inlining the
  reader's bounds (an inlined "wide" spec is what historically timed out). Reconstruct the reader's cross-block
  inputs from the chip columns in the `Spec` (e.g. `clk_low := cols.state.clk_0_16 + cols.state.clk_16_24*65536`,
  `wv* := cols.add_operation.value[i]`). See `Proofs/Chips/AddChip.lean`.
- **Gate a reader's byte/range checks by `is_real` so padding rows are vacuous — range-check `is_real * value`.**
  SP1 sends each byte lookup with multiplicity `is_real`, so on padding (`is_real = 0`) the check isn't
  enforced and a real zero-padding row (all columns 0) is accepted. We don't model the byte bus (we use
  `Gadgets.ToBits.rangeCheck`, an unconditional assertion), so replicate the gating by range-checking
  `is_real * value`: on `is_real = 1` it's `value` (the real check), on `is_real = 0` it's `0` (trivially in
  range). The reader takes `is_real` as an input and its `Spec` becomes `is_real = 1 → <bounds>`. Soundness:
  under `is_real = 1`, `rw [h_real, one_mul]` turns the `is_real * value` bound into the `value` bound.
  Completeness: the padding-safe witness makes `value = 0`, so the gated check is `is_real * 0 = 0` (`mul_zero`)
  for *any* `is_real` — no `is_real`-binary assumption needed. **Scope it per SP1's constraint list:** in
  `RTypeReader` only the timestamp **byte** checks are `is_real`-gated; the `op_a_0 * wv` **zeroing gates are
  unconditional** (SP1 emits bare `assertZero`). And a pure arithmetic gadget like `AddOperation` needs *no*
  gating — a zero row already satisfies `0 = 0+0`; it's specifically the readers' byte checks that break on
  zeros. See `Native/Readers/{CPUState,RTypeReader}.lean`.
- **`is_real`-binary is *proven*, not assumed — split it across `Assumptions`/`ProverAssumptions`.** The chip
  emits the binary gate `is_real * (is_real - 1) === 0`, so soundness derives `is_real = 0 ∨ is_real = 1` from
  the gate hypothesis via `bool_of_mul_pred` (`Math/Word.lean`; it wants the `x * (x + -1) = 0` form,
  which is exactly the eval'd gate) and puts it in the `Spec`. Drop it from the (soundness) `Assumptions`. Only
  *completeness* still needs it as a precondition — keep it in `ProverAssumptions` (the prover commits to a
  boolean selector). This is the point of `GeneralFormalCircuit`'s decoupled Assumptions/ProverAssumptions.
- **A `maxHeartbeats` bump in a *simple* proof is a code smell, not a fix.** Genuine arithmetic (the
  `toBitVec64`/`asm8`/carry-chain rw towers in `Operations/`) legitimately needs `2_000_000`–`16_000_000`. But a
  *structural/compositional* proof — a chip threading subcircuit Specs, an `ElaboratedCircuit` instance, a reader
  range-check — that only passes with a bump is almost always brute-forcing a `whnf`/defeq blowup that a cheap
  normalization removes. Before bumping such a proof, find the unnormalized term and fix it: prefer the default
  obligations; `simp [circuit_norm] at <hyp>` to align forms before `exact`; witness via `fromElements #v[…]` so
  `toElements` reduces (see above). `AddChip` went 16M-everywhere → **zero bumps** this way (243 s → 1.7 s).

## Reader composition (nested-struct readers as composed `FormalCircuit`s)

A reader whose `Extracted` output is a *deeply nested* `ProvableStruct` (`Extracted.RTypeReader` = four
scalars + three `RegisterAccessCols`, each a `Word` + a `RegisterAccessTimestamp`) cannot be a single
flat-witness circuit: even with the `fromElements` trick, `circuit_proof_start`'s `circuit_norm` has to
normalize the whole nested tower in one `whnf` and times out (minutes, then a hard timeout even at 4 M / 16 M
heartbeats). The fix that scales — and the shape the readers now use — is to **mirror the struct nesting with
composed sub-circuits**, exactly how `Clean/Gadgets/Keccak/KeccakRound.lean` proves a 1288-column state with
plain `circuit_proof_start`.

- **Factor each sub-struct into its own `FormalCircuit` that fills its own witness-gen obligations; compose
  them as `subcircuit`s.** One file per block (`Native/Readers/RegisterAccessTimestamp.lean` ⊂
  `Native/Readers/RegisterAccessCols.lean` ⊂ `Native/Readers/RTypeReader.lean`). The parent witnesses only its *own* scalar
  columns and `subcircuit <Block>.circuit ⟨…⟩` per nested block, then `return ⟨…⟩` assembling the output from
  the scalars and the sub-circuit outputs. Because each block is a sub-circuit *output* (an opaque
  `varFromOffset`), no nested struct literal is ever witnessed, so `circuit_norm` treats each block as a
  black box and every proof closes at the **default** heartbeat floor (the point — a bump here is the code
  smell above). The parent's `localLength` is just the sum (`4 + 3 * 6` for `RTypeReader`); a chip composing
  the reader sums the readers' `localLength`s in `main` order (`6 + (4+4*16) + (4+3*6)` for `AddChip`) — and
  this is the one obligation to **recompute whenever a composed reader's column count changes**, because the
  default `localLength_eq` `rfl` only fails *late* (once the reader compiles), as a stale `AddChip` did when
  the readers moved off `Gadgets.ToBits.rangeCheck` bit-witnesses onto zero-width `ByteTable` lookups.
- **A `FormalCircuit` whose `main` composes sub-circuits must *omit* `output` — same rule as a chip.** Setting
  `output _ i0 := varFromOffset <Struct> i0` forces the `output_eq` obligation to `whnf` the subcircuit
  composition → `(deterministic) timeout at whnf (200000 heartbeats)`, which then cascades to `Unknown
  identifier 'elaborated'` at `def circuit := { elaborated with … }`. Omit it: the default `output :=
  (main).output offset` is the assembled struct of sub-circuit outputs and `output_eq` is `rfl` with no
  unfolding (`Native/Readers/RegisterAccessCols.lean`, `Native/Readers/RTypeReader.lean`, `Proofs/Chips/AddChip.lean`). Set
  `output` explicitly **only** for a *leaf* circuit whose `main` has no sub-circuits — there `varFromOffset`
  is right and cheap (`Native/Readers/RegisterAccessTimestamp.lean`).
- **Emit a struct-input-projected byte check as an inline `Circuit.lookup ByteTable ⟨…⟩`, not a
  `byteRangeCheck`/`byteRangeCheckBits` `FormalAssertion` sub-circuit.** When the lookup argument flows from a
  *struct field* of the input (`input.clk_target` into the `U8Range`/`Range` argument), composing the
  `FormalAssertion` wrapper as a sub-circuit makes `circuit_proof_start` explode in `whnf` (superlinear in
  subcircuit-args-over-struct-projections). The raw inline `Circuit.lookup ByteTable ⟨op, x, …⟩` — the
  in-circuit half of SP1's `send_byte`, the same way `BitwiseU16Operation` uses `ByteXorTable` — is
  semantically identical (membership in the same `ByteTable`) and closes at the default floor. Soundness:
  `simp only [circuit_norm, ByteTable] at h_holds` turns each lookup into a `ByteRowSpec` fact; convert via
  `byteRowSpec_range`/`byteRowSpec_u8range`. The `FormalAssertion` wrappers stay fine when the arg is the
  *whole* bare input (`Native/Readers/CPUState.lean`'s clock checks). Related: a `FormalAssertion`'s predicate
  *preconditions* belong in its internal `Assumptions`, not threaded in as extra inputs.
- **Soundness/completeness shapes for a reader composing N sub-circuits.** After `circuit_proof_start`,
  `h_holds` is the N sub-circuit results (`Assumptions → Spec`, `Assumptions = True` so use `h_ trivial`)
  **then** this circuit's own asserts, in `main` emission order — `obtain ⟨h_a, h_b, h_c, z0, z1, z2, z3⟩`.
  The *soundness goal* is `Spec ∧ (N `Requirements` tails)`, one tail per composed sub-circuit
  (`channelsWithRequirements = [] ∨ Assumptions`, closed by `Or.inl rfl` since the sub-circuits declare no
  channels). The `Spec` is a *folded* unit and the anonymous-constructor flattening is **shallow** (it will
  not auto-split a nested `∧` sitting in a non-tail field), so match the goal tree exactly — e.g.
  `refine ⟨⟨⟨z0,z1,z2,z3⟩, ?_⟩, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩` nests the `Spec`'s own conjuncts; a
  flat tuple mis-associates and the elaborator reports `z0` "expected to have type `[the whole conjunction]`".
  *Completeness* is the opposite: `circuit_norm` yields a *flat* conjunction of the sub-circuits' `True`
  assumptions and this circuit's gate obligations (e.g. `env.get(op_a_0) * wv = 0`), so a flat
  `refine ⟨trivial, …, ?_, ?_⟩` fits; pull a witnessed-`0` column out as the k-th conjunct of `h_env`
  (`obtain ⟨_, _, h0, -⟩ := h_env`) and close each gate with `rw [h0, zero_mul]`. See `Native/Readers/RTypeReader.lean`.
  (For *channel*-emitting readers the tails carry real `Guarantees` content — see `../bus-model.md` §3 for
  that boilerplate; `Channel` is the faithful way to model the State/Byte/Program/Memory interactions.)

## `ElaboratedCircuit` field obligations: let the default tactics close them (don't hand-write proofs)

**Rule of thumb: an `ElaboratedCircuit` instance should almost never carry a hand-written field proof.**
Every field obligation — `localLength_eq`, `output_eq`, `subcircuitsConsistent`, `channelsLawful` — ships
with a Clean **default tactic** (`Clean/Circuit/Basic.lean`) that runs `simp only [circuit_norm, seval]`
(plus a `try`-closer). The right move is *always* to make that default succeed by feeding `circuit_norm`
the right `rfl`-lemmas — **not** to override the field with a bespoke `:= by …`. When you find yourself
writing an explicit field proof, treat it as a smell: the missing piece is a `circuit_norm` lemma, and
once it exists the field can be **omitted** so the default tactic resolves the goal. The
*only* manual `ElaboratedCircuit` field proofs left in the project are the deferred skeletons in
`Native/Operations/LtOperationUnsigned.lean` and `Native/Operations/AddressOperation.lean` (`localLength_eq`/`output_eq
:= by sorry`, WIP) plus one explicit `channelsLawful` in `Native/Operations/LtOperationSigned.lean` — everything
else, including every reader and `Proofs/Chips/AddChip.lean`, omits all four fields.

The recipe that gets you there:

1. **Every circuit exposes its `channelsWithGuarantees` / `channelsWithRequirements` / `localLength` as
   `@[circuit_norm]` `rfl`-lemmas, right after its `elaborated` instance.** Name them
   `channelsWithGuarantees_eq` / `channelsWithRequirements_eq` / `localLength_eq` (namespace-local, so no
   clashes). Prefix each with `set_option linter.unusedSectionVars false in` (the `Fact` prime/bound
   instances are in scope but unused in a `rfl` lemma; `omit` errors on the ones whose projection still
   needs the field instance, so the `set_option` form is the robust choice). Example
   (`Native/Readers/CPUState.lean`):
   ```lean
   set_option linter.unusedSectionVars false in
   @[circuit_norm] lemma channelsWithGuarantees_eq :
       (ElaboratedCircuit.channelsWithGuarantees field Extracted.CPUState : List (RawChannel (ZMod p)))
         = [stateChannel.toRaw, byteChannel.toRaw] := rfl
   ```
   These are the cheap rewrites that replace the old inline `have … := rfl; rw […]` boilerplate, and they
   are what lets a *composing* circuit's default tactic see through the sub-circuit's declared lists/length
   (otherwise they "sit in an instance argument" that `simp` won't cheaply reduce — the `RTypeReader`
   instance in particular `whnf`-blows up).

   **Companion lemma — `circuit.localLength`, not just `elaborated.localLength`.** When an op/reader is
   *composed* as a sub-circuit, the updated Clean routes its offset through `<Sub>.circuit.localLength`
   (via the `@[circuit_norm]` `FormalCircuit/FormalAssertion/GeneralFormalCircuit.toSubcircuit_localLength`
   lemmas). That term is *syntactically distinct* from the `elaborated.localLength` that the `localLength_eq`
   above is stated about, so `localLength_eq` never fires on it — the offset stays an unreduced
   `circuit.localLength` and bloats every downstream `e*`/`hsem` in the composing chip's soundness proof.
   So **also expose `circuit.localLength` as an `@[circuit_norm]` rfl-lemma**, named `circuit_localLength`,
   placed right after `def circuit` (it can't sit beside `localLength_eq`, because `circuit` is defined
   later — in `Formal.lean` for split ops). Every op/reader that is ever composed as a sub-circuit carries
   one (example `Native/Operations/MulOperation.lean`):
   ```lean
   set_option linter.unusedSectionVars false in
   @[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
       circuit.localLength x = 557 := rfl   -- same numeral as `localLength_eq` (0 for most)
   ```
   With these in `circuit_norm`, subcircuit offsets reduce to numerals *inside `circuit_proof_start`* for
   every chip, keeping the manipulated terms small. (This globalized a per-chip workaround that used to
   re-declare the eight `<Op>.circuit.localLength` values locally inside `Proofs/Chips/DivRemChip/Formal.lean`.)
   Corollary: strengthening `circuit_norm` this way can make a previously-needed manual
   `simp only [<Sub>.circuit, circuit_norm]` in a sub-op's *own* proof report `` `simp` made no progress``
   or flag a now-unused simp arg — that's the lemma working; drop the redundant step (as in
   `Native/Operations/LtOperationSigned.lean`).
2. **The generic list/propositional closers are tagged `circuit_norm` once**, in
   `Model/Channels.lean` (conceptually they belong with Clean's `channels_lawful` default, but that
   is a pinned dep we don't edit): `List.cons_subset List.mem_cons List.cons_ne_nil List.not_mem_nil
   List.Subset.refl or_false and_self`. With these, the residual `⊆`/`∈` `channelsLawful` goal reduces to
   `True` and the default tactic finishes.

With (1)+(2) in place, **omit `channelsLawful` (and `localLength_eq` / `output_eq`) entirely** — the
default tactic closes them. This holds for `RegisterAccessTimestamp`, `RegisterAccessCols`, `RTypeReader`,
`CPUState`, `AddOperation`, and every chip (`AddChip`, `AddwChip`, `SubwChip`, …). If a default *doesn't*
close — usually because a sub-circuit's `_eq` lemma is missing or not `@[circuit_norm]` — **add the lemma**
rather than reaching for an override. A one-line `channelsLawful := by simp only [circuit_norm, seval,
<Sub>.channelsWith*_eq …]` naming the sub-circuit lemmas is the last resort (still no inline `have`s); it
remains only in `LtOperationSigned`.

**Soundness-tail caveat.** Because the `channelsWith*_eq` lemmas are in `circuit_norm`, `circuit_proof_start`
also reduces the sub-circuit channel projections in a `GeneralFormalCircuit`/`FormalCircuit` *soundness*
goal: the per-sub-circuit "requirement tail" (`channelsWithRequirements = [] ∨ Assumptions`) collapses —
sometimes all the way to `True`, sometimes to the bare `Assumptions`, sometimes staying a disjunction.
Don't hard-code its shape; close it with a `first` that covers every collapse level:
```lean
refine ⟨⟨…the Spec tuple…⟩, ?_⟩
first
  | trivial
  | exact ⟨trivial, Or.inl rfl, Or.inl rfl⟩
  | (refine ⟨?_, ?_, ?_⟩ <;> first | trivial | exact Or.inl rfl | exact Or.inr h_as | exact Or.inr trivial)
```
See `Proofs/Chips/AddChip.lean` and `Native/Readers/RegisterAccessCols.lean` for the worked examples.

## "emitted = projection": `<b>Lookups_eq_emitted` (proving a trace projection IS the emission)

Goal: prove a hand-written trace-level projection (`Soundness/*Consistency.lean`'s `stateLookups`,
`memoryLookups`, `programLookups`) equals the `toAccess`-image of what the circuit *actually emits* on that
channel — turning the projection from a parallel shadow into a derived theorem. **State, Program, and Memory
are DONE** (`stateLookups_eq_emitted`, `programLookups_eq_emitted`, `memoryLookups_eq_emitted`, all
axiom-clean). **Only Byte remains** (its emits are *carried by* the `RAC ⊃ RAT` subcircuits + `pullIf`
form — a recovery-*through*-nesting, not the drop-based recovery below).

Two foundations files: `Model/InteractionProjection.lean` (`AbstractInteraction.toAccess env`,
`signedVal` = the centered representative for `-is_real`-valued mults, and the per-channel
`toAccess_emitted_<msg>` kernels) and `Model/InteractionRecovery.lean` (the subcircuit-drop toolkit).

**Kernel form (critical).** `Channel.emit` produces `_root_.emitted`, and `circuit_norm` unfolds the
`@[circuit_norm] Channel.emitted` def to it — so the `toAccess_emitted_<msg>` kernels are stated on
`emitted (channel := <chan>) mult msg` (the `_root_.emitted` form), **not** `chan.emitted`. This lets the
kernel fire by `simp` directly, with no per-emit `rw [show … = chan.emitted … from rfl]` re-fold (which
doesn't scale past 1 emit). Kernel proof: `simp only [..., emitted, ...]` then a trailing `simp` — but the
9/16-field `toElements` unfold must be `simp only` (deterministic, linear); plain `simp` over the full set
blows up at `whnf` for the bigger structs.

**The recipe (worked for Program + Memory — a *composed* reader, `RTypeReader`):**
1. **Drop the byte-only subcircuits.** `have hnil : ∀ inp o, interactionsWith <chan>
   (RegisterAccessCols.elaborated.main inp o).2 = [] := by intro inp o; apply
   interactionsWith_main_snd_eq_nil; simp [circuit_norm, ElaboratedCircuit.channels]`. The `.2`-form
   `interactionsWith_main_snd_eq_nil` (InteractionRecovery) matches what `circuit_norm` leaves
   (`(main … off).2`, since `Circuit.operations c off = (c off).2`); it discharges `<chan> ∉ circuit.channels`
   from `ElaboratedCircuit.channels_subset` — needs the *symmetric* channel-distinctness
   (`memoryChannel_eq_byteChannel_false` etc.) + `ElaboratedCircuit.channels` in the simp set.
2. **Drop the `op_a_0 === 0` Equality gates.** `have heq := fun n inp =>
   filter_interactions_formalAssertion_eq_nil (Gadgets.Equality.circuit id) <chan> (n := n) inp
   List.not_mem_nil List.not_mem_nil` (the `===` desugars to `Gadgets.Equality.circuit id`, a
   `FormalAssertion` with no channels; TypeMap is `id` not `field`; `List.not_mem_nil` takes the element
   *implicitly* — no `_`).
3. **Reduce `interactionsWith` to the target emits.** `simp only [<rdr>.main, circuit_norm, hnil, heq,
   <otherchan>_eq_<chan>_false, if_false]` — the other bus's emits collapse via the explicit
   channel-distinctness `= False` lemma + `if_false` (`circuit_norm` alone leaves the `if … = … then`).
4. **Apply the kernel + bind.** `simp only [toAccess_emitted_<msg>]` then `simp [circuit_norm,
   signedVal_is_real hp2 h_real, signedVal_neg_is_real hp2 h_real, <Lookups>, <Access>, h_*]`. Realization
   hyps: WITNESSED columns as `env.get <offset> = r.cols.…` (`circuit_norm` turns `eval env (var ⟨off⟩)` into
   `env.get off`); INPUT fields as `Expression.eval env input.… = …`; SUBCIRCUIT-output columns as
   `Expression.eval env (RegisterAccessCols.elaborated.output ⟨…⟩ <off>).field = …` (these stay `eval env
   (output …)`, NOT `env.get`). `hp2 : 2 < p` from `Fact (2^17 < p)`.

**Byte (deferred — the different case; see `../architecture.md` §"Interaction half" and `../roadmap.md`).**
Byte's emits are *the content* of the `RAC ⊃ RAT` subcircuits (they
don't drop), so recovery must *recover* their emits through two levels of nesting (the State
`exposedChannels` route composed through nesting), plus a `pullIf` kernel (mult `-is_real`,
value-folded `is_real*value`). First the **byte faithfulness cleanup** removed the divergent reader byte
checks (CPUState's 4 `pc`, `RegisterAccessCols`'s 4 `prev_value`) SP1 has no analog of — so the readers now
emit exactly `ByteConsistency.byteRows`'s 8 checks, which is what makes byte `eq_emitted` well-posed.

## `ChipAir` / `Machine` (the cross-chip bus aggregate)

`Model/ChipAir.lean`: `ChipAir {name, perRow : Row → LookupAccessList, included}`, `Machine := List
(ChipAir Row)`, `Machine.busAggregate`/`busBalance` over the *computable* `InteractionBus`
core (never `noncomputable interactionsWith`). `multiplicitySum_busAggregate_cons` decomposes a machine's
per-key sum into per-chip sums. (The bespoke per-bus `ChipAir`s + `Machine` that drove the retired
`TraceValid` capstone lived in `Soundness/MachineConsistency.lean`, removed 2026-06-05; the surviving
statement-layer infra is `Model/ChipAir.lean`, and the live cross-chip argument is the gated
`Soundness/GatedVm/` path.) **Gotcha:** `Machine` is an `abbrev` for `List`, so `m.busAggregate`
dot-notation resolves to `List.busAggregate` — call `Machine.busAggregate m` explicitly. Statement layer
only: it makes Σsends = Σreceives expressible; it does not derive the per-bus meaning (those stay threaded).

## Build-validation gotcha (repeat from LEAN_SAIL_NOTES)

- **`lake build <module>` is the only authoritative signal.** The lean-lsp diagnostics/`lean_goal`
  results can go stale and report a clean state while `lake build` still fails. Capture build output to a
  logfile and check the exit code; an empty log + `Build completed successfully` = real success.
- Work one file and one build at a time; avoid batching many edit + LSP calls in a single turn.
- **LSP times out on a big chip file → introspect via a scratch `import`.** `lean_goal` on a 600+-line chip
  (e.g. `ShiftLeftChip.lean`'s completeness) times out because it re-elaborates the whole file. Instead write
  a throwaway `SP1Clean/Scratch.lean` = `import …<Chip>` + `example : …Completeness … := by
  circuit_proof_start; sorry`; the import is served from the cached olean, so only the tiny `example`
  elaborates live and `lean_goal` returns the full proof state instantly. Delete the scratch before
  committing (it lands in the lake glob).
