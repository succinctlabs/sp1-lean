# SP1Clean — verification status of record (ground-truth snapshot)

**Snapshot date:** 2026-05-28. **Toolchain:** `leanprover/lean4:v4.29.0`, Clean `v6.2.2`.

This doc is the **honest, verified status** of the SP1Clean effort and the path to *full*
verification. Unlike `CLEAN_OVERVIEW.md` (narrative current-state) and `CLEAN_FUTURE.md`
(roadmap/rationale), every claim here is established from the tree at snapshot time —
`grep` for the inventory, and `#print axioms` for closure — **not** from prior docs. Where the
roadmap docs have drifted, §5 reconciles them.

The central honesty point, stated up front: there are **two different notions of "completeness"**
in play, and conflating them overstates how close we are. See §4 — for the chips with free
combinatorial witnesses (Mul, Shift, DivRem, Lt, Bitwise), *actual* completeness cannot be proven
without modeling internal **witness generation**, and that work is the open frontier sitting
directly under the chips that already look "closed."

---

## 1. Ground-truth snapshot

- **0 axioms declared in `SP1Clean/`.** `grep -rn "^[[:space:]]*axiom" SP1Clean/` is empty. No
  trusted bridges sneak in; everything either reduces to Lean's standard
  `propext / Classical.choice / Quot.sound`, or is an open `sorry`. This is a genuine strength.
- **≈82 genuine `sorry` obligations** (93 raw textual occurrences across 33 files; the ~11-line gap
  is `sorry` appearing in doc comments, e.g. `SP1Clean/Operations/LtOperationSigned.lean:288`,
  which describes a design choice rather than marking an open goal). The headline count is stable
  vs. the roadmap's "82" — what has drifted is *which* goals are open, not the total (see §5).
- **Where the sorries cluster** (approximate genuine counts, by area):
  - **Mul / ShiftLeft / ShiftRight ≈ 38** — split across `Circuit`, `Lemmas`, `Aggregate`, and
    `Multiplicity/{Circuit,Lemmas}`. The dominant block.
  - **System-level `Soundness/` = 13** — `MemoryConsistency.lean` (7, the per-chip
    `memoryAccessesValid_of_spec_*` for bitwise/lt/mul/shift/divRem) and
    `MemoryConsistencyClock.lean` (6). These gate the trace aggregator regardless of per-chip status.
  - **Control: Jal = 7** (`Circuit` 2 + `Lemmas` 5), **Branch = 4** (`Multiplicity/Circuit`). `Jalr`
    is aggregate-only (0).
  - **DivRem = 6**, **UType = 2**, **Bitwise = 1** (`SailBridge`).
  - **Memory: 4** — `MemoryGlobalChip` (3) + `LoadByteChip` (1).
  - **Operations = 5** — `IsZeroWordOperation`, `IsEqualWordOperation`, `U16CompareOperation` (1
    each) + `MulOperation` (2). Note `MulOperation` here is the SP1Clean wrapper; the **SP1-side**
    `SP1Operations/.../MulOperation.lean:42` and `BitwiseU16Operation.lean:536` carry the real
    witness-construction sorries (see §4).
  - **Infra: `SP1Lookup.lean` = 1**.
- **The base layer (`SP1Chips`, `SP1Foundations`) is genuinely sorry-free.** Their `grep` hits are
  all doc comments. The `SP1Chips.*.correct_*` RISC-V-equivalence proofs the SailBridges reuse are
  solid. (`SP1Operations` is *not* uniformly clean — three real witness-construction sorries, §4.)
- **Build state is incomplete.** The 6 closed chips and their dependencies are built and current
  (oleans present), which is what makes the axiom checks in §2 valid. But `SP1Clean.lean` (the lib
  root) imports modules whose oleans are **absent** — e.g. `DivRemChip.Circuit`, `MulChip.*`,
  `ShiftLeft/RightChip.*`. So a full `lake build SP1Clean` has **not** been driven to a green state
  in this tree; the ~82 sorries would register as warnings, which the repo's "0 errors **and** 0
  warnings = passing" policy treats as non-passing. *(Minor: a stale orphaned olean tree exists under
  the pre-migration flat layout `.lake/build/lib/lean/SP1Clean/AddChip/…`; the live source uses the
  nested `SP1Clean/Chips/ALU/AddChip/…` layout.)*

---

## 2. Per-chip closure matrix

"FormalAssertion-complete" = Clean's `completeness` (Assumptions ∧ Spec ⇒ constraints) is proven and
**axiom-clean** (no `sorryAx`). "Actually complete" = the *semantic* inputs alone imply a satisfying
witness exists — the stronger notion full verification needs (§4). **SailBridge is a real proof**
reusing `SP1Chips.*.correct_*`, not an axiom.

Closure of the 6 "closed" chips was verified with `#print axioms` (all show only
`propext, Classical.choice, Quot.sound`); the check was calibrated against a known sorry
(`MulOperation.iff_sp1_full` correctly reports `sorryAx`). The MCP `lean_verify` tool returns empty
results in this environment (missing `ripgrep`) — do **not** trust its `[]`; use
`#print axioms` via `lake env lean`.

| Chip | Spec form | FormalAssertion-complete (axiom-clean)? | Actually complete? | SailBridge | Notes |
|------|-----------|------------------------------------------|--------------------|------------|-------|
| **Add** | semantic `RV64.add` | ✅ verified | ✅ (carry witness proven) | ✅ verified | reference baseline |
| **Addi** | semantic `RV64.addi` | ✅ verified | ✅ | ✅ verified | |
| **Sub** | semantic `RV64.sub` | ✅ verified | ✅ | ✅ verified | |
| **Addw** | structural `AddwOp.AssertionGated.Spec` + semantic `RV64.addw` | ✅ verified | ⚠️ structural | ✅ verified (addw + addiw) | semantic collapse bypassed to avoid BV64↔BV32+msb inversion |
| **Subw** | structural `SubwOp.AssertionGated.Spec` + semantic `RV64.subw` | ✅ verified | ⚠️ structural | ✅ verified | as Addw |
| **Lt** | structural literal-conjunction | ✅ verified | ❌ blocked | ✅ verified (slt + sltu) | deliberately structural: SP1-side `LtOperationSigned.iff_sp1_full.mpr` is `sorry` (documented at `Operations/LtOperationSigned.lean:286–288`) |
| **UType** | structural `AddOp.Assertion.Spec` + semantic | ❌ 2 sorries (`Circuit`) | ❌ | present | mechanical envelope reshape |
| **Bitwise** | structural `BitwiseU16Op.Assertion.Spec` | ❌ 1 sorry (`SailBridge`) + `Multiplicity` | ❌ | sorry | backward byte-witness is SP1-side `BitwiseU16Operation.lean:536` |
| **Mul** | structural | ❌ ~14 sorries | ❌ | sorry | needs `.Gated` reshape + `MulOperation.lean:42` witness |
| **ShiftLeft** | structural | ❌ ~12 sorries | ❌ | (comment only) | bit-decomp + shift-power chain |
| **ShiftRight** | structural | ❌ ~12 sorries | ❌ | present | as ShiftLeft |
| **DivRem** | structural | ❌ ~6 sorries | ❌ | present | Phase-6 scope-fence (composes Mul/IsZeroWord/Add) |
| **Jal** | — | ❌ 7 sorries | ❌ | — | `Circuit` + `Lemmas` |
| **Branch** | — | ❌ 4 sorries (`Multiplicity/Circuit`) | ❌ | — | needs `is_blt + is_bge ∈ {0,1}` field-characteristic case-bash |
| **Jalr** | — | aggregate-only (no `Circuit`) | — | — | no FormalAssertion layer yet |
| **Load/Store** | — | mostly present; `MemoryGlobalChip` 3, `LoadByteChip` 1 | — | per-width bridges | route register access through `LoadMemoryAccessGated` |

**Key reading of the matrix:** Add/Addi/Sub are the *only* chips that are both FormalAssertion-complete
**and** actually complete — because their Spec is pure-semantic and the witness (the carry) is cheap to
construct, so the backward direction was genuinely proven. Every other chip with combinatorial
witnesses either (a) is closed but only in the *structural* sense (Addw, Subw, Lt), or (b) is still
open. For the per-`FormalSpec` semantic-purity classification, see the existing `docs/SPEC_AUDIT.md`
(categories a/b = semantic, c = faithful-mirror-without-`RV64.*` = structural); this doc adds the
*completeness* consequence on top of that classification.

---

## 3. Path to soundness-end-to-end (near-term target)

The soundness chain — "a constraint-satisfying trace certifies a correct RISC-V execution" — and where
it breaks:

1. **Per-chip `constraints.allHold ⟺ FormalSpec`** (Clean soundness + completeness, via
   `allHold_iff_structural`). Done & axiom-clean for the 6 closed chips; sorried for the other ~10.
2. **Per-chip `FormalSpec ⇒ Sail-equivalence`** (SailBridge, reusing `SP1Chips.*.correct_*`). Done &
   axiom-clean for the 6.
3. **Trace aggregation** — `trace_soundness_aggregateMemory` / `trace_soundness_with_boundary`
   (`SP1Clean/Soundness/TraceSoundness.lean:65,90`). This is **constraint-level only**. By its own
   docstring it does *not* link to `SailState` evolution: it assumes `∀ row ∈ rows, ChipRow.Spec row`
   plus trace-shape bundles (`TraceClkValid`, `TraceStateValid`, online memory consistency) and
   concludes memory-bus offline consistency + PC-chain + `is_real ∈ {0,1}`.
4. **The two missing rungs** (the file enumerates them under "what this does NOT prove"):
   - (a) a `Sail.execute_trace` recursive executor over `LeanRV64D` per-instruction steps (~50 LOC; none
     exists today);
   - (b) per-chip `correct_*` lifted to the clean side and threaded through that executor, so the
     conclusion becomes `∃ s_final, Sail.execute_trace s₀ rows.length = some s_final` matching the bus
     history.

**Honest near-term cost.** The dominant work is finishing the ~10 open chips' completeness + SailBridge
and closing the 13 system-level `Soundness/` sorries. The `Sail.execute_trace` wrapper itself is small.
None of this, however, establishes *prover liveness* — that requires §4.

---

## 4. Witness generation — required for *actual* completeness, not an optional frontier

The user-facing thesis: **for chips with free combinatorial witnesses (Mul, Shift{L,R}, DivRem, Lt,
Bitwise), proving actual completeness is impossible without modeling internal witness generation.** The
current proofs route *around* this by weakening the Spec, which is sound but does not close the loop.

### Two notions of completeness

1. **Clean's `FormalAssertion.completeness`** (`.lake/packages/Clean/Clean/Circuit/Basic.lean:317`) =
   `Assumptions ∧ Spec ⇒ constraints`. Chips use `FormalAssertion` with `localLength := 0`, so **every**
   column — carries, products, byte limbs, is-zero inverses — is an *input*, not an internally
   witnessed value. This direction is provable **only because the `Spec` is structural** — it references
   the aux-column relationships via `<SubOp>.AssertionGated.Spec`. With a pure-semantic Spec
   (`op_a = a * b`) it is literally **false**: the semantic equation does not pin the aux columns the
   constraints constrain.
2. **Actual completeness** (what full verification needs) = *semantic inputs alone* (a, b) ⇒ **there
   exists** a full row, aux columns included, satisfying the constraints. **That existence proof is the
   witness construction.** For the combinatorial chips you must build the carry/product/byte/inverse
   columns from the BitVec equation. There is no way around modeling internal witness generation.

### The code already admits this

The structural-Spec design is an explicit, documented workaround for the missing witness construction:

- `SP1Clean/Operations/LtOperationSigned.lean:286–288` — *"Spec is literal-conjunction under
  `is_real = 1 →` — the BV-collapsed semantic form is unavailable because
  `LtOperationSigned.iff_sp1_full.mpr` contains a `sorry` (no `spec_inv` exists for signed-`<`)."*
- The unavoidable obligation lives in the **backward direction of the operation-level iff** — and these
  are the real, built, `sorryAx`-positive lemmas:
  - `SP1Operations/Operation/MulOperation/MulOperation.lean:42` — *"construct carry/product/byte-witness
    from the BitVec eq — TBD."* (`MulOperation.iff_sp1_full` confirmed `sorryAx`.)
  - `SP1Operations/Operation/BitwiseU16Operation/BitwiseU16Operation.lean:536` — byte-witness.
  - `SP1Operations/Compare/LtOperationSigned/LtOperationSigned.lean:529` — byte-comparison witness.
- Addw/Subw take the same escape hatch *for cost reasons even where the op may be provable* (the Spec
  keeps `AddwOp/SubwOp.AssertionGated.Spec` to avoid a "costly BV64↔BV32+msb inversion").

So witness-generation modeling is **not** hypothetical future work; it is the frontier directly under
the chips that already verify clean.

### Consequence for the "closed" claim

A chip can be FormalAssertion-complete (axiom-clean) yet **not actually complete**. Lt is the live
example: its `completeness` and both SailBridges are `sorryAx`-free, but the Spec is structural, so the
"a valid `b<c` row exists" step is exactly the SP1-side sorry it routes around. Add/Addi/Sub avoid this
only because their witness (the carry) is cheap and was genuinely constructed.

### Two distinct boundaries, both "witness generation"

- **Boundary A (intra-Lean):** construct the aux columns from semantic inputs *in Lean* and prove they
  satisfy the constraints. Closes the operation backward sorries → unlocks actual completeness. Required.
- **Boundary B (Rust-prover link):** prove the values the **SP1 Rust generator** emits match a
  Spec-satisfying row. **The Rust generator is never referenced today** — `update_constraints.py` +
  `sp1-constraint-compiler` extract *constraints* only; there is no `genTrace`/`generateTrace`/
  `populate`/`assign` anywhere in `SP1Clean/`. Boundary A is a prerequisite to B.

### Why it matters (verifier vs prover)

Soundness (§3) protects the **verifier**: any accepted proof corresponds to a correct execution. That is
the security-critical direction and most of the value, and it is largely in hand. Actual completeness +
the Rust link protect the **prover / liveness**: a legitimate execution can always be proven, and the
real prover in fact produces such a proof. A gap here is a liveness / trust-in-the-prover gap, **not** a
soundness hole — weight the remaining work accordingly.

### The workstream to close it (staged 1 → 2 → 3)

1. **(Boundary A) Close the operation-level witness-construction lemmas.** Discharge the backward
   directions of `MulOperation` / `BitwiseU16Operation` / `LtOperationSigned` (and siblings): given the
   BitVec equation, construct the carry/product/byte/inverse columns and prove they satisfy the
   constraints. Converts the affected chips from FormalAssertion-complete to *actually* complete.
   Prerequisite for everything below.
2. **(Boundary A, trace level) Lean reference generator + correctness proof.** Define
   `genRow : InstrContext → ChipRow` in Lean; prove `ChipRow.Spec (genRow ctx)` and the trace-shape
   bundles for valid contexts, reusing step 1. This discharges the `h_specs` / `TraceClkValid` /
   `TraceStateValid` hypotheses of `trace_soundness_*` *constructively*, turning the conditional trace
   theorem into an unconditional prover-liveness statement.
3. **(Boundary B) Extract the Rust generator + differential check** (analogous to constraint
   extraction). Emit a Lean transcript of the SP1 Rust witness-gen per chip and prove its rows match the
   step-2 reference rows / satisfy Spec. Highest fidelity, but needs new tooling in the SP1 checkout (no
   such compiler pass exists today) and is the most expensive.

**Recommended honest interim stance:** drive boundary A (steps 1–2) to completion — it is required for
any truthful completeness claim — and explicitly document the Rust generator as *trusted* (boundary B
open) rather than silently assuming the loop is closed.

---

## 5. Reconciliation with `CLEAN_FUTURE.md` / `CLEAN_OVERVIEW.md` drift

`CLEAN_FUTURE.md` remains the design-rationale / roadmap doc; this doc is the status of record. Observed
drift at snapshot time:

| `CLEAN_FUTURE.md` claim | Observed reality |
|---|---|
| "82 sorry occurrences across **25 files**" (2026-05-25 audit) | ≈82 genuine sorries still, but spread across **~32 files** (93 raw across 33). Count stable; spread grew. |
| "Two open sorries: `AddwChip/Circuit.lean:152`, `MemoryConsistency.lean:1067`" | **Both gone.** AddwChip is fully closed & axiom-clean; `MemoryConsistency.lean` has no sorry near 1067 (the 7 there now are the per-chip `memoryAccessesValid_of_spec_*` lemmas elsewhere in the file). |
| "LtChip — 7 sorries; close `SailBridge` sorries" | **LtChip is closed & axiom-clean (0 sorries).** Its completeness is structural, not actual (§4). |
| Paths like `SP1Clean/AddwChip/Circuit.lean` | Tree migrated to nested `SP1Clean/Chips/ALU/AddwChip/Circuit.lean`; the flat paths survive only as orphaned oleans. |
| `MULTIPLICITY_BUS.md` "two remaining sorries at `AddwChip/Circuit.lean:152` and `MemoryConsistency.lean:1067`" | Both closed; the multiplicity-bus Phase 1–3/5–6 work landed. |

The roadmap's high-level critical path (steps 1–6 → ensemble soundness + completeness) is still
structurally correct; what it under-weights is the §4 distinction — its "completeness" means Clean's
FormalAssertion notion, not actual completeness, so its cost estimate omits boundary A/B entirely.

---

## How to reproduce the checks in this doc

```sh
# inventory
grep -rn "\bsorry\b" SP1Clean/ | wc -l            # raw occurrences (~93)
grep -rn "^[[:space:]]*axiom" SP1Clean/            # axioms (empty)

# authoritative closure check (lean_verify MCP is unreliable here — missing ripgrep)
cat > _axcheck.lean <<'EOF'
import SP1Clean.Chips.ALU.LtChip.Circuit
import SP1Operations.Operation.MulOperation.MulOperation
#print axioms MulOperation.iff_sp1_full            -- calibration: MUST show sorryAx
#print axioms SP1Clean.Lt.Assertion.completeness    -- expect: propext/Classical.choice/Quot.sound
EOF
lake env lean _axcheck.lean && rm _axcheck.lean
```
