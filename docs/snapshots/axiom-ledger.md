# Axiom & trust ledger

> Current snapshot: **2026-07-22**. Regenerate with `scripts/run_audit.sh` before relying on it.
> The authoritative per-declaration output is [`axiom-census.txt`](axiom-census.txt).

## Current result

The audit passes with **471 elaborated probes**, no project `axiom` declarations, no
`skipKernelTC`, and no `native_decide` in the main `SP1Clean/` library. Of those probes, **31**
carry `sorryAx`; all are allowlisted consequences of the **nine direct admissions** below. The
larger carrier count is not a count of independent proof holes: Clean's bundled circuit records retain
their completeness and channel-law fields, and the supported-machine registry deliberately retains the
full circuit records.

The probe generator now includes every chip's bundled `circuit`, DivRem's separately housed
completeness driver, the exact Core profile guards, and both ArkLib-facing Core AIR capstone
declarations. These expansions close audit-harness blind spots: the previous census saw the textual
DivRem `stop` without probing its declaration, and the first Core AIR draft built without explicitly
probing `sp1_air_refinement` or `sp1_air_sound`. Both capstone declarations are `sorryAx`-free; their
reported Sail platform hooks enter through the semantic target types.

## Direct admissions (9)

| Declaration / field | Kind | Status |
|---|---|---|
| `BranchChip.completeness` | completeness/liveness | Lean/Clean normalization regression |
| `ShiftLeftChip.completeness` | completeness/liveness | Lean/Clean normalization regression |
| `ShiftRightChip.completeness` | completeness/liveness | Lean/Clean normalization regression |
| `DivRemChip.completeness` | completeness/liveness | intentionally secondary to the chip contract |
| `DivRemChip.evidenceSoundness` | **chip soundness** | generated whole-chip row → isolated family evidence |
| `DivRemChip.main_exposedChannelsLawful` | structural packaging | exposed-channel normalization regression |
| `DivRemChip.circuit.requirementsChannelsLawful` | structural packaging | proves off-gate byte pulls are vacuous |
| `Soundness.sp1_decoded_rows_sound` | legacy structural machine seam | deterministic rows → frozen Eulerian prerequisites |
| `Soundness.supportedCore_orderedRows_dynamic` | **machine soundness** | exact ordered physical rows → timed Memory/spec/operand/readiness facts |

All theorems in the isolated DivRem contract and case-evidence layers are `sorryAx`-free. The public
`DivRemChip.contractSoundness` and `DivRemChip.soundness` are proved consumers of the one admitted
`evidenceSoundness` bridge.

## Transitive `sorryAx` carriers (31)

The exact set is machine-gated in `scripts/run_audit.sh`. It consists of:

- 11 chip declarations: the four completeness theorems; the four affected bundled circuits; and
  DivRem's `evidenceSoundness`, `contractSoundness`, and `soundness`;
- 19 registry/coverage/ensemble/capstone declarations that embed or consume those circuits and the two
  machine seams; and
- `Target.sp1_target_soundness`, which consumes the capstone chain.

Notably, `supported_core_native_sound` is a proved execution theorem, but it transitively carries
`sorryAx` because `supported_core_witness_grounding` invokes `supportedCore_orderedRows_dynamic`.
This is dependency disclosure,
not a second admitted proof.

## Other trust classes

| Axiom class | Meaning | Policy |
|---|---|---|
| `propext`, `Classical.choice`, `Quot.sound` | standard Lean/mathlib baseline | accepted headline baseline |
| generated `bv_decide` axioms | kernel-checked bit-vector decision procedure artifacts used by selected arithmetic proofs | accepted and disclosed per declaration |
| LeanRV64D platform hooks (`sys_enable_experimental_extensions`, reservation hooks, floating-point hooks, and related platform constants) | axioms present in the Sail model or in theorem statements over it | disclosed Sail-model trust boundary |
| generated `native_decide` axioms | compiler-trusted conformance evaluation | confined to `SP1CleanTest/`; **forbidden** in the main library |
| `sorryAx` | incomplete proof | permitted only for the nine direct admissions and their exact allowlisted carriers |

The test library currently contains 29 textual `native_decide` occurrences. They check witness/trace
conformance and are deliberately outside the main library and headline theorem dependency graph.

## Reproduce

```bash
lake build SP1Clean
lake test
lake lint
scripts/run_audit.sh
```

The latest full build completed 3578 jobs with no errors, warnings, or stray `info:` output. The probe
is generated from the live tree by `scripts/gen_axiom_probe.py`; an invalid fully qualified declaration
name makes elaboration fail. Use the raw census rather than `grep sorry` alone: only `#print axioms`
reveals transitive structure-field contamination.
