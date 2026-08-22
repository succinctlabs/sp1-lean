#!/usr/bin/env python3
"""Generate the axiom-census probes: one `#print axioms` line per headline declaration.

Scans the SP1Clean tree for the released theorem set (chip soundness/completeness, Sail
bridges + `kind` registrations, faithfulness anchors, witness-conformance anchors, the
timed-grounding capstone layer, and the coverage guards), resolving each declaration's fully
qualified name by tracking `namespace`/`end` blocks. The probe is self-checking: a wrong
FQN fails to elaborate, so a green probe run certifies the census covers real declarations.

Two probe files are emitted, one per library, so each elaborates against exactly the
oleans its build target produces (the CI `audit` job builds only `SP1Clean`; the `test`
job additionally builds `SP1CleanTest` via `lake test`):

- `scripts/axiom_probe.lean` — the main library (`import SP1Clean` only);
- `scripts/axiom_probe_test.lean` — the `SP1CleanTest` conformance and executable
  audit anchors (the native_decide quarantine), importing each test module explicitly.

Usage: `python3 scripts/gen_axiom_probe.py` (from the repo root); then
`lake env lean scripts/axiom_probe.lean` / `... scripts/axiom_probe_test.lean`
(see `scripts/run_audit.sh`).
"""

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT_MAIN = ROOT / "scripts" / "axiom_probe.lean"
OUT_TEST = ROOT / "scripts" / "axiom_probe_test.lean"

# (glob, declaration-name regex) → collect matching theorems/defs with their namespace.
TARGETS = [
    ("SP1Clean/Proofs/Chips/*/Formal.lean",
     # Probe the bundled circuit as well as its named proof fields.  In particular, a deferred
     # channel-law field lives only inside `circuit`, and every deferred completeness proof is
     # retained transitively by that structure even when a soundness consumer never projects it.
     r"(?:theorem|def)\s+(soundness|completeness|contractSoundness|evidenceSoundness|circuit)\b"),
    # Branch isolates its heavy soundness/completeness proofs in `Core.lean`; `Formal.circuit`
    # retains both, but direct probes keep the audit ledger readable.
    ("SP1Clean/Proofs/Chips/BranchChip/Core.lean",
     r"theorem\s+(soundness|completeness)\b"),
    # DivRem keeps its heavyweight completeness driver outside `Formal.lean`; without this explicit
    # target the textual admission gate saw the `stop`, but the axiom census silently skipped the
    # declaration itself.
    ("SP1Clean/Proofs/Chips/DivRemChip/Completeness/Driver.lean",
     r"theorem\s+(completeness)\b"),
    # DivRem's isolated, circuit-independent contract and evidence layer is a first-class audit
    # surface: probe every named theorem rather than only the admitted whole-chip extraction seam.
    # Dotted capture: `theorem Unsigned64Evidence.total` must probe the theorem, not collapse to
    # the (already-probed) structure name at the first `.`.
    ("SP1Clean/FormalModel/Contracts/DivRem.lean", r"(?:theorem|lemma)\s+([\w.]+)\b"),
    ("SP1Clean/Proofs/Chips/DivRemChip/Cases.lean", r"(?:theorem|lemma)\s+([\w.]+)\b"),
    ("SP1Clean/Proofs/Chips/*/Bridge.lean", r"theorem\s+(correct_\w+|\w*reaches_sail\w*)\b"),
    ("SP1Clean/Proofs/Chips/*/Bridge.lean", r"def\s+(kind)\b"),
    ("SP1Clean/Faithful/*.lean", r"(?:theorem|def)\s+(\w*faithful\w*)\b"),
    ("SP1Clean/Faithful/DivRemChip/Exact.lean",
     r"(?:theorem|def)\s+(\w*faithful\w*)\b"),
    ("SP1Clean/Faithful/SupportedMachine.lean",
     r"(?:theorem|def)\s+(supportedChipFaithfulness\w*)\b"),
    # W6: the transport layer — the generic per-table transport and its twenty-five
    # instantiations, plus the identity that makes the transported tables the ensemble's own.
    # These are the declarations that put `Faithful/` inside a live import closure.
    ("SP1Clean/Faithful/Transport/Table.lean",
     r"theorem\s+(transportTable_constraints|transportTable_accesses_perm|transportTable_spec)\b"),
    ("SP1Clean/Faithful/Transport/Ensemble.lean",
     r"theorem\s+(transported_map_component|transported_constraints)\b"),
    # The real-row satisfiability battery: every named anchor (28 per-chip rows + the Spec-level
    # companions + the nonempty-assert-list guard) is census-visible so its native_decide trust is
    # disclosed per-declaration like the conformance anchors.
    ("SP1CleanTest/NonVacuityReal.lean", r"theorem\s+(\w+)\b"),
    # The independent-audit joint-premise regression freezes both the full native constraint
    # check and the exact evaluated bus footprint. Keep its native_decide trust visible alongside
    # the older conformance and per-row satisfiability batteries.
    ("SP1CleanTest/Audit/*.lean",
     r"theorem\s+(constraints_hold|interactions_exact|program_projection|"
     r"supportedCoreNativeRelation_nonvacuous|traceGeneratableRelation_nonvacuous|"
     r"anchorTrace_yields_airWitness)\b"),
    # The W4 completeness layer's provider/ledger half: the built provider and verifier tables'
    # constraint theorems, and the generic push/pull balance bridge the W5 assembly consumes.
    ("SP1Clean/Proofs/Completeness/Providers.lean",
     r"theorem\s+(traceTable_constraints)\b"),
    ("SP1Clean/Proofs/Completeness/Ledger.lean",
     r"theorem\s+(balancedInteractions_of_signed_perm|balancedInteractions_of_flatMap_perm|"
     r"balanceOf_eq_pushed_sub_pulled)\b"),
    # W5: the machine-level assembly and its completeness capstone. The assembly's constraint
    # theorem is the join of all forty-one tables' own theorems, so a regression anywhere in the
    # completeness layer surfaces here first.
    ("SP1Clean/Proofs/Completeness/Assembly.lean",
     r"theorem\s+(witness_constraints|tables_map_component)\b"),
    ("SP1Clean/Soundness/AIRCompleteness.lean",
     r"theorem\s+(supported_core_native_complete|sp1Ensemble_statement_of_traceGeneratable|"
     r"witness_balancedChannels)\b"),
    # The W4 completeness layer: each chip's trace-table constraint/guarantee theorems and its
    # event-to-prover-assumptions discharge. Probed from the pilot onward so the rollout cannot
    # silently introduce a compiler-trusted or deferred step.
    ("SP1Clean/Proofs/Chips/*/Complete.lean",
     r"theorem\s+(traceTable_constraints|traceTable_guarantees|proverAssumptions_of_event)\b"),
    # The abstract walk/trail core (live — used by AIR + RankedGrounding).
    ("SP1Clean/Soundness/Walk.lean", r"theorem\s+(exists_trail)\b"),
    # The W3 generic engines: the goodness filter + self-loop cancellation (StateBump) and the
    # refresh elimination (MemoryBump). Keystones probed like Walk's `exists_trail`.
    ("SP1Clean/Soundness/GoodnessFilter.lean",
     r"theorem\s+(endpointBalanced_of_cancel_loops|good_of_endpointBalanced)\b"),
    ("SP1Clean/Soundness/RefreshElimination.lean", r"theorem\s+(eliminate)\b"),
    # The field⇒ℤ balance bridge (relocated in W11 Phase 5).
    ("SP1Clean/Model/BalanceBridge.lean",
     r"theorem\s+(isConsistentBalanced_of_intCast_zero|intCast_multiplicitySum_map_toAccess|"
     r"isConsistentBalanced_of_balancedInteractions)\b"),
    ("SP1Clean/Soundness/SP1Ensemble.lean",
     r"(?:theorem|def)\s+((?:sp1|balanced)\w*)\b"),
    ("SP1Clean/Soundness/AIR.lean",
     r"theorem\s+(statePullAlign8_of_stateWalk|"
     r"supportedCore_groundingObligations_of_constraints|"
     r"supportedCore_orderedRows_dynamic_of_obligations|"
     r"supportedCore_orderedRows_dynamic|supported_core_witness_grounding|"
     r"supported_core_native_sound)\b"),
    # Exact v6.3.1 table/profile guards and the public ArkLib-facing Core AIR capstone.  These are
    # release headlines: adding a new capstone file must not silently leave it outside the census.
    ("SP1Clean/FormalModel/CoreProfile.lean",
     r"theorem\s+(checkedIn_semanticRevision|coreCluster_matchesExtracted|"
     r"coreClusterShapes_matchExtracted|memoryBoundaryCluster_matchesExtracted|"
     r"memoryBoundaryClusterShapes_matchExtracted|publicValuesWidth_matchesExtracted)\b"),
    # The opcode-alphabet cross-check: the hand-maintained `Model/Opcode.lean` mirror against the
    # extracted `Opcode` enum discriminant table (trust-gap F8 closure).
    ("SP1Clean/FormalModel/OpcodeTable.lean",
     r"theorem\s+(opcodeTable_matchesExtracted)\b"),
    ("SP1Clean/Faithful/CoreAIR.lean", r"theorem\s+(system_isCurrent)\b"),
    ("SP1Clean/Soundness/CoreAIR.lean",
     r"(?:theorem|def)\s+(sp1_air_refinement_of_obligations|sp1_air_sound_of_obligations)\b"),
    # The base execution relation deliberately excludes COMMIT-row existence. Probe the persistence,
    # terminal-digest, and optional program-contract theorems separately so a future output theorem
    # cannot hide an admission behind wrapper or verifying-key terminology.
    ("SP1Clean/FormalModel/Contracts/PublicValues.lean",
     r"theorem\s+(SP1PublicValues\.committedDigest_eq_last_of_flag)\b"),
    ("SP1Clean/FormalModel/Execution.lean",
     r"theorem\s+(finalCommitRowsMatch_of_layout|finalCommitRowsMatch_of_execution|"
     r"completeCommitDigestMatches_of_coveredExecution|commitCovered_of_standardWrapper|"
     r"commitCovered_of_commitCoveringVerifyingKey)\b"),
    ("SP1Clean/Soundness/TimedGrounding.lean", r"theorem\s+(walk)\b"),
    ("SP1Clean/Soundness/FinishedChannels.lean", r"theorem\s+(sp1_finishedChannel_guarantees)\b"),
    ("SP1Clean/Soundness/ChipRegistry.lean", r"(?:theorem|def)\s+(allChipKinds\w*)\b"),
    ("SP1Clean/Soundness/Coverage.lean",
     r"theorem\s+(coverage_kinds_eq_registry|coverage_length|covered_iff_routed|"
     r"wired_subset_reachable|reachable_subset_wired|routeOf_reaches_sail)\b"),
    ("SP1Clean/Soundness/Decode.lean",
     r"(?:theorem|def)\s+(decodedInROM[\w.]*|sailConfigured_nonempty)\b"),
    # C1/Move-2: the decode projection, guards, ∃I∀s `decodedInROM`, its accessor, the 16 collapsed
    # `decodes<T>` producers, and the `instrToProgramRow(_inv)_*` inversions all live here (Model layer).
    ("SP1Clean/Model/Semantics/Decode.lean",
     r"(?:theorem|def)\s+(decodedInROM[\w.]*|decodes[A-Z]\w*|instrToProgramRow\w*|"
     r"mulOpCanonical|loadWidthOK|storeWidthOK|mulOp_canonical_inj|"
     r"loadOpcode_\w+|storeOpcode_\w+)\b"),
    ("SP1Clean/Model/SailDecode.lean",
     r"theorem\s+(run_bind_ok_\w+|decode_\w+)\b"),
    ("SP1Clean/FormalModel/Trace/Witness.lean",
     r"(?:theorem|lemma)\s+(isInitialState_nonvacuous|cfgState_[\w?]+|mem_fullRegs)\b"),
    ("SP1Clean/Soundness/MemoryGlobal.lean",
     r"theorem\s+(memProviderGenesis_of_contributions|memProviderGenesis_of_boundary|"
     r"traceMemoryValid_of_genesis_and_balance|traceMemoryValid_of_boundary_and_balance)\b"),
    ("SP1Clean/Soundness/MemoryIsU64.lean",
     r"(?:theorem|def)\s+(memBalanceHyps_of_genesis|memBalanceHyps_of_boundary|"
     r"operand_\w+_isU64_of_memBalance)\b"),
    ("SP1Clean/Soundness/ValueBound.lean",
     r"(?:theorem|def|lemma)\s+(value_targetBound|operandsBound_full_targetBound|targetObligations_full|"
     r"ValueOperandsBound|walk_clk_monotone|sndClk_eq_rcvClk)\b"),
]

NS_RE = re.compile(r"^namespace\s+([\w.]+)")
END_RE = re.compile(r"^end\b\s*([\w.]+)?")
SECTION_RE = re.compile(r"^section\b\s*([\w.]+)?")


def fqns_in(path: Path, decl_re: re.Pattern) -> list[str]:
    stack: list[tuple[str, str]] = []  # (kind, name) — kind ∈ {ns, sec}
    out = []
    comment_depth = 0
    for line in path.read_text().splitlines():
        if comment_depth > 0:
            comment_depth += line.count("/-") - line.count("-/")
            continue
        opens = line.count("/-") - line.count("-/")
        if opens > 0:
            comment_depth = opens
            continue
        if m := NS_RE.match(line):
            for part in m.group(1).split("."):
                stack.append(("ns", part))
        elif m := SECTION_RE.match(line):
            stack.append(("sec", m.group(1) or ""))
        elif m := END_RE.match(line):
            parts = (m.group(1) or "").split(".") if m.group(1) else [""]
            for part in reversed(parts):
                if stack and (stack[-1][1] == part or (stack[-1][0] == "sec" and not part)):
                    stack.pop()
        elif m := decl_re.search(line):
            stripped = line.lstrip()
            if not stripped.startswith("--") and not stripped.startswith("private "):
                ns = ".".join(p for k, p in stack if k == "ns")
                out.append(f"{ns}.{m.group(1)}" if ns else m.group(1))
    return out


def main() -> None:
    main_fqns: list[str] = []
    test_fqns: list[str] = []
    test_imports: list[str] = []  # `SP1CleanTest.*` modules, imported explicitly in the test probe
    seen_imports: set[str] = set()
    for glob, pattern in TARGETS:
        decl_re = re.compile(pattern)
        for path in sorted(ROOT.glob(glob)):
            found = fqns_in(path, decl_re)
            if not found:
                continue
            # `import SP1Clean` (the umbrella) covers every main-library declaration, but NOT the
            # `SP1CleanTest` conformance anchors (that test library is not imported by the umbrella —
            # it is the native_decide quarantine). Those go to the separate test probe, importing
            # each module explicitly so its FQNs resolve there.
            rel = path.relative_to(ROOT)
            if rel.parts[0] != "SP1Clean":
                test_fqns.extend(found)
                mod = ".".join(rel.with_suffix("").parts)
                if mod not in seen_imports:
                    seen_imports.add(mod)
                    test_imports.append(mod)
            else:
                main_fqns.extend(found)

    def dedupe(fqns: list[str]) -> list[str]:
        seen, ordered = set(), []
        for f in fqns:
            if f not in seen:
                seen.add(f)
                ordered.append(f)
        return ordered

    main_ordered = dedupe(main_fqns)
    lines = ["import SP1Clean",
             "",
             "/-! Auto-generated by `scripts/gen_axiom_probe.py` — do not edit by hand.",
             "Main-library census probe (elaborates against the `SP1Clean` oleans only).",
             "Run via `lake env lean scripts/axiom_probe.lean` (see `scripts/run_audit.sh`). -/",
             ""]
    lines += [f"#print axioms {f}" for f in main_ordered]
    OUT_MAIN.write_text("\n".join(lines) + "\n")
    print(f"wrote {OUT_MAIN.relative_to(ROOT)} with {len(main_ordered)} probes")

    test_ordered = dedupe(test_fqns)
    lines = [f"import {m}" for m in test_imports]
    lines += ["",
              "/-! Auto-generated by `scripts/gen_axiom_probe.py` — do not edit by hand.",
              "Test-library census probe (the `SP1CleanTest` conformance anchors; requires the",
              "test-library oleans — run `lake test` first).",
              "Run via `lake env lean scripts/axiom_probe_test.lean` (see `scripts/run_audit.sh`). -/",
              ""]
    lines += [f"#print axioms {f}" for f in test_ordered]
    OUT_TEST.write_text("\n".join(lines) + "\n")
    print(f"wrote {OUT_TEST.relative_to(ROOT)} with {len(test_ordered)} probes")


if __name__ == "__main__":
    main()
