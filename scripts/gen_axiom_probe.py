#!/usr/bin/env python3
"""Generate `scripts/axiom_probe.lean`: one `#print axioms` line per headline declaration.

Scans the SP1Clean tree for the released theorem set (chip soundness/completeness, Sail
bridges + `kind` registrations, faithfulness anchors, witness-conformance anchors, the
GatedVm/capstone layer, and the coverage guards), resolving each declaration's fully
qualified name by tracking `namespace`/`end` blocks. The probe is self-checking: a wrong
FQN fails to elaborate, so a green probe run certifies the census covers real declarations.

Usage: `python3 scripts/gen_axiom_probe.py` (from the repo root); then
`lake env lean scripts/axiom_probe.lean` (see `scripts/run_audit.sh`).
"""

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "scripts" / "axiom_probe.lean"

# (glob, declaration-name regex) → collect matching theorems/defs with their namespace.
TARGETS = [
    ("SP1Clean/Proofs/Chips/*/Formal.lean", r"theorem\s+(soundness|completeness)\b"),
    ("SP1Clean/Proofs/Chips/*/Bridge.lean", r"theorem\s+(correct_\w+|\w*reaches_sail\w*)\b"),
    ("SP1Clean/Proofs/Chips/*/Bridge.lean", r"def\s+(kind)\b"),
    ("SP1Clean/Faithful/*.lean", r"theorem\s+(\w*faithful\w*)\b"),
    # The witness/trace conformance anchors now live in the separate `SP1CleanTest` test library (the
    # native_decide quarantine); the census still probes them to disclose their ofReduceBool axioms.
    ("SP1CleanTest/WitnessTests/*.lean", r"theorem\s+(\w*conforms\w*)\b"),
    ("SP1CleanTest/TraceGenTests/*.lean", r"theorem\s+(\w*conforms\w*)\b"),
    ("SP1Clean/Soundness/GatedVm/*.lean",
     r"theorem\s+(exists_trail|chipRows_step_sound|state_trail_of_balance|"
     r"gatedExecution_of_specs_and_balance|gatedExecution_allChips)\b"),
    # The field⇒ℤ balance bridge (formerly GatedVm/BalanceMod.lean, relocated in W11 Phase 5).
    ("SP1Clean/Model/BalanceBridge.lean",
     r"theorem\s+(isConsistentBalanced_of_intCast_zero|intCast_multiplicitySum_map_toAccess|"
     r"isConsistentBalanced_of_balancedInteractions)\b"),
    ("SP1Clean/Soundness/SP1Ensemble.lean", r"(?:theorem|def)\s+(sp1\w*)\b"),
    ("SP1Clean/Soundness/FinishedChannels.lean", r"theorem\s+(sp1_finishedChannel_guarantees)\b"),
    ("SP1Clean/Soundness/ChipRegistry.lean", r"(?:theorem|def)\s+(allChipKinds\w*)\b"),
    ("SP1Clean/Soundness/Coverage.lean",
     r"theorem\s+(coverage_kinds_eq_registry|coverage_length|covered_iff_routed|"
     r"wired_subset_reachable|reachable_subset_wired|routeOf_reaches_sail)\b"),
    ("SP1Clean/Soundness/TargetVm.lean", r"theorem\s+(sp1_target\w*)\b"),
    ("SP1Clean/Soundness/Decode.lean",
     r"(?:theorem|def)\s+(decode_\w+|instrToProgramRow_\w+|DecodeOperandsBound|decodedInROM\w*|"
     r"targetObligations_of_decode)\b"),
    ("SP1Clean/Model/SailDecode.lean",
     r"theorem\s+(run_bind_ok_\w+|decode_\w+)\b"),
    ("SP1Clean/FormalModel/Trace/Witness.lean",
     r"(?:theorem|lemma)\s+(isInitialState_nonvacuous|cfgState_\w+|mem_fullRegs)\b"),
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
            if not line.lstrip().startswith("--"):
                ns = ".".join(p for k, p in stack if k == "ns")
                out.append(f"{ns}.{m.group(1)}" if ns else m.group(1))
    return out


def main() -> None:
    fqns: list[str] = []
    extra_imports: list[str] = []  # modules outside the `SP1Clean` umbrella (e.g. `SP1CleanTest.*`)
    seen_imports: set[str] = set()
    for glob, pattern in TARGETS:
        decl_re = re.compile(pattern)
        for path in sorted(ROOT.glob(glob)):
            found = fqns_in(path, decl_re)
            if not found:
                continue
            fqns.extend(found)
            # `import SP1Clean` (the umbrella) covers every main-library declaration, but NOT the
            # `SP1CleanTest` conformance anchors (that test library is not imported by the umbrella —
            # it is the native_decide quarantine). Import each such module explicitly so its FQNs
            # resolve in the probe.
            rel = path.relative_to(ROOT)
            if rel.parts[0] != "SP1Clean":
                mod = ".".join(rel.with_suffix("").parts)
                if mod not in seen_imports:
                    seen_imports.add(mod)
                    extra_imports.append(mod)
    # dedupe, keep order
    seen, ordered = set(), []
    for f in fqns:
        if f not in seen:
            seen.add(f)
            ordered.append(f)
    lines = ["import SP1Clean"]
    lines += [f"import {m}" for m in extra_imports]
    lines += ["",
              "/-! Auto-generated by `scripts/gen_axiom_probe.py` — do not edit by hand.",
              "Run via `lake env lean scripts/axiom_probe.lean` (see `scripts/run_audit.sh`). -/",
              ""]
    lines += [f"#print axioms {f}" for f in ordered]
    OUT.write_text("\n".join(lines) + "\n")
    print(f"wrote {OUT.relative_to(ROOT)} with {len(ordered)} probes")


if __name__ == "__main__":
    main()
