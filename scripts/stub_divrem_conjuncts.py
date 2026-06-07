#!/usr/bin/env python3
"""Produce a stubbed copy of DivRemChip/Formal.lean for fast single-conjunct iteration.

Each of the 8 flag conjuncts (div/divu/rem/remu/divw/remw/divuw/remuw) lives as a `·` bullet
under the 8-way `refine`. This rewrites every conjunct NOT in --keep to `    · sorry`, so the
file builds in a fraction of the time (the kept conjunct is the only heavy elaboration).

Usage: stub_divrem_conjuncts.py <src> <dst> --keep divw,remw
The conjunct bullets are matched by their leading comment / sorry marker at 4-space indent.
"""
import sys, re

SRC, DST = sys.argv[1], sys.argv[2]
keep = set()
if "--keep" in sys.argv:
    keep = set(sys.argv[sys.argv.index("--keep") + 1].split(","))

lines = open(SRC).read().split("\n")

# conjunct bullet markers, in order. Each is the start of a `    · ` bullet.
# match either `    · -- <name>:` or `    · sorry -- <name>`
markers = ["div", "divu", "rem", "remu", "divw", "remw", "divuw", "remuw"]

def bullet_name(line):
    m = re.match(r"^    · (?:-- (\w+):|sorry -- (\w+))", line)
    if m:
        return m.group(1) or m.group(2)
    return None

# find bullet start line indices in order
starts = []
for i, ln in enumerate(lines):
    nm = bullet_name(ln)
    if nm is not None:
        starts.append((i, nm))

# The 8 conjunct bullets are the first 8 matched (in source order). After them comes `  · ` (?_tail).
assert len(starts) >= 8, f"found {len(starts)} bullets, expected >=8"
conj = starts[:8]
# determine the end of the last conjunct: the next line at indent<=4 that is `  · ` (?_tail) or `/-` etc.
# We bound each conjunct by the next conjunct's start; the 8th ends just before the `  · ` tail bullet.
# find the tail bullet (2-space indent `· `) after the 8th conjunct start.
tail_idx = None
for i in range(conj[7][0] + 1, len(lines)):
    if re.match(r"^  · ", lines[i]) or re.match(r"^  sorry", lines[i]):
        tail_idx = i
        break
assert tail_idx is not None, "could not find ?_tail bullet"

bounds = []
for k, (i, nm) in enumerate(conj):
    end = conj[k + 1][0] if k + 1 < 8 else tail_idx
    bounds.append((i, end, nm))

out = []
prev_end = 0
for (i, end, nm) in bounds:
    out.extend(lines[prev_end:i])
    if nm in keep:
        out.extend(lines[i:end])
    else:
        out.append("    · sorry")
    prev_end = end
out.extend(lines[prev_end:])

open(DST, "w").write("\n".join(out))
print(f"stubbed -> {DST}; kept: {sorted(keep)}; conjunct lines: {[(nm,i+1,end+1) for (i,end,nm) in bounds]}")
