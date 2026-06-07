import SP1Clean.Foundations.Word

/-! # AUTO-GENERATED — do not edit by hand.

Witness-generation conformance vectors for SP1's `U16MSBOperation`, dumped from the **real**
`U16MSBOperation::populate` by `update_extracted.py` (the `witness_vectors` binary,
`--operation U16MSBOperation`). Unlike the constraint (`eval`) extraction, `populate` is native
imperative code and cannot be symbolically extracted; these vectors instead tie the Lean
witness function to the Rust source by **conformance** (agreement on the sampled inputs —
edge cases + a seeded LCG — not an all-inputs proof). Each entry is `(a, msb)`. The
check lives in `SP1Clean/WitnessTests/U16MSBOperationWitness.lean`. Regenerate with
`SP1_DIR=… python3 update_extracted.py`. -/

namespace SP1Clean.WitnessTests
open SP1Clean

/-- 42 conformance vectors for `U16MSBOperation` (`(a, msb)`). -/
def U16MSBOperationWitnessVectors : List (ℕ × ℕ) := [
  (0, 0),
  (1, 0),
  (32767, 0),
  (32768, 1),
  (32769, 1),
  (65535, 1),
  (32767, 0),
  (32768, 1),
  (42, 0),
  (12345, 0),
  (30029, 0),
  (53058, 1),
  (5598, 0),
  (59045, 1),
  (7087, 0),
  (56097, 1),
  (44186, 1),
  (13938, 0),
  (27145, 0),
  (21887, 0),
  (38365, 1),
  (8638, 0),
  (15015, 0),
  (22917, 0),
  (32322, 0),
  (5231, 0),
  (45075, 1),
  (53435, 1),
  (47827, 1),
  (60338, 1),
  (59257, 1),
  (48609, 1),
  (31096, 0),
  (48173, 1),
  (42700, 1),
  (36195, 1),
  (62973, 1),
  (20584, 0),
  (46057, 1),
  (46740, 1),
  (12565, 0),
  (46982, 1),
]

end SP1Clean.WitnessTests
