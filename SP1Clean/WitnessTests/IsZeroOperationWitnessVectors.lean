import SP1Clean.Foundations.Word

/-! # AUTO-GENERATED — do not edit by hand.

Witness-generation conformance vectors for SP1's `IsZeroOperation`, dumped from the **real**
`IsZeroOperation::populate` by `update_extracted.py` (the `witness_vectors` binary,
`--operation IsZeroOperation`). Unlike the constraint (`eval`) extraction, `populate` is native
imperative code and cannot be symbolically extracted; these vectors instead tie the Lean
witness function to the Rust source by **conformance** (agreement on the sampled inputs —
edge cases + a seeded LCG — not an all-inputs proof). Each entry is `(a_field, inverse, result)`. The
check lives in `SP1Clean/WitnessTests/IsZeroOperationWitness.lean`. Regenerate with
`SP1_DIR=… python3 update_extracted.py`. -/

namespace SP1Clean.WitnessTests
open SP1Clean

set_option linter.all false  -- auto-generated: skip linters

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 64000 in
/-- 47 conformance vectors for `IsZeroOperation` (`(a_field, inverse, result)`). -/
def IsZeroOperationWitnessVectors : List (ℕ × ℕ × ℕ) := [
  (0, 0, 1),
  (1, 1, 0),
  (2130706432, 2130706432, 0),
  (0, 0, 1),
  (1, 1, 0),
  (65535, 845584999, 0),
  (65536, 2130673921, 0),
  (33554429, 1568823013, 0),
  (402124771, 1412061464, 0),
  (201062386, 1081934337, 0),
  (201062385, 1083216884, 0),
  (368570342, 511792869, 0),
  (33554429, 1568823013, 0),
  (42, 1572664272, 0),
  (1234567890, 1138436308, 0),
  (1499102127, 704092636, 0),
  (1029102645, 936895377, 0),
  (586603739, 107049376, 0),
  (1296695632, 26410081, 0),
  (1939261898, 1333026660, 0),
  (576450950, 1716289993, 0),
  (1021641046, 2107872107, 0),
  (1124726018, 1088359373, 0),
  (845428854, 197389531, 0),
  (2015421173, 759328148, 0),
  (707060026, 1729914598, 0),
  (1686979369, 1195663, 0),
  (62068399, 1822089349, 0),
  (1480093297, 536221425, 0),
  (1708912919, 430627903, 0),
  (116822495, 1835407863, 0),
  (570151892, 1740610897, 0),
  (2068334617, 381426443, 0),
  (1032782297, 485797034, 0),
  (661167964, 1945077832, 0),
  (1344308801, 1963060128, 0),
  (1425450856, 749778175, 0),
  (1984900018, 1762305554, 0),
  (513714112, 997879770, 0),
  (2032986559, 1979980977, 0),
  (1998344821, 1950888349, 0),
  (473333143, 1728743134, 0),
  (1964135573, 801450489, 0),
  (1835453917, 1777795991, 0),
  (1772524630, 1392417396, 0),
  (2071263228, 997952451, 0),
  (288952997, 1373180003, 0),
]

end SP1Clean.WitnessTests
