# DivRemChip/Soundness conjunct costs — from the 2026-06-10 warm `lake build` log

Not re-measured in the isolated sweep (each is ~25–40 min; excluded via EXCLUDE_RE).
Numbers are from the parallel build (≤5 jobs concurrently elaborating these files on a
14-core machine), so they are contention-inflated upper bounds; the *ranking* is reliable.

| Module | Build wall |
| --- | ---: |
| Chips.DivRemChip.Soundness.Div   | 2354s |
| Chips.DivRemChip.Soundness.Divu  | 2220s |
| Chips.DivRemChip.Soundness.Remu  | 2127s |
| Chips.DivRemChip.Soundness.Rem   | 1901s |
| Chips.DivRemChip.Soundness.Remw  | 1804s |
| Chips.DivRemChip.Soundness.Divw  | 1789s |
| Chips.DivRemChip.Soundness.Divuw | 1474s |
| Chips.DivRemChip.Soundness.Remuw | (scrolled out of captured log tail; same cluster) |

Each file is one conjunct's `GeneralFormalCircuit.Soundness` over the **same** DivRem `main`
at 128M maxHeartbeats — i.e. the chip pays the circuit_proof_start/main-normalization cost
up to 9× (8 conjuncts + Reader). ~4h of the ~2.4h-parallel build was this cluster.
