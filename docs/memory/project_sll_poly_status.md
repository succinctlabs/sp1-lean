---
name: shiftleft-poly-migration-status-as-of-2026-05-12
description: spec.sll_poly fully closed via 5-layer helper architecture; spec.slli_poly + spec.sllw_poly + spec.slliw_poly + chip-level correct_* stubs remain
metadata: 
  node_type: memory
  type: project
  originSessionId: d13f597f-47d0-47b7-9a65-f20721f2701f
---

**Current state of ShiftLeft `_poly` migration:**

`spec.sll_poly` is **fully closed**. All 64 sub-cases (4 byte-shifts × 16 within-byte cb patterns) close via the helper architecture in `SP1Chips/ShiftLeft/Common.lean`.

**Helpers in place** (Common.lean, ~450 net lines added):
- `sll_within_byte_shift_poly` (byte_shift=0 core)
- `sll_within_byte_shift_1_poly` (byte_shift=1 core)
- `sll_within_byte_shift_2_poly` (byte_shift=2 core)
- `sll_within_byte_shift_3_poly` (byte_shift=3 core)
- `sll_close_cb4cb5_zero_case` (cb4=cb5=0 wrapper)
- `sll_close_cb4cb5_one_zero_case` (cb4=1, cb5=0 wrapper)
- `sll_close_cb4cb5_zero_one_case` (cb4=0, cb5=1 wrapper)
- `sll_close_cb4cb5_one_one_case` (cb4=cb5=1 wrapper)

**Remaining sorries in `SP1Chips/ShiftLeft/Sll.lean`** (3 of them):
- Line 14: `spec.sll` (Fin-KB version with `stop` marker — pre-existing, intentional)
- Line ~1177: `spec.slli` (Fin-KB version, similar)
- Line ~1188: `spec.slli_poly` (the `_poly` immediate-shift variant — out of scope for current task)

**Pickup for next session:**

1. **`spec.slli_poly`** — immediate-shift variant of SLL. Should mostly reuse the same 8 helpers from Common.lean. Differences from `spec.sll_poly`:
   - `imm = 1` instead of `imm = 0` (the immediate path).
   - `c0..c3` comes from `Main[21..24]` not `Main[25..28]` (the immediate decode path uses different limbs).
   - The constraint structure for c0..c3 differs: `c1 = c2 = c3 = 0` and `c0` carries the shift amount.
   - Otherwise the within-byte and byte-shift split is identical.

2. **`SP1Chips/ShiftLeft/Sllw.lean`** — `spec.sllw_poly` and `spec.slliw_poly` (32-bit word-shift variants). 
   - Operates on lower 32 bits only; output truncated.
   - Within-byte and byte_shift structure is similar but with a 32-bit output mask.
   - The 8 helpers in Common.lean may need adaptation OR new variants for the truncation.

3. **`SP1Chips/ShiftLeftChip.lean`** — chip-level `correct_*_poly` stubs (`correct_sll_poly`, `correct_slli_poly`, `correct_sllw_poly`, `correct_slliw_poly`). These build on `spec.*_poly` and follow the AddChip / MulChip mechanical pattern.

4. **Phase 6 collapse** — once all `_poly` variants close, delete the Fin-KB `spec.sll`, `spec.slli`, `spec.sllw`, `spec.slliw` proofs (currently still in the file with `stop` markers).

**Key reusable infrastructure** (built this session):

The 5-layer helper architecture in `Common.lean:108-757`:
- **Within-byte helpers** (lines ~145-525): one per byte_shift k, each proving the algebraic identity `(byte_shift_k LHS).toNat = (b.toNat * M * 2^(16k)) % 2^64`. Closes via `linear_combination (... * 2^(16k)) * h_MN` + `conv_rhs => rw [Nat.mul_assoc, Nat.mod_mul_mod, ← Nat.mul_assoc]` + `Nat.add_mul_mod_self_right`.
- **Case wrappers** (lines ~234-757): one per (cb4, cb5) selector, bridges `<<<` to `*`, applies cancel_mul_65536_poly, normalizes bounds, calls the matching within-byte helper.

**Call-site pattern** (~10 lines per sub-case):
```lean
· -- cb pattern: S=<shift>, M=<2^S>, N=<2^(16-S)>
  have hv0123_val : v0123.val = M := by
    have h : v0123 = M := by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; ring
    rw [h]; exact val_M_zmod_p
  exact sll_close_cb4cb5_<branch>_case S (by omega) M N (by decide) (by omega) rfl rfl
    hv0123_val
    (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
    (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
    lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
    h_b0_dec h_b1_dec h_b2_dec h_b3_dec
```

**File line counts after this session:**
- `Sll.lean`: 1294 lines (was 762 at session start; +532 for 3 byte-shift branches with 64 sub-cases total)
- `Common.lean`: 1209 lines (was 757; +452 for 6 new helpers and bug fixes to existing)

**Build state:** Common.lean: 0 errors, 0 sorries. Sll.lean: 0 errors, 3 sorry warnings (all out-of-scope for `spec.sll_poly`).
