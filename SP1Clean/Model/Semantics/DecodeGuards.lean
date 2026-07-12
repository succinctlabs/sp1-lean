import SP1Clean.Model.Semantics.Decode

/-! # Decode Move 1 — image-guarded row projection (`instrToProgramRow'`)

Consolidation step **C1 / Move 1** (`docs/proposals/2026-07-architecture-consolidation.md` §3.4,
SP-1-validated). The row projection `instrToProgramRow` is total, so its `.MUL`/`.LOAD`/`.STORE` arms
admit *phantom* records the real decoder never emits — the non-canonical `mul_op` (High, Unsigned,
Signed) that aliases MULHSU with a **different** product, and the width-8 unsigned load (LDU, absent on
RV64). Those phantoms are what blocked the MUL / LoadDouble / LoadX0 / StoreDouble inversions (the
`hpin`-unprovable cases) and hence their `advance` obligations.

Here we guard the three arms to the decoder's canonical image (`mulOpCanonical` / `loadWidthOK` /
`storeWidthOK`) via `instrToProgramRow'` — **definitionally a guard wrapper** around `instrToProgramRow`
(so nothing existing changes), on which the projection is injective. The payoff: `instrToProgramRow_inv_mul'`
inverts the MUL arm **without `hpin`** (`mulOp_canonical_inj` supplies the pin from the guard), and
`loadOpcode`/`storeOpcode` are injective on their guarded widths — unblocking all four seam chips.

Move 2 (the ∃I∀s `decodedInROM` hoist + collapsing the 16 `decodes<T>` producers to single-inversion
consumers) builds on this. Ported from the SP-1 spike; axiom-clean. -/

namespace SP1Clean.Soundness.Target

open Sail LeanRV64D LeanRV64D.Functions LeanRV64D.Defs
open SP1Clean.ProgramChip (ProgramRow)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## The image guards -/

/-- The 4 canonical `mul_op` records — exactly the image of `encdec_mul_op_backwards`:
(Low,S,S) = MUL, (High,S,S) = MULH, (High,S,U) = MULHSU, (High,U,U) = MULHU. The 4 others (incl.
(High,U,S), the phantom MULHSU alias with a different product) are never decoded. -/
def mulOpCanonical (m : mul_op) : Bool :=
  match m.result_part, m.signed_rs1, m.signed_rs2 with
  | .Low, .Signed, .Signed => true
  | .High, .Signed, .Signed => true
  | .High, .Signed, .Unsigned => true
  | .High, .Unsigned, .Unsigned => true
  | _, _, _ => false

/-- The LOAD widths the decoder can emit (`valid_load_encdec`, RV64 `xlen_bytes = 8`):
width ∈ {1,2,4} any sign, width 8 only signed (no LDU). -/
def loadWidthOK (width : word_width) (isU : Bool) : Bool :=
  width == 1 || width == 2 || width == 4 || (width == 8 && !isU)

/-- The STORE widths the decoder can emit (`width_enc_backwards` image): {1,2,4,8}. -/
def storeWidthOK (width : word_width) : Bool :=
  width == 1 || width == 2 || width == 4 || width == 8

/-- `instrToProgramRow` with the MUL/LOAD/STORE arms image-guarded (a guard wrapper, definitionally
equal to inlining the guards into the three arms). -/
def instrToProgramRow' (pc : Vector (ZMod p) 3) : instruction → Option (ProgramRow (ZMod p))
  | .MUL (rs2, rs1, rd, m) =>
      if mulOpCanonical m then instrToProgramRow pc (.MUL (rs2, rs1, rd, m)) else none
  | .LOAD (imm, rs1, rd, isU, width) =>
      if loadWidthOK width isU then instrToProgramRow pc (.LOAD (imm, rs1, rd, isU, width)) else none
  | .STORE (imm, rs2, rs1, width) =>
      if storeWidthOK width then instrToProgramRow pc (.STORE (imm, rs2, rs1, width)) else none
  | i => instrToProgramRow pc i

omit [Fact (2 ^ 17 < p)] in
/-- The guards only restrict: a primed projection is an unprimed one. -/
theorem instrToProgramRow'_some {pc : Vector (ZMod p) 3} {i : instruction}
    {row : ProgramRow (ZMod p)}
    (h : instrToProgramRow' pc i = some row) : instrToProgramRow pc i = some row := by
  unfold instrToProgramRow' at h
  split at h
  · split at h
    · exact h
    · exact absurd h (by simp)
  · split at h
    · exact h
    · exact absurd h (by simp)
  · split at h
    · exact h
    · exact absurd h (by simp)
  · exact h

omit [Fact (2 ^ 17 < p)] in
/-- Guard extraction at the MUL arm: a primed projection of a `.MUL` forces canonicity. -/
theorem instrToProgramRow'_mul_canonical {pc : Vector (ZMod p) 3} {rs2 rs1 rd : regidx}
    {m : mul_op} {row : ProgramRow (ZMod p)}
    (h : instrToProgramRow' pc (.MUL (rs2, rs1, rd, m)) = some row) :
    mulOpCanonical m = true := by
  cases hcm : mulOpCanonical m with
  | true => rfl
  | false =>
    rw [instrToProgramRow'] at h
    rw [hcm] at h
    simp at h

omit [Fact (2 ^ 17 < p)] in
/-- On concrete constructors the primed projection is unguarded (default arm). -/
theorem instrToProgramRow'_rtype (pc : Vector (ZMod p) 3) (t : regidx × regidx × regidx × rop) :
    instrToProgramRow' pc (.RTYPE t) = instrToProgramRow pc (.RTYPE t) := rfl

/-- `mulOpToOpcode` is injective **on the canonical records** (globally 4-to-1 at MUL, 2-to-1 at
MULHSU — this is the fact the guard buys). -/
theorem mulOp_canonical_inj (m op : mul_op) (hm : mulOpCanonical m = true)
    (hop : mulOpCanonical op = true)
    (h : (mulOpToOpcode m).toNat = (mulOpToOpcode op).toNat) : m = op := by
  rcases m with ⟨a, b, c⟩; rcases op with ⟨a', b', c'⟩
  cases a <;> cases b <;> cases c <;> cases a' <;> cases b' <;> cases c' <;>
    first
      | rfl
      | (exact absurd hm (by decide))
      | (exact absurd hop (by decide))
      | (exact absurd h (by decide))

/-- **The MUL inversion WITHOUT `hpin`.** From the *guarded* projection, the opcode column pins the
whole `mul_op` record for any canonical `op` (in particular MUL and MULHSU, the two `hpin`-unprovable
cases): the guard on the projection side supplies the record's canonicity, and `mulOp_canonical_inj`
finishes. `hcanon` is `by decide`/`rfl` at each concrete opcode. -/
theorem instrToProgramRow_inv_mul' {pc : Vector (ZMod p) 3} {i : instruction}
    {row : ProgramRow (ZMod p)}
    (op : mul_op) (hcanon : mulOpCanonical op = true)
    (h : instrToProgramRow' pc i = some row)
    (hop : row.opcode = ((mulOpToOpcode op).toNat : ZMod p))
    (himm : row.imm_c = (0 : ZMod p)) :
    ∃ rs2 rs1 rd : regidx, i = .MUL (rs2, rs1, rd, op) ∧
      row.op_a = regidxVal rd ∧ row.op_b = #v[regidxVal rs1, 0, 0, 0]
      ∧ row.op_c = #v[regidxVal rs2, 0, 0, 0] := by
  have h0 : instrToProgramRow pc i = some row := instrToProgramRow'_some h
  simp only [instrToProgramRow] at h0
  split at h0
  all_goals first | contradiction | (rw [Option.some.injEq] at h0; subst h0)
  all_goals (try (exact absurd himm one_ne_zero))
  · rename_i rs2 rs1 rd op'
    exact absurd (opcodeCast_inj hop)
      (by cases op' <;> (rcases op with ⟨a, b, c⟩; cases a <;> cases b <;> cases c <;> decide))
  · rename_i rs2 rs1 rd op'
    exact absurd (opcodeCast_inj hop)
      (by cases op' <;> (rcases op with ⟨a, b, c⟩; cases a <;> cases b <;> cases c <;> decide))
  · rename_i rs2 rs1 rd m
    have hg : mulOpCanonical m = true := instrToProgramRow'_mul_canonical h
    obtain rfl : m = op := mulOp_canonical_inj m op hg hcanon (opcodeCast_inj hop)
    exact ⟨rs2, rs1, rd, rfl, rfl, rfl, rfl⟩
  · rename_i rs2 rs1 rd
    exact absurd (opcodeCast_inj hop)
      (by rcases op with ⟨a, b, c⟩; cases a <;> cases b <;> cases c <;> decide)
  · rename_i rs2 rs1 rd isU'
    exact absurd (opcodeCast_inj hop)
      (by cases isU' <;> (rcases op with ⟨a, b, c⟩; cases a <;> cases b <;> cases c <;> decide))
  · rename_i rs2 rs1 rd isU'
    exact absurd (opcodeCast_inj hop)
      (by cases isU' <;> (rcases op with ⟨a, b, c⟩; cases a <;> cases b <;> cases c <;> decide))
  · rename_i rs2 rs1 rd isU'
    exact absurd (opcodeCast_inj hop)
      (by cases isU' <;> (rcases op with ⟨a, b, c⟩; cases a <;> cases b <;> cases c <;> decide))
  · rename_i rs2 rs1 rd isU'
    exact absurd (opcodeCast_inj hop)
      (by cases isU' <;> (rcases op with ⟨a, b, c⟩; cases a <;> cases b <;> cases c <;> decide))

/-- The MULHSU corollary — the previously-blocked case, zero side conditions beyond the columns. -/
theorem instrToProgramRow_inv_mulhsu {pc : Vector (ZMod p) 3} {i : instruction}
    {row : ProgramRow (ZMod p)}
    (h : instrToProgramRow' pc i = some row)
    (hop : row.opcode = ((Opcode.MULHSU).toNat : ZMod p))
    (himm : row.imm_c = (0 : ZMod p)) :
    ∃ rs2 rs1 rd : regidx,
      i = .MUL (rs2, rs1, rd, ⟨.High, .Signed, .Unsigned⟩) ∧
      row.op_a = regidxVal rd ∧ row.op_b = #v[regidxVal rs1, 0, 0, 0]
      ∧ row.op_c = #v[regidxVal rs2, 0, 0, 0] :=
  instrToProgramRow_inv_mul' ⟨.High, .Signed, .Unsigned⟩ rfl h hop himm

/-- The plain-MUL corollary — the 4-preimage case, also unblocked. -/
theorem instrToProgramRow_inv_mul_low {pc : Vector (ZMod p) 3} {i : instruction}
    {row : ProgramRow (ZMod p)}
    (h : instrToProgramRow' pc i = some row)
    (hop : row.opcode = ((Opcode.MUL).toNat : ZMod p))
    (himm : row.imm_c = (0 : ZMod p)) :
    ∃ rs2 rs1 rd : regidx,
      i = .MUL (rs2, rs1, rd, ⟨.Low, .Signed, .Signed⟩) ∧
      row.op_a = regidxVal rd ∧ row.op_b = #v[regidxVal rs1, 0, 0, 0]
      ∧ row.op_c = #v[regidxVal rs2, 0, 0, 0] :=
  instrToProgramRow_inv_mul' ⟨.Low, .Signed, .Signed⟩ rfl h hop himm

/-! ## `loadOpcode` / `storeOpcode` injective on the decoder image -/

theorem loadOpcode_one (isU : Bool) :
    loadOpcode (1 : word_width) isU = if isU then Opcode.LBU else Opcode.LB := by
  unfold loadOpcode; rw [if_pos (beq_self_eq_true (1 : word_width))]

theorem loadOpcode_two (isU : Bool) :
    loadOpcode (2 : word_width) isU = if isU then Opcode.LHU else Opcode.LH := by
  unfold loadOpcode
  rw [if_neg (by decide), if_pos (beq_self_eq_true (2 : word_width))]

theorem loadOpcode_four (isU : Bool) :
    loadOpcode (4 : word_width) isU = if isU then Opcode.LWU else Opcode.LW := by
  unfold loadOpcode
  rw [if_neg (by decide), if_neg (by decide), if_pos (beq_self_eq_true (4 : word_width))]

theorem loadOpcode_eight (isU : Bool) : loadOpcode (8 : word_width) isU = Opcode.LD := by
  unfold loadOpcode
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]

/-- **`loadOpcode` is injective on the decoder image** {(1,*),(2,*),(4,*),(8,false)}. -/
theorem loadOpcode_inj_on_valid (w w' : word_width) (u u' : Bool)
    (hw : loadWidthOK w u = true) (hw' : loadWidthOK w' u' = true)
    (h : (loadOpcode w u).toNat = (loadOpcode w' u').toNat) : w = w' ∧ u = u' := by
  have hc : w = 1 ∨ w = 2 ∨ w = 4 ∨ (w = 8 ∧ u = false) := by
    simp only [loadWidthOK, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
      Bool.not_eq_true'] at hw
    tauto
  have hc' : w' = 1 ∨ w' = 2 ∨ w' = 4 ∨ (w' = 8 ∧ u' = false) := by
    simp only [loadWidthOK, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
      Bool.not_eq_true'] at hw'
    tauto
  rcases hc with rfl | rfl | rfl | ⟨rfl, rfl⟩ <;>
    rcases hc' with rfl | rfl | rfl | ⟨rfl, rfl⟩ <;>
    simp only [loadOpcode_one, loadOpcode_two, loadOpcode_four, loadOpcode_eight] at h <;>
    (try cases u) <;> (try cases u') <;>
    (try simp at h) <;>
    first
      | exact ⟨rfl, rfl⟩
      | exact absurd h (by decide)

/-- `(storeOpcode 8).toNat = 39` (SD) — completing the existing 1/2/4 pin family. -/
theorem storeOpcode_eight_toNat : (storeOpcode (8 : word_width)).toNat = 39 := by
  have hsd : storeOpcode (8 : word_width) = Opcode.SD := by
    unfold storeOpcode
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]
  rw [hsd]; rfl

/-- **`storeOpcode` injective on the guarded widths** — including the previously un-pinnable SD case. -/
theorem storeOpcode_inj_on_valid (w w' : word_width)
    (hw : storeWidthOK w = true) (hw' : storeWidthOK w' = true)
    (h : (storeOpcode w).toNat = (storeOpcode w').toNat) : w = w' := by
  have hc : w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8 := by
    simp only [storeWidthOK, Bool.or_eq_true, beq_iff_eq] at hw; tauto
  have hc' : w' = 1 ∨ w' = 2 ∨ w' = 4 ∨ w' = 8 := by
    simp only [storeWidthOK, Bool.or_eq_true, beq_iff_eq] at hw'; tauto
  rcases hc with rfl | rfl | rfl | rfl <;> rcases hc' with rfl | rfl | rfl | rfl <;>
    simp only [storeOpcode_one_toNat, storeOpcode_two_toNat, storeOpcode_four_toNat,
      storeOpcode_eight_toNat] at h <;>
    first
      | rfl
      | exact absurd h (by decide)

/-- The SD pin — impossible without the guard. -/
theorem storeOpcode_pin_eight (w' : word_width) (hw' : storeWidthOK w' = true)
    (h : (storeOpcode w').toNat = (storeOpcode (8 : word_width)).toNat) : w' = 8 :=
  storeOpcode_inj_on_valid w' 8 hw' (by decide) h

end SP1Clean.Soundness.Target
