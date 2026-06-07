import SP1Clean.Foundations.Channels

/-! # `SP1Clean.ShiftRightChip` — binary-flag selectors & byte-channel padding (shared field lemmas)

The ShiftRight chip dispatches a single row across four RV64 variants (SRL/SRA/SRLW/SRAW) selected by
four binary flags whose four-way sum is itself binary. The soundness proof repeatedly needs the
field-arithmetic consequences of that one-hot/co-one-hot structure (`single_flag`, `srlw_sraw_gate`,
`pair_flag`), plus the byte-range pull discharges (`byteReqPad`, `byteRowSpec_range_val`).

All of these are stated over **plain `ZMod p` field elements** / a single byte-table row — no
`Environment`/circuit context — so the case analysis is elaborated **once, in a small context** instead
of inside the giant `circuit_proof_start` chip goal (the `BranchChip/Decision.lean` convention). Split
out of `Formal.lean` so the soundness/completeness proofs read against named lemmas. -/

namespace SP1Clean.ShiftRightChip

open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

omit [Fact (2 ^ 17 < p)] in
/-- A byte-range pull's padding requirement on the `toRawGated` channel: the gate `s` is binary, so the
two requirement antecedents `-s ≠ -1` (⟹ `s ≠ 1`) and `-s ≠ 0` (⟹ `s ≠ 0`) are jointly contradictory —
the value is passed **raw** (no `s * v` fold) and padding owes nothing. Discharges each of the nine
`InteractSpec` byte pulls' `Channel.gatedReceive` requirements (`binary_gate_req_vacuous`). -/
lemma byteReqPad {s v w : ZMod p} {data : ProverData (ZMod p)}
    (hs : s * (s + -1) = 0) :
    ¬ -s = -1 → ¬ -s = 0 → byteChannel.Guarantees (⟨6, v, w, 0⟩ : ByteRow (ZMod p)) data :=
  Channels.binary_gate_req_vacuous (bool_of_mul_pred hs) _

/-- Extract the `Range` bound `x.val < 2 ^ w.val` from a byte-table membership `⟨6, x, w, 0⟩` with a
**symbolic** width column `w` (the general-width form of `byteRowSpec_range`, whose `w` is a `Nat` cast).
The `opcode = 6` column pins the `ByteOpcode` to `Range` (`cast_le6_inj`), whose `constrain` is exactly the
bound. Used to read the `lower/higher_limb` ranges off the shift chip's byte-pull guarantees. -/
lemma byteRowSpec_range_val {x w : ZMod p}
    (h : ByteRowSpec (⟨6, x, w, 0⟩ : ByteRow (ZMod p))) : x.val < 2 ^ w.val := by
  obtain ⟨op, hop, hc⟩ := h
  have hk : op.idx = 6 := cast_le6_inj (by cases op <;> decide) (by norm_num) (by rw [hop]; norm_cast)
  cases op <;> simp only [ByteOpcode.idx] at hk <;>
    first
      | omega
      | (simp only [ByteOpcode.constrain] at hc; exact hc)

/-- **Single-op selection.** With one variant flag `a = 1`, the other three binary flags `b, c, d` whose
four-way sum is binary are all `0` (the sum is `1`, and `1 + b + c + d = 1` forces `b = c = d = 0`). Used
by each variant `Spec` conjunct to zero out the off-variant flags. -/
lemma single_flag {a b c d : ZMod p} (ha : a = 1)
    (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1) (hd : d = 0 ∨ d = 1)
    (hsum : a + b + c + d = 0 ∨ a + b + c + d = 1) : b = 0 ∧ c = 0 ∧ d = 0 := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have hva : a.val = 1 := by rw [ha]; exact ZMod.val_one p
  have vb : b.val ≤ 1 := by rcases hb with rfl | rfl <;> simp [ZMod.val_zero, ZMod.val_one]
  have vc : c.val ≤ 1 := by rcases hc with rfl | rfl <;> simp [ZMod.val_zero, ZMod.val_one]
  have vd : d.val ≤ 1 := by rcases hd with rfl | rfl <;> simp [ZMod.val_zero, ZMod.val_one]
  have e1 : (a + b).val = 1 + b.val := by
    rw [ZMod.val_add_of_lt, hva]; omega
  have e2 : (a + b + c).val = 1 + b.val + c.val := by
    rw [ZMod.val_add_of_lt, e1]; omega
  have e3 : (a + b + c + d).val = 1 + b.val + c.val + d.val := by
    rw [ZMod.val_add_of_lt, e2]; omega
  rcases hsum with h | h
  · exact absurd (congrArg ZMod.val h) (by rw [e3, ZMod.val_zero]; omega)
  · have hv := congrArg ZMod.val h; rw [e3, ZMod.val_one] at hv
    exact ⟨(ZMod.val_eq_zero b).mp (by omega), (ZMod.val_eq_zero c).mp (by omega),
      (ZMod.val_eq_zero d).mp (by omega)⟩

/-- The `srw_msb` gate `c + d = is_srlw + is_sraw = 1` (a word-variant row) forces the two 64-bit-shift
flags `a = is_srl`, `b = is_sra` to `0` and pins the full flag-sum to `1` — the "co-`single_flag`" used to
discharge `msb3A`'s `a[1] < 2^16` obligation without re-entering the per-variant `Spec` context. -/
lemma srlw_sraw_gate {a b c d : ZMod p}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1) (hd : d = 0 ∨ d = 1)
    (hsum : a + b + c + d = 0 ∨ a + b + c + d = 1) (hcd : c + d = 1) :
    a = 0 ∧ b = 0 ∧ a + b + c + d = 1 := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have va : a.val ≤ 1 := by rcases ha with rfl | rfl <;> simp [ZMod.val_zero, ZMod.val_one]
  have vb : b.val ≤ 1 := by rcases hb with rfl | rfl <;> simp [ZMod.val_zero, ZMod.val_one]
  have vc : c.val ≤ 1 := by rcases hc with rfl | rfl <;> simp [ZMod.val_zero, ZMod.val_one]
  have vd : d.val ≤ 1 := by rcases hd with rfl | rfl <;> simp [ZMod.val_zero, ZMod.val_one]
  have e1 : (a + b).val = a.val + b.val := by rw [ZMod.val_add_of_lt]; omega
  have e2 : (a + b + c).val = a.val + b.val + c.val := by rw [ZMod.val_add_of_lt, e1]; omega
  have e3 : (a + b + c + d).val = a.val + b.val + c.val + d.val := by
    rw [ZMod.val_add_of_lt, e2]; omega
  have ecd : (c + d).val = c.val + d.val := by rw [ZMod.val_add_of_lt]; omega
  have hcd1 : c.val + d.val = 1 := by rw [← ecd, hcd]; exact ZMod.val_one p
  have hsum1 : a.val + b.val + c.val + d.val = 1 := by
    rcases hsum with h | h
    · exfalso; have hh := congrArg ZMod.val h; rw [e3, ZMod.val_zero] at hh; omega
    · have hh := congrArg ZMod.val h; rw [e3, ZMod.val_one] at hh; omega
  refine ⟨(ZMod.val_eq_zero a).mp (by omega), (ZMod.val_eq_zero b).mp (by omega), ?_⟩
  rcases hsum with h | h
  · exfalso; have hh := congrArg ZMod.val h; rw [e3, ZMod.val_zero] at hh; omega
  · exact h

/-- Four binary flags with a binary sum ⇒ the pair `c + d` is itself binary — discharges `msb3A`'s
`is_srlw + is_sraw ∈ {0,1}` half. -/
lemma pair_flag {a b c d : ZMod p}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1) (hd : d = 0 ∨ d = 1)
    (hsum : a + b + c + d = 0 ∨ a + b + c + d = 1) : c + d = 0 ∨ c + d = 1 := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have va : a.val ≤ 1 := by rcases ha with rfl | rfl <;> simp [ZMod.val_zero, ZMod.val_one]
  have vb : b.val ≤ 1 := by rcases hb with rfl | rfl <;> simp [ZMod.val_zero, ZMod.val_one]
  have vc : c.val ≤ 1 := by rcases hc with rfl | rfl <;> simp [ZMod.val_zero, ZMod.val_one]
  have vd : d.val ≤ 1 := by rcases hd with rfl | rfl <;> simp [ZMod.val_zero, ZMod.val_one]
  have e1 : (a + b).val = a.val + b.val := by rw [ZMod.val_add_of_lt]; omega
  have e2 : (a + b + c).val = a.val + b.val + c.val := by rw [ZMod.val_add_of_lt, e1]; omega
  have e3 : (a + b + c + d).val = a.val + b.val + c.val + d.val := by
    rw [ZMod.val_add_of_lt, e2]; omega
  have hcd2 : c.val + d.val ≤ 1 := by
    rcases hsum with h | h
    · have hh := congrArg ZMod.val h; rw [e3, ZMod.val_zero] at hh; omega
    · have hh := congrArg ZMod.val h; rw [e3, ZMod.val_one] at hh; omega
  rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
  · left; ring
  · right; ring
  · right; ring
  · exfalso; simp only [ZMod.val_one] at hcd2; omega

end SP1Clean.ShiftRightChip
