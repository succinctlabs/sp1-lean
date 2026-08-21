import SP1Clean.FormalModel.TraceGen.Inputs

/-! # Trace generation — the reader contracts of a built row

**The rollout payload.** A chip's `ProverAssumptions` is, almost entirely, the semantic `Spec`s of
the reader families whose column blocks the row threads: the `CPUState` clock block and one
`RegisterAccessCols` block per register operand. Those blocks are *shared* — the builder
(`Inputs.lean`) is the same for every chip of a family, and for the `CPUState` block, the same for
every chip in the machine — so proving their contracts once, **stated over the builder's
outputs**, discharges the bulk of every chip's `ProverAssumptions` verbatim.

Everything here is derived from `RTypeEvent.WellFormed`'s plain-`ℕ` execution facts. Nothing in
this file asks the trace for a range check, a limb bound, or a difference decomposition: those are
consequences of how the builder splits a clock, and that is the whole point of the layer.

## The two theorems that do the work

* `cpuState_spec` — from `clk ≡ 1 (mod 8)` alone (SP1's `CLK_INC = 8`), the built `CPUState`
  block satisfies `Readers.CPUState.Spec` at *any* `next_pc`, `clk_inc` and `is_real`. The content
  is the two byte-range facts the state row's byte-bus pulls consume: `(clk_0_16 - 1) / 8 < 2^13`
  and `clk_16_24 < 2^8`.
* `registerAccessCols_spec` — from "the previous access is strictly earlier" (plus the clock
  window, which `clk_window_of_mod` gets for free from the same `CLK_INC = 8` discipline), the
  built access block satisfies `Readers.RegisterAccessCols.Spec` at the operand's access clock.
  The content is the timestamp difference's two-byte decomposition, which is where the 24-bit
  clock arithmetic has to be non-wrapping in the field — hence this layer's
  `Fact (2 ^ 24 < p)`.

`clkTarget_eq` is the small bridge between the two: a chip states its operand access clocks as
`state.clk_0_16 + state.clk_16_24 * 65536 + 4` (a *field* expression over the `CPUState` block),
and `registerAccessCols_spec` wants that to be the cast of the `ℕ` clock `clk % 2^24 + 4`. The
three `registerAccessCols_spec_op{A,B,C}` corollaries package that bridge at the three
`MemoryAccessPosition` offsets, so a chip cites them and nothing else. -/

namespace SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## `ℕ`-level clock arithmetic -/

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- The 24-bit low clock is exactly what the `CPUState` block's two limbs recombine to
(`clk_0_16 + clk_16_24 * 65536`), which is how SP1's `CPUState::populate` splits it. -/
lemma clk_split (clk : ℕ) : clk % 2 ^ 24 = clk % 2 ^ 16 + clk >>> 16 % 256 * 65536 := by
  rw [Nat.shiftRight_eq_div_pow]
  omega

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- **The window fact is free.** SP1's clock discipline already keeps a row's register accesses
(at `clk + 1 … clk + 4`) inside the current 24-bit window: `8 ∣ 2^24`, so `clk ≡ 1 (mod 8)`
forces `clk % 2^24 ≤ 2^24 - 7`. This is why `RTypeEvent.WellFormed` carries no window conjunct. -/
lemma clk_window_of_mod {clk : ℕ} (h : clk % 8 = 1) : clk % 2 ^ 24 + 4 < 2 ^ 24 := by
  have h1 : clk % 2 ^ 24 % 8 = 1 := by
    rw [Nat.mod_mod_of_dvd clk (by norm_num : (8 : ℕ) ∣ 2 ^ 24)]; exact h
  have h2 : clk % 2 ^ 24 < 2 ^ 24 := Nat.mod_lt _ (by norm_num)
  omega

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- **The ordering fact.** The committed previous-access clock is strictly below this access's
clock: within one 24-bit window that is the trace's timestamp ordering, and across windows the
previous clock is committed as `0`, which is below any access clock of a positive offset. -/
lemma prevLowOf_lt {prevTs clk k : ℕ} (hk0 : 0 < k) (hk : k ≤ 4)
    (hwin : clk % 2 ^ 24 + 4 < 2 ^ 24) (hprev : prevTs < clk + k) :
    prevLowOf prevTs (clk + k) < clk % 2 ^ 24 + k := by
  unfold prevLowOf
  split
  · rename_i hw
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow] at hw
    omega
  · omega

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- A committed previous-access clock is a 24-bit value, in both branches of `prevLowOf`. -/
lemma prevLowOf_lt_window (prevTs currTs : ℕ) : prevLowOf prevTs currTs < 2 ^ 24 := by
  unfold prevLowOf
  split <;> omega

/-! ## Word limbs -/

/-- Every limb of a built word is a genuine u16 — by construction, for *any* natural number: the
builder commits residues. This is why `RTypeEvent.WellFormed` owes no limb bounds. -/
lemma wordOfNat_isU64 (n : ℕ) : Word.isU64 (wordOfNat (p := p) n) := by
  have hp : 2 ^ 24 < p := Fact.out
  refine Word.isU64_of_cases ?_ ?_ ?_ ?_ <;>
    · simp only [wordOfNat, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
      rw [ZMod.val_natCast_of_lt (by omega)]
      omega

/-! ## The `CPUState` block -/

/-- **The state block's contract.** SP1's clock discipline (`clk ≡ 1 mod 8`, from `CLK_INC = 8`)
is the only thing a real trace has to supply: the two byte-range facts the `CPUState` row owes are
then properties of the limb split. Stated at an arbitrary `next_pc`/`clk_inc`/`is_real`, so every
chip in the machine — straight-line or branching — uses this one lemma. -/
theorem cpuState_spec (clk pc : ℕ) (h : clk % 8 = 1) (next_pc : fields 3 (ZMod p))
    (clk_inc is_real : ZMod p) :
    Readers.CPUState.Spec
      { cols := cpuStateCols clk pc, next_pc := next_pc, clk_inc := clk_inc,
        is_real := is_real } := by
  have hp : 2 ^ 24 < p := Fact.out
  have hmod : clk % 2 ^ 16 % 8 = 1 := by
    rw [Nat.mod_mod_of_dvd clk (by norm_num : (8 : ℕ) ∣ 2 ^ 16)]; exact h
  have hlt : clk % 2 ^ 16 < 2 ^ 16 := Nat.mod_lt _ (by norm_num)
  obtain ⟨q, hq, hqlt⟩ : ∃ q, clk % 2 ^ 16 = 8 * q + 1 ∧ q < 2 ^ 13 :=
    ⟨clk % 2 ^ 16 / 8, by omega, by omega⟩
  intro _
  refine ⟨?_, ?_⟩
  · show ((((clk % 2 ^ 16 : ℕ) : ZMod p) - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13
    rw [hq]
    push_cast
    rw [show (8 : ZMod p) * (q : ZMod p) + 1 - 1 = (q : ZMod p) * 8 from by ring, mul_assoc,
      mul_inv_cancel₀ (val_8_ne_zero (p := p)), mul_one, ZMod.val_natCast_of_lt (by omega)]
    exact hqlt
  · show (((clk >>> 16 % 256 : ℕ) : ZMod p)).val < 2 ^ 8
    rw [ZMod.val_natCast_of_lt (by omega)]
    omega

omit [Fact p.Prime] in
/-- The program-counter limbs of a built state block are u16s — again by construction, for any
`pc`. (The chips' `ProverAssumptions` ask for these alongside the destination-index bound, both
`is_real`-gated: they are the decode facts the Program-bus fetch pull carries.) -/
lemma cpuStateCols_pc_val_lt (clk pc : ℕ) :
    ((cpuStateCols (p := p) clk pc).pc[0]).val < 2 ^ 16 ∧
      ((cpuStateCols (p := p) clk pc).pc[1]).val < 2 ^ 16 ∧
      ((cpuStateCols (p := p) clk pc).pc[2]).val < 2 ^ 16 := by
  have hp : 2 ^ 24 < p := Fact.out
  refine ⟨?_, ?_, ?_⟩ <;>
    · simp only [cpuStateCols_pc_zero, cpuStateCols_pc_one, cpuStateCols_pc_two]
      rw [ZMod.val_natCast_of_lt (by omega)]
      omega

omit [Fact (2 ^ 24 < p)] in
/-- The operand access clock a chip passes to a reader — `clk_0_16 + clk_16_24 * 65536 + k`, a
field expression over the built state block — is the cast of the `ℕ` clock `clk % 2^24 + k`. -/
theorem clkTarget_eq (clk pc k : ℕ) :
    (cpuStateCols (p := p) clk pc).clk_0_16 + (cpuStateCols (p := p) clk pc).clk_16_24 * 65536
        + (k : ZMod p) = ((clk % 2 ^ 24 + k : ℕ) : ZMod p) := by
  rw [cpuStateCols_clk_0_16, cpuStateCols_clk_16_24, clk_split clk]
  push_cast
  ring

/-! ## The `RegisterAccessCols` blocks -/

/-- **The access block's contract.** The timestamp difference `clk_target - prev_low - 1` splits
into a 16-bit low limb and an 8-bit high part — the two byte-bus range checks SP1's
`RegisterAccessTimestamp` owes — as soon as the previous access is strictly earlier (`hprev`) and
this row's accesses stay inside the current 24-bit clock window (`hwin`, which the three
corollaries below get from the clock discipline alone). Nothing else about the event is needed,
and in particular the *value* the block commits is irrelevant: SP1 imposes no local
well-formedness on a register read-prior value — its `isU64` is received from the writer over the
offline-memory argument.

`k` is the operand's `MemoryAccessPosition` offset (`4` for the `op_a` write, `3`/`2` for the
`op_b`/`op_c` reads); `clkTarget` is taken abstractly with `hct` so that the chip can supply it in
whatever field spelling its `ProverAssumptions` uses (`clkTarget_eq` is the bridge). -/
theorem registerAccessCols_spec {value prevTs clk k : ℕ} {is_real clkTarget : ZMod p}
    (hk0 : 0 < k) (hk : k ≤ 4) (hwin : clk % 2 ^ 24 + 4 < 2 ^ 24) (hprev : prevTs < clk + k)
    (hct : clkTarget = ((clk % 2 ^ 24 + k : ℕ) : ZMod p)) :
    Readers.RegisterAccessCols.Spec
      { cols := registerAccessCols value prevTs (clk + k), is_real := is_real,
        clk_target := clkTarget } := by
  have hp : 2 ^ 24 < p := Fact.out
  have hprevLow : prevLowOf prevTs (clk + k) < clk % 2 ^ 24 + k :=
    prevLowOf_lt hk0 hk hwin hprev
  have hcurr : (clk + k) % 2 ^ 24 = clk % 2 ^ 24 + k := by omega
  obtain ⟨d, hd, hdlt⟩ :
      ∃ d, clk % 2 ^ 24 + k = prevLowOf prevTs (clk + k) + 1 + d ∧ d < 2 ^ 24 :=
    ⟨clk % 2 ^ 24 + k - prevLowOf prevTs (clk + k) - 1, by omega, by omega⟩
  have hdiff : diffLowOf prevTs (clk + k) = d % 2 ^ 16 := by
    unfold diffLowOf; rw [hcurr]; omega
  intro _
  refine ⟨?_, ?_⟩
  · show (((diffLowOf prevTs (clk + k) : ℕ) : ZMod p)).val < 2 ^ 16
    rw [hdiff, ZMod.val_natCast_of_lt (by omega)]
    omega
  · show ((clkTarget - ((prevLowOf prevTs (clk + k) : ℕ) : ZMod p) - 1
        - ((diffLowOf prevTs (clk + k) : ℕ) : ZMod p)) * (65536 : ZMod p)⁻¹).val < 2 ^ 8
    have hcast : ((d : ℕ) : ZMod p)
        = ((d % 2 ^ 16 : ℕ) : ZMod p) + ((d / 2 ^ 16 : ℕ) : ZMod p) * 65536 := by
      conv_lhs => rw [show d = d % 2 ^ 16 + d / 2 ^ 16 * 65536 from by omega]
      push_cast
      ring
    have hexpr : clkTarget - ((prevLowOf prevTs (clk + k) : ℕ) : ZMod p) - 1
        - ((diffLowOf prevTs (clk + k) : ℕ) : ZMod p)
          = ((d / 2 ^ 16 : ℕ) : ZMod p) * 65536 := by
      rw [hct, hdiff, hd]
      push_cast
      linear_combination hcast
    rw [hexpr, mul_assoc, mul_inv_cancel₀ (val_65536_ne_zero (p := p)), mul_one,
      ZMod.val_natCast_of_lt (by omega)]
    omega

/-! ### The three operand corollaries

The form a chip actually meets: the access clock spelled as the chip spells it — the *field*
expression `state.clk_0_16 + state.clk_16_24 * 65536 + <offset>` over the built state block, at
each `MemoryAccessPosition` offset. Every R-type chip's `ProverAssumptions` uses exactly these
three; the immediate-capable families reuse them unchanged (only the `is_real` gate differs, and
it is arbitrary here). -/

/-- The `op_a` register **write**, at `MemoryAccessPosition::A = 4`. -/
theorem registerAccessCols_spec_opA {value prevTs clk pc : ℕ} {is_real : ZMod p}
    (hclk : clk % 8 = 1) (hprev : prevTs < clk + 4) :
    Readers.RegisterAccessCols.Spec
      { cols := registerAccessCols value prevTs (clk + 4), is_real := is_real,
        clk_target := (cpuStateCols (p := p) clk pc).clk_0_16
          + (cpuStateCols (p := p) clk pc).clk_16_24 * 65536 + 4 } :=
  registerAccessCols_spec (by norm_num) (by norm_num) (clk_window_of_mod hclk) hprev
    (by simpa using clkTarget_eq (p := p) clk pc 4)

/-- The `op_b` register **read**, at `MemoryAccessPosition::B = 3`. -/
theorem registerAccessCols_spec_opB {value prevTs clk pc : ℕ} {is_real : ZMod p}
    (hclk : clk % 8 = 1) (hprev : prevTs < clk + 3) :
    Readers.RegisterAccessCols.Spec
      { cols := registerAccessCols value prevTs (clk + 3), is_real := is_real,
        clk_target := (cpuStateCols (p := p) clk pc).clk_0_16
          + (cpuStateCols (p := p) clk pc).clk_16_24 * 65536 + 3 } :=
  registerAccessCols_spec (by norm_num) (by norm_num) (clk_window_of_mod hclk) hprev
    (by simpa using clkTarget_eq (p := p) clk pc 3)

/-- The `op_c` register **read**, at `MemoryAccessPosition::C = 2`. -/
theorem registerAccessCols_spec_opC {value prevTs clk pc : ℕ} {is_real : ZMod p}
    (hclk : clk % 8 = 1) (hprev : prevTs < clk + 2) :
    Readers.RegisterAccessCols.Spec
      { cols := registerAccessCols value prevTs (clk + 2), is_real := is_real,
        clk_target := (cpuStateCols (p := p) clk pc).clk_0_16
          + (cpuStateCols (p := p) clk pc).clk_16_24 * 65536 + 2 } :=
  registerAccessCols_spec (by norm_num) (by norm_num) (clk_window_of_mod hclk) hprev
    (by simpa using clkTarget_eq (p := p) clk pc 2)

omit [Fact p.Prime] in
/-- A built access block's committed previous-access clock is a 24-bit value — the `ClkBound` half
of the memory channel's guarantees, which a pull's completeness has to exhibit. Derived, not
assumed: `prevLowOf` is either a 24-bit residue or zero. -/
theorem registerAccessCols_prevLow_val_lt (value prevTs currTs : ℕ) :
    ((registerAccessCols (p := p) value prevTs currTs).access_timestamp.prev_low).val < 2 ^ 24 := by
  have hp : 2 ^ 24 < p := Fact.out
  have h := prevLowOf_lt_window prevTs currTs
  rw [registerAccessCols_prev_low, ZMod.val_natCast_of_lt (by omega)]
  exact h

/-! ## The `RTypeReader` block -/

omit [Fact p.Prime] in
/-- The committed destination-register index of a built R-type block is `< 32` — the decode bound
the chips' `ProverAssumptions` ask for, from the event's own index bound. -/
lemma rTypeReaderCols_op_a_val_lt {e : RTypeEvent} (h : e.opA < 32) :
    ((rTypeReaderCols (p := p) e).op_a).val < 32 := by
  have hp : 2 ^ 24 < p := Fact.out
  rw [rTypeReaderCols_op_a, ZMod.val_natCast_of_lt (by omega)]
  exact h

omit [Fact (2 ^ 24 < p)] in
/-- A built R-type block's `op_a_0` flag is `0` exactly when the destination is not `x0`. -/
lemma rTypeReaderCols_op_a_0_eq_zero {e : RTypeEvent} (h : e.opA ≠ 0) :
    (rTypeReaderCols (p := p) e).op_a_0 = 0 := by
  rw [rTypeReaderCols_op_a_0, if_neg h]

/-! ## The sibling adapter blocks

The `op_a` half of every adapter is the same block — a destination index, its write access block,
and the `rd = x0` flag — so each family gets the same pair of one-line decode lemmas. The families
differ only in the `op_c` slot, which is where `ALUTypeReader` needs two extra lemmas (its `op_c`
block is row-dependent) and `ITypeReader`/`JTypeReader` need none (their `op_c` is a committed
immediate word, whose `isU64` is `wordOfNat_isU64`). -/

omit [Fact p.Prime] in
/-- The committed destination-register index of a built I-type block is `< 32`. -/
lemma iTypeReaderCols_op_a_val_lt {e : ITypeEvent} (h : e.opA < 32) :
    ((iTypeReaderCols (p := p) e).op_a).val < 32 := by
  have hp : 2 ^ 24 < p := Fact.out
  rw [iTypeReaderCols_op_a, ZMod.val_natCast_of_lt (by omega)]
  exact h

omit [Fact (2 ^ 24 < p)] in
/-- A built I-type block's `op_a_0` flag is `0` exactly when the destination is not `x0`. -/
lemma iTypeReaderCols_op_a_0_eq_zero {e : ITypeEvent} (h : e.opA ≠ 0) :
    (iTypeReaderCols (p := p) e).op_a_0 = 0 := by
  rw [iTypeReaderCols_op_a_0, if_neg h]

omit [Fact p.Prime] in
/-- The committed destination-register index of a built ALU-type block is `< 32`. -/
lemma aluTypeReaderCols_op_a_val_lt {e : ALUTypeEvent} (h : e.opA < 32) :
    ((aluTypeReaderCols (p := p) e).op_a).val < 32 := by
  have hp : 2 ^ 24 < p := Fact.out
  rw [aluTypeReaderCols_op_a, ZMod.val_natCast_of_lt (by omega)]
  exact h

omit [Fact (2 ^ 24 < p)] in
/-- A built ALU-type block's `op_a_0` flag is `0` exactly when the destination is not `x0`. -/
lemma aluTypeReaderCols_op_a_0_eq_zero {e : ALUTypeEvent} (h : e.opA ≠ 0) :
    (aluTypeReaderCols (p := p) e).op_a_0 = 0 := by
  rw [aluTypeReaderCols_op_a_0, if_neg h]

/-- The value a built ALU-type `op_c` block commits is a u64 in **both** row forms — the `rs2`
read value on a register row, the copied immediate word on an immediate row. Both are built by
`wordOfNat`, so neither owes the event a limb bound. -/
lemma aluTypeOpCCols_prev_value_isU64 (e : ALUTypeEvent) :
    Word.isU64 (aluTypeOpCCols (p := p) e).prev_value := by
  rw [aluTypeOpCCols]
  split
  · exact wordOfNat_isU64 _
  · rw [registerAccessCols_prev_value]
    exact wordOfNat_isU64 _

omit [Fact p.Prime] in
/-- A built ALU-type `op_c` block's committed previous-access clock is a 24-bit value in both row
forms: the `prevLowOf` residue on a register row, the literal `0` an immediate row is populated
with. -/
lemma aluTypeOpCCols_prevLow_val_lt (e : ALUTypeEvent) :
    ((aluTypeOpCCols (p := p) e).access_timestamp.prev_low).val < 2 ^ 24 := by
  rw [aluTypeOpCCols]
  split
  · simp
  · exact registerAccessCols_prevLow_val_lt _ _ _

omit [Fact p.Prime] in
/-- The committed destination-register index of a built J-type block is `< 32`. -/
lemma jTypeReaderCols_op_a_val_lt {e : JTypeEvent} (h : e.opA < 32) :
    ((jTypeReaderCols (p := p) e).op_a).val < 32 := by
  have hp : 2 ^ 24 < p := Fact.out
  rw [jTypeReaderCols_op_a, ZMod.val_natCast_of_lt (by omega)]
  exact h

omit [Fact (2 ^ 24 < p)] in
/-- A built J-type block's `op_a_0` flag is `0` exactly when the destination is not `x0`. -/
lemma jTypeReaderCols_op_a_0_eq_zero {e : JTypeEvent} (h : e.opA ≠ 0) :
    (jTypeReaderCols (p := p) e).op_a_0 = 0 := by
  rw [jTypeReaderCols_op_a_0, if_neg h]

/-- **The program counter as a word.** The three committed `pc` limbs padded with a zero high limb
form a u64 — the shape `UType` (and `Jal`) feed to their `AddOperation` as the `pc + imm` operand.
Derived from the limb split, like `cpuStateCols_pc_val_lt`, so no event conjunct is spent on it. -/
lemma cpuStateCols_pcWord_isU64 (clk pc : ℕ) :
    Word.isU64 (#v[(cpuStateCols (p := p) clk pc).pc[0], (cpuStateCols (p := p) clk pc).pc[1],
      (cpuStateCols (p := p) clk pc).pc[2], 0] : Word (ZMod p)) := by
  obtain ⟨h0, h1, h2⟩ := cpuStateCols_pc_val_lt (p := p) clk pc
  refine Word.isU64_of_cases ?_ ?_ ?_ ?_ <;>
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, ZMod.val_zero]
  · exact h0
  · exact h1
  · exact h2
  · norm_num

end SP1Clean.TraceGen
