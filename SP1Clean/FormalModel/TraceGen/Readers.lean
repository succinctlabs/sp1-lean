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

omit [Fact (2 ^ 24 < p)] in
/-- The chip-side spelling of the recombined low clock — `clk_0_16 + clk_16_24 · 2^16` over the
built state block — is the cast of the `ℕ` residue `clk % 2^24`. The `k = 0` companion of
`clkTarget_eq`, which the memory family needs on its own (the RAM access clock is formed *inside*
`MemoryAccess`, from an unshifted `clk_low`). -/
theorem clkLow_eq (clk pc : ℕ) :
    (cpuStateCols (p := p) clk pc).clk_0_16 + (cpuStateCols (p := p) clk pc).clk_16_24 * 65536
      = ((clk % 2 ^ 24 : ℕ) : ZMod p) := by
  rw [cpuStateCols_clk_0_16, cpuStateCols_clk_16_24, clk_split clk]
  push_cast
  ring

/-- The `ℕ` value a built word reassembles to: the argument's low 64 bits. The builder commits
residues, so nothing is assumed — and for an event field the trace already bounds by `2 ^ 64` the
`% 2 ^ 64` is the identity. -/
lemma wordOfNat_toNat (n : ℕ) : Word.toNat (wordOfNat (p := p) n) = n % 2 ^ 64 := by
  have hp : 2 ^ 24 < p := Fact.out
  have hval : ∀ m : ℕ, m < 2 ^ 16 → ((m : ZMod p)).val = m := fun m hm =>
    ZMod.val_natCast_of_lt (by omega)
  simp only [Word.toNat_def, wordOfNat, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  rw [hval _ (Nat.mod_lt _ (by norm_num)), hval _ (Nat.mod_lt _ (by norm_num)),
    hval _ (Nat.mod_lt _ (by norm_num)), hval _ (Nat.mod_lt _ (by norm_num))]
  omega

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

omit [Fact (2 ^ 24 < p)] in
/-- A built ALU-type block's `op_a_0` flag is `1` exactly when the destination **is** `x0` — the
routing condition of the `AluX0` chip. -/
lemma aluTypeReaderCols_op_a_0_eq_one {e : ALUTypeEvent} (h : e.opA = 0) :
    (aluTypeReaderCols (p := p) e).op_a_0 = 1 := by
  rw [aluTypeReaderCols_op_a_0, if_pos h]

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

omit [Fact (2 ^ 24 < p)] in
/-- The built word of `0` is the zero word — RISC-V's `x0` read value, in committed form. -/
lemma wordOfNat_zero_eq : wordOfNat (p := p) 0 = (#v[0, 0, 0, 0] : Word (ZMod p)) := by
  simp [wordOfNat]

/-- **The immutable ALU-type adapter's contract on a built row.** The sibling of
`iTypeReaderImmutable_spec` for the reader `AluX0` composes: `op_a` is a discarded source **read**,
so the four `op_a_0` gates pin the *read* value rather than a write value, and the `op_c` slot keeps
the ALU family's two forms.

Stated at the real row's `is_real = 1`, because three of the conjuncts mention it non-vacuously (the
`imm_c` padding gate, the `is_real - imm_c` access multiplicity, and the `op_c` access gate); the
padding row is discharged separately by the chip. `hzero` is the `x0`-reads-as-zero fact — a fact
about the machine, not the builder — and is exactly what makes the `op_a_0 = 1` branch of the gates
hold. -/
theorem aluTypeReaderImmutable_spec {e : ALUTypeEvent} (hclk : e.clk % 8 = 1) (hopA : e.opA < 32)
    (hzero : e.opA = 0 → e.prevA = 0) (himmC : e.immC = 0 ∨ e.immC = 1)
    (hprevTsA : e.prevTsA < e.clk + 4) (hprevTsB : e.prevTsB < e.clk + 3)
    (hprevTsC : e.immC = 0 → e.prevTsC < e.clk + 2) (is_trusted clk_high opcode : ZMod p) :
    Readers.ALUTypeReaderImmutable.Spec
      { cols := aluTypeReaderCols (p := p) e, is_real := 1, is_trusted := is_trusted,
        clk_high := clk_high,
        clk_low := (cpuStateCols (p := p) e.clk e.pc).clk_0_16
          + (cpuStateCols (p := p) e.clk e.pc).clk_16_24 * 65536,
        pc := (cpuStateCols (p := p) e.clk e.pc).pc, opcode := opcode } := by
  have hp : 2 ^ 24 < p := Fact.out
  -- the flag is binary either way, and on the `x0` branch the read value is the zero word
  have hbin : (aluTypeReaderCols (p := p) e).op_a_0 = 0
      ∨ (aluTypeReaderCols (p := p) e).op_a_0 = 1 := by
    by_cases hA : e.opA = 0
    · exact Or.inr (aluTypeReaderCols_op_a_0_eq_one hA)
    · exact Or.inl (aluTypeReaderCols_op_a_0_eq_zero hA)
  have hgate : ∀ i (hi : i < 4), (aluTypeReaderCols (p := p) e).op_a_0
      * (aluTypeReaderCols (p := p) e).op_a_memory.prev_value[i] = 0 := by
    intro i hi
    by_cases hA : e.opA = 0
    · rw [aluTypeReaderCols_op_a_memory, registerAccessCols_prev_value, hzero hA,
        wordOfNat_zero_eq]
      have : (#v[0, 0, 0, 0] : Word (ZMod p))[i] = 0 := by interval_cases i <;> rfl
      rw [this, mul_zero]
    · rw [aluTypeReaderCols_op_a_0_eq_zero hA, zero_mul]
  -- the immediate-consistency gates: on an immediate row the `op_c` block's committed value *is*
  -- the committed `op_c` word (`ALUTypeReader::populate` copies it); on a register row it is 0
  have himmGate : ∀ i (hi : i < 4), (aluTypeReaderCols (p := p) e).imm_c
      * ((aluTypeReaderCols (p := p) e).op_c_memory.prev_value[i]
        - (aluTypeReaderCols (p := p) e).op_c[i]) = 0 := by
    intro i hi
    rcases himmC with h | h
    · rw [aluTypeReaderCols_imm_c, h, Nat.cast_zero, zero_mul]
    · rw [aluTypeReaderCols_op_c_memory, aluTypeReaderCols_op_c, aluTypeOpCCols, if_pos h,
        sub_self, mul_zero]
  refine ⟨⟨hgate 0 (by omega), hgate 1 (by omega), hgate 2 (by omega), hgate 3 (by omega)⟩,
    hbin, by rw [sub_self, zero_mul], ?_,
    ⟨himmGate 0 (by omega), himmGate 1 (by omega), himmGate 2 (by omega), himmGate 3 (by omega)⟩,
    registerAccessCols_spec_opA hclk hprevTsA, registerAccessCols_spec_opB hclk hprevTsB, ?_,
    fun _ => ⟨aluTypeReaderCols_op_a_val_lt hopA, (cpuStateCols_pc_val_lt e.clk e.pc).1,
      (cpuStateCols_pc_val_lt e.clk e.pc).2.1, (cpuStateCols_pc_val_lt e.clk e.pc).2.2⟩,
    fun _ => ⟨wordOfNat_isU64 _, wordOfNat_isU64 _, registerAccessCols_prevLow_val_lt _ _ _,
      registerAccessCols_prevLow_val_lt _ _ _⟩,
    fun _ => ⟨aluTypeOpCCols_prev_value_isU64 e, aluTypeOpCCols_prevLow_val_lt e⟩⟩
  · -- the `op_c` access multiplicity `is_real - imm_c` is the flag's complement, hence binary
    rcases himmC with h | h
    · exact Or.inr (by rw [aluTypeReaderCols_imm_c, h, Nat.cast_zero, sub_zero])
    · exact Or.inl (by rw [aluTypeReaderCols_imm_c, h, Nat.cast_one, sub_self])
  · -- the `op_c` register access: present (and the shared corollary) on a register row, gated off
    -- on an immediate row, where `ALUTypeReader::populate` zeroes both timestamp columns
    rcases himmC with h | h
    · rw [aluTypeReaderCols_op_c_memory, aluTypeOpCCols_of_reg h]
      exact registerAccessCols_spec_opC hclk (hprevTsC h)
    · intro hgateOn
      rw [aluTypeReaderCols_imm_c, h, Nat.cast_one, sub_self] at hgateOn
      exact absurd hgateOn zero_ne_one

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

/-! ## The `ITypeReader` block, whole

`Addi` needed only the two `RegisterAccessCols` corollaries out of the I-type adapter's contract,
because its `ProverAssumptions` lists the adapter's conjuncts one by one. The memory chips ask for
`Readers.ITypeReader.Spec` itself, so here it is in one piece — every conjunct from the same event
facts, with `is_real`, `is_trusted`, `clk_high`, `opcode` and the four write-value limbs left
arbitrary (the reader's contract constrains none of them, and each chip supplies a different
extended loaded word). -/

/-- **The I-type adapter's contract on a built row.** From `ITypeEvent.WellFormed` alone: the four
`op_a_0` zeroing gates and the `op_a_0` binary fact hold because `rd ≠ x0` makes the flag `0`; the
two `RegisterAccessCols` contracts are the shared corollaries at offsets `4` / `3`; the decode
bounds are the index and pc-limb bounds of the builder; and the `is_real` bundle is the two
committed words' `isU64` plus the two previous-access clocks' 24-bit bounds. -/
theorem iTypeReader_spec {e : ITypeEvent} (h : e.WellFormed)
    (is_real is_trusted clk_high opcode wv0 wv1 wv2 wv3 : ZMod p) :
    Readers.ITypeReader.Spec
      { cols := iTypeReaderCols (p := p) e, is_real := is_real, is_trusted := is_trusted,
        clk_high := clk_high,
        clk_low := (cpuStateCols (p := p) e.clk e.pc).clk_0_16
          + (cpuStateCols (p := p) e.clk e.pc).clk_16_24 * 65536,
        pc := (cpuStateCols (p := p) e.clk e.pc).pc, opcode := opcode,
        wv0 := wv0, wv1 := wv1, wv2 := wv2, wv3 := wv3 } := by
  have hzero : (iTypeReaderCols (p := p) e).op_a_0 = 0 :=
    iTypeReaderCols_op_a_0_eq_zero h.opA_ne_zero
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fun _ => Or.inl hzero, ?_, ?_, fun _ => ?_, fun _ => ?_⟩
  · rw [hzero, zero_mul]
  · rw [hzero, zero_mul]
  · rw [hzero, zero_mul]
  · rw [hzero, zero_mul]
  · exact registerAccessCols_spec_opA h.clk_mod h.prevTsA_lt
  · exact registerAccessCols_spec_opB h.clk_mod h.prevTsB_lt
  · exact ⟨iTypeReaderCols_op_a_val_lt h.opA_lt, (cpuStateCols_pc_val_lt e.clk e.pc).1,
      (cpuStateCols_pc_val_lt e.clk e.pc).2.1, (cpuStateCols_pc_val_lt e.clk e.pc).2.2⟩
  · exact ⟨wordOfNat_isU64 _, wordOfNat_isU64 _, registerAccessCols_prevLow_val_lt _ _ _,
      registerAccessCols_prevLow_val_lt _ _ _⟩

omit [Fact (2 ^ 24 < p)] in
/-- A built I-type block's `op_a_0` flag is `1` exactly when the destination **is** `x0` — the
routing condition of the `AluX0`/`LoadX0`/`StoreX0` chips. -/
lemma iTypeReaderCols_op_a_0_eq_one {e : ITypeEvent} (h : e.opA = 0) :
    (iTypeReaderCols (p := p) e).op_a_0 = 1 := by
  rw [iTypeReaderCols_op_a_0, if_pos h]

/-- **The immutable I-type adapter's contract on a built row.** The sibling of `iTypeReader_spec`
for the reader the `x0` and store chips compose: `op_a` is a source **read**, so the four `op_a_0`
gates pin the *read* value rather than a write value.

That is the only difference, and it is why the hypothesis here is `hzero` rather than
`WellFormed`'s `opA_ne_zero`. The gates are `op_a_0 · v_i = 0`; on an `op_a ≠ x0` row the flag is
`0` and they are vacuous, while on an `op_a = x0` row the flag is `1` and the *only* way to satisfy
them is the zero read — which is RISC-V's rule that `x0` reads as zero, a fact about the machine,
not about the builder. Both branches are proved, so this one lemma serves the `x0` load rows (where
`op_a` is always `x0`) and the store rows (where `rs2` may or may not be). -/
theorem iTypeReaderImmutable_spec {e : ITypeEvent} (hclk : e.clk % 8 = 1) (hopA : e.opA < 32)
    (hzero : e.opA = 0 → e.prevA = 0) (hprevTsA : e.prevTsA < e.clk + 4)
    (hprevTsB : e.prevTsB < e.clk + 3) (is_real is_trusted clk_high opcode : ZMod p) :
    Readers.ITypeReaderImmutable.Spec
      { cols := iTypeReaderCols (p := p) e, is_real := is_real, is_trusted := is_trusted,
        clk_high := clk_high,
        clk_low := (cpuStateCols (p := p) e.clk e.pc).clk_0_16
          + (cpuStateCols (p := p) e.clk e.pc).clk_16_24 * 65536,
        pc := (cpuStateCols (p := p) e.clk e.pc).pc, opcode := opcode } := by
  have hp : 2 ^ 24 < p := Fact.out
  -- the flag is binary either way, and on the `x0` branch the read value is the zero word
  have hbin : (iTypeReaderCols (p := p) e).op_a_0 = 0 ∨ (iTypeReaderCols (p := p) e).op_a_0 = 1 := by
    by_cases hA : e.opA = 0
    · exact Or.inr (iTypeReaderCols_op_a_0_eq_one hA)
    · exact Or.inl (iTypeReaderCols_op_a_0_eq_zero hA)
  have hgate : ∀ i (hi : i < 4), (iTypeReaderCols (p := p) e).op_a_0
      * (iTypeReaderCols (p := p) e).op_a_memory.prev_value[i] = 0 := by
    intro i hi
    by_cases hA : e.opA = 0
    · rw [iTypeReaderCols_op_a_memory, registerAccessCols_prev_value, hzero hA]
      have : (wordOfNat (p := p) 0)[i] = 0 := by
        interval_cases i
        · rw [wordOfNat_zero]; simp
        · rw [wordOfNat_one]; simp
        · rw [wordOfNat_two]; simp
        · rw [wordOfNat_three]; simp
      rw [this, mul_zero]
    · rw [iTypeReaderCols_op_a_0_eq_zero hA, zero_mul]
  refine ⟨⟨hgate 0 (by omega), hgate 1 (by omega), hgate 2 (by omega), hgate 3 (by omega)⟩,
    fun _ => hbin, ?_, ?_, fun _ => ?_, fun _ => ?_⟩
  · exact registerAccessCols_spec_opA hclk hprevTsA
  · exact registerAccessCols_spec_opB hclk hprevTsB
  · exact ⟨iTypeReaderCols_op_a_val_lt hopA, (cpuStateCols_pc_val_lt e.clk e.pc).1,
      (cpuStateCols_pc_val_lt e.clk e.pc).2.1, (cpuStateCols_pc_val_lt e.clk e.pc).2.2⟩
  · exact ⟨wordOfNat_isU64 _, wordOfNat_isU64 _, registerAccessCols_prevLow_val_lt _ _ _,
      registerAccessCols_prevLow_val_lt _ _ _⟩

/-- **The immutable I-type adapter's contract on an `x0`-destination row** — the `LoadX0` form of
`iTypeReaderImmutable_spec`, where the routing condition `hA` fixes the register index and the read
value is unconditionally zero. -/
theorem iTypeReaderImmutable_spec_x0 {e : ITypeEvent} (hclk : e.clk % 8 = 1) (hA : e.opA = 0)
    (hprevA : e.prevA = 0) (hprevTsA : e.prevTsA < e.clk + 4) (hprevTsB : e.prevTsB < e.clk + 3)
    (is_real is_trusted clk_high opcode : ZMod p) :
    Readers.ITypeReaderImmutable.Spec
      { cols := iTypeReaderCols (p := p) e, is_real := is_real, is_trusted := is_trusted,
        clk_high := clk_high,
        clk_low := (cpuStateCols (p := p) e.clk e.pc).clk_0_16
          + (cpuStateCols (p := p) e.clk e.pc).clk_16_24 * 65536,
        pc := (cpuStateCols (p := p) e.clk e.pc).pc, opcode := opcode } :=
  iTypeReaderImmutable_spec hclk (by omega) (fun _ => hprevA) hprevTsA hprevTsB
    is_real is_trusted clk_high opcode

/-- The effective address the `AddressOperation` gadget sees — the `ℕ` sum of the two committed
operand words, truncated to 64 bits — is the event's own `addr`. The two words are `wordOfNat` of
`ℕ` fields the event already bounds by `2 ^ 64`, so nothing is lost. -/
theorem addr_eq {e : MemoryEvent} (hb : e.b < 2 ^ 64) (himm : e.imm < 2 ^ 64) :
    (Word.toNat (iTypeReaderCols (p := p) e.toITypeEvent).op_b_memory.prev_value
        + Word.toNat (iTypeReaderCols (p := p) e.toITypeEvent).op_c_imm) % 2 ^ 64 = e.addr := by
  rw [iTypeReaderCols_op_b_memory, registerAccessCols_prev_value, iTypeReaderCols_op_c_imm,
    wordOfNat_toNat, wordOfNat_toNat, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt himm, MemoryEvent.addr]

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

omit [Fact (2 ^ 24 < p)] in
/-- **The program counter as a built word.** The three committed `pc` limbs padded with a zero high
limb *are* `wordOfNat pc` — the high limb of a 48-bit address is zero, so the padding is not an
approximation. This is what lets the jump chips (`Jal`, `Jalr`) reduce their `AddOperation` operands
to the shared builder. -/
lemma cpuStateCols_pcWord_eq {clk pc : ℕ} (h : pc < 2 ^ 48) :
    (#v[(cpuStateCols (p := p) clk pc).pc[0], (cpuStateCols (p := p) clk pc).pc[1],
      (cpuStateCols (p := p) clk pc).pc[2], 0] : Word (ZMod p)) = wordOfNat pc := by
  simp only [cpuStateCols_pc_zero, cpuStateCols_pc_one, cpuStateCols_pc_two, wordOfNat,
    Nat.shiftRight_eq_div_pow]
  refine Vector.ext (fun i hi => ?_)
  interval_cases i
  · rfl
  · rfl
  · rfl
  · rw [show pc / 2 ^ 48 % 2 ^ 16 = 0 from by omega]
    simp

omit [Fact p.Prime] in
/-- The value a built word's low limb commits, as an `ℕ`. -/
lemma wordOfNat_zero_val (n : ℕ) : ((wordOfNat (p := p) n)[0]).val = n % 2 ^ 16 := by
  have hp : 2 ^ 24 < p := Fact.out
  rw [wordOfNat_zero, ZMod.val_natCast_of_lt (by omega)]

omit [Fact (2 ^ 24 < p)] in
/-- A 48-bit value's built word has a zero high limb — the `value[3] = 0` conjunct the jump chips'
`AddOperation` results owe (their targets are program counters, and SP1 commits a pc as three u16
limbs). -/
lemma wordOfNat_three_eq_zero {n : ℕ} (h : n < 2 ^ 48) : (wordOfNat (p := p) n)[3] = 0 := by
  rw [wordOfNat_three, show n / 2 ^ 48 % 2 ^ 16 = 0 from by omega, Nat.cast_zero]

/-- **The 4-byte alignment range check.** A 4-aligned value's built low limb divided by four is a
14-bit quantity — the byte-bus `Range(value[0] / 4, 14)` pull the jump chips emit. The content is
exactly the alignment: a u16 limb is `< 2 ^ 16` regardless, so it is the divisibility that makes the
quotient exact. `sub` is the low bit a `JALR` target has cleared before the check (`0` for `JAL`).
-/
lemma wordOfNat_div_four_val_lt {n sub : ℕ} (hsub : sub ≤ n % 2 ^ 16) (h : (n - sub) % 4 = 0) :
    (((wordOfNat (p := p) n)[0] - ((sub : ℕ) : ZMod p)) * (4 : ZMod p)⁻¹).val < 2 ^ 14 := by
  have hp : 2 ^ 24 < p := Fact.out
  obtain ⟨k, hk, hklt⟩ : ∃ k, n % 2 ^ 16 - sub = 4 * k ∧ k < 2 ^ 14 :=
    ⟨(n % 2 ^ 16 - sub) / 4, by omega, by omega⟩
  rw [wordOfNat_zero, show ((n % 2 ^ 16 : ℕ) : ZMod p) - ((sub : ℕ) : ZMod p)
      = ((n % 2 ^ 16 - sub : ℕ) : ZMod p) from by
    rw [Nat.cast_sub (by omega)], hk]
  push_cast
  rw [show (4 : ZMod p) * (k : ZMod p) = (k : ZMod p) * 4 from by ring, mul_assoc,
    mul_inv_cancel₀ (val_4_ne_zero (p := p)), mul_one, ZMod.val_natCast_of_lt (by omega)]
  exact hklt

end SP1Clean.TraceGen
