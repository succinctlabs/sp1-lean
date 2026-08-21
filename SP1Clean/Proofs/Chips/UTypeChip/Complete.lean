import SP1Clean.FormalModel.TraceGen.Readers
import SP1Clean.Proofs.Chips.UTypeChip.Witgen
import ToClean.Air.TableBuild

/-! # `SP1Clean.UTypeChip` — from trace events to a valid AIR table (the J-type template)

The first chip of the **J-type** family through the trace-generation chain (see
`AddChip/Complete.lean` for the programme note). `UType` reads `Extracted.JTypeReader`: both source
operands are decoded immediates, so the row makes a **single** register access — the `op_a` write —
and commits one extra selector column, `is_auipc`.

Two things are genuinely new here, and both are about the immediate.

1. **`is_auipc` is built, not assumed.** The event carries the executor's opcode discriminant, and
   the builder reads the selector off it (`Opcode::AUIPC = 48`), so its booleanity is a property of
   the builder — one `split`, no event conjunct.
2. **The decode relation is proved, not assumed.** `UTypeChip.ProverAssumptions` carries
   `toBitVec64 op_b_imm = RV64.lui (immOf adapter)`, which is *false* for an arbitrary 64-bit
   `op_b` and so cannot be a consequence of `JTypeEvent.WellFormed` (its sibling `Jal` puts a jump
   offset in the same slot). What makes it true is a plain-`ℕ` fact about SP1's decoder —
   `JTypeEvent.UTypeImm`, "the committed `op_b` is `sign_extend(imm << 12)` for a genuine 20-bit
   U-immediate", which is exactly what `Instruction::encode` re-derives and range-checks on the way
   back out. Given that, `toBitVec64_luiImmNat` and `immOf_jTypeReaderCols` below turn the relation
   into a theorem about the builder: the committed limbs of `luiImmNat imm` *are* the sign-extended
   shifted immediate, and `immOf` recovers `imm` from them exactly.

So nine of the eleven bullets are single citations; the two that are not are the `is_auipc` split
and the decode relation.
-/

namespace SP1Clean.UTypeChip

open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## The U-type immediate, limb by limb

`luiImmNat imm` is `imm <<< 12` sign-extended to 64 bits. Its four committed u16 limbs are
`[(imm % 16) * 4096, imm / 16, s, s]` with the sign fill `s = 0` or `65535` — the exact shape
`toBitVec64_signExtend_word` (the ADDW/SUBW keystone) consumes, which is why this file needs no
bit-level reasoning of its own. -/

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- The four little-endian u16 limbs of `luiImmNat imm`, as `ℕ` residues. The low two carry the
shifted immediate and the high two are the sign fill, `65535` exactly when the U-immediate's top
bit is set (`imm ≥ 2 ^ 19`). -/
lemma luiImmNat_limbs {imm : ℕ} (h : imm < 2 ^ 20) :
    luiImmNat imm % 2 ^ 16 = imm % 16 * 4096 ∧
      luiImmNat imm / 2 ^ 16 % 2 ^ 16 = imm / 16 ∧
      luiImmNat imm / 2 ^ 32 % 2 ^ 16 = (if imm < 2 ^ 19 then 0 else 65535) ∧
      luiImmNat imm / 2 ^ 48 % 2 ^ 16 = (if imm < 2 ^ 19 then 0 else 65535) := by
  rw [luiImmNat]
  split_ifs with hs <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

omit [Fact p.Prime] in
/-- The committed limb values of the built immediate word, as `ℕ`. -/
lemma luiWord_val {imm : ℕ} (h : imm < 2 ^ 20) :
    (wordOfNat (p := p) (luiImmNat imm))[0].val = imm % 16 * 4096 ∧
      (wordOfNat (p := p) (luiImmNat imm))[1].val = imm / 16 ∧
      (wordOfNat (p := p) (luiImmNat imm))[2].val = (if imm < 2 ^ 19 then 0 else 65535) ∧
      (wordOfNat (p := p) (luiImmNat imm))[3].val = (if imm < 2 ^ 19 then 0 else 65535) := by
  have hp : 2 ^ 24 < p := Fact.out
  obtain ⟨h0, h1, h2, h3⟩ := luiImmNat_limbs h
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · simp only [wordOfNat, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
      rw [ZMod.val_natCast_of_lt (by omega)]
      omega

/-- **The decode relation, proved.** The word the builder commits for a U-type row's `op_b` is the
64-bit value of `RV64.lui` at the row's own 20-bit immediate. Reduced to the project's
sign-extension keystone `toBitVec64_signExtend_word`: the low two limbs are the 32-bit value
`imm ++ 0#12`, and the high two are its sign fill. -/
theorem toBitVec64_luiImmNat {imm : ℕ} (h : imm < 2 ^ 20) :
    Word.toBitVec64 (wordOfNat (p := p) (luiImmNat imm)) = RV64.lui (BitVec.ofNat 20 imm) := by
  obtain ⟨hv0, hv1, -, -⟩ := luiWord_val (p := p) h
  obtain ⟨-, -, hn2, hn3⟩ := luiImmNat_limbs h
  -- the two high limbs, as casts of their `ℕ` residues (a projection of the builder)
  have hc2 : (wordOfNat (p := p) (luiImmNat imm))[2]
      = ((luiImmNat imm / 2 ^ 32 % 2 ^ 16 : ℕ) : ZMod p) := rfl
  have hc3 : (wordOfNat (p := p) (luiImmNat imm))[3]
      = ((luiImmNat imm / 2 ^ 48 % 2 ^ 16 : ℕ) : ZMod p) := rfl
  have hzero : ((0x0 : BitVec 12)).toNat = 0 := rfl
  have hX : ((BitVec.ofNat 20 imm) ++ (0x0 : BitVec 12)).toNat
      = (wordOfNat (p := p) (luiImmNat imm))[0].val
        + (wordOfNat (p := p) (luiImmNat imm))[1].val * 2 ^ 16 := by
    rw [hv0, hv1, BitVec.toNat_append, hzero, Nat.or_zero, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt h, Nat.shiftLeft_eq]
    omega
  rw [RV64.lui]
  refine toBitVec64_signExtend_word _ _ (if imm < 2 ^ 19 then (0 : ZMod p) else 1)
    (by omega) (by omega) ?_ ?_ ?_ hX
  · rw [hv1]
    split_ifs <;> first | rfl | omega
  · rw [hc2, hn2]
    split_ifs <;> push_cast <;> ring
  · rw [hc3, hn3]
    split_ifs <;> push_cast <;> ring

omit [Fact p.Prime] in
/-- **`immOf` inverts the builder.** The chip's immediate extractor — the high 20 bits of the
committed 32-bit immediate, read off limbs `0` and `1` — recovers the event's own U-immediate. -/
theorem immOf_jTypeReaderCols {e : JTypeEvent} {imm : ℕ} (h : imm < 2 ^ 20)
    (he : e.immB = luiImmNat imm) :
    immOf (jTypeReaderCols (p := p) e) = BitVec.ofNat 20 imm := by
  obtain ⟨hv0, hv1, -, -⟩ := luiWord_val (p := p) h
  rw [immOf, jTypeReaderCols_op_b_imm, he]
  congr 1
  rw [hv0, hv1]
  omega

/-! ## The chip's honest-prover contract on a built row -/

/--
**A well-formed, U-decoded trace event builds a row the honest prover can complete.** Every
conjunct of `UTypeChip.ProverAssumptions` at the built input row follows from
`JTypeEvent.WellFormed` together with `hdec : e.UTypeImm`, with no residual side condition.

`hdec` is the one thing the J-type record cannot supply — see the module docstring.

The `data` and `hint` are arbitrary: `UType`'s prover contract reads neither.
-/
theorem proverAssumptions_of_event {e : JTypeEvent} (h : e.WellFormed) (hdec : e.UTypeImm)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ProverAssumptions (e.toUTypeInputs (p := p)) data hint := by
  obtain ⟨imm, himm, he⟩ := hdec
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- the committed immediate word, and the program counter as a word: both built limb-wise
  · exact wordOfNat_isU64 _
  · exact cpuStateCols_pcWord_isU64 e.clk e.pc
  -- the value the `op_a` write displaces
  · exact fun _ => wordOfNat_isU64 _
  -- the row is real
  · exact Or.inr rfl
  -- the variant selector is built from the event's opcode discriminant, hence binary
  · rw [JTypeEvent.toUTypeInputs_is_auipc]
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  -- `rd ≠ x0`, so the `op_a_0` zeroing flag is off
  · exact jTypeReaderCols_op_a_0_eq_zero h.opA_ne_zero
  -- the shared reader contracts: the state block, then the single register access
  · exact cpuState_spec e.clk e.pc h.clk_mod _ _ _
  · exact registerAccessCols_spec_opA h.clk_mod h.prevTsA_lt
  -- the decode relation: proved from the event's U-immediate, not assumed
  · rw [JTypeEvent.toUTypeInputs_adapter, immOf_jTypeReaderCols himm he, jTypeReaderCols_op_b_imm,
      he]
    exact toBitVec64_luiImmNat himm
  -- the decode bounds the Program-bus fetch carries
  · exact fun _ => ⟨jTypeReaderCols_op_a_val_lt h.opA_lt, (cpuStateCols_pc_val_lt e.clk e.pc).1,
      (cpuStateCols_pc_val_lt e.clk e.pc).2.1, (cpuStateCols_pc_val_lt e.clk e.pc).2.2⟩
  -- G1: the pulled prior record's 24-bit access clock
  · exact fun _ => registerAccessCols_prevLow_val_lt _ _ _

/-- **A padding row satisfies the same contract.** `is_real = 0` makes every gated conjunct
vacuous; what survives is the two `isU64`s, the two zero flags, and — because it is stated
**ungated** — the decode relation, which the zero row satisfies as `RV64.lui 0 = 0`. -/
theorem proverAssumptions_padding (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ProverAssumptions (uTypePaddingInputs (p := p)) data hint := by
  have hzero : Word.isU64 (#v[0, 0, 0, 0] : Word (ZMod p)) :=
    Word.isU64_of_cases (by simp) (by simp) (by simp) (by simp)
  have hne : ¬((0 : ZMod p) = 1) := zero_ne_one
  have hword : wordOfNat (p := p) (luiImmNat 0) = (#v[0, 0, 0, 0] : Word (ZMod p)) := by
    simp [wordOfNat, luiImmNat]
  have himmOf : immOf (zeroJTypeReaderCols (p := p)) = BitVec.ofNat 20 0 := by
    rw [immOf]
    simp [zeroJTypeReaderCols]
  have hlui : Word.toBitVec64 (#v[0, 0, 0, 0] : Word (ZMod p))
      = RV64.lui (immOf (zeroJTypeReaderCols (p := p))) := by
    rw [himmOf, ← hword]
    exact toBitVec64_luiImmNat (p := p) (by norm_num)
  exact ⟨hzero, hzero, fun hr => absurd hr hne, Or.inl rfl, Or.inl rfl, rfl,
    fun hr => absurd hr hne, fun hr => absurd hr hne, hlui, fun hr => absurd hr hne,
    fun hr => absurd hr hne⟩

/-! ## The built table -/

/-- The UType chip as a flat-AIR component: one circuit, checked independently on each row.

A plain `def`, deliberately not an `abbrev` (see `AddChip.component` for the measurement). -/
def component : Air.Flat.Component (ZMod p) := ⟨circuit⟩

/-- The rows a trace builds: one input row per event, then `padding` zero rows. -/
def traceInputs (events : List JTypeEvent) (padding : ℕ) : List (Inputs (ZMod p)) :=
  events.map JTypeEvent.toUTypeInputs ++ List.replicate padding uTypePaddingInputs

/-- Every row of a built trace — event row or padding row — satisfies the chip's honest-prover
contract. -/
theorem proverAssumptions_of_mem_traceInputs {events : List JTypeEvent} {padding : ℕ}
    (h : ∀ e ∈ events, e.WellFormed ∧ e.UTypeImm) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) events padding, ProverAssumptions input data hint := by
  intro input hin
  rcases List.mem_append.mp hin with hin | hin
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
    exact proverAssumptions_of_event (h e he).1 (h e he).2 data hint
  · rw [List.eq_of_mem_replicate hin]
    exact proverAssumptions_padding data hint

/-- **A real trace builds a valid UType table.** Every `assertZero` of the whole flattened chip
circuit evaluates to zero on every built row, and no static lookup is left unchecked. -/
theorem traceTable_constraints (events : List JTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (h : ∀ e ∈ events, e.WellFormed ∧ e.UTypeImm) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events padding) data
      hint).Constraints :=
  Air.Flat.Table.build_constraints _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

/-- The same table satisfies its **channel guarantees** — every message it pushes onto the State,
Memory, Program and Byte channels carries the payload its channel promises. -/
theorem traceTable_guarantees (events : List JTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (h : ∀ e ∈ events, e.WellFormed ∧ e.UTypeImm) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events padding) data
      hint).Guarantees :=
  Air.Flat.Table.build_guarantees _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

/-- The table's interaction list on a channel, in closed form: the per-row evaluated interactions,
concatenated in row order. -/
theorem traceTable_interactionsWith (events : List JTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) (channel : RawChannel (ZMod p)) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events padding) data
        hint).interactionsWith channel =
      (traceInputs (p := p) events padding).flatMap fun input =>
        (component (p := p)).operations.interactionValuesWith channel
          (Environment.fromArray ((component (p := p)).buildRow input data hint) data) :=
  Air.Flat.Table.build_interactions _ _ _ _ channel

end SP1Clean.UTypeChip
