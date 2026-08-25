import SP1Clean.Proofs.Completeness.ProviderInteractions

/-!
# Tier 2 of the provider closure: a whole provider table's ledger

`ProviderInteractions.lean` proves what *one* built provider row emits. This file lifts each of
those eight closed forms to the table the trace generator builds, via
`tableCleanAccesses_build_map_singleton`:

> the Clean-orientation ledger of `Table.build component (traceInputs entries)` is exactly
> `entries.map access`.

That is the statement Tier 3 needs, and it is stated over **`ℕ` keys and an `ℤ` multiplicity** —
the `LookupAccess` vocabulary the closure arithmetic in `Model/InteractionBus.lean` speaks — rather
than over field elements. Discharging the `ZMod.val` round trips here rather than in Tier 3 is what
lets Tier 3 be pure list algebra against `closingAccesses`/`closingKeys`.

Each family costs three ingredients: its Tier-1 row lemma, the entry type's
`signedVal_multiplicity` (the centered-ledger recovery of the aggregate count), and the two
well-formedness bounds that make the operand cells round-trip. The `MultiplicityFits` premise is
the trace-generator capacity contract, not a circuit constraint — a provider row cannot see its own
aggregate count's magnitude.
-/

namespace SP1Clean.Soundness

open Air.Flat (Component Table)
open SP1Clean.Channels (byteChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## The cast round trips -/

/-- A natural that fits the field's guaranteed headroom round-trips through `ZMod.val`. Every
operand cell below reduces to this. -/
theorem val_natCast_eq {n : ℕ} (h : n < 2 ^ 24) : ((n : ℕ) : ZMod p).val = n := by
  have := Fact.out (p := 2 ^ 24 < p)
  exact ZMod.val_natCast_of_lt (by omega)

/-- The small opcode-selector literals the Byte channel's first cell carries. -/
theorem val_ofNat_small {n : ℕ} (h : n < 2 ^ 24) [n.AtLeastTwo] :
    (OfNat.ofNat n : ZMod p).val = n := by
  rw [← Nat.cast_ofNat (R := ZMod p) (n := n)]
  exact val_natCast_eq h

omit [Fact (2 ^ 24 < p)] in
/-- `ZMod.val` of the field's zero. Restated locally so the cell rewrites below can name it in a
`simp only` set without pulling in `NeZero` side conditions. -/
theorem val_zero_zmod : (0 : ZMod p).val = 0 := by simp

theorem val_one_zmod : (1 : ZMod p).val = 1 := by
  have := Fact.out (p := 2 ^ 24 < p)
  haveI : Fact (1 < p) := ⟨by omega⟩
  exact ZMod.val_one p

/-- The derived boolean cells (`MSB`'s high bit, `LTU`'s comparison result) are field bits, and
their `val` is the corresponding natural bit. -/
theorem val_ite_bit (c : Prop) [Decidable c] :
    (if c then (1 : ZMod p) else 0).val = if c then 1 else 0 := by
  split
  · exact val_one_zmod
  · exact val_zero_zmod

/-! ## `U8Range` -/

/-- The access one `U8Range` occurrence contributes. -/
def u8RangeAccess (e : TraceGen.ByteEntry) : LookupAccess :=
  (InteractionKind.Byte, "SP1Byte", [3, 0, e.b, e.c], (e.multiplicity : ℤ))

/-- **The `U8Range` provider table's ledger is exactly its occurrence list.** -/
theorem u8Range_traceTable_cleanAccesses (entries : List TraceGen.ByteEntry)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (hwf : ∀ e ∈ entries, e.WellFormed)
    (hmult : ∀ e ∈ entries, e.MultiplicityFits p) :
    tableCleanAccesses (Table.build (ByteChip.U8Range.component (p := p))
        (ByteChip.U8Range.traceInputs entries) data hint) =
      entries.map u8RangeAccess := by
  refine tableCleanAccesses_build_map_singleton (ByteChip.U8Range.component (p := p)) entries
    ByteChip.U8Range.ofEntry u8RangeAccess data hint (fun e he => ?_)
  rw [u8Range_buildRow_cleanAccesses]
  have hb := (hwf e he).1
  have hc := (hwf e he).2
  simp only [u8RangeAccess, ByteChip.U8Range.ofEntry,
    val_ofNat_small (p := p) (n := 3) (by norm_num), val_zero_zmod,
    val_natCast_eq (p := p) (by omega : e.b < 2 ^ 24),
    val_natCast_eq (p := p) (by omega : e.c < 2 ^ 24),
    TraceGen.ByteEntry.signedVal_multiplicity e (hmult e he)]

/-! ## `MSB` -/

/-- The access one `MSB` occurrence contributes: the high bit `MSB` derives in-circuit is the second cell, and the provider
computes it, so it is not part of the occurrence the consumer names. -/
def msbAccess (e : TraceGen.ByteEntry) : LookupAccess :=
  (InteractionKind.Byte, "SP1Byte", [5, if 128 ≤ e.b then 1 else 0, e.b, 0], (e.multiplicity : ℤ))

/-- **The `MSB` provider table's ledger is exactly its occurrence list.** -/
theorem msb_traceTable_cleanAccesses (entries : List TraceGen.ByteEntry)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (hwf : ∀ e ∈ entries, e.WellFormed)
    (hmult : ∀ e ∈ entries, e.MultiplicityFits p) :
    tableCleanAccesses (Table.build (ByteChip.MSB.component (p := p))
        (ByteChip.MSB.traceInputs entries) data hint) =
      entries.map msbAccess := by
  refine tableCleanAccesses_build_map_singleton (ByteChip.MSB.component (p := p)) entries
    ByteChip.MSB.ofEntry msbAccess data hint (fun e he => ?_)
  rw [msb_buildRow_cleanAccesses _ _ _ (val_natCast_lt (hwf e he).1 (by norm_num))]
  simp only [msbAccess, ByteChip.MSB.ofEntry, val_ofNat_small (p := p) (n := 5) (by norm_num), val_ite_bit, val_zero_zmod,
    val_natCast_eq (p := p) (by have := (hwf e he).1; omega : e.b < 2 ^ 24),
    TraceGen.ByteEntry.signedVal_multiplicity e (hmult e he)]

/-! ## `AndByte` -/

/-- The access one `AndByte` occurrence contributes: the bitwise AND is the second cell, and the provider
computes it, so it is not part of the occurrence the consumer names. -/
def andAccess (e : TraceGen.ByteEntry) : LookupAccess :=
  (InteractionKind.Byte, "SP1Byte", [0, e.b &&& e.c, e.b, e.c], (e.multiplicity : ℤ))

/-- **The `AndByte` provider table's ledger is exactly its occurrence list.** -/
theorem and_traceTable_cleanAccesses (entries : List TraceGen.ByteEntry)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (hwf : ∀ e ∈ entries, e.WellFormed)
    (hmult : ∀ e ∈ entries, e.MultiplicityFits p) :
    tableCleanAccesses (Table.build (ByteChip.AndByte.component (p := p))
        (ByteChip.AndByte.traceInputs entries) data hint) =
      entries.map andAccess := by
  refine tableCleanAccesses_build_map_singleton (ByteChip.AndByte.component (p := p)) entries
    ByteChip.AndByte.ofEntry andAccess data hint (fun e he => ?_)
  rw [and_buildRow_cleanAccesses _ _ _ ⟨val_natCast_lt (hwf e he).1 (by norm_num), val_natCast_lt (hwf e he).2 (by norm_num)⟩]
  simp only [andAccess, ByteChip.AndByte.ofEntry, val_zero_zmod,
    val_natCast_eq (p := p) (by have := (hwf e he).1; omega : e.b < 2 ^ 24),
    val_natCast_eq (p := p) (by have := (hwf e he).2; omega : e.c < 2 ^ 24),
    TraceGen.ByteEntry.signedVal_multiplicity e (hmult e he)]

/-! ## `OrByte` -/

/-- The access one `OrByte` occurrence contributes: the bitwise OR is the second cell, and the provider
computes it, so it is not part of the occurrence the consumer names. -/
def orAccess (e : TraceGen.ByteEntry) : LookupAccess :=
  (InteractionKind.Byte, "SP1Byte", [1, e.b ||| e.c, e.b, e.c], (e.multiplicity : ℤ))

/-- **The `OrByte` provider table's ledger is exactly its occurrence list.** -/
theorem or_traceTable_cleanAccesses (entries : List TraceGen.ByteEntry)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (hwf : ∀ e ∈ entries, e.WellFormed)
    (hmult : ∀ e ∈ entries, e.MultiplicityFits p) :
    tableCleanAccesses (Table.build (ByteChip.OrByte.component (p := p))
        (ByteChip.OrByte.traceInputs entries) data hint) =
      entries.map orAccess := by
  refine tableCleanAccesses_build_map_singleton (ByteChip.OrByte.component (p := p)) entries
    ByteChip.OrByte.ofEntry orAccess data hint (fun e he => ?_)
  rw [or_buildRow_cleanAccesses _ _ _ ⟨val_natCast_lt (hwf e he).1 (by norm_num), val_natCast_lt (hwf e he).2 (by norm_num)⟩]
  simp only [orAccess, ByteChip.OrByte.ofEntry, val_one_zmod,
    val_natCast_eq (p := p) (by have := (hwf e he).1; omega : e.b < 2 ^ 24),
    val_natCast_eq (p := p) (by have := (hwf e he).2; omega : e.c < 2 ^ 24),
    TraceGen.ByteEntry.signedVal_multiplicity e (hmult e he)]

/-! ## `XorByte` -/

/-- The access one `XorByte` occurrence contributes: the bitwise XOR is the second cell, and the provider
computes it, so it is not part of the occurrence the consumer names. -/
def xorAccess (e : TraceGen.ByteEntry) : LookupAccess :=
  (InteractionKind.Byte, "SP1Byte", [2, e.b ^^^ e.c, e.b, e.c], (e.multiplicity : ℤ))

/-- **The `XorByte` provider table's ledger is exactly its occurrence list.** -/
theorem xor_traceTable_cleanAccesses (entries : List TraceGen.ByteEntry)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (hwf : ∀ e ∈ entries, e.WellFormed)
    (hmult : ∀ e ∈ entries, e.MultiplicityFits p) :
    tableCleanAccesses (Table.build (ByteChip.XorByte.component (p := p))
        (ByteChip.XorByte.traceInputs entries) data hint) =
      entries.map xorAccess := by
  refine tableCleanAccesses_build_map_singleton (ByteChip.XorByte.component (p := p)) entries
    ByteChip.XorByte.ofEntry xorAccess data hint (fun e he => ?_)
  rw [xor_buildRow_cleanAccesses _ _ _ ⟨val_natCast_lt (hwf e he).1 (by norm_num), val_natCast_lt (hwf e he).2 (by norm_num)⟩]
  simp only [xorAccess, ByteChip.XorByte.ofEntry, val_ofNat_small (p := p) (n := 2) (by norm_num),
    val_natCast_eq (p := p) (by have := (hwf e he).1; omega : e.b < 2 ^ 24),
    val_natCast_eq (p := p) (by have := (hwf e he).2; omega : e.c < 2 ^ 24),
    TraceGen.ByteEntry.signedVal_multiplicity e (hmult e he)]

/-! ## `Ltu` -/

/-- The access one `Ltu` occurrence contributes: the unsigned comparison is the second cell, and the provider
computes it, so it is not part of the occurrence the consumer names. -/
def ltuAccess (e : TraceGen.ByteEntry) : LookupAccess :=
  (InteractionKind.Byte, "SP1Byte", [4, if e.b < e.c then 1 else 0, e.b, e.c], (e.multiplicity : ℤ))

/-- **The `Ltu` provider table's ledger is exactly its occurrence list.** -/
theorem ltu_traceTable_cleanAccesses (entries : List TraceGen.ByteEntry)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (hwf : ∀ e ∈ entries, e.WellFormed)
    (hmult : ∀ e ∈ entries, e.MultiplicityFits p) :
    tableCleanAccesses (Table.build (ByteChip.Ltu.component (p := p))
        (ByteChip.Ltu.traceInputs entries) data hint) =
      entries.map ltuAccess := by
  refine tableCleanAccesses_build_map_singleton (ByteChip.Ltu.component (p := p)) entries
    ByteChip.Ltu.ofEntry ltuAccess data hint (fun e he => ?_)
  rw [ltu_buildRow_cleanAccesses _ _ _ ⟨val_natCast_lt (hwf e he).1 (by norm_num), val_natCast_lt (hwf e he).2 (by norm_num)⟩]
  simp only [ltuAccess, ByteChip.Ltu.ofEntry, val_ofNat_small (p := p) (n := 4) (by norm_num), val_ite_bit,
    val_natCast_eq (p := p) (by have := (hwf e he).1; omega : e.b < 2 ^ 24),
    val_natCast_eq (p := p) (by have := (hwf e he).2; omega : e.c < 2 ^ 24),
    TraceGen.ByteEntry.signedVal_multiplicity e (hmult e he)]

/-! ## `Range` -/

/-- The access one range occurrence at `width` contributes. The width itself is a key cell: SP1's
byte table serves all seventeen widths through one channel, so the width is what separates them. -/
def rangeAccess (width : RangeChip.Width) (e : TraceGen.RangeEntry) : LookupAccess :=
  (InteractionKind.Byte, "SP1Byte", [6, e.a, width.val, 0], (e.multiplicity : ℤ))

/-- **The `Range` provider table at one width has exactly its occurrence list as its ledger.** -/
theorem range_traceTable_cleanAccesses (width : RangeChip.Width)
    (entries : List TraceGen.RangeEntry)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (hwf : ∀ e ∈ entries, e.WellFormed width.val)
    (hmult : ∀ e ∈ entries, e.MultiplicityFits p) :
    tableCleanAccesses (Table.build (RangeChip.componentFor (p := p) width)
        (RangeChip.traceInputs entries) data hint) =
      entries.map (rangeAccess width) := by
  have hwidth : width.val ≤ 16 := Nat.le_of_lt_succ width.isLt
  refine tableCleanAccesses_build_map_singleton (RangeChip.componentFor (p := p) width) entries
    RangeChip.ofEntry (rangeAccess width) data hint (fun e he => ?_)
  rw [range_buildRow_cleanAccesses]
  have ha : e.a < 2 ^ 24 := by
    have hlt : e.a < 2 ^ width.val := hwf e he
    exact lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega))
  simp only [rangeAccess, RangeChip.ofEntry,
    val_ofNat_small (p := p) (n := 6) (by norm_num), val_zero_zmod,
    val_natCast_eq (p := p) ha,
    val_natCast_eq (p := p) (by omega : width.val < 2 ^ 24),
    TraceGen.RangeEntry.signedVal_multiplicity e (hmult e he)]

/-! ## `Program` -/

/-- What a ROM entry's *key* cells need for the Program table's ledger to be its occurrence list.

The provider circuit range-checks the three pc limbs and the `op_a_0` flag, and the builder limbs
`opB`/`opC` by construction — so those cells round-trip through `ZMod.val` for free. `opcode`,
`opA`, `opA0`, `immB` and `immC` it passes straight through, so their round trip is a
trace-generator obligation and is stated here rather than assumed silently. -/
def RomKeyFits (e : TraceGen.RomEntry) : Prop :=
  e.opcode < 2 ^ 24 ∧ e.opA < 2 ^ 24 ∧ e.opA0 < 2 ^ 24 ∧ e.immB < 2 ^ 24 ∧ e.immC < 2 ^ 24

/-- The access one committed ROM entry contributes: its fetch address as three 16-bit limbs, the
decoded operands (the two 64-bit slots limbed exactly as the fetch message carries them), the three
flags, and its explicit fetch count. -/
def programEntryAccess (e : TraceGen.RomEntry) : LookupAccess :=
  (InteractionKind.Program, "SP1Program",
    [e.pc % 2 ^ 16, e.pc / 2 ^ 16 % 2 ^ 16, e.pc / 2 ^ 32 % 2 ^ 16, e.opcode, e.opA,
      e.opB % 2 ^ 16, e.opB / 2 ^ 16 % 2 ^ 16, e.opB / 2 ^ 32 % 2 ^ 16, e.opB / 2 ^ 48 % 2 ^ 16,
      e.opC % 2 ^ 16, e.opC / 2 ^ 16 % 2 ^ 16, e.opC / 2 ^ 32 % 2 ^ 16, e.opC / 2 ^ 48 % 2 ^ 16,
      e.opA0, e.immB, e.immC],
    (e.multiplicity : ℤ))

/-- **The `Program` provider table's ledger is exactly its committed-entry list.** -/
theorem program_traceTable_cleanAccesses (entries : List TraceGen.RomEntry)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (hfit : ∀ e ∈ entries, RomKeyFits e)
    (hmult : ∀ e ∈ entries, e.MultiplicityFits p) :
    tableCleanAccesses (Table.build (ProgramProviderChip.component (p := p))
        (ProgramProviderChip.traceInputs entries) data hint) =
      entries.map programEntryAccess := by
  refine tableCleanAccesses_build_map_singleton (ProgramProviderChip.component (p := p)) entries
    ProgramProviderChip.ofEntry programEntryAccess data hint (fun e he => ?_)
  rw [program_buildRow_cleanAccesses]
  obtain ⟨hop, hopa, hopa0, himmb, himmc⟩ := hfit e he
  simp only [programRowAccess, programEntryAccess, ProgramProviderChip.ofEntry,
    TraceGen.wordOfNat_zero, TraceGen.wordOfNat_one, TraceGen.wordOfNat_two,
    TraceGen.wordOfNat_three,
    val_natCast_eq (p := p) (by omega : e.pc % 2 ^ 16 < 2 ^ 24),
    val_natCast_eq (p := p) (by omega : e.pc / 2 ^ 16 % 2 ^ 16 < 2 ^ 24),
    val_natCast_eq (p := p) (by omega : e.pc / 2 ^ 32 % 2 ^ 16 < 2 ^ 24),
    val_natCast_eq (p := p) (by omega : e.opB % 2 ^ 16 < 2 ^ 24),
    val_natCast_eq (p := p) (by omega : e.opB / 2 ^ 16 % 2 ^ 16 < 2 ^ 24),
    val_natCast_eq (p := p) (by omega : e.opB / 2 ^ 32 % 2 ^ 16 < 2 ^ 24),
    val_natCast_eq (p := p) (by omega : e.opB / 2 ^ 48 % 2 ^ 16 < 2 ^ 24),
    val_natCast_eq (p := p) (by omega : e.opC % 2 ^ 16 < 2 ^ 24),
    val_natCast_eq (p := p) (by omega : e.opC / 2 ^ 16 % 2 ^ 16 < 2 ^ 24),
    val_natCast_eq (p := p) (by omega : e.opC / 2 ^ 32 % 2 ^ 16 < 2 ^ 24),
    val_natCast_eq (p := p) (by omega : e.opC / 2 ^ 48 % 2 ^ 16 < 2 ^ 24),
    val_natCast_eq (p := p) hop, val_natCast_eq (p := p) hopa,
    val_natCast_eq (p := p) hopa0, val_natCast_eq (p := p) himmb,
    val_natCast_eq (p := p) himmc,
    TraceGen.RomEntry.signedVal_multiplicity e (hmult e he)]

end SP1Clean.Soundness
