import SP1Clean.Proofs.Chips.ByteChip.ByteChip
import SP1Clean.Proofs.Chips.ByteChip.RangeChip
import SP1Clean.Proofs.Chips.ProgramProviderChip
import SP1Clean.Proofs.Chips.MemoryProviderChip
import SP1Clean.Proofs.Chips.MemoryFinalizeChip
import SP1Clean.Proofs.Chips.StateBumpChip.Formal
import SP1Clean.Proofs.Chips.MemoryBumpChip.Formal
import ToClean.Gadgets.ComputableWitnesses

/-! # Honest witness generation for the provider/boundary tables

The `ComputableWitnesses` half of the completeness chain, for the provider segment of
`sp1ProviderTables` (`Soundness/SP1Ensemble.lean`): the six `ByteChip` opcode providers, all
seventeen fixed-width `RangeChip` providers, the Program-ROM provider, the two memory boundary
tables, and the two W3 system tables. The instruction chips' counterparts are the twenty-five
`Proofs/Chips/<Chip>/Witgen.lean` files; this is the same statement for the tables on the other side
of every bus.

Three shapes, in increasing order of work:

* **No cells at all.** `StateBump` and `MemoryBump` are flat own-assert tables: every column is an
  input, `localLength = 0`, and `FlatOperation.forAll_witnessCongr_of_localLength_zero` closes the
  whole obligation without looking at a single operation.
* **No local cells.** `MemoryFinalize` reads its boolean multiplicity from the row input, so its
  witness-congruence obligation is vacuous too. This makes both active rows and zero padding rows
  reachable through `Table.build`.
* **Bit decompositions.** Everything that proves a range bound in-circuit composes
  `Gadgets.ToBits.rangeCheck`, which does declare cells (the bits). Those are dispatched by the
  gadget's own `ComputableWitnesses` (`ToClean/Gadgets/ComputableWitnesses.lean`) through
  `forAll_witnessCongr_of_assertionSubcircuit`, so no provider proof ever unfolds a bit
  decomposition.

Two providers read a cell of their *own* row inside a child's input expression: `MSB` and `LTU`
range-check `2 * b - msb * 256` and `b - c + ltu * 256`, whose `msb`/`ltu` are cells the row
witnessed one step earlier. That is what the `AgreesBelow` premise of
`forAll_witnessCongr_of_assertionSubcircuit` is for — the parent's own environment agreement at the
child's starting offset covers those cells, so they need no extra hypothesis.

**Multiplicity.** Provider multiplicities are explicit input columns, never synthesized local
witnesses. Byte, Range, and Program rows may therefore carry zero (padding), one (per occurrence),
or an aggregate field count. Memory init/finalize keep their upstream boolean selector gate; their
honest input builders expose both `0` and `1`. `ComputableWitnesses` consequently proves only the
derived cells (bit decompositions and byte-operation results), not a hidden policy about table-row
multiplicity. -/

namespace SP1Clean

open Circuit

/-! ## The byte-table providers (opcodes 0–5) -/

namespace ByteChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

-- `local` for the same reason the provider modules keep theirs local: a leaked `Fact (p > 2)`
-- derived from `Fact (2 ^ 17 < p)` makes downstream `omit` clauses illegal.
local instance : Fact (p > 2) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
local instance : Fact (p > 512) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

namespace U8Range

/-- The `U8Range` provider has computable witnesses: two bit decompositions over the two input
cells. Its multiplicity is an input, not a local witness. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnesses := by
  intro k input env env'
  simp only [circuit, main, circuit_norm, Operations.forAllFlat]
  exact ⟨FlatOperation.forAll_witnessCongr_of_assertionSubcircuit _ _ (by omega)
      (Gadgets.ToBits.rangeCheck_computableWitnesses _ _)
      (fun _ h => by simpa [circuit_norm] using congrArg Inputs.b h),
    FlatOperation.forAll_witnessCongr_of_assertionSubcircuit _ _ (by omega)
      (Gadgets.ToBits.rangeCheck_computableWitnesses _ _)
      (fun _ h => by simpa [circuit_norm] using congrArg Inputs.c h)⟩

end U8Range

namespace MSB

/-- The `MSB` provider has computable witnesses. The one non-constant cell is the high bit of `b`;
the third bit decomposition reads it back through `2 * b - msb * 256`, which is what the
`AgreesBelow` premise supplies. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnesses := by
  intro k input env env'
  simp only [circuit, main, circuit_norm, Operations.forAllFlat]
  refine ⟨FlatOperation.forAll_witnessCongr_of_assertionSubcircuit _ _ (by omega)
      (Gadgets.ToBits.rangeCheck_computableWitnesses _ _)
      (fun _ h => by simpa [circuit_norm] using congrArg Inputs.b h),
    fun _ h => ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ (by simp [circuit_norm]),
    FlatOperation.forAll_witnessCongr_of_assertionSubcircuit _ _ (by omega)
      (Gadgets.ToBits.rangeCheck_computableWitnesses _ _) (fun ha h => ?_)⟩
  · rw [h]
  · have hb : Expression.eval env.toEnvironment input.b
        = Expression.eval env'.toEnvironment input.b := by
      simpa [circuit_norm] using congrArg Inputs.b h
    have hm : env.toEnvironment.get (k + (Gadgets.ToBits.rangeCheck 8 two_pow_eight_lt).localLength
        input.b) = env'.toEnvironment.get (k +
        (Gadgets.ToBits.rangeCheck 8 two_pow_eight_lt).localLength input.b) := ha.get_eq (by omega)
    simp [circuit_norm, hb, hm]

end MSB

namespace AndByte

/-- The `AND` provider has computable witnesses: two bit decompositions plus the `And8` gadget's
own witnessed result cell. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnesses := by
  intro k input env env'
  simp only [circuit, main, circuit_norm, Operations.forAllFlat]
  exact ⟨FlatOperation.forAll_witnessCongr_of_assertionSubcircuit _ _ (by omega)
      (Gadgets.ToBits.rangeCheck_computableWitnesses _ _)
      (fun _ h => by simpa [circuit_norm] using congrArg Inputs.b h),
    FlatOperation.forAll_witnessCongr_of_assertionSubcircuit _ _ (by omega)
      (Gadgets.ToBits.rangeCheck_computableWitnesses _ _)
      (fun _ h => by simpa [circuit_norm] using congrArg Inputs.c h),
    FlatOperation.forAll_witnessCongr_of_formalSubcircuit _ _ (by omega)
      Gadgets.And.And8.computableWitnesses (fun _ h => by
        have hb : Expression.eval env.toEnvironment input.b
            = Expression.eval env'.toEnvironment input.b := by
          simpa [circuit_norm] using congrArg Inputs.b h
        have hc : Expression.eval env.toEnvironment input.c
            = Expression.eval env'.toEnvironment input.c := by
          simpa [circuit_norm] using congrArg Inputs.c h
        simp [circuit_norm, hb, hc])⟩

end AndByte

namespace OrByte

/-- The `OR` provider has computable witnesses — the `AND` argument verbatim, at `Or8`. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnesses := by
  intro k input env env'
  simp only [circuit, main, circuit_norm, Operations.forAllFlat]
  exact ⟨FlatOperation.forAll_witnessCongr_of_assertionSubcircuit _ _ (by omega)
      (Gadgets.ToBits.rangeCheck_computableWitnesses _ _)
      (fun _ h => by simpa [circuit_norm] using congrArg Inputs.b h),
    FlatOperation.forAll_witnessCongr_of_assertionSubcircuit _ _ (by omega)
      (Gadgets.ToBits.rangeCheck_computableWitnesses _ _)
      (fun _ h => by simpa [circuit_norm] using congrArg Inputs.c h),
    FlatOperation.forAll_witnessCongr_of_formalSubcircuit _ _ (by omega)
      Gadgets.Or.Or8.computableWitnesses (fun _ h => by
        have hb : Expression.eval env.toEnvironment input.b
            = Expression.eval env'.toEnvironment input.b := by
          simpa [circuit_norm] using congrArg Inputs.b h
        have hc : Expression.eval env.toEnvironment input.c
            = Expression.eval env'.toEnvironment input.c := by
          simpa [circuit_norm] using congrArg Inputs.c h
        simp [circuit_norm, hb, hc])⟩

end OrByte

namespace XorByte

/-- The `XOR` provider has computable witnesses: two bit decompositions, then the result cell
computed from the two operands (its correctness carried by a static lookup, which declares no
cells). -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnesses := by
  intro k input env env'
  simp only [circuit, main, circuit_norm, Operations.forAllFlat]
  refine ⟨FlatOperation.forAll_witnessCongr_of_assertionSubcircuit _ _ (by omega)
      (Gadgets.ToBits.rangeCheck_computableWitnesses _ _)
      (fun _ h => by simpa [circuit_norm] using congrArg Inputs.b h),
    FlatOperation.forAll_witnessCongr_of_assertionSubcircuit _ _ (by omega)
      (Gadgets.ToBits.rangeCheck_computableWitnesses _ _)
      (fun _ h => by simpa [circuit_norm] using congrArg Inputs.c h),
    fun _ h => ?_⟩
  rw [h]

end XorByte

namespace Ltu

/-- The `LTU` provider has computable witnesses — the `MSB` argument verbatim, at the comparison
bit and `b - c + ltu * 256`. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnesses := by
  intro k input env env'
  simp only [circuit, main, circuit_norm, Operations.forAllFlat]
  refine ⟨FlatOperation.forAll_witnessCongr_of_assertionSubcircuit _ _ (by omega)
      (Gadgets.ToBits.rangeCheck_computableWitnesses _ _)
      (fun _ h => by simpa [circuit_norm] using congrArg Inputs.b h),
    FlatOperation.forAll_witnessCongr_of_assertionSubcircuit _ _ (by omega)
      (Gadgets.ToBits.rangeCheck_computableWitnesses _ _)
      (fun _ h => by simpa [circuit_norm] using congrArg Inputs.c h),
    fun _ h => ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ (by simp [circuit_norm]),
    FlatOperation.forAll_witnessCongr_of_assertionSubcircuit _ _ (by omega)
      (Gadgets.ToBits.rangeCheck_computableWitnesses _ _) (fun ha h => ?_)⟩
  · -- `circuit_norm` normalises the *proposition* under the comparison bit's `decide` but leaves
    -- its `Decidable` instance in the witness-IR spelling, so the ordinary `rw` motive does not
    -- typecheck; the two spellings are definitionally equal, which is what the unfolding does.
    with_unfolding_all exact congrArg (fun r : Inputs (ZMod p) =>
      #[if decide (r.b.val < r.c.val) = true then (1 : ZMod p) else 0]) h
  · have hb : Expression.eval env.toEnvironment input.b
        = Expression.eval env'.toEnvironment input.b := by
      simpa [circuit_norm] using congrArg Inputs.b h
    have hc : Expression.eval env.toEnvironment input.c
        = Expression.eval env'.toEnvironment input.c := by
      simpa [circuit_norm] using congrArg Inputs.c h
    have hl : env.toEnvironment.get (k
        + (Gadgets.ToBits.rangeCheck 8 two_pow_eight_lt).localLength input.b
        + (Gadgets.ToBits.rangeCheck 8 two_pow_eight_lt).localLength input.c)
        = env'.toEnvironment.get (k
        + (Gadgets.ToBits.rangeCheck 8 two_pow_eight_lt).localLength input.b
        + (Gadgets.ToBits.rangeCheck 8 two_pow_eight_lt).localLength input.c) := ha.get_eq (by omega)
    simp [circuit_norm, hb, hc, hl]

end Ltu

end ByteChip

/-! ## The fixed-width range providers -/

namespace RangeChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : Fact (p > 2) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- The fixed-width `Range` provider has computable witnesses, at every width: one bit
decomposition over the single input cell. -/
theorem computableWitnesses (n : ℕ) (hn : 2 ^ n < p) :
    (circuit n hn (p := p)).base.ComputableWitnesses := by
  intro k input env env'
  simp only [circuit, main, circuit_norm, Operations.forAllFlat]
  exact FlatOperation.forAll_witnessCongr_of_assertionSubcircuit _ _ (by omega)
    (Gadgets.ToBits.rangeCheck_computableWitnesses n hn)
    fun _ h => by simpa [circuit_norm] using congrArg Inputs.a h

/-- Computable witnesses for every member of the complete `0, …, 16` fixed-width profile. -/
theorem computableWitnessesFor (width : Width) :
    (circuitFor width (p := p)).base.ComputableWitnesses :=
  computableWitnesses width.val _

end RangeChip

/-! ## The Program-ROM provider -/

namespace ProgramProviderChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : Fact (p > 2) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- The Program-ROM provider has computable witnesses: four bit decompositions over four input
cells. Its boolean decode gate and explicit multiplicity declare no cells. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnesses := by
  intro k input env env'
  simp only [circuit, main, circuit_norm, Operations.forAllFlat]
  exact ⟨FlatOperation.forAll_witnessCongr_of_assertionSubcircuit _ _ (by omega)
      (Gadgets.ToBits.rangeCheck_computableWitnesses _ _)
      (fun _ h => by simpa [circuit_norm] using congrArg Inputs.op_a h),
    FlatOperation.forAll_witnessCongr_of_assertionSubcircuit _ _ (by omega)
      (Gadgets.ToBits.rangeCheck_computableWitnesses _ _)
      (fun _ h => by simpa [circuit_norm] using congrArg Inputs.pc0 h),
    FlatOperation.forAll_witnessCongr_of_assertionSubcircuit _ _ (by omega)
      (Gadgets.ToBits.rangeCheck_computableWitnesses _ _)
      (fun _ h => by simpa [circuit_norm] using congrArg Inputs.pc1 h),
    FlatOperation.forAll_witnessCongr_of_assertionSubcircuit _ _ (by omega)
      (Gadgets.ToBits.rangeCheck_computableWitnesses _ _)
      (fun _ h => by simpa [circuit_norm] using congrArg Inputs.pc2 h),
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ (by simp [circuit_norm])⟩

end ProgramProviderChip

/-! ## The memory boundary tables -/

namespace WordRangeCheck

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : Fact (p > 2) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- The whole-`Word` range check has computable witnesses: four per-limb bit decompositions. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnesses := by
  intro k input env env'
  simp only [circuit, main, circuit_norm, Operations.forAllFlat]
  exact ⟨FlatOperation.forAll_witnessCongr_of_assertionSubcircuit _ _ (by omega)
      (Gadgets.ToBits.rangeCheck_computableWitnesses _ _)
      (fun _ h => by simpa [circuit_norm] using congrArg (fun v : Word (ZMod p) => v[0]) h),
    FlatOperation.forAll_witnessCongr_of_assertionSubcircuit _ _ (by omega)
      (Gadgets.ToBits.rangeCheck_computableWitnesses _ _)
      (fun _ h => by simpa [circuit_norm] using congrArg (fun v : Word (ZMod p) => v[1]) h),
    FlatOperation.forAll_witnessCongr_of_assertionSubcircuit _ _ (by omega)
      (Gadgets.ToBits.rangeCheck_computableWitnesses _ _)
      (fun _ h => by simpa [circuit_norm] using congrArg (fun v : Word (ZMod p) => v[2]) h),
    FlatOperation.forAll_witnessCongr_of_assertionSubcircuit _ _ (by omega)
      (Gadgets.ToBits.rangeCheck_computableWitnesses _ _)
      (fun _ h => by simpa [circuit_norm] using congrArg (fun v : Word (ZMod p) => v[3]) h)⟩

end WordRangeCheck

namespace MemoryProviderChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The memory-init provider has computable witnesses: the whole-`Word` range check's bit
decompositions. The boolean multiplicity is an explicit input. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnesses := by
  intro k input env env'
  simp only [circuit, main, circuit_norm, Operations.forAllFlat]
  exact FlatOperation.forAll_witnessCongr_of_assertionSubcircuit _ _ (by omega)
    WordRangeCheck.computableWitnesses
    fun _ h => by with_unfolding_all exact congrArg Inputs.value h

end MemoryProviderChip

namespace MemoryFinalizeChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
/-- The memory-finalize table has computable witnesses vacuously: it declares no local cells. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnesses := by
  intro k input env env'
  exact Operations.forAllFlat_witnessCongr_of_localLength_zero _ _
    (by simp [circuit, main, circuit_norm])

end MemoryFinalizeChip

/-! ## The two W3 system tables

Both are flat own-assert tables — every column is an input, nothing is witnessed — so the whole
obligation is `localLength = 0`. -/

namespace StateBumpChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- StateBump has computable witnesses vacuously: the table declares no cells. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnesses := fun k input env env' =>
  Operations.forAllFlat_witnessCongr_of_localLength_zero _ _ (by simp [circuit, main, circuit_norm])

end StateBumpChip

namespace MemoryBumpChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- MemoryBump has computable witnesses vacuously: the table declares no cells. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnesses := fun k input env env' =>
  Operations.forAllFlat_witnessCongr_of_localLength_zero _ _ (by simp [circuit, main, circuit_norm])

end MemoryBumpChip

end SP1Clean
