import Mathlib.Data.ZMod.Basic
import SP1Clean.Model.InteractionBus
import SP1Clean.Math.Word

/-! # The `ProgramChip` receiver — discharging instruction-fetch membership from bus balance

SP1's program/decode chip (`crates/core/machine/src/program/`) is the **preprocessed receiver** of the
Program bus: every CPU row `send`s its fetched `(pc, opcode, operands)` tuple gated by `is_trusted`
(`= is_real` on Add), the program chip *receives* each with a count multiplicity, and the LogUp argument
balances them. Its preprocessed trace contains **only valid decoded ROM rows** — so the register-index
bounds (`op_* < 32`), the pc bounds, and the opcode `trusted_instr` decode that the *sender* cannot prove
locally (`Foundations/Channels.lean`'s `ProgramMsg.Spec` defers them as *received* facts) hold for every
real fetch, exactly what `Soundness/ProgramConsistency.lean`'s `TraceProgramLink` threads.

This module models the receiver's side natively, the Program-bus sibling of `Chips/ByteChip.lean`: the
receiver is characterized by a membership **predicate** (`inROM`), not the ROM enumeration. A
`ProgramProvider inROM` is any contribution list whose every entry sits at the key of some `inROM`-valid
program row. The key fact that makes the membership transfer work is that the Program-bus key is the *full*
`ZMod.val`-projection of every meaningful instruction field, so (val injective) **the key determines the
row** — identical to the byte argument. -/

namespace SP1Clean.ProgramChip

open SP1Clean
open SP1Clean.LookupAccessList

variable {p : ℕ} [NeZero p]

/-- One decoded program-ROM row: the three pc limbs, the opcode, the `op_a` register operand, the `op_b`
and `op_c` operands as full `Word`s (their low limbs are register indices; the high limbs carry an
immediate), the `op_a_0` zero flag, and the `imm_b`/`imm_c` immediate flags — the meaningful columns of the
Program-bus key (mirrors `Soundness/ProgramConsistency.lean`'s `programLookups` 16-tuple). A pure R-type
fetch has `op_b = #v[idx, 0, 0, 0]`, `op_c = #v[idx, 0, 0, 0]`, `imm_b = imm_c = 0`; a J-type fetch
(JAL/AUIPC) has `op_b`/`op_c` full immediates with `imm_b = imm_c = 1`. -/
structure ProgramRow (F : Type) where
  pc0 : F
  pc1 : F
  pc2 : F
  opcode : F
  op_a : F
  op_b : Word F
  imm_b : F
  op_c : Word F
  op_a_0 : F
  imm_c : F

/-- The val-projected Program-bus key of a program row — the 16-tuple `programLookups` sends, with the
meaningful fields (`op_b`/`op_c` as their four limbs, plus `imm_b`/`imm_c`) through `ZMod.val`. -/
def programRowKey (row : ProgramRow (ZMod p)) : LookupKey :=
  (.Program, "SP1Program",
    [row.pc0.val, row.pc1.val, row.pc2.val, row.opcode.val, row.op_a.val,
      row.op_b[0].val, row.op_b[1].val, row.op_b[2].val, row.op_b[3].val,
      row.op_c[0].val, row.op_c[1].val, row.op_c[2].val, row.op_c[3].val,
      row.op_a_0.val, row.imm_b.val, row.imm_c.val])

/-- **The key determines the row.** The Program-bus key is the full `ZMod.val`-projection of every
meaningful field, and `ZMod.val` is injective (`[NeZero p]`), so two rows with the same key are equal
(the `op_c` `Word` recovered limb-by-limb via `Vector.ext`). This is what lets the provider's *membership*
(it carries only valid rows) transfer to the *consumer's* sent row. -/
theorem programRow_eq_of_key {r1 r2 : ProgramRow (ZMod p)} (h : programRowKey r1 = programRowKey r2) :
    r1 = r2 := by
  simp only [programRowKey, Prod.mk.injEq, List.cons.injEq, and_true, true_and] at h
  obtain ⟨h0, h1, h2, h3, h4, hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3, ha0, himmb, himm⟩ := h
  cases r1; cases r2
  simp only [ProgramRow.mk.injEq]
  refine ⟨ZMod.val_injective p h0, ZMod.val_injective p h1, ZMod.val_injective p h2,
    ZMod.val_injective p h3, ZMod.val_injective p h4, ?_, ZMod.val_injective p himmb, ?_,
    ZMod.val_injective p ha0, ZMod.val_injective p himm⟩
  · apply Vector.ext; intro i hi
    rcases i with _|_|_|_|i
    · exact ZMod.val_injective p hb0
    · exact ZMod.val_injective p hb1
    · exact ZMod.val_injective p hb2
    · exact ZMod.val_injective p hb3
    · omega
  · apply Vector.ext; intro i hi
    rcases i with _|_|_|_|i
    · exact ZMod.val_injective p hc0
    · exact ZMod.val_injective p hc1
    · exact ZMod.val_injective p hc2
    · exact ZMod.val_injective p hc3
    · omega

/-- The **rich ROM-membership predicate** SP1's program/decode chip establishes for every received row —
the *received* facts `Foundations/Channels.lean`'s `ProgramMsg.Spec` defers: the register indices are
`< 32` (5-bit, from instruction decode), the pc limbs are `< 2^16`, and `op_a_0` is boolean. Instantiating
`programConsistent_of_balance` with this is what hands those bounds to every real instruction fetch. -/
def ProgramRowSpec (row : ProgramRow (ZMod p)) : Prop :=
  row.op_a.val < 32 ∧ row.op_b[0].val < 32 ∧ row.op_c[0].val < 32 ∧
  row.pc0.val < 2 ^ 16 ∧ row.pc1.val < 2 ^ 16 ∧ row.pc2.val < 2 ^ 16 ∧
  (row.op_a_0 = 0 ∨ row.op_a_0 = 1)

/-- The **`ProgramChip` provider**: any Program-bus contribution list whose every entry sits at the key of
some `inROM`-valid program row. This is the native, predicate-characterized content of SP1's preprocessed
program/decode chip — its trace carries *only* validly-decoded ROM rows. Generic over the membership
predicate `inROM` (instantiated with `ProgramRowSpec` to deliver the rich received facts), exactly as
`Chips/ByteChip.lean`'s `ByteProvider` is characterized by `ByteRowSpec`. -/
def ProgramProvider (inROM : ProgramRow (ZMod p) → Prop) (prov : LookupAccessList) : Prop :=
  ∀ b ∈ prov, ∃ row : ProgramRow (ZMod p), inROM row ∧ keyOf b = programRowKey row

/-- A program fetch whose key a `ProgramProvider` carries is an `inROM`-valid row. (The provider has a
valid row at that key; the key determines the row, so the fetched row *is* that valid row.) -/
theorem inROM_of_provider {inROM : ProgramRow (ZMod p) → Prop} {row : ProgramRow (ZMod p)}
    {prov : LookupAccessList} (h_prov : ProgramProvider inROM prov) {b : LookupAccess} (hb : b ∈ prov)
    (hk : keyOf b = programRowKey row) : inROM row := by
  obtain ⟨row', h_spec, h_key⟩ := h_prov b hb
  rw [hk] at h_key
  rwa [programRow_eq_of_key h_key]

end SP1Clean.ProgramChip
