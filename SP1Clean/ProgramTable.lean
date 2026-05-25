import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Utils.Field
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations.Constraint
import SP1Foundations.Opcode
import SP1Foundations.Assumptions
import SP1Clean.SP1Lookup

/-! # Clean-side mirror of SP1's program-bus interactions

This file defines the lookup table that mirrors SP1's
`send (.program pc0 pc1 pc2 opcode op_a op_b_0..3 op_c_0..3 op_a_0 imm_b imm_c) mult`
interactions emitted by readers (R-type, I-type, ALU-type, etc.).

The program bus is "send-only" in SP1 — there is no receive side; chips
trust the row's claim that it is executing `opcode` at `pc`. We mirror this
on the Clean side with a **stateless** `Table` whose `Contains` predicate
is exactly the RHS of `SP1Constraint.toProp` for the `.program` case
in `SP1Foundations/Constraint.lean`:

  opcode.trusted_instr ∧ register bounds ∧ PC alignment ∧ flag binarity ∧
  (op_a_0 ↔ op_a = 0)

Per the pilot's convention (see `SP1Clean/ByteOpcodeTable.lean`), SP1's
multiplicity is dropped here; per-row this is sound because every program
send carries `is_trusted = 1` from the surrounding reader.

The row layout `#v[pc0, pc1, pc2, opcode, op_a, op_b_0..3, op_c_0..3, op_a_0,
imm_b, imm_c]` (16 fields) matches `AirInteraction.program` from
`SP1Foundations/Constraint.lean:9-22`, with `opcode` encoded as a field
element whose `.val` projects back to `Opcode.ofNat`.
-/

namespace SP1Clean

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Spec of `ProgramTable`. A 16-tuple
`#v[pc0, pc1, pc2, opcode, op_a, op_b_0..3, op_c_0..3, op_a_0, imm_b, imm_c]`
is in the table iff the corresponding `AirInteraction.program` clause's
`SP1Constraint.toProp` (under `mult = 1`) holds. -/
def ProgramSpec (row : fields 16 (ZMod p)) : Prop :=
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  (Opcode.ofNat row[3].val).trusted_instr
      row[4] row[5] row[6] row[7] row[8] row[9] row[10] row[11] row[12]
      row[14] row[15]
    ∧ row[4] < (32 : ZMod p)
    ∧ (row[5] < (65536 : ZMod p) ∧ row[6] < (65536 : ZMod p) ∧
       row[7] < (65536 : ZMod p) ∧ row[8] < (65536 : ZMod p))
    ∧ (row[9] < (65536 : ZMod p) ∧ row[10] < (65536 : ZMod p) ∧
       row[11] < (65536 : ZMod p) ∧ row[12] < (65536 : ZMod p))
    ∧ (row[13] = 0 ∨ row[13] = 1)
    ∧ (row[13] = 1 ↔ row[4] = 0)
    ∧ (row[14] = 0 ∨ row[14] = 1)
    ∧ (row[15] = 0 ∨ row[15] = 1)
    ∧ (row[0] % 4 = 0 ∧ row[0] < (65536 : ZMod p) ∧
       row[1] < (65536 : ZMod p) ∧ row[2] < (65536 : ZMod p))

/-- The polymorphic program table.

`Contains := Soundness := Completeness := ProgramSpec`. Like
`ByteOpcodeTable`, this sidesteps a `StaticTable` enumeration (a full RV64IM
program ROM would have to list every valid instruction encoding — overkill
for the pilot, whose goal is the per-row equivalence to SP1's
`toProp`). -/
def ProgramTable : Table (ZMod p) (fields 16) where
  name := "SP1Program"
  Contains _ row := ProgramSpec row
  Soundness _ row := ProgramSpec row
  Completeness _ row := ProgramSpec row

namespace ProgramTable

open Circuit

/-- Bundled inputs for the program-bus assertion. Mirrors
`AirInteraction.program`'s 16 fields: 3-limb PC, opcode field-encoded,
op_a register index, op_b's four limbs, op_c's four limbs, the op_a_0
flag, and the two immediate-mode flags `imm_b`, `imm_c`.

`pc`, `op_b`, `op_c` are kept as `Vector` fields (3 and 4 limbs) so that
the destructuring lines up with chip-level column structs like `AddCols`
and propagation of `h_input` equalities through `Vector.map` works
uniformly with the existing `circuit_norm` simp set. -/
structure Inputs (F : Type) where
  pc : Vector F 3
  opcode : F
  op_a : F
  op_b : Vector F 4
  op_c : Vector F 4
  op_a_0 : F
  imm_b : F
  imm_c : F
deriving ProvableStruct

/-- Clean-side circuit: one `ProgramTable` lookup over the 16 input fields. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  lookup ProgramTable
    (#v[input.pc[0], input.pc[1], input.pc[2], input.opcode, input.op_a,
        input.op_b[0], input.op_b[1], input.op_b[2], input.op_b[3],
        input.op_c[0], input.op_c[1], input.op_c[2], input.op_c[3],
        input.op_a_0, input.imm_b, input.imm_c]
      : Vector (Expression (ZMod p)) 16)

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.ProgramTable"
  main := main
  localLength _ := 0

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- The spec: the assembled 16-tuple row is in the program table. Stated
exactly as `SP1Clean.ProgramSpec` on the corresponding row vector. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  SP1Clean.ProgramSpec
    (#v[input.pc[0], input.pc[1], input.pc[2], input.opcode, input.op_a,
        input.op_b[0], input.op_b[1], input.op_b[2], input.op_b[3],
        input.op_c[0], input.op_c[1], input.op_c[2], input.op_c[3],
        input.op_a_0, input.imm_b, input.imm_c]
      : fields 16 (ZMod p))

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨ep, eo, ea, eb, ec, ea0, eib, eic⟩ := h_input
  subst ep; subst eo; subst ea; subst eb; subst ec; subst ea0
  subst eib; subst eic
  simp only [Spec, Vector.getElem_map]
  simp only [main, circuit_norm, Lookup.Soundness, Table.toRaw,
             SP1Clean.ProgramTable] at h_holds
  exact h_holds

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨ep, eo, ea, eb, ec, ea0, eib, eic⟩ := h_input
  subst ep; subst eo; subst ea; subst eb; subst ec; subst ea0
  subst eib; subst eic
  simp only [Spec, Vector.getElem_map] at h_spec
  simp only [main, circuit_norm, Lookup.Completeness, Table.toRaw,
             SP1Clean.ProgramTable]
  exact h_spec

end ProgramTable

/-- The Clean `FormalAssertion` for one program-bus interaction: a single
lookup against `ProgramTable` whose `Spec` is `ProgramSpec` on the assembled
16-tuple. Composes into any chip-level `main` as a subcircuit. -/
def ProgramTable.assertion : FormalAssertion (ZMod p) ProgramTable.Inputs :=
  { ProgramTable.elaborated with
    Assumptions := ProgramTable.Assumptions,
    Spec := ProgramTable.Spec,
    soundness := ProgramTable.soundness,
    completeness := ProgramTable.completeness }

end SP1Clean

/-! ## `HasDefaultRow` for `ProgramTable`

To use the multiplicity-aware `SP1Lookup.lookupGated` with `ProgramTable`
(needed by readers that thread `is_trusted` through the program-bus
interaction), we need a known-valid default row. We use the `UNIMP`
opcode (52), whose `trusted_instr` predicate is trivially `True` for any
operand values (`SP1Foundations/Assumptions.lean:137`). -/

namespace SP1Clean

/-- Default row for `ProgramTable`: opcode = UNIMP (52), op_a_0 = 1
(matching op_a = 0 in the op_a_0 iff), all other fields zero. UNIMP's
`trusted_instr` branch is `True`, so the row satisfies `ProgramSpec`
unconditionally. -/
instance ProgramTable.hasDefaultRow
    {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)] :
    SP1Lookup.HasDefaultRow (SP1Clean.ProgramTable : Table (ZMod p) (fields 16)) where
  defaultRow := #v[0, 0, 0, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
  defaultRow_in_table := by
    intro _
    haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    have hp : 2 ^ 17 < p := Fact.out
    have h65536 : (65536 : ZMod p).val = 65536 := by
      rw [show (65536 : ZMod p) = ((65536 : ℕ) : ZMod p) from by push_cast; rfl,
          ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have h32 : (32 : ZMod p).val = 32 := by
      rw [show (32 : ZMod p) = ((32 : ℕ) : ZMod p) from by push_cast; rfl,
          ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have h52 : (52 : ZMod p).val = 52 := by
      rw [show (52 : ZMod p) = ((52 : ℕ) : ZMod p) from by push_cast; rfl,
          ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have h_zero_lt_32 : (0 : ZMod p) < (32 : ZMod p) := by
      change (0 : ZMod p).val < (32 : ZMod p).val; simp [h32]
    have h_zero_lt_65536 : (0 : ZMod p) < (65536 : ZMod p) := by
      change (0 : ZMod p).val < (65536 : ZMod p).val; simp [h65536]
    -- The default row's ProgramSpec: discharge each clause.
    refine ⟨?_, h_zero_lt_32,
            ⟨h_zero_lt_65536, h_zero_lt_65536, h_zero_lt_65536, h_zero_lt_65536⟩,
            ⟨h_zero_lt_65536, h_zero_lt_65536, h_zero_lt_65536, h_zero_lt_65536⟩,
            Or.inr ?_, ?_, Or.inl ?_, Or.inl ?_,
            ?_, h_zero_lt_65536, h_zero_lt_65536, h_zero_lt_65536⟩
    -- trusted_instr: row[3] = 52 ⇒ Opcode.UNIMP whose trusted_instr branch is True
    · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
                 List.getElem_cons_succ, h52,
                 show (Opcode.ofNat 52 : Opcode) = .UNIMP from rfl,
                 Opcode.trusted_instr]
    -- op_a_0 = 1 (right disjunct of {0, 1})
    · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
                 List.getElem_cons_succ]
    -- op_a_0 = 1 ↔ op_a = 0 (both sides are 1 = 1 / 0 = 0 trivially)
    · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
                 List.getElem_cons_succ]
    -- imm_b = 0 (left disjunct of {0, 1})
    · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
                 List.getElem_cons_succ]
    -- imm_c = 0 (left disjunct of {0, 1})
    · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
                 List.getElem_cons_succ]
    -- pc[0] % 4 = 0 (pc[0] = 0)
    · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero]
      rw [val_mod_4_eq_zero_iff_zmod]
      simp

end SP1Clean
