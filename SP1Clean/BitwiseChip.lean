import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Lookup
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations.Constraint
import SP1Foundations.ByteOpcode
import SP1Foundations.Field
import SP1Operations.Operation.BitwiseU16Operation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader
import SP1Chips.BitwiseChip
import SP1Clean.BitwiseOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ALUTypeReader

/-! # Chip-level `BitwiseChip` mirror — bundled 6-variant ALU chip

The SP1 Bitwise chip bundles six RISC-V variants (xor/or/and × R-type/I-type)
into a single 51-column trace, distinguished by a one-hot `is_xor`/`is_or`/
`is_and` selector and an `imm_c` flag that toggles R-type vs I-type via the
shared `ALUTypeReader`.

This mirror exposes:
- `BitwiseCols T` — a `ProvableStruct` view of the 51 columns
- `main` — a best-effort Clean `Circuit` emitting the trailing assertZero
  gates plus the 2 CPUState range lookups (skipping the BitwiseU16/ALU
  sub-fragment lookups, since neither has a Clean operation wrapper yet —
  the iff-only pilot doesn't need them)
- `Spec` — predicate Spec matching the RHS of
  `_root_.Bitwise.allHold_constraints_iff_poly`, with `CPUState` and
  `ALUTypeReader` packaged via their Clean Spec helpers
- `iff_sp1` — chip-level bridge between SP1's `allHold_poly` and `Spec`
- Six `correct_<variant>` wrappers — each composes the corresponding
  `_root_.<Variant>.correct_<variant>` SP1 proof with `iff_sp1.mpr`
-/

namespace SP1Clean.Bitwise

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct, mirroring SP1's Rust `BitwiseCols<T>`. -/
structure BitwiseCols (T : Type) where
  clk_high : T
  clk_16_24 : T
  clk_0_16 : T
  pc : Vector T 3
  op_a : T
  op_a_memory_prev_value : Vector T 4
  op_a_memory_prev_low : T
  op_a_memory_diff_low : T
  op_a_0 : T
  op_b : T
  op_b_memory_prev_value : Vector T 4
  op_b_memory_prev_low : T
  op_b_memory_diff_low : T
  op_c : Vector T 4
  op_c_memory_prev_value : Vector T 4
  op_c_memory_prev_low : T
  op_c_memory_diff_low : T
  imm_c : T
  b_low_bytes : Vector T 4
  c_low_bytes : Vector T 4
  bitwise_result : Vector T 8
  is_xor : T
  is_or : T
  is_and : T
deriving ProvableStruct

/-- Clean-side circuit. Mirrors SP1 Rust's `BitwiseChip::eval(builder, cols)`
at the level the FormalAssertion below proves: emits the `CPUState.assertion`
subcircuit (the two clk byte lookups), the `ProgramTable.assertion`
subcircuit (the program-bus interaction with selector-weighted opcode),
and the trailing assertZero gates (opcode-selector binarity + op_a_0).
The 8 byte-opcode lookups (`BitwiseOperation`) and per-reader byte
ranges (`ALUTypeReader`) are intentionally omitted — neither sub-fragment
has a Clean operation wrapper yet; the `FormalAssertion` below proves
only what `main` actually emits. -/
def main (cols : Var BitwiseCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨_clk_high, clk_16_24, clk_0_16, pc, op_a, _op_a_memory_prev_value,
       _op_a_memory_prev_low, _op_a_memory_diff_low, op_a_0, op_b,
       _op_b_memory_prev_value, _op_b_memory_prev_low, _op_b_memory_diff_low,
       op_c, _op_c_memory_prev_value, _op_c_memory_prev_low,
       _op_c_memory_diff_low, imm_c, _b_low_bytes, _c_low_bytes,
       _bitwise_result, is_xor, is_or, is_and⟩ := cols
  -- CPUState range lookups (clk_0_16 progression + clk_16_24 U8 bound).
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  -- Program-bus interaction. Bitwise is a fan-out chip covering 6 opcodes
  -- (XOR/OR/AND × R/I). Opcode encoding mirrors SP1's selector arithmetic:
  -- `is_xor * 3 + is_or * 4 + is_and * 5` is the active opcode index (XOR=3,
  -- OR=4, AND=5). `imm_c` toggles R-type (single-limb op_c register index +
  -- three zero limbs) vs I-type (4 immediate limbs); we use the 4-limb
  -- `op_c` slot uniformly since R-type column `op_c` is just `op_c[0]` with
  -- limbs 1..3 zeroed by the trusted_instr_poly check.
  SP1Clean.ProgramTable.assertion
    (⟨pc, is_xor * 3 + is_or * 4 + is_and * 5,
      op_a, #v[op_b, 0, 0, 0], op_c, op_a_0, 0, imm_c⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  -- Trailing assertZero gates: the three opcode selectors are booleans,
  -- their sum is 0 or 1, and op_a_0 is forced to 0.
  is_xor * (is_xor - 1) === 0
  is_or * (is_or - 1) === 0
  is_and * (is_and - 1) === 0
  (is_xor + is_or + is_and) * (is_xor + is_or + is_and - 1) === 0
  op_a_0 === 0

/-- Pilot Spec, expressed over field-valued `BitwiseCols (ZMod p)`. Matches
the RHS of `_root_.Bitwise.allHold_constraints_iff_poly`: a propositional
clause for the `BitwiseU16Operation` sub-fragment (no Clean wrapper yet),
two Clean Spec helpers (`cpuStateSpec` / `aluTypeReaderSpec`), the four
boolean disjunctions on the opcode selectors, and `op_a_0 = 0`. -/
def Spec (cols : BitwiseCols (ZMod p)) : Prop :=
  let opcode_bw : ZMod p := cols.is_xor * 2 + cols.is_or * 1 + cols.is_and * 0
  let is_real : ZMod p := cols.is_xor + cols.is_or + cols.is_and
  let bw_cols : BitwiseU16Operation (ZMod p) :=
    { b_low_bytes := { low_bytes := cols.b_low_bytes },
      c_low_bytes := { low_bytes := cols.c_low_bytes },
      bitwise_operation := { result := cols.bitwise_result } }
  let ret_val : Word (ZMod p) :=
    (BitwiseU16Operation.constraints (F := ZMod p)
      cols.op_b_memory_prev_value cols.op_c_memory_prev_value
      bw_cols opcode_bw is_real).1
  List.Forall SP1Constraint.toProp_poly
    (BitwiseU16Operation.constraints (F := ZMod p)
      cols.op_b_memory_prev_value cols.op_c_memory_prev_value
      bw_cols opcode_bw is_real).2 ∧
  SP1Clean.CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 ∧
  SP1Clean.ALUTypeReader.aluTypeReaderSpec
      (cols.clk_0_16 + cols.clk_16_24 * 65536)
      (cols.is_xor * 3 + cols.is_or * 4 + cols.is_and * 5)
      cols.pc
      #v[ret_val[0], ret_val[1], ret_val[2], ret_val[3]]
      { op_a := cols.op_a,
        op_a_memory :=
          { prev_value := cols.op_a_memory_prev_value,
            access_timestamp :=
              { prev_low := cols.op_a_memory_prev_low,
                diff_low_limb := cols.op_a_memory_diff_low } },
        op_a_0 := cols.op_a_0, op_b := cols.op_b,
        op_b_memory :=
          { prev_value := cols.op_b_memory_prev_value,
            access_timestamp :=
              { prev_low := cols.op_b_memory_prev_low,
                diff_low_limb := cols.op_b_memory_diff_low } },
        op_c := cols.op_c,
        op_c_memory :=
          { prev_value := cols.op_c_memory_prev_value,
            access_timestamp :=
              { prev_low := cols.op_c_memory_prev_low,
                diff_low_limb := cols.op_c_memory_diff_low } },
        imm_c := cols.imm_c } ∧
  (cols.is_xor = 0 ∨ cols.is_xor = 1) ∧
  (cols.is_or = 0 ∨ cols.is_or = 1) ∧
  (cols.is_and = 0 ∨ cols.is_and = 1) ∧
  (cols.is_xor + cols.is_or + cols.is_and = 0 ∨
    cols.is_xor + cols.is_or + cols.is_and - 1 = 0) ∧
  cols.op_a_0 = 0

/-- Project a raw SP1 row into the structured `BitwiseCols` view. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 51) : BitwiseCols (ZMod p) :=
  ⟨Main[0], Main[1], Main[2],
   #v[Main[3], Main[4], Main[5]],
   Main[6],
   #v[Main[7], Main[8], Main[9], Main[10]],
   Main[11], Main[12], Main[13], Main[14],
   #v[Main[15], Main[16], Main[17], Main[18]],
   Main[19], Main[20],
   #v[Main[21], Main[22], Main[23], Main[24]],
   #v[Main[25], Main[26], Main[27], Main[28]],
   Main[29], Main[30], Main[31],
   #v[Main[32], Main[33], Main[34], Main[35]],
   #v[Main[36], Main[37], Main[38], Main[39]],
   #v[Main[40], Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47]],
   Main[48], Main[49], Main[50]⟩

set_option maxHeartbeats 800000 in
-- Chip-level bridge: SP1's `allHold_poly` over the flat row equals
-- `Spec (fromMain Main)` under `is_real = Main[48] + Main[49] + Main[50] = 1`.
-- 800K mirrors the budget of `Bitwise.allHold_constraints_iff_poly`, whose
-- 51-column conjunction plus the BitwiseU16/U16toU8 unfolding exceeds default.
theorem iff_sp1
    (Main : Vector (ZMod p) 51)
    (h_is_real : Main[48] + Main[49] + Main[50] = 1) :
    (_root_.Bitwise.constraints Main).allHold_poly ↔ Spec (fromMain Main) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  -- Bridge `.allHold_poly` (reducible) to `List.Forall toProp_poly` so the
  -- existing `Bitwise.allHold_constraints_iff_poly` lemma applies.
  change List.Forall SP1Constraint.toProp_poly (_root_.Bitwise.constraints Main) ↔ _
  rw [_root_.Bitwise.allHold_constraints_iff_poly]
  -- Collapse the `is_real` sum to `1` so the sub-iff lemmas fire.
  simp only [Spec, h_is_real]
  -- Bridge each sub-conjunct from `List.Forall toProp_poly (...)` to its
  -- `.allHold_poly` form so `cpuStateSpec_iff_sp1` / `aluTypeReaderSpec_iff_sp1`
  -- can rewrite it. The two forms are defn-equal (`.allHold_poly` is reducible).
  rw [show ∀ (cols : CPUState (ZMod p)) (next_pc : Vector (ZMod p) 3)
          (clk_increment is_real : ZMod p),
        List.Forall SP1Constraint.toProp_poly
          (CPUState.constraints cols next_pc clk_increment is_real) =
        (CPUState.constraints cols next_pc clk_increment is_real).allHold_poly
        from fun _ _ _ _ => rfl,
      show ∀ (clk_high clk_low opcode : ZMod p) (pc : Vector (ZMod p) 3)
          (op_a_write_value : Word (ZMod p)) (cols : ALUTypeReader (ZMod p))
          (is_real is_trusted : ZMod p),
        List.Forall SP1Constraint.toProp_poly
          (ALUTypeReader.constraints clk_high clk_low pc opcode op_a_write_value
            cols is_real is_trusted) =
        (ALUTypeReader.constraints clk_high clk_low pc opcode op_a_write_value
            cols is_real is_trusted).allHold_poly
        from fun _ _ _ _ _ _ _ _ => rfl]
  rw [SP1Clean.CPUState.cpuStateSpec_iff_sp1,
      SP1Clean.ALUTypeReader.aluTypeReaderSpec_iff_sp1]
  -- Final residual: `↑2 vs 2` coercion artifacts in the opcode arguments
  -- from `Bitwise.allHold_constraints_iff_poly`'s LHS-side polymorphic
  -- elaboration. After normalizing with push_cast both sides are identical
  -- (modulo the still-folded `cpuStateSpec` / `aluTypeReaderSpec` named calls).
  push_cast
  rfl

/-- Clean-side `correct_xor`: same Sail equivalence statement as SP1's
`Xor.correct_xor`, but with the constraint hypothesis re-expressed against
the Clean-flavored `Spec` predicate over a structured `BitwiseCols` view. -/
theorem correct_xor
    (Main : Vector (ZMod p) 51) (s : SailState)
    (h_is_real : Main[48] + Main[49] + Main[50] = 1)
    (h_is_xor : Main[48] = 1) (h_imm_c : Main[31] = 0)
    (h_spec : Spec (fromMain Main))
    (state_cstrs : (_root_.Bitwise.constraints Main).initialState_poly s) :
    let op_c := _root_.Xor.sp1_op_c Main
    let op_b := _root_.Xor.sp1_op_b Main
    let op_a := _root_.Xor.sp1_op_a Main
    (_root_.Xor.spec_xor (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.Bitwise.sp1_bitwise Main).run s :=
  _root_.Xor.correct_xor Main s ((iff_sp1 Main h_is_real).mpr h_spec)
    ⟨h_is_xor, h_imm_c⟩ state_cstrs

/-- Clean-side `correct_or`. -/
theorem correct_or
    (Main : Vector (ZMod p) 51) (s : SailState)
    (h_is_real : Main[48] + Main[49] + Main[50] = 1)
    (h_is_or : Main[49] = 1) (h_imm_c : Main[31] = 0)
    (h_spec : Spec (fromMain Main))
    (state_cstrs : (_root_.Bitwise.constraints Main).initialState_poly s) :
    let op_c := _root_.Or.sp1_op_c Main
    let op_b := _root_.Or.sp1_op_b Main
    let op_a := _root_.Or.sp1_op_a Main
    (_root_.Or.spec_or (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.Bitwise.sp1_bitwise Main).run s :=
  _root_.Or.correct_or Main s ((iff_sp1 Main h_is_real).mpr h_spec)
    ⟨h_is_or, h_imm_c⟩ state_cstrs

/-- Clean-side `correct_and`. -/
theorem correct_and
    (Main : Vector (ZMod p) 51) (s : SailState)
    (h_is_real : Main[48] + Main[49] + Main[50] = 1)
    (h_is_and : Main[50] = 1) (h_imm_c : Main[31] = 0)
    (h_spec : Spec (fromMain Main))
    (state_cstrs : (_root_.Bitwise.constraints Main).initialState_poly s) :
    let op_c := _root_.And.sp1_op_c Main
    let op_b := _root_.And.sp1_op_b Main
    let op_a := _root_.And.sp1_op_a Main
    (_root_.And.spec_and (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.Bitwise.sp1_bitwise Main).run s :=
  _root_.And.correct_and Main s ((iff_sp1 Main h_is_real).mpr h_spec)
    ⟨h_is_and, h_imm_c⟩ state_cstrs

/-- Clean-side `correct_xori`. -/
theorem correct_xori
    (Main : Vector (ZMod p) 51) (s : SailState)
    (h_is_real : Main[48] + Main[49] + Main[50] = 1)
    (h_is_xor : Main[48] = 1) (h_imm_c : Main[31] = 1)
    (h_spec : Spec (fromMain Main))
    (state_cstrs : (_root_.Bitwise.constraints Main).initialState_poly s) :
    let op_c := _root_.Xori.sp1_op_c Main
    let op_b := _root_.Xori.sp1_op_b Main
    let op_a := _root_.Xori.sp1_op_a Main
    (_root_.Xori.spec_xori op_c (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.Bitwise.sp1_bitwise Main).run s :=
  _root_.Xori.correct_xori Main s ((iff_sp1 Main h_is_real).mpr h_spec)
    ⟨h_is_xor, h_imm_c⟩ state_cstrs

/-- Clean-side `correct_ori`. -/
theorem correct_ori
    (Main : Vector (ZMod p) 51) (s : SailState)
    (h_is_real : Main[48] + Main[49] + Main[50] = 1)
    (h_is_or : Main[49] = 1) (h_imm_c : Main[31] = 1)
    (h_spec : Spec (fromMain Main))
    (state_cstrs : (_root_.Bitwise.constraints Main).initialState_poly s) :
    let op_c := _root_.Ori.sp1_op_c Main
    let op_b := _root_.Ori.sp1_op_b Main
    let op_a := _root_.Ori.sp1_op_a Main
    (_root_.Ori.spec_ori op_c (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.Bitwise.sp1_bitwise Main).run s :=
  _root_.Ori.correct_ori Main s ((iff_sp1 Main h_is_real).mpr h_spec)
    ⟨h_is_or, h_imm_c⟩ state_cstrs

/-- Clean-side `correct_andi`. -/
theorem correct_andi
    (Main : Vector (ZMod p) 51) (s : SailState)
    (h_is_real : Main[48] + Main[49] + Main[50] = 1)
    (h_is_and : Main[50] = 1) (h_imm_c : Main[31] = 1)
    (h_spec : Spec (fromMain Main))
    (state_cstrs : (_root_.Bitwise.constraints Main).initialState_poly s) :
    let op_c := _root_.Andi.sp1_op_c Main
    let op_b := _root_.Andi.sp1_op_b Main
    let op_a := _root_.Andi.sp1_op_a Main
    (_root_.Andi.spec_andi op_c (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.Bitwise.sp1_bitwise Main).run s :=
  _root_.Andi.correct_andi Main s ((iff_sp1 Main h_is_real).mpr h_spec)
    ⟨h_is_and, h_imm_c⟩ state_cstrs

/-! ## Full `FormalAssertion` promotion

Wraps the chip's `main` (CPUState lookups + ProgramTable lookup + 4
boolean asserts + 1 zero assert) into a Clean `FormalAssertion`. The
`FormalSpec` is the byte and program lookup-derivable subset of `Spec`:
specifically it drops the `BitwiseU16Operation` carry-chain content and
the `aluTypeReaderSpec` register-read content (neither has a Clean
operation wrapper yet, and `main` does not emit those lookups).

Composes `CPUState.assertion` and `ProgramTable.assertion` as
subcircuits. -/

namespace Assertion

open Circuit ProvableType

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) BitwiseCols unit where
  name := "SP1Clean.Bitwise"
  main := main
  localLength _ := 0

def Assumptions (_ : BitwiseCols (ZMod p)) : Prop := True

/-- The byte- and program-lookup-derivable subset of `Spec`. Includes
the two sub-assertion consequences plus the four trailing assert
clauses. Drops the BitwiseU16 carry chain + `aluTypeReaderSpec`
content, which is not derivable from `main`'s lookups alone. -/
def FormalSpec (cols : BitwiseCols (ZMod p)) : Prop :=
  SP1Clean.CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.pc,
      opcode := cols.is_xor * 3 + cols.is_or * 4 + cols.is_and * 5,
      op_a := cols.op_a,
      op_b := #v[cols.op_b, 0, 0, 0],
      op_c := cols.op_c,
      op_a_0 := cols.op_a_0, imm_b := 0, imm_c := cols.imm_c } ∧
  cols.is_xor * (cols.is_xor - 1) = 0 ∧
  cols.is_or * (cols.is_or - 1) = 0 ∧
  cols.is_and * (cols.is_and - 1) = 0 ∧
  (cols.is_xor + cols.is_or + cols.is_and)
    * (cols.is_xor + cols.is_or + cols.is_and - 1) = 0 ∧
  cols.op_a_0 = 0

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨h_cpu_sub, h_prog_sub, h_xor, h_or, h_and, h_sum, h_op_a_0⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_prog_sub trivial
  · linear_combination h_xor
  · linear_combination h_or
  · linear_combination h_and
  · linear_combination h_sum
  · exact h_op_a_0

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨h_cpu, h_prog, h_xor, h_or, h_and, h_sum, h_op_a_0⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_prog⟩
  · linear_combination h_xor
  · linear_combination h_or
  · linear_combination h_and
  · linear_combination h_sum
  · exact h_op_a_0

end Assertion

/-- The full Clean `FormalAssertion` for the byte- and program-lookup-
derivable subset of `BitwiseChip`'s constraint surface. Composes
`CPUState.assertion` and the `ProgramTable` lookup with four trailing
assertZero gates. Multi-variant analog of `SP1Clean.Add.assertion`. -/
def assertion : FormalAssertion (ZMod p) BitwiseCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.Bitwise
