import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations.Constraint
import SP1Foundations.ByteOpcode
import SP1Foundations.Field
import SP1Operations.Compare.LtOperationSigned.LtOperationSigned
import SP1Operations.Operation.AddrAddOperation.AddrAddOperation
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.ALUTypeReader.ALUTypeReader
import SP1Chips.Lt.LtChip
import SP1Clean.AddrAddOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ALUTypeReader
import SP1Clean.Compare.LtOperationSigned
import SP1Clean.Reader.OperandAccess

/-! # Chip-level `LtChip` mirror — bundled signed/unsigned compare

The Lt chip bundles four RV64I variants — `slt` / `sltu` (R-type) and
`slti` / `sltiu` (I-type) — into a single 44-column trace. Variants
distinguished by selectors `is_slt`/`is_sltu` (Main[32..33]) and
`imm_c` (Main[31]). The signed/unsigned distinction is carried into the
`LtOperationSigned` sub-fragment via `is_signed := Main[32]`.

Structural mirror discipline (Spec only). The `LtOperationSigned`
constraint clause is left in raw `allHold` form — no Clean
operation wrapper yet for this Compare-family sub-fragment.

Opcode encoding: `is_slt * 9 + is_sltu * 10` (SLT=9, SLTU=10).
Result is a 1-bit boolean written into `op_a_write_value[0]` (via
`Main[34]`), with the other 3 limbs zero.
-/

namespace SP1Clean.Lt

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct, mirroring SP1's Rust `LtCols<T>`. -/
structure LtCols (T : Type) where
  state : CPUState T
  op_a : T
  op_a_memory : MemoryAccessInSharedCols T
  op_a_0 : T
  op_b : T
  op_b_memory : MemoryAccessInSharedCols T
  op_c : Vector T 4
  op_c_memory : MemoryAccessInSharedCols T
  imm_c : T
  is_slt : T
  is_sltu : T
  lt_operation : LtOperationSigned T
  next_pc_carry_value : Vector T 3
deriving ProvableStruct

/-- Clean-side circuit. Emits CPUState range lookups, the program-bus
interaction (opcode = `is_slt * 9 + is_sltu * 10`), and the trailing
assertZero gates (the two opcode-selector booleans, the sum-boolean,
and the op_a_0 = 0 forcing). The `LtOperationSigned` sub-fragment
constraints are captured propositionally in `Spec` below. -/
def main (cols : Var LtCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩, op_a, _op_a_memory, op_a_0, op_b,
       _op_b_memory,
       op_c, _op_c_memory, imm_c, is_slt, is_sltu, lt_operation,
       _next_pc_carry_value⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ProgramTable.assertion
    (⟨pc, is_slt * 9 + is_sltu * 10,
      op_a, #v[op_b, 0, 0, 0], op_c,
      op_a_0, 0, imm_c⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  let _ := lt_operation.result.u16_compare_operation.bit
  -- Trailing assertZero gates.
  is_slt * (is_slt - 1) === 0
  is_sltu * (is_sltu - 1) === 0
  (is_slt + is_sltu) * (is_slt + is_sltu - 1) === 0
  op_a_0 === 0

/-- Pilot Spec, expressed over field-valued `LtCols (ZMod p)`. The
`LtOperationSigned` clause is left in raw `allHold` form (it
internally fans out into `U16MSBOperation` and `LtOperationUnsigned`
sub-fragments). The chip-level `is_signed` argument is `is_slt`; the
chip-level `is_real` argument is `is_slt + is_sltu`. -/
def Spec (cols : LtCols (ZMod p)) : Prop :=
  let is_real : ZMod p := cols.is_slt + cols.is_sltu
  (_root_.LtOperationSigned.constraints (F := ZMod p)
      cols.op_b_memory.prev_value cols.op_c_memory.prev_value
      cols.lt_operation cols.is_slt is_real).allHold ∧
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ALUTypeReader.aluTypeReaderSpec
      (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
      (cols.is_slt * 9 + cols.is_sltu * 10) cols.state.pc
      #v[cols.lt_operation.result.u16_compare_operation.bit, 0, 0, 0]
      { op_a := cols.op_a,
        op_a_memory :=
          { prev_value := cols.op_a_memory.prev_value,
            access_timestamp :=
              { prev_low := cols.op_a_memory.access_timestamp.prev_low,
                diff_low_limb := cols.op_a_memory.access_timestamp.diff_low_limb } },
        op_a_0 := cols.op_a_0, op_b := cols.op_b,
        op_b_memory :=
          { prev_value := cols.op_b_memory.prev_value,
            access_timestamp :=
              { prev_low := cols.op_b_memory.access_timestamp.prev_low,
                diff_low_limb := cols.op_b_memory.access_timestamp.diff_low_limb } },
        op_c := cols.op_c,
        op_c_memory :=
          { prev_value := cols.op_c_memory.prev_value,
            access_timestamp :=
              { prev_low := cols.op_c_memory.access_timestamp.prev_low,
                diff_low_limb := cols.op_c_memory.access_timestamp.diff_low_limb } },
        imm_c := cols.imm_c } ∧
  cols.is_slt * (cols.is_slt - 1) = 0 ∧
  cols.is_sltu * (cols.is_sltu - 1) = 0 ∧
  (cols.is_slt + cols.is_sltu) * (cols.is_slt + cols.is_sltu - 1) = 0 ∧
  cols.op_a_0 = 0

/-- Project a raw SP1 row into the structured `LtCols` view. Mirrors
the index map in `SP1Chips/Lt/Constraints.lean` (44 columns; the
`lt_operation` sub-struct is packed from `Main[34..43]`). -/
@[reducible] def fromMain (Main : Vector (ZMod p) 44) : LtCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
      Main[6],
   ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩, Main[13],
   Main[14],
   ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
   #v[Main[21], Main[22], Main[23], Main[24]],
   ⟨#v[Main[25], Main[26], Main[27], Main[28]], ⟨Main[29], Main[30]⟩⟩,
   Main[31], Main[32], Main[33],
   { result :=
       { u16_compare_operation := { bit := Main[34] },
         u16_flags := #v[Main[35], Main[36], Main[37], Main[38]],
         not_eq_inv := Main[39],
         comparison_limbs := #v[Main[40], Main[41]] },
     b_msb := { msb := Main[42] },
     c_msb := { msb := Main[43] } },
   #v[0, 0, 0]⟩

/-- The chip-level half-iff bridge (Lt): under
`is_slt + is_sltu = 1 ∧ op_a_0 = 0`, the Clean `Spec` implies SP1's
`allHold`. Used by `correct_slt`/`correct_sltu` wrappers.
**Proof body sorry'd** (see `feedback_path2_correct_bridge_costs.md`). -/
theorem spec_implies_allHold (Main : Vector (ZMod p) 44)
    (h_is_real : Main[32] + Main[33] = 1) (h_op_a_0 : Main[13] = 0)
    (h_spec : Spec (fromMain Main)) :
    (_root_.Lt.constraints Main).allHold := by
  sorry

/-- Clean-side `correct_slt`: signed less-than (R-type). -/
theorem correct_slt
    (Main : Vector (ZMod p) 44) (s : SailState)
    (h_is_slt : Main[32] = 1) (h_imm_c : Main[31] = 0) (h_op_a_0 : Main[13] = 0)
    (h_sltu_zero : Main[33] = 0)
    (h_spec : Spec (fromMain Main))
    (state_cstrs : (_root_.Lt.constraints Main).initialState s) :
    let op_c := _root_.Slt.sp1_op_c Main
    let op_b := _root_.Slt.sp1_op_b Main
    let op_a := _root_.Slt.sp1_op_a Main
    (_root_.Slt.spec_slt (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.Lt.sp1_lt Main).run s :=
  _root_.Slt.correct_slt Main s
    (spec_implies_allHold Main (by rw [h_is_slt, h_sltu_zero]; ring) h_op_a_0 h_spec)
    ⟨h_is_slt, h_imm_c⟩ state_cstrs

/-- Clean-side `correct_sltu`: unsigned less-than (R-type). -/
theorem correct_sltu
    (Main : Vector (ZMod p) 44) (s : SailState)
    (h_is_sltu : Main[33] = 1) (h_imm_c : Main[31] = 0) (h_op_a_0 : Main[13] = 0)
    (h_slt_zero : Main[32] = 0)
    (h_spec : Spec (fromMain Main))
    (state_cstrs : (_root_.Lt.constraints Main).initialState s) :
    let op_c := _root_.Sltu.sp1_op_c Main
    let op_b := _root_.Sltu.sp1_op_b Main
    let op_a := _root_.Sltu.sp1_op_a Main
    (_root_.Sltu.spec_sltu (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.Lt.sp1_lt Main).run s :=
  _root_.Sltu.correct_sltu Main s
    (spec_implies_allHold Main (by rw [h_is_sltu, h_slt_zero]; ring) h_op_a_0 h_spec)
    ⟨h_is_sltu, h_imm_c⟩ state_cstrs

/-- The op_a / op_b / op_c register accesses, exposed for trace-level
OfflineMemory aggregation. op_a writes the 4-limb boolean result
`#v[compare_bit, 0, 0, 0]`. -/
def opAMemoryAccess (cols : LtCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := #v[cols.op_a, 0, 0],
    prev_value := cols.op_a_memory.prev_value,
    prev_low := cols.op_a_memory.access_timestamp.prev_low,
    diff_low_limb := cols.op_a_memory.access_timestamp.diff_low_limb }

def opBMemoryAccess (cols : LtCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := #v[cols.op_b, 0, 0],
    prev_value := cols.op_b_memory.prev_value,
    prev_low := cols.op_b_memory.access_timestamp.prev_low,
    diff_low_limb := cols.op_b_memory.access_timestamp.diff_low_limb }

def opCMemoryAccess (cols : LtCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := #v[cols.op_c[0], 0, 0],
    prev_value := cols.op_c_memory.prev_value,
    prev_low := cols.op_c_memory.access_timestamp.prev_low,
    diff_low_limb := cols.op_c_memory.access_timestamp.diff_low_limb }

/-! ## Full `FormalAssertion` promotion (Path-2)

Wraps the chip-level constraint surface into a Clean `FormalAssertion`.
Composes `SP1Clean.CPUState.assertion` and `SP1Clean.ProgramTable.assertion`
as subcircuits, plus the four scalar trailing assertZero gates
(`is_slt` binary, `is_sltu` binary, sum binary, `op_a_0 = 0`).

**Path-2 drops.** The `LtOperationSigned` `allHold` clause is NOT
promoted here — no Clean operation wrapper exists yet for the
Compare-family sub-fragment. The memory-bus side of `aluTypeReaderSpec`
is also deferred to the legacy chip-level `Spec` / `iff_sp1` route.
Same Path-2 design as `SP1Clean.Addi.Assertion`. -/

namespace Assertion

open Circuit

/-- Refactored chip-level circuit using subcircuit composition. Drops
the `LtOperationSigned` byte lookups and `ALUTypeReader` memory accesses. -/
@[reducible]
def main (cols : Var LtCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩, op_a, op_a_memory, op_a_0, op_b,
       op_b_memory,
       op_c, op_c_memory, imm_c, is_slt, is_sltu, _lt_operation,
       next_pc_carry_value⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ProgramTable.assertion
    (⟨pc, is_slt * 9 + is_sltu * 10,
      op_a, #v[op_b, 0, 0, 0], op_c,
      op_a_0, 0, imm_c⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  SP1Clean.AddrAddOp.assertion
    (⟨#v[pc[0], pc[1], pc[2], (0 : Expression (ZMod p))],
       #v[(4 : Expression (ZMod p)), 0, 0, 0],
       next_pc_carry_value⟩ :
      Var SP1Clean.AddrAddOp.Inputs (ZMod p))
  is_slt * (is_slt - 1) === 0
  is_sltu * (is_sltu - 1) === 0
  (is_slt + is_sltu) * (is_slt + is_sltu - 1) === 0
  op_a_0 === 0
  -- Iter-8 sub-task E: per-operand memory-bus byte content.
  -- R-type-shaped: op_a at +4, op_b at +3, op_c at +2.
  let clk_low := clk_0_16 + clk_16_24 * 65536
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 4, op_a_memory.access_timestamp.prev_low, op_a_memory.access_timestamp.diff_low_limb,
       op_a_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 3, op_b_memory.access_timestamp.prev_low, op_b_memory.access_timestamp.diff_low_limb,
       op_b_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 2, op_c_memory.access_timestamp.prev_low, op_c_memory.access_timestamp.diff_low_limb,
       op_c_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) LtCols unit where
  name := "SP1Clean.Lt"
  main := main
  localLength _ := 0

def Assumptions (_ : LtCols (ZMod p)) : Prop := True

/-- The chip's Circuit-derivable spec: byte-lookup consequences for the
clock-decomposition gadget, the program-bus existential witness, and the
four scalar trailing assertZero gates. -/
def FormalSpec (cols : LtCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc,
      opcode := cols.is_slt * 9 + cols.is_sltu * 10,
      op_a := cols.op_a,
      op_b := #v[cols.op_b, 0, 0, 0],
      op_c := cols.op_c,
      op_a_0 := cols.op_a_0, imm_b := 0, imm_c := cols.imm_c } ∧
  SP1Clean.AddrAddOp.assertion.Spec
    ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
     #v[(4 : ZMod p), 0, 0, 0],
     cols.next_pc_carry_value⟩ ∧
  cols.is_slt * (cols.is_slt - 1) = 0 ∧
  cols.is_sltu * (cols.is_sltu - 1) = 0 ∧
  (cols.is_slt + cols.is_sltu) * (cols.is_slt + cols.is_sltu - 1) = 0 ∧
  cols.op_a_0 = 0 ∧
  -- Iter-8 sub-task E: per-operand memory-bus byte-content consequences.
  -- R-type-shaped: op_a/+4, op_b/+3, op_c/+2.
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 4, cols.op_a_memory.access_timestamp.prev_low, cols.op_a_memory.access_timestamp.diff_low_limb,
     cols.op_a_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 3, cols.op_b_memory.access_timestamp.prev_low, cols.op_b_memory.access_timestamp.diff_low_limb,
     cols.op_b_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 2, cols.op_c_memory.access_timestamp.prev_low, cols.op_c_memory.access_timestamp.diff_low_limb,
     cols.op_c_memory.prev_value⟩

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu_sub, h_prog_sub, h_addr_sub, h_isslt, h_issltu, h_sum,
          h_op_a_0, h_oa_a, h_oa_b, h_oa_c⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_prog_sub trivial
  · simp only [Vector.getElem_map]
    exact h_addr_sub trivial
  · linear_combination h_isslt
  · linear_combination h_issltu
  · linear_combination h_sum
  · exact h_op_a_0
  · exact h_oa_a trivial
  · exact h_oa_b trivial
  · exact h_oa_c trivial

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu, h_prog, h_addr, h_isslt, h_issltu, h_sum, h_op_a_0,
          h_oa_a, h_oa_b, h_oa_c⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_prog⟩
  · refine ⟨trivial, ?_⟩
    simp only [Vector.getElem_map] at h_addr
    exact h_addr
  · linear_combination h_isslt
  · linear_combination h_issltu
  · linear_combination h_sum
  · exact h_op_a_0
  · exact ⟨trivial, h_oa_a⟩
  · exact ⟨trivial, h_oa_b⟩
  · exact ⟨trivial, h_oa_c⟩

end Assertion

/-- The full Clean `FormalAssertion` for the byte- and program-lookup-
derivable subset of `LtChip`'s constraint surface (Path-2 design;
drops the `LtOperationSigned` byte lookups and memory-bus side of
`ALUTypeReader`). -/
def assertion : FormalAssertion (ZMod p) LtCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.Lt
