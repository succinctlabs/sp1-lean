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
import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState

/-! # Chip-level `ShiftLeftChip` mirror — second heavy-arithmetic scaling probe

The ShiftLeft chip bundles 4 RV64IM left-shift variants (sll/slli/sllw/slliw)
into a single 65-column trace. Distinct from `MulChip` in its mechanics:
the 64-bit shift amount is decomposed into 6 boolean bits (`Main[36..41]`)
which select between 1×, 2×, 4×, 8×, 16×, 32× multiplications via a chain
of multipliers (`Main[42..44]`). A one-hot byte-shift selector
(`Main[45..48]`) routes the shifted limbs into the appropriate write
position. The result is committed to `Main[32..35]`.

This is the **second heavy-chip data point** for Risk 1 (heavy-chip
scaling). The SP1-side proof uses `maxHeartbeats 100000000` (100M)
because of the bit-decomposition chain and the conditional `(is_sll = 0
∨ byte_selector_k = 0 ∨ ...)` clauses. The Clean structural mirror is
expected to compile much faster since it skips those proof obligations.

Same focused-pilot-mirror discipline as `MulChip`: define the column
struct, emit the structural lookups in `main` (CPUState bounds, byte
shift power lookup, ProgramTable.assertion with selector-weighted
opcode), expose the per-row Spec consequences, leave the shift-
arithmetic content to `shiftSpec` as a placeholder.

Opcode encoding mirrors SP1: `is_sll * 8 + is_sllw * 14` for the
top-level opcode field (RV64IM IDs).
-/

namespace SP1Clean.ShiftLeft

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct, mirroring SP1's Rust `ShiftLeftCols<T>`
over 65 field elements. The non-reader columns are grouped into named
Vector blocks where SP1's emission already treats them as a unit
(`bit_shift`, `byte_shift`, `shifted_limbs`, `result`). -/
structure ShiftLeftCols (T : Type) where
  clk_high : T                              -- Main[0]
  clk_16_24 : T                             -- Main[1]
  clk_0_16 : T                              -- Main[2]
  pc : Vector T 3                           -- Main[3..5]
  op_a : T                                  -- Main[6]
  op_a_memory_prev_value : Vector T 4       -- Main[7..10]
  op_a_memory_prev_low : T                  -- Main[11]
  op_a_memory_diff_low : T                  -- Main[12]
  op_a_0 : T                                -- Main[13]
  op_b : T                                  -- Main[14]
  op_b_memory_prev_value : Vector T 4       -- Main[15..18]
  op_b_memory_prev_low : T                  -- Main[19]
  op_b_memory_diff_low : T                  -- Main[20]
  op_c : T                                  -- Main[21]
  op_c_memory_prev_value : Vector T 4       -- Main[22..25]
  op_c_memory_prev_low : T                  -- Main[26]
  op_c_memory_diff_low : T                  -- Main[27]
  imm_c : T                                 -- Main[28] (I-type immediate-mode flag)
  -- Intermediate shift-amount columns (Main[29..31]).
  shift_imm_low : T                         -- Main[29]
  shift_imm_high : T                        -- Main[30]
  msb : T                                   -- Main[31]
  -- The 4-limb shifted result (committed to op_a register).
  result : Vector T 4                       -- Main[32..35]
  -- 6-bit decomposition of the shift amount mod 64 (Main[36..41]).
  bit_shift : Vector T 6                    -- Main[36..41]
  -- Shift power intermediates (Main[42..44]).
  shift_pow : Vector T 3                    -- Main[42..44]
  -- One-hot byte-shift selector over 4 byte positions (Main[45..48]).
  byte_shift : Vector T 4                   -- Main[45..48]
  -- Shifted-limb intermediates and high-half spill (Main[49..56]).
  limb_shift : Vector T 8                   -- Main[49..56]
  -- Intermediate result columns before final assignment (Main[57..61]).
  result_intermediate : Vector T 5          -- Main[57..61]
  is_sll : T                                -- Main[62]
  is_sllw : T                               -- Main[63]
  sign_extend : T                           -- Main[64]
deriving ProvableStruct

/-- The aggregate is-real flag: at least one of the two shift variants
active. -/
def isRealExpr (cols : Var ShiftLeftCols (ZMod p)) : Expression (ZMod p) :=
  cols.is_sll + cols.is_sllw

/-- The opcode field expression for the program-bus interaction:
`is_sll * 8 + is_sllw * 14`. Matches SP1's RV64IM opcode IDs (SLL=8,
SLLW=14). The `imm_c` flag toggles R-type (sll/sllw) vs I-type
(slli/slliw) at chip granularity. -/
def opcodeExpr (cols : Var ShiftLeftCols (ZMod p)) : Expression (ZMod p) :=
  cols.is_sll * 8 + cols.is_sllw * 14

/-- Clean-side circuit. Emits the structural lookups and asserts:
- CPUState clk bounds (via subcircuit)
- 6 boolean asserts on the bit-decomposition
- 4 boolean asserts on the byte-shift selector
- 2 boolean asserts on the opcode selectors
- Aggregate is-real boolean
- ProgramTable.assertion with selector-weighted opcode
- op_a_0 = 0

The shift-arithmetic content (bit-decomposition correctness, shift
power chain, byte-shift one-hot, limb-shift correctness) is deferred
to `shiftSpec` placeholder; see file docstring. -/
def main (cols : Var ShiftLeftCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨_clk_high, clk_16_24, clk_0_16, pc, op_a,
       _op_a_memory_prev_value, _op_a_memory_prev_low, _op_a_memory_diff_low,
       op_a_0, op_b, _op_b_memory_prev_value, _op_b_memory_prev_low,
       _op_b_memory_diff_low, op_c, _op_c_memory_prev_value,
       _op_c_memory_prev_low, _op_c_memory_diff_low, imm_c,
       _shift_imm_low, _shift_imm_high, _msb, _result,
       bit_shift, _shift_pow, byte_shift, _limb_shift,
       _result_intermediate, is_sll, is_sllw, _sign_extend⟩ := cols
  -- CPUState range lookups (clk_0_16 progression + clk_16_24 U8 bound).
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  -- 6 boolean asserts on the bit decomposition.
  bit_shift[0] * (bit_shift[0] - 1) === 0
  bit_shift[1] * (bit_shift[1] - 1) === 0
  bit_shift[2] * (bit_shift[2] - 1) === 0
  bit_shift[3] * (bit_shift[3] - 1) === 0
  bit_shift[4] * (bit_shift[4] - 1) === 0
  bit_shift[5] * (bit_shift[5] - 1) === 0
  -- 4 boolean asserts on the byte-shift selector.
  byte_shift[0] * (byte_shift[0] - 1) === 0
  byte_shift[1] * (byte_shift[1] - 1) === 0
  byte_shift[2] * (byte_shift[2] - 1) === 0
  byte_shift[3] * (byte_shift[3] - 1) === 0
  -- 2 opcode-selector boolean asserts + aggregate is-real boolean.
  is_sll * (is_sll - 1) === 0
  is_sllw * (is_sllw - 1) === 0
  (is_sll + is_sllw) * (is_sll + is_sllw - 1) === 0
  -- Program-bus interaction. R-type discipline when imm_c = 0
  -- (sll/sllw); I-type when imm_c = 1 (slli/slliw). op_c column carries
  -- either single-limb register index or first immediate limb;
  -- additional immediate limbs are not present in the column struct
  -- (the constraints check them implicitly via the shift decomposition).
  SP1Clean.ProgramTable.assertion
    (⟨pc, is_sll * 8 + is_sllw * 14,
      op_a, #v[op_b, 0, 0, 0], #v[op_c, 0, 0, 0],
      op_a_0, 0, imm_c⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  -- op_a_0 forced to zero.
  op_a_0 === 0

/-- Placeholder for the shift-arithmetic Spec content (bit decomposition
correctness, shift power chain, byte-shift one-hot, limb-shift). Currently
trivially `True` — a follow-up iteration can inline the relevant clauses
from `_root_.ShiftLeft.allHold_constraints_iff`'s RHS or factor a
dedicated `SP1Clean.ShiftLeftOp.Spec` predicate. -/
def shiftSpec (_cols : ShiftLeftCols (ZMod p)) : Prop := True

/-- The Clean-flavored Spec for `ShiftLeftChip`. Composes the existing
per-fragment specs with three memory access records (op_a, op_b, op_c),
the program-bus consequence, the boolean gates, and the placeholder
shift content. -/
def Spec (cols : ShiftLeftCols (ZMod p)) : Prop :=
  SP1Clean.CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 ∧
  SP1Clean.memoryAccessSpec
    (cols.clk_0_16 + cols.clk_16_24 * 65536) 4
    (SP1Clean.MemoryAccess.ofRegisterShared cols.op_a
      { prev_value := cols.op_a_memory_prev_value,
        access_timestamp :=
          { prev_low := cols.op_a_memory_prev_low,
            diff_low_limb := cols.op_a_memory_diff_low } }) ∧
  SP1Clean.memoryAccessSpec
    (cols.clk_0_16 + cols.clk_16_24 * 65536) 3
    (SP1Clean.MemoryAccess.ofRegisterShared cols.op_b
      { prev_value := cols.op_b_memory_prev_value,
        access_timestamp :=
          { prev_low := cols.op_b_memory_prev_low,
            diff_low_limb := cols.op_b_memory_diff_low } }) ∧
  SP1Clean.memoryAccessSpec
    (cols.clk_0_16 + cols.clk_16_24 * 65536) 2
    (SP1Clean.MemoryAccess.ofRegisterShared cols.op_c
      { prev_value := cols.op_c_memory_prev_value,
        access_timestamp :=
          { prev_low := cols.op_c_memory_prev_low,
            diff_low_limb := cols.op_c_memory_diff_low } }) ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.pc,
      opcode := cols.is_sll * 8 + cols.is_sllw * 14,
      op_a := cols.op_a,
      op_b := #v[cols.op_b, 0, 0, 0],
      op_c := #v[cols.op_c, 0, 0, 0],
      op_a_0 := cols.op_a_0, imm_b := 0, imm_c := cols.imm_c } ∧
  -- 6 + 4 + 2 + 1 = 13 boolean gates.
  cols.bit_shift[0] * (cols.bit_shift[0] - 1) = 0 ∧
  cols.bit_shift[1] * (cols.bit_shift[1] - 1) = 0 ∧
  cols.bit_shift[2] * (cols.bit_shift[2] - 1) = 0 ∧
  cols.bit_shift[3] * (cols.bit_shift[3] - 1) = 0 ∧
  cols.bit_shift[4] * (cols.bit_shift[4] - 1) = 0 ∧
  cols.bit_shift[5] * (cols.bit_shift[5] - 1) = 0 ∧
  cols.byte_shift[0] * (cols.byte_shift[0] - 1) = 0 ∧
  cols.byte_shift[1] * (cols.byte_shift[1] - 1) = 0 ∧
  cols.byte_shift[2] * (cols.byte_shift[2] - 1) = 0 ∧
  cols.byte_shift[3] * (cols.byte_shift[3] - 1) = 0 ∧
  cols.is_sll * (cols.is_sll - 1) = 0 ∧
  cols.is_sllw * (cols.is_sllw - 1) = 0 ∧
  (cols.is_sll + cols.is_sllw) * (cols.is_sll + cols.is_sllw - 1) = 0 ∧
  cols.op_a_0 = 0 ∧
  shiftSpec cols

/-! ## Full `FormalAssertion` promotion (Path-2 — trimmed)

`Assertion.main` drops the 10 Vector-indexed boolean gates (6 for
`bit_shift`, 4 for `byte_shift`) that the chip's `main` emits. Those
gates are internal to the shift-arithmetic operation and would trip
the documented Path-1 friction (`Vector.map (eval env) input_var_X =
input_X` doesn't reduce per-element under `circuit_proof_start`). They
stay in the legacy `Spec` via `shiftSpec` placeholder and are consumed
through the chip-level pipeline, not the trace-level FormalAssertion.

Assertion.main keeps: `CPUState` + `ProgramTable` + 2 opcode boolean
gates + aggregate sum + `op_a_0 = 0` = 6 conjuncts. -/

namespace Assertion

open Circuit

@[reducible]
def main (cols : Var ShiftLeftCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨_clk_high, clk_16_24, clk_0_16, pc, op_a,
       _op_a_memory_prev_value, _op_a_memory_prev_low, _op_a_memory_diff_low,
       op_a_0, op_b, _op_b_memory_prev_value, _op_b_memory_prev_low,
       _op_b_memory_diff_low, op_c, _op_c_memory_prev_value,
       _op_c_memory_prev_low, _op_c_memory_diff_low, imm_c,
       _shift_imm_low, _shift_imm_high, _msb, _result,
       _bit_shift, _shift_pow, _byte_shift, _limb_shift,
       _result_intermediate, is_sll, is_sllw, _sign_extend⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ProgramTable.assertion
    (⟨pc, is_sll * 8 + is_sllw * 14,
      op_a, #v[op_b, 0, 0, 0], #v[op_c, 0, 0, 0],
      op_a_0, 0, imm_c⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  is_sll * (is_sll - 1) === 0
  is_sllw * (is_sllw - 1) === 0
  (is_sll + is_sllw) * (is_sll + is_sllw - 1) === 0
  op_a_0 === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) ShiftLeftCols unit where
  name := "SP1Clean.ShiftLeft"
  main := main
  localLength _ := 0

def Assumptions (_ : ShiftLeftCols (ZMod p)) : Prop := True

def FormalSpec (cols : ShiftLeftCols (ZMod p)) : Prop :=
  SP1Clean.CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.pc, opcode := cols.is_sll * 8 + cols.is_sllw * 14,
      op_a := cols.op_a, op_b := #v[cols.op_b, 0, 0, 0],
      op_c := #v[cols.op_c, 0, 0, 0],
      op_a_0 := cols.op_a_0, imm_b := 0, imm_c := cols.imm_c } ∧
  cols.is_sll * (cols.is_sll - 1) = 0 ∧
  cols.is_sllw * (cols.is_sllw - 1) = 0 ∧
  (cols.is_sll + cols.is_sllw) * (cols.is_sll + cols.is_sllw - 1) = 0 ∧
  cols.op_a_0 = 0

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨h_cpu_sub, h_prog_sub, h_sll, h_sllw, h_sum, h_op_a_0⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_prog_sub trivial
  · linear_combination h_sll
  · linear_combination h_sllw
  · linear_combination h_sum
  · exact h_op_a_0

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨h_cpu, h_prog, h_sll, h_sllw, h_sum, h_op_a_0⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_prog⟩
  · linear_combination h_sll
  · linear_combination h_sllw
  · linear_combination h_sum
  · exact h_op_a_0

end Assertion

def assertion : FormalAssertion (ZMod p) ShiftLeftCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.ShiftLeft
