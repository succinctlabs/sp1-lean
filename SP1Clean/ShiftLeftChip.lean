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
import SP1Operations.Operation.U16MSBOperation.U16MSBOperation
import SP1Operations.Operation.AddrAddOperation.AddrAddOperation
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.ALUTypeReader.ALUTypeReader
import SP1Clean.AddrAddOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.OperandAccess
import SP1Chips.ShiftLeft.ShiftLeftChip

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
(`c_bits`, `shift_u16`, `shifted_limbs`, `result`). -/
structure ShiftLeftCols (T : Type) where
  state : CPUState T
  op_a : T                                  -- Main[6]
  op_a_memory : MemoryAccessInSharedCols T
  op_a_0 : T                                -- Main[13]
  op_b : T                                  -- Main[14]
  op_b_memory : MemoryAccessInSharedCols T
  op_c : T                                  -- Main[21]
  op_c_memory : MemoryAccessInSharedCols T
  imm_c : T                                 -- Main[28] (I-type immediate-mode flag)
  -- Intermediate shift-amount columns (Main[29..31]).
  shift_imm_low : T                         -- Main[29]
  shift_imm_high : T                        -- Main[30]
  msb : T                                   -- Main[31]
  -- The 4-limb shifted result (committed to op_a register).
  result : Vector T 4                       -- Main[32..35]
  -- 6-bit decomposition of the shift amount mod 64 (Main[36..41]).
  c_bits : Vector T 6                       -- Main[36..41]
  -- Shift-power intermediates (Main[42..44]). Upstream Rust names these
  -- as three named scalars (`v_01, v_012, v_0123`) rather than a 3-vector.
  -- Phase 2.3 decomposition (open-question #4): split for name alignment.
  v_01 : T                                  -- Main[42] (was shift_pow[0])
  v_012 : T                                 -- Main[43] (was shift_pow[1])
  v_0123 : T                                -- Main[44] (was shift_pow[2])
  -- One-hot byte-shift selector over 4 byte positions (Main[45..48]).
  shift_u16 : Vector T 4                    -- Main[45..48]
  -- Shifted-limb intermediates (Main[49..56]). Upstream Rust names the
  -- two halves as `lower_limb: Word<T>` and `higher_limb: Word<T>`.
  -- Phase 2.3 decomposition (open-question #4): split the 8-vector.
  lower_limb : Vector T 4                   -- Main[49..52] (was limb_shift[0..3])
  higher_limb : Vector T 4                  -- Main[53..56] (was limb_shift[4..7])
  -- Intermediate result columns (Main[57..61]). Upstream Rust splits this
  -- into `limb_result: Word<T>` (4 cells) and `sllw_msb: U16MSBOperation<T>`
  -- (1 cell, the MSB witness for SLLW sign-extension fed to U16MSBOperation
  -- in the bridge — see CS0 in SP1Chips/ShiftLeft/Constraints.lean).
  -- Phase 2.3 decomposition (open-question #4): split the 5-vector.
  limb_result : Vector T 4                  -- Main[57..60] (was result_intermediate[0..3])
  sllw_msb : U16MSBOperation T              -- Main[61] (was result_intermediate[4])
  is_sll : T                                -- Main[62]
  is_sllw : T                               -- Main[63]
  -- Renamed from `sign_extend` to upstream's `is_sllw_imm` (Phase 2.3).
  -- Bridge: Main[64] = Main[63] * Main[31] = is_sllw * imm_c = is_slliw.
  is_sllw_imm : T                           -- Main[64] (was sign_extend)
  next_pc_carry_value : Vector T 3
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
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩, op_a,
       _op_a_memory,
       op_a_0, op_b, _op_b_memory, op_c, _op_c_memory, imm_c,
       _shift_imm_low, _shift_imm_high, _msb, _result,
       c_bits, _v_01, _v_012, _v_0123, shift_u16, _lower_limb, _higher_limb,
       _limb_result, _sllw_msb, is_sll, is_sllw, _is_sllw_imm,
       _next_pc_carry_value⟩ := cols
  -- CPUState range lookups (clk_0_16 progression + clk_16_24 U8 bound).
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  -- 6 boolean asserts on the bit decomposition.
  c_bits[0] * (c_bits[0] - 1) === 0
  c_bits[1] * (c_bits[1] - 1) === 0
  c_bits[2] * (c_bits[2] - 1) === 0
  c_bits[3] * (c_bits[3] - 1) === 0
  c_bits[4] * (c_bits[4] - 1) === 0
  c_bits[5] * (c_bits[5] - 1) === 0
  -- 4 boolean asserts on the byte-shift selector.
  shift_u16[0] * (shift_u16[0] - 1) === 0
  shift_u16[1] * (shift_u16[1] - 1) === 0
  shift_u16[2] * (shift_u16[2] - 1) === 0
  shift_u16[3] * (shift_u16[3] - 1) === 0
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
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.memoryAccessSpec
    (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 4
    (SP1Clean.MemoryAccess.ofRegisterShared cols.op_a
      { prev_value := cols.op_a_memory.prev_value,
        access_timestamp :=
          { prev_low := cols.op_a_memory.access_timestamp.prev_low,
            diff_low_limb := cols.op_a_memory.access_timestamp.diff_low_limb } }) ∧
  SP1Clean.memoryAccessSpec
    (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 3
    (SP1Clean.MemoryAccess.ofRegisterShared cols.op_b
      { prev_value := cols.op_b_memory.prev_value,
        access_timestamp :=
          { prev_low := cols.op_b_memory.access_timestamp.prev_low,
            diff_low_limb := cols.op_b_memory.access_timestamp.diff_low_limb } }) ∧
  SP1Clean.memoryAccessSpec
    (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 2
    (SP1Clean.MemoryAccess.ofRegisterShared cols.op_c
      { prev_value := cols.op_c_memory.prev_value,
        access_timestamp :=
          { prev_low := cols.op_c_memory.access_timestamp.prev_low,
            diff_low_limb := cols.op_c_memory.access_timestamp.diff_low_limb } }) ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc,
      opcode := cols.is_sll * 8 + cols.is_sllw * 14,
      op_a := cols.op_a,
      op_b := #v[cols.op_b, 0, 0, 0],
      op_c := #v[cols.op_c, 0, 0, 0],
      op_a_0 := cols.op_a_0, imm_b := 0, imm_c := cols.imm_c } ∧
  -- 6 + 4 + 2 + 1 = 13 boolean gates.
  cols.c_bits[0] * (cols.c_bits[0] - 1) = 0 ∧
  cols.c_bits[1] * (cols.c_bits[1] - 1) = 0 ∧
  cols.c_bits[2] * (cols.c_bits[2] - 1) = 0 ∧
  cols.c_bits[3] * (cols.c_bits[3] - 1) = 0 ∧
  cols.c_bits[4] * (cols.c_bits[4] - 1) = 0 ∧
  cols.c_bits[5] * (cols.c_bits[5] - 1) = 0 ∧
  cols.shift_u16[0] * (cols.shift_u16[0] - 1) = 0 ∧
  cols.shift_u16[1] * (cols.shift_u16[1] - 1) = 0 ∧
  cols.shift_u16[2] * (cols.shift_u16[2] - 1) = 0 ∧
  cols.shift_u16[3] * (cols.shift_u16[3] - 1) = 0 ∧
  cols.is_sll * (cols.is_sll - 1) = 0 ∧
  cols.is_sllw * (cols.is_sllw - 1) = 0 ∧
  (cols.is_sll + cols.is_sllw) * (cols.is_sll + cols.is_sllw - 1) = 0 ∧
  cols.op_a_0 = 0 ∧
  shiftSpec cols

/-- Project a raw SP1 row into the structured `ShiftLeftCols` view.
65 columns. Post-Phase-2.3 decomposition: `v_01/v_012/v_0123` are scalars
(Main[42..44]), `lower_limb`/`higher_limb` split the former 8-vector
(Main[49..56]), `limb_result`+`sllw_msb` split the former 5-vector
(Main[57..61]), and `is_sllw_imm` replaces the old `sign_extend`. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 65) : ShiftLeftCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
      Main[6],
   ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩, Main[13],
   Main[14],
   ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
   Main[21],
   ⟨#v[Main[22], Main[23], Main[24], Main[25]], ⟨Main[26], Main[27]⟩⟩,
   Main[28],
   Main[29], Main[30], Main[31],
   #v[Main[32], Main[33], Main[34], Main[35]],
   #v[Main[36], Main[37], Main[38], Main[39], Main[40], Main[41]],
   Main[42], Main[43], Main[44],
   #v[Main[45], Main[46], Main[47], Main[48]],
   #v[Main[49], Main[50], Main[51], Main[52]],
   #v[Main[53], Main[54], Main[55], Main[56]],
   #v[Main[57], Main[58], Main[59], Main[60]],
   { msb := Main[61] },
   Main[62], Main[63], Main[64],
   #v[0, 0, 0]⟩

/-- The chip-level half-iff bridge (ShiftLeft). **Proof body sorry'd**
— see `feedback_path2_correct_bridge_costs.md`. -/
theorem spec_implies_allHold (Main : Vector (ZMod p) 65)
    (h_is_real : Main[62] + Main[63] = 1)
    (h_spec : Spec (fromMain Main)) :
    (_root_.ShiftLeft.constraints Main).allHold := by
  sorry

/-- Clean-side `correct_sll`: R-type left shift. -/
theorem correct_sll
    (Main : Vector (ZMod p) 65) (s : SailState)
    (h_is_sll : Main[62] = 1) (h_imm_c : Main[31] = 0)
    (h_sllw_zero : Main[63] = 0)
    (h_spec : Spec (fromMain Main))
    (state_cstrs : (_root_.ShiftLeft.constraints Main).initialState s) :
    let op_c := _root_.ShiftLeft.sp1_op_c Main
    let op_b := _root_.ShiftLeft.sp1_op_b Main
    let op_a := _root_.ShiftLeft.sp1_op_a Main
    (_root_.Sll.Poly.spec_sll (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.ShiftLeft.sp1_shift_left Main).run s :=
  _root_.Sll.Poly.correct_sll Main s
    (spec_implies_allHold Main (by rw [h_is_sll, h_sllw_zero]; ring) h_spec)
    ⟨h_is_sll, h_imm_c⟩ state_cstrs

/-! ## Full `FormalAssertion` promotion (Path-2 — trimmed)

`Assertion.main` drops the 10 Vector-indexed boolean gates (6 for
`c_bits`, 4 for `shift_u16`) that the chip's `main` emits. Those
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
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩, op_a,
       op_a_memory,
       op_a_0, op_b, op_b_memory, op_c, op_c_memory, imm_c,
       _shift_imm_low, _shift_imm_high, _msb, _result,
       _c_bits, _v_01, _v_012, _v_0123, _shift_u16, _lower_limb, _higher_limb,
       _limb_result, _sllw_msb, is_sll, is_sllw, _is_sllw_imm,
       next_pc_carry_value⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ProgramTable.assertion
    (⟨pc, is_sll * 8 + is_sllw * 14,
      op_a, #v[op_b, 0, 0, 0], #v[op_c, 0, 0, 0],
      op_a_0, 0, imm_c⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  SP1Clean.AddrAddOp.assertion
    (⟨#v[pc[0], pc[1], pc[2], (0 : Expression (ZMod p))],
       #v[(4 : Expression (ZMod p)), 0, 0, 0],
       next_pc_carry_value⟩ :
      Var SP1Clean.AddrAddOp.Inputs (ZMod p))
  is_sll * (is_sll - 1) === 0
  is_sllw * (is_sllw - 1) === 0
  (is_sll + is_sllw) * (is_sll + is_sllw - 1) === 0
  op_a_0 === 0
  -- Iter-8 sub-task E: per-operand memory-bus byte content.
  -- R-type: op_a/+4, op_b/+3, op_c/+2.
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

set_option maxHeartbeats 800000 in
-- Higher heartbeats: 31 input fields + 4 subcircuit calls + 3 OperandAccess
-- calls pushes localLength_eq synthesis past the default 200k cap.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) ShiftLeftCols unit where
  name := "SP1Clean.ShiftLeft"
  main := main
  localLength _ := 0

def Assumptions (_ : ShiftLeftCols (ZMod p)) : Prop := True

def FormalSpec (cols : ShiftLeftCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := cols.is_sll * 8 + cols.is_sllw * 14,
      op_a := cols.op_a, op_b := #v[cols.op_b, 0, 0, 0],
      op_c := #v[cols.op_c, 0, 0, 0],
      op_a_0 := cols.op_a_0, imm_b := 0, imm_c := cols.imm_c } ∧
  SP1Clean.AddrAddOp.assertion.Spec
    ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
     #v[(4 : ZMod p), 0, 0, 0],
     cols.next_pc_carry_value⟩ ∧
  cols.is_sll * (cols.is_sll - 1) = 0 ∧
  cols.is_sllw * (cols.is_sllw - 1) = 0 ∧
  (cols.is_sll + cols.is_sllw) * (cols.is_sll + cols.is_sllw - 1) = 0 ∧
  cols.op_a_0 = 0 ∧
  -- Iter-8 sub-task E: per-operand memory-bus byte-content consequences.
  -- R-type: op_a/+4, op_b/+3, op_c/+2.
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 4, cols.op_a_memory.access_timestamp.prev_low,
     cols.op_a_memory.access_timestamp.diff_low_limb,
     cols.op_a_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 3, cols.op_b_memory.access_timestamp.prev_low,
     cols.op_b_memory.access_timestamp.diff_low_limb,
     cols.op_b_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 2, cols.op_c_memory.access_timestamp.prev_low,
     cols.op_c_memory.access_timestamp.diff_low_limb,
     cols.op_c_memory.prev_value⟩

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30,
          e31⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu_sub, h_prog_sub, h_addr_sub, h_sll, h_sllw, h_sum,
          h_op_a_0, h_oa_a, h_oa_b, h_oa_c⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_prog_sub trivial
  · simp only [Vector.getElem_map]
    exact h_addr_sub trivial
  · linear_combination h_sll
  · linear_combination h_sllw
  · linear_combination h_sum
  · exact h_op_a_0
  · exact h_oa_a trivial
  · exact h_oa_b trivial
  · exact h_oa_c trivial

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30,
          e31⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu, h_prog, h_addr, h_sll, h_sllw, h_sum, h_op_a_0,
          h_oa_a, h_oa_b, h_oa_c⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_prog⟩
  · refine ⟨trivial, ?_⟩
    simp only [Vector.getElem_map] at h_addr
    exact h_addr
  · linear_combination h_sll
  · linear_combination h_sllw
  · linear_combination h_sum
  · exact h_op_a_0
  · exact ⟨trivial, h_oa_a⟩
  · exact ⟨trivial, h_oa_b⟩
  · exact ⟨trivial, h_oa_c⟩

end Assertion

def assertion : FormalAssertion (ZMod p) ShiftLeftCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.ShiftLeft
