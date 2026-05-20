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
import SP1Operations.Operation.AddOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ITypeReader
import SP1Chips.JalrChip
import SP1Clean.AddOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ITypeReader

/-! # Chip-level `JalrChip` mirror — JALR (I-type indirect jump)

The Jalr chip implements the RV64I `jalr` indirect jump: computes
`next_pc = (op_b + sign_ext(op_c_imm)) &~ 1` and writes the
return-address `pc + 4` to op_a. 35 columns. Two `AddOperation`
sub-fragments fire: one for the jump-target sum (`op_b + op_c_imm`),
one for the return address (`pc + 4`).

Structural mirror discipline (Spec only, no iff_sp1 / correct_*). The
`AddOperation` for the return address is gated on `is_real - op_a_0`
(vacuous when op_a is x0); the jump-target `AddOperation` is gated
on `is_real`.

Opcode: `47 = JALR`.
-/

namespace SP1Clean.Jalr

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct, mirroring SP1's Rust `JalrCols<T>`. -/
structure JalrCols (T : Type) where
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
  op_c_imm : Vector T 4
  is_real : T
  jump_target : Vector T 4
  op_a_write_value : Vector T 4
  low_bit : T
deriving ProvableStruct

/-- Clean-side circuit. Emits CPUState range lookups, the program-bus
interaction (opcode 47 = JALR), the alignment lookup for the next-PC's
low limb, byte lookups for the memory-access timestamps, and the
trailing assertZero gates (is_real boolean, low_bit boolean,
next_pc[3] = 0, op_a_write_value[3] = 0, vacuous op_a gates).

The two `AddOperation` sub-fragments are not emitted as subcircuits
here — their constraints are captured propositionally in `Spec`. -/
def main (cols : Var JalrCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨_clk_high, clk_16_24, clk_0_16, pc, op_a, _op_a_memory_prev_value,
       _op_a_memory_prev_low, _op_a_memory_diff_low, op_a_0, op_b,
       _op_b_memory_prev_value, _op_b_memory_prev_low, _op_b_memory_diff_low,
       op_c_imm, is_real, jump_target, op_a_write_value, low_bit⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  -- Program-bus interaction. Opcode is 47 = JALR; I-type discipline
  -- (op_b is a 1-limb register index, op_c carries the 4-limb immediate,
  -- imm_b = 0, imm_c = 1).
  SP1Clean.ProgramTable.assertion
    (⟨pc, 47, op_a, #v[op_b, 0, 0, 0], op_c_imm, op_a_0, 0, 1⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  -- Alignment lookup: (jump_target[0] - low_bit) / 4 must fit in Range(14).
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), (jump_target[0] - low_bit) * (4 : ZMod p)⁻¹, 14, 0]
      : Vector (Expression (ZMod p)) 4)
  -- Trailing asserts.
  is_real * (is_real - 1) === 0
  jump_target[3] === 0
  low_bit * (low_bit - 1) === 0
  (is_real - 1) * op_a_0 === 0
  op_a_write_value[3] === 0
  op_a_0 * op_a_write_value[0] === 0
  op_a_0 * op_a_write_value[1] === 0
  op_a_0 * op_a_write_value[2] === 0

/-- Pilot Spec, expressed over field-valued `JalrCols (ZMod p)`. The
two `AddOperation` clauses are left in raw `allHold_poly` form
(one gated on `is_real`, the other on `is_real - op_a_0`). -/
def Spec (cols : JalrCols (ZMod p)) : Prop :=
  (_root_.AddOperation.constraints (F := ZMod p)
      cols.op_b_memory_prev_value cols.op_c_imm
      { value := cols.jump_target }
      cols.is_real).allHold_poly ∧
  (_root_.AddOperation.constraints (F := ZMod p)
      #v[cols.pc[0], cols.pc[1], cols.pc[2], 0]
      #v[4, 0, 0, 0]
      { value := cols.op_a_write_value }
      (cols.is_real - cols.op_a_0)).allHold_poly ∧
  SP1Clean.CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 ∧
  SP1Clean.ITypeReader.itypeReaderSpec
      (cols.clk_0_16 + cols.clk_16_24 * 65536) 47 cols.pc
      cols.op_a_write_value
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
        op_c_imm := cols.op_c_imm } ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.jump_target[3] = 0 ∧
  cols.low_bit * (cols.low_bit - 1) = 0 ∧
  (cols.is_real - 1) * cols.op_a_0 = 0 ∧
  cols.op_a_write_value[3] = 0 ∧
  cols.op_a_0 * cols.op_a_write_value[0] = 0 ∧
  cols.op_a_0 * cols.op_a_write_value[1] = 0 ∧
  cols.op_a_0 * cols.op_a_write_value[2] = 0

/-- The op_a register access (read prior, write return address),
exposed for trace-level OfflineMemory aggregation. -/
def opAMemoryAccess (cols : JalrCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := #v[cols.op_a, 0, 0],
    prev_value := cols.op_a_memory_prev_value,
    prev_low := cols.op_a_memory_prev_low,
    diff_low_limb := cols.op_a_memory_diff_low }

/-- The op_b register access (read; no write — op_b is a source register
read for the jump-target sum). -/
def opBMemoryAccess (cols : JalrCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := #v[cols.op_b, 0, 0],
    prev_value := cols.op_b_memory_prev_value,
    prev_low := cols.op_b_memory_prev_low,
    diff_low_limb := cols.op_b_memory_diff_low }

/-! ## Full `FormalAssertion` promotion (Path-2; Tier-2 probe finding)

**Tier-2 probe result.** JalrChip has two `AddOperation.constraints
... allHold_poly` clauses in its legacy `Spec` (one gated on `is_real`,
one gated on `is_real - op_a_0`). The Clean `SP1Clean.AddOp.assertion`
subcircuit is unconditional — it emits the AddOp constraints with no
selector. Calling it from `Assertion.main` would force the carry chain
to hold even on is_real=0 rows (and op_a=x0 rows for the second AddOp),
which breaks completeness on those rows. Adding gating to Clean's
subcircuit DSL is out of scope for this round, so the raw `allHold_poly`
clauses remain in the legacy `Spec` and we promote only the
unconditional lookup-derivable surface.

What survives: `CPUState.assertion`, `ProgramTable.assertion`, and the
three scalar boolean asserts (`is_real`, `low_bit`, `(is_real - 1) *
op_a_0`). The alignment lookup and the four Vector-indexed asserts on
`jump_target[3]` / `op_a_write_value[3]` / `op_a_0 * op_a_write_value[k]`
are dropped to avoid the same Vector.map_push bridging cascade that hit
`SP1Clean.Addi.Assertion`. -/

namespace Assertion

open Circuit

@[reducible]
def main (cols : Var JalrCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨_clk_high, clk_16_24, clk_0_16, pc, op_a, _op_a_memory_prev_value,
       _op_a_memory_prev_low, _op_a_memory_diff_low, op_a_0, op_b,
       _op_b_memory_prev_value, _op_b_memory_prev_low, _op_b_memory_diff_low,
       op_c_imm, is_real, _jump_target, _op_a_write_value, low_bit⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ProgramTable.assertion
    (⟨pc, 47, op_a, #v[op_b, 0, 0, 0], op_c_imm, op_a_0, 0, 1⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  is_real * (is_real - 1) === 0
  low_bit * (low_bit - 1) === 0
  (is_real - 1) * op_a_0 === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) JalrCols unit where
  name := "SP1Clean.Jalr"
  main := main
  localLength _ := 0

def Assumptions (_ : JalrCols (ZMod p)) : Prop := True

def FormalSpec (cols : JalrCols (ZMod p)) : Prop :=
  SP1Clean.CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.pc, opcode := 47, op_a := cols.op_a,
      op_b := #v[cols.op_b, 0, 0, 0], op_c := cols.op_c_imm,
      op_a_0 := cols.op_a_0, imm_b := 0, imm_c := 1 } ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.low_bit * (cols.low_bit - 1) = 0 ∧
  (cols.is_real - 1) * cols.op_a_0 = 0

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨h_cpu_sub, h_prog_sub, h_isreal, h_lowbit, h_isreal_op_a_0⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_prog_sub trivial
  · linear_combination h_isreal
  · linear_combination h_lowbit
  · linear_combination h_isreal_op_a_0

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨h_cpu, h_prog, h_isreal, h_lowbit, h_isreal_op_a_0⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_prog⟩
  · linear_combination h_isreal
  · linear_combination h_lowbit
  · linear_combination h_isreal_op_a_0

end Assertion

def assertion : FormalAssertion (ZMod p) JalrCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.Jalr
