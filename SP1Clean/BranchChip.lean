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
import SP1Operations.Compare.LtOperationSigned
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ITypeReaderImmutable
import SP1Chips.BranchChip
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ITypeReader

/-! # Chip-level `BranchChip` mirror — bundled 6-variant conditional branch

The Branch chip bundles six RV64I conditional-branch variants
(`beq`/`bne`/`blt`/`bge`/`bltu`/`bgeu`) into a single 45-column trace.
Variants are distinguished by selectors at `Main[28..33]`. Uses
`ITypeReaderImmutable` (op_a / op_b read, no write) plus an inline
`LtOperationSigned` sub-fragment to compute the comparison result.

Structural mirror discipline (Spec only). The `LtOperationSigned`
constraint clause is left in raw `allHold` form. The next_pc
chain is state-bus content (per-row `True`); cross-row PC consistency
is a separate trace-level concern.

Opcode encoding: `is_beq * 40 + is_bne * 41 + is_blt * 42 + is_bge * 43
+ is_bltu * 44 + is_bgeu * 45` (40-45 = BEQ/BNE/BLT/BGE/BLTU/BGEU).
-/

namespace SP1Clean.Branch

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct, mirroring SP1's Rust `BranchCols<T>`. -/
structure BranchCols (T : Type) where
  clk_high : T                              -- Main[0]
  clk_16_24 : T                             -- Main[1]
  clk_0_16 : T                              -- Main[2]
  pc : Vector T 3                           -- Main[3..5]
  op_a : T                                  -- Main[6]
  op_a_memory_prev_value : Vector T 4       -- Main[7..10] (source register a)
  op_a_memory_prev_low : T                  -- Main[11]
  op_a_memory_diff_low : T                  -- Main[12]
  op_a_0 : T                                -- Main[13]
  op_b : T                                  -- Main[14]
  op_b_memory_prev_value : Vector T 4       -- Main[15..18] (source register b)
  op_b_memory_prev_low : T                  -- Main[19]
  op_b_memory_diff_low : T                  -- Main[20]
  op_c_imm : Vector T 4                     -- Main[21..24]
  next_pc : Vector T 3                      -- Main[25..27]
  is_beq : T                                -- Main[28]
  is_bne : T                                -- Main[29]
  is_blt : T                                -- Main[30]
  is_bge : T                                -- Main[31]
  is_bltu : T                               -- Main[32]
  is_bgeu : T                               -- Main[33]
  lt_is_signed : T                          -- Main[34]
  compare_bit : T                           -- Main[35]
  u16_flags : Vector T 4                    -- Main[36..39]
  not_eq_inv : T                            -- Main[40]
  comparison_limbs : Vector T 2             -- Main[41..42]
  b_msb : T                                 -- Main[43]
  c_msb : T                                 -- Main[44]
deriving ProvableStruct

/-- Aggregate is-real flag: sum of 6 selectors. -/
def isRealExpr (cols : Var BranchCols (ZMod p)) : Expression (ZMod p) :=
  cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge +
    cols.is_bltu + cols.is_bgeu

/-- Selector-weighted opcode expression. -/
def opcodeExpr (cols : Var BranchCols (ZMod p)) : Expression (ZMod p) :=
  cols.is_beq * 40 + cols.is_bne * 41 + cols.is_blt * 42 +
    cols.is_bge * 43 + cols.is_bltu * 44 + cols.is_bgeu * 45

def main (cols : Var BranchCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨_clk_high, clk_16_24, clk_0_16, pc, op_a,
       _op_a_memory_prev_value, _op_a_memory_prev_low, _op_a_memory_diff_low,
       op_a_0, op_b, _op_b_memory_prev_value, _op_b_memory_prev_low,
       _op_b_memory_diff_low, op_c_imm, _next_pc,
       is_beq, is_bne, is_blt, is_bge, is_bltu, is_bgeu,
       _lt_is_signed, _compare_bit, _u16_flags, _not_eq_inv,
       _comparison_limbs, _b_msb, _c_msb⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  let opcode_e := is_beq * 40 + is_bne * 41 + is_blt * 42 +
                    is_bge * 43 + is_bltu * 44 + is_bgeu * 45
  SP1Clean.ProgramTable.assertion
    (⟨pc, opcode_e, op_a, #v[op_b, 0, 0, 0], op_c_imm, op_a_0, 0, 1⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  -- Six opcode-selector boolean gates plus the aggregate-is-real boolean.
  is_beq * (is_beq - 1) === 0
  is_bne * (is_bne - 1) === 0
  is_blt * (is_blt - 1) === 0
  is_bge * (is_bge - 1) === 0
  is_bltu * (is_bltu - 1) === 0
  is_bgeu * (is_bgeu - 1) === 0
  let sum := is_beq + is_bne + is_blt + is_bge + is_bltu + is_bgeu
  sum * (sum - 1) === 0

def Spec (cols : BranchCols (ZMod p)) : Prop :=
  let is_real : ZMod p :=
    cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge +
      cols.is_bltu + cols.is_bgeu
  let opcode_e : ZMod p :=
    cols.is_beq * 40 + cols.is_bne * 41 + cols.is_blt * 42 +
      cols.is_bge * 43 + cols.is_bltu * 44 + cols.is_bgeu * 45
  let lt_cols : _root_.LtOperationSigned (ZMod p) :=
    { result :=
        { u16_compare_operation := { bit := cols.compare_bit },
          u16_flags := cols.u16_flags,
          not_eq_inv := cols.not_eq_inv,
          comparison_limbs := cols.comparison_limbs },
      b_msb := { msb := cols.b_msb },
      c_msb := { msb := cols.c_msb } }
  (_root_.LtOperationSigned.constraints (F := ZMod p)
      cols.op_a_memory_prev_value cols.op_b_memory_prev_value
      lt_cols cols.lt_is_signed is_real).allHold ∧
  SP1Clean.CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.pc, opcode := opcode_e,
      op_a := cols.op_a,
      op_b := #v[cols.op_b, 0, 0, 0],
      op_c := cols.op_c_imm,
      op_a_0 := cols.op_a_0, imm_b := 0, imm_c := 1 } ∧
  cols.is_beq * (cols.is_beq - 1) = 0 ∧
  cols.is_bne * (cols.is_bne - 1) = 0 ∧
  cols.is_blt * (cols.is_blt - 1) = 0 ∧
  cols.is_bge * (cols.is_bge - 1) = 0 ∧
  cols.is_bltu * (cols.is_bltu - 1) = 0 ∧
  cols.is_bgeu * (cols.is_bgeu - 1) = 0 ∧
  is_real * (is_real - 1) = 0

/-- The op_a / op_b register accesses (both reads; no writes — Branch
doesn't update any register, only PC). -/
def opAMemoryAccess (cols : BranchCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := #v[cols.op_a, 0, 0],
    prev_value := cols.op_a_memory_prev_value,
    prev_low := cols.op_a_memory_prev_low,
    diff_low_limb := cols.op_a_memory_diff_low }

def opBMemoryAccess (cols : BranchCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := #v[cols.op_b, 0, 0],
    prev_value := cols.op_b_memory_prev_value,
    prev_low := cols.op_b_memory_prev_low,
    diff_low_limb := cols.op_b_memory_diff_low }

end SP1Clean.Branch
