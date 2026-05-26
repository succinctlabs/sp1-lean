import SP1Clean.Chips.ALU.BitwiseChip.Multiplicity.Cols
import SP1Operations.Operation.BitwiseU16Operation.BitwiseU16Operation
import SP1Clean.Reader.ALUTypeReader
import SP1Chips.Bitwise.Common

/-! # `BitwiseChip` cols-level lemmas (directory-form scaffold)

Two non-trivial lemmas. Note the chip has 6 variants but a single
constraint surface, so there's still exactly one
`allHold_iff_structural`. The variant-specific monadic Sail bridges live
in `SailBridge.lean` (6 theorems, one per variant). Bodies are `sorry`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.BitwiseChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
/-- `fromMain` is a left inverse of `toMain`, conditional on
`cols.adapter_cols.is_trusted = cols.is_xor + cols.is_or + cols.is_and`
(the chip's aggregate is_real sum). -/
lemma fromMain_toMain (cols : BitwiseCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted =
      cols.is_xor + cols.is_or + cols.is_and) :
    fromMain (toMain cols) = cols := by
  sorry

/-- The chip-level structural bridge: SP1's `allHold` over the flat row
`Bitwise.constraints Main` is exactly the conjunction of the
BitwiseU16Operation propositional clause, `cpuStateSpec`,
`aluTypeReaderSpec`, the 4 selector booleans, and `op_a_0 = 0`, under
`is_real = Main[48] + Main[49] + Main[50] = 1`. -/
lemma allHold_iff_structural
    (Main : Vector (ZMod p) 51)
    (h_is_real : Main[48] + Main[49] + Main[50] = 1) :
    (_root_.Bitwise.constraints Main).allHold ↔
      (let opcode_bw : ZMod p := Main[48] * 2 + Main[49] * 1 + Main[50] * 0
       let is_real : ZMod p := Main[48] + Main[49] + Main[50]
       let bw_cols : BitwiseU16Operation (ZMod p) :=
         ⟨⟨#v[Main[32], Main[33], Main[34], Main[35]]⟩,
          ⟨#v[Main[36], Main[37], Main[38], Main[39]]⟩,
          ⟨#v[Main[40], Main[41], Main[42], Main[43],
              Main[44], Main[45], Main[46], Main[47]]⟩⟩
       let ret_val : Word (ZMod p) :=
         (BitwiseU16Operation.constraints (F := ZMod p)
           #v[Main[15], Main[16], Main[17], Main[18]]
           #v[Main[25], Main[26], Main[27], Main[28]]
           bw_cols opcode_bw is_real).1
       List.Forall SP1Constraint.toProp
         (BitwiseU16Operation.constraints (F := ZMod p)
           #v[Main[15], Main[16], Main[17], Main[18]]
           #v[Main[25], Main[26], Main[27], Main[28]]
           bw_cols opcode_bw is_real).2 ∧
       SP1Clean.CPUState.cpuStateSpec Main[2] Main[1] ∧
       SP1Clean.ALUTypeReader.aluTypeReaderSpec
          (Main[2] + Main[1] * 65536)
          (Main[48] * 3 + Main[49] * 4 + Main[50] * 5)
          #v[Main[3], Main[4], Main[5]]
          ret_val
          { op_a := Main[6],
            op_a_memory :=
              { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
                access_timestamp :=
                  { prev_low := Main[11], diff_low_limb := Main[12] } },
            op_a_0 := Main[13], op_b := Main[14],
            op_b_memory :=
              { prev_value := #v[Main[15], Main[16], Main[17], Main[18]],
                access_timestamp :=
                  { prev_low := Main[19], diff_low_limb := Main[20] } },
            op_c := #v[Main[21], Main[22], Main[23], Main[24]],
            op_c_memory :=
              { prev_value := #v[Main[25], Main[26], Main[27], Main[28]],
                access_timestamp :=
                  { prev_low := Main[29], diff_low_limb := Main[30] } },
            imm_c := Main[31] } ∧
       (Main[48] = 0 ∨ Main[48] = 1) ∧
       (Main[49] = 0 ∨ Main[49] = 1) ∧
       (Main[50] = 0 ∨ Main[50] = 1) ∧
       (is_real = 0 ∨ is_real - 1 = 0) ∧
       Main[13] = 0) := by
  sorry

end SP1Clean.BitwiseChip
