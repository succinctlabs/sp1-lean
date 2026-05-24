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
import SP1Operations.Operation.AddrAddOperation.AddrAddOperation
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.RTypeReader.RTypeReader
import SP1Clean.AddrAddOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.OperandAccess
import SP1Clean.TrustMode
import SP1Chips.DivRem.DivRemChip

/-! # Chip-level `DivRemChip` mirror — bundled 4-variant integer division

The DivRem chip bundles four RV64IM division variants
(`div`/`divu`/`rem`/`remu`) into a single 246-column trace, with two
`MulOperation` sub-fragments (one for the quotient × divisor product,
one for the dividend reconstruction), plus `IsZeroWord`, `AddOperation`
(for remainder), and other sub-fragments.

Iff-only structural mirror discipline (heaviest chip in the ISA). The
division-arithmetic content (carry chains, sign handling, remainder
reconstruction) is captured as a placeholder `divRemSpec` (currently
`True`).
-/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.DivRem

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Sub-record bundling the 14 named fields of upstream `DivRemCols`'s
"post-MulOperation" intermediates (Main[166..240]). Nested into `DivRemCols`
to keep the top-level field count tractable for `deriving ProvableStruct`
(the auto-deriver bails on flat structs with >~25 fields). -/
structure DivRemAuxPost (T : Type) where
  c_neg_operation : AddOperation T          -- Main[166..169]
  rem_neg_operation : AddOperation T        -- Main[170..173]
  remainder_lt_operation : LtOperationUnsigned T  -- Main[174..181]
  carry : Vector T 8                        -- Main[182..189]
  is_c_0 : IsZeroWordOperation T            -- Main[190..200]
  -- 8 one-hot mode flags (Main[201..208]): is_div, is_divu, is_rem,
  -- is_remu, is_divw, is_remw, is_divuw, is_remuw in declaration order.
  mode_flags : Vector T 8                   -- Main[201..208]
  is_overflow : T                           -- Main[209]
  is_overflow_b : IsEqualWordOperation T    -- Main[210..220]
  is_overflow_c : IsEqualWordOperation T    -- Main[221..231]
  b_msb : U16MSBOperation T                 -- Main[232]
  rem_msb : U16MSBOperation T               -- Main[233]
  c_msb : U16MSBOperation T                 -- Main[234]
  quot_msb : U16MSBOperation T              -- Main[235]
  -- Five single-bit flags (Main[236..240]): b_neg, b_neg_not_overflow,
  -- b_not_neg_not_overflow, is_real_not_word, rem_neg in order.
  neg_flags : Vector T 5                    -- Main[236..240]
deriving ProvableStruct

/-- The chip's column struct. The 246 columns mirror upstream
`DivRemCols<T, M>` declaration order (alu/divrem/mod.rs:58-200). The 14
aux_post fields are bundled into a `DivRemAuxPost` sub-record so the
total field count stays inside what `deriving ProvableStruct` can
chain-coerce. -/
structure DivRemCols (T : Type) where
  state : CPUState T
  adapter : RTypeReader T
  op_a_write_value : Vector T 4             -- Main[28..31] (= upstream `a : Word<T>`)
  -- Phase 3f: aux_pre:44 fully decomposed into 10 named upstream sub-fields.
  b : Vector T 4                            -- Main[32..35]
  c : Vector T 4                            -- Main[36..39]
  quotient : Vector T 4                     -- Main[40..43]
  quotient_comp : Vector T 4                -- Main[44..47]
  remainder_comp : Vector T 4               -- Main[48..51]
  remainder : Vector T 4                    -- Main[52..55]
  abs_remainder : Vector T 4                -- Main[56..59]
  abs_c : Vector T 4                        -- Main[60..63]
  max_abs_c_or_1 : Vector T 4               -- Main[64..67]
  c_times_quotient : Vector T 8             -- Main[68..75]
  c_times_quotient_lower : MulOperation T   -- Main[76..120]
  c_times_quotient_upper : MulOperation T   -- Main[121..165]
  aux_post : DivRemAuxPost T                -- Main[166..240], decomposed in sub-record
  -- Main[241..245]: per-mode multiplicity flags (Rust DivRemCols layout).
  -- The 3-flag (is_signed, is_w, is_rem) labels these previously carried
  -- were a mode-encoding placeholder that got out of sync with upstream
  -- — Rust has the 8-flag one-hot at Main[201..208] (see mode_flags in
  -- DivRemAuxPost) and reserves these cells for sub-operation multiplicity.
  c_neg : T                                 -- Main[241] (sign-flip flag for c)
  abs_c_alu_event : T                       -- Main[242] (mult arg to c_neg AddOp)
  abs_rem_alu_event : T                     -- Main[243] (mult arg to rem_neg AddOp)
  is_real : T                               -- Main[244]
  remainder_check_multiplicity : T          -- Main[245] (mult arg to remainder_lt_op)
  next_pc_carry_value : Vector T 3
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

def main (cols : Var DivRemCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, _op_a_memory, op_a_0, op_b, _op_b_memory, op_c, _op_c_memory⟩,
       _op_a_write_value,
       _b, _c, _quotient, _quotient_comp, _remainder_comp, _remainder,
       _abs_remainder, _abs_c, _max_abs_c_or_1, _c_times_quotient,
       _c_times_quotient_lower, _c_times_quotient_upper,
       aux_post,
       c_neg, abs_c_alu_event, abs_rem_alu_event, is_real, _remainder_check_multiplicity,
       _next_pc_carry_value, _adapter_cols⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  -- Opcode encoded one-hot via the 8 mode flags at Main[201..208].
  -- Opcodes: DIV=15, DIVU=16, REM=17, REMU=18, DIVW=25, DIVUW=26,
  --          REMW=27, REMUW=28. mode_flags order matches upstream:
  --          [is_div, is_divu, is_rem, is_remu, is_divw, is_remw,
  --           is_divuw, is_remuw].
  let is_div   : Expression (ZMod p) := aux_post.mode_flags[0]
  let is_divu  : Expression (ZMod p) := aux_post.mode_flags[1]
  let is_rem_f : Expression (ZMod p) := aux_post.mode_flags[2]
  let is_remu  : Expression (ZMod p) := aux_post.mode_flags[3]
  let is_divw  : Expression (ZMod p) := aux_post.mode_flags[4]
  let is_remw  : Expression (ZMod p) := aux_post.mode_flags[5]
  let is_divuw : Expression (ZMod p) := aux_post.mode_flags[6]
  let is_remuw : Expression (ZMod p) := aux_post.mode_flags[7]
  SP1Clean.ProgramTable.assertion
    (⟨pc,
      is_div * 15 + is_divu * 16 + is_rem_f * 17 + is_remu * 18
        + is_divw * 25 + is_remw * 27 + is_divuw * 26 + is_remuw * 28,
      op_a, #v[op_b, 0, 0, 0], #v[op_c, 0, 0, 0], op_a_0, 0, 0⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  c_neg * (c_neg - 1) === 0
  abs_c_alu_event * (abs_c_alu_event - 1) === 0
  abs_rem_alu_event * (abs_rem_alu_event - 1) === 0
  is_real * (is_real - 1) === 0
  op_a_0 === 0

/-- Placeholder for the DivRem arithmetic Spec content. Currently
`True`; a future iteration can inline `MulOperation` × 2,
`IsZeroWordOperation`, `AddOperation` constraints and the
quotient/remainder/sign-handling clauses. -/
def divRemSpec (_cols : DivRemCols (ZMod p)) : Prop := True

def Spec (cols : DivRemCols (ZMod p)) : Prop :=
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.memoryAccessSpec
    (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 4
    (SP1Clean.MemoryAccess.ofRegisterShared cols.adapter.op_a
      { prev_value := cols.adapter.op_a_memory.prev_value,
        access_timestamp :=
          { prev_low := cols.adapter.op_a_memory.access_timestamp.prev_low,
            diff_low_limb := cols.adapter.op_a_memory.access_timestamp.diff_low_limb } }) ∧
  SP1Clean.memoryAccessSpec
    (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 3
    (SP1Clean.MemoryAccess.ofRegisterShared cols.adapter.op_b
      { prev_value := cols.adapter.op_b_memory.prev_value,
        access_timestamp :=
          { prev_low := cols.adapter.op_b_memory.access_timestamp.prev_low,
            diff_low_limb := cols.adapter.op_b_memory.access_timestamp.diff_low_limb } }) ∧
  SP1Clean.memoryAccessSpec
    (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 2
    (SP1Clean.MemoryAccess.ofRegisterShared cols.adapter.op_c
      { prev_value := cols.adapter.op_c_memory.prev_value,
        access_timestamp :=
          { prev_low := cols.adapter.op_c_memory.access_timestamp.prev_low,
            diff_low_limb := cols.adapter.op_c_memory.access_timestamp.diff_low_limb } }) ∧
  cols.c_neg * (cols.c_neg - 1) = 0 ∧
  cols.abs_c_alu_event * (cols.abs_c_alu_event - 1) = 0 ∧
  cols.abs_rem_alu_event * (cols.abs_rem_alu_event - 1) = 0 ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.adapter.op_a_0 = 0 ∧
  divRemSpec cols ∧
  cols.adapter_cols.is_trusted = 1

/-- Project a raw SP1 row into the structured `DivRemCols` view. 246 columns,
all fields named per the upstream `DivRemCols<T, M>` declaration order. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 246) : DivRemCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
      ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    Main[21],
    ⟨#v[Main[22], Main[23], Main[24], Main[25]], ⟨Main[26], Main[27]⟩⟩⟩,
   #v[Main[28], Main[29], Main[30], Main[31]],
   -- aux_pre[44]: 10 Word/Vector fields at Main[32..75].
   #v[Main[32], Main[33], Main[34], Main[35]],   -- b
   #v[Main[36], Main[37], Main[38], Main[39]],   -- c
   #v[Main[40], Main[41], Main[42], Main[43]],   -- quotient
   #v[Main[44], Main[45], Main[46], Main[47]],   -- quotient_comp
   #v[Main[48], Main[49], Main[50], Main[51]],   -- remainder_comp
   #v[Main[52], Main[53], Main[54], Main[55]],   -- remainder
   #v[Main[56], Main[57], Main[58], Main[59]],   -- abs_remainder
   #v[Main[60], Main[61], Main[62], Main[63]],   -- abs_c
   #v[Main[64], Main[65], Main[66], Main[67]],   -- max_abs_c_or_1
   #v[Main[68], Main[69], Main[70], Main[71],
      Main[72], Main[73], Main[74], Main[75]],   -- c_times_quotient
   -- c_times_quotient_lower (45 cells: Main[76..120])
   { carry := #v[Main[76], Main[77], Main[78], Main[79], Main[80], Main[81], Main[82],
                 Main[83], Main[84], Main[85], Main[86], Main[87], Main[88], Main[89],
                 Main[90], Main[91]],
     product := #v[Main[92], Main[93], Main[94], Main[95], Main[96], Main[97], Main[98],
                   Main[99], Main[100], Main[101], Main[102], Main[103], Main[104], Main[105],
                   Main[106], Main[107]],
     b_lower_byte := ⟨#v[Main[108], Main[109], Main[110], Main[111]]⟩,
     c_lower_byte := ⟨#v[Main[112], Main[113], Main[114], Main[115]]⟩,
     b_msb := Main[116], c_msb := Main[117],
     product_msb := ⟨Main[118]⟩,
     b_sign_extend := Main[119], c_sign_extend := Main[120] },
   -- c_times_quotient_upper (45 cells: Main[121..165])
   { carry := #v[Main[121], Main[122], Main[123], Main[124], Main[125], Main[126], Main[127],
                 Main[128], Main[129], Main[130], Main[131], Main[132], Main[133], Main[134],
                 Main[135], Main[136]],
     product := #v[Main[137], Main[138], Main[139], Main[140], Main[141], Main[142], Main[143],
                   Main[144], Main[145], Main[146], Main[147], Main[148], Main[149], Main[150],
                   Main[151], Main[152]],
     b_lower_byte := ⟨#v[Main[153], Main[154], Main[155], Main[156]]⟩,
     c_lower_byte := ⟨#v[Main[157], Main[158], Main[159], Main[160]]⟩,
     b_msb := Main[161], c_msb := Main[162],
     product_msb := ⟨Main[163]⟩,
     b_sign_extend := Main[164], c_sign_extend := Main[165] },
   -- aux_post (Main[166..240]) : DivRemAuxPost (14 fields)
   { c_neg_operation := ⟨#v[Main[166], Main[167], Main[168], Main[169]]⟩,
     rem_neg_operation := ⟨#v[Main[170], Main[171], Main[172], Main[173]]⟩,
     remainder_lt_operation :=
       { u16_compare_operation := ⟨Main[174]⟩,
         u16_flags := #v[Main[175], Main[176], Main[177], Main[178]],
         not_eq_inv := Main[179],
         comparison_limbs := #v[Main[180], Main[181]] },
     carry := #v[Main[182], Main[183], Main[184], Main[185],
                 Main[186], Main[187], Main[188], Main[189]],
     is_c_0 :=
       { is_zero_limb := #v[⟨Main[190], Main[191]⟩, ⟨Main[192], Main[193]⟩,
                            ⟨Main[194], Main[195]⟩, ⟨Main[196], Main[197]⟩],
         is_zero_first_half := Main[198],
         is_zero_second_half := Main[199],
         result := Main[200] },
     mode_flags := #v[Main[201], Main[202], Main[203], Main[204],
                      Main[205], Main[206], Main[207], Main[208]],
     is_overflow := Main[209],
     is_overflow_b :=
       { is_diff_zero :=
           { is_zero_limb := #v[⟨Main[210], Main[211]⟩, ⟨Main[212], Main[213]⟩,
                                ⟨Main[214], Main[215]⟩, ⟨Main[216], Main[217]⟩],
             is_zero_first_half := Main[218],
             is_zero_second_half := Main[219],
             result := Main[220] } },
     is_overflow_c :=
       { is_diff_zero :=
           { is_zero_limb := #v[⟨Main[221], Main[222]⟩, ⟨Main[223], Main[224]⟩,
                                ⟨Main[225], Main[226]⟩, ⟨Main[227], Main[228]⟩],
             is_zero_first_half := Main[229],
             is_zero_second_half := Main[230],
             result := Main[231] } },
     b_msb := ⟨Main[232]⟩, rem_msb := ⟨Main[233]⟩,
     c_msb := ⟨Main[234]⟩, quot_msb := ⟨Main[235]⟩,
     neg_flags := #v[Main[236], Main[237], Main[238], Main[239], Main[240]] },
   -- Legacy 3-flag labels (Main[241..245]).
   Main[241], Main[242], Main[243], Main[244], Main[245],
   #v[0, 0, 0],
   ⟨Main[244]⟩⟩

/-- The chip-level half-iff bridge (DivRem). **Proof body sorry'd**. -/
theorem spec_implies_allHold (Main : Vector (ZMod p) 246)
    (h_is_real : Main[244] = 1) (h_op_a_0 : Main[13] = 0)
    (h_spec : Spec (fromMain Main)) :
    (_root_.DivRem.constraints Main).allHold := by
  sorry

/-- Clean-side `correct_div`: 64-bit signed division. -/
theorem correct_div [Fact (2 ^ 24 < p)]
    (Main : Vector (ZMod p) 246) (s : SailState)
    (h_is_div : Main[201] = 1) (h_is_real : Main[244] = 1) (h_op_a_0 : Main[13] = 0)
    (h_spec : Spec (fromMain Main))
    (state_cstrs : (_root_.DivRem.constraints Main).initialState s) :
    let op_c := _root_.DivRem.sp1_op_c Main
    let op_b := _root_.DivRem.sp1_op_b Main
    let op_a := _root_.DivRem.sp1_op_a Main
    (_root_.Div.spec_div (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.DivRem.Poly.sp1_op Main).run s :=
  _root_.DivRem.Poly.correct_div Main s
    (spec_implies_allHold Main h_is_real h_op_a_0 h_spec)
    h_is_real h_is_div state_cstrs

/-! ## Full `FormalAssertion` promotion (Path-2)

`Assertion.main` is identical to the chip's `main` (no byte lookups to
drop). The 209 intermediate columns (`MulOperation × 2`, `IsZeroWord`,
`AddOperation`, sign-extension, quotient/remainder layout) stay in
legacy `Spec` via `divRemSpec` placeholder; memory-bus consistency is
deferred to OfflineMemory. -/

namespace Assertion

open Circuit

@[reducible]
def main (cols : Var DivRemCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c, op_c_memory⟩,
       _op_a_write_value,
       _b, _c, _quotient, _quotient_comp, _remainder_comp, _remainder,
       _abs_remainder, _abs_c, _max_abs_c_or_1, _c_times_quotient,
       _c_times_quotient_lower, _c_times_quotient_upper,
       aux_post,
       c_neg, abs_c_alu_event, abs_rem_alu_event, is_real, _remainder_check_multiplicity,
       next_pc_carry_value, _adapter_cols⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  let is_div   : Expression (ZMod p) := aux_post.mode_flags[0]
  let is_divu  : Expression (ZMod p) := aux_post.mode_flags[1]
  let is_rem_f : Expression (ZMod p) := aux_post.mode_flags[2]
  let is_remu  : Expression (ZMod p) := aux_post.mode_flags[3]
  let is_divw  : Expression (ZMod p) := aux_post.mode_flags[4]
  let is_remw  : Expression (ZMod p) := aux_post.mode_flags[5]
  let is_divuw : Expression (ZMod p) := aux_post.mode_flags[6]
  let is_remuw : Expression (ZMod p) := aux_post.mode_flags[7]
  SP1Clean.ProgramTable.assertion
    (⟨pc,
      is_div * 15 + is_divu * 16 + is_rem_f * 17 + is_remu * 18
        + is_divw * 25 + is_remw * 27 + is_divuw * 26 + is_remuw * 28,
      op_a, #v[op_b, 0, 0, 0], #v[op_c, 0, 0, 0], op_a_0, 0, 0⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  SP1Clean.AddrAddOp.assertion
    (⟨#v[pc[0], pc[1], pc[2], (0 : Expression (ZMod p))],
       #v[(4 : Expression (ZMod p)), 0, 0, 0],
       next_pc_carry_value⟩ :
      Var SP1Clean.AddrAddOp.Inputs (ZMod p))
  c_neg * (c_neg - 1) === 0
  abs_c_alu_event * (abs_c_alu_event - 1) === 0
  abs_rem_alu_event * (abs_rem_alu_event - 1) === 0
  is_real * (is_real - 1) === 0
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
-- Higher heartbeats: 25 input fields + 4 subcircuit calls + 3 OperandAccess
-- calls pushes localLength_eq synthesis past the default 200k cap.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) DivRemCols unit where
  name := "SP1Clean.DivRem"
  main := main
  localLength _ := 0

def Assumptions (_ : DivRemCols (ZMod p)) : Prop := True

def FormalSpec (cols : DivRemCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let is_div   : ZMod p := cols.aux_post.mode_flags[0]
  let is_divu  : ZMod p := cols.aux_post.mode_flags[1]
  let is_rem_f : ZMod p := cols.aux_post.mode_flags[2]
  let is_remu  : ZMod p := cols.aux_post.mode_flags[3]
  let is_divw  : ZMod p := cols.aux_post.mode_flags[4]
  let is_remw  : ZMod p := cols.aux_post.mode_flags[5]
  let is_divuw : ZMod p := cols.aux_post.mode_flags[6]
  let is_remuw : ZMod p := cols.aux_post.mode_flags[7]
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc,
      opcode := is_div * 15 + is_divu * 16 + is_rem_f * 17 + is_remu * 18
                  + is_divw * 25 + is_remw * 27 + is_divuw * 26 + is_remuw * 28,
      op_a := cols.adapter.op_a, op_b := #v[cols.adapter.op_b, 0, 0, 0],
      op_c := #v[cols.adapter.op_c, 0, 0, 0],
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 0 } ∧
  SP1Clean.AddrAddOp.assertion.Spec
    ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
     #v[(4 : ZMod p), 0, 0, 0],
     cols.next_pc_carry_value⟩ ∧
  cols.c_neg * (cols.c_neg - 1) = 0 ∧
  cols.abs_c_alu_event * (cols.abs_c_alu_event - 1) = 0 ∧
  cols.abs_rem_alu_event * (cols.abs_rem_alu_event - 1) = 0 ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.adapter.op_a_0 = 0 ∧
  -- Iter-8 sub-task E: per-operand memory-bus byte-content consequences.
  -- R-type: op_a/+4, op_b/+3, op_c/+2.
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 4, cols.adapter.op_a_memory.access_timestamp.prev_low, cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 3, cols.adapter.op_b_memory.access_timestamp.prev_low, cols.adapter.op_b_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_b_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 2, cols.adapter.op_c_memory.access_timestamp.prev_low, cols.adapter.op_c_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_c_memory.prev_value⟩

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22, e23, e24, e25⟩ := h_input
  -- e19 is the 14-way conjunction of DivRemAuxPost field equations.
  -- Flatten enough to expose the mode_flags equation so `subst_eqs` can
  -- substitute `input_aux_post_mode_flags` globally.
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, e_mf, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := e19
  subst_eqs
  obtain ⟨h_cpu_sub, h_prog_sub, h_addr_sub, h_c_neg, h_abs_c, h_abs_rem, h_real,
          h_op_a_0, h_oa_a, h_oa_b, h_oa_c⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · convert h_prog_sub trivial using 2
    simp only [Vector.getElem_map]
  · simp only [Vector.getElem_map]
    exact h_addr_sub trivial
  · linear_combination h_c_neg
  · linear_combination h_abs_c
  · linear_combination h_abs_rem
  · linear_combination h_real
  · exact h_op_a_0
  · exact h_oa_a trivial
  · exact h_oa_b trivial
  · exact h_oa_c trivial

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22, e23, e24, e25⟩ := h_input
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, e_mf, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := e19
  subst_eqs
  obtain ⟨h_cpu, h_prog, h_addr, h_c_neg, h_abs_c, h_abs_rem, h_real, h_op_a_0,
          h_oa_a, h_oa_b, h_oa_c⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · refine ⟨trivial, ?_⟩
    convert h_prog using 2
    simp only [Vector.getElem_map]
  · refine ⟨trivial, ?_⟩
    simp only [Vector.getElem_map] at h_addr
    exact h_addr
  · linear_combination h_c_neg
  · linear_combination h_abs_c
  · linear_combination h_abs_rem
  · linear_combination h_real
  · exact h_op_a_0
  · exact ⟨trivial, h_oa_a⟩
  · exact ⟨trivial, h_oa_b⟩
  · exact ⟨trivial, h_oa_c⟩

end Assertion

def assertion : FormalAssertion (ZMod p) DivRemCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.DivRem
