import SP1Clean.Faithful.LtChip
import SP1Clean.Extracted.ChipOracle.Branch
import SP1Clean.Faithful.LtOperationUnsigned
import SP1Clean.Faithful.U16MSBOperation
import SP1Clean.Faithful.ITypeReaderImmutable
import SP1Clean.Proofs.Chips.BranchChip.Formal

/-!
# Exact whole-chip faithfulness for SP1 `Branch`

This file relates the native Clean Branch row to the complete generated row-level oracle for
pinned SP1 v6.4.0. The public `ChipFaithful` theorem covers every assertion and the complete active
interaction multiset across State, Byte, Memory, and Program.
-/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Rebuild the shared standalone `LtOperationSigned` block as the byte-identical struct embedded in
the generated Branch oracle namespace. -/
def branchOracleCompareOperation {F : Type} (cols : Extracted.LtOperationSigned F) :
    Extracted.BranchOracle.LtOperationSigned F :=
  { result :=
      { u16_compare_operation := { bit := cols.result.u16_compare_operation.bit }
        u16_flags := cols.result.u16_flags
        not_eq_inv := cols.result.not_eq_inv
        comparison_limbs := cols.result.comparison_limbs }
    b_msb := { msb := cols.b_msb.msb }
    c_msb := { msb := cols.c_msb.msb } }

/-- Inverse of `branchOracleCompareOperation`. -/
def branchNativeCompareOperation {F : Type} (cols : Extracted.BranchOracle.LtOperationSigned F) :
    Extracted.LtOperationSigned F :=
  { result :=
      { u16_compare_operation := { bit := cols.result.u16_compare_operation.bit }
        u16_flags := cols.result.u16_flags
        not_eq_inv := cols.result.not_eq_inv
        comparison_limbs := cols.result.comparison_limbs }
    b_msb := { msb := cols.b_msb.msb }
    c_msb := { msb := cols.c_msb.msb } }

/-- Whole-chip row reconfiguration. The reader blocks, the flag/next-pc columns, and the compare
block's cell values are already the canonical generated substrate; the compare block is copied into
Rust's chip-private operation row. This is not an operation-level faithfulness claim. -/
def branchChipReconfigure {F : Type} (cols : BranchChip.Columns F) :
    Extracted.BranchOracle.BranchColumns F :=
  { state := cols.state
    adapter := cols.adapter
    next_pc := cols.next_pc
    is_beq := cols.is_beq
    is_bne := cols.is_bne
    is_blt := cols.is_blt
    is_bge := cols.is_bge
    is_bltu := cols.is_bltu
    is_bgeu := cols.is_bgeu
    is_branching := cols.is_branching
    compare_operation := branchOracleCompareOperation cols.compare_operation }

/-- Inverse whole-row map used to reconstruct the native proof row from an arbitrary Rust row. -/
def branchChipDeconfigure {F : Type} (cols : Extracted.BranchOracle.BranchColumns F) :
    BranchChip.Columns F :=
  { state := cols.state
    adapter := cols.adapter
    next_pc := cols.next_pc
    is_beq := cols.is_beq
    is_bne := cols.is_bne
    is_blt := cols.is_blt
    is_bge := cols.is_bge
    is_bltu := cols.is_bltu
    is_bgeu := cols.is_bgeu
    is_branching := cols.is_branching
    compare_operation := branchNativeCompareOperation cols.compare_operation }

/-- SP1 Rust's complete Branch-chip oracle, viewed from the native Lean row. -/
def branchChipOracle {F : Type} [FiniteField F] [CoeHead F ℕ] :
    ChipOracle F BranchChip.Columns Extracted.BranchOracle.BranchColumns where
  reconfigure := branchChipReconfigure
  deconfigure := branchChipDeconfigure
  reconfigure_deconfigure := by intro cols; cases cols; rfl
  deconfigure_reconfigure := by intro cols; cases cols; rfl
  assertZeros := Extracted.BranchOracle.BranchColumns.asserts
  interactions := Extracted.BranchOracle.BranchColumns.interactions

/- Namespace bridges between the Branch oracle's embedded chip-private helper copies and the
canonical standalone generated modules. The two bodies are rendered from the same compiler output,
so each bridge is a definitional unfolding, not a mathematical claim. They let every heavy
compare-op lemma below stay stated once against the standalone modules (also consumed by the Lt
chip and the DivRem oracle bridges). -/

private theorem branchOracle_u16compare_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a b bit is_real : F) :
    Extracted.BranchOracle.U16CompareOperation.asserts a b ⟨bit⟩ is_real =
      Extracted.U16CompareOperation.asserts a b ⟨bit⟩ is_real := by
  rw [Extracted.BranchOracle.U16CompareOperation.asserts,
    Extracted.U16CompareOperation.asserts]

private theorem branchOracle_u16compare_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a b bit is_real : F) :
    Extracted.BranchOracle.U16CompareOperation.interactions a b ⟨bit⟩ is_real =
      Extracted.U16CompareOperation.interactions a b ⟨bit⟩ is_real := by
  rw [Extracted.BranchOracle.U16CompareOperation.interactions,
    Extracted.U16CompareOperation.interactions]

private theorem branchOracle_u16msb_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a msb is_real : F) :
    Extracted.BranchOracle.U16MSBOperation.asserts a ⟨msb⟩ is_real =
      Extracted.U16MSBOperation.asserts a ⟨msb⟩ is_real := by
  rw [Extracted.BranchOracle.U16MSBOperation.asserts,
    Extracted.U16MSBOperation.asserts]

private theorem branchOracle_u16msb_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a msb is_real : F) :
    Extracted.BranchOracle.U16MSBOperation.interactions a ⟨msb⟩ is_real =
      Extracted.U16MSBOperation.interactions a ⟨msb⟩ is_real := by
  rw [Extracted.BranchOracle.U16MSBOperation.interactions,
    Extracted.U16MSBOperation.interactions]

private theorem branchOracle_ltUnsigned_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (b cc : Word F) (bit : F) (u16_flags : Vector F 4) (not_eq_inv : F)
    (comparison_limbs : Vector F 2) (is_real : F) :
    Extracted.BranchOracle.LtOperationUnsigned.asserts b cc
        ⟨⟨bit⟩, u16_flags, not_eq_inv, comparison_limbs⟩ is_real =
      Extracted.LtOperationUnsigned.asserts b cc
        ⟨⟨bit⟩, u16_flags, not_eq_inv, comparison_limbs⟩ is_real := by
  rw [Extracted.BranchOracle.LtOperationUnsigned.asserts,
    Extracted.LtOperationUnsigned.asserts]
  simp only [branchOracle_u16compare_asserts_eq]

private theorem branchOracle_ltUnsigned_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (b cc : Word F) (bit : F) (u16_flags : Vector F 4) (not_eq_inv : F)
    (comparison_limbs : Vector F 2) (is_real : F) :
    Extracted.BranchOracle.LtOperationUnsigned.interactions b cc
        ⟨⟨bit⟩, u16_flags, not_eq_inv, comparison_limbs⟩ is_real =
      Extracted.LtOperationUnsigned.interactions b cc
        ⟨⟨bit⟩, u16_flags, not_eq_inv, comparison_limbs⟩ is_real := by
  rw [Extracted.BranchOracle.LtOperationUnsigned.interactions,
    Extracted.LtOperationUnsigned.interactions]
  simp only [branchOracle_u16compare_interactions_eq]

private theorem branchOracle_ltSigned_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (b cc : Word F) (bit : F) (u16_flags : Vector F 4) (not_eq_inv : F)
    (comparison_limbs : Vector F 2) (bMsb cMsb is_signed is_real : F) :
    Extracted.BranchOracle.LtOperationSigned.asserts b cc
        ⟨⟨⟨bit⟩, u16_flags, not_eq_inv, comparison_limbs⟩, ⟨bMsb⟩, ⟨cMsb⟩⟩
        is_signed is_real =
      Extracted.LtOperationSigned.asserts b cc
        ⟨⟨⟨bit⟩, u16_flags, not_eq_inv, comparison_limbs⟩, ⟨bMsb⟩, ⟨cMsb⟩⟩
        is_signed is_real := by
  rw [Extracted.BranchOracle.LtOperationSigned.asserts,
    Extracted.LtOperationSigned.asserts]
  simp only [branchOracle_u16msb_asserts_eq, branchOracle_ltUnsigned_asserts_eq]

private theorem branchOracle_ltSigned_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (b cc : Word F) (bit : F) (u16_flags : Vector F 4) (not_eq_inv : F)
    (comparison_limbs : Vector F 2) (bMsb cMsb is_signed is_real : F) :
    Extracted.BranchOracle.LtOperationSigned.interactions b cc
        ⟨⟨⟨bit⟩, u16_flags, not_eq_inv, comparison_limbs⟩, ⟨bMsb⟩, ⟨cMsb⟩⟩
        is_signed is_real =
      Extracted.LtOperationSigned.interactions b cc
        ⟨⟨⟨bit⟩, u16_flags, not_eq_inv, comparison_limbs⟩, ⟨bMsb⟩, ⟨cMsb⟩⟩
        is_signed is_real := by
  rw [Extracted.BranchOracle.LtOperationSigned.interactions,
    Extracted.LtOperationSigned.interactions]
  simp only [branchOracle_u16msb_interactions_eq, branchOracle_ltUnsigned_interactions_eq]

def branchChipInput {F : Type} [Add F]
    (cols : BranchChip.Columns F) : BranchChip.Inputs F :=
  { is_real :=
      cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge +
        cols.is_bltu + cols.is_bgeu
    state := cols.state
    adapter := cols.adapter }

private theorem branchChipInput_isReal {F : Type} [Add F]
    (cols : BranchChip.Columns F) :
    (branchChipInput cols).is_real =
      cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge +
        cols.is_bltu + cols.is_bgeu := rfl

def branchChipPrefix {F : Type}
    (cols : BranchChip.Columns F) : Vector F 10 :=
  #v[cols.is_beq, cols.is_bne, cols.is_blt, cols.is_bge,
    cols.is_bltu, cols.is_bgeu, cols.is_branching,
    cols.next_pc[0], cols.next_pc[1], cols.next_pc[2]]

def branchChipLocals {F : Type}
    (cols : BranchChip.Columns F) : Vector F 20 :=
  Vector.cast (by rfl)
    (branchChipPrefix cols ++
      toElements cols.compare_operation)

def branchChipPhysicalRow {F : Type} [Add F]
    (cols : BranchChip.Columns F) : Array F :=
  inputFirstRow (branchChipInput cols) (branchChipLocals cols)

private theorem vec3_eta {F : Type} (value : Vector F 3) :
    #v[value[0], value[1], value[2]] = value := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

private theorem branchChipLocals_prefix {F : Type}
    (cols : BranchChip.Columns F) (i : ℕ) (hi : i < 10) :
    (branchChipLocals cols)[i] = (branchChipPrefix cols)[i] := by
  unfold branchChipLocals
  rw [Vector.getElem_cast, Vector.getElem_append_left hi]

private theorem branchChipLocals_suffix {F : Type}
    (cols : BranchChip.Columns F) (i : ℕ)
    (hi : i < size Extracted.LtOperationSigned) :
    (branchChipLocals cols)[10 + i]'(by
      have hsize : size Extracted.LtOperationSigned = 10 := rfl
      rw [hsize] at hi
      omega) =
      (toElements cols.compare_operation)[i] := by
  unfold branchChipLocals
  rw [Vector.getElem_cast,
    Vector.getElem_append_right (by
      have hsize : size Extracted.LtOperationSigned = 10 := rfl
      rw [hsize] at hi
      omega) (by omega)]
  congr
  omega

private theorem branchChipPrefix_zero {F : Type}
    (cols : BranchChip.Columns F) :
    (branchChipPrefix cols)[0] = cols.is_beq := rfl

private theorem branchChipPrefix_one {F : Type}
    (cols : BranchChip.Columns F) :
    (branchChipPrefix cols)[1] = cols.is_bne := rfl

private theorem branchChipPrefix_two {F : Type}
    (cols : BranchChip.Columns F) :
    (branchChipPrefix cols)[2] = cols.is_blt := rfl

private theorem branchChipPrefix_three {F : Type}
    (cols : BranchChip.Columns F) :
    (branchChipPrefix cols)[3] = cols.is_bge := rfl

private theorem branchChipPrefix_four {F : Type}
    (cols : BranchChip.Columns F) :
    (branchChipPrefix cols)[4] = cols.is_bltu := rfl

private theorem branchChipPrefix_five {F : Type}
    (cols : BranchChip.Columns F) :
    (branchChipPrefix cols)[5] = cols.is_bgeu := rfl

private theorem branchChipPrefix_six {F : Type}
    (cols : BranchChip.Columns F) :
    (branchChipPrefix cols)[6] = cols.is_branching := rfl

private theorem branchChipPrefix_seven {F : Type}
    (cols : BranchChip.Columns F) :
    (branchChipPrefix cols)[7] = cols.next_pc[0] := rfl

private theorem branchChipPrefix_eight {F : Type}
    (cols : BranchChip.Columns F) :
    (branchChipPrefix cols)[8] = cols.next_pc[1] := rfl

private theorem branchChipPrefix_nine {F : Type}
    (cols : BranchChip.Columns F) :
    (branchChipPrefix cols)[9] = cols.next_pc[2] := rfl

omit [Fact (2 ^ 17 < p)] in
private theorem eval_branchChipCompare
    (cols : BranchChip.Columns (ZMod p))
    (data : ProverData (ZMod p)) :
    Eval.eval
        (Environment.fromArray
          (inputFirstRow (branchChipInput cols)
            (branchChipLocals cols)) data)
        (varFromOffset Extracted.LtOperationSigned (F := ZMod p)
          (size BranchChip.Inputs + 10)) =
      cols.compare_operation := by
  rw [ProvableType.eval_varFromOffset]
  rw [← ProvableType.fromElements_toElements cols.compare_operation]
  apply congrArg fromElements
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_mapRange]
  have hlocal := eval_local_inputFirstRow
    (branchChipInput cols) (branchChipLocals cols) data (10 + i) (by
      have hsize : size Extracted.LtOperationSigned = 10 := rfl
      rw [hsize] at hi
      omega)
  simp only [Expression.eval] at hlocal
  exact (by
    simpa only [Nat.add_assoc] using
      hlocal.trans (branchChipLocals_suffix cols i hi))

omit [Fact (2 ^ 17 < p)] in
private theorem eval_branchChipPrefixLocal
    (cols : BranchChip.Columns (ZMod p))
    (data : ProverData (ZMod p)) (i : ℕ) (hi : i < 10) :
    Expression.eval
        (Environment.fromArray
          (inputFirstRow (branchChipInput cols)
            (branchChipLocals cols)) data)
        (var { index := size BranchChip.Inputs + i }) =
      (branchChipPrefix cols)[i] := by
  exact (eval_local_inputFirstRow (branchChipInput cols)
    (branchChipLocals cols) data i (by omega)).trans
      (branchChipLocals_prefix cols i hi)

theorem eval_branchChipDirectOutput
    (cols : BranchChip.Columns (ZMod p))
    (data : ProverData (ZMod p)) :
    ProvableType.eval
        (Environment.fromArray
          (inputFirstRow (branchChipInput cols)
            (branchChipLocals cols)) data)
        ((BranchChip.elaborated (p := p)).output
          (varFromOffset BranchChip.Inputs 0)
          (size BranchChip.Inputs)) =
      cols := by
  rw [BranchChip.directOutput_eq]
  rw [← CircuitType.eval_expression, BranchChip.eval_columns]
  rw [BranchChip.Columns.mk.injEq]
  dsimp only
  have hinputEval := eval_inputFirstRow
    (branchChipInput cols) (branchChipLocals cols) data
  rw [BranchChip.eval_inputs, BranchChip.Inputs.mk.injEq] at hinputEval
  refine
    ⟨by simpa only [branchChipInput] using hinputEval.2.1,
      by simpa only [branchChipInput] using hinputEval.2.2,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
  · apply Vector.ext
    intro i hi
    rw [← ProvableType.getElem_eval_fields
      (Environment.fromArray
        (inputFirstRow (branchChipInput cols)
          (branchChipLocals cols)) data)
      (Vector.mapRange 3 fun i =>
        var { index := size BranchChip.Inputs + 7 + i }) i hi]
    rw [Vector.getElem_mapRange]
    interval_cases i
    · simpa only [branchChipPrefix_seven] using
        (eval_branchChipPrefixLocal (p := p) cols data 7 (by decide))
    · simpa only [branchChipPrefix_eight] using
        (eval_branchChipPrefixLocal (p := p) cols data 8 (by decide))
    · simpa only [branchChipPrefix_nine] using
        (eval_branchChipPrefixLocal (p := p) cols data 9 (by decide))
  · simpa only [branchChipPrefix_zero, ProvableType.eval_field,
      Nat.add_zero] using
      (eval_branchChipPrefixLocal (p := p) cols data 0 (by decide))
  · simpa only [branchChipPrefix_one, ProvableType.eval_field] using
      (eval_branchChipPrefixLocal (p := p) cols data 1 (by decide))
  · simpa only [branchChipPrefix_two, ProvableType.eval_field] using
      (eval_branchChipPrefixLocal (p := p) cols data 2 (by decide))
  · simpa only [branchChipPrefix_three, ProvableType.eval_field] using
      (eval_branchChipPrefixLocal (p := p) cols data 3 (by decide))
  · simpa only [branchChipPrefix_four, ProvableType.eval_field] using
      (eval_branchChipPrefixLocal (p := p) cols data 4 (by decide))
  · simpa only [branchChipPrefix_five, ProvableType.eval_field] using
      (eval_branchChipPrefixLocal (p := p) cols data 5 (by decide))
  · simpa only [branchChipPrefix_six, ProvableType.eval_field] using
      (eval_branchChipPrefixLocal (p := p) cols data 6 (by decide))
  · exact eval_branchChipCompare cols data

def branchChipRowCodec :
    ChipRowCodec BranchChip.Inputs BranchChip.Columns
      (BranchChip.circuit (p := p)) where
  assignment cols data := {
    row := branchChipPhysicalRow cols
    input := branchChipInput cols
    width_eq := by
      rw [branchChipPhysicalRow, inputFirstRow_size,
        Air.Flat.Component.width]
      rfl
    rowInput_eq := by
      exact rowInput_inputFirstRow (BranchChip.circuit (p := p))
        (branchChipInput cols) (branchChipLocals cols) data
    rowOutput_eq := by
      change ProvableType.eval _ ((BranchChip.main _).output _) = _
      rw [BranchChip.elaborated.output_eq]
      rw [Air.Flat.Component.rowInputVar_mk,
        Air.Flat.Component.rowOffset_mk]
      exact eval_branchChipDirectOutput (p := p) cols data }

theorem branchChip_lookups_empty :
    (⟨BranchChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).operations.lookups = [] := by
  rw [Air.Flat.Component.lookups_eq,
    Air.Flat.Component.rowOperations_mk]
  change ((BranchChip.main
    (varFromOffset BranchChip.Inputs 0)).operations
      (size BranchChip.Inputs)).lookups = []
  simp [BranchChip.main, LtOperationSigned.circuit,
    LtOperationSigned.main, U16MSBOperation.circuit,
    U16MSBOperation.main, LtOperationUnsigned.circuit,
    LtOperationUnsigned.main, U16CompareOperation.circuit,
    U16CompareOperation.main, Readers.CPUState.circuit,
    Readers.CPUState.main, Readers.ITypeReaderImmutable.circuit,
    Readers.ITypeReaderImmutable.main,
    Readers.RegisterAccessCols.circuit,
    Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit,
    Readers.RegisterAccessTimestamp.main,
    Gadgets.Equality.main, circuit_norm]

private def branchFlag (offset i : ℕ) : Expression (ZMod p) :=
  var { index := offset + i }

private def branchIsBranching (offset : ℕ) : Expression (ZMod p) :=
  var { index := offset + 6 }

private def branchNextPc (offset : ℕ) :
    Vector (Expression (ZMod p)) 3 :=
  #v[var { index := offset + 7 },
    var { index := offset + 8 },
    var { index := offset + 9 }]

private def branchCompare (offset : ℕ) :
    Extracted.LtOperationSigned (Expression (ZMod p)) :=
  varFromOffset Extracted.LtOperationSigned (offset + 10)

private def branchSum (offset : ℕ) : Expression (ZMod p) :=
  branchFlag offset 0 + branchFlag offset 1 +
    branchFlag offset 2 + branchFlag offset 3 +
      branchFlag offset 4 + branchFlag offset 5

private def branchOpcode (offset : ℕ) : Expression (ZMod p) :=
  branchFlag offset 0 * 40 + branchFlag offset 1 * 41 +
    branchFlag offset 2 * 42 + branchFlag offset 3 * 43 +
      branchFlag offset 4 * 44 + branchFlag offset 5 * 45

private def branchLtInput
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) :
    Var LtOperationSigned.Inputs (ZMod p) :=
  ⟨#v[input.adapter.op_a_memory.prev_value[0],
      input.adapter.op_a_memory.prev_value[1],
      input.adapter.op_a_memory.prev_value[2],
      input.adapter.op_a_memory.prev_value[3]],
    #v[input.adapter.op_b_memory.prev_value[0],
      input.adapter.op_b_memory.prev_value[1],
      input.adapter.op_b_memory.prev_value[2],
      input.adapter.op_b_memory.prev_value[3]],
    branchCompare offset,
    branchFlag offset 2 + branchFlag offset 3,
    input.is_real⟩

private def branchCpuInput
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) :
    Var Readers.CPUState.Inputs (ZMod p) :=
  ⟨input.state, branchNextPc offset, 8, input.is_real⟩

private def branchITypeInput
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) :
    Var Readers.ITypeReaderImmutable.Inputs (ZMod p) :=
  ⟨input.adapter, input.is_real, input.is_real,
    input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536,
    input.state.pc, branchOpcode offset⟩

private def branchInlineConstraints
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) :
    List (Expression (ZMod p)) :=
  let f0 := branchFlag offset 0
  let f1 := branchFlag offset 1
  let f2 := branchFlag offset 2
  let f3 := branchFlag offset 3
  let f4 := branchFlag offset 4
  let f5 := branchFlag offset 5
  let sum := branchSum offset
  let branching := branchIsBranching offset
  let cmp := branchCompare offset
  let nextPc := branchNextPc offset
  let isEq := (1 : Expression (ZMod p)) -
    (cmp.result.u16_flags[0] + cmp.result.u16_flags[1] +
      cmp.result.u16_flags[2] + cmp.result.u16_flags[3])
  let bit := cmp.result.u16_compare_operation.bit
  let decision := f0 * isEq + f1 * (1 - isEq) +
    (f3 + f5) * (1 - bit) + (f2 + f4) * bit
  let inv := Expression.const ((65536 : ZMod p)⁻¹)
  let taken0 :=
    (input.state.pc[0] + input.adapter.op_c_imm[0] -
      nextPc[0]) * inv
  let taken1 :=
    (input.state.pc[1] + input.adapter.op_c_imm[1] -
      nextPc[1] + taken0) * inv
  let taken2 :=
    (input.state.pc[2] + input.adapter.op_c_imm[2] -
      nextPc[2] + taken1) * inv
  let taken3 :=
    (input.adapter.op_c_imm[3] + taken2) * inv
  let fall0 :=
    (input.state.pc[0] + (4 : Expression (ZMod p)) -
      nextPc[0]) * inv
  let fall1 :=
    (input.state.pc[1] - nextPc[1] + fall0) * inv
  let fall2 :=
    (input.state.pc[2] - nextPc[2] + fall1) * inv
  let fall3 := fall2 * inv
  let fallGate := sum - branching
  [ f0 * (f0 - 1), f1 * (f1 - 1),
    f2 * (f2 - 1), f3 * (f3 - 1),
    f4 * (f4 - 1), f5 * (f5 - 1),
    input.is_real - sum, sum * (sum - 1),
    branching * (branching - 1),
    sum * (branching - decision),
    branching * (taken0 * (taken0 - 1)),
    branching * (taken1 * (taken1 - 1)),
    branching * (taken2 * (taken2 - 1)),
    branching * (taken3 * (taken3 - 1)),
    fallGate * (fall0 * (fall0 - 1)),
    fallGate * (fall1 * (fall1 - 1)),
    fallGate * (fall2 * (fall2 - 1)),
    fallGate * (fall3 * (fall3 - 1)) ]

private def branchNativeMeaning
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
      (nativeAssertZeros env
        ((LtOperationSigned.main
          (branchLtInput input offset)).operations (offset + 20))) ∧
    List.Forall (· = 0)
      ((branchInlineConstraints input offset).map
        (Expression.eval env)) ∧
    List.Forall (· = 0)
      (nativeAssertZeros env
        ((Readers.CPUState.main
          (branchCpuInput input offset)).operations (offset + 20))) ∧
    List.Forall (· = 0)
      (nativeAssertZeros env
        ((Readers.ITypeReaderImmutable.main
          (branchITypeInput input offset)).operations (offset + 20)))

private theorem branchNativeAssertionsDecompose
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (nativeAssertZeros env
          ((BranchChip.main input).operations offset)) ↔
      branchNativeMeaning env input offset := by
  have hLtSize : size Extracted.LtOperationSigned = 10 := rfl
  unfold branchNativeMeaning
  simp only [nativeAssertZeros, BranchChip.main,
    Circuit.operations, Circuit.bind_def, Circuit.pure_def,
    witnessVectorIR, witnessField, Witnessable.witness, witnessIR,
    subcircuitWithAssertion, assertion, assertZero,
    HasAssertEq.assert_eq, Expression.assertEquals,
    Channel.pullIf, Operations.localLength]
  simp only [Operations.constraints_append,
    Operations.constraints_witness,
    Operations.constraints_subcircuit,
    constraints_toSubcircuit_generalFormalCircuit,
    constraints_toSubcircuit_formalAssertion,
    GeneralFormalCircuit.toSubcircuit_localLength,
    FormalAssertion.toSubcircuit_localLength,
    LtOperationSigned.circuit_localLength,
    Readers.CPUState.circuit_localLength,
    Gadgets.Equality.localLength_eq,
    Operations.constraints_assert,
    Operations.constraints_interact,
    Operations.constraints_nil,
    List.map_append, List.map_cons, List.map_nil,
    List.forall_append, List.forall_cons]
  simp only [branchLtInput, branchCpuInput, branchITypeInput,
    branchInlineConstraints, branchFlag, branchIsBranching,
    branchNextPc, branchCompare, branchSum, branchOpcode,
    LtOperationSigned.circuit, Readers.CPUState.circuit,
    Readers.ITypeReaderImmutable.circuit,
    Gadgets.Equality.circuit,
    ProvableType.varFromOffset_fields,
    hLtSize, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd,
    Vector.getElem_mapRange, List.Forall, true_and, and_true,
    eval_sub, Expression.eval]
  repeat' rw [CanonicalReader.equalityAssertionList]
  simp only [List.map_cons, List.map_nil, List.Forall,
    Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ,
    eval_sub, Expression.eval, sub_zero]
  tauto

private theorem vec2_eta {F : Type} (value : Vector F 2) :
    #v[value[0], value[1]] = value := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

private theorem vec4_eta {F : Type} (value : Vector F 4) :
    #v[value[0], value[1], value[2], value[3]] = value := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

private theorem branchCpuEta {F : Type}
    (cols : Extracted.CPUState F) :
    ({ clk_high := cols.clk_high
       clk_16_24 := cols.clk_16_24
       clk_0_16 := cols.clk_0_16
       pc := #v[cols.pc[0], cols.pc[1], cols.pc[2]] } :
      Extracted.CPUState F) = cols := by
  cases cols
  simp only
  rw [vec3_eta]

private theorem branchITypeEta {F : Type}
    (cols : Extracted.ITypeReader F) :
    ({ op_a := cols.op_a
       op_a_memory :=
         { prev_value :=
             #v[cols.op_a_memory.prev_value[0],
               cols.op_a_memory.prev_value[1],
               cols.op_a_memory.prev_value[2],
               cols.op_a_memory.prev_value[3]]
           access_timestamp :=
             { prev_low := cols.op_a_memory.access_timestamp.prev_low
               diff_low_limb :=
                 cols.op_a_memory.access_timestamp.diff_low_limb } }
       op_a_0 := cols.op_a_0
       op_b := cols.op_b
       op_b_memory :=
         { prev_value :=
             #v[cols.op_b_memory.prev_value[0],
               cols.op_b_memory.prev_value[1],
               cols.op_b_memory.prev_value[2],
               cols.op_b_memory.prev_value[3]]
           access_timestamp :=
             { prev_low := cols.op_b_memory.access_timestamp.prev_low
               diff_low_limb :=
                 cols.op_b_memory.access_timestamp.diff_low_limb } }
       op_c_imm :=
         #v[cols.op_c_imm[0], cols.op_c_imm[1],
           cols.op_c_imm[2], cols.op_c_imm[3]] } :
      Extracted.ITypeReader F) = cols := by
  cases cols with
  | mk opA opAMemory opA0 opB opBMemory opCImm =>
      cases opAMemory with
      | mk opAPrev opATimestamp =>
          cases opATimestamp
          cases opBMemory with
          | mk opBPrev opBTimestamp =>
              cases opBTimestamp
              simp only
              rw [vec4_eta, vec4_eta, vec4_eta]

private theorem branchLtUnsignedEta {F : Type}
    (cols : Extracted.LtOperationUnsigned F) :
    ({ u16_compare_operation :=
         { bit := cols.u16_compare_operation.bit }
       u16_flags :=
         #v[cols.u16_flags[0], cols.u16_flags[1],
           cols.u16_flags[2], cols.u16_flags[3]]
       not_eq_inv := cols.not_eq_inv
       comparison_limbs :=
         #v[cols.comparison_limbs[0], cols.comparison_limbs[1]] } :
      Extracted.LtOperationUnsigned F) = cols := by
  cases cols with
  | mk compare flags inv limbs =>
      cases compare
      simp only
      rw [vec4_eta, vec2_eta]

private theorem branchLtSignedEta {F : Type}
    (cols : Extracted.LtOperationSigned F) :
    ({ result :=
         { u16_compare_operation :=
             { bit := cols.result.u16_compare_operation.bit }
           u16_flags :=
             #v[cols.result.u16_flags[0],
               cols.result.u16_flags[1],
               cols.result.u16_flags[2],
               cols.result.u16_flags[3]]
           not_eq_inv := cols.result.not_eq_inv
           comparison_limbs :=
             #v[cols.result.comparison_limbs[0],
               cols.result.comparison_limbs[1]] }
       b_msb := { msb := cols.b_msb.msb }
       c_msb := { msb := cols.c_msb.msb } } :
      Extracted.LtOperationSigned F) = cols := by
  cases cols with
  | mk result bMsb cMsb =>
      cases bMsb
      cases cMsb
      rw [Extracted.LtOperationSigned.mk.injEq]
      exact ⟨branchLtUnsignedEta result, rfl, rfl⟩

private def branchRustTail
    (cols : BranchChip.Columns (ZMod p)) : List (ZMod p) :=
  let f0 := cols.is_beq
  let f1 := cols.is_bne
  let f2 := cols.is_blt
  let f3 := cols.is_bge
  let f4 := cols.is_bltu
  let f5 := cols.is_bgeu
  let sum := f0 + f1 + f2 + f3 + f4 + f5
  let branching := cols.is_branching
  let isEq := (1 : ZMod p) -
    (cols.compare_operation.result.u16_flags[0] +
      cols.compare_operation.result.u16_flags[1] +
      cols.compare_operation.result.u16_flags[2] +
      cols.compare_operation.result.u16_flags[3])
  let bit := cols.compare_operation.result.u16_compare_operation.bit
  let decision := f0 * isEq + f1 * (1 - isEq) +
    (f3 + f5) * (1 - bit) + (f2 + f4) * bit
  let inv := (65536 : ZMod p)⁻¹
  let taken0 :=
    (cols.state.pc[0] + cols.adapter.op_c_imm[0] -
      cols.next_pc[0]) * inv
  let taken1 :=
    (cols.state.pc[1] + cols.adapter.op_c_imm[1] -
      cols.next_pc[1] + taken0) * inv
  let taken2 :=
    (cols.state.pc[2] + cols.adapter.op_c_imm[2] -
      cols.next_pc[2] + taken1) * inv
  let taken3 :=
    (cols.adapter.op_c_imm[3] + taken2) * inv
  let fall0 :=
    (cols.state.pc[0] + 4 - cols.next_pc[0]) * inv
  let fall1 :=
    (cols.state.pc[1] - cols.next_pc[1] + fall0) * inv
  let fall2 :=
    (cols.state.pc[2] - cols.next_pc[2] + fall1) * inv
  let fall3 := fall2 * inv
  let fallGate := sum - branching
  [ f0 * (f0 - 1), f1 * (f1 - 1),
    f2 * (f2 - 1), f3 * (f3 - 1),
    f4 * (f4 - 1), f5 * (f5 - 1),
    sum * (sum - 1),
    branching * (branching - 1),
    sum * (branching - decision),
    branching * (taken0 * (taken0 - 1)),
    branching * (taken1 * (taken1 - 1)),
    branching * (taken2 * (taken2 - 1)),
    branching * (taken3 * (taken3 - 1)),
    fallGate * (fall0 * (fall0 - 1)),
    fallGate * (fall1 * (fall1 - 1)),
    fallGate * (fall2 * (fall2 - 1)),
    fallGate * (fall3 * (fall3 - 1)) ]

-- The closing `ring_nf` normalizes the arithmetic inside a long right-nested list of assertions, so
-- it recurses past the 512 default. Ladder-measured: 700 fails, 1000 ok -- floor bracket (700, 1000].
-- The former 100000 stamp was ~100x over. (`ring_nf` is not redundant here, unlike the one that used
-- to sit in `branchTailMeaningFaithful`: dropping it leaves the goal open.) The other two decompose
-- lemmas in this file carried the same 100000 stamp and clear the plain default outright.
omit [Fact (2 ^ 17 < p)] in
set_option maxRecDepth 1000 in
private theorem branchColumns_asserts_decompose
    (cols : BranchChip.Columns (ZMod p)) :
    Extracted.BranchOracle.BranchColumns.asserts (branchChipReconfigure cols) =
      Extracted.CPUState.asserts cols.state cols.next_pc 8
          (cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge +
            cols.is_bltu + cols.is_bgeu) ++
      Extracted.ITypeReaderImmutable.asserts cols.state.clk_high
          (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
          cols.state.pc
          (cols.is_beq * 40 + cols.is_bne * 41 + cols.is_blt * 42 +
            cols.is_bge * 43 + cols.is_bltu * 44 + cols.is_bgeu * 45)
          cols.adapter
          (cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge +
            cols.is_bltu + cols.is_bgeu)
          (cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge +
            cols.is_bltu + cols.is_bgeu) ++
      Extracted.LtOperationSigned.asserts
          cols.adapter.op_a_memory.prev_value
          cols.adapter.op_b_memory.prev_value
          cols.compare_operation (cols.is_blt + cols.is_bge)
          (cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge +
            cols.is_bltu + cols.is_bgeu) ++
      branchRustTail cols := by
  rw [Extracted.BranchOracle.BranchColumns.asserts]
  dsimp only [branchChipReconfigure, branchOracleCompareOperation]
  simp only [branchOracle_ltSigned_asserts_eq]
  rw [branchCpuEta, branchITypeEta, branchLtSignedEta]
  simp only [vec3_eta, vec4_eta]
  simp only [branchRustTail, zero_add, add_zero, sub_zero]
  ring_nf

private def branchRustInteractionTail
    (cols : BranchChip.Columns (ZMod p)) :
    List (Extracted.Interaction (ZMod p)) :=
  let sum := cols.is_beq + cols.is_bne + cols.is_blt +
    cols.is_bge + cols.is_bltu + cols.is_bgeu
  [ ⟨.send,
      (.byte 6 (cols.next_pc[0] * (4 : ZMod p)⁻¹) 14 0),
      sum⟩,
    ⟨.send, (.byte 6 cols.next_pc[1] 16 0), sum⟩,
    ⟨.send, (.byte 6 cols.next_pc[2] 16 0), sum⟩ ]

omit [Fact (2 ^ 17 < p)] in
private theorem branchColumns_interactions_decompose
    (cols : BranchChip.Columns (ZMod p)) :
    Extracted.BranchOracle.BranchColumns.interactions (branchChipReconfigure cols) =
      Extracted.CPUState.interactions cols.state cols.next_pc 8
          (cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge +
            cols.is_bltu + cols.is_bgeu) ++
      Extracted.ITypeReaderImmutable.interactions cols.state.clk_high
          (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
          cols.state.pc
          (cols.is_beq * 40 + cols.is_bne * 41 + cols.is_blt * 42 +
            cols.is_bge * 43 + cols.is_bltu * 44 + cols.is_bgeu * 45)
          cols.adapter
          (cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge +
            cols.is_bltu + cols.is_bgeu)
          (cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge +
            cols.is_bltu + cols.is_bgeu) ++
      Extracted.LtOperationSigned.interactions
          cols.adapter.op_a_memory.prev_value
          cols.adapter.op_b_memory.prev_value
          cols.compare_operation (cols.is_blt + cols.is_bge)
          (cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge +
            cols.is_bltu + cols.is_bgeu) ++
      branchRustInteractionTail cols := by
  rw [Extracted.BranchOracle.BranchColumns.interactions]
  dsimp only [branchChipReconfigure, branchOracleCompareOperation]
  simp only [branchOracle_ltSigned_interactions_eq]
  rw [branchCpuEta, branchITypeEta, branchLtSignedEta]
  simp only [vec3_eta, vec4_eta]
  simp only [branchRustInteractionTail]

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
private theorem branchNextPcMap_eq (offset : ℕ) :
    (Vector.mapRange 3 fun i =>
      (var { index := offset + 7 + i } :
        Expression (ZMod p))) =
      branchNextPc offset := by
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_mapRange]
  interval_cases i <;> rfl

private def branchChipRustColumns
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) :
    BranchChip.Columns (ZMod p) :=
  { state := Eval.eval env input.state
    adapter := Eval.eval env input.adapter
    next_pc := Eval.eval env
      (Vector.mapRange 3 fun i =>
        (var { index := offset + 7 + i } :
          Expression (ZMod p)))
    is_beq := Expression.eval env (branchFlag offset 0)
    is_bne := Expression.eval env (branchFlag offset 1)
    is_blt := Expression.eval env (branchFlag offset 2)
    is_bge := Expression.eval env (branchFlag offset 3)
    is_bltu := Expression.eval env (branchFlag offset 4)
    is_bgeu := Expression.eval env (branchFlag offset 5)
    is_branching := Expression.eval env
      (branchIsBranching offset)
    compare_operation := Eval.eval env (branchCompare (p := p) offset) }

private def branchRustCpuMeaning
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := branchChipRustColumns env input offset
  let sum := cols.is_beq + cols.is_bne + cols.is_blt +
    cols.is_bge + cols.is_bltu + cols.is_bgeu
  List.Forall (· = 0)
    (Extracted.CPUState.asserts cols.state cols.next_pc 8 sum)

private def branchRustITypeMeaning
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := branchChipRustColumns env input offset
  let sum := cols.is_beq + cols.is_bne + cols.is_blt +
    cols.is_bge + cols.is_bltu + cols.is_bgeu
  let opcode := cols.is_beq * 40 + cols.is_bne * 41 +
    cols.is_blt * 42 + cols.is_bge * 43 +
      cols.is_bltu * 44 + cols.is_bgeu * 45
  List.Forall (· = 0)
    (Extracted.ITypeReaderImmutable.asserts
      cols.state.clk_high
      (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
      cols.state.pc opcode cols.adapter sum sum)

private def branchRustLtMeaning
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := branchChipRustColumns env input offset
  let sum := cols.is_beq + cols.is_bne + cols.is_blt +
    cols.is_bge + cols.is_bltu + cols.is_bgeu
  List.Forall (· = 0)
    (Extracted.LtOperationSigned.asserts
      cols.adapter.op_a_memory.prev_value
      cols.adapter.op_b_memory.prev_value
      cols.compare_operation (cols.is_blt + cols.is_bge) sum)

private def branchRustTailMeaning
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (branchRustTail (branchChipRustColumns env input offset))

private def branchRustMeaning
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  branchRustCpuMeaning env input offset ∧
    branchRustITypeMeaning env input offset ∧
    branchRustLtMeaning env input offset ∧
    branchRustTailMeaning env input offset

omit [Fact (2 ^ 17 < p)] in
private theorem branchRustAssertionsDecompose
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (branchChipOracle.nativeAssertZeros
          (branchChipRustColumns env input offset)) ↔
      branchRustMeaning env input offset := by
  simp only [ChipOracle.nativeAssertZeros, branchChipOracle]
  rw [branchColumns_asserts_decompose]
  unfold branchRustMeaning branchRustCpuMeaning
    branchRustITypeMeaning branchRustLtMeaning branchRustTailMeaning
  simp only [List.forall_append]
  tauto

omit [Fact (2 ^ 17 < p)] in
private theorem branchCpuMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (branchSum (p := p) offset)) :
    branchRustCpuMeaning env input offset ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((Readers.CPUState.main
            (branchCpuInput input offset)).operations (offset + 20))) := by
  let cpuInput := branchCpuInput input offset
  have hCpu := CanonicalReader.cpuStateAssertions
    (p := p) env cpuInput (offset + 20)
    (Eval.eval env input.state)
    (Eval.eval env (branchNextPc (p := p) offset))
    8 (Expression.eval env (branchSum (p := p) offset)) (by
      simp only [cpuInput, branchCpuInput,
        ProvableStruct.structEvalLiteralProc]
      exact hinputReal)
  unfold branchRustCpuMeaning
  dsimp only [branchChipRustColumns]
  rw [branchNextPcMap_eq]
  simpa only [branchSum, branchFlag, eval_add,
    Expression.eval] using hCpu

private theorem branchITypeMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (branchSum (p := p) offset)) :
    branchRustITypeMeaning env input offset ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((Readers.ITypeReaderImmutable.main
            (branchITypeInput input offset)).operations (offset + 20))) := by
  let readerInput := branchITypeInput input offset
  have hIType := CanonicalReader.iTypeImmutableAssertionsExact
    (p := p) env readerInput (offset + 20)
    (Expression.eval env input.state.clk_high)
    (Expression.eval env
      (input.state.clk_0_16 + input.state.clk_16_24 * 65536))
    (Expression.eval env (branchOpcode (p := p) offset))
    (Expression.eval env (branchSum (p := p) offset))
    (Expression.eval env (branchSum (p := p) offset))
    (Eval.eval env input.state.pc)
    (Eval.eval env input.adapter)
    (by
      simp only [readerInput, branchITypeInput,
        ProvableStruct.eval_eq_eval,
        ProvableStruct.structEvalLiteralProc]
      exact hinputReal)
    (by
      simp only [readerInput, branchITypeInput,
        ProvableStruct.eval_eq_eval,
        ProvableStruct.structEvalLiteralProc]
      exact hinputReal)
    (by
      simp only [readerInput, branchITypeInput]
      rw [Readers.ITypeReader.eval_cols]
      simp only [ProvableType.eval_field])
    (by
      simp only [readerInput, branchITypeInput]
      rw [Readers.ITypeReader.eval_cols]
      dsimp only
      rw [eval_registerAccessCols]
      exact ProvableType.getElem_eval_fields env
        input.adapter.op_a_memory.prev_value 0 (by decide))
    (by
      simp only [readerInput, branchITypeInput]
      rw [Readers.ITypeReader.eval_cols]
      dsimp only
      rw [eval_registerAccessCols]
      exact ProvableType.getElem_eval_fields env
        input.adapter.op_a_memory.prev_value 1 (by decide))
    (by
      simp only [readerInput, branchITypeInput]
      rw [Readers.ITypeReader.eval_cols]
      dsimp only
      rw [eval_registerAccessCols]
      exact ProvableType.getElem_eval_fields env
        input.adapter.op_a_memory.prev_value 2 (by decide))
    (by
      simp only [readerInput, branchITypeInput]
      rw [Readers.ITypeReader.eval_cols]
      dsimp only
      rw [eval_registerAccessCols]
      exact ProvableType.getElem_eval_fields env
        input.adapter.op_a_memory.prev_value 3 (by decide))
    rfl
  unfold branchRustITypeMeaning
  dsimp only [branchChipRustColumns]
  simpa only [readerInput, branchITypeInput, branchSum,
    branchOpcode, branchFlag, eval_cpuState,
    Readers.ITypeReader.eval_cols, ProvableType.eval_field,
    eval_add, eval_mul, Expression.eval] using hIType

private theorem branchLtMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (branchSum (p := p) offset)) :
    branchRustLtMeaning env input offset ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((LtOperationSigned.main
            (branchLtInput input offset)).operations (offset + 20))) := by
  let ltInput := branchLtInput input offset
  have hA :
      Eval.eval env ltInput.b =
        (Eval.eval env input.adapter).op_a_memory.prev_value := by
    simp only [ltInput, branchLtInput]
    rw [vec4_eta]
    rw [Readers.ITypeReader.eval_cols]
    dsimp only
    rw [eval_registerAccessCols]
  have hB :
      Eval.eval env ltInput.cc =
        (Eval.eval env input.adapter).op_b_memory.prev_value := by
    simp only [ltInput, branchLtInput]
    rw [vec4_eta]
    rw [Readers.ITypeReader.eval_cols]
    dsimp only
    rw [eval_registerAccessCols]
  have hExact := ltSigned_assertions_exact
    (p := p) env ltInput (offset + 20)
  rw [hA, hB] at hExact
  simp only [ltInput, branchLtInput, branchFlag,
    Expression.eval] at hExact
  rw [hinputReal] at hExact
  simp only [branchSum, branchFlag,
    Expression.eval] at hExact
  unfold branchRustLtMeaning
  dsimp only [branchChipRustColumns]
  simp only [branchFlag, Expression.eval]
  rw [← hExact]
  rfl

-- Formerly carried a 1600000 ceiling against a measured floor of (200000, 400000]. The whole cost
-- was the `ring_nf` that used to sit before the closing `tauto`: diagnostics put the failure inside
-- `ring_nf` itself (it is simp-based, and its own `Mathlib.Tactic.RingNF.*` lemmas dominate the
-- census -- `mul_assoc_rev` 142, `add_assoc_rev` 64, `mul_neg`/`add_neg` 22 each), with no whnf
-- runaway anywhere (top elaboration counter only 765). It was also redundant: `tauto` closes the
-- goal on its own. Dropping it took the floor below 20000 -- >10x -- so the ceiling is gone.
omit [Fact (2 ^ 17 < p)] in
private theorem branchTailMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (branchSum (p := p) offset)) :
    branchRustTailMeaning env input offset ↔
      List.Forall (· = 0)
        ((branchInlineConstraints input offset).map
          (Expression.eval env)) := by
  unfold branchRustTailMeaning
  dsimp only [branchChipRustColumns]
  rw [branchNextPcMap_eq]
  simp only [branchRustTail, branchInlineConstraints]
  simp only [branchFlag, branchIsBranching, branchNextPc,
    branchCompare, branchSum,
    eval_cpuState, Readers.ITypeReader.eval_cols,
    eval_ltSignedColumns, eval_ltUnsignedColumns,
    eval_u16CompareColumns, ProvableType.eval_field,
    ← ProvableType.getElem_eval_fields,
    Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ,
    List.map_cons, List.map_nil, List.Forall,
    eval_sub, Expression.eval]
  rw [hinputReal]
  simp only [branchSum, branchFlag,
    Expression.eval, sub_self]
  tauto

private theorem branchMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (branchSum (p := p) offset)) :
    branchRustMeaning env input offset ↔
      branchNativeMeaning env input offset := by
  unfold branchRustMeaning branchNativeMeaning
  rw [branchCpuMeaningFaithful env input offset hinputReal,
    branchITypeMeaningFaithful env input offset hinputReal,
    branchLtMeaningFaithful env input offset hinputReal,
    branchTailMeaningFaithful env input offset hinputReal]
  tauto

theorem branchChip_constraints_faithful
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : BranchChip.Columns (ZMod p))
    (hbind : BindsChipOutput BranchChip.main env input offset cols)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (branchSum (p := p) offset)) :
    List.Forall (· = 0)
        (branchChipOracle.nativeAssertZeros cols) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((BranchChip.main input).operations offset)) := by
  replace hbind := BindsChipOutput.ofElaborated
    (BranchChip.elaborated (p := p)) hbind
  rw [BranchChip.directOutput_eq] at hbind
  rw [← ProvableStruct.eval_eq_eval,
    BranchChip.eval_columns] at hbind
  simp only [ProvableType.eval_field] at hbind
  change branchChipRustColumns env input offset = cols at hbind
  subst cols
  exact (branchRustAssertionsDecompose
    (p := p) env input offset).trans
      ((branchMeaningFaithful env input offset hinputReal).trans
        (branchNativeAssertionsDecompose env input offset).symm)

private theorem branchChipRowCodec_inputReal
    (cols : BranchChip.Columns (ZMod p))
    (data : ProverData (ZMod p)) :
    let assignment := branchChipRowCodec.assignment cols data
    Expression.eval assignment.environment
        (⟨BranchChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowInputVar.is_real =
      Expression.eval assignment.environment
        (branchSum
          (⟨BranchChip.circuit (p := p)⟩ :
            Air.Flat.Component (ZMod p)).rowOffset) := by
  dsimp only
  let assignment := branchChipRowCodec.assignment cols data
  rw [Air.Flat.Component.rowInputVar_mk,
    Air.Flat.Component.rowOffset_mk]
  have hInput :
      Expression.eval
          (Environment.fromArray
            (inputFirstRow (branchChipInput cols)
              (branchChipLocals cols)) data)
          (varFromOffset BranchChip.Inputs 0).is_real =
        (branchChipInput cols).is_real := by
    rw [← BranchChip.eval_inputIsReal]
    exact congrArg (fun value => value.is_real)
      (eval_inputFirstRow (branchChipInput cols)
        (branchChipLocals cols) data)
  have h0 := eval_branchChipPrefixLocal
    (p := p) cols data 0 (by decide)
  have h1 := eval_branchChipPrefixLocal
    (p := p) cols data 1 (by decide)
  have h2 := eval_branchChipPrefixLocal
    (p := p) cols data 2 (by decide)
  have h3 := eval_branchChipPrefixLocal
    (p := p) cols data 3 (by decide)
  have h4 := eval_branchChipPrefixLocal
    (p := p) cols data 4 (by decide)
  have h5 := eval_branchChipPrefixLocal
    (p := p) cols data 5 (by decide)
  change
    Expression.eval assignment.environment
        (varFromOffset BranchChip.Inputs 0).is_real =
      assignment.environment.get (size BranchChip.Inputs) +
          assignment.environment.get (size BranchChip.Inputs + 1) +
        assignment.environment.get (size BranchChip.Inputs + 2) +
        assignment.environment.get (size BranchChip.Inputs + 3) +
        assignment.environment.get (size BranchChip.Inputs + 4) +
        assignment.environment.get (size BranchChip.Inputs + 5)
  rw [show assignment.environment =
      Environment.fromArray
        (inputFirstRow (branchChipInput cols)
          (branchChipLocals cols)) data by rfl]
  rw [branchChipPrefix_zero] at h0
  rw [branchChipPrefix_one] at h1
  rw [branchChipPrefix_two] at h2
  rw [branchChipPrefix_three] at h3
  rw [branchChipPrefix_four] at h4
  rw [branchChipPrefix_five] at h5
  rw [branchChipInput_isReal] at hInput
  simp only [Expression.eval] at h0 h1 h2 h3 h4 h5
  have h01 := congrArg₂ (· + ·) h0 h1
  have h012 := congrArg₂ (· + ·) h01 h2
  have h0123 := congrArg₂ (· + ·) h012 h3
  have h01234 := congrArg₂ (· + ·) h0123 h4
  have h012345 := congrArg₂ (· + ·) h01234 h5
  simpa only [Nat.add_zero] using hInput.trans h012345.symm

theorem branchChip_constraints_constructive
    (rustCols : Extracted.BranchOracle.BranchColumns (ZMod p))
    (data : ProverData (ZMod p)) :
    let assignment := branchChipRowCodec.assignment
      (branchChipOracle.deconfigure rustCols) data
    List.Forall (· = 0) (branchChipOracle.assertZeros rustCols) ↔
      (⟨BranchChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).operations.ConstraintsHold
          assignment.environment := by
  dsimp only
  let cols := branchChipOracle.deconfigure rustCols
  let assignment := branchChipRowCodec.assignment cols data
  have hbind : BindsChipOutput BranchChip.main assignment.environment
      (⟨BranchChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).rowInputVar
      (⟨BranchChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [BranchChip.circuit_main_eq] at h
    exact h
  have hinputReal :
      Expression.eval assignment.environment
          (⟨BranchChip.circuit (p := p)⟩ :
            Air.Flat.Component (ZMod p)).rowInputVar.is_real =
        Expression.eval assignment.environment
          (branchSum
            (⟨BranchChip.circuit (p := p)⟩ :
              Air.Flat.Component (ZMod p)).rowOffset) :=
    branchChipRowCodec_inputReal (p := p) cols data
  have hlegacy := branchChip_constraints_faithful (p := p)
    assignment.environment
    (⟨BranchChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowInputVar
    (⟨BranchChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind hinputReal
  have hassertions :
      List.Forall (· = 0) (branchChipOracle.assertZeros rustCols) ↔
        List.Forall (· = 0)
          (nativeAssertZeros assignment.environment
            (⟨BranchChip.circuit (p := p)⟩ :
              Air.Flat.Component (ZMod p)).rowOperations) := by
    simpa only [cols, ChipOracle.nativeAssertZeros_deconfigure,
      Air.Flat.Component.rowOperations_mk,
      Air.Flat.Component.rowInputVar_mk,
      Air.Flat.Component.rowOffset_mk,
      BranchChip.circuit_main_eq] using hlegacy
  exact hassertions.trans
    (constraintsHold_iff_nativeAssertZeros
      (BranchChip.circuit (p := p))
      assignment.environment branchChip_lookups_empty).symm

open SP1Clean.Channels
  (stateChannel byteChannel memoryChannel programChannel)
open InteractionRecovery

private theorem ltSigned_interactions_exact
    (env : Environment (ZMod p))
    (input : Var LtOperationSigned.Inputs (ZMod p)) (offset : ℕ) :
    (((LtOperationSigned.main input).operations offset).interactionsWith
        byteChannel.toRaw).map (AbstractInteraction.toAccess env) =
      (Extracted.LtOperationSigned.interactions
          (Eval.eval env input.b) (Eval.eval env input.cc)
          (Eval.eval env input.cols)
          (Expression.eval env input.is_signed)
          (Expression.eval env input.is_real)).map
        Extracted.Interaction.toAccess := by
  let signedCols := Eval.eval env input.cols
  let firstInput : Var U16MSBOperation.Inputs (ZMod p) :=
    ⟨input.b[3], { msb := input.cols.b_msb.msb }, input.is_signed⟩
  let secondInput : Var U16MSBOperation.Inputs (ZMod p) :=
    ⟨input.cc[3], { msb := input.cols.c_msb.msb }, input.is_signed⟩
  let unsignedCols : Extracted.LtOperationUnsigned (ZMod p) :=
    { u16_compare_operation :=
        { bit := signedCols.result.u16_compare_operation.bit }
      u16_flags :=
        #v[signedCols.result.u16_flags[0],
          signedCols.result.u16_flags[1],
          signedCols.result.u16_flags[2],
          signedCols.result.u16_flags[3]]
      not_eq_inv := signedCols.result.not_eq_inv
      comparison_limbs :=
        #v[signedCols.result.comparison_limbs[0],
          signedCols.result.comparison_limbs[1]] }
  let unsignedInput : Var LtOperationUnsigned.Inputs (ZMod p) :=
    ⟨#v[input.b[0], input.b[1], input.b[2],
          input.b[3] + input.is_signed * 32768 -
            65536 * input.cols.b_msb.msb],
      #v[input.cc[0], input.cc[1], input.cc[2],
          input.cc[3] + input.is_signed * 32768 -
            65536 * input.cols.c_msb.msb],
      { u16_compare_operation :=
          { bit := input.cols.result.u16_compare_operation.bit }
        u16_flags :=
          #v[input.cols.result.u16_flags[0],
            input.cols.result.u16_flags[1],
            input.cols.result.u16_flags[2],
            input.cols.result.u16_flags[3]]
        not_eq_inv := input.cols.result.not_eq_inv
        comparison_limbs :=
          #v[input.cols.result.comparison_limbs[0],
            input.cols.result.comparison_limbs[1]] },
      input.is_real⟩
  have hb3 :
      Expression.eval env input.b[3] = (Eval.eval env input.b)[3] :=
    ProvableType.getElem_eval_fields env input.b 3 (by decide)
  have hc3 :
      Expression.eval env input.cc[3] = (Eval.eval env input.cc)[3] :=
    ProvableType.getElem_eval_fields env input.cc 3 (by decide)
  have hbmsb :
      Expression.eval env input.cols.b_msb.msb = signedCols.b_msb.msb := by
    simp only [signedCols, eval_ltSignedColumns, eval_u16MSBColumns,
      CircuitType.eval_expr]
  have hcmsb :
      Expression.eval env input.cols.c_msb.msb = signedCols.c_msb.msb := by
    simp only [signedCols, eval_ltSignedColumns, eval_u16MSBColumns,
      CircuitType.eval_expr]
  have hFirst := u16msb_interactions_faithful_syntactic
    (p := p) env firstInput offset
    (Eval.eval env input.b)[3] signedCols.b_msb.msb
    (Expression.eval env input.is_signed) rfl hb3 hbmsb
  have hSecond := u16msb_interactions_faithful_syntactic
    (p := p) env secondInput offset
    (Eval.eval env input.cc)[3] signedCols.c_msb.msb
    (Expression.eval env input.is_signed) rfl hc3 hcmsb
  have hcl0 :
      Expression.eval env unsignedInput.cols.comparison_limbs[0] =
        unsignedCols.comparison_limbs[0] := by
    simp only [unsignedInput, unsignedCols, signedCols,
      eval_ltSignedColumns, eval_ltUnsignedColumns,
      ← ProvableType.getElem_eval_fields, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero]
  have hcl1 :
      Expression.eval env unsignedInput.cols.comparison_limbs[1] =
        unsignedCols.comparison_limbs[1] := by
    simp only [unsignedInput, unsignedCols, signedCols,
      eval_ltSignedColumns, eval_ltUnsignedColumns,
      ← ProvableType.getElem_eval_fields, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_succ,
      List.getElem_cons_zero]
  have hbit :
      Expression.eval env unsignedInput.cols.u16_compare_operation.bit =
        unsignedCols.u16_compare_operation.bit := by
    simp only [unsignedInput, unsignedCols, signedCols,
      eval_ltSignedColumns, eval_ltUnsignedColumns,
      eval_u16CompareColumns, CircuitType.eval_expr]
  have hUnsigned := ltUnsigned_interactions_faithful_syntactic
    (p := p) env unsignedInput offset
    (Eval.eval env unsignedInput.b) (Eval.eval env unsignedInput.cc)
    unsignedCols (Expression.eval env input.is_real)
    rfl hcl0 hcl1 hbit
  rw [LtOperationSigned.interactionsWith_byte_eq]
  simp only [List.map_append]
  rw [← hFirst, ← hSecond, ← hUnsigned]
  simp [Extracted.LtOperationSigned.interactions,
    Extracted.U16MSBOperation.interactions,
    Extracted.LtOperationUnsigned.interactions,
    Extracted.U16CompareOperation.interactions,
    unsignedCols, signedCols, eval_ltSignedColumns,
    eval_ltUnsignedColumns, eval_u16CompareColumns,
    eval_u16MSBColumns, ← ProvableType.getElem_eval_fields]

private def branchStateInteractions
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (stateChannel (p := p))) :=
  Readers.CPUState.stateInteractions (branchCpuInput input offset)

private def branchProgramInteractions
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (programChannel (p := p))) :=
  [ programChannel.pulledIf input.is_real
      ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2],
        branchOpcode offset, input.adapter.op_a,
        #v[input.adapter.op_b, 0, 0, 0],
        input.adapter.op_c_imm, input.adapter.op_a_0, 0, 1⟩ ]

private def branchTailByteInteractions
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  [ byteChannel.pulledIf input.is_real
      ⟨6, (var { index := offset + 7 } :
        Expression (ZMod p)) * (4 : ZMod p)⁻¹, 14, 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨6, var { index := offset + 8 }, 16, 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨6, var { index := offset + 9 }, 16, 0⟩ ]

private theorem branchStateInteractions_eq
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) :
    ((BranchChip.main input).operations offset).interactionsWith
        stateChannel.toRaw =
      (branchStateInteractions input offset).map
        ChannelInteraction.toRaw := by
  exact (BranchChip.circuit (p := p)).interactionsWith_eq_of_mem_exposedChannels
    input offset
    ⟨stateChannel.toRaw,
      (branchStateInteractions input offset).map
        ChannelInteraction.toRaw⟩
    (by
      simp only [BranchChip.circuit, BranchChip.stateExposure,
        List.mem_append]
      apply Or.inl
      simp [Readers.CPUState.exposedState, branchStateInteractions,
        branchCpuInput, branchNextPc, expose])

private theorem branchProgramInteractions_eq
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) :
    ((BranchChip.main input).operations offset).interactionsWith
        programChannel.toRaw =
      (branchProgramInteractions input offset).map
        ChannelInteraction.toRaw := by
  exact (BranchChip.circuit (p := p)).interactionsWith_eq_of_mem_exposedChannels
    input offset
    ⟨programChannel.toRaw,
      (branchProgramInteractions input offset).map
        ChannelInteraction.toRaw⟩
    (by
      simp [BranchChip.circuit, BranchChip.stateExposure,
        branchProgramInteractions, BranchChip.exposedOpcode,
        branchOpcode, branchFlag, expose])

private theorem branchLtByteInteractions_subcircuit
    (input : Var LtOperationSigned.Inputs (ZMod p))
    (offset : ℕ) (ops : Operations (ZMod p)) :
    Operations.interactionsWith byteChannel.toRaw
        (.subcircuit
          ((LtOperationSigned.circuit (p := p)).toSubcircuit
            offset input) :: ops) =
      ((LtOperationSigned.main input).operations offset).interactionsWith
          byteChannel.toRaw ++
        Operations.interactionsWith byteChannel.toRaw ops :=
  InteractionRecovery.interactionsWith_assertionSubcircuit_of_main_exact
    LtOperationSigned.circuit byteChannel.toRaw input offset ops _ rfl

private theorem branchCpuByteInteractions_subcircuit
    (input : Var Readers.CPUState.Inputs (ZMod p))
    (offset : ℕ) (ops : Operations (ZMod p)) :
    Operations.interactionsWith byteChannel.toRaw
        (.subcircuit
          ((Readers.CPUState.circuit (p := p)).toSubcircuit
            offset input) :: ops) =
      ((Readers.CPUState.main input).operations offset).interactionsWith
          byteChannel.toRaw ++
        Operations.interactionsWith byteChannel.toRaw ops :=
  InteractionRecovery.interactionsWith_generalSubcircuit_of_main_exact_list
    Readers.CPUState.circuit byteChannel.toRaw input offset ops _ rfl

private theorem branchITypeByteInteractions_subcircuit
    (input : Var Readers.ITypeReaderImmutable.Inputs (ZMod p))
    (offset : ℕ) (ops : Operations (ZMod p)) :
    Operations.interactionsWith byteChannel.toRaw
        (.subcircuit
          ((Readers.ITypeReaderImmutable.circuit (p := p)).toSubcircuit
            offset input) :: ops) =
      ((Readers.ITypeReaderImmutable.main input).operations offset).interactionsWith
          byteChannel.toRaw ++
        Operations.interactionsWith byteChannel.toRaw ops :=
  InteractionRecovery.interactionsWith_generalSubcircuit_of_main_exact_list
    Readers.ITypeReaderImmutable.circuit byteChannel.toRaw
    input offset ops _ rfl

private theorem branchByteInteractions_decompose
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) :
    ((BranchChip.main input).operations offset).interactionsWith
        byteChannel.toRaw =
      ((LtOperationSigned.main
        (branchLtInput input offset)).operations
          (offset + 20)).interactionsWith byteChannel.toRaw ++
      ((Readers.CPUState.main
        (branchCpuInput input offset)).operations
          (offset + 20)).interactionsWith byteChannel.toRaw ++
      ((Readers.ITypeReaderImmutable.main
        (branchITypeInput input offset)).operations
          (offset + 20)).interactionsWith byteChannel.toRaw ++
      (branchTailByteInteractions input offset).map
        ChannelInteraction.toRaw := by
  have hLtSize : size Extracted.LtOperationSigned = 10 := rfl
  have heq := fun (n : ℕ)
      (inp : Var (ProvablePair field field) (ZMod p))
      (ops : Operations (ZMod p)) =>
    @InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil
      (ZMod p) _ (ProvablePair field field) ProvablePair.instance
      (Gadgets.Equality.circuit field) byteChannel.toRaw n inp ops
      List.not_mem_nil List.not_mem_nil
  simp only [BranchChip.main, Circuit.operations,
    Circuit.bind_def, Circuit.pure_def,
    witnessVectorIR, witnessField, Witnessable.witness, witnessIR,
    subcircuitWithAssertion, assertion, assertZero,
    HasAssertEq.assert_eq, Expression.assertEquals,
    Channel.pullIf, Operations.localLength]
  simp only [Operations.interactionsWith_append,
    Operations.interactionsWith_witness,
    branchLtByteInteractions_subcircuit,
    branchCpuByteInteractions_subcircuit,
    branchITypeByteInteractions_subcircuit,
    heq,
    Operations.interactionsWith_assert,
    Operations.interactionsWith_interact,
    Operations.interactionsWith_nil,
    GeneralFormalCircuit.toSubcircuit_localLength,
    FormalAssertion.toSubcircuit_localLength,
    LtOperationSigned.circuit_localLength,
    Readers.CPUState.circuit_localLength,
    Gadgets.Equality.localLength_eq,
    ChannelInteraction.toRaw_channel,
    List.nil_append]
  simp only [branchLtInput, branchCpuInput, branchITypeInput,
    branchTailByteInteractions, branchFlag, branchNextPc,
    branchCompare, branchOpcode,
    hLtSize, Nat.add_zero, Nat.add_assoc,
    Nat.reduceAdd,
    List.map_cons, List.map_nil, List.append_assoc]
  simp only [if_true, List.nil_append, List.append_nil,
    Circuit.operations, ProvableType.varFromOffset_fields,
    Vector.getElem_mapRange, Nat.add_zero, Nat.add_assoc,
    Nat.reduceAdd, Nat.cast_ofNat,
    Channel.pulledIf, pulledIf, ChannelInteraction.toRaw,
    List.cons_append]
  rfl

private def branchRustAccesses
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) :
    LookupAccessList :=
  (Extracted.BranchOracle.BranchColumns.interactions
    (branchChipReconfigure (branchChipRustColumns env input offset))).map
      Extracted.Interaction.toAccess

private def branchCpuRustAccesses
    (cols : BranchChip.Columns (ZMod p)) : LookupAccessList :=
  (Extracted.CPUState.interactions cols.state cols.next_pc 8
    (cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge +
      cols.is_bltu + cols.is_bgeu)).map
        Extracted.Interaction.toAccess

private def branchITypeRustAccesses
    (cols : BranchChip.Columns (ZMod p)) : LookupAccessList :=
  (Extracted.ITypeReaderImmutable.interactions cols.state.clk_high
    (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
    cols.state.pc
    (cols.is_beq * 40 + cols.is_bne * 41 + cols.is_blt * 42 +
      cols.is_bge * 43 + cols.is_bltu * 44 + cols.is_bgeu * 45)
    cols.adapter
    (cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge +
      cols.is_bltu + cols.is_bgeu)
    (cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge +
      cols.is_bltu + cols.is_bgeu)).map
        Extracted.Interaction.toAccess

private def branchLtRustAccesses
    (cols : BranchChip.Columns (ZMod p)) : LookupAccessList :=
  (Extracted.LtOperationSigned.interactions
    cols.adapter.op_a_memory.prev_value
    cols.adapter.op_b_memory.prev_value
    cols.compare_operation (cols.is_blt + cols.is_bge)
    (cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge +
      cols.is_bltu + cols.is_bgeu)).map
        Extracted.Interaction.toAccess

private def branchTailRustAccesses
    (cols : BranchChip.Columns (ZMod p)) : LookupAccessList :=
  (branchRustInteractionTail cols).map
    Extracted.Interaction.toAccess

omit [Fact (2 ^ 17 < p)] in
private theorem branchRustAccesses_decompose
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) :
    branchRustAccesses env input offset =
      branchCpuRustAccesses (branchChipRustColumns env input offset) ++
      branchITypeRustAccesses (branchChipRustColumns env input offset) ++
      branchLtRustAccesses (branchChipRustColumns env input offset) ++
      branchTailRustAccesses (branchChipRustColumns env input offset) := by
  unfold branchRustAccesses
  rw [branchColumns_interactions_decompose]
  simp only [List.map_append, branchCpuRustAccesses,
    branchITypeRustAccesses, branchLtRustAccesses,
    branchTailRustAccesses]

omit [Fact (2 ^ 17 < p)] in
private theorem branchITypeRustAccesses_noState
    (cols : BranchChip.Columns (ZMod p)) :
    (branchITypeRustAccesses cols).filter
        (fun access => access.1 = InteractionKind.State) = [] := by
  simp [branchITypeRustAccesses,
    Extracted.ITypeReaderImmutable.interactions,
    Extracted.Interaction.toAccess]

omit [Fact (2 ^ 17 < p)] in
private theorem branchLtRustAccesses_noState
    (cols : BranchChip.Columns (ZMod p)) :
    (branchLtRustAccesses cols).filter
        (fun access => access.1 = InteractionKind.State) = [] := by
  simp [branchLtRustAccesses,
    Extracted.LtOperationSigned.interactions,
    Extracted.U16MSBOperation.interactions,
    Extracted.LtOperationUnsigned.interactions,
    Extracted.U16CompareOperation.interactions,
    Extracted.Interaction.toAccess]

omit [Fact (2 ^ 17 < p)] in
private theorem branchTailRustAccesses_noState
    (cols : BranchChip.Columns (ZMod p)) :
    (branchTailRustAccesses cols).filter
        (fun access => access.1 = InteractionKind.State) = [] := by
  simp [branchTailRustAccesses, branchRustInteractionTail,
    Extracted.Interaction.toAccess]

omit [Fact (2 ^ 17 < p)] in
private theorem branchRustColumns_state
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) :
    (branchChipRustColumns env input offset).state =
      Eval.eval env input.state := rfl

omit [Fact (2 ^ 17 < p)] in
private theorem branchRustColumns_nextPc
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) :
    (branchChipRustColumns env input offset).next_pc =
      Eval.eval env (branchNextPc (p := p) offset) := by
  simp only [branchChipRustColumns]
  rw [branchNextPcMap_eq]

omit [Fact (2 ^ 17 < p)] in
private theorem branchRustColumns_sum
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) :
    let cols := branchChipRustColumns env input offset
    cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge +
        cols.is_bltu + cols.is_bgeu =
      Expression.eval env (branchSum offset) := by
  simp only [branchChipRustColumns, branchSum, branchFlag,
    Expression.eval]

omit [Fact (2 ^ 17 < p)] in
private theorem branchRustColumns_adapter
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) :
    (branchChipRustColumns env input offset).adapter =
      Eval.eval env input.adapter := rfl

omit [Fact (2 ^ 17 < p)] in
private theorem branchRustColumns_opcode
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) :
    let cols := branchChipRustColumns env input offset
    cols.is_beq * 40 + cols.is_bne * 41 + cols.is_blt * 42 +
          cols.is_bge * 43 + cols.is_bltu * 44 + cols.is_bgeu * 45 =
      Expression.eval env (branchOpcode offset) := by
  simp only [branchChipRustColumns, branchOpcode, branchFlag,
    Expression.eval]

private theorem branchStateInteractions_faithful
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (branchSum (p := p) offset)) :
    (((branchStateInteractions input offset).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env)) =
      ((branchRustAccesses env input offset).filter
        (fun access => access.1 = InteractionKind.State)) := by
  let cpuInput := branchCpuInput input offset
  have hCpu := cpustate_state_interactions_faithful_syntactic
    (p := p) env cpuInput
    (Eval.eval env input.state)
    (Eval.eval env (branchNextPc (p := p) offset))
    8 (Expression.eval env (branchSum offset))
    (by simpa only [cpuInput, branchCpuInput,
      ProvableStruct.structEvalLiteralProc] using hinputReal)
    (by simp only [cpuInput, branchCpuInput, eval_cpuState,
      ProvableType.eval_field])
    (by simp only [cpuInput, branchCpuInput, eval_cpuState,
      ProvableType.eval_field])
    (by simp only [cpuInput, branchCpuInput, eval_cpuState,
      ProvableType.eval_field])
    (by
      simp only [cpuInput, branchCpuInput, eval_cpuState]
      exact ProvableType.getElem_eval_fields env input.state.pc 0
        (by decide))
    (by
      simp only [cpuInput, branchCpuInput, eval_cpuState]
      exact ProvableType.getElem_eval_fields env input.state.pc 1
        (by decide))
    (by
      simp only [cpuInput, branchCpuInput, eval_cpuState]
      exact ProvableType.getElem_eval_fields env input.state.pc 2
        (by decide))
    (by
      simp only [cpuInput, branchCpuInput]
      exact ProvableType.getElem_eval_fields env
        (branchNextPc (p := p) offset) 0 (by decide))
    (by
      simp only [cpuInput, branchCpuInput]
      exact ProvableType.getElem_eval_fields env
        (branchNextPc (p := p) offset) 1 (by decide))
    (by
      simp only [cpuInput, branchCpuInput]
      exact ProvableType.getElem_eval_fields env
        (branchNextPc (p := p) offset) 2 (by decide))
    rfl
  rw [branchRustAccesses_decompose, List.filter_append,
    List.filter_append, List.filter_append,
    branchITypeRustAccesses_noState,
    branchLtRustAccesses_noState,
    branchTailRustAccesses_noState]
  simp only [List.append_nil]
  rw [branchCpuRustAccesses, branchRustColumns_state,
    branchRustColumns_nextPc, branchRustColumns_sum]
  simpa only [cpuInput, branchStateInteractions] using hCpu

omit [Fact (2 ^ 17 < p)] in
private theorem branchCpuRustAccesses_noMemory
    (cols : BranchChip.Columns (ZMod p)) :
    (branchCpuRustAccesses cols).filter
        (fun access => access.1 = InteractionKind.Memory) = [] := by
  simp [branchCpuRustAccesses, Extracted.CPUState.interactions,
    Extracted.Interaction.toAccess]

omit [Fact (2 ^ 17 < p)] in
private theorem branchLtRustAccesses_noMemory
    (cols : BranchChip.Columns (ZMod p)) :
    (branchLtRustAccesses cols).filter
        (fun access => access.1 = InteractionKind.Memory) = [] := by
  simp [branchLtRustAccesses,
    Extracted.LtOperationSigned.interactions,
    Extracted.U16MSBOperation.interactions,
    Extracted.LtOperationUnsigned.interactions,
    Extracted.U16CompareOperation.interactions,
    Extracted.Interaction.toAccess]

omit [Fact (2 ^ 17 < p)] in
private theorem branchTailRustAccesses_noMemory
    (cols : BranchChip.Columns (ZMod p)) :
    (branchTailRustAccesses cols).filter
        (fun access => access.1 = InteractionKind.Memory) = [] := by
  simp [branchTailRustAccesses, branchRustInteractionTail,
    Extracted.Interaction.toAccess]

private theorem branchITypeMemory_faithful
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (branchSum (p := p) offset)) :
    (((((Readers.ITypeReaderImmutable.main
          (branchITypeInput input offset)).operations
            (offset + 20)).interactionsWith memoryChannel.toRaw).map
              (AbstractInteraction.toAccess env)).map
                LookupAccessList.negMult) =
      (branchITypeRustAccesses
        (branchChipRustColumns env input offset)).filter
          (fun access => access.1 = InteractionKind.Memory) := by
  let readerInput := branchITypeInput input offset
  let rustAdapter := Eval.eval env input.adapter
  have hReader :=
    itypereaderimmutable_memory_interactions_faithful_syntactic
      (p := p) env readerInput (offset + 20)
      (Expression.eval env input.state.clk_high)
      (Expression.eval env
        (input.state.clk_0_16 +
          input.state.clk_16_24 * 65536))
      (Eval.eval env input.state.pc)
      (Expression.eval env (branchOpcode offset))
      rustAdapter
      (Expression.eval env (branchSum offset))
      (Expression.eval env (branchSum offset))
      (by simpa only [readerInput, branchITypeInput,
        ProvableStruct.structEvalLiteralProc] using hinputReal)
      (by rfl)
      (by rfl)
      (by simp only [readerInput, branchITypeInput, rustAdapter,
        Readers.ITypeReader.eval_cols, ProvableType.eval_field])
      (by simp only [readerInput, branchITypeInput, rustAdapter,
        Readers.ITypeReader.eval_cols, ProvableType.eval_field])
      (by simp only [readerInput, branchITypeInput, rustAdapter,
        Readers.ITypeReader.eval_cols, eval_registerAccessCols,
        eval_registerAccessTimestamp, ProvableType.eval_field])
      (by simp only [readerInput, branchITypeInput, rustAdapter,
        Readers.ITypeReader.eval_cols, eval_registerAccessCols,
        ← ProvableType.getElem_eval_fields])
      (by simp only [readerInput, branchITypeInput, rustAdapter,
        Readers.ITypeReader.eval_cols, eval_registerAccessCols,
        ← ProvableType.getElem_eval_fields])
      (by simp only [readerInput, branchITypeInput, rustAdapter,
        Readers.ITypeReader.eval_cols, eval_registerAccessCols,
        ← ProvableType.getElem_eval_fields])
      (by simp only [readerInput, branchITypeInput, rustAdapter,
        Readers.ITypeReader.eval_cols, eval_registerAccessCols,
        ← ProvableType.getElem_eval_fields])
      (by simp only [readerInput, branchITypeInput, rustAdapter,
        Readers.ITypeReader.eval_cols, eval_registerAccessCols,
        eval_registerAccessTimestamp, ProvableType.eval_field])
      (by simp only [readerInput, branchITypeInput, rustAdapter,
        Readers.ITypeReader.eval_cols, eval_registerAccessCols,
        ← ProvableType.getElem_eval_fields])
      (by simp only [readerInput, branchITypeInput, rustAdapter,
        Readers.ITypeReader.eval_cols, eval_registerAccessCols,
        ← ProvableType.getElem_eval_fields])
      (by simp only [readerInput, branchITypeInput, rustAdapter,
        Readers.ITypeReader.eval_cols, eval_registerAccessCols,
        ← ProvableType.getElem_eval_fields])
      (by simp only [readerInput, branchITypeInput, rustAdapter,
        Readers.ITypeReader.eval_cols, eval_registerAccessCols,
        ← ProvableType.getElem_eval_fields])
  have hClkLow :
      Expression.eval env
          (input.state.clk_0_16 +
            input.state.clk_16_24 * 65536) =
        Expression.eval env input.state.clk_0_16 +
          Expression.eval env input.state.clk_16_24 * 65536 := rfl
  rw [hClkLow] at hReader
  rw [branchITypeRustAccesses, branchRustColumns_state,
    branchRustColumns_adapter, branchRustColumns_opcode,
    branchRustColumns_sum]
  rw [show branchITypeInput input offset = readerInput by rfl]
  simp only [eval_cpuState, ProvableType.eval_field]
  rw [hReader, LookupAccessList.map_negMult_negMult]

private theorem branchMemoryInteractions_faithful
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (branchSum (p := p) offset)) :
    (((((BranchChip.exposedMemoryInteractions input offset).map
          ChannelInteraction.toRaw).map
            (AbstractInteraction.toAccess env)).map
              LookupAccessList.negMult)) =
      (branchRustAccesses env input offset).filter
        (fun access => access.1 = InteractionKind.Memory) := by
  let readerInput := branchITypeInput input offset
  have hReader :=
    Soundness.iTypeReaderImmutable_memoryInteractions
      (p := p) readerInput (offset + 20)
  change
    ((Readers.ITypeReaderImmutable.main readerInput).operations
        (offset + 20)).interactionsWith memoryChannel.toRaw =
      Soundness.iTypeImmutableMemoryInteractions readerInput at hReader
  have hExposure :
      Soundness.iTypeImmutableMemoryInteractions readerInput =
        (BranchChip.exposedMemoryInteractions input offset).map
          ChannelInteraction.toRaw := by
    simp [readerInput, branchITypeInput,
      Soundness.iTypeImmutableMemoryInteractions,
      BranchChip.exposedMemoryInteractions]
  rw [branchRustAccesses_decompose, List.filter_append,
    List.filter_append, List.filter_append,
    branchCpuRustAccesses_noMemory,
    branchLtRustAccesses_noMemory,
    branchTailRustAccesses_noMemory]
  simp only [List.nil_append, List.append_nil]
  rw [← branchITypeMemory_faithful env input offset hinputReal]
  apply congrArg (List.map LookupAccessList.negMult)
  apply congrArg (List.map (AbstractInteraction.toAccess env))
  exact (hReader.trans hExposure).symm

omit [Fact (2 ^ 17 < p)] in
private theorem branchCpuRustAccesses_noProgram
    (cols : BranchChip.Columns (ZMod p)) :
    (branchCpuRustAccesses cols).filter
        (fun access => access.1 = InteractionKind.Program) = [] := by
  simp [branchCpuRustAccesses, Extracted.CPUState.interactions,
    Extracted.Interaction.toAccess]

omit [Fact (2 ^ 17 < p)] in
private theorem branchLtRustAccesses_noProgram
    (cols : BranchChip.Columns (ZMod p)) :
    (branchLtRustAccesses cols).filter
        (fun access => access.1 = InteractionKind.Program) = [] := by
  simp [branchLtRustAccesses,
    Extracted.LtOperationSigned.interactions,
    Extracted.U16MSBOperation.interactions,
    Extracted.LtOperationUnsigned.interactions,
    Extracted.U16CompareOperation.interactions,
    Extracted.Interaction.toAccess]

omit [Fact (2 ^ 17 < p)] in
private theorem branchTailRustAccesses_noProgram
    (cols : BranchChip.Columns (ZMod p)) :
    (branchTailRustAccesses cols).filter
        (fun access => access.1 = InteractionKind.Program) = [] := by
  simp [branchTailRustAccesses, branchRustInteractionTail,
    Extracted.Interaction.toAccess]

private theorem branchITypeProgram_faithful
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (branchSum (p := p) offset)) :
    (((((Readers.ITypeReaderImmutable.main
          (branchITypeInput input offset)).operations
            (offset + 20)).interactionsWith programChannel.toRaw).map
              (AbstractInteraction.toAccess env)).map
                LookupAccessList.negMult) =
      (branchITypeRustAccesses
        (branchChipRustColumns env input offset)).filter
          (fun access => access.1 = InteractionKind.Program) := by
  let readerInput := branchITypeInput input offset
  let rustAdapter := Eval.eval env input.adapter
  have hReader :=
    itypereaderimmutable_program_interactions_faithful_syntactic
      (p := p) env readerInput (offset + 20)
      (Expression.eval env input.state.clk_high)
      (Expression.eval env
        (input.state.clk_0_16 +
          input.state.clk_16_24 * 65536))
      (Eval.eval env input.state.pc)
      (Expression.eval env (branchOpcode offset))
      rustAdapter
      (Expression.eval env (branchSum offset))
      (Expression.eval env (branchSum offset))
      (by simpa only [readerInput, branchITypeInput,
        ProvableStruct.structEvalLiteralProc] using hinputReal)
      (by
        simp only [readerInput, branchITypeInput]
        exact ProvableType.getElem_eval_fields env input.state.pc 0
          (by decide))
      (by
        simp only [readerInput, branchITypeInput]
        exact ProvableType.getElem_eval_fields env input.state.pc 1
          (by decide))
      (by
        simp only [readerInput, branchITypeInput]
        exact ProvableType.getElem_eval_fields env input.state.pc 2
          (by decide))
      rfl
      (by simp only [readerInput, branchITypeInput, rustAdapter,
        Readers.ITypeReader.eval_cols, ProvableType.eval_field])
      (by simp only [readerInput, branchITypeInput, rustAdapter,
        Readers.ITypeReader.eval_cols, ProvableType.eval_field])
      (by simp only [readerInput, branchITypeInput, rustAdapter,
        Readers.ITypeReader.eval_cols, ProvableType.eval_field])
      (by simp only [readerInput, branchITypeInput, rustAdapter,
        Readers.ITypeReader.eval_cols,
        ← ProvableType.getElem_eval_fields])
      (by simp only [readerInput, branchITypeInput, rustAdapter,
        Readers.ITypeReader.eval_cols,
        ← ProvableType.getElem_eval_fields])
      (by simp only [readerInput, branchITypeInput, rustAdapter,
        Readers.ITypeReader.eval_cols,
        ← ProvableType.getElem_eval_fields])
      (by simp only [readerInput, branchITypeInput, rustAdapter,
        Readers.ITypeReader.eval_cols,
        ← ProvableType.getElem_eval_fields])
  have hClkLow :
      Expression.eval env
          (input.state.clk_0_16 +
            input.state.clk_16_24 * 65536) =
        Expression.eval env input.state.clk_0_16 +
          Expression.eval env input.state.clk_16_24 * 65536 := rfl
  rw [hClkLow] at hReader
  rw [branchITypeRustAccesses, branchRustColumns_state,
    branchRustColumns_adapter, branchRustColumns_opcode,
    branchRustColumns_sum]
  rw [show branchITypeInput input offset = readerInput by rfl]
  simp only [eval_cpuState, ProvableType.eval_field]
  rw [hReader, LookupAccessList.map_negMult_negMult]

private theorem branchProgramInteractions_faithful
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (branchSum (p := p) offset)) :
    (((((branchProgramInteractions input offset).map
          ChannelInteraction.toRaw).map
            (AbstractInteraction.toAccess env)).map
              LookupAccessList.negMult)) =
      (branchRustAccesses env input offset).filter
        (fun access => access.1 = InteractionKind.Program) := by
  let readerInput := branchITypeInput input offset
  have hReader :=
    Soundness.iTypeReaderImmutable_programInteractions
      (p := p) readerInput (offset + 20)
  change
    ((Readers.ITypeReaderImmutable.main readerInput).operations
        (offset + 20)).interactionsWith programChannel.toRaw =
      [(programChannel.pulledIf readerInput.is_trusted
        (Soundness.iTypeImmutableProgramMessage readerInput)).toRaw]
      at hReader
  have hExposure :
      [(programChannel.pulledIf readerInput.is_trusted
        (Soundness.iTypeImmutableProgramMessage readerInput)).toRaw] =
        (branchProgramInteractions input offset).map
          ChannelInteraction.toRaw := by
    simp [readerInput, branchITypeInput,
      Soundness.iTypeImmutableProgramMessage,
      branchProgramInteractions, branchOpcode]
  rw [branchRustAccesses_decompose, List.filter_append,
    List.filter_append, List.filter_append,
    branchCpuRustAccesses_noProgram,
    branchLtRustAccesses_noProgram,
    branchTailRustAccesses_noProgram]
  simp only [List.nil_append, List.append_nil]
  rw [← branchITypeProgram_faithful env input offset hinputReal]
  apply congrArg (List.map LookupAccessList.negMult)
  apply congrArg (List.map (AbstractInteraction.toAccess env))
  exact (hReader.trans hExposure).symm

omit [Fact (2 ^ 17 < p)] in
private theorem branchRustColumns_compare
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) :
    (branchChipRustColumns env input offset).compare_operation =
      Eval.eval env (branchCompare (p := p) offset) := rfl

omit [Fact (2 ^ 17 < p)] in
private theorem branchRustColumns_signed
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) :
    let cols := branchChipRustColumns env input offset
    cols.is_blt + cols.is_bge =
      Expression.eval env
        (branchFlag offset 2 + branchFlag offset 3) := by
  simp only [branchChipRustColumns, branchFlag,
    Expression.eval]

private theorem branchCpuByte_faithful
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (branchSum (p := p) offset)) :
    (((Readers.CPUState.main
        (branchCpuInput input offset)).operations
          (offset + 20)).interactionsWith byteChannel.toRaw).map
            (AbstractInteraction.toAccess env) =
      (branchCpuRustAccesses
        (branchChipRustColumns env input offset)).filter
          (fun access => access.1 = InteractionKind.Byte) := by
  let cpuInput := branchCpuInput input offset
  have hCpu := cpustate_byte_interactions_faithful_syntactic
    (p := p) env cpuInput (offset + 20)
    (Eval.eval env input.state)
    (Eval.eval env (branchNextPc (p := p) offset))
    8 (Expression.eval env (branchSum offset))
    (by simpa only [cpuInput, branchCpuInput,
      ProvableStruct.structEvalLiteralProc] using hinputReal)
    (by simp only [cpuInput, branchCpuInput, eval_cpuState,
      ProvableType.eval_field])
    (by simp only [cpuInput, branchCpuInput, eval_cpuState,
      ProvableType.eval_field])
  rw [branchCpuRustAccesses, branchRustColumns_state,
    branchRustColumns_nextPc, branchRustColumns_sum]
  simpa only [cpuInput] using hCpu

private theorem branchITypeByte_faithful
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (branchSum (p := p) offset)) :
    (((Readers.ITypeReaderImmutable.main
        (branchITypeInput input offset)).operations
          (offset + 20)).interactionsWith byteChannel.toRaw).map
            (AbstractInteraction.toAccess env) =
      (branchITypeRustAccesses
        (branchChipRustColumns env input offset)).filter
          (fun access => access.1 = InteractionKind.Byte) := by
  let readerInput := branchITypeInput input offset
  let rustAdapter := Eval.eval env input.adapter
  have hReader :=
    itypereaderimmutable_byte_interactions_faithful_syntactic
      (p := p) env readerInput (offset + 20)
      (Expression.eval env input.state.clk_high)
      (Expression.eval env
        (input.state.clk_0_16 +
          input.state.clk_16_24 * 65536))
      (Eval.eval env input.state.pc)
      (Expression.eval env (branchOpcode offset))
      rustAdapter
      (Expression.eval env (branchSum offset))
      (Expression.eval env (branchSum offset))
      (by simpa only [readerInput, branchITypeInput,
        ProvableStruct.structEvalLiteralProc] using hinputReal)
      (by rfl)
      (by simp only [readerInput, branchITypeInput, rustAdapter,
        Readers.ITypeReader.eval_cols, eval_registerAccessCols,
        eval_registerAccessTimestamp, ProvableType.eval_field])
      (by simp only [readerInput, branchITypeInput, rustAdapter,
        Readers.ITypeReader.eval_cols, eval_registerAccessCols,
        eval_registerAccessTimestamp, ProvableType.eval_field])
      (by simp only [readerInput, branchITypeInput, rustAdapter,
        Readers.ITypeReader.eval_cols, eval_registerAccessCols,
        eval_registerAccessTimestamp, ProvableType.eval_field])
      (by simp only [readerInput, branchITypeInput, rustAdapter,
        Readers.ITypeReader.eval_cols, eval_registerAccessCols,
        eval_registerAccessTimestamp, ProvableType.eval_field])
  have hClkLow :
      Expression.eval env
          (input.state.clk_0_16 +
            input.state.clk_16_24 * 65536) =
        Expression.eval env input.state.clk_0_16 +
          Expression.eval env input.state.clk_16_24 * 65536 := rfl
  rw [hClkLow] at hReader
  rw [branchITypeRustAccesses, branchRustColumns_state,
    branchRustColumns_adapter, branchRustColumns_opcode,
    branchRustColumns_sum]
  rw [show branchITypeInput input offset = readerInput by rfl]
  simp only [eval_cpuState, ProvableType.eval_field]
  exact hReader

private theorem branchLtByte_faithful
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (branchSum (p := p) offset)) :
    (((LtOperationSigned.main
        (branchLtInput input offset)).operations
          (offset + 20)).interactionsWith byteChannel.toRaw).map
            (AbstractInteraction.toAccess env) =
      branchLtRustAccesses
        (branchChipRustColumns env input offset) := by
  let ltInput := branchLtInput input offset
  have hA :
      Eval.eval env ltInput.b =
        (Eval.eval env input.adapter).op_a_memory.prev_value := by
    simp only [ltInput, branchLtInput]
    rw [vec4_eta]
    rw [Readers.ITypeReader.eval_cols]
    dsimp only
    rw [eval_registerAccessCols]
  have hB :
      Eval.eval env ltInput.cc =
        (Eval.eval env input.adapter).op_b_memory.prev_value := by
    simp only [ltInput, branchLtInput]
    rw [vec4_eta]
    rw [Readers.ITypeReader.eval_cols]
    dsimp only
    rw [eval_registerAccessCols]
  have hLt := ltSigned_interactions_exact
    (p := p) env ltInput (offset + 20)
  rw [hA, hB] at hLt
  simp only [ltInput, branchLtInput, branchFlag,
    Expression.eval] at hLt
  rw [hinputReal] at hLt
  rw [branchLtRustAccesses, branchRustColumns_adapter,
    branchRustColumns_compare, branchRustColumns_signed,
    branchRustColumns_sum]
  exact hLt

omit [Fact (2 ^ 17 < p)] in
private theorem branchLtRustAccesses_allByte
    (cols : BranchChip.Columns (ZMod p)) :
    (branchLtRustAccesses cols).filter
        (fun access => access.1 = InteractionKind.Byte) =
      branchLtRustAccesses cols := by
  simp [branchLtRustAccesses,
    Extracted.LtOperationSigned.interactions,
    Extracted.U16MSBOperation.interactions,
    Extracted.LtOperationUnsigned.interactions,
    Extracted.U16CompareOperation.interactions,
    Extracted.Interaction.toAccess]

omit [Fact (2 ^ 17 < p)] in
private theorem branchTailRustAccesses_allByte
    (cols : BranchChip.Columns (ZMod p)) :
    (branchTailRustAccesses cols).filter
        (fun access => access.1 = InteractionKind.Byte) =
      branchTailRustAccesses cols := by
  simp [branchTailRustAccesses, branchRustInteractionTail,
    Extracted.Interaction.toAccess]

private theorem branchTailByte_faithful
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (branchSum (p := p) offset)) :
    (((branchTailByteInteractions input offset).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env)) =
      branchTailRustAccesses
        (branchChipRustColumns env input offset) := by
  have h6 : (6 : ZMod p).val = 6 := val_6_zmod_p
  have h14 : (14 : ZMod p).val = 14 := val_14_zmod_p
  have h16 : (16 : ZMod p).val = 16 := val_16_zmod_p
  have hBytePull :
      ∀ (gate : Expression (ZMod p))
        (msg : ByteRow (Expression (ZMod p))),
        AbstractInteraction.toAccess env
            (((byteChannel (p := p)).pulledIf gate msg).toRaw) =
          (InteractionKind.Byte, "SP1Byte",
            [(Expression.eval env msg.opcode).val,
             (Expression.eval env msg.a).val,
             (Expression.eval env msg.b).val,
             (Expression.eval env msg.c).val],
            signedVal (Expression.eval env (-gate))) :=
    fun gate msg => toAccess_pullIf_byte env gate msg
  rw [branchTailRustAccesses]
  simp only [branchRustInteractionTail]
  rw [branchRustColumns_nextPc, branchRustColumns_sum]
  simp [branchTailByteInteractions,
    hBytePull, Extracted.Interaction.toAccess, Extracted.Dir.sign, branchNextPc,
    ← ProvableType.getElem_eval_fields,
    Expression.eval, hinputReal, h6, h14, h16]

private theorem branchByteInteractions_faithful
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (branchSum (p := p) offset)) :
    List.Perm
      ((((BranchChip.main input).operations offset).interactionsWith
          byteChannel.toRaw).map
            (AbstractInteraction.toAccess env))
      ((branchRustAccesses env input offset).filter
        (fun access => access.1 = InteractionKind.Byte)) := by
  rw [branchByteInteractions_decompose]
  simp only [List.map_append]
  rw [branchRustAccesses_decompose,
    List.filter_append, List.filter_append, List.filter_append,
    branchLtRustAccesses_allByte,
    branchTailRustAccesses_allByte]
  rw [branchLtByte_faithful env input offset hinputReal,
    branchCpuByte_faithful env input offset hinputReal,
    branchITypeByte_faithful env input offset hinputReal,
    branchTailByte_faithful env input offset hinputReal]
  simpa only [List.append_assoc] using
    (List.perm_append_comm
      (l₁ := branchLtRustAccesses
        (branchChipRustColumns env input offset))
      (l₂ := (branchCpuRustAccesses
          (branchChipRustColumns env input offset)).filter
            (fun access => access.1 = InteractionKind.Byte) ++
        (branchITypeRustAccesses
          (branchChipRustColumns env input offset)).filter
            (fun access => access.1 = InteractionKind.Byte))).append_right
      (branchTailRustAccesses
        (branchChipRustColumns env input offset))

private theorem branchUnexpectedInteractions_empty
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) :
    unexpectedInteractions
        ((BranchChip.main input).operations offset) = [] := by
  unfold unexpectedInteractions
  apply List.filter_eq_nil_iff.mpr
  intro interaction hmem hunexpected
  have hchannel :
      interaction.channel ∈
        ((BranchChip.main input).operations offset).channels := by
    rw [Operations.channels]
    exact List.mem_map.mpr ⟨interaction, hmem, rfl⟩
  have hknown :=
    (BranchChip.circuit (p := p)).channels_subset
      input offset hchannel
  simp only [BranchChip.circuit,
    FormalCircuitBase.channelsWithGuarantees_def,
    FormalCircuitBase.channelsWithRequirements_def,
    circuit_norm] at hknown
  simp only [decide_eq_true_eq] at hunexpected
  tauto

theorem branchChip_interactions_faithful
    (env : Environment (ZMod p))
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : BranchChip.Columns (ZMod p))
    (hbind : BindsChipOutput BranchChip.main env input offset cols)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (branchSum (p := p) offset)) :
    List.Perm
      (nativeAccesses env
        ((BranchChip.main input).operations offset))
      (branchChipOracle.accesses cols) := by
  replace hbind := BindsChipOutput.ofElaborated
    (BranchChip.elaborated (p := p)) hbind
  rw [BranchChip.directOutput_eq] at hbind
  rw [← ProvableStruct.eval_eq_eval,
    BranchChip.eval_columns] at hbind
  simp only [ProvableType.eval_field] at hbind
  change branchChipRustColumns env input offset = cols at hbind
  subst cols
  let rustAccesses :=
    branchRustAccesses env input offset
  simp only [nativeAccesses]
  rw [branchUnexpectedInteractions_empty]
  simp only [List.map_nil, List.append_nil]
  simp only [ChipOracle.accesses,
    ChipOracle.nativeInteractions, branchChipOracle]
  rw [branchStateInteractions_eq,
    BranchChip.interactionsWith_memory_eq,
    branchProgramInteractions_eq]
  have hState :=
    branchStateInteractions_faithful
      (p := p) env input offset hinputReal
  have hByte :=
    branchByteInteractions_faithful
      (p := p) env input offset hinputReal
  have hMemory :=
    branchMemoryInteractions_faithful
      (p := p) env input offset hinputReal
  have hProgram :=
    branchProgramInteractions_faithful
      (p := p) env input offset hinputReal
  refine List.Perm.trans ?_
    (LookupAccessList.perm_filter_by_kind rustAccesses).symm
  dsimp only [rustAccesses] at hState hByte hMemory hProgram ⊢
  rw [hState, hMemory, hProgram]
  simpa only [List.append_assoc] using
    (hByte.append_left _).append_right _

theorem branchChip_interactions_constructive
    (rustCols : Extracted.BranchOracle.BranchColumns (ZMod p))
    (data : ProverData (ZMod p)) :
    let assignment := branchChipRowCodec.assignment
      (branchChipOracle.deconfigure rustCols) data
    List.Perm
      (nativeAccesses assignment.environment
        (⟨BranchChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).operations)
      (branchChipOracle.rustAccesses rustCols) := by
  dsimp only
  let cols := branchChipOracle.deconfigure rustCols
  let assignment := branchChipRowCodec.assignment cols data
  have hbind : BindsChipOutput BranchChip.main assignment.environment
      (⟨BranchChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).rowInputVar
      (⟨BranchChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [BranchChip.circuit_main_eq] at h
    exact h
  have hlegacy := branchChip_interactions_faithful
    (p := p) assignment.environment
    (⟨BranchChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowInputVar
    (⟨BranchChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind
    (branchChipRowCodec_inputReal (p := p) cols data)
  rw [nativeAccesses_component_eq_rowOperations
    (BranchChip.circuit (p := p)) assignment.environment]
  simpa only [cols, ChipOracle.accesses_deconfigure,
    Air.Flat.Component.rowOperations_mk,
    Air.Flat.Component.rowInputVar_mk,
    Air.Flat.Component.rowOffset_mk,
    BranchChip.circuit_main_eq] using hlegacy

theorem branchChip_faithful :
    ChipFaithful (p := p) BranchChip.Inputs
      BranchChip.Columns Extracted.BranchOracle.BranchColumns
      BranchChip.circuit branchChipRowCodec branchChipOracle where
  constraints := branchChip_constraints_constructive (p := p)
  interactions := fun rustCols data _ =>
    LookupAccessList.active_perm
      (branchChip_interactions_constructive
        (p := p) rustCols data)

end SP1Clean.Faithful
