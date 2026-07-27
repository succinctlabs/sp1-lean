import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Model.SP1Constraint
import SP1Clean.Extracted.AluX0Chip
import SP1Clean.Faithful.CPUState
import SP1Clean.Faithful.ChipOracle
import SP1Clean.Proofs.Chips.AluX0Chip.Formal

/-! # Chip-level faithfulness anchor — SP1's whole `AluX0` chip constraint list ↔ combined spec

The fourth-artifact anchor for `AluX0` (ALU instructions into `x0`). SP1's generated `AluX0` constraint
list is `CPUState.{asserts,interactions} ++ [the inlined ALU-reader-immutable constraints, the LTU
`opcode < 29` range send, and the `is_real`/`op_a_0` gates]`. Unlike `LoadX0`, the register adapter is
**inlined** (SP1's `ALUTypeReader::eval_op_a_immutable` is a plain method, not an `SP1Operation`), so only
`CPUState` is a sub-call; the reader fragment is discharged directly with the same byte/memory `toProp`
reductions `Faithful/ALUTypeReader.lean` uses. Under `is_real = 1` the `is_real`-binary gates collapse and
the gated constraints reduce. -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

private lemma val_29'' [NeZero p] : (29 : ZMod p).val = 29 := by
  have : (131072 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  exact ZMod.val_natCast_of_lt (show (29 : ℕ) < p by omega)

set_option maxHeartbeats 4000000 in
/-- **Chip-level faithfulness anchor.** Under `is_real = 1`, SP1's generated `AluX0` chip constraint list
holds iff: the two CPUState clock bounds; the `op_a_0 = 1` forcing (`rd = x0`); the four op_a **read**-zeroing
gates; the op_c immediate gate (`is_real - imm_c` boolean) and the four immediate-consistency gates; the
dynamic opcode in ALU range (`opcode < 29`, the LTU send); and the op_a/op_b/op_c register timestamp byte
bounds (op_c guarded by `imm_c ≠ 1`). Every fragment reduces with the same machinery as
`Faithful/ALUTypeReader.lean`; the reader is inlined (not a sub-`asserts` call). -/
theorem alux0cols_constraints_faithful (cols : Extracted.AluX0Cols (ZMod p))
    (h_real : cols.is_real = 1) :
    (List.Forall (· = 0) (Extracted.AluX0Cols.asserts cols) ∧
      List.Forall Interaction.toProp (Extracted.AluX0Cols.interactions cols)) ↔
      ((((cols.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧ cols.state.clk_16_24.val < 256)
        ∧ (cols.adapter.op_a_0 - 1 = 0 ∧
            cols.adapter.op_a_0 * cols.adapter.op_a_memory.prev_value[0] = 0 ∧
            cols.adapter.op_a_0 * cols.adapter.op_a_memory.prev_value[1] = 0 ∧
            cols.adapter.op_a_0 * cols.adapter.op_a_memory.prev_value[2] = 0 ∧
            cols.adapter.op_a_0 * cols.adapter.op_a_memory.prev_value[3] = 0 ∧
            (1 - cols.adapter.imm_c) * (1 - cols.adapter.imm_c - 1) = 0 ∧
            cols.adapter.imm_c * (cols.adapter.op_c_memory.prev_value[0] - cols.adapter.op_c[0]) = 0 ∧
            cols.adapter.imm_c * (cols.adapter.op_c_memory.prev_value[1] - cols.adapter.op_c[1]) = 0 ∧
            cols.adapter.imm_c * (cols.adapter.op_c_memory.prev_value[2] - cols.adapter.op_c[2]) = 0 ∧
            cols.adapter.imm_c * (cols.adapter.op_c_memory.prev_value[3] - cols.adapter.op_c[3]) = 0)
        ∧ (cols.opcode.val < 256 ∧ cols.opcode.val < 29)
          ∧ cols.adapter.op_a_memory.access_timestamp.diff_low_limb.val < 65536
          ∧ ((cols.state.clk_0_16 + cols.state.clk_16_24 * 65536 + 4
                - cols.adapter.op_a_memory.access_timestamp.prev_low - 1
                - cols.adapter.op_a_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 256
          ∧ cols.adapter.op_b_memory.access_timestamp.diff_low_limb.val < 65536
          ∧ ((cols.state.clk_0_16 + cols.state.clk_16_24 * 65536 + 3
                - cols.adapter.op_b_memory.access_timestamp.prev_low - 1
                - cols.adapter.op_b_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 256
          ∧ (¬1 - cols.adapter.imm_c = 0 →
              cols.adapter.op_c_memory.access_timestamp.diff_low_limb.val < 65536)
          ∧ (¬1 - cols.adapter.imm_c = 0 →
              ((cols.state.clk_0_16 + cols.state.clk_16_24 * 65536 + 2
                - cols.adapter.op_c_memory.access_timestamp.prev_low - 1
                - cols.adapter.op_c_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 256)) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [Extracted.AluX0Cols.asserts, Extracted.AluX0Cols.interactions]
  rw [Extracted.forall_append_pair]
  simp only [h_real]
  rw [cpustate_constraints_faithful]
  simp only [List.Forall, Interaction.toProp_send_byte, Interaction.toProp_receive,
    Interaction.toProp_send_memory, Interaction.toProp_send_program,
    ByteOpcode.constrainField_six, ByteOpcode.constrainField_three,
    ByteOpcode.constrainField_four,
    ByteOpcode.constrain_Range, ByteOpcode.constrain_U8Range, ByteOpcode.constrain_LTU,
    val_16_zmod_p, val_29'', ZMod.val_zero, ZMod.val_one, one_ne_zero, ne_eq, not_false_eq_true,
    true_implies, sub_self, mul_zero, sub_zero, zero_mul, one_mul, Nat.ofNat_pos, true_and, and_true,
    false_or, true_iff, show (1 : ℕ) < 256 from by norm_num, show (29 : ℕ) < 256 from by norm_num,
    show (2 : ℕ) ^ 8 = 256 from by norm_num, show (2 : ℕ) ^ 16 = 65536 from by norm_num]

/-! ## Constructive whole-chip boundary -/

def aluX0ChipOracle :
    ChipOracle (ZMod p) Extracted.AluX0Cols Extracted.AluX0Cols :=
  ChipOracle.identity Extracted.AluX0Cols.asserts Extracted.AluX0Cols.interactions

def aluX0ChipInput {F : Type} (cols : Extracted.AluX0Cols F) : AluX0Chip.Inputs F :=
  { state := cols.state, adapter := cols.adapter, opcode := cols.opcode,
    is_real := cols.is_real }

def aluX0ChipLocals {F : Type} (_cols : Extracted.AluX0Cols F) : Vector F 0 :=
  #v[]

def aluX0ChipPhysicalRow {F : Type} (cols : Extracted.AluX0Cols F) : Array F :=
  inputFirstRow (aluX0ChipInput cols) (aluX0ChipLocals cols)

def aluX0ChipColumnsOfInput {F : Type} (input : AluX0Chip.Inputs F) :
    Extracted.AluX0Cols F :=
  ⟨input.state, input.adapter, input.opcode, input.is_real⟩

theorem aluX0ChipColumnsOfInput_roundtrip {F : Type} (cols : Extracted.AluX0Cols F) :
    aluX0ChipColumnsOfInput (aluX0ChipInput cols) = cols := by
  cases cols
  rfl

theorem eval_aluX0ChipDirectOutput
    (input : AluX0Chip.Inputs (ZMod p)) (data : ProverData (ZMod p)) :
    ProvableType.eval (Environment.fromArray (inputFirstRow input #v[]) data)
        ((AluX0Chip.elaborated (p := p)).output
          (varFromOffset AluX0Chip.Inputs 0) (size AluX0Chip.Inputs)) =
      aluX0ChipColumnsOfInput input := by
  rw [AluX0Chip.directOutput_eq]
  rw [← CircuitType.eval_expression, AluX0Chip.eval_columns]
  unfold aluX0ChipColumnsOfInput
  rw [Extracted.AluX0Cols.mk.injEq]
  dsimp only
  have hinputEval := eval_inputFirstRow input #v[] data
  rw [AluX0Chip.eval_inputs, AluX0Chip.Inputs.mk.injEq] at hinputEval
  exact hinputEval

def aluX0ChipRowCodec : ChipRowCodec AluX0Chip.Inputs Extracted.AluX0Cols
    (AluX0Chip.circuit (p := p)) where
  assignment cols data := {
    row := aluX0ChipPhysicalRow cols
    input := aluX0ChipInput cols
    width_eq := by
      rw [aluX0ChipPhysicalRow, inputFirstRow_size, Air.Flat.Component.width,
        AluX0Chip.circuit_size_eq]
      simp
    rowInput_eq := by
      exact rowInput_inputFirstRow (AluX0Chip.circuit (p := p)) (aluX0ChipInput cols)
        (aluX0ChipLocals cols) data
    rowOutput_eq := by
      change ProvableType.eval _ ((AluX0Chip.main _).output _) = _
      rw [AluX0Chip.elaborated.output_eq]
      rw [Air.Flat.Component.rowInputVar_mk, Air.Flat.Component.rowOffset_mk]
      exact (eval_aluX0ChipDirectOutput (p := p) (aluX0ChipInput cols) data).trans
        (aluX0ChipColumnsOfInput_roundtrip cols) }

theorem aluX0Chip_lookups_empty :
    (⟨AluX0Chip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).operations.lookups = [] := by
  rw [Air.Flat.Component.lookups_eq, Air.Flat.Component.rowOperations_mk,
    AluX0Chip.circuit_main_eq]
  simp [AluX0Chip.main, Readers.CPUState.circuit, Readers.CPUState.main,
    Readers.ALUTypeReaderImmutable.circuit, Readers.ALUTypeReaderImmutable.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    Gadgets.Equality.main, circuit_norm]

set_option maxHeartbeats 1000000 in
private theorem aluX0_chip_constraints_decompose
    (env : Environment (ZMod p)) (input : Var AluX0Chip.Inputs (ZMod p))
    (offset : ℕ) :
    List.Forall (· = 0)
        (nativeAssertZeros env ((AluX0Chip.main input).operations offset)) ↔
      (List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.CPUState.main
              ⟨input.state,
                #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
                8, input.is_real⟩).operations offset)) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.ALUTypeReaderImmutable.main
              ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
                input.state.clk_0_16 + input.state.clk_16_24 * 65536,
                input.state.pc, input.opcode⟩).operations offset)) ∧
        Expression.eval env (input.is_real * (input.is_real - 1)) = 0 ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main
              (M := field) (input.is_real * (input.adapter.op_a_0 - 1), 0)).operations
                offset)) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main
              (M := field) ((input.is_real - 1) * input.adapter.op_a_0, 0)).operations
                offset))) := by
  simp only [nativeAssertZeros, AluX0Chip.main, Readers.CPUState.circuit,
    Readers.ALUTypeReaderImmutable.circuit, circuit_norm, List.map_append,
    List.forall_append, List.forall_cons]

set_option maxHeartbeats 4000000 in
theorem aluX0Chip_constraints_faithful
    (env : Environment (ZMod p)) (input : Var AluX0Chip.Inputs (ZMod p))
    (offset : ℕ) (cols : Extracted.AluX0Cols (ZMod p))
    (hbind : BindsChipOutput AluX0Chip.main env input offset cols) :
    List.Forall (· = 0) (aluX0ChipOracle.nativeAssertZeros cols) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env ((AluX0Chip.main input).operations offset)) := by
  let stateValue := ProvableStruct.eval env input.state
  let isReal := Expression.eval env input.is_real
  let cpuInput : Var Readers.CPUState.Inputs (ZMod p) :=
    ⟨input.state,
      #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
      8, input.is_real⟩
  let rustState : Extracted.CPUState (ZMod p) :=
    { clk_high := stateValue.clk_high
      clk_16_24 := stateValue.clk_16_24
      clk_0_16 := stateValue.clk_0_16
      pc := #v[stateValue.pc[0], stateValue.pc[1], stateValue.pc[2]] }
  let rustNextPc : Vector (ZMod p) 3 :=
    #v[stateValue.pc[0] + 4, stateValue.pc[1], stateValue.pc[2]]
  have hCpu := CanonicalReader.cpuStateAssertions (p := p) env cpuInput offset
    rustState rustNextPc 8 isReal (by
      simp only [cpuInput, isReal, ProvableStruct.structEvalLiteralProc])
  let readerInput : Var Readers.ALUTypeReaderImmutable.Inputs (ZMod p) :=
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      input.state.pc, input.opcode⟩
  have hReaderList :=
    CanonicalReader.aluTypeImmutableAssertionList (p := p) env readerInput offset
  have hReader :
      List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.ALUTypeReaderImmutable.main readerInput).operations offset)) ↔
        List.Forall (· = 0)
          (CanonicalReader.aluTypeImmutableAssertionValues env readerInput) := by
    unfold nativeAssertZeros
    rw [hReaderList]
  replace hbind := BindsChipOutput.ofElaborated (AluX0Chip.elaborated (p := p)) hbind
  rw [AluX0Chip.directOutput_eq] at hbind
  simp only [ProvableStruct.structEvalLiteralProc] at hbind
  subst cols
  rw [aluX0_chip_constraints_decompose]
  simp only [ChipOracle.nativeAssertZeros, aluX0ChipOracle,
    ChipOracle.identity, id_eq]
  simp only [Extracted.AluX0Cols.asserts, List.forall_append, List.forall_cons]
  dsimp [rustState, rustNextPc, stateValue, isReal, cpuInput] at hCpu
  simp_rw [← ProvableStruct.eval_eq_eval] at hCpu
  rw [hCpu]
  rw [hReader]
  rw [CanonicalReader.equalityAssertions env
      (input.is_real * (input.adapter.op_a_0 - 1)) 0 offset,
    CanonicalReader.equalityAssertions env
      ((input.is_real - 1) * input.adapter.op_a_0) 0 offset]
  unfold CanonicalReader.aluTypeImmutableAssertionValues
  dsimp only [readerInput]
  simp only [List.Forall, eval_sub, Expression.eval, sub_zero,
    eval_aluTypeReader, eval_registerAccessCols, ProvableType.eval_field,
    ← ProvableType.getElem_eval_fields]
  have hopA0 :
      Expression.eval env input.is_real *
            (Expression.eval env input.is_real - 1) = 0 →
        Expression.eval env input.is_real *
            (Expression.eval env input.adapter.op_a_0 - 1) = 0 →
        (Expression.eval env input.is_real - 1) *
            Expression.eval env input.adapter.op_a_0 = 0 →
        Expression.eval env input.adapter.op_a_0 *
            (Expression.eval env input.adapter.op_a_0 - 1) = 0 := by
    intro hreal hone hzero
    rcases bool_of_mul_pred hreal with realZero | realOne
    · rw [realZero] at hzero
      simp only [zero_sub, neg_mul, neg_eq_zero] at hzero
      have hopZero : Expression.eval env input.adapter.op_a_0 = 0 := by
        simpa using hzero
      rw [hopZero]
      simp
    · rw [realOne] at hone
      simp only [one_mul, sub_eq_zero] at hone
      have hopOne : Expression.eval env input.adapter.op_a_0 = 1 := hone
      rw [hopOne]
      simp
  tauto

set_option maxHeartbeats 4000000 in
theorem aluX0Chip_constraints_constructive
    (rustCols : Extracted.AluX0Cols (ZMod p)) (data : ProverData (ZMod p)) :
    let assignment := aluX0ChipRowCodec.assignment
      (aluX0ChipOracle.deconfigure rustCols) data
    List.Forall (· = 0) (aluX0ChipOracle.assertZeros rustCols) ↔
      (⟨AluX0Chip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).operations.ConstraintsHold
          assignment.environment := by
  dsimp only
  let cols := aluX0ChipOracle.deconfigure rustCols
  let assignment := aluX0ChipRowCodec.assignment cols data
  have hbind : BindsChipOutput AluX0Chip.main assignment.environment
      (⟨AluX0Chip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowInputVar
      (⟨AluX0Chip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowOffset
      cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [AluX0Chip.circuit_main_eq] at h
    exact h
  have hlegacy := aluX0Chip_constraints_faithful (p := p)
    assignment.environment
    (⟨AluX0Chip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowInputVar
    (⟨AluX0Chip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowOffset
    cols hbind
  have hassertions :
      List.Forall (· = 0) (aluX0ChipOracle.assertZeros rustCols) ↔
        List.Forall (· = 0)
          (nativeAssertZeros assignment.environment
            (⟨AluX0Chip.circuit (p := p)⟩ :
              Air.Flat.Component (ZMod p)).rowOperations) := by
    simpa only [cols, ChipOracle.nativeAssertZeros_deconfigure,
      Air.Flat.Component.rowOperations_mk, Air.Flat.Component.rowInputVar_mk,
      Air.Flat.Component.rowOffset_mk, AluX0Chip.circuit_main_eq] using hlegacy
  exact hassertions.trans
    (constraintsHold_iff_nativeAssertZeros (AluX0Chip.circuit (p := p))
      assignment.environment aluX0Chip_lookups_empty).symm

set_option maxHeartbeats 4000000 in
theorem aluX0Chip_interactions_faithful
    (env : Environment (ZMod p)) (input : Var AluX0Chip.Inputs (ZMod p))
    (offset : ℕ) (cols : Extracted.AluX0Cols (ZMod p))
    (hbind : BindsChipOutput AluX0Chip.main env input offset cols) :
    List.Perm (nativeAccesses env ((AluX0Chip.main input).operations offset))
      (aluX0ChipOracle.accesses cols) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp2 : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have h6 : (6 : ZMod p).val = 6 := by
    have h : (6 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt h
  have hsign :
      -signedVal
          (Expression.eval env input.is_real -
            Expression.eval env input.adapter.imm_c) =
        signedVal
          (Expression.eval env input.adapter.imm_c -
            Expression.eval env input.is_real) := by
    rw [(by ring :
      Expression.eval env input.adapter.imm_c -
          Expression.eval env input.is_real =
        -(Expression.eval env input.is_real -
          Expression.eval env input.adapter.imm_c)), signedVal_neg hp2]
  replace hbind := BindsChipOutput.ofElaborated (AluX0Chip.elaborated (p := p)) hbind
  rw [AluX0Chip.directOutput_eq] at hbind
  simp only [ProvableStruct.structEvalLiteralProc] at hbind
  subst cols
  simp only [nativeAccesses]
  have hunexpected :
      unexpectedInteractions ((AluX0Chip.main input).operations offset) = [] := by
    simp [unexpectedInteractions, AluX0Chip.main,
      Readers.CPUState.circuit, Readers.CPUState.main,
      Readers.ALUTypeReaderImmutable.circuit, Readers.ALUTypeReaderImmutable.main,
      Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
      Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
      Gadgets.Equality.main, FormalAssertion.toSubcircuit_interactions,
      GeneralFormalCircuit.toSubcircuit_interactions, circuit_norm]
  rw [hunexpected]
  simp only [List.map_nil, List.append_nil]
  simp only [ChipOracle.accesses, ChipOracle.nativeInteractions,
    aluX0ChipOracle, ChipOracle.identity, id_eq]
  rw [AluX0Chip.interactionsWith_state_eq, AluX0Chip.interactionsWith_byte_eq,
    AluX0Chip.interactionsWith_memory_eq, AluX0Chip.interactionsWith_program_eq]
  have hStatePull :
      ∀ (gate : Expression (ZMod p))
        (msg : SP1Clean.Channels.StateMsg (Expression (ZMod p))),
        AbstractInteraction.toAccess env
            (((SP1Clean.Channels.stateChannel (p := p)).pulledIf gate msg).toRaw) =
          (InteractionKind.State, "SP1State",
            [(Expression.eval env msg.clk_high).val,
             (Expression.eval env msg.clk_low).val,
             (Expression.eval env msg.pc0).val,
             (Expression.eval env msg.pc1).val,
             (Expression.eval env msg.pc2).val],
            signedVal (Expression.eval env (-gate))) :=
    fun gate msg => toAccess_pullIf_state env gate msg
  have hStatePush :
      ∀ (mult : Expression (ZMod p))
        (msg : SP1Clean.Channels.StateMsg (Expression (ZMod p))),
        AbstractInteraction.toAccess env
            (((SP1Clean.Channels.stateChannel (p := p)).pushedIf mult msg).toRaw) =
          (InteractionKind.State, "SP1State",
            [(Expression.eval env msg.clk_high).val,
             (Expression.eval env msg.clk_low).val,
             (Expression.eval env msg.pc0).val,
             (Expression.eval env msg.pc1).val,
             (Expression.eval env msg.pc2).val],
            signedVal (Expression.eval env mult)) :=
    fun mult msg => toAccess_pushIf_state env mult msg
  have hBytePull :
      ∀ (gate : Expression (ZMod p)) (msg : ByteRow (Expression (ZMod p))),
        AbstractInteraction.toAccess env
            (((SP1Clean.Channels.byteChannel (p := p)).pulledIf gate msg).toRaw) =
          (InteractionKind.Byte, "SP1Byte",
            [(Expression.eval env msg.opcode).val,
             (Expression.eval env msg.a).val,
             (Expression.eval env msg.b).val,
             (Expression.eval env msg.c).val],
            signedVal (Expression.eval env (-gate))) :=
    fun gate msg => toAccess_pullIf_byte env gate msg
  have hMemoryPull :
      ∀ (gate : Expression (ZMod p))
        (msg : SP1Clean.Channels.MemoryMsg (Expression (ZMod p))),
        AbstractInteraction.toAccess env
            (((SP1Clean.Channels.memoryChannel (p := p)).pulledIf gate msg).toRaw) =
          (InteractionKind.Memory, "SP1Memory",
            [(Expression.eval env msg.clk_high).val,
             (Expression.eval env msg.clk_low).val,
             (Expression.eval env msg.addr0).val,
             (Expression.eval env msg.addr1).val,
             (Expression.eval env msg.addr2).val,
             (Expression.eval env msg.value[0]).val,
             (Expression.eval env msg.value[1]).val,
             (Expression.eval env msg.value[2]).val,
             (Expression.eval env msg.value[3]).val],
            signedVal (Expression.eval env (-gate))) :=
    fun gate msg => toAccess_pullIf_memory env gate msg
  have hMemoryPush :
      ∀ (mult : Expression (ZMod p))
        (msg : SP1Clean.Channels.MemoryMsg (Expression (ZMod p))),
        AbstractInteraction.toAccess env
            (((SP1Clean.Channels.memoryChannel (p := p)).pushedIf mult msg).toRaw) =
          (InteractionKind.Memory, "SP1Memory",
            [(Expression.eval env msg.clk_high).val,
             (Expression.eval env msg.clk_low).val,
             (Expression.eval env msg.addr0).val,
             (Expression.eval env msg.addr1).val,
             (Expression.eval env msg.addr2).val,
             (Expression.eval env msg.value[0]).val,
             (Expression.eval env msg.value[1]).val,
             (Expression.eval env msg.value[2]).val,
             (Expression.eval env msg.value[3]).val],
            signedVal (Expression.eval env mult)) :=
    fun mult msg => toAccess_pushIf_memory env mult msg
  have hProgramPull :
      ∀ (gate : Expression (ZMod p))
        (msg : SP1Clean.Channels.ProgramMsg (Expression (ZMod p))),
        AbstractInteraction.toAccess env
            (((SP1Clean.Channels.programChannel (p := p)).pulledIf gate msg).toRaw) =
          (InteractionKind.Program, "SP1Program",
            [(Expression.eval env msg.pc0).val,
             (Expression.eval env msg.pc1).val,
             (Expression.eval env msg.pc2).val,
             (Expression.eval env msg.opcode).val,
             (Expression.eval env msg.op_a).val,
             (Expression.eval env msg.op_b[0]).val,
             (Expression.eval env msg.op_b[1]).val,
             (Expression.eval env msg.op_b[2]).val,
             (Expression.eval env msg.op_b[3]).val,
             (Expression.eval env msg.op_c[0]).val,
             (Expression.eval env msg.op_c[1]).val,
             (Expression.eval env msg.op_c[2]).val,
             (Expression.eval env msg.op_c[3]).val,
             (Expression.eval env msg.op_a_0).val,
             (Expression.eval env msg.imm_b).val,
             (Expression.eval env msg.imm_c).val],
            signedVal (Expression.eval env (-gate))) :=
    fun gate msg => toAccess_pullIf_program env gate msg
  refine List.Perm.trans (List.Perm.of_eq ?_)
    (LookupAccessList.perm_filter_by_kind _).symm
  simp only [AluX0Chip.exposedStateInteractions, AluX0Chip.exposedByteInteractions,
    AluX0Chip.exposedMemoryInteractions, AluX0Chip.exposedProgramInteractions,
    List.map_cons, List.map_nil, hStatePull, hStatePush, hBytePull,
    hMemoryPull, hMemoryPush, hProgramPull]
  simp [Extracted.AluX0Cols.interactions, Extracted.CPUState.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    Expression.eval, ProvableType.eval_field,
    eval_cpuState, eval_aluTypeReader, eval_registerAccessCols,
    eval_registerAccessTimestamp, ← ProvableType.getElem_eval_fields,
    Opcode.ofNat, ConstraintCoe.coe_eq_val,
    LookupAccessList.negMult, signedVal_neg hp2, h6]
  simp only [← ProvableStruct.eval_eq_eval, AluX0Chip.eval_inputs,
    eval_cpuState, eval_aluTypeReader, eval_registerAccessCols,
    eval_registerAccessTimestamp, eval_sub,
    ProvableType.eval_field, Expression.eval]
  simp only [hsign, true_and]

set_option maxHeartbeats 4000000 in
theorem aluX0Chip_interactions_constructive
    (rustCols : Extracted.AluX0Cols (ZMod p)) (data : ProverData (ZMod p)) :
    let assignment := aluX0ChipRowCodec.assignment
      (aluX0ChipOracle.deconfigure rustCols) data
    List.Perm
      (nativeAccesses assignment.environment
        (⟨AluX0Chip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).operations)
      (aluX0ChipOracle.rustAccesses rustCols) := by
  dsimp only
  let cols := aluX0ChipOracle.deconfigure rustCols
  let assignment := aluX0ChipRowCodec.assignment cols data
  have hbind : BindsChipOutput AluX0Chip.main assignment.environment
      (⟨AluX0Chip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowInputVar
      (⟨AluX0Chip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowOffset
      cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [AluX0Chip.circuit_main_eq] at h
    exact h
  have hlegacy := aluX0Chip_interactions_faithful (p := p)
    assignment.environment
    (⟨AluX0Chip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowInputVar
    (⟨AluX0Chip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowOffset
    cols hbind
  rw [nativeAccesses_component_eq_rowOperations (AluX0Chip.circuit (p := p))
    assignment.environment]
  simpa only [cols, ChipOracle.accesses_deconfigure,
    Air.Flat.Component.rowOperations_mk, Air.Flat.Component.rowInputVar_mk,
    Air.Flat.Component.rowOffset_mk, AluX0Chip.circuit_main_eq] using hlegacy

theorem aluX0Chip_faithful :
    ChipFaithful (p := p) AluX0Chip.Inputs Extracted.AluX0Cols
      Extracted.AluX0Cols AluX0Chip.circuit aluX0ChipRowCodec
      aluX0ChipOracle where
  constraints := aluX0Chip_constraints_constructive (p := p)
  interactions := fun rustCols data _ =>
    LookupAccessList.active_perm
      (aluX0Chip_interactions_constructive (p := p) rustCols data)

end SP1Clean.Faithful
