import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Faithful.ChipOracle
import SP1Clean.Extracted.ChipOracle.Subw
import SP1Clean.Native.Chips.SubwChip.Defs
import SP1Clean.Proofs.Chips.SubwChip.Formal
import SP1Clean.Model.InteractionRecovery

/-! # Whole-chip faithfulness anchor — native SUBW row ↔ SP1 Rust Subw AIR

The public boundary is `subwChip_faithful`: it compares the complete native chip assertion system and
four-bus interaction multiset with the complete extracted Rust chip oracle after one explicit row
reconfiguration. The generated Rust expression still contains operation/reader helper calls, but those
are unfolded only in private calculations below. They are not correspondence claims about the native
Lean gadget decomposition. -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Whole-chip row reconfiguration. The reader blocks are already the canonical generated substrate,
so only the native arithmetic block (two witnessed low limbs + the composed sign bit) is copied into
Rust's chip-private operation row. This is not an operation-level faithfulness claim. -/
def subwChipReconfigure {F : Type} (cols : SubwChip.Columns F) :
    Extracted.SubwOracle.SubwCols F :=
  { state := cols.state
    adapter := cols.adapter
    subw_operation :=
      { value := cols.subw_operation.value
        msb := { msb := cols.subw_operation.msb.msb } }
    is_real := cols.is_real }

/-- Inverse whole-row map used to reconstruct the native proof row from an arbitrary Rust row. -/
def subwChipDeconfigure {F : Type} (cols : Extracted.SubwOracle.SubwCols F) :
    SubwChip.Columns F :=
  { is_real := cols.is_real
    state := cols.state
    adapter := cols.adapter
    subw_operation :=
      { value := cols.subw_operation.value
        msb := { msb := cols.subw_operation.msb.msb } } }

/-- SP1 Rust's complete Subw-chip oracle, viewed from the native Lean row. -/
def subwChipOracle {F : Type} [FiniteField F] [CoeHead F ℕ] :
    ChipOracle F SubwChip.Columns Extracted.SubwOracle.SubwCols where
  reconfigure := subwChipReconfigure
  deconfigure := subwChipDeconfigure
  reconfigure_deconfigure := by intro cols; cases cols; rfl
  deconfigure_reconfigure := by intro cols; cases cols; rfl
  assertZeros := Extracted.SubwOracle.SubwCols.asserts
  interactions := Extracted.SubwOracle.SubwCols.interactions

/-- Native input decoded from a complete SUBW row. -/
def subwChipInput {F : Type} (cols : SubwChip.Columns F) : SubwChip.Inputs F :=
  { is_real := cols.is_real, state := cols.state, adapter := cols.adapter }

/-- The three local witness cells introduced by `SubwChip.main`: the two low result limbs and the
sign bit. -/
def subwChipLocals {F : Type} (cols : SubwChip.Columns F) : Vector F 3 :=
  #v[cols.subw_operation.value[0], cols.subw_operation.value[1],
    cols.subw_operation.msb.msb]

/-- Clean input-first physical row for SUBW. -/
def subwChipPhysicalRow {F : Type} (cols : SubwChip.Columns F) : Array F :=
  inputFirstRow (subwChipInput cols) (subwChipLocals cols)

/-- Assemble the native row represented by an input prefix and the three SUBW local witnesses. -/
def subwChipColumnsOfInput {F : Type} (input : SubwChip.Inputs F)
    (locals : Vector F 3) : SubwChip.Columns F :=
  ⟨input.is_real, input.state, input.adapter, ⟨#v[locals[0], locals[1]], ⟨locals[2]⟩⟩⟩

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

theorem subwChipColumnsOfInput_roundtrip {F : Type} (cols : SubwChip.Columns F) :
    subwChipColumnsOfInput (subwChipInput cols) (subwChipLocals cols) = cols := by
  cases cols with
  | mk isReal state adapter operation =>
      cases operation with
      | mk value msb =>
          cases msb with
          | mk msbValue =>
              change
                (⟨isReal, state, adapter, ⟨#v[value[0], value[1]], ⟨msbValue⟩⟩⟩ :
                    SubwChip.Columns F) =
                  ⟨isReal, state, adapter, ⟨value, ⟨msbValue⟩⟩⟩
              rw [vec2_eta]

@[circuit_norm] theorem eval_extractedU16MSBOperation_subw {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.U16MSBOperation (Expression F)) :
    Eval.eval env cols =
      ({ msb := Eval.eval env cols.msb } : Extracted.U16MSBOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] theorem eval_subwOperationColumns {F : Type} [FiniteField F]
    (env : Environment F) (cols : SubwOperation.Columns (Expression F)) :
    Eval.eval env cols =
      ({ value := Eval.eval env cols.value, msb := Eval.eval env cols.msb } :
        SubwOperation.Columns F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] theorem eval_subwOperationColumns_value {F : Type} [FiniteField F]
    (env : Environment F) (cols : SubwOperation.Columns (Expression F)) :
    (Eval.eval env cols).value = Eval.eval env cols.value := by
  rw [eval_subwOperationColumns]

@[circuit_norm] theorem eval_subwOperationColumns_msb {F : Type} [FiniteField F]
    (env : Environment F) (cols : SubwOperation.Columns (Expression F)) :
    (Eval.eval env cols).msb.msb = Eval.eval env cols.msb.msb := by
  rw [eval_subwOperationColumns, eval_extractedU16MSBOperation_subw]

@[circuit_norm] theorem eval_subwOperationInputs {F : Type} [FiniteField F]
    (env : Environment F) (input : SubwOperation.Inputs (Expression F)) :
    Eval.eval env input =
      ({ a := Eval.eval env input.a, b := Eval.eval env input.b,
         cols := Eval.eval env input.cols, is_real := Eval.eval env input.is_real } :
        SubwOperation.Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

/-- Abstract evaluation lemma for the physical SUBW row. Keeping the input and local suffix symbolic
prevents the kernel from unfolding a concrete nested row while checking every codec instance. -/
theorem eval_subwChipDirectOutput
    (input : SubwChip.Inputs (ZMod p)) (locals : Vector (ZMod p) 3)
    (data : ProverData (ZMod p)) :
    ProvableType.eval (Environment.fromArray (inputFirstRow input locals) data)
        ((SubwChip.elaborated (p := p)).output
          (varFromOffset SubwChip.Inputs 0) (size SubwChip.Inputs)) =
      subwChipColumnsOfInput input locals := by
  rw [SubwChip.directOutput_eq]
  rw [← CircuitType.eval_expression, SubwChip.eval_columns]
  unfold subwChipColumnsOfInput
  rw [SubwChip.Columns.mk.injEq]
  dsimp only
  have hinputEval := eval_inputFirstRow input locals data
  rw [SubwChip.eval_inputs, SubwChip.Inputs.mk.injEq] at hinputEval
  constructor
  · exact hinputEval.1
  constructor
  · exact hinputEval.2.1
  constructor
  · exact hinputEval.2.2
  rw [SubwOperation.Columns.mk.injEq]
  constructor
  · rw [eval_subwOperationColumns_value]
    ext i hi
    interval_cases i
    · rw [← ProvableType.getElem_eval_fields
        (Environment.fromArray (inputFirstRow input locals) data)
        (Vector.mapRange 2 fun i => var { index := size SubwChip.Inputs + i })
        0 (by decide), Vector.getElem_mapRange]
      exact eval_local_inputFirstRow input locals data 0 (by decide)
    · rw [← ProvableType.getElem_eval_fields
        (Environment.fromArray (inputFirstRow input locals) data)
        (Vector.mapRange 2 fun i => var { index := size SubwChip.Inputs + i })
        1 (by decide), Vector.getElem_mapRange]
      exact eval_local_inputFirstRow input locals data 1 (by decide)
  · rw [Extracted.U16MSBOperation.mk.injEq]
    simpa only [eval_subwOperationColumns, eval_extractedU16MSBOperation_subw,
      ProvableType.eval_field] using
        (eval_local_inputFirstRow input locals data 2 (by decide))

/-- Constructive native-row codec for SUBW. -/
def subwChipRowCodec : ChipRowCodec SubwChip.Inputs SubwChip.Columns
    (SubwChip.circuit (p := p)) where
  assignment cols data := {
    row := subwChipPhysicalRow cols
    input := subwChipInput cols
    width_eq := by
      rw [subwChipPhysicalRow, inputFirstRow_size, Air.Flat.Component.width,
        SubwChip.circuit_size_eq]
    rowInput_eq := by
      exact rowInput_inputFirstRow (SubwChip.circuit (p := p)) (subwChipInput cols)
        (subwChipLocals cols) data
    rowOutput_eq := by
      change ProvableType.eval _ ((SubwChip.main _).output _) = _
      rw [SubwChip.elaborated.output_eq]
      rw [Air.Flat.Component.rowInputVar_mk, Air.Flat.Component.rowOffset_mk]
      exact (eval_subwChipDirectOutput (p := p) (subwChipInput cols)
        (subwChipLocals cols) data).trans (subwChipColumnsOfInput_roundtrip cols) }

/-- SUBW uses SP1 bus interactions for byte/range checks and contains no separate Clean lookup. -/
theorem subwChip_lookups_empty :
    (⟨SubwChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).operations.lookups = [] := by
  rw [Air.Flat.Component.lookups_eq, Air.Flat.Component.rowOperations_mk,
    SubwChip.circuit_main_eq]
  simp [SubwChip.main, Readers.CPUState.circuit, Readers.CPUState.main,
    Readers.RTypeReader.circuit, Readers.RTypeReader.main,
    Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    SubwOperation.circuit, SubwOperation.main, U16MSBOperation.circuit,
    U16MSBOperation.main, Gadgets.Equality.main, circuit_norm]

open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel StateMsg)
open SP1Clean.InteractionRecovery

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
/-- **Chip-level faithfulness anchor — State-bus interactions, SYNTACTIC.** The State interactions the
whole `SubwChip` row emits (recovered by descending the chip into its three composed sub-readers) project
to the same `LookupAccess` list as the State entries of SP1's extracted `SubwCols.interactions` oracle.
Only the `CPUState` fragment emits State, so this is a clean `=` (no fragment-reorder `Perm`); the `Add`
and `RTypeReader` byte/memory/program emits drop under the `State` channel filter. Witness-free (the
State bus does not touch the witnessed ALU result). -/
private theorem subwcols_state_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var SubwChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : SubwChip.Columns (ZMod p))
    (h_ir : Expression.eval env input.is_real = cols.is_real)
    (h_ch : Expression.eval env input.state.clk_high = cols.state.clk_high)
    (h_c0 : Expression.eval env input.state.clk_0_16 = cols.state.clk_0_16)
    (h_c1 : Expression.eval env input.state.clk_16_24 = cols.state.clk_16_24)
    (h_p0 : Expression.eval env input.state.pc[0] = cols.state.pc[0])
    (h_p1 : Expression.eval env input.state.pc[1] = cols.state.pc[1])
    (h_p2 : Expression.eval env input.state.pc[2] = cols.state.pc[2]) :
    (((SubwChip.main input).operations offset).interactionsWith stateChannel.toRaw).map
        (AbstractInteraction.toAccess env)
      = ((Extracted.SubwOracle.SubwCols.interactions (subwChipReconfigure cols)).map
          Extracted.Interaction.toAccess).filter
          (fun a => a.1 = InteractionKind.State) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hsk : ∀ (m : Expression (ZMod p)) (s : StateMsg (Expression (ZMod p))),
      AbstractInteraction.toAccess env ((stateChannel.pushedIf m s).toRaw) =
        (InteractionKind.State, "SP1State",
          [(Expression.eval env s.clk_high).val, (Expression.eval env s.clk_low).val,
           (Expression.eval env s.pc0).val, (Expression.eval env s.pc1).val,
           (Expression.eval env s.pc2).val], signedVal (Expression.eval env m)) :=
    fun m s => toAccess_pushIf_state env m s
  have hsk_pull : ∀ (g : Expression (ZMod p)) (s : StateMsg (Expression (ZMod p))),
      AbstractInteraction.toAccess env ((stateChannel.pulledIf g s).toRaw) =
        (InteractionKind.State, "SP1State",
          [(Expression.eval env s.clk_high).val, (Expression.eval env s.clk_low).val,
           (Expression.eval env s.pc0).val, (Expression.eval env s.pc1).val,
           (Expression.eval env s.pc2).val], signedVal (Expression.eval env (-g))) :=
    fun g s => toAccess_pullIf_state env g s
  have heq := fun (n : ℕ) (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil (ZMod p) _ (ProvablePair field field)
      ProvablePair.instance (Gadgets.Equality.circuit field) stateChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  -- descend the chip into its three sub-readers; the `Add`/`RTypeReader` byte/mem/program emits drop under
  -- the `State` filter (channel distinctness), leaving CPUState's two State interactions.
  simp only [SubwChip.main, Readers.CPUState.circuit, Readers.CPUState.main,
    Readers.RTypeReader.circuit, Readers.RTypeReader.main,
    Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    SP1Clean.SubwOperation.circuit, SP1Clean.SubwOperation.main,
    SP1Clean.U16MSBOperation.circuit, SP1Clean.U16MSBOperation.main,
    circuit_norm, FormalAssertion.toSubcircuit_interactions, GeneralFormalCircuit.toSubcircuit_interactions, hsk, hsk_pull, heq]
  -- the residual: CPUState's 2 State interactions (via `hsk`), everything else dropped by the `State`
  -- filter (byte/mem/program channel distinctness) or emitting nothing (`Gadgets.Equality.main`); the
  -- oracle `.filter .State` likewise keeps only the CPUState fragment's 2 State entries.
  simp [circuit_norm, hsk, hsk_pull, toAccess_pushIf_state, toAccess_pullIf_state,
    Gadgets.Equality.main,
    subwChipReconfigure, Extracted.SubwOracle.SubwCols.interactions,
    Extracted.SubwOracle.SubwOperation.interactions,
    Extracted.SubwOracle.U16MSBOperation.interactions,
    Extracted.CPUState.interactions, Extracted.RTypeReader.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    h_ir, h_ch, h_c0, h_c1, h_p0, h_p1, h_p2]

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
/-- **Chip-level faithfulness anchor — Program-bus interaction, SYNTACTIC.** The single Program
instruction-fetch the whole `SubwChip` row emits (only the `RTypeReader` fragment emits Program) projects
to the same arity-16 `LookupAccess` as the Program entry of SP1's extracted `SubwCols.interactions`
oracle. Witness-free (the Program tuple is the decoded instruction, not the ALU result). -/
private theorem subwcols_program_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var SubwChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : SubwChip.Columns (ZMod p))
    (h_ir : Expression.eval env input.is_real = cols.is_real)
    (h_p0 : Expression.eval env input.state.pc[0] = cols.state.pc[0])
    (h_p1 : Expression.eval env input.state.pc[1] = cols.state.pc[1])
    (h_p2 : Expression.eval env input.state.pc[2] = cols.state.pc[2])
    (h_oa : Expression.eval env input.adapter.op_a = cols.adapter.op_a)
    (h_ob : Expression.eval env input.adapter.op_b = cols.adapter.op_b)
    (h_oc : Expression.eval env input.adapter.op_c = cols.adapter.op_c)
    (h_oa0 : Expression.eval env input.adapter.op_a_0 = cols.adapter.op_a_0) :
    (((SubwChip.main input).operations offset).interactionsWith programChannel.toRaw).map
        (AbstractInteraction.toAccess env)
      = (((Extracted.SubwOracle.SubwCols.interactions (subwChipReconfigure cols)).map
          Extracted.Interaction.toAccess).filter
          (fun a => a.1 = InteractionKind.Program)).map LookupAccessList.negMult := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp2 : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have heq := fun (n : ℕ) (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil (ZMod p) _ (ProvablePair field field)
      ProvablePair.instance (Gadgets.Equality.circuit field) programChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  -- SC Phase 2a: unfold the `Channel` kernel's `pulledIf` to match `circuit_norm`'s raw recovery.
  have hk := fun (g : Expression (ZMod p)) (m : SP1Clean.Channels.ProgramMsg (Expression (ZMod p))) =>
    toAccess_pullIf_program env g m
  simp only [SubwChip.main, Readers.CPUState.circuit, Readers.CPUState.main,
    Readers.RTypeReader.circuit, Readers.RTypeReader.main,
    Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    SP1Clean.SubwOperation.circuit, SP1Clean.SubwOperation.main,
    SP1Clean.U16MSBOperation.circuit, SP1Clean.U16MSBOperation.main,
    circuit_norm, FormalAssertion.toSubcircuit_interactions, GeneralFormalCircuit.toSubcircuit_interactions, hk, heq]
  -- only RTypeReader's Program emit survives the `Program` filter; close via the kernel + bindings + the
  -- opcode coercion (`Opcode.ofNat 0 = 0`), then drop the byte/state/memory residual by channel name. The
  -- emit is now a `pull` (W11 flip), so its multiplicity is `-is_real` — matched by `negMult` on the oracle.
  simp [circuit_norm, hk, Gadgets.Equality.main, LookupAccessList.negMult,
    signedVal_neg hp2,
    subwChipReconfigure, Extracted.SubwOracle.SubwCols.interactions,
    Extracted.SubwOracle.SubwOperation.interactions,
    Extracted.SubwOracle.U16MSBOperation.interactions,
    Extracted.CPUState.interactions, Extracted.RTypeReader.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign, Opcode.ofNat, ConstraintCoe.coe_eq_val,
    h_ir, h_p0, h_p1, h_p2, h_oa, h_ob, h_oc, h_oa0]

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
/-- **Chip-level faithfulness anchor — Memory-bus interactions, SYNTACTIC (composition + WITNESSED + `Perm`
+ `negMult`).** The six Memory interactions the whole `SubwChip` row emits — `RTypeReader`'s five reads
(op_a read, op_b read+write-back, op_c read+write-back) **plus** `RegisterWrite`'s op_a write (Option B:
the write factored out, composed after `SubwOperation`) — project, after the W11-flip `negMult` sign-bridge,
to a `List.Perm` of the Memory entries of SP1's extracted `SubwCols.interactions` oracle. As `AddChip`/`SubChip`:
(1) the reads/writes are `pullIf`/`pushIf` (the negation of SP1's send/receive), so the whole emitted block is
`negMult`-bridged; (2) the op_a write trails the block (it comes from the separate `RegisterWrite`
sub-assertion) whereas the oracle lists it second — a `List.Perm`, not `=`. The op_a write value is the
chip-**witnessed** sign-extended result `[value[0], value[1], msb·65535, msb·65535]`, bound via
`env.get (offset + k)` (`h_wv0`/`h_wv1`/`h_msb`). -/
private theorem subwcols_memory_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var SubwChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : SubwChip.Columns (ZMod p))
    (h_ir : Expression.eval env input.is_real = cols.is_real)
    (h_ch : Expression.eval env input.state.clk_high = cols.state.clk_high)
    (h_c0 : Expression.eval env input.state.clk_0_16 = cols.state.clk_0_16)
    (h_c1 : Expression.eval env input.state.clk_16_24 = cols.state.clk_16_24)
    (h_oa : Expression.eval env input.adapter.op_a = cols.adapter.op_a)
    (h_ob : Expression.eval env input.adapter.op_b = cols.adapter.op_b)
    (h_oc : Expression.eval env input.adapter.op_c = cols.adapter.op_c)
    (h_wv0 : env.get offset = cols.subw_operation.value[0])
    (h_wv1 : env.get (offset + 1) = cols.subw_operation.value[1])
    (h_msb : env.get (offset + 2) = cols.subw_operation.msb.msb)
    (h_pl_a : Expression.eval env input.adapter.op_a_memory.access_timestamp.prev_low =
      cols.adapter.op_a_memory.access_timestamp.prev_low)
    (h_pv_a0 : Expression.eval env input.adapter.op_a_memory.prev_value[0] = cols.adapter.op_a_memory.prev_value[0])
    (h_pv_a1 : Expression.eval env input.adapter.op_a_memory.prev_value[1] = cols.adapter.op_a_memory.prev_value[1])
    (h_pv_a2 : Expression.eval env input.adapter.op_a_memory.prev_value[2] = cols.adapter.op_a_memory.prev_value[2])
    (h_pv_a3 : Expression.eval env input.adapter.op_a_memory.prev_value[3] = cols.adapter.op_a_memory.prev_value[3])
    (h_pl_b : Expression.eval env input.adapter.op_b_memory.access_timestamp.prev_low =
      cols.adapter.op_b_memory.access_timestamp.prev_low)
    (h_pv_b0 : Expression.eval env input.adapter.op_b_memory.prev_value[0] = cols.adapter.op_b_memory.prev_value[0])
    (h_pv_b1 : Expression.eval env input.adapter.op_b_memory.prev_value[1] = cols.adapter.op_b_memory.prev_value[1])
    (h_pv_b2 : Expression.eval env input.adapter.op_b_memory.prev_value[2] = cols.adapter.op_b_memory.prev_value[2])
    (h_pv_b3 : Expression.eval env input.adapter.op_b_memory.prev_value[3] = cols.adapter.op_b_memory.prev_value[3])
    (h_pl_c : Expression.eval env input.adapter.op_c_memory.access_timestamp.prev_low =
      cols.adapter.op_c_memory.access_timestamp.prev_low)
    (h_pv_c0 : Expression.eval env input.adapter.op_c_memory.prev_value[0] = cols.adapter.op_c_memory.prev_value[0])
    (h_pv_c1 : Expression.eval env input.adapter.op_c_memory.prev_value[1] = cols.adapter.op_c_memory.prev_value[1])
    (h_pv_c2 : Expression.eval env input.adapter.op_c_memory.prev_value[2] = cols.adapter.op_c_memory.prev_value[2])
    (h_pv_c3 : Expression.eval env input.adapter.op_c_memory.prev_value[3] = cols.adapter.op_c_memory.prev_value[3]) :
    List.Perm
      (((((SubwChip.main input).operations offset).interactionsWith memoryChannel.toRaw).map
          (AbstractInteraction.toAccess env)).map LookupAccessList.negMult)
      (((Extracted.SubwOracle.SubwCols.interactions (subwChipReconfigure cols)).map
          Extracted.Interaction.toAccess).filter
          (fun a => a.1 = InteractionKind.Memory)) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp2 : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have heq := fun (n : ℕ) (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil (ZMod p) _ (ProvablePair field field)
      ProvablePair.instance (Gadgets.Equality.circuit field) memoryChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  simp only [SubwChip.main, Readers.CPUState.circuit, Readers.CPUState.main,
    Readers.RTypeReader.circuit, Readers.RTypeReader.main,
    Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    SP1Clean.SubwOperation.circuit, SP1Clean.SubwOperation.main,
    SP1Clean.U16MSBOperation.circuit, SP1Clean.U16MSBOperation.main,
    circuit_norm, FormalAssertion.toSubcircuit_interactions, GeneralFormalCircuit.toSubcircuit_interactions,
    toAccess_pushIf_memory, toAccess_pullIf_memory, heq]
  simp [circuit_norm, toAccess_pushIf_memory, toAccess_pullIf_memory, Gadgets.Equality.main,
    LookupAccessList.negMult, signedVal_neg hp2,
    subwChipReconfigure, Extracted.SubwOracle.SubwCols.interactions,
    Extracted.SubwOracle.SubwOperation.interactions,
    Extracted.SubwOracle.U16MSBOperation.interactions,
    Extracted.CPUState.interactions, Extracted.RTypeReader.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    h_ir, h_ch, h_c0, h_c1, h_oa, h_ob, h_oc,
    h_wv0, h_wv1, h_msb, h_pl_a, h_pv_a0, h_pv_a1, h_pv_a2, h_pv_a3,
    h_pl_b, h_pv_b0, h_pv_b1, h_pv_b2, h_pv_b3,
    h_pl_c, h_pv_c0, h_pv_c1, h_pv_c2, h_pv_c3]
  -- circuit `[op_b read, op_b write, op_c read, op_c write, op_a write]` vs oracle
  -- `[op_a write, op_b read, op_b write, op_c read, op_c write]` (common op_a read head stripped);
  -- rotate the relocated op_a write (`RegisterWrite`) to the front.
  exact List.perm_append_comm (l₁ := [_, _, _, _]) (l₂ := [_])

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
/-- **Chip-level faithfulness anchor — Byte-bus interactions, SYNTACTIC (multi-fragment `Perm` + WITNESSED).**
All three fragments emit byte: `CPUState` (2 clock checks), `SubwOperation` (the `U16MSB` sign check + 2
result-limb ranges on the chip-**witnessed** ALU `value`), `RTypeReader` (6 timestamp checks). The circuit
emits them in order `[CPUState 2] ++ [Subw 3] ++ [RTypeReader 6]`, the oracle lists
`[Subw 3] ++ [CPUState 2] ++ [RTypeReader 6]` — the first two blocks swapped, so this is a `List.Perm`
(the bus is a multiset). The `Subw` block's `value[k]`/`msb` are bound via `env.get (offset + k)`. -/
private theorem subwcols_byte_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var SubwChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : SubwChip.Columns (ZMod p))
    (h_ir : Expression.eval env input.is_real = cols.is_real)
    (h_c0 : Expression.eval env input.state.clk_0_16 = cols.state.clk_0_16)
    (h_c1 : Expression.eval env input.state.clk_16_24 = cols.state.clk_16_24)
    (h_wv0 : env.get offset = cols.subw_operation.value[0])
    (h_wv1 : env.get (offset + 1) = cols.subw_operation.value[1])
    (h_msb : env.get (offset + 2) = cols.subw_operation.msb.msb)
    (h_pl_a : Expression.eval env input.adapter.op_a_memory.access_timestamp.prev_low =
      cols.adapter.op_a_memory.access_timestamp.prev_low)
    (h_dl_a : Expression.eval env input.adapter.op_a_memory.access_timestamp.diff_low_limb =
      cols.adapter.op_a_memory.access_timestamp.diff_low_limb)
    (h_pl_b : Expression.eval env input.adapter.op_b_memory.access_timestamp.prev_low =
      cols.adapter.op_b_memory.access_timestamp.prev_low)
    (h_dl_b : Expression.eval env input.adapter.op_b_memory.access_timestamp.diff_low_limb =
      cols.adapter.op_b_memory.access_timestamp.diff_low_limb)
    (h_pl_c : Expression.eval env input.adapter.op_c_memory.access_timestamp.prev_low =
      cols.adapter.op_c_memory.access_timestamp.prev_low)
    (h_dl_c : Expression.eval env input.adapter.op_c_memory.access_timestamp.diff_low_limb =
      cols.adapter.op_c_memory.access_timestamp.diff_low_limb) :
    List.Perm
      ((((SubwChip.main input).operations offset).interactionsWith byteChannel.toRaw).map
        (AbstractInteraction.toAccess env))
      (((Extracted.SubwOracle.SubwCols.interactions (subwChipReconfigure cols)).map
          Extracted.Interaction.toAccess).filter
          (fun a => a.1 = InteractionKind.Byte)) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h6 : (6 : ZMod p).val = 6 := by
    have h : (6 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt h
  have h3 : (3 : ZMod p).val = 3 := by
    have h : (3 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt h
  have hk : ∀ (g : Expression (ZMod p)) (s : ByteRow (Expression (ZMod p))),
      AbstractInteraction.toAccess env ((pulledIf (channel := byteChannel) g s).toRaw) =
        (InteractionKind.Byte, "SP1Byte",
          [(Expression.eval env s.opcode).val, (Expression.eval env s.a).val,
           (Expression.eval env s.b).val, (Expression.eval env s.c).val],
          signedVal (Expression.eval env (-g))) :=
    fun g s => toAccess_pullIf_byte env g s
  have heq := fun (n : ℕ) (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil (ZMod p) _ (ProvablePair field field)
      ProvablePair.instance (Gadgets.Equality.circuit field) byteChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  simp only [SubwChip.main, Readers.CPUState.circuit, Readers.CPUState.main,
    Readers.RTypeReader.circuit, Readers.RTypeReader.main,
    Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    SP1Clean.SubwOperation.circuit, SP1Clean.SubwOperation.main,
    SP1Clean.U16MSBOperation.circuit, SP1Clean.U16MSBOperation.main,
    circuit_norm, FormalAssertion.toSubcircuit_interactions, GeneralFormalCircuit.toSubcircuit_interactions, hk, heq]
  simp [circuit_norm, hk, Gadgets.Equality.main,
    subwChipReconfigure, Extracted.SubwOracle.SubwCols.interactions,
    Extracted.SubwOracle.SubwOperation.interactions,
    Extracted.SubwOracle.U16MSBOperation.interactions,
    Extracted.CPUState.interactions, Extracted.RTypeReader.interactions,
    Extracted.Interaction.toAccess_byte, Extracted.Interaction.toAccess, Extracted.Dir.sign,
    ZMod.val_zero,
    h_ir, h_c0, h_c1, h_wv0, h_wv1, h_msb,
    h_pl_a, h_dl_a, h_pl_b, h_dl_b, h_pl_c, h_dl_c, h6, h3]
  -- circuit `[CPUState 2] ++ [Subw 3] ++ [RTypeReader 6]` vs oracle `[Subw 3] ++ [CPUState 2] ++ [RT 6]`:
  -- swap the first two blocks (the `RTypeReader 6` tail is shared).
  exact (List.perm_append_comm (l₁ := [_, _]) (l₂ := [_, _, _])).append_right [_, _, _, _, _, _]

set_option maxHeartbeats 2000000 in
/-- **Chip-level faithfulness anchor — COMBINED, SYNTACTIC.** The full faithfulness statement for `SubwChip`:
the interactions the row emits on its four buses — `State`, `Byte`, `Memory`, `Program` — taken together
are a `List.Perm` of SP1's *entire* extracted `SubwCols.interactions` oracle (projected to `LookupAccess`).
Assembled from the four per-channel anchors via `perm_filter_by_kind` (which decomposes the oracle image
into its four `InteractionKind` blocks) + `List.Perm.append` (Byte is the only `Perm`; State/Memory/Program
are `=`). No semantics, no channel filter — the complete emitted-interaction list vs the complete oracle. -/
private theorem subwcols_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var SubwChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : SubwChip.Columns (ZMod p))
    (h_ir : Expression.eval env input.is_real = cols.is_real)
    (h_ch : Expression.eval env input.state.clk_high = cols.state.clk_high)
    (h_c0 : Expression.eval env input.state.clk_0_16 = cols.state.clk_0_16)
    (h_c1 : Expression.eval env input.state.clk_16_24 = cols.state.clk_16_24)
    (h_p0 : Expression.eval env input.state.pc[0] = cols.state.pc[0])
    (h_p1 : Expression.eval env input.state.pc[1] = cols.state.pc[1])
    (h_p2 : Expression.eval env input.state.pc[2] = cols.state.pc[2])
    (h_oa : Expression.eval env input.adapter.op_a = cols.adapter.op_a)
    (h_ob : Expression.eval env input.adapter.op_b = cols.adapter.op_b)
    (h_oc : Expression.eval env input.adapter.op_c = cols.adapter.op_c)
    (h_oa0 : Expression.eval env input.adapter.op_a_0 = cols.adapter.op_a_0)
    (h_wv0 : env.get offset = cols.subw_operation.value[0])
    (h_wv1 : env.get (offset + 1) = cols.subw_operation.value[1])
    (h_msb : env.get (offset + 2) = cols.subw_operation.msb.msb)
    (h_pl_a : Expression.eval env input.adapter.op_a_memory.access_timestamp.prev_low =
      cols.adapter.op_a_memory.access_timestamp.prev_low)
    (h_dl_a : Expression.eval env input.adapter.op_a_memory.access_timestamp.diff_low_limb =
      cols.adapter.op_a_memory.access_timestamp.diff_low_limb)
    (h_pv_a0 : Expression.eval env input.adapter.op_a_memory.prev_value[0] = cols.adapter.op_a_memory.prev_value[0])
    (h_pv_a1 : Expression.eval env input.adapter.op_a_memory.prev_value[1] = cols.adapter.op_a_memory.prev_value[1])
    (h_pv_a2 : Expression.eval env input.adapter.op_a_memory.prev_value[2] = cols.adapter.op_a_memory.prev_value[2])
    (h_pv_a3 : Expression.eval env input.adapter.op_a_memory.prev_value[3] = cols.adapter.op_a_memory.prev_value[3])
    (h_pl_b : Expression.eval env input.adapter.op_b_memory.access_timestamp.prev_low =
      cols.adapter.op_b_memory.access_timestamp.prev_low)
    (h_dl_b : Expression.eval env input.adapter.op_b_memory.access_timestamp.diff_low_limb =
      cols.adapter.op_b_memory.access_timestamp.diff_low_limb)
    (h_pv_b0 : Expression.eval env input.adapter.op_b_memory.prev_value[0] = cols.adapter.op_b_memory.prev_value[0])
    (h_pv_b1 : Expression.eval env input.adapter.op_b_memory.prev_value[1] = cols.adapter.op_b_memory.prev_value[1])
    (h_pv_b2 : Expression.eval env input.adapter.op_b_memory.prev_value[2] = cols.adapter.op_b_memory.prev_value[2])
    (h_pv_b3 : Expression.eval env input.adapter.op_b_memory.prev_value[3] = cols.adapter.op_b_memory.prev_value[3])
    (h_pl_c : Expression.eval env input.adapter.op_c_memory.access_timestamp.prev_low =
      cols.adapter.op_c_memory.access_timestamp.prev_low)
    (h_dl_c : Expression.eval env input.adapter.op_c_memory.access_timestamp.diff_low_limb =
      cols.adapter.op_c_memory.access_timestamp.diff_low_limb)
    (h_pv_c0 : Expression.eval env input.adapter.op_c_memory.prev_value[0] = cols.adapter.op_c_memory.prev_value[0])
    (h_pv_c1 : Expression.eval env input.adapter.op_c_memory.prev_value[1] = cols.adapter.op_c_memory.prev_value[1])
    (h_pv_c2 : Expression.eval env input.adapter.op_c_memory.prev_value[2] = cols.adapter.op_c_memory.prev_value[2])
    (h_pv_c3 : Expression.eval env input.adapter.op_c_memory.prev_value[3] = cols.adapter.op_c_memory.prev_value[3]) :
    List.Perm
      (((((SubwChip.main input).operations offset).interactionsWith stateChannel.toRaw).map
          (AbstractInteraction.toAccess env)) ++
        ((((SubwChip.main input).operations offset).interactionsWith byteChannel.toRaw).map
          (AbstractInteraction.toAccess env)) ++
        (((((SubwChip.main input).operations offset).interactionsWith memoryChannel.toRaw).map
          (AbstractInteraction.toAccess env)).map LookupAccessList.negMult) ++
        (((((SubwChip.main input).operations offset).interactionsWith programChannel.toRaw).map
          (AbstractInteraction.toAccess env)).map LookupAccessList.negMult))
      (subwChipOracle.accesses cols) := by
  have hS := subwcols_state_interactions_faithful_syntactic env input offset cols h_ir h_ch h_c0 h_c1 h_p0 h_p1 h_p2
  have hP := subwcols_program_interactions_faithful_syntactic env input offset cols h_ir h_p0 h_p1 h_p2
    h_oa h_ob h_oc h_oa0
  -- The Program block carries one `negMult` (W11 flip: our pull is `-is_real`); re-negating `hP`'s already-
  -- negated oracle block recovers the pristine Program filter, so the whole equation stays vs. SP1's oracle.
  have hP' : ((((SubwChip.main input).operations offset).interactionsWith programChannel.toRaw).map
      (AbstractInteraction.toAccess env)).map LookupAccessList.negMult
      = ((Extracted.SubwOracle.SubwCols.interactions (subwChipReconfigure cols)).map
          Extracted.Interaction.toAccess).filter
          (fun a => a.1 = InteractionKind.Program) := by rw [hP, LookupAccessList.map_negMult_negMult]
  have hM := subwcols_memory_interactions_faithful_syntactic env input offset cols h_ir h_ch h_c0 h_c1
    h_oa h_ob h_oc h_wv0 h_wv1 h_msb h_pl_a h_pv_a0 h_pv_a1 h_pv_a2 h_pv_a3
    h_pl_b h_pv_b0 h_pv_b1 h_pv_b2 h_pv_b3 h_pl_c h_pv_c0 h_pv_c1 h_pv_c2 h_pv_c3
  have hB := subwcols_byte_interactions_faithful_syntactic env input offset cols h_ir h_c0 h_c1
    h_wv0 h_wv1 h_msb h_pl_a h_dl_a h_pl_b h_dl_b h_pl_c h_dl_c
  refine List.Perm.trans ?_ (LookupAccessList.perm_filter_by_kind _).symm
  -- State + Program blocks are clean `=` (`rw`); Byte + Memory are `Perm`s (`hB`/`hM`) threaded through the
  -- append structure (W11 memory flip: the Memory block is now `negMult`-bridged + reordered, like Program).
  rw [hS, hP']
  exact ((hB.append_left _).append hM).append_right _

/- The generated oracle keeps Rust's helper decomposition, whereas the native chip composes its own
Clean gadgets. These private lemmas are deliberately local normalization steps: only the whole-chip
theorem below is part of the faithfulness boundary. -/

set_option maxHeartbeats 1000000 in
private theorem subwOperationAssertions
    (env : Environment (ZMod p)) (input : Var SubwOperation.Inputs (ZMod p))
    (offset : ℕ) (a b : Word (ZMod p)) (cols : SubwOperation.Columns (ZMod p))
    (isReal : ZMod p)
    (ha : (ProvableStruct.eval env input).a = a)
    (hb : (ProvableStruct.eval env input).b = b)
    (hcols : ProvableStruct.eval env input.cols = cols)
    (hreal : (ProvableStruct.eval env input).is_real = isReal) :
    List.Forall (· = 0)
        (Extracted.SubwOracle.SubwOperation.asserts a b
          { value := cols.value, msb := { msb := cols.msb.msb } } isReal) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env ((SubwOperation.main input).operations offset)) := by
  simp [nativeAssertZeros, SubwOperation.main, U16MSBOperation.circuit,
    U16MSBOperation.main, Extracted.SubwOracle.SubwOperation.asserts,
    Extracted.SubwOracle.U16MSBOperation.asserts, Gadgets.Equality.main, circuit_norm]
  have ha0 : Expression.eval env input.a[0] = a[0] := by
    rw [ProvableType.getElem_eval_fields]
    exact congrArg (fun x => x[0]) ha
  have ha1 : Expression.eval env input.a[1] = a[1] := by
    rw [ProvableType.getElem_eval_fields]
    exact congrArg (fun x => x[1]) ha
  have hb0 : Expression.eval env input.b[0] = b[0] := by
    rw [ProvableType.getElem_eval_fields]
    exact congrArg (fun x => x[0]) hb
  have hb1 : Expression.eval env input.b[1] = b[1] := by
    rw [ProvableType.getElem_eval_fields]
    exact congrArg (fun x => x[1]) hb
  have hvalue := congrArg (fun x => x.value) hcols
  have hv0 : Expression.eval env input.cols.value[0] = cols.value[0] := by
    rw [ProvableType.getElem_eval_fields]
    exact congrArg (fun x => x[0]) hvalue
  have hv1 : Expression.eval env input.cols.value[1] = cols.value[1] := by
    rw [ProvableType.getElem_eval_fields]
    exact congrArg (fun x => x[1]) hvalue
  have hmsb : Expression.eval env input.cols.msb.msb = cols.msb.msb := by
    have h := congrArg (fun x => x.msb.msb) hcols
    rw [← ProvableStruct.eval_eq_eval, eval_subwOperationColumns,
      eval_extractedU16MSBOperation_subw] at h
    simpa only [ProvableType.eval_field] using h
  have hr : Expression.eval env input.is_real = isReal := by
    have h := hreal
    rw [← ProvableStruct.eval_eq_eval, eval_subwOperationInputs] at h
    simpa only [ProvableType.eval_field] using h
  have heval (x : Expression (ZMod p)) :
      Expression.eval env (toElements (M := field) x)[0] = Expression.eval env x := rfl
  simp_rw [heval]
  simp only [eval_sub, Expression.eval]
  rw [ha0, ha1, hb0, hb1, hv0, hv1, hmsb, hr, hreal]
  simp

private theorem forall_nil_iff {alpha : Type} (pred : alpha → Prop) :
    List.Forall pred [] ↔ True := Iff.rfl

private def subw_chip_value (offset : ℕ) : Vector (Expression (ZMod p)) 2 :=
  Vector.mapRange 2 fun i => var { index := offset + i }

private def subw_chip_msb (offset : ℕ) : Expression (ZMod p) :=
  var { index := offset + 2 }

set_option maxHeartbeats 1000000 in
private theorem subw_chip_constraints_decompose
    (env : Environment (ZMod p)) (input : Var SubwChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0) (nativeAssertZeros env ((SubwChip.main input).operations offset)) ↔
      (List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.CPUState.main
              ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
                8, input.is_real⟩).operations offset)) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((SubwOperation.main
              ⟨input.op_b_val, input.op_c_val,
                ⟨subw_chip_value offset, ⟨subw_chip_msb offset⟩⟩,
                input.is_real⟩).operations (offset + 3))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.RTypeReader.main
              ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
                input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 20,
                (subw_chip_value offset)[0], (subw_chip_value offset)[1],
                subw_chip_msb offset * 65535, subw_chip_msb offset * 65535⟩).operations
                  (offset + 3))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.RegisterWrite.main
              ⟨input.state.clk_high,
                input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
                input.adapter.op_a,
                #v[(subw_chip_value offset)[0], (subw_chip_value offset)[1],
                  subw_chip_msb offset * 65535, subw_chip_msb offset * 65535],
                input.is_real⟩).operations (offset + 3))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field) (input.adapter.op_a_0, 0)).operations
              (offset + 3))) ∧
        Expression.eval env (input.is_real * (input.is_real - 1)) = 0) := by
  simp only [nativeAssertZeros, SubwChip.main, subw_chip_value, subw_chip_msb,
    Readers.CPUState.circuit, SubwOperation.circuit, Readers.RTypeReader.circuit,
    Readers.RegisterWrite.circuit, circuit_norm, List.map_append, List.forall_append]

set_option maxHeartbeats 4000000 in
/-- **Complete assertion-system anchor for the native SUBW row.** For every verifier environment and
every row bound to the native circuit output, all of SP1 Rust's extracted `assertZero`s vanish iff all
assertions emitted by the complete native Clean chip (including true subcircuits) vanish. This covers
both real and padding rows and exports no operation-level correspondence theorem. -/
theorem subwChip_constraints_faithful
    (env : Environment (ZMod p)) (input : Var SubwChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : SubwChip.Columns (ZMod p))
    (hbind : BindsChipOutput SubwChip.main env input offset cols) :
    List.Forall (· = 0) (subwChipOracle.nativeAssertZeros cols) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env ((SubwChip.main input).operations offset)) := by
  let value : Vector (Expression (ZMod p)) 2 := subw_chip_value offset
  let msb : Expression (ZMod p) := subw_chip_msb offset
  let stateValue := ProvableStruct.eval env input.state
  let adapterValue := ProvableStruct.eval env input.adapter
  let rustValue : Vector (ZMod p) 2 :=
    #v[(Eval.eval env value)[0], (Eval.eval env value)[1]]
  let rustMsb : ZMod p := Eval.eval env msb
  let rustOperation : SubwOperation.Columns (ZMod p) :=
    { value := rustValue, msb := { msb := rustMsb } }
  let rustA : Word (ZMod p) :=
    #v[adapterValue.op_b_memory.prev_value[0], adapterValue.op_b_memory.prev_value[1],
      adapterValue.op_b_memory.prev_value[2], adapterValue.op_b_memory.prev_value[3]]
  let rustB : Word (ZMod p) :=
    #v[adapterValue.op_c_memory.prev_value[0], adapterValue.op_c_memory.prev_value[1],
      adapterValue.op_c_memory.prev_value[2], adapterValue.op_c_memory.prev_value[3]]
  let rustWriteValue : Word (ZMod p) :=
    #v[rustValue[0], rustValue[1], rustMsb * 65535, rustMsb * 65535]
  let isReal := Expression.eval env input.is_real
  let cpuInput : Var Readers.CPUState.Inputs (ZMod p) :=
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
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
  let opInput : Var SubwOperation.Inputs (ZMod p) :=
    ⟨input.op_b_val, input.op_c_val, ⟨value, ⟨msb⟩⟩, input.is_real⟩
  have ha : (ProvableStruct.eval env opInput).a = rustA := by
    simp only [opInput, rustA, adapterValue, SubwChip.Inputs.op_b_val,
      ProvableStruct.structEvalLiteralProc]
    have hOuter : (ProvableStruct.eval env input.adapter).op_b_memory =
        Eval.eval env input.adapter.op_b_memory := rfl
    rw [hOuter, ProvableStruct.eval_eq_eval]
    have hPrev : (ProvableStruct.eval env input.adapter.op_b_memory).prev_value =
        Eval.eval env input.adapter.op_b_memory.prev_value := rfl
    rw [hPrev]
    ext i hi
    interval_cases i <;> simp
  have hb : (ProvableStruct.eval env opInput).b = rustB := by
    simp only [opInput, rustB, adapterValue, SubwChip.Inputs.op_c_val,
      ProvableStruct.structEvalLiteralProc]
    have hOuter : (ProvableStruct.eval env input.adapter).op_c_memory =
        Eval.eval env input.adapter.op_c_memory := rfl
    rw [hOuter, ProvableStruct.eval_eq_eval]
    have hPrev : (ProvableStruct.eval env input.adapter.op_c_memory).prev_value =
        Eval.eval env input.adapter.op_c_memory.prev_value := rfl
    rw [hPrev]
    ext i hi
    interval_cases i <;> simp
  have hOpCols : ProvableStruct.eval env opInput.cols = rustOperation := by
    simp only [opInput, rustOperation, rustValue, rustMsb,
      ProvableStruct.structEvalLiteralProc]
    rw [SubwOperation.Columns.mk.injEq]
    constructor
    · ext i hi
      interval_cases i
      · rfl
      · rfl
    · rw [Extracted.U16MSBOperation.mk.injEq]
      rw [eval_extractedU16MSBOperation_subw]
  have hOp := subwOperationAssertions (p := p) env opInput (offset + 3)
    rustA rustB rustOperation isReal ha hb hOpCols (by
      simp only [opInput, isReal, ProvableStruct.structEvalLiteralProc])
  let rustAdapter : Extracted.RTypeReader (ZMod p) := adapterValue
  let rTypeInput : Var Readers.RTypeReader.Inputs (ZMod p) :=
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 20,
      value[0], value[1], msb * 65535, msb * 65535⟩
  have hopAdapter : Expression.eval env input.adapter.op_a_0 = rustAdapter.op_a_0 := by
    calc
      _ = (Eval.eval env input.adapter).op_a_0 :=
        (Readers.RTypeReader.eval_opA0 env input.adapter).symm
      _ = (ProvableStruct.eval env input.adapter).op_a_0 :=
        congrArg (fun x => x.op_a_0) (ProvableStruct.eval_eq_eval env input.adapter)
      _ = _ := rfl
  have hopEval : Expression.eval env input.adapter.op_a_0 =
      (Eval.eval env input.adapter).op_a_0 :=
    (Readers.RTypeReader.eval_opA0 env input.adapter).symm
  have hRType := CanonicalReader.rTypeAssertions (p := p) env rTypeInput (offset + 3)
    stateValue.clk_high (stateValue.clk_0_16 + stateValue.clk_16_24 * 65536) 20
    isReal isReal #v[stateValue.pc[0], stateValue.pc[1], stateValue.pc[2]]
    rustWriteValue rustAdapter
    (by simp only [rTypeInput, isReal, ProvableStruct.structEvalLiteralProc])
    (by simp only [rTypeInput, isReal, ProvableStruct.structEvalLiteralProc])
    hopAdapter
    (by simpa only [rTypeInput, rustWriteValue, rustValue,
      ProvableStruct.structEvalLiteralProc, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero] using
        (ProvableType.getElem_eval_fields env value 0 (by decide)))
    (by simpa only [rTypeInput, rustWriteValue, rustValue,
      ProvableStruct.structEvalLiteralProc, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ] using
        (ProvableType.getElem_eval_fields env value 1 (by decide)))
    (by simp only [rTypeInput, rustWriteValue, rustMsb,
      ProvableType.eval_field, Expression.eval,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ])
    (by simp only [rTypeInput, rustWriteValue, rustMsb,
      ProvableType.eval_field, Expression.eval,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]) rfl
  let writeInput : Var Readers.RegisterWrite.Inputs (ZMod p) :=
    ⟨input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
      input.adapter.op_a,
      #v[value[0], value[1], msb * 65535, msb * 65535], input.is_real⟩
  replace hbind := BindsChipOutput.ofElaborated (SubwChip.elaborated (p := p)) hbind
  rw [SubwChip.directOutput_eq] at hbind
  simp only [ProvableStruct.structEvalLiteralProc, eval_subwOperationColumns,
    eval_extractedU16MSBOperation_subw] at hbind
  subst cols
  rw [subw_chip_constraints_decompose]
  simp only [ChipOracle.nativeAssertZeros, subwChipOracle, subwChipReconfigure]
  simp only [Extracted.SubwOracle.SubwCols.asserts, List.forall_append, List.forall_cons]
  rw [forall_nil_iff]
  dsimp [rustA, rustB, rustValue, rustMsb, rustOperation, adapterValue,
    isReal, opInput, value, msb, subw_chip_value, subw_chip_msb] at hOp
  dsimp [rustState, rustNextPc, stateValue, isReal, cpuInput] at hCpu
  dsimp [stateValue, rustWriteValue, rustValue, rustMsb, rustAdapter,
    adapterValue, isReal, rTypeInput, value, msb, subw_chip_value,
    subw_chip_msb] at hRType
  simp_rw [← ProvableStruct.eval_eq_eval] at hOp hCpu hRType
  constructor
  · rintro ⟨⟨⟨hOpG, hCpuG⟩, hRTypeG⟩, hGate, hOpA0, _⟩
    have hOpN := hOp.mp hOpG
    have hCpuN := hCpu.mp hCpuG
    have hRTypeN := (hRType.mp
      ⟨(by simpa only [vec4_eta] using hRTypeG), hOpA0⟩).1
    have hWriteN :=
      (CanonicalReader.registerWriteAssertions env writeInput (offset + 3)).mpr trivial
    have hEqSem : Expression.eval env input.adapter.op_a_0 =
        Expression.eval env (0 : Expression (ZMod p)) := by
      rw [hopEval, hOpA0]
      rfl
    have hEqN :=
      (CanonicalReader.equalityAssertions env input.adapter.op_a_0 0
        (offset + 3)).mpr hEqSem
    have hGateN : Expression.eval env (input.is_real * (input.is_real - 1)) = 0 := by
      simpa only [eval_mul, eval_sub, Expression.eval] using hGate
    exact ⟨hCpuN, hOpN, hRTypeN, hWriteN, hEqN, hGateN⟩
  · rintro ⟨hCpuN, hOpN, hRTypeN, _hWriteN, hEqN, hGateN⟩
    have hCpuG := hCpu.mpr hCpuN
    have hOpG := hOp.mpr hOpN
    have hEqSem :=
      (CanonicalReader.equalityAssertions env input.adapter.op_a_0 0
        (offset + 3)).mp hEqN
    have hOpA0 : (Eval.eval env input.adapter).op_a_0 = 0 := by
      rw [← hopEval]
      simpa only [Expression.eval] using hEqSem
    have hRTypeG := (hRType.mpr ⟨hRTypeN, hOpA0⟩).1
    have hGate : Expression.eval env input.is_real *
        (Expression.eval env input.is_real - 1) = 0 := by
      simpa only [eval_mul, eval_sub, Expression.eval] using hGateN
    refine ⟨⟨⟨hOpG, hCpuG⟩, ?_⟩, hGate, hOpA0, trivial⟩
    simpa only [vec4_eta] using hRTypeG

set_option maxHeartbeats 2000000 in
/-- **Complete interaction-system anchor for the native SUBW row.** Binding the circuit output supplies
all column equalities needed by the detailed per-bus calculations above; the public conclusion compares
the canonical four-bus multiset emitted by the native chip with SP1 Rust's complete extracted oracle. -/
theorem subwChip_interactions_faithful
    (env : Environment (ZMod p)) (input : Var SubwChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : SubwChip.Columns (ZMod p))
    (hbind : BindsChipOutput SubwChip.main env input offset cols) :
    List.Perm (nativeAccesses env ((SubwChip.main input).operations offset))
      (subwChipOracle.accesses cols) := by
  replace hbind := BindsChipOutput.ofElaborated (SubwChip.elaborated (p := p)) hbind
  rw [SubwChip.directOutput_eq] at hbind
  simp only [ProvableStruct.structEvalLiteralProc, eval_subwOperationColumns,
    eval_extractedU16MSBOperation_subw] at hbind
  subst cols
  simp only [nativeAccesses]
  have hunexpected :
      unexpectedInteractions ((SubwChip.main input).operations offset) = [] := by
    simp [unexpectedInteractions, SubwChip.main,
      Readers.CPUState.circuit, Readers.CPUState.main,
      Readers.RTypeReader.circuit, Readers.RTypeReader.main,
      Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
      Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
      Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
      SubwOperation.circuit, SubwOperation.main,
      U16MSBOperation.circuit, U16MSBOperation.main, Gadgets.Equality.main,
      FormalAssertion.toSubcircuit_interactions,
      GeneralFormalCircuit.toSubcircuit_interactions, circuit_norm]
  rw [hunexpected]
  simp only [List.map_nil, List.append_nil]
  apply subwcols_interactions_faithful_syntactic
  all_goals
    simp only [eval_cpuState, Readers.RTypeReader.eval_cols,
      eval_registerAccessCols, eval_registerAccessTimestamp,
      ProvableType.eval_field,
      ← ProvableType.getElem_eval_fields, Vector.getElem_mapRange,
      Expression.eval, Nat.add_zero]

set_option maxHeartbeats 2000000 in
/-- The extracted Rust row itself reconstructs a complete satisfying Clean row; no caller-supplied
output binding is part of the public boundary. -/
theorem subwChip_constraints_constructive
    (rustCols : Extracted.SubwOracle.SubwCols (ZMod p)) (data : ProverData (ZMod p)) :
    let assignment := subwChipRowCodec.assignment
      (subwChipOracle.deconfigure rustCols) data
    List.Forall (· = 0) (subwChipOracle.assertZeros rustCols) ↔
      (⟨SubwChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).operations.ConstraintsHold
          assignment.environment := by
  dsimp only
  let cols := subwChipOracle.deconfigure rustCols
  let assignment := subwChipRowCodec.assignment cols data
  have hbind : BindsChipOutput SubwChip.main assignment.environment
      (⟨SubwChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowInputVar
      (⟨SubwChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [SubwChip.circuit_main_eq] at h
    exact h
  have hlegacy := subwChip_constraints_faithful (p := p) assignment.environment
    (⟨SubwChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowInputVar
    (⟨SubwChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowOffset cols hbind
  have hassertions :
      List.Forall (· = 0) (subwChipOracle.assertZeros rustCols) ↔
        List.Forall (· = 0)
          (nativeAssertZeros assignment.environment
            (⟨SubwChip.circuit (p := p)⟩ :
              Air.Flat.Component (ZMod p)).rowOperations) := by
    simpa only [cols, ChipOracle.nativeAssertZeros_deconfigure,
      Air.Flat.Component.rowOperations_mk, Air.Flat.Component.rowInputVar_mk,
      Air.Flat.Component.rowOffset_mk, SubwChip.circuit_main_eq] using hlegacy
  exact hassertions.trans
    (constraintsHold_iff_nativeAssertZeros (SubwChip.circuit (p := p))
      assignment.environment subwChip_lookups_empty).symm

set_option maxHeartbeats 2000000 in
/-- Constructive interaction half of SUBW faithfulness, evaluated on the same reconstructed row. -/
theorem subwChip_interactions_constructive
    (rustCols : Extracted.SubwOracle.SubwCols (ZMod p)) (data : ProverData (ZMod p)) :
    let assignment := subwChipRowCodec.assignment
      (subwChipOracle.deconfigure rustCols) data
    List.Perm
      (nativeAccesses assignment.environment
        (⟨SubwChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).operations)
      (subwChipOracle.rustAccesses rustCols) := by
  dsimp only
  let cols := subwChipOracle.deconfigure rustCols
  let assignment := subwChipRowCodec.assignment cols data
  have hbind : BindsChipOutput SubwChip.main assignment.environment
      (⟨SubwChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowInputVar
      (⟨SubwChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [SubwChip.circuit_main_eq] at h
    exact h
  have hlegacy := subwChip_interactions_faithful (p := p) assignment.environment
    (⟨SubwChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowInputVar
    (⟨SubwChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowOffset cols hbind
  rw [nativeAccesses_component_eq_rowOperations (SubwChip.circuit (p := p))
    assignment.environment]
  simpa only [cols, ChipOracle.accesses_deconfigure,
    Air.Flat.Component.rowOperations_mk, Air.Flat.Component.rowInputVar_mk,
    Air.Flat.Component.rowOffset_mk, SubwChip.circuit_main_eq] using hlegacy

/-- SUBW packaged at the intended stable boundary: native whole-chip circuit versus the complete Rust
whole-chip oracle. Rust operation helpers and Lean gadgets are deliberately absent from the
statement. -/
theorem subwChip_faithful :
    ChipFaithful (p := p) SubwChip.Inputs SubwChip.Columns Extracted.SubwOracle.SubwCols
      SubwChip.circuit subwChipRowCodec subwChipOracle where
  constraints := subwChip_constraints_constructive (p := p)
  interactions := fun rustCols data _ =>
    LookupAccessList.active_perm
      (subwChip_interactions_constructive (p := p) rustCols data)

end SP1Clean.Faithful
