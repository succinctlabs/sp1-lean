import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Faithful.ChipOracle
import SP1Clean.Extracted.ChipOracle.Sub
import SP1Clean.Native.Chips.SubChip.Defs
import SP1Clean.Proofs.Chips.SubChip.Formal
import SP1Clean.Model.InteractionRecovery

/-! # Whole-chip faithfulness anchor — native Sub row ↔ SP1 Rust Sub AIR

The public boundary is `subChip_faithful`: it compares the complete native chip assertion system and
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
so only the native arithmetic block is copied into Rust's chip-private operation row. This is not an
operation-level faithfulness claim. -/
def subChipReconfigure {F : Type} (cols : SubChip.Columns F) : Extracted.SubOracle.SubCols F :=
  { state := cols.state
    adapter := cols.adapter
    sub_operation := { value := cols.sub_operation.value }
    is_real := cols.is_real }

/-- Inverse whole-row map used to reconstruct the native proof row from an arbitrary Rust row. -/
def subChipDeconfigure {F : Type} (cols : Extracted.SubOracle.SubCols F) : SubChip.Columns F :=
  { state := cols.state
    adapter := cols.adapter
    sub_operation := { value := cols.sub_operation.value }
    is_real := cols.is_real }

/-- SP1 Rust's complete Sub-chip oracle, viewed from the native Lean row. -/
def subChipOracle {F : Type} [FiniteField F] [CoeHead F ℕ] :
    ChipOracle F SubChip.Columns Extracted.SubOracle.SubCols where
  reconfigure := subChipReconfigure
  deconfigure := subChipDeconfigure
  reconfigure_deconfigure := by intro cols; cases cols; rfl
  deconfigure_reconfigure := by intro cols; cases cols; rfl
  assertZeros := Extracted.SubOracle.SubCols.asserts
  interactions := Extracted.SubOracle.SubCols.interactions

/-- Native input decoded from a complete Sub row. -/
def subChipInput {F : Type} (cols : SubChip.Columns F) : SubChip.Inputs F :=
  { is_real := cols.is_real, state := cols.state, adapter := cols.adapter }

/-- Clean input-first physical row for Sub. The four arithmetic output limbs are exactly the four
local witnesses introduced by `SubChip.main`. -/
def subChipPhysicalRow {F : Type} (cols : SubChip.Columns F) : Array F :=
  inputFirstRow (subChipInput cols) cols.sub_operation.value

@[circuit_norm] theorem eval_subChipInputs {F : Type} [FiniteField F]
    (env : Environment F) (input : SubChip.Inputs (Expression F)) :
    Eval.eval env input =
      ({ is_real := Eval.eval env input.is_real, state := Eval.eval env input.state,
         adapter := Eval.eval env input.adapter } : SubChip.Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] theorem eval_subOperationColumnsRow {F : Type} [FiniteField F]
    (env : Environment F) (cols : SubOperation.Columns (Expression F)) :
    Eval.eval env cols =
      ({ value := Eval.eval env cols.value } : SubOperation.Columns F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] theorem eval_subChipColumns {F : Type} [FiniteField F]
    (env : Environment F) (cols : SubChip.Columns (Expression F)) :
    Eval.eval env cols =
      ({ is_real := Eval.eval env cols.is_real, state := Eval.eval env cols.state,
         adapter := Eval.eval env cols.adapter,
         sub_operation := Eval.eval env cols.sub_operation } : SubChip.Columns F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

/-- Assemble the native row represented by an input prefix and the four Sub local witnesses. -/
def subChipColumnsOfInput {F : Type} (input : SubChip.Inputs F) (value : Word F) :
    SubChip.Columns F :=
  ⟨input.is_real, input.state, input.adapter, ⟨value⟩⟩

theorem subChipColumnsOfInput_roundtrip {F : Type} (cols : SubChip.Columns F) :
    subChipColumnsOfInput (subChipInput cols) cols.sub_operation.value = cols := by
  cases cols
  rfl

/-- Abstract evaluation lemma for the physical Sub row. Keeping the input and local suffix symbolic
prevents the kernel from unfolding a concrete nested row while checking every codec instance. -/
theorem eval_subChipDirectOutput
    (input : SubChip.Inputs (ZMod p)) (value : Word (ZMod p)) (data : ProverData (ZMod p)) :
    ProvableType.eval (Environment.fromArray (inputFirstRow input value) data)
        ((SubChip.elaborated (p := p)).output
          (varFromOffset SubChip.Inputs 0) (size SubChip.Inputs)) =
      subChipColumnsOfInput input value := by
  rw [SubChip.directOutput_eq]
  rw [← CircuitType.eval_expression, eval_subChipColumns]
  unfold subChipColumnsOfInput
  rw [SubChip.Columns.mk.injEq]
  dsimp only
  have hinputEval := eval_inputFirstRow input value data
  rw [eval_subChipInputs, SubChip.Inputs.mk.injEq] at hinputEval
  constructor
  · exact hinputEval.1
  constructor
  · exact hinputEval.2.1
  constructor
  · exact hinputEval.2.2
  rw [eval_subOperationColumnsRow, SubOperation.Columns.mk.injEq]
  dsimp only
  ext i hi
  rw [← ProvableType.getElem_eval_fields
    (Environment.fromArray (inputFirstRow input value) data)
    (Vector.mapRange 4 fun i => var { index := size SubChip.Inputs + i }) i hi]
  rw [Vector.getElem_mapRange]
  exact eval_local_inputFirstRow input value data i hi

/-- Constructive native-row codec for Sub. -/
def subChipRowCodec : ChipRowCodec SubChip.Inputs SubChip.Columns
    (SubChip.circuit (p := p)) where
  assignment cols data := {
    row := subChipPhysicalRow cols
    input := subChipInput cols
    width_eq := by
      rw [subChipPhysicalRow, inputFirstRow_size, Air.Flat.Component.width,
        SubChip.circuit_size_eq]
    rowInput_eq := by
      exact rowInput_inputFirstRow (SubChip.circuit (p := p)) (subChipInput cols)
        cols.sub_operation.value data
    rowOutput_eq := by
      rw [SubChip.circuit_main_eq]
      rw [SubChip.elaborated.output_eq]
      rw [Air.Flat.Component.rowInputVar_mk, Air.Flat.Component.rowOffset_mk]
      exact (eval_subChipDirectOutput (p := p) (subChipInput cols)
        cols.sub_operation.value data).trans (subChipColumnsOfInput_roundtrip cols) }

/-- Sub uses SP1 bus interactions for byte/range checks and contains no separate Clean lookup. -/
theorem subChip_lookups_empty :
    (⟨SubChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).operations.lookups = [] := by
  rw [Air.Flat.Component.lookups_eq, Air.Flat.Component.rowOperations_mk,
    SubChip.circuit_main_eq]
  simp [SubChip.main, Readers.CPUState.circuit, Readers.CPUState.main,
    Readers.RTypeReader.circuit, Readers.RTypeReader.main,
    Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    SubOperation.circuit, SubOperation.main, Gadgets.Equality.main, circuit_norm]

open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel StateMsg)
open SP1Clean.InteractionRecovery

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
/-- **Chip-level faithfulness anchor — State-bus interactions, SYNTACTIC.** The State interactions the
whole `SubChip` row emits (recovered by descending the chip into its three composed sub-readers) project
to the same `LookupAccess` list as the State entries of SP1's extracted `SubCols.interactions` oracle.
Only the `CPUState` fragment emits State, so this is a clean `=` (no fragment-reorder `Perm`); the `Add`
and `RTypeReader` byte/memory/program emits drop under the `State` channel filter. Witness-free (the
State bus does not touch the witnessed ALU result). -/
private theorem subcols_state_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var SubChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : SubChip.Columns (ZMod p))
    (h_ir : Expression.eval env input.is_real = cols.is_real)
    (h_ch : Expression.eval env input.state.clk_high = cols.state.clk_high)
    (h_c0 : Expression.eval env input.state.clk_0_16 = cols.state.clk_0_16)
    (h_c1 : Expression.eval env input.state.clk_16_24 = cols.state.clk_16_24)
    (h_p0 : Expression.eval env input.state.pc[0] = cols.state.pc[0])
    (h_p1 : Expression.eval env input.state.pc[1] = cols.state.pc[1])
    (h_p2 : Expression.eval env input.state.pc[2] = cols.state.pc[2]) :
    (((SubChip.main input).operations offset).interactionsWith stateChannel.toRaw).map
        (AbstractInteraction.toAccess env)
      = ((Extracted.SubOracle.SubCols.interactions (subChipReconfigure cols)).map
          Extracted.Interaction.toAccess).filter
          (fun a => a.1 = InteractionKind.State) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have heq := fun (n : ℕ) (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil (ZMod p) _ (ProvablePair field field)
      ProvablePair.instance (Gadgets.Equality.circuit field) stateChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  -- descend the chip into its three sub-readers; the `Add`/`RTypeReader` byte/mem/program emits drop under
  -- the `State` filter (channel distinctness), leaving CPUState's two State interactions.
  simp only [SubChip.main, Readers.CPUState.circuit, Readers.CPUState.main,
    Readers.RTypeReader.circuit, Readers.RTypeReader.main,
    Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    SP1Clean.SubOperation.circuit, SP1Clean.SubOperation.main,
    circuit_norm, FormalAssertion.toSubcircuit_interactions, GeneralFormalCircuit.toSubcircuit_interactions,
    toAccess_pushIf_state, toAccess_pullIf_state, heq]
  -- the residual: CPUState's 2 State interactions (via `hsk`), everything else dropped by the `State`
  -- filter (byte/mem/program channel distinctness) or emitting nothing (`Gadgets.Equality.main`); the
  -- oracle `.filter .State` likewise keeps only the CPUState fragment's 2 State entries.
  simp [circuit_norm, toAccess_pushIf_state, toAccess_pullIf_state, Gadgets.Equality.main,
    subChipReconfigure, Extracted.SubOracle.SubCols.interactions,
    Extracted.SubOracle.SubOperation.interactions,
    Extracted.CPUState.interactions, Extracted.RTypeReader.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    h_ir, h_ch, h_c0, h_c1, h_p0, h_p1, h_p2]

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
/-- **Chip-level faithfulness anchor — Program-bus interaction, SYNTACTIC.** The single Program
instruction-fetch the whole `SubChip` row emits (only the `RTypeReader` fragment emits Program) projects
to the same arity-16 `LookupAccess` as the Program entry of SP1's extracted `SubCols.interactions`
oracle. Witness-free (the Program tuple is the decoded instruction, not the ALU result). -/
private theorem subcols_program_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var SubChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : SubChip.Columns (ZMod p))
    (h_ir : Expression.eval env input.is_real = cols.is_real)
    (h_p0 : Expression.eval env input.state.pc[0] = cols.state.pc[0])
    (h_p1 : Expression.eval env input.state.pc[1] = cols.state.pc[1])
    (h_p2 : Expression.eval env input.state.pc[2] = cols.state.pc[2])
    (h_oa : Expression.eval env input.adapter.op_a = cols.adapter.op_a)
    (h_ob : Expression.eval env input.adapter.op_b = cols.adapter.op_b)
    (h_oc : Expression.eval env input.adapter.op_c = cols.adapter.op_c)
    (h_oa0 : Expression.eval env input.adapter.op_a_0 = cols.adapter.op_a_0) :
    (((SubChip.main input).operations offset).interactionsWith programChannel.toRaw).map
        (AbstractInteraction.toAccess env)
      = (((Extracted.SubOracle.SubCols.interactions (subChipReconfigure cols)).map
          Extracted.Interaction.toAccess).filter
          (fun a => a.1 = InteractionKind.Program)).map LookupAccessList.negMult := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp2 : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have heq := fun (n : ℕ) (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil (ZMod p) _ (ProvablePair field field)
      ProvablePair.instance (Gadgets.Equality.circuit field) programChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  -- SC Phase 2a: `programChannel` is a `Channel` — `circuit_norm` recovers the program pull in the raw
  -- `ChannelInteraction` form, so unfold the kernel's `pulledIf` to match it (cf. `StateConsistency`).
  have hk := fun (g : Expression (ZMod p)) (m : SP1Clean.Channels.ProgramMsg (Expression (ZMod p))) =>
    toAccess_pullIf_program env g m
  simp only [SubChip.main, Readers.CPUState.circuit, Readers.CPUState.main,
    Readers.RTypeReader.circuit, Readers.RTypeReader.main,
    Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    SP1Clean.SubOperation.circuit, SP1Clean.SubOperation.main,
    circuit_norm, FormalAssertion.toSubcircuit_interactions, GeneralFormalCircuit.toSubcircuit_interactions, hk, heq]
  -- only RTypeReader's Program emit survives the `Program` filter; close via the kernel + bindings + the
  -- opcode coercion (`Opcode.ofNat 0 = 0`), then drop the byte/state/memory residual by channel name. The
  -- emit is now a `pull` (W11 flip), so its multiplicity is `-is_real` — matched by `negMult` on the oracle.
  simp [circuit_norm, hk, Gadgets.Equality.main, LookupAccessList.negMult,
    signedVal_neg hp2,
    subChipReconfigure, Extracted.SubOracle.SubCols.interactions,
    Extracted.SubOracle.SubOperation.interactions,
    Extracted.CPUState.interactions, Extracted.RTypeReader.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign, Opcode.ofNat, ConstraintCoe.coe_eq_val,
    h_ir, h_p0, h_p1, h_p2, h_oa, h_ob, h_oc, h_oa0]

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
/-- **Chip-level faithfulness anchor — Memory-bus interactions, SYNTACTIC (composition + WITNESSED + `Perm`
+ `negMult`).** The six Memory interactions the whole `SubChip` row emits — `RTypeReader`'s five reads
(op_a read, op_b read+write-back, op_c read+write-back) **plus** `RegisterWrite`'s op_a write (Option B:
the write factored out, composed by the chip after `SubOperation`) — project, after the W11-flip `negMult`
sign-bridge, to a `List.Perm` of the Memory entries of SP1's extracted `SubCols.interactions` oracle. Two
shifts from the old clean `=`: (1) the reads/writes are `pullIf`/`pushIf` (the negation of SP1's
send/receive), so the whole emitted block is `negMult`-bridged; (2) the op_a write now trails the block (it
comes from the separate `RegisterWrite` sub-assertion) whereas the oracle lists it second — so it is a
`List.Perm`, not `=`. The `op_a` write value is the chip-**witnessed** ALU result `cols.sub_operation.value`,
bound via `env.get (offset + k)`. The `clk_low` E4 (`clk_0_16 + clk_16_24 * 2^16`) is from `h_c0`/`h_c1`. -/
private theorem subcols_memory_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var SubChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : SubChip.Columns (ZMod p))
    (h_ir : Expression.eval env input.is_real = cols.is_real)
    (h_ch : Expression.eval env input.state.clk_high = cols.state.clk_high)
    (h_c0 : Expression.eval env input.state.clk_0_16 = cols.state.clk_0_16)
    (h_c1 : Expression.eval env input.state.clk_16_24 = cols.state.clk_16_24)
    (h_oa : Expression.eval env input.adapter.op_a = cols.adapter.op_a)
    (h_ob : Expression.eval env input.adapter.op_b = cols.adapter.op_b)
    (h_oc : Expression.eval env input.adapter.op_c = cols.adapter.op_c)
    (h_wv0 : env.get offset = cols.sub_operation.value[0])
    (h_wv1 : env.get (offset + 1) = cols.sub_operation.value[1])
    (h_wv2 : env.get (offset + 2) = cols.sub_operation.value[2])
    (h_wv3 : env.get (offset + 3) = cols.sub_operation.value[3])
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
      (((((SubChip.main input).operations offset).interactionsWith memoryChannel.toRaw).map
          (AbstractInteraction.toAccess env)).map LookupAccessList.negMult)
      (((Extracted.SubOracle.SubCols.interactions (subChipReconfigure cols)).map
          Extracted.Interaction.toAccess).filter
          (fun a => a.1 = InteractionKind.Memory)) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp2 : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have heq := fun (n : ℕ) (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil (ZMod p) _ (ProvablePair field field)
      ProvablePair.instance (Gadgets.Equality.circuit field) memoryChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  simp only [SubChip.main, Readers.CPUState.circuit, Readers.CPUState.main,
    Readers.RTypeReader.circuit, Readers.RTypeReader.main,
    Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    SP1Clean.SubOperation.circuit, SP1Clean.SubOperation.main,
    circuit_norm, FormalAssertion.toSubcircuit_interactions, GeneralFormalCircuit.toSubcircuit_interactions,
    toAccess_pushIf_memory, toAccess_pullIf_memory, heq]
  simp [circuit_norm, toAccess_pushIf_memory, toAccess_pullIf_memory, Gadgets.Equality.main,
    LookupAccessList.negMult, signedVal_neg hp2,
    subChipReconfigure, Extracted.SubOracle.SubCols.interactions,
    Extracted.SubOracle.SubOperation.interactions,
    Extracted.CPUState.interactions, Extracted.RTypeReader.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    h_ir, h_ch, h_c0, h_c1, h_oa, h_ob, h_oc,
    h_wv0, h_wv1, h_wv2, h_wv3, h_pl_a, h_pv_a0, h_pv_a1, h_pv_a2, h_pv_a3,
    h_pl_b, h_pv_b0, h_pv_b1, h_pv_b2, h_pv_b3,
    h_pl_c, h_pv_c0, h_pv_c1, h_pv_c2, h_pv_c3]
  -- `simp` reduced both sides + stripped the common `op_a read` head. Residual: the circuit's
  -- `[op_b read, op_b write, op_c read, op_c write, op_a write]` vs the oracle's
  -- `[op_a write, op_b read, op_b write, op_c read, op_c write]` — the relocated op_a write (`RegisterWrite`)
  -- trails the circuit block but leads the oracle's, so rotate it to the front (`perm_append_comm`).
  exact List.perm_append_comm (l₁ := [_, _, _, _]) (l₂ := [_])

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
/-- **Chip-level faithfulness anchor — Byte-bus interactions, SYNTACTIC (multi-fragment `Perm` + WITNESSED).**
All three fragments emit byte: `CPUState` (2 clock checks), `SubOperation` (4 result-limb ranges on the
chip-**witnessed** ALU `value`), `RTypeReader` (6 timestamp checks). The circuit emits them in order
`[CPUState 2] ++ [Add 4] ++ [RTypeReader 6]`, the oracle lists `[Add 4] ++ [CPUState 2] ++ [RTypeReader 6]`
— the first two blocks swapped, so this is a `List.Perm` (the bus is a multiset). The `Add` block's
`value[k]` is bound via `env.get (offset + k)`. -/
private theorem subcols_byte_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var SubChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : SubChip.Columns (ZMod p))
    (h_ir : Expression.eval env input.is_real = cols.is_real)
    (h_c0 : Expression.eval env input.state.clk_0_16 = cols.state.clk_0_16)
    (h_c1 : Expression.eval env input.state.clk_16_24 = cols.state.clk_16_24)
    (h_wv0 : env.get offset = cols.sub_operation.value[0])
    (h_wv1 : env.get (offset + 1) = cols.sub_operation.value[1])
    (h_wv2 : env.get (offset + 2) = cols.sub_operation.value[2])
    (h_wv3 : env.get (offset + 3) = cols.sub_operation.value[3])
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
      ((((SubChip.main input).operations offset).interactionsWith byteChannel.toRaw).map
        (AbstractInteraction.toAccess env))
      (((Extracted.SubOracle.SubCols.interactions (subChipReconfigure cols)).map
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
  simp only [SubChip.main, Readers.CPUState.circuit, Readers.CPUState.main,
    Readers.RTypeReader.circuit, Readers.RTypeReader.main,
    Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    SP1Clean.SubOperation.circuit, SP1Clean.SubOperation.main,
    circuit_norm, FormalAssertion.toSubcircuit_interactions, GeneralFormalCircuit.toSubcircuit_interactions, hk, heq]
  simp [circuit_norm, hk, Gadgets.Equality.main,
    subChipReconfigure, Extracted.SubOracle.SubCols.interactions,
    Extracted.SubOracle.SubOperation.interactions,
    Extracted.CPUState.interactions, Extracted.RTypeReader.interactions,
    Extracted.Interaction.toAccess_byte, Extracted.Interaction.toAccess, Extracted.Dir.sign,
    ZMod.val_zero,
    h_ir, h_c0, h_c1, h_wv0, h_wv1, h_wv2, h_wv3,
    h_pl_a, h_dl_a, h_pl_b, h_dl_b, h_pl_c, h_dl_c, h6, h3]
  -- circuit `[CPUState 2] ++ [Add 4] ++ [RTypeReader 6]` vs oracle `[Add 4] ++ [CPUState 2] ++ [RT 6]`:
  -- swap the first two blocks (the `RTypeReader 6` tail is shared).
  exact (List.perm_append_comm (l₁ := [_, _]) (l₂ := [_, _, _, _])).append_right [_, _, _, _, _, _]

set_option maxHeartbeats 2000000 in
/-- **Chip-level faithfulness anchor — COMBINED, SYNTACTIC.** The full faithfulness statement for `SubChip`:
the interactions the row emits on its four buses — `State`, `Byte`, `Memory`, `Program` — taken together
are a `List.Perm` of SP1's *entire* extracted `SubCols.interactions` oracle (projected to `LookupAccess`).
Assembled from the four per-channel anchors via `perm_filter_by_kind` (which decomposes the oracle image
into its four `InteractionKind` blocks) + `List.Perm.append` (Byte is the only `Perm`; State/Memory/Program
are `=`). No semantics, no channel filter — the complete emitted-interaction list vs the complete oracle.
This closes out `SubChip`'s four-artifact chain at the syntactic-interaction level. -/
private theorem subcols_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var SubChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : SubChip.Columns (ZMod p))
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
    (h_wv0 : env.get offset = cols.sub_operation.value[0])
    (h_wv1 : env.get (offset + 1) = cols.sub_operation.value[1])
    (h_wv2 : env.get (offset + 2) = cols.sub_operation.value[2])
    (h_wv3 : env.get (offset + 3) = cols.sub_operation.value[3])
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
      (((((SubChip.main input).operations offset).interactionsWith stateChannel.toRaw).map
          (AbstractInteraction.toAccess env)) ++
        ((((SubChip.main input).operations offset).interactionsWith byteChannel.toRaw).map
          (AbstractInteraction.toAccess env)) ++
        (((((SubChip.main input).operations offset).interactionsWith memoryChannel.toRaw).map
          (AbstractInteraction.toAccess env)).map LookupAccessList.negMult) ++
        (((((SubChip.main input).operations offset).interactionsWith programChannel.toRaw).map
          (AbstractInteraction.toAccess env)).map LookupAccessList.negMult))
      (subChipOracle.accesses cols) := by
  have hS := subcols_state_interactions_faithful_syntactic env input offset cols h_ir h_ch h_c0 h_c1 h_p0 h_p1 h_p2
  have hP := subcols_program_interactions_faithful_syntactic env input offset cols h_ir h_p0 h_p1 h_p2
    h_oa h_ob h_oc h_oa0
  -- The Program block carries one `negMult` (W11 flip: our pull is `-is_real`); re-negating `hP`'s already-
  -- negated oracle block recovers the pristine Program filter, so the whole equation stays vs. SP1's oracle.
  have hP' : ((((SubChip.main input).operations offset).interactionsWith programChannel.toRaw).map
      (AbstractInteraction.toAccess env)).map LookupAccessList.negMult
      = ((Extracted.SubOracle.SubCols.interactions (subChipReconfigure cols)).map
          Extracted.Interaction.toAccess).filter
          (fun a => a.1 = InteractionKind.Program) := by rw [hP, LookupAccessList.map_negMult_negMult]
  have hM := subcols_memory_interactions_faithful_syntactic env input offset cols h_ir h_ch h_c0 h_c1
    h_oa h_ob h_oc h_wv0 h_wv1 h_wv2 h_wv3 h_pl_a h_pv_a0 h_pv_a1 h_pv_a2 h_pv_a3
    h_pl_b h_pv_b0 h_pv_b1 h_pv_b2 h_pv_b3 h_pl_c h_pv_c0 h_pv_c1 h_pv_c2 h_pv_c3
  have hB := subcols_byte_interactions_faithful_syntactic env input offset cols h_ir h_c0 h_c1
    h_wv0 h_wv1 h_wv2 h_wv3 h_pl_a h_dl_a h_pl_b h_dl_b h_pl_c h_dl_c
  refine List.Perm.trans ?_ (LookupAccessList.perm_filter_by_kind _).symm
  -- State + Program blocks are clean `=` (`rw`); Byte + Memory are `Perm`s (`hB`/`hM`) threaded through the
  -- append structure (W11 memory flip: the Memory block is now `negMult`-bridged + reordered, like Program).
  rw [hS, hP']
  exact ((hB.append_left _).append hM).append_right _

/- The generated oracle keeps Rust's helper decomposition, whereas the native chip composes its own
Clean gadgets. These private lemmas are deliberately local normalization steps: only the whole-chip
theorem below is part of the faithfulness boundary. -/

omit [Fact (2 ^ 17 < p)] in
set_option maxHeartbeats 2000000 in
private theorem sub_operation_assertions_local
    (env : Environment (ZMod p)) (input : Var SubOperation.Inputs (ZMod p)) (offset : ℕ)
    (a b value : Word (ZMod p)) (isReal : ZMod p)
    (ha : (ProvableStruct.eval env input).a = a)
    (hb : (ProvableStruct.eval env input).b = b)
    (hv : (ProvableStruct.eval env input.cols).value = value)
    (hr : (ProvableStruct.eval env input).is_real = isReal) :
    List.Forall (· = 0)
        (Extracted.SubOracle.SubOperation.asserts a b { value := value } isReal) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env ((SubOperation.main input).operations offset)) := by
  simp [nativeAssertZeros, SubOperation.main, Extracted.SubOracle.SubOperation.asserts,
    circuit_norm]
  rw [ha, hb, hv, hr]

private theorem forall_nil_iff {alpha : Type} (pred : alpha → Prop) :
    List.Forall pred [] ↔ True := Iff.rfl

private def sub_chip_value (offset : ℕ) : Word (Expression (ZMod p)) :=
  Vector.mapRange 4 fun i => var { index := offset + i }

omit [Fact (2 ^ 17 < p)] in
private theorem eval_sub_operation_columns
    (env : Environment (ZMod p)) (cols : SubOperation.Columns (Expression (ZMod p))) :
    Eval.eval env cols =
      ({ value := Eval.eval env cols.value } : SubOperation.Columns (ZMod p)) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

set_option maxHeartbeats 1000000 in
private theorem sub_chip_constraints_decompose
    (env : Environment (ZMod p)) (input : Var SubChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0) (nativeAssertZeros env ((SubChip.main input).operations offset)) ↔
      (List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.CPUState.main
              ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
                8, input.is_real⟩).operations offset)) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((SubOperation.main
              ⟨input.op_b_val, input.op_c_val, { value := sub_chip_value offset },
                input.is_real⟩).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.RTypeReader.main
              ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
                input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 2,
                (sub_chip_value offset)[0], (sub_chip_value offset)[1],
                (sub_chip_value offset)[2], (sub_chip_value offset)[3]⟩).operations
                  (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.RegisterWrite.main
              ⟨input.state.clk_high,
                input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
                input.adapter.op_a, sub_chip_value offset, input.is_real⟩).operations
                  (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field) (input.adapter.op_a_0, 0)).operations
              (offset + 4))) ∧
        Expression.eval env (input.is_real * (input.is_real - 1)) = 0) := by
  simp only [nativeAssertZeros, SubChip.main, sub_chip_value, Readers.CPUState.circuit,
    SubOperation.circuit, Readers.RTypeReader.circuit, Readers.RegisterWrite.circuit,
    circuit_norm, List.map_append, List.forall_append]

set_option maxHeartbeats 2000000 in
/-- **Complete assertion-system anchor for the native Sub row.** For every verifier environment and
every row bound to the native circuit output, all of SP1 Rust's extracted `assertZero`s vanish iff all
assertions emitted by the complete native Clean chip (including true subcircuits) vanish. This covers
both real and padding rows and exports no operation-level correspondence theorem. -/
theorem subChip_constraints_faithful
    (env : Environment (ZMod p)) (input : Var SubChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : SubChip.Columns (ZMod p))
    (hbind : BindsChipOutput SubChip.main env input offset cols) :
    List.Forall (· = 0) (subChipOracle.nativeAssertZeros cols) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env ((SubChip.main input).operations offset)) := by
  let value : Word (Expression (ZMod p)) := sub_chip_value offset
  let stateValue := ProvableStruct.eval env input.state
  let adapterValue := ProvableStruct.eval env input.adapter
  let valueCols : SubOperation.Columns (ZMod p) :=
    ProvableStruct.eval env
      ({ value := value } : Var SubOperation.Columns (ZMod p))
  let rustValue : Word (ZMod p) :=
    #v[valueCols.value[0], valueCols.value[1], valueCols.value[2], valueCols.value[3]]
  let rustA : Word (ZMod p) :=
    #v[adapterValue.op_b_memory.prev_value[0], adapterValue.op_b_memory.prev_value[1],
      adapterValue.op_b_memory.prev_value[2], adapterValue.op_b_memory.prev_value[3]]
  let rustB : Word (ZMod p) :=
    #v[adapterValue.op_c_memory.prev_value[0], adapterValue.op_c_memory.prev_value[1],
      adapterValue.op_c_memory.prev_value[2], adapterValue.op_c_memory.prev_value[3]]
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
  let subInput : Var SubOperation.Inputs (ZMod p) :=
    ⟨input.op_b_val, input.op_c_val, { value := value }, input.is_real⟩
  have ha : (ProvableStruct.eval env subInput).a = rustA := by
    simp only [subInput, rustA, adapterValue, SubChip.Inputs.op_b_val,
      ProvableStruct.structEvalLiteralProc]
    have hOuter : (ProvableStruct.eval env input.adapter).op_b_memory =
        Eval.eval env input.adapter.op_b_memory := rfl
    rw [hOuter, ProvableStruct.eval_eq_eval]
    have hPrev : (ProvableStruct.eval env input.adapter.op_b_memory).prev_value =
        Eval.eval env input.adapter.op_b_memory.prev_value := rfl
    rw [hPrev]
    ext i hi
    interval_cases i <;> simp
  have hb : (ProvableStruct.eval env subInput).b = rustB := by
    simp only [subInput, rustB, adapterValue, SubChip.Inputs.op_c_val,
      ProvableStruct.structEvalLiteralProc]
    have hOuter : (ProvableStruct.eval env input.adapter).op_c_memory =
        Eval.eval env input.adapter.op_c_memory := rfl
    rw [hOuter, ProvableStruct.eval_eq_eval]
    have hPrev : (ProvableStruct.eval env input.adapter.op_c_memory).prev_value =
        Eval.eval env input.adapter.op_c_memory.prev_value := rfl
    rw [hPrev]
    ext i hi
    interval_cases i <;> simp
  have hv : (ProvableStruct.eval env subInput.cols).value = rustValue := by
    simp only [subInput, rustValue, valueCols, ProvableStruct.structEvalLiteralProc]
    ext i hi
    interval_cases i <;> simp
  have hSub := sub_operation_assertions_local (p := p) env subInput (offset + 4)
    rustA rustB rustValue isReal ha hb hv (by
      simp only [subInput, isReal, ProvableStruct.structEvalLiteralProc])
  let rustAdapter : Extracted.RTypeReader (ZMod p) :=
    { op_a := adapterValue.op_a
      op_a_memory :=
        { prev_value :=
            #v[adapterValue.op_a_memory.prev_value[0], adapterValue.op_a_memory.prev_value[1],
              adapterValue.op_a_memory.prev_value[2], adapterValue.op_a_memory.prev_value[3]]
          access_timestamp := adapterValue.op_a_memory.access_timestamp }
      op_a_0 := adapterValue.op_a_0
      op_b := adapterValue.op_b
      op_b_memory :=
        { prev_value :=
            #v[adapterValue.op_b_memory.prev_value[0], adapterValue.op_b_memory.prev_value[1],
              adapterValue.op_b_memory.prev_value[2], adapterValue.op_b_memory.prev_value[3]]
          access_timestamp := adapterValue.op_b_memory.access_timestamp }
      op_c := adapterValue.op_c
      op_c_memory :=
        { prev_value :=
            #v[adapterValue.op_c_memory.prev_value[0], adapterValue.op_c_memory.prev_value[1],
              adapterValue.op_c_memory.prev_value[2], adapterValue.op_c_memory.prev_value[3]]
          access_timestamp := adapterValue.op_c_memory.access_timestamp } }
  let rtypeInput : Var Readers.RTypeReader.Inputs (ZMod p) :=
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 2,
      value[0], value[1], value[2], value[3]⟩
  have hopAdapter : Expression.eval env input.adapter.op_a_0 = adapterValue.op_a_0 := by
    simp [adapterValue, ProvableStruct.eval, circuit_norm]
  have hRType := CanonicalReader.rTypeAssertions (p := p) env rtypeInput (offset + 4)
    stateValue.clk_high (stateValue.clk_0_16 + stateValue.clk_16_24 * 65536) 2
    isReal isReal #v[stateValue.pc[0], stateValue.pc[1], stateValue.pc[2]]
    rustValue rustAdapter
    (by simp only [rtypeInput, isReal, ProvableStruct.structEvalLiteralProc])
    (by simp only [rtypeInput, isReal, ProvableStruct.structEvalLiteralProc])
    (by simpa only [rtypeInput, rustAdapter] using hopAdapter)
    (by simpa only [rtypeInput, rustValue, valueCols,
      ProvableStruct.structEvalLiteralProc, ProvableType.eval_field,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] using
        (ProvableType.getElem_eval_fields env value 0 (by decide)))
    (by simpa only [rtypeInput, rustValue, valueCols,
      ProvableStruct.structEvalLiteralProc, ProvableType.eval_field,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ] using
        (ProvableType.getElem_eval_fields env value 1 (by decide)))
    (by simpa only [rtypeInput, rustValue, valueCols,
      ProvableStruct.structEvalLiteralProc, ProvableType.eval_field,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ] using
        (ProvableType.getElem_eval_fields env value 2 (by decide)))
    (by simpa only [rtypeInput, rustValue, valueCols,
      ProvableStruct.structEvalLiteralProc, ProvableType.eval_field,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ] using
        (ProvableType.getElem_eval_fields env value 3 (by decide))) rfl
  let writeInput : Var Readers.RegisterWrite.Inputs (ZMod p) :=
    ⟨input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
      input.adapter.op_a, value, input.is_real⟩
  have hopEval : Expression.eval env input.adapter.op_a_0 =
      (Eval.eval env input.adapter).op_a_0 := by
    rw [ProvableStruct.eval_eq_eval]
    exact hopAdapter
  replace hbind := BindsChipOutput.ofElaborated (SubChip.elaborated (p := p)) hbind
  rw [SubChip.directOutput_eq] at hbind
  simp only [ProvableStruct.structEvalLiteralProc] at hbind
  subst cols
  rw [sub_chip_constraints_decompose]
  simp only [ChipOracle.nativeAssertZeros, subChipOracle, subChipReconfigure]
  simp only [Extracted.SubOracle.SubCols.asserts, List.forall_append]
  simp only [List.forall_cons]
  rw [forall_nil_iff]
  dsimp [rustA, rustB, rustValue, adapterValue, valueCols, isReal, subInput,
    value] at hSub
  dsimp [rustState, rustNextPc, stateValue, isReal, cpuInput] at hCpu
  dsimp [stateValue, rustValue, valueCols, rustAdapter, adapterValue, isReal,
    rtypeInput, value] at hRType
  simp_rw [← ProvableStruct.eval_eq_eval] at hSub hCpu hRType
  constructor
  · rintro ⟨⟨⟨hSubG, hCpuG⟩, hRTypeG⟩, hGate, hOp, _⟩
    have hSubN := hSub.mp hSubG
    have hCpuN := hCpu.mp hCpuG
    have hRTypeN := (hRType.mp ⟨hRTypeG, hOp⟩).1
    have hWriteN :=
      (CanonicalReader.registerWriteAssertions env writeInput (offset + 4)).mpr trivial
    have hEqSem : Expression.eval env input.adapter.op_a_0 =
        Expression.eval env (0 : Expression (ZMod p)) := by
      rw [hopEval, hOp]
      rfl
    have hEqN :=
      (CanonicalReader.equalityAssertions env input.adapter.op_a_0 0 (offset + 4)).mpr hEqSem
    have hGateN : Expression.eval env (input.is_real * (input.is_real - 1)) = 0 := by
      simpa only [eval_mul, eval_sub, Expression.eval] using hGate
    exact ⟨hCpuN, hSubN, hRTypeN, hWriteN, hEqN, hGateN⟩
  · rintro ⟨hCpuN, hSubN, hRTypeN, _hWriteN, hEqN, hGateN⟩
    have hCpuG := hCpu.mpr hCpuN
    have hSubG := hSub.mpr hSubN
    have hEqSem :=
      (CanonicalReader.equalityAssertions env input.adapter.op_a_0 0 (offset + 4)).mp hEqN
    have hOp : (Eval.eval env input.adapter).op_a_0 = 0 := by
      rw [← hopEval]
      simpa only [Expression.eval] using hEqSem
    have hRTypeG := (hRType.mpr ⟨hRTypeN, hOp⟩).1
    have hGate : Expression.eval env input.is_real *
        (Expression.eval env input.is_real - 1) = 0 := by
      simpa only [eval_mul, eval_sub, Expression.eval] using hGateN
    exact ⟨⟨⟨hSubG, hCpuG⟩, hRTypeG⟩, hGate, hOp, trivial⟩

set_option maxHeartbeats 4000000 in
/-- **Complete interaction-system anchor for the native Sub row.** Binding the circuit output supplies
all column equalities needed by the detailed per-bus calculations above; the public conclusion compares
the canonical four-bus multiset emitted by the native chip with SP1 Rust's complete extracted oracle. -/
theorem subChip_interactions_faithful
    (env : Environment (ZMod p)) (input : Var SubChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : SubChip.Columns (ZMod p))
    (hbind : BindsChipOutput SubChip.main env input offset cols) :
    List.Perm (nativeAccesses env ((SubChip.main input).operations offset))
      (subChipOracle.accesses cols) := by
  replace hbind := BindsChipOutput.ofElaborated (SubChip.elaborated (p := p)) hbind
  rw [SubChip.directOutput_eq] at hbind
  simp only [ProvableStruct.structEvalLiteralProc] at hbind
  subst cols
  simp only [nativeAccesses]
  have h_unexpected :
      unexpectedInteractions ((SubChip.main input).operations offset) = [] := by
    simp [unexpectedInteractions, SubChip.main,
      Readers.CPUState.circuit, Readers.CPUState.main,
      Readers.RTypeReader.circuit, Readers.RTypeReader.main,
      Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
      Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
      Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
      SP1Clean.SubOperation.circuit, SP1Clean.SubOperation.main,
      Gadgets.Equality.main, FormalAssertion.toSubcircuit_interactions,
      GeneralFormalCircuit.toSubcircuit_interactions, circuit_norm]
  rw [h_unexpected]
  simp only [List.map_nil, List.append_nil]
  apply subcols_interactions_faithful_syntactic
  all_goals
    simp only [eval_cpuState, eval_rTypeReader, eval_registerAccessCols,
      eval_registerAccessTimestamp, eval_sub_operation_columns, ProvableType.eval_field,
      ← ProvableType.getElem_eval_fields, Vector.getElem_mapRange, Expression.eval,
      Nat.add_zero]

/-- The extracted Rust row itself reconstructs a complete satisfying Clean row; no caller-supplied
output binding is part of the public boundary. -/
theorem subChip_constraints_constructive
    (rustCols : Extracted.SubOracle.SubCols (ZMod p)) (data : ProverData (ZMod p)) :
    let assignment := subChipRowCodec.assignment (subChipOracle.deconfigure rustCols) data
    List.Forall (· = 0) (subChipOracle.assertZeros rustCols) ↔
      (⟨SubChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).operations.ConstraintsHold
        assignment.environment := by
  dsimp only
  let cols := subChipOracle.deconfigure rustCols
  let assignment := subChipRowCodec.assignment cols data
  have hbind : BindsChipOutput SubChip.main assignment.environment
      (⟨SubChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowInputVar
      (⟨SubChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [SubChip.circuit_main_eq] at h
    exact h
  have hlegacy := subChip_constraints_faithful (p := p) assignment.environment
    (⟨SubChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowInputVar
    (⟨SubChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowOffset cols hbind
  have hassertions :
      List.Forall (· = 0) (subChipOracle.assertZeros rustCols) ↔
        List.Forall (· = 0)
          (nativeAssertZeros assignment.environment
            (⟨SubChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowOperations) := by
    simpa only [cols, ChipOracle.nativeAssertZeros_deconfigure,
      Air.Flat.Component.rowOperations_mk, Air.Flat.Component.rowInputVar_mk,
      Air.Flat.Component.rowOffset_mk, SubChip.circuit_main_eq] using hlegacy
  exact hassertions.trans
    (constraintsHold_iff_nativeAssertZeros (SubChip.circuit (p := p)) assignment.environment
      subChip_lookups_empty).symm

/-- Constructive interaction half of Sub faithfulness, evaluated on the same reconstructed row. -/
theorem subChip_interactions_constructive
    (rustCols : Extracted.SubOracle.SubCols (ZMod p)) (data : ProverData (ZMod p)) :
    let assignment := subChipRowCodec.assignment (subChipOracle.deconfigure rustCols) data
    List.Perm
      (nativeAccesses assignment.environment
        (⟨SubChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).operations)
      (subChipOracle.rustAccesses rustCols) := by
  dsimp only
  let cols := subChipOracle.deconfigure rustCols
  let assignment := subChipRowCodec.assignment cols data
  have hbind : BindsChipOutput SubChip.main assignment.environment
      (⟨SubChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowInputVar
      (⟨SubChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [SubChip.circuit_main_eq] at h
    exact h
  have hlegacy := subChip_interactions_faithful (p := p) assignment.environment
    (⟨SubChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowInputVar
    (⟨SubChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowOffset cols hbind
  rw [nativeAccesses_component_eq_rowOperations (SubChip.circuit (p := p))
    assignment.environment]
  simpa only [cols, ChipOracle.accesses_deconfigure,
    Air.Flat.Component.rowOperations_mk, Air.Flat.Component.rowInputVar_mk,
    Air.Flat.Component.rowOffset_mk, SubChip.circuit_main_eq] using hlegacy

/-- The Sub pilot packaged at the intended stable boundary: native whole-chip circuit versus the
complete Rust whole-chip oracle. Rust operation helpers and Lean gadgets are deliberately absent from
the statement. -/
theorem subChip_faithful :
    ChipFaithful (p := p) SubChip.Inputs SubChip.Columns Extracted.SubOracle.SubCols
      SubChip.circuit subChipRowCodec subChipOracle where
  constraints := subChip_constraints_constructive (p := p)
  interactions := fun rustCols data _ =>
    LookupAccessList.active_perm
      (subChip_interactions_constructive (p := p) rustCols data)

end SP1Clean.Faithful
