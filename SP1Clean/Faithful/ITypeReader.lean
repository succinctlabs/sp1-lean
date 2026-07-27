import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Model.SP1Constraint
import SP1Clean.Model.InteractionProjection
import SP1Clean.Model.InteractionRecovery
import SP1Clean.Faithful.ExtractedInteractionModel
import SP1Clean.Native.Readers.ITypeReader
import SP1Clean.Extracted.ITypeReader
import SP1Clean.Faithful.ChipTactics

/-! # Faithfulness anchor — SP1's `ITypeReader` constraint fragment ↔ the native reader spec

Sibling of `Faithful/RTypeReader.lean`, for the **I-type** register-adapter fragment (op_a write,
op_b read, op_c an *immediate* — no op_c register access). SP1's generated `ITypeReader.constraints`
(`Extracted/ITypeReader.lean`) emits, under `is_real = is_trusted = 1`:

- three copies of the `is_real` binary gate `.assertZero (is_real * (is_real - 1))` (vacuous at `1`);
- the `.send (.program …) is_trusted` instruction fetch (per-row meaning `True`; its content is the
  trace-level program bus, `Soundness/ProgramConsistency.lean`);
- per *register* operand (op_a, op_b only): a `.send (.byte Range diff 16 0)` (16-bit range) and a
  `.send (.byte U8Range 0 scaled 0)` (`< 256`) timestamp check, plus a `.send`/`.receive (.memory …)`
  pair (per-row meaning `True`; content is the trace-level memory bus,
  `Soundness/MemoryConsistency.lean`);
- four `.assertZero (op_a_0 * (op_a_write_value[i] - 0))` zeroing gates (`rd = x0 ⟹ write 0`).

`itypereader_constraints_faithful` proves the constraint lists hold exactly iff the four `op_a_0`
zeroing equations and the two operands' timestamp byte bounds — `Readers.ITypeReader.Spec` at
`is_real = 1`. -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

set_option maxHeartbeats 1000000 in
/-- **Faithfulness anchor (ITypeReader fragment).** Under `is_real = is_trusted = 1`, SP1's generated
`ITypeReader` constraint list holds iff the four `op_a_0` zeroing equations and the two register
operands' (op_a, op_b) timestamp byte bounds hold. The `.program`/`.memory` interactions contribute
`True` (their meaning is the trace-level buses); the three binary gates are vacuous at `is_real = 1`. -/
theorem itypereader_constraints_faithful
    (clk_high clk_low : ZMod p) (pc : Vector (ZMod p) 3) (opcode : ZMod p)
    (op_a_write_value : Word (ZMod p)) (cols : Extracted.ITypeReader (ZMod p)) :
    (List.Forall (· = 0)
          (Extracted.ITypeReader.asserts clk_high clk_low pc opcode op_a_write_value cols 1 1) ∧
        List.Forall Interaction.toProp
          (Extracted.ITypeReader.interactions clk_high clk_low pc opcode op_a_write_value cols 1 1)) ↔
      ((cols.op_a_0 * op_a_write_value[0] = 0 ∧ cols.op_a_0 * op_a_write_value[1] = 0 ∧
          cols.op_a_0 * op_a_write_value[2] = 0 ∧ cols.op_a_0 * op_a_write_value[3] = 0) ∧
        (cols.op_a_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
          ((clk_low + 4 - cols.op_a_memory.access_timestamp.prev_low - 1
              - cols.op_a_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8) ∧
        (cols.op_b_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
          ((clk_low + 3 - cols.op_b_memory.access_timestamp.prev_low - 1
              - cols.op_b_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8)) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [Extracted.ITypeReader.asserts, Extracted.ITypeReader.interactions, List.Forall,
    Interaction.toProp_send_byte, Interaction.toProp_receive,
    Interaction.toProp_send_memory, Interaction.toProp_send_program,
    ByteOpcode.constrainField_six, ByteOpcode.constrainField_three,
    ByteOpcode.constrain_Range,
    ByteOpcode.constrain_U8Range, val_16, ZMod.val_zero, one_ne_zero, ne_eq, not_false_eq_true,
    true_implies, sub_self, mul_zero, sub_zero, Nat.ofNat_pos, true_and, and_true,
    show (2 : ℕ) ^ 8 = 256 from by norm_num, show (2 : ℕ) ^ 16 = 65536 from by norm_num]
  tauto

open SP1Clean.Channels (byteChannel memoryChannel programChannel)
open SP1Clean.InteractionRecovery

set_option maxHeartbeats 2000000 in
/-- The native pure-reader Memory block is SP1's I-type Memory block with the destination write
removed. The composing chip restores that write through `Readers.RegisterWrite`; the whole-chip
anchor therefore compares the complete four-entry block. -/
theorem itypereader_memory_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var Readers.ITypeReader.Inputs (ZMod p)) (offset : ℕ)
    (clkHigh clkLow : ZMod p) (pc : Vector (ZMod p) 3) (opcode : ZMod p)
    (writeValue : Word (ZMod p)) (cols : Extracted.ITypeReader (ZMod p))
    (isReal isTrusted : ZMod p)
    (hreal : Expression.eval env input.is_real = isReal)
    (hclkHigh : Expression.eval env input.clk_high = clkHigh)
    (hclkLow : Expression.eval env input.clk_low = clkLow)
    (hopA : Expression.eval env input.cols.op_a = cols.op_a)
    (hopB : Expression.eval env input.cols.op_b = cols.op_b)
    (hprevA : Expression.eval env input.cols.op_a_memory.access_timestamp.prev_low =
      cols.op_a_memory.access_timestamp.prev_low)
    (hvalueA0 : Expression.eval env input.cols.op_a_memory.prev_value[0] =
      cols.op_a_memory.prev_value[0])
    (hvalueA1 : Expression.eval env input.cols.op_a_memory.prev_value[1] =
      cols.op_a_memory.prev_value[1])
    (hvalueA2 : Expression.eval env input.cols.op_a_memory.prev_value[2] =
      cols.op_a_memory.prev_value[2])
    (hvalueA3 : Expression.eval env input.cols.op_a_memory.prev_value[3] =
      cols.op_a_memory.prev_value[3])
    (hprevB : Expression.eval env input.cols.op_b_memory.access_timestamp.prev_low =
      cols.op_b_memory.access_timestamp.prev_low)
    (hvalueB0 : Expression.eval env input.cols.op_b_memory.prev_value[0] =
      cols.op_b_memory.prev_value[0])
    (hvalueB1 : Expression.eval env input.cols.op_b_memory.prev_value[1] =
      cols.op_b_memory.prev_value[1])
    (hvalueB2 : Expression.eval env input.cols.op_b_memory.prev_value[2] =
      cols.op_b_memory.prev_value[2])
    (hvalueB3 : Expression.eval env input.cols.op_b_memory.prev_value[3] =
      cols.op_b_memory.prev_value[3]) :
    (((Readers.ITypeReader.main input).operations offset).interactionsWith
        memoryChannel.toRaw).map (AbstractInteraction.toAccess env) =
      ((((Extracted.ITypeReader.interactions clkHigh clkLow pc opcode writeValue cols
          isReal isTrusted).map Extracted.Interaction.toAccess).filter
            (fun access => access.1 = InteractionKind.Memory)).eraseIdx 1).map
        LookupAccessList.negMult := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp2 : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have hrac := fun (n : ℕ) (inp : Var Readers.RegisterAccessCols.Inputs (ZMod p)) =>
    filter_interactions_formalAssertion_eq_nil Readers.RegisterAccessCols.circuit
      memoryChannel.toRaw (n := n) inp
      (by simp [circuit_norm, Readers.RegisterAccessCols.circuit])
      (by simp [circuit_norm, Readers.RegisterAccessCols.circuit])
  have heq := fun (n : ℕ) (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil (ZMod p) _ (ProvablePair field field)
      ProvablePair.instance (Gadgets.Equality.circuit field) memoryChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  simp only [Readers.ITypeReader.main, circuit_norm, hrac, heq,
    SP1Clean.Channels.programChannel_eq_memoryChannel_false, if_false]
  simp only [toAccess_pushIf_memory, toAccess_pullIf_memory]
  simp only [Extracted.ITypeReader.interactions, List.map_cons, List.map_nil,
    Extracted.Interaction.toAccess, Extracted.Dir.sign, List.filter_cons]
  simp [circuit_norm, LookupAccessList.negMult, signedVal_neg hp2,
    hreal, hclkHigh, hclkLow, hopA, hopB, hprevA,
    hvalueA0, hvalueA1, hvalueA2, hvalueA3, hprevB,
    hvalueB0, hvalueB1, hvalueB2, hvalueB3]

set_option maxHeartbeats 1000000 in
/-- Exact Program-bus projection for the I-type reader, including the immediate operand and
`imm_c = 1`. Native pulls are dualized by `nativeAccesses`, matching Rust's send orientation. -/
theorem itypereader_program_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var Readers.ITypeReader.Inputs (ZMod p)) (offset : ℕ)
    (clkHigh clkLow : ZMod p) (pc : Vector (ZMod p) 3) (opcode : ZMod p)
    (writeValue : Word (ZMod p)) (cols : Extracted.ITypeReader (ZMod p))
    (isReal isTrusted : ZMod p)
    (htrusted : Expression.eval env input.is_trusted = isTrusted)
    (hpc0 : Expression.eval env input.pc[0] = pc[0])
    (hpc1 : Expression.eval env input.pc[1] = pc[1])
    (hpc2 : Expression.eval env input.pc[2] = pc[2])
    (hopcode : Expression.eval env input.opcode = opcode)
    (hopA : Expression.eval env input.cols.op_a = cols.op_a)
    (hopB : Expression.eval env input.cols.op_b = cols.op_b)
    (hopA0 : Expression.eval env input.cols.op_a_0 = cols.op_a_0)
    (himm0 : Expression.eval env input.cols.op_c_imm[0] = cols.op_c_imm[0])
    (himm1 : Expression.eval env input.cols.op_c_imm[1] = cols.op_c_imm[1])
    (himm2 : Expression.eval env input.cols.op_c_imm[2] = cols.op_c_imm[2])
    (himm3 : Expression.eval env input.cols.op_c_imm[3] = cols.op_c_imm[3]) :
    (((Readers.ITypeReader.main input).operations offset).interactionsWith
        programChannel.toRaw).map (AbstractInteraction.toAccess env) =
      (((Extracted.ITypeReader.interactions clkHigh clkLow pc opcode writeValue cols
          isReal isTrusted).map Extracted.Interaction.toAccess).filter
            (fun access => access.1 = InteractionKind.Program)).map
        LookupAccessList.negMult := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp2 : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have hrac := fun (n : ℕ) (inp : Var Readers.RegisterAccessCols.Inputs (ZMod p)) =>
    filter_interactions_formalAssertion_eq_nil Readers.RegisterAccessCols.circuit
      programChannel.toRaw (n := n) inp
      (by simp [circuit_norm, Readers.RegisterAccessCols.circuit])
      (by simp [circuit_norm, Readers.RegisterAccessCols.circuit])
  have heq := fun (n : ℕ) (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil (ZMod p) _ (ProvablePair field field)
      ProvablePair.instance (Gadgets.Equality.circuit field) programChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  simp only [Readers.ITypeReader.main, circuit_norm, hrac, heq,
    SP1Clean.Channels.memoryChannel_eq_programChannel_false, if_false]
  have hk := fun (g : Expression (ZMod p))
      (message : SP1Clean.Channels.ProgramMsg (Expression (ZMod p))) =>
    toAccess_pullIf_program env g message
  simp only [hk, Extracted.ITypeReader.interactions, List.map_cons, List.map_nil,
    Extracted.Interaction.toAccess, Extracted.Dir.sign, List.filter_cons]
  simp [circuit_norm, Opcode.ofNat, ConstraintCoe.coe_eq_val,
    LookupAccessList.negMult, signedVal_neg hp2, htrusted,
    hpc0, hpc1, hpc2, hopcode, hopA, hopB, hopA0,
    himm0, himm1, himm2, himm3]

set_option maxHeartbeats 1000000 in
/-- Exact four-entry timestamp Byte block for the two I-type register accesses. -/
theorem itypereader_byte_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var Readers.ITypeReader.Inputs (ZMod p)) (offset : ℕ)
    (clkHigh clkLow : ZMod p) (pc : Vector (ZMod p) 3) (opcode : ZMod p)
    (writeValue : Word (ZMod p)) (cols : Extracted.ITypeReader (ZMod p))
    (isReal isTrusted : ZMod p)
    (hreal : Expression.eval env input.is_real = isReal)
    (hclkLow : Expression.eval env input.clk_low = clkLow)
    (hprevA : Expression.eval env input.cols.op_a_memory.access_timestamp.prev_low =
      cols.op_a_memory.access_timestamp.prev_low)
    (hdiffA : Expression.eval env input.cols.op_a_memory.access_timestamp.diff_low_limb =
      cols.op_a_memory.access_timestamp.diff_low_limb)
    (hprevB : Expression.eval env input.cols.op_b_memory.access_timestamp.prev_low =
      cols.op_b_memory.access_timestamp.prev_low)
    (hdiffB : Expression.eval env input.cols.op_b_memory.access_timestamp.diff_low_limb =
      cols.op_b_memory.access_timestamp.diff_low_limb) :
    (((Readers.ITypeReader.main input).operations offset).interactionsWith
        byteChannel.toRaw).map (AbstractInteraction.toAccess env) =
      ((Extracted.ITypeReader.interactions clkHigh clkLow pc opcode writeValue cols
          isReal isTrusted).map Extracted.Interaction.toAccess).filter
        (fun access => access.1 = InteractionKind.Byte) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h6 : (6 : ZMod p).val = 6 := by
    have h : (6 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt h
  have h3 : (3 : ZMod p).val = 3 := by
    have h : (3 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt h
  have hbk : ∀ (g : Expression (ZMod p)) (row : ByteRow (Expression (ZMod p))),
      AbstractInteraction.toAccess env ((pulledIf (channel := byteChannel) g row).toRaw) =
        (InteractionKind.Byte, "SP1Byte",
          [(Expression.eval env row.opcode).val, (Expression.eval env row.a).val,
           (Expression.eval env row.b).val, (Expression.eval env row.c).val],
          signedVal (Expression.eval env (-g))) :=
    fun g row => toAccess_pullIf_byte env g row
  have heq := fun (n : ℕ) (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil (ZMod p) _ (ProvablePair field field)
      ProvablePair.instance (Gadgets.Equality.circuit field) byteChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  simp only [Readers.ITypeReader.main, Readers.RegisterAccessCols.circuit,
    Readers.RegisterAccessCols.main, Readers.RegisterAccessTimestamp.circuit,
    Readers.RegisterAccessTimestamp.main, circuit_norm,
    FormalAssertion.toSubcircuit_interactions]
  simp [circuit_norm, hbk, Gadgets.Equality.main,
    Extracted.ITypeReader.interactions, Extracted.Interaction.toAccess,
    Extracted.Dir.sign, h6, h3, hreal, hclkLow, hprevA, hdiffA, hprevB, hdiffB]

end SP1Clean.Faithful
