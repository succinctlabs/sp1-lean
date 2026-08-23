import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Model.SP1Constraint
import SP1Clean.Model.InteractionProjection
import ToClean.Circuit.InteractionRecovery
import SP1Clean.Extracted.InteractionModel
import SP1Clean.Native.Readers.ITypeReaderImmutable
import SP1Clean.Extracted.ITypeReaderImmutable
import SP1Clean.Faithful.ChipTactics

/-! # Faithfulness anchor — SP1's `ITypeReaderImmutable` constraint fragment ↔ the native reader spec

The reader-fragment anchor for the **immutable** I-type register-adapter used by
stores (op_a = rs2 *read*, op_b = rs1 read, op_c an immediate) — a sibling of the
`Faithful/RTypeReader.lean`/`Faithful/ALUTypeReader.lean` reader anchors (there is no separate
`ITypeReader` anchor; the mutable I-type fragment is covered through the chip anchors). SP1's generated
`ITypeReaderImmutable.constraints` (`Extracted/ITypeReaderImmutable.lean`) is `ITypeReader` with op_a a
read: the four `op_a_0` zeroing gates pin the **read** value of `x0` to `0`
(`op_a_0 * op_a_memory.prev_value[i] = 0`), and the op_a memory `.receive` carries `prev_value`
(no write value). Under `is_real = is_trusted = 1` it emits three `is_real` binary gates
(vacuous), the `.program` fetch (per-row meaning `True`), and per register operand (op_a, op_b) a
`.byte Range`/`.byte U8Range` timestamp check + a `.memory` send/receive pair (meaning `True`).

`itypereaderimmutable_constraints_faithful` proves the lists hold iff the four `op_a_0` read-zeroing
equations and the two operands' timestamp byte bounds — precisely `Readers.ITypeReaderImmutable.Spec`
restricted to `is_real = 1`. -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **Faithfulness anchor (ITypeReaderImmutable fragment).** Under `is_real = is_trusted = 1`, SP1's
generated `ITypeReaderImmutable` constraint list holds iff the four `op_a_0` *read*-zeroing equations and
the two register operands' (op_a, op_b) timestamp byte bounds hold. -/
theorem itypereaderimmutable_constraints_faithful
    (clk_high clk_low : ZMod p) (pc : Vector (ZMod p) 3) (opcode : ZMod p)
    (cols : Extracted.ITypeReader (ZMod p)) :
    (List.Forall (· = 0)
          (Extracted.ITypeReaderImmutable.asserts clk_high clk_low pc opcode cols 1 1) ∧
        List.Forall Interaction.toProp
          (Extracted.ITypeReaderImmutable.interactions clk_high clk_low pc opcode cols 1 1)) ↔
      ((cols.op_a_0 * cols.op_a_memory.prev_value[0] = 0 ∧
          cols.op_a_0 * cols.op_a_memory.prev_value[1] = 0 ∧
          cols.op_a_0 * cols.op_a_memory.prev_value[2] = 0 ∧
          cols.op_a_0 * cols.op_a_memory.prev_value[3] = 0) ∧
        (cols.op_a_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
          ((clk_low + 4 - cols.op_a_memory.access_timestamp.prev_low - 1
              - cols.op_a_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8) ∧
        (cols.op_b_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
          ((clk_low + 3 - cols.op_b_memory.access_timestamp.prev_low - 1
              - cols.op_b_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8)) := by
  simp only [Extracted.ITypeReaderImmutable.asserts, Extracted.ITypeReaderImmutable.interactions,
    List.Forall, Interaction.toProp_send_byte, Interaction.toProp_receive,
    Interaction.toProp_send_memory, Interaction.toProp_send_program,
    ByteOpcode.constrainField_six, ByteOpcode.constrainField_three,
    ByteOpcode.constrain_Range,
    ByteOpcode.constrain_U8Range, val_16, ZMod.val_zero, one_ne_zero, ne_eq, not_false_eq_true,
    true_implies, sub_self, mul_zero, sub_zero, Nat.ofNat_pos, true_and, and_true,
    show (2 : ℕ) ^ 8 = 256 by norm_num, show (2 : ℕ) ^ 16 = 65536 by norm_num]
  tauto

open SP1Clean.Channels (byteChannel memoryChannel programChannel)
open InteractionRecovery

/-- Exact Memory-bus projection for the immutable I-type reader. Both operands are reads, so the
native pull/push pairs cover the complete four-entry Rust Memory block; `nativeAccesses` dualizes
the Clean direction to the Rust send/receive convention. -/
theorem itypereaderimmutable_memory_interactions_faithful_syntactic
    (env : Environment (ZMod p))
    (input : Var Readers.ITypeReaderImmutable.Inputs (ZMod p)) (offset : ℕ)
    (clkHigh clkLow : ZMod p) (pc : Vector (ZMod p) 3) (opcode : ZMod p)
    (cols : Extracted.ITypeReader (ZMod p)) (isReal isTrusted : ZMod p)
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
    (((Readers.ITypeReaderImmutable.main input).operations offset).interactionsWith
        memoryChannel.toRaw).map (AbstractInteraction.toAccess env) =
      (((Extracted.ITypeReaderImmutable.interactions clkHigh clkLow pc opcode cols
          isReal isTrusted).map Extracted.Interaction.toAccess).filter
            (fun access => access.1 = InteractionKind.Memory)).map
        LookupAccessList.negMult := by
  haveI : NeZero p :=
    ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp2 : 2 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    omega
  have hrac := fun (n : ℕ)
      (inp : Var Readers.RegisterAccessCols.Inputs (ZMod p)) =>
    filter_interactions_formalAssertion_eq_nil
      Readers.RegisterAccessCols.circuit memoryChannel.toRaw
      (n := n) inp
      (by simp [circuit_norm, Readers.RegisterAccessCols.circuit])
      (by simp [circuit_norm, Readers.RegisterAccessCols.circuit])
  have heq := fun (n : ℕ)
      (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil
      (ZMod p) _ (ProvablePair field field) ProvablePair.instance
      (Gadgets.Equality.circuit field) memoryChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  simp only [Readers.ITypeReaderImmutable.main, circuit_norm, hrac, heq,
    SP1Clean.Channels.programChannel_eq_memoryChannel_false, if_false]
  simp only [toAccess_pushIf_memory, toAccess_pullIf_memory]
  simp only [Extracted.ITypeReaderImmutable.interactions, List.map_cons,
    List.map_nil, Extracted.Interaction.toAccess, Extracted.Dir.sign,
    List.filter_cons]
  simp [circuit_norm, LookupAccessList.negMult, signedVal_neg hp2,
    hreal, hclkHigh, hclkLow, hopA, hopB, hprevA,
    hvalueA0, hvalueA1, hvalueA2, hvalueA3, hprevB,
    hvalueB0, hvalueB1, hvalueB2, hvalueB3]

/-- Exact Program-bus projection for the immutable I-type reader, including `imm_c = 1`. -/
theorem itypereaderimmutable_program_interactions_faithful_syntactic
    (env : Environment (ZMod p))
    (input : Var Readers.ITypeReaderImmutable.Inputs (ZMod p)) (offset : ℕ)
    (clkHigh clkLow : ZMod p) (pc : Vector (ZMod p) 3) (opcode : ZMod p)
    (cols : Extracted.ITypeReader (ZMod p)) (isReal isTrusted : ZMod p)
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
    (((Readers.ITypeReaderImmutable.main input).operations offset).interactionsWith
        programChannel.toRaw).map (AbstractInteraction.toAccess env) =
      (((Extracted.ITypeReaderImmutable.interactions clkHigh clkLow pc opcode cols
          isReal isTrusted).map Extracted.Interaction.toAccess).filter
            (fun access => access.1 = InteractionKind.Program)).map
        LookupAccessList.negMult := by
  haveI : NeZero p :=
    ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp2 : 2 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    omega
  have hrac := fun (n : ℕ)
      (inp : Var Readers.RegisterAccessCols.Inputs (ZMod p)) =>
    filter_interactions_formalAssertion_eq_nil
      Readers.RegisterAccessCols.circuit programChannel.toRaw
      (n := n) inp
      (by simp [circuit_norm, Readers.RegisterAccessCols.circuit])
      (by simp [circuit_norm, Readers.RegisterAccessCols.circuit])
  have heq := fun (n : ℕ)
      (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil
      (ZMod p) _ (ProvablePair field field) ProvablePair.instance
      (Gadgets.Equality.circuit field) programChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  simp only [Readers.ITypeReaderImmutable.main, circuit_norm, hrac, heq,
    SP1Clean.Channels.memoryChannel_eq_programChannel_false, if_false]
  have hk := fun (g : Expression (ZMod p))
      (message : SP1Clean.Channels.ProgramMsg (Expression (ZMod p))) =>
    toAccess_pullIf_program env g message
  simp only [hk, Extracted.ITypeReaderImmutable.interactions,
    List.map_cons, List.map_nil, Extracted.Interaction.toAccess,
    Extracted.Dir.sign, List.filter_cons]
  simp [circuit_norm, Opcode.ofNat, ConstraintCoe.coe_eq_val,
    LookupAccessList.negMult, signedVal_neg hp2, htrusted,
    hpc0, hpc1, hpc2, hopcode, hopA, hopB, hopA0,
    himm0, himm1, himm2, himm3]

/-- Exact four-entry timestamp Byte block for the immutable I-type reader. -/
theorem itypereaderimmutable_byte_interactions_faithful_syntactic
    (env : Environment (ZMod p))
    (input : Var Readers.ITypeReaderImmutable.Inputs (ZMod p)) (offset : ℕ)
    (clkHigh clkLow : ZMod p) (pc : Vector (ZMod p) 3) (opcode : ZMod p)
    (cols : Extracted.ITypeReader (ZMod p)) (isReal isTrusted : ZMod p)
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
    (((Readers.ITypeReaderImmutable.main input).operations offset).interactionsWith
        byteChannel.toRaw).map (AbstractInteraction.toAccess env) =
      ((Extracted.ITypeReaderImmutable.interactions clkHigh clkLow pc opcode cols
          isReal isTrusted).map Extracted.Interaction.toAccess).filter
        (fun access => access.1 = InteractionKind.Byte) := by
  haveI : NeZero p :=
    ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h6 : (6 : ZMod p).val = 6 := val_6_zmod_p
  have h3 : (3 : ZMod p).val = 3 := val_3_zmod_p
  have hbk := toAccess_pullIf_byte_forall env
  have heq := fun (n : ℕ)
      (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil
      (ZMod p) _ (ProvablePair field field) ProvablePair.instance
      (Gadgets.Equality.circuit field) byteChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  simp only [Readers.ITypeReaderImmutable.main,
    Readers.RegisterAccessCols.circuit,
    Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit,
    Readers.RegisterAccessTimestamp.main, circuit_norm,
    FormalAssertion.toSubcircuit_interactions]
  simp [circuit_norm, hbk, Gadgets.Equality.main,
    Extracted.ITypeReaderImmutable.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign, h6, h3,
    hreal, hclkLow, hprevA, hdiffA, hprevB, hdiffB]

end SP1Clean.Faithful
