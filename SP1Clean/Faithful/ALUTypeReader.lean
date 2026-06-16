import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Model.SP1Constraint
import SP1Clean.Model.InteractionProjection
import SP1Clean.Model.InteractionRecovery
import SP1Clean.Faithful.ExtractedInteractionModel
import SP1Clean.Readers.ALUTypeReader
import SP1Clean.Extracted.ALUTypeReader

/-! # Faithfulness anchor — SP1's `ALUTypeReader` constraint fragment ↔ the native reader spec

Sibling of `Faithful/RTypeReader.lean`, for the *ALU-type* register-adapter fragment used by the
ALU chips whose op_c may be an **immediate** (`Addw`, `Lt`, `Bitwise`, `ShiftLeft`, `ShiftRight`).
SP1's generated `ALUTypeReader.constraints` (`Extracted/ALUTypeReader.lean`) is the `RTypeReader`
fragment plus the immediate-`c` machinery: a flag `imm_c`, a `Word`-typed `op_c`, and gates that
(a) force `imm_c` boolean, (b) when `imm_c = 1` pin the op_c register read to the immediate value, and
(c) gate the op_c register byte/memory interactions by `is_real - imm_c` (no register read for an
immediate).

`alutypereader_constraints_faithful` proves the list's `allHold`, under `is_real = is_trusted = 1`, is
exactly: the four `op_a_0` zeroing equations, the `imm_c` boolean gate, the four immediate-consistency
gates, the op_a/op_b timestamp byte bounds (identical to `RTypeReader`), and the op_c timestamp byte
bounds **guarded by `imm_c ≠ 1`** (the op_c byte sends carry multiplicity `is_real - imm_c`, and a byte
send's per-row meaning is `mult ≠ 0 → constrain`). The `.program`/`.memory` interactions contribute
`True`; the three `is_real` binary gates are vacuous at `is_real = 1`. -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- `(16 : ZMod p).val = 16` under `Fact (2^17 < p)`. -/
private lemma val_16' [NeZero p] : (16 : ZMod p).val = 16 := by
  have : (131072 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  exact ZMod.val_natCast_of_lt (show (16 : ℕ) < p by omega)

set_option maxHeartbeats 4000000 in
/-- **Faithfulness anchor (ALUTypeReader fragment).** Under `is_real = is_trusted = 1`, SP1's generated
`ALUTypeReader` constraint list holds iff the combined spec holds. -/
theorem alutypereader_constraints_faithful
    (clk_high clk_low : ZMod p) (pc : Vector (ZMod p) 3) (opcode : ZMod p)
    (op_a_write_value : Word (ZMod p)) (cols : Extracted.ALUTypeReader (ZMod p)) :
    (List.Forall (· = 0)
          (Extracted.ALUTypeReader.asserts clk_high clk_low pc opcode op_a_write_value cols 1 1) ∧
        List.Forall Interaction.toProp
          (Extracted.ALUTypeReader.interactions clk_high clk_low pc opcode op_a_write_value cols 1 1)) ↔
      ((cols.op_a_0 * op_a_write_value[0] = 0 ∧ cols.op_a_0 * op_a_write_value[1] = 0 ∧
          cols.op_a_0 * op_a_write_value[2] = 0 ∧ cols.op_a_0 * op_a_write_value[3] = 0) ∧
        ((1 - cols.imm_c) * (1 - cols.imm_c - 1) = 0) ∧
        (cols.imm_c * (cols.op_c_memory.prev_value[0] - cols.op_c[0]) = 0 ∧
          cols.imm_c * (cols.op_c_memory.prev_value[1] - cols.op_c[1]) = 0 ∧
          cols.imm_c * (cols.op_c_memory.prev_value[2] - cols.op_c[2]) = 0 ∧
          cols.imm_c * (cols.op_c_memory.prev_value[3] - cols.op_c[3]) = 0) ∧
        (cols.op_a_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
          ((clk_low + 4 - cols.op_a_memory.access_timestamp.prev_low - 1
              - cols.op_a_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8) ∧
        (cols.op_b_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
          ((clk_low + 3 - cols.op_b_memory.access_timestamp.prev_low - 1
              - cols.op_b_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8) ∧
        ((1 - cols.imm_c ≠ 0 → cols.op_c_memory.access_timestamp.diff_low_limb.val < 2 ^ 16) ∧
          (1 - cols.imm_c ≠ 0 →
            ((clk_low + 2 - cols.op_c_memory.access_timestamp.prev_low - 1
              - cols.op_c_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8))) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [Extracted.ALUTypeReader.asserts, Extracted.ALUTypeReader.interactions, List.Forall,
    Interaction.toProp_send_byte, Interaction.toProp_receive,
    Interaction.toProp_send_memory, Interaction.toProp_send_program,
    ByteOpcode.ofNat_six, ByteOpcode.ofNat_three, ByteOpcode.constrain_Range,
    ByteOpcode.constrain_U8Range, val_16', ZMod.val_zero, one_ne_zero, ne_eq, not_false_eq_true,
    true_implies, sub_self, mul_zero, sub_zero, zero_mul, Nat.ofNat_pos, true_and, and_true,
    show (2 : ℕ) ^ 8 = 256 from by norm_num, show (2 : ℕ) ^ 16 = 65536 from by norm_num]
  tauto

open SP1Clean.Channels (byteChannel memoryChannel MemoryMsg programChannel ProgramMsg)
open SP1Clean.InteractionRecovery

set_option maxHeartbeats 1000000 in
/-- **Faithfulness anchor (ALUTypeReader fragment) — Program-bus interaction, SYNTACTIC.** Sibling of
`rtypereader_program_…`: the single Program fetch projects to the same arity-16 `LookupAccess` as the
oracle's Program entry. ALU-type differences vs R-type: `op_c` is a full **Word** (`op_c[0..3]` in the
Program tuple) and the immediate flag `imm_c` is carried (vs R-type's scalar op_c + `imm_c = 0`). -/
theorem alutypereader_program_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var Readers.ALUTypeReader.Inputs (ZMod p)) (offset : ℕ)
    (clk_high clk_low : ZMod p) (pc : Vector (ZMod p) 3) (opcode : ZMod p)
    (op_a_write_value : Word (ZMod p)) (cols : Extracted.ALUTypeReader (ZMod p)) (is_real is_trusted : ZMod p)
    (h_it : Expression.eval env input.is_trusted = is_trusted)
    (h_p0 : Expression.eval env input.pc[0] = pc[0])
    (h_p1 : Expression.eval env input.pc[1] = pc[1])
    (h_p2 : Expression.eval env input.pc[2] = pc[2])
    (h_oc : Expression.eval env input.opcode = opcode)
    (h_oa : Expression.eval env input.cols.op_a = cols.op_a)
    (h_ob : Expression.eval env input.cols.op_b = cols.op_b)
    (h_oc0 : Expression.eval env input.cols.op_c[0] = cols.op_c[0])
    (h_oc1 : Expression.eval env input.cols.op_c[1] = cols.op_c[1])
    (h_oc2 : Expression.eval env input.cols.op_c[2] = cols.op_c[2])
    (h_oc3 : Expression.eval env input.cols.op_c[3] = cols.op_c[3])
    (h_oa0 : Expression.eval env input.cols.op_a_0 = cols.op_a_0)
    (h_imm : Expression.eval env input.cols.imm_c = cols.imm_c) :
    (((Readers.ALUTypeReader.main input).operations offset).interactionsWith
        programChannel.toRaw).map (AbstractInteraction.toAccess env)
      = ((Extracted.ALUTypeReader.interactions clk_high clk_low pc opcode op_a_write_value cols is_real
          is_trusted).map Extracted.Interaction.toAccess).filter (fun a => a.1 = InteractionKind.Program) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hrac := fun (n : ℕ) (inp : Var Readers.RegisterAccessCols.Inputs (ZMod p)) =>
    filter_interactions_formalAssertion_eq_nil Readers.RegisterAccessCols.circuit programChannel.toRaw
      (n := n) inp (by simp [circuit_norm, Readers.RegisterAccessCols.circuit])
      (by simp [circuit_norm, Readers.RegisterAccessCols.circuit])
  have heq := fun (n : ℕ) (inp : Var (ProvablePair id id) (ZMod p)) =>
    filter_interactions_formalAssertion_eq_nil (Gadgets.Equality.circuit id) programChannel.toRaw
      (n := n) inp List.not_mem_nil List.not_mem_nil
  simp only [Readers.ALUTypeReader.main, circuit_norm, hrac, heq,
    SP1Clean.Channels.memoryChannel_eq_programChannel_false, if_false]
  simp only [toAccess_pushIf_program]
  simp only [Extracted.ALUTypeReader.interactions, List.map_cons, List.map_nil,
    Extracted.Interaction.toAccess, Extracted.Dir.sign, List.filter_cons]
  simp [circuit_norm, Opcode.ofNat, ConstraintCoe.coe_eq_val,
    h_it, h_p0, h_p1, h_p2, h_oc, h_oa, h_ob, h_oc0, h_oc1, h_oc2, h_oc3, h_oa0, h_imm]

set_option maxHeartbeats 1000000 in
/-- **Faithfulness anchor (ALUTypeReader fragment) — Memory-bus interactions, SYNTACTIC.** Sibling of
`rtypereader_memory_…`: the six Memory interactions project to the oracle's Memory entries. ALU-type
differences: the `op_c` register read uses the low limb `op_c[0]` as its address, and its two Memory emits
are gated by `is_real - imm_c` (an immediate does no register read) — handled by binding `imm_c` (`h_imm`),
the mult reduces to `is_real - cols.imm_c` matching the oracle's `E29`. -/
theorem alutypereader_memory_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var Readers.ALUTypeReader.Inputs (ZMod p)) (offset : ℕ)
    (clk_high clk_low : ZMod p) (pc : Vector (ZMod p) 3) (opcode : ZMod p)
    (op_a_write_value : Word (ZMod p)) (cols : Extracted.ALUTypeReader (ZMod p)) (is_real is_trusted : ZMod p)
    (h_ir : Expression.eval env input.is_real = is_real)
    (h_ch : Expression.eval env input.clk_high = clk_high)
    (h_cl : Expression.eval env input.clk_low = clk_low)
    (h_oa : Expression.eval env input.cols.op_a = cols.op_a)
    (h_ob : Expression.eval env input.cols.op_b = cols.op_b)
    (h_oc0 : Expression.eval env input.cols.op_c[0] = cols.op_c[0])
    (h_imm : Expression.eval env input.cols.imm_c = cols.imm_c)
    (h_wv0 : Expression.eval env input.wv0 = op_a_write_value[0])
    (h_wv1 : Expression.eval env input.wv1 = op_a_write_value[1])
    (h_wv2 : Expression.eval env input.wv2 = op_a_write_value[2])
    (h_wv3 : Expression.eval env input.wv3 = op_a_write_value[3])
    (h_pl_a : Expression.eval env input.cols.op_a_memory.access_timestamp.prev_low =
      cols.op_a_memory.access_timestamp.prev_low)
    (h_pv_a0 : Expression.eval env input.cols.op_a_memory.prev_value[0] = cols.op_a_memory.prev_value[0])
    (h_pv_a1 : Expression.eval env input.cols.op_a_memory.prev_value[1] = cols.op_a_memory.prev_value[1])
    (h_pv_a2 : Expression.eval env input.cols.op_a_memory.prev_value[2] = cols.op_a_memory.prev_value[2])
    (h_pv_a3 : Expression.eval env input.cols.op_a_memory.prev_value[3] = cols.op_a_memory.prev_value[3])
    (h_pl_b : Expression.eval env input.cols.op_b_memory.access_timestamp.prev_low =
      cols.op_b_memory.access_timestamp.prev_low)
    (h_pv_b0 : Expression.eval env input.cols.op_b_memory.prev_value[0] = cols.op_b_memory.prev_value[0])
    (h_pv_b1 : Expression.eval env input.cols.op_b_memory.prev_value[1] = cols.op_b_memory.prev_value[1])
    (h_pv_b2 : Expression.eval env input.cols.op_b_memory.prev_value[2] = cols.op_b_memory.prev_value[2])
    (h_pv_b3 : Expression.eval env input.cols.op_b_memory.prev_value[3] = cols.op_b_memory.prev_value[3])
    (h_pl_c : Expression.eval env input.cols.op_c_memory.access_timestamp.prev_low =
      cols.op_c_memory.access_timestamp.prev_low)
    (h_pv_c0 : Expression.eval env input.cols.op_c_memory.prev_value[0] = cols.op_c_memory.prev_value[0])
    (h_pv_c1 : Expression.eval env input.cols.op_c_memory.prev_value[1] = cols.op_c_memory.prev_value[1])
    (h_pv_c2 : Expression.eval env input.cols.op_c_memory.prev_value[2] = cols.op_c_memory.prev_value[2])
    (h_pv_c3 : Expression.eval env input.cols.op_c_memory.prev_value[3] = cols.op_c_memory.prev_value[3]) :
    (((Readers.ALUTypeReader.main input).operations offset).interactionsWith
        memoryChannel.toRaw).map (AbstractInteraction.toAccess env)
      = ((Extracted.ALUTypeReader.interactions clk_high clk_low pc opcode op_a_write_value cols is_real
          is_trusted).map Extracted.Interaction.toAccess).filter (fun a => a.1 = InteractionKind.Memory) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hrac := fun (n : ℕ) (inp : Var Readers.RegisterAccessCols.Inputs (ZMod p)) =>
    filter_interactions_formalAssertion_eq_nil Readers.RegisterAccessCols.circuit memoryChannel.toRaw
      (n := n) inp (by simp [circuit_norm, Readers.RegisterAccessCols.circuit])
      (by simp [circuit_norm, Readers.RegisterAccessCols.circuit])
  have heq := fun (n : ℕ) (inp : Var (ProvablePair id id) (ZMod p)) =>
    filter_interactions_formalAssertion_eq_nil (Gadgets.Equality.circuit id) memoryChannel.toRaw
      (n := n) inp List.not_mem_nil List.not_mem_nil
  simp only [Readers.ALUTypeReader.main, circuit_norm, hrac, heq,
    SP1Clean.Channels.programChannel_eq_memoryChannel_false, if_false]
  simp only [toAccess_pushIf_memory]
  simp only [Extracted.ALUTypeReader.interactions, List.map_cons, List.map_nil,
    Extracted.Interaction.toAccess, Extracted.Dir.sign, List.filter_cons]
  simp [circuit_norm, h_ir, h_ch, h_cl, h_oa, h_ob, h_oc0, h_imm,
    h_wv0, h_wv1, h_wv2, h_wv3, h_pl_a, h_pv_a0, h_pv_a1, h_pv_a2, h_pv_a3,
    h_pl_b, h_pv_b0, h_pv_b1, h_pv_b2, h_pv_b3,
    h_pl_c, h_pv_c0, h_pv_c1, h_pv_c2, h_pv_c3, sub_eq_add_neg]

set_option maxHeartbeats 1000000 in
/-- **Faithfulness anchor (ALUTypeReader fragment) — Byte-bus interactions, SYNTACTIC.** Sibling of
`rtypereader_byte_…` (the nested `RegisterAccessCols → RegisterAccessTimestamp` descent surfacing the six
timestamp byte checks). ALU-type difference: the op_c timestamp byte checks are gated by `is_real - imm_c`
(the op_c `RegisterAccessCols` carries that multiplicity) — bound via `h_imm`, the mult matching the
oracle's `E29` (`sub_eq_add_neg` folds the circuit's `+ -` to the oracle's `-`). -/
theorem alutypereader_byte_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var Readers.ALUTypeReader.Inputs (ZMod p)) (offset : ℕ)
    (clk_high clk_low : ZMod p) (pc : Vector (ZMod p) 3) (opcode : ZMod p)
    (op_a_write_value : Word (ZMod p)) (cols : Extracted.ALUTypeReader (ZMod p)) (is_real is_trusted : ZMod p)
    (h_ir : Expression.eval env input.is_real = is_real)
    (h_cl : Expression.eval env input.clk_low = clk_low)
    (h_imm : Expression.eval env input.cols.imm_c = cols.imm_c)
    (h_pl_a : Expression.eval env input.cols.op_a_memory.access_timestamp.prev_low =
      cols.op_a_memory.access_timestamp.prev_low)
    (h_dl_a : Expression.eval env input.cols.op_a_memory.access_timestamp.diff_low_limb =
      cols.op_a_memory.access_timestamp.diff_low_limb)
    (h_pl_b : Expression.eval env input.cols.op_b_memory.access_timestamp.prev_low =
      cols.op_b_memory.access_timestamp.prev_low)
    (h_dl_b : Expression.eval env input.cols.op_b_memory.access_timestamp.diff_low_limb =
      cols.op_b_memory.access_timestamp.diff_low_limb)
    (h_pl_c : Expression.eval env input.cols.op_c_memory.access_timestamp.prev_low =
      cols.op_c_memory.access_timestamp.prev_low)
    (h_dl_c : Expression.eval env input.cols.op_c_memory.access_timestamp.diff_low_limb =
      cols.op_c_memory.access_timestamp.diff_low_limb) :
    (((Readers.ALUTypeReader.main input).operations offset).interactionsWith
        byteChannel.toRaw).map (AbstractInteraction.toAccess env)
      = ((Extracted.ALUTypeReader.interactions clk_high clk_low pc opcode op_a_write_value cols is_real
          is_trusted).map Extracted.Interaction.toAccess).filter (fun a => a.1 = InteractionKind.Byte) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h6 : (6 : ZMod p).val = 6 := by
    have h : (6 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt h
  have h3 : (3 : ZMod p).val = 3 := by
    have h : (3 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt h
  have hbk : ∀ (g : Expression (ZMod p)) (s : ByteRow (Expression (ZMod p))),
      AbstractInteraction.toAccess env ((pullIf (channel := byteChannel) g s).toRaw) =
        (InteractionKind.Byte, "SP1Byte",
          [(Expression.eval env s.opcode).val, (Expression.eval env s.a).val,
           (Expression.eval env s.b).val, (Expression.eval env s.c).val],
          signedVal (Expression.eval env (-g))) :=
    fun g s => toAccess_pullIf_byte env g s
  have heq := fun (n : ℕ) (inp : Var (ProvablePair id id) (ZMod p)) =>
    filter_interactions_formalAssertion_eq_nil (Gadgets.Equality.circuit id) byteChannel.toRaw
      (n := n) inp List.not_mem_nil List.not_mem_nil
  simp only [Readers.ALUTypeReader.main, Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    circuit_norm, FormalAssertion.toSubcircuit_interactions]
  simp [circuit_norm, hbk, Gadgets.Equality.main, Extracted.ALUTypeReader.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    ByteOpcode.ofNat_six, ByteOpcode.ofNat_three, ByteOpcode.idx, h6, h3,
    h_ir, h_cl, h_imm, h_pl_a, h_dl_a, h_pl_b, h_dl_b, h_pl_c, h_dl_c, sub_eq_add_neg]

end SP1Clean.Faithful
