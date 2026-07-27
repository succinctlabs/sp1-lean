import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Model.SP1Constraint
import SP1Clean.Model.InteractionProjection
import SP1Clean.Model.InteractionRecovery
import SP1Clean.Faithful.ExtractedInteractionModel
import SP1Clean.Native.Readers.RTypeReader
import SP1Clean.Extracted.RTypeReader
import SP1Clean.Faithful.ChipTactics

/-! # Faithfulness anchor — SP1's `RTypeReader` constraint fragment ↔ the native reader spec

Sibling of `Faithful/CPUState.lean`, for the register-adapter fragment. SP1's generated
`RTypeReader.constraints` (`Extracted/RTypeReader.lean`) emits, under `is_real = is_trusted = 1`:

- four copies of the `is_real` binary gate `.assertZero (is_real * (is_real - 1))` (vacuous at `1`);
- the `.send (.program …) is_trusted` instruction fetch (per-row meaning `True`; its content is the
  trace-level program bus, `Soundness/ProgramConsistency.lean`);
- per operand: a `.send (.byte Range diff 16 0)` (16-bit range) and a `.send (.byte U8Range 0 scaled 0)`
  (`< 256`) timestamp check, a `.send (.memory …)` (read prev) and a `.receive (.memory …)` (write/read
  new) — the memory interactions' per-row meaning is `True` (their content is the trace-level memory
  bus, `Soundness/MemoryConsistency.lean`);
- four `.assertZero (op_a_0 * (op_a_write_value[i] - 0))` zeroing gates (`rd = x0 ⟹ write 0`).

`rtypereader_constraints_faithful` proves the constraint lists hold exactly iff the four `op_a_0`
zeroing equations and the three operands' timestamp byte bounds — `Readers.RTypeReader.Spec` at
`is_real = 1` (the binary clause drops because `is_real` is pinned). -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

set_option maxHeartbeats 2000000 in
/-- **Faithfulness anchor (RTypeReader fragment).** Under `is_real = is_trusted = 1`, SP1's generated
`RTypeReader` constraint list holds iff the four `op_a_0` zeroing equations and the three operands'
timestamp byte bounds hold. The `.program`/`.memory` interactions contribute `True` (their meaning is
the trace-level buses); the four binary gates are vacuous at `is_real = 1`. -/
theorem rtypereader_constraints_faithful
    (clk_high clk_low : ZMod p) (pc : Vector (ZMod p) 3) (opcode : ZMod p)
    (op_a_write_value : Word (ZMod p)) (cols : Extracted.RTypeReader (ZMod p)) :
    (List.Forall (· = 0)
          (Extracted.RTypeReader.asserts clk_high clk_low pc opcode op_a_write_value cols 1 1) ∧
        List.Forall Interaction.toProp
          (Extracted.RTypeReader.interactions clk_high clk_low pc opcode op_a_write_value cols 1 1)) ↔
      ((cols.op_a_0 * op_a_write_value[0] = 0 ∧ cols.op_a_0 * op_a_write_value[1] = 0 ∧
          cols.op_a_0 * op_a_write_value[2] = 0 ∧ cols.op_a_0 * op_a_write_value[3] = 0) ∧
        (cols.op_a_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
          ((clk_low + 4 - cols.op_a_memory.access_timestamp.prev_low - 1
              - cols.op_a_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8) ∧
        (cols.op_b_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
          ((clk_low + 3 - cols.op_b_memory.access_timestamp.prev_low - 1
              - cols.op_b_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8) ∧
        (cols.op_c_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
          ((clk_low + 2 - cols.op_c_memory.access_timestamp.prev_low - 1
              - cols.op_c_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8)) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [Extracted.RTypeReader.asserts, Extracted.RTypeReader.interactions, List.Forall,
    Interaction.toProp_send_byte, Interaction.toProp_receive,
    Interaction.toProp_send_memory, Interaction.toProp_send_program,
    ByteOpcode.constrainField_six, ByteOpcode.constrainField_three,
    ByteOpcode.constrain_Range,
    ByteOpcode.constrain_U8Range, val_16, ZMod.val_zero, one_ne_zero, ne_eq, not_false_eq_true,
    true_implies, sub_self, mul_zero, sub_zero, Nat.ofNat_pos, true_and, and_true,
    show (2 : ℕ) ^ 8 = 256 by norm_num, show (2 : ℕ) ^ 16 = 65536 by norm_num]
  -- The simp leaves a right-associated flat conjunction; the RHS groups the byte facts per operand.
  -- Only associativity differs.
  tauto

omit [Fact (2 ^ 17 < p)] in
/-- **RTypeReader fragment — assertion half.** Under `is_real = 1`, SP1's generated `RTypeReader`
`asserts` list holds iff the four `op_a_0` zeroing equations (`rd = x0 ⟹ write 0`); the four binary
gates are vacuous at `is_real = 1`. -/
theorem rtypereader_asserts_faithful
    (clk_high clk_low : ZMod p) (pc : Vector (ZMod p) 3) (opcode : ZMod p)
    (op_a_write_value : Word (ZMod p)) (cols : Extracted.RTypeReader (ZMod p)) :
    List.Forall (· = 0)
        (Extracted.RTypeReader.asserts clk_high clk_low pc opcode op_a_write_value cols 1 1) ↔
      (cols.op_a_0 * op_a_write_value[0] = 0 ∧ cols.op_a_0 * op_a_write_value[1] = 0 ∧
        cols.op_a_0 * op_a_write_value[2] = 0 ∧ cols.op_a_0 * op_a_write_value[3] = 0) := by
  simp only [Extracted.RTypeReader.asserts, List.Forall, sub_self, mul_zero, sub_zero,
    true_and, and_true]

set_option maxHeartbeats 2000000 in
/-- **RTypeReader fragment — interaction half.** Under `is_real = is_trusted = 1`, SP1's generated
`RTypeReader` `interactions` list holds iff the three operands' timestamp byte bounds. The
`.program`/`.memory` interactions contribute `True`; the bounds come from the per-operand byte
sends. -/
theorem rtypereader_interactions_faithful
    (clk_high clk_low : ZMod p) (pc : Vector (ZMod p) 3) (opcode : ZMod p)
    (op_a_write_value : Word (ZMod p)) (cols : Extracted.RTypeReader (ZMod p)) :
    List.Forall Interaction.toProp
        (Extracted.RTypeReader.interactions clk_high clk_low pc opcode op_a_write_value cols 1 1) ↔
      ((cols.op_a_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
          ((clk_low + 4 - cols.op_a_memory.access_timestamp.prev_low - 1
              - cols.op_a_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8) ∧
        (cols.op_b_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
          ((clk_low + 3 - cols.op_b_memory.access_timestamp.prev_low - 1
              - cols.op_b_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8) ∧
        (cols.op_c_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
          ((clk_low + 2 - cols.op_c_memory.access_timestamp.prev_low - 1
              - cols.op_c_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8)) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [Extracted.RTypeReader.interactions, List.Forall,
    Interaction.toProp_send_byte, Interaction.toProp_receive,
    Interaction.toProp_send_memory, Interaction.toProp_send_program,
    ByteOpcode.constrainField_six, ByteOpcode.constrainField_three,
    ByteOpcode.constrain_Range,
    ByteOpcode.constrain_U8Range, val_16, ZMod.val_zero, one_ne_zero, ne_eq, not_false_eq_true,
    true_implies, Nat.ofNat_pos, true_and, and_true,
    show (2 : ℕ) ^ 8 = 256 by norm_num, show (2 : ℕ) ^ 16 = 65536 by norm_num]
  tauto

open SP1Clean.Channels (byteChannel memoryChannel MemoryMsg programChannel ProgramMsg)
open SP1Clean.InteractionRecovery

set_option maxHeartbeats 1000000 in
/-- **Faithfulness anchor (RTypeReader fragment) — Memory-bus interactions, SYNTACTIC.** Option B: the
reader is now a **pure read** — its op_a (`rd`) **write** is factored out into `RegisterWrite` (composed by
the chip). So the **five** Memory interactions the reader actually emits (`interactionsWith memoryChannel`:
op_a read, op_b read+write, op_c read+write) project to the same `LookupAccess` list as the Memory entries
of SP1's extracted `RTypeReader.interactions` oracle **with the op_a write dropped** (`.eraseIdx 1` — the
op_a write is Memory-index 1). The relocated op_a write is recovered at the chip level by `RegisterWrite`'s
own emit, so the *combined* chip Memory block still equals the full oracle (`Faithful/AddChip.lean`). Same
`op_a(read), op_b, op_c` order, so a clean `=` after the erase. Exercises the `.memory` arm of
`Extracted.Interaction.toAccess` and its `.send`/`.receive` `Dir.sign`. -/
theorem rtypereader_memory_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var Readers.RTypeReader.Inputs (ZMod p)) (offset : ℕ)
    (clk_high clk_low : ZMod p) (pc : Vector (ZMod p) 3) (opcode : ZMod p)
    (op_a_write_value : Word (ZMod p)) (cols : Extracted.RTypeReader (ZMod p)) (is_real is_trusted : ZMod p)
    (h_ir : Expression.eval env input.is_real = is_real)
    (h_ch : Expression.eval env input.clk_high = clk_high)
    (h_cl : Expression.eval env input.clk_low = clk_low)
    (h_oa : Expression.eval env input.cols.op_a = cols.op_a)
    (h_ob : Expression.eval env input.cols.op_b = cols.op_b)
    (h_oc : Expression.eval env input.cols.op_c = cols.op_c)
    -- (Option B) the op_a write left the reader, so the `op_a_write_value` eval-bridges `h_wv*` are gone.
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
    (((Readers.RTypeReader.main input).operations offset).interactionsWith
        memoryChannel.toRaw).map (AbstractInteraction.toAccess env)
      = ((((Extracted.RTypeReader.interactions clk_high clk_low pc opcode op_a_write_value cols is_real
          is_trusted).map Extracted.Interaction.toAccess).filter
            (fun a => a.1 = InteractionKind.Memory)).eraseIdx 1).map LookupAccessList.negMult := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp2 : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have hrac := fun (n : ℕ) (inp : Var Readers.RegisterAccessCols.Inputs (ZMod p)) =>
    filter_interactions_formalAssertion_eq_nil Readers.RegisterAccessCols.circuit memoryChannel.toRaw
      (n := n) inp (by simp [circuit_norm, Readers.RegisterAccessCols.circuit])
      (by simp [circuit_norm, Readers.RegisterAccessCols.circuit])
  have heq := fun (n : ℕ) (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil (ZMod p) _ (ProvablePair field field)
      ProvablePair.instance (Gadgets.Equality.circuit field) memoryChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  simp only [Readers.RTypeReader.main, circuit_norm, hrac, heq,
    SP1Clean.Channels.programChannel_eq_memoryChannel_false, if_false]
  -- W11 memory flip: reads are `pullIf` (mult `-is_real`), the op_b/op_c read-backs `pushIf` (mult `is_real`);
  -- the op_a write `pushIf` is GONE (factored to `RegisterWrite`), so the oracle's op_a write (Memory-index 1)
  -- is `eraseIdx 1`'d off the RHS, and the whole list is `negMult`-bridged (our pull/push polarity is the
  -- negation of SP1's send/receive — same up-to-sign bridge as the Program bus).
  simp only [toAccess_pushIf_memory, toAccess_pullIf_memory]
  -- RHS: unfold the oracle + projection, drop the byte/program entries (`.1 ≠ .Memory`) from the filter.
  simp only [Extracted.RTypeReader.interactions, List.map_cons, List.map_nil,
    Extracted.Interaction.toAccess, Extracted.Dir.sign, List.filter_cons]
  -- both sides are now the same five `.Memory` accesses (modulo `negMult`); bind the evals + sign bridge.
  simp [circuit_norm, LookupAccessList.negMult, signedVal_neg hp2,
    h_ir, h_ch, h_cl, h_oa, h_ob, h_oc,
    h_pl_a, h_pv_a0, h_pv_a1, h_pv_a2, h_pv_a3,
    h_pl_b, h_pv_b0, h_pv_b1, h_pv_b2, h_pv_b3,
    h_pl_c, h_pv_c0, h_pv_c1, h_pv_c2, h_pv_c3]

set_option maxHeartbeats 1000000 in
/-- **Faithfulness anchor (RTypeReader fragment) — Program-bus interaction, SYNTACTIC.** The single
Program instruction-fetch the reader emits projects to the same arity-16 `LookupAccess` as the Program
entry of SP1's extracted oracle. Exercises the `.program` arm of `Extracted.Interaction.toAccess`,
including the opcode coercion (`Opcode.ofNat opcode = opcode.val` via `ConstraintCoe.coe_eq_val`) and the
R-type operand shape (`0 + op_b = op_b`, literal-`0` higher limbs / `imm` flags). -/
theorem rtypereader_program_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var Readers.RTypeReader.Inputs (ZMod p)) (offset : ℕ)
    (clk_high clk_low : ZMod p) (pc : Vector (ZMod p) 3) (opcode : ZMod p)
    (op_a_write_value : Word (ZMod p)) (cols : Extracted.RTypeReader (ZMod p)) (is_real is_trusted : ZMod p)
    (h_it : Expression.eval env input.is_trusted = is_trusted)
    (h_p0 : Expression.eval env input.pc[0] = pc[0])
    (h_p1 : Expression.eval env input.pc[1] = pc[1])
    (h_p2 : Expression.eval env input.pc[2] = pc[2])
    (h_oc : Expression.eval env input.opcode = opcode)
    (h_oa : Expression.eval env input.cols.op_a = cols.op_a)
    (h_ob : Expression.eval env input.cols.op_b = cols.op_b)
    (h_oct : Expression.eval env input.cols.op_c = cols.op_c)
    (h_oa0 : Expression.eval env input.cols.op_a_0 = cols.op_a_0) :
    (((Readers.RTypeReader.main input).operations offset).interactionsWith
        programChannel.toRaw).map (AbstractInteraction.toAccess env)
      = (((Extracted.RTypeReader.interactions clk_high clk_low pc opcode op_a_write_value cols is_real
          is_trusted).map Extracted.Interaction.toAccess).filter
            (fun a => a.1 = InteractionKind.Program)).map LookupAccessList.negMult := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp2 : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have hrac := fun (n : ℕ) (inp : Var Readers.RegisterAccessCols.Inputs (ZMod p)) =>
    filter_interactions_formalAssertion_eq_nil Readers.RegisterAccessCols.circuit programChannel.toRaw
      (n := n) inp (by simp [circuit_norm, Readers.RegisterAccessCols.circuit])
      (by simp [circuit_norm, Readers.RegisterAccessCols.circuit])
  have heq := fun (n : ℕ) (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil (ZMod p) _ (ProvablePair field field)
      ProvablePair.instance (Gadgets.Equality.circuit field) programChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  simp only [Readers.RTypeReader.main, circuit_norm, hrac, heq,
    SP1Clean.Channels.memoryChannel_eq_programChannel_false, if_false]
  -- SC Phase 2a: `programChannel` is a `Channel` — `circuit_norm` recovers the program pull in the raw
  -- `ChannelInteraction.toRaw` form, so unfold the kernel's `pulledIf`/`toRaw` to match it (cf. the
  -- `StateConsistency` state-kernel pattern), then rewrite.
  have hk := fun (g : Expression (ZMod p)) (m : SP1Clean.Channels.ProgramMsg (Expression (ZMod p))) =>
    toAccess_pullIf_program env g m
  simp only [hk]
  simp only [Extracted.RTypeReader.interactions, List.map_cons, List.map_nil,
    Extracted.Interaction.toAccess, Extracted.Dir.sign, List.filter_cons]
  simp [circuit_norm, Opcode.ofNat, ConstraintCoe.coe_eq_val, LookupAccessList.negMult,
    signedVal_neg hp2,
    h_it, h_p0, h_p1, h_p2, h_oc, h_oa, h_ob, h_oct, h_oa0]

set_option maxHeartbeats 1000000 in
/-- **Faithfulness anchor (RTypeReader fragment) — Byte-bus interactions, SYNTACTIC.** The six timestamp
byte checks the reader emits — recovered **through two nested subcircuit levels** (`RTypeReader →
RegisterAccessCols → RegisterAccessTimestamp`) — project to the same `LookupAccess` list as the Byte
entries of SP1's extracted oracle. Per operand: a 16-bit `Range` on `diff_low_limb` and a `U8Range` on the
scaled high part; same `a,b,c` order as the oracle, so a clean `=`. -/
theorem rtypereader_byte_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var Readers.RTypeReader.Inputs (ZMod p)) (offset : ℕ)
    (clk_high clk_low : ZMod p) (pc : Vector (ZMod p) 3) (opcode : ZMod p)
    (op_a_write_value : Word (ZMod p)) (cols : Extracted.RTypeReader (ZMod p)) (is_real is_trusted : ZMod p)
    (h_ir : Expression.eval env input.is_real = is_real)
    (h_cl : Expression.eval env input.clk_low = clk_low)
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
    (((Readers.RTypeReader.main input).operations offset).interactionsWith
        byteChannel.toRaw).map (AbstractInteraction.toAccess env)
      = ((Extracted.RTypeReader.interactions clk_high clk_low pc opcode op_a_write_value cols is_real
          is_trusted).map Extracted.Interaction.toAccess).filter (fun a => a.1 = InteractionKind.Byte) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h6 : (6 : ZMod p).val = 6 := by
    have h : (6 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt h
  have h3 : (3 : ZMod p).val = 3 := by
    have h : (3 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt h
  have hbk : ∀ (g : Expression (ZMod p)) (s : ByteRow (Expression (ZMod p))),
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
  -- descend through the two nested `FormalAssertion` sub-readers (`RegisterAccessCols →
  -- RegisterAccessTimestamp`) to surface the byte emits (Clean's general `interactionsWith_subcircuit`
  -- only exposes the flat `.ops.toFlat`; `FormalAssertion.toSubcircuit_interactions` rewrites that back to
  -- the child `main`'s interactions, recursively — so the sub-readers' `main`/`circuit` defs must unfold).
  simp only [Readers.RTypeReader.main, Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    circuit_norm, FormalAssertion.toSubcircuit_interactions]
  -- the six byte pulls have surfaced (in filter-`if` form); reduce the filters, map via the byte kernel,
  -- unfold the oracle + its `.Byte` filter, and bind the evals.
  simp [circuit_norm, hbk, Gadgets.Equality.main, Extracted.RTypeReader.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign, h6, h3,
    h_ir, h_cl, h_pl_a, h_dl_a, h_pl_b, h_dl_b, h_pl_c, h_dl_c]

end SP1Clean.Faithful
