import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Model.SP1Constraint
import SP1Clean.Model.InteractionProjection
import SP1Clean.Faithful.ExtractedInteractionModel
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Extracted.CPUState

/-! # Faithfulness anchor — SP1's `CPUState` constraint fragment ↔ the native reader spec

SP1's generated `CPUState.constraints` (`Extracted/CPUState.lean`) emits, under `is_real = 1`:
- the binary gate (vacuous);
- two State-bus interactions (per-row meaning `True`; content is the trace-level PC chain);
- the 13-bit `Range` clock check and the `U8Range` (`< 256`) clock check.

`cpustate_constraints_faithful` proves the constraint lists hold **exactly** iff the two clock-range
bounds — i.e. `Readers.CPUState.Spec`. -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- `(13 : ZMod p).val = 13` under `Fact (2^17 < p)`. -/
private lemma val_13 [NeZero p] : (13 : ZMod p).val = 13 := by
  have : (131072 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  exact ZMod.val_natCast_of_lt (show (13 : ℕ) < p by omega)

/-- **Faithfulness anchor (CPUState fragment).** Under `is_real = 1`, SP1's generated `CPUState`
constraint list holds iff the two clock-range bounds hold — i.e. iff `Readers.CPUState.Spec` holds.
The `.state` `receive`/`send` interactions contribute `True` (their meaning is the trace-level bus);
the binary gate is vacuous at `is_real = 1`. -/
theorem cpustate_constraints_faithful
    (cols : Extracted.CPUState (ZMod p)) (next_pc : Vector (ZMod p) 3) (clk_increment : ZMod p) :
    (List.Forall (· = 0) (Extracted.CPUState.asserts cols next_pc clk_increment 1) ∧
      List.Forall Interaction.toProp (Extracted.CPUState.interactions cols next_pc clk_increment 1)) ↔
      ((cols.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧ cols.clk_16_24.val < 2 ^ 8 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [Extracted.CPUState.asserts, Extracted.CPUState.interactions, List.Forall,
    Interaction.toProp_send_byte, Interaction.toProp_receive,
    Interaction.toProp_send_state, ByteOpcode.ofNat_six, ByteOpcode.ofNat_three,
    ByteOpcode.constrain_Range, ByteOpcode.constrain_U8Range, val_13, ZMod.val_zero,
    one_ne_zero, ne_eq, not_false_eq_true, true_implies, sub_self, mul_zero,
    Nat.ofNat_pos, true_and, and_true, show (2 : ℕ) ^ 8 = 256 by norm_num]

omit [Fact (2 ^ 17 < p)] in
/-- **CPUState fragment — assertion half.** `CPUState` emits only the (vacuous at `is_real = 1`)
binary gate as an `assert`, so its `asserts` list trivially holds. -/
theorem cpustate_asserts_faithful
    (cols : Extracted.CPUState (ZMod p)) (next_pc : Vector (ZMod p) 3) (clk_increment : ZMod p) :
    List.Forall (· = 0) (Extracted.CPUState.asserts cols next_pc clk_increment 1) ↔ True := by
  simp only [Extracted.CPUState.asserts, List.Forall, sub_self, mul_zero]

/-- **CPUState fragment — interaction half.** Under `is_real = 1`, SP1's generated `CPUState`
`interactions` list holds iff the two clock-range bounds hold — i.e. iff `Readers.CPUState.Spec`. The
`.state` interactions contribute `True`; the two clock bounds come from the byte sends. -/
theorem cpustate_interactions_faithful
    (cols : Extracted.CPUState (ZMod p)) (next_pc : Vector (ZMod p) 3) (clk_increment : ZMod p) :
    List.Forall Interaction.toProp (Extracted.CPUState.interactions cols next_pc clk_increment 1) ↔
      ((cols.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧ cols.clk_16_24.val < 2 ^ 8 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [Extracted.CPUState.interactions, List.Forall,
    Interaction.toProp_send_byte, Interaction.toProp_receive,
    Interaction.toProp_send_state, ByteOpcode.ofNat_six, ByteOpcode.ofNat_three,
    ByteOpcode.constrain_Range, ByteOpcode.constrain_U8Range, val_13, ZMod.val_zero,
    one_ne_zero, ne_eq, not_false_eq_true, true_implies,
    Nat.ofNat_pos, true_and, and_true, show (2 : ℕ) ^ 8 = 256 by norm_num]

open SP1Clean.Channels (stateChannel byteChannel StateMsg)

/-- **Faithfulness anchor (CPUState fragment) — interaction half, SYNTACTIC.** The reader's emitted
interaction list and SP1's extracted `CPUState.interactions` project to the same `LookupAccess`
multiset. Exercises both the State and Byte buses; the relation is `List.Perm` (the reader emits
byte,byte,state,state while the oracle lists state,state,byte,byte). The U8Range tuple
`⟨3, 0, clk_16_24, 0⟩` slot order matters — `toProp` had masked an earlier mismatch. -/
theorem cpustate_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var Readers.CPUState.Inputs (ZMod p)) (offset : ℕ)
    (cols : Extracted.CPUState (ZMod p)) (next_pc : Vector (ZMod p) 3) (clk_inc is_real : ZMod p)
    (h_ir : Expression.eval env input.is_real = is_real)
    (h_ch : Expression.eval env input.cols.clk_high = cols.clk_high)
    (h_c0 : Expression.eval env input.cols.clk_0_16 = cols.clk_0_16)
    (h_c1 : Expression.eval env input.cols.clk_16_24 = cols.clk_16_24)
    (h_p0 : Expression.eval env input.cols.pc[0] = cols.pc[0])
    (h_p1 : Expression.eval env input.cols.pc[1] = cols.pc[1])
    (h_p2 : Expression.eval env input.cols.pc[2] = cols.pc[2])
    (h_np0 : Expression.eval env input.next_pc[0] = next_pc[0])
    (h_np1 : Expression.eval env input.next_pc[1] = next_pc[1])
    (h_np2 : Expression.eval env input.next_pc[2] = next_pc[2])
    (h_clk : Expression.eval env input.clk_inc = clk_inc) :
    List.Perm
      ((((Readers.CPUState.main input).operations offset).interactions).map
        (AbstractInteraction.toAccess env))
      ((Extracted.CPUState.interactions cols next_pc clk_inc is_real).map
          Extracted.Interaction.toAccess) := by
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
  have hsk : ∀ (m : Expression (ZMod p)) (s : StateMsg (Expression (ZMod p))),
      AbstractInteraction.toAccess env ((pushIf (channel := stateChannel) m s).toRaw) =
        (InteractionKind.State, "SP1State",
          [(Expression.eval env s.clk_high).val, (Expression.eval env s.clk_low).val,
           (Expression.eval env s.pc0).val, (Expression.eval env s.pc1).val,
           (Expression.eval env s.pc2).val], signedVal (Expression.eval env m)) :=
    fun m s => toAccess_pushIf_state env m s
  simp only [Readers.CPUState.main, circuit_norm, hbk, hsk,
    Extracted.CPUState.interactions, List.map_cons, List.map_nil,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    ByteOpcode.ofNat_six, ByteOpcode.ofNat_three, ByteOpcode.idx,
    h_ir, h_ch, h_c0, h_c1, h_p0, h_p1, h_p2, h_np0, h_np1, h_np2, h_clk, h6, h3,
    sub_eq_add_neg]
  -- both sides are now the same 4 `LookupAccess`es; the reader emits [byte,byte,state,state] and the
  -- oracle [state,state,byte,byte] — a two-block rotation, closed by `List.perm_append_comm`.
  exact List.perm_append_comm (l₁ := [_, _]) (l₂ := [_, _])

set_option maxHeartbeats 1000000 in
/-- **CPUState fragment — Byte-bus interactions, SYNTACTIC (channel-filtered `=`).** The `.Byte`-filtered
companion of `cpustate_interactions_faithful_syntactic`: the two byte clock-range checks the reader emits
project to the same `LookupAccess` list as the Byte entries of SP1's extracted `CPUState.interactions`
oracle. Both emit `byte,byte` in the same order, so this is a clean `=` (no `Perm`). The reusable byte
chunk every chip's combined byte anchor composes. -/
theorem cpustate_byte_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var Readers.CPUState.Inputs (ZMod p)) (offset : ℕ)
    (cols : Extracted.CPUState (ZMod p)) (next_pc : Vector (ZMod p) 3) (clk_inc is_real : ZMod p)
    (h_ir : Expression.eval env input.is_real = is_real)
    (h_c0 : Expression.eval env input.cols.clk_0_16 = cols.clk_0_16)
    (h_c1 : Expression.eval env input.cols.clk_16_24 = cols.clk_16_24) :
    (((Readers.CPUState.main input).operations offset).interactionsWith byteChannel.toRaw).map
        (AbstractInteraction.toAccess env)
      = ((Extracted.CPUState.interactions cols next_pc clk_inc is_real).map
          Extracted.Interaction.toAccess).filter (fun a => a.1 = InteractionKind.Byte) := by
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
  simp [Readers.CPUState.main, circuit_norm, hbk,
    Extracted.CPUState.interactions, List.map_cons, List.map_nil,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    ByteOpcode.ofNat_six, ByteOpcode.ofNat_three, ByteOpcode.idx,
    h_ir, h_c0, h_c1, h6, h3, sub_eq_add_neg]

end SP1Clean.Faithful
