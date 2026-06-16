import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Model.SP1Constraint
import SP1Clean.Faithful.ChipTactics
import SP1Clean.Extracted.AddChip
import SP1Clean.Faithful.AddOperation
import SP1Clean.Faithful.CPUState
import SP1Clean.Faithful.RTypeReader
import SP1Clean.Chips.AddChip.Defs

/-! # Chip-level faithfulness anchor — SP1's whole `Add` chip constraint list ↔ the combined spec

Where `Faithful/{AddOperation,CPUState,RTypeReader}` anchor each *fragment*, this anchors the **entire**
generated `Extracted.AddCols.constraints` list. SP1's chip constraints are
`CS0 ++ CS1 ++ CS2 ++ [binary gate, op_a_0 = 0]` (`CS0` = `AddOperation.constraints` on the register-read
columns, `CS1` = `CPUState.constraints`, `CS2` = `RTypeReader.constraints`); splitting at each `++`
(`forall_append_pair`) discharges each fragment by its anchor, leaving the two trailing `assertZero`s
(the binary gate, vacuous at `is_real = 1`, and the `op_a_0 = 0` register-index gate).

So one theorem certifies SP1's generated `Add` chip constraint list means **exactly**: the `AddOperation`
raw arithmetic spec on the register-read operands, the two CPUState clock byte bounds, the RTypeReader
per-row well-formedness, and `op_a_0 = 0`. -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

set_option maxHeartbeats 2000000 in
/-- **Chip-level faithfulness anchor — assertion half.** Under `is_real = 1`, SP1's generated `Add`
chip `asserts` list holds iff: the `AddOperation` assertion spec (carry-bools) on the register-read
operands and result word, the four `op_a_0` zeroing equations, and the `op_a_0 = 0` register-index
gate. (CPUState contributes no assertions.) -/
theorem addcols_asserts_faithful (cols : Extracted.AddCols (ZMod p)) (h_real : cols.is_real = 1) :
    List.Forall (· = 0) (Extracted.AddCols.asserts cols) ↔
      ( AddOperation.AssertSpec
          #v[cols.adapter.op_b_memory.prev_value[0], cols.adapter.op_b_memory.prev_value[1],
              cols.adapter.op_b_memory.prev_value[2], cols.adapter.op_b_memory.prev_value[3]]
          #v[cols.adapter.op_c_memory.prev_value[0], cols.adapter.op_c_memory.prev_value[1],
              cols.adapter.op_c_memory.prev_value[2], cols.adapter.op_c_memory.prev_value[3]]
          #v[cols.add_operation.value[0], cols.add_operation.value[1],
              cols.add_operation.value[2], cols.add_operation.value[3]]
        ∧ (cols.adapter.op_a_0 * cols.add_operation.value[0] = 0 ∧
            cols.adapter.op_a_0 * cols.add_operation.value[1] = 0 ∧
            cols.adapter.op_a_0 * cols.add_operation.value[2] = 0 ∧
            cols.adapter.op_a_0 * cols.add_operation.value[3] = 0)
        ∧ cols.adapter.op_a_0 = 0 ) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  faithful_chip_assert Extracted.AddCols.asserts h_real
    add_asserts_faithful rtypereader_asserts_faithful

set_option maxHeartbeats 2000000 in
/-- **Chip-level faithfulness anchor — interaction half.** Under `is_real = 1`, SP1's generated `Add`
chip `interactions` list holds iff: the `AddOperation` interaction spec (result-limb ranges), the two
CPUState clock-range bounds, and the three operands' RTypeReader timestamp byte bounds. -/
theorem addcols_interactions_faithful (cols : Extracted.AddCols (ZMod p)) (h_real : cols.is_real = 1) :
    List.Forall Interaction.toProp (Extracted.AddCols.interactions cols) ↔
      ( AddOperation.InteractSpec
          #v[cols.add_operation.value[0], cols.add_operation.value[1],
              cols.add_operation.value[2], cols.add_operation.value[3]]
        ∧ (((cols.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧ cols.state.clk_16_24.val < 2 ^ 8)
        ∧ ( (cols.adapter.op_a_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
              ((cols.state.clk_0_16 + cols.state.clk_16_24 * 65536 + 4
                  - cols.adapter.op_a_memory.access_timestamp.prev_low - 1
                  - cols.adapter.op_a_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8) ∧
            (cols.adapter.op_b_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
              ((cols.state.clk_0_16 + cols.state.clk_16_24 * 65536 + 3
                  - cols.adapter.op_b_memory.access_timestamp.prev_low - 1
                  - cols.adapter.op_b_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8) ∧
            (cols.adapter.op_c_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
              ((cols.state.clk_0_16 + cols.state.clk_16_24 * 65536 + 2
                  - cols.adapter.op_c_memory.access_timestamp.prev_low - 1
                  - cols.adapter.op_c_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8) ) ) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  faithful_chip_interact Extracted.AddCols.interactions h_real
    add_interactions_faithful rtypereader_interactions_faithful

open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel StateMsg)
open SP1Clean.InteractionRecovery

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- **Chip-level faithfulness anchor — State-bus interactions, SYNTACTIC.** The State interactions the
whole `AddChip` row emits (recovered by descending the chip into its three composed sub-readers) project
to the same `LookupAccess` list as the State entries of SP1's extracted `AddCols.interactions` oracle.
Only the `CPUState` fragment emits State, so this is a clean `=` (no fragment-reorder `Perm`); the `Add`
and `RTypeReader` byte/memory/program emits drop under the `State` channel filter. Witness-free (the
State bus does not touch the witnessed ALU result). -/
theorem addcols_state_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var AddChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : Extracted.AddCols (ZMod p))
    (h_ir : Expression.eval env input.is_real = cols.is_real)
    (h_ch : Expression.eval env input.state.clk_high = cols.state.clk_high)
    (h_c0 : Expression.eval env input.state.clk_0_16 = cols.state.clk_0_16)
    (h_c1 : Expression.eval env input.state.clk_16_24 = cols.state.clk_16_24)
    (h_p0 : Expression.eval env input.state.pc[0] = cols.state.pc[0])
    (h_p1 : Expression.eval env input.state.pc[1] = cols.state.pc[1])
    (h_p2 : Expression.eval env input.state.pc[2] = cols.state.pc[2]) :
    (((AddChip.main input).operations offset).interactionsWith stateChannel.toRaw).map
        (AbstractInteraction.toAccess env)
      = ((Extracted.AddCols.interactions cols).map Extracted.Interaction.toAccess).filter
          (fun a => a.1 = InteractionKind.State) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hsk : ∀ (m : Expression (ZMod p)) (s : StateMsg (Expression (ZMod p))),
      AbstractInteraction.toAccess env ((pushIf (channel := stateChannel) m s).toRaw) =
        (InteractionKind.State, "SP1State",
          [(Expression.eval env s.clk_high).val, (Expression.eval env s.clk_low).val,
           (Expression.eval env s.pc0).val, (Expression.eval env s.pc1).val,
           (Expression.eval env s.pc2).val], signedVal (Expression.eval env m)) :=
    fun m s => toAccess_pushIf_state env m s
  have heq := fun (n : ℕ) (inp : Var (ProvablePair id id) (ZMod p)) =>
    filter_interactions_formalAssertion_eq_nil (Gadgets.Equality.circuit id) stateChannel.toRaw
      (n := n) inp List.not_mem_nil List.not_mem_nil
  -- descend the chip into its three sub-readers; the `Add`/`RTypeReader` byte/mem/program emits drop under
  -- the `State` filter (channel distinctness), leaving CPUState's two State interactions.
  simp only [AddChip.main, Readers.CPUState.circuit, Readers.CPUState.main,
    Readers.RTypeReader.circuit, Readers.RTypeReader.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    SP1Clean.AddOperation.circuit, SP1Clean.AddOperation.main,
    circuit_norm, FormalAssertion.toSubcircuit_interactions, hsk, heq]
  -- the residual: CPUState's 2 State interactions (via `hsk`), everything else dropped by the `State`
  -- filter (byte/mem/program channel distinctness) or emitting nothing (`Gadgets.Equality.main`); the
  -- oracle `.filter .State` likewise keeps only the CPUState fragment's 2 State entries.
  simp [circuit_norm, hsk, Gadgets.Equality.main,
    Extracted.AddCols.interactions, Extracted.AddOperation.interactions,
    Extracted.CPUState.interactions, Extracted.RTypeReader.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    h_ir, h_ch, h_c0, h_c1, h_p0, h_p1, h_p2]

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- **Chip-level faithfulness anchor — Program-bus interaction, SYNTACTIC.** The single Program
instruction-fetch the whole `AddChip` row emits (only the `RTypeReader` fragment emits Program) projects
to the same arity-16 `LookupAccess` as the Program entry of SP1's extracted `AddCols.interactions`
oracle. Witness-free (the Program tuple is the decoded instruction, not the ALU result). -/
theorem addcols_program_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var AddChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : Extracted.AddCols (ZMod p))
    (h_ir : Expression.eval env input.is_real = cols.is_real)
    (h_p0 : Expression.eval env input.state.pc[0] = cols.state.pc[0])
    (h_p1 : Expression.eval env input.state.pc[1] = cols.state.pc[1])
    (h_p2 : Expression.eval env input.state.pc[2] = cols.state.pc[2])
    (h_oa : Expression.eval env input.adapter.op_a = cols.adapter.op_a)
    (h_ob : Expression.eval env input.adapter.op_b = cols.adapter.op_b)
    (h_oc : Expression.eval env input.adapter.op_c = cols.adapter.op_c)
    (h_oa0 : Expression.eval env input.adapter.op_a_0 = cols.adapter.op_a_0) :
    (((AddChip.main input).operations offset).interactionsWith programChannel.toRaw).map
        (AbstractInteraction.toAccess env)
      = ((Extracted.AddCols.interactions cols).map Extracted.Interaction.toAccess).filter
          (fun a => a.1 = InteractionKind.Program) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have heq := fun (n : ℕ) (inp : Var (ProvablePair id id) (ZMod p)) =>
    filter_interactions_formalAssertion_eq_nil (Gadgets.Equality.circuit id) programChannel.toRaw
      (n := n) inp List.not_mem_nil List.not_mem_nil
  simp only [AddChip.main, Readers.CPUState.circuit, Readers.CPUState.main,
    Readers.RTypeReader.circuit, Readers.RTypeReader.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    SP1Clean.AddOperation.circuit, SP1Clean.AddOperation.main,
    circuit_norm, FormalAssertion.toSubcircuit_interactions, toAccess_pushIf_program, heq]
  -- only RTypeReader's Program emit survives the `Program` filter; close via the kernel + bindings + the
  -- opcode coercion (`Opcode.ofNat 0 = 0`), then drop the byte/state/memory residual by channel name.
  simp [circuit_norm, toAccess_pushIf_program, Gadgets.Equality.main,
    Extracted.AddCols.interactions, Extracted.AddOperation.interactions,
    Extracted.CPUState.interactions, Extracted.RTypeReader.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign, Opcode.ofNat, ConstraintCoe.coe_eq_val,
    h_ir, h_p0, h_p1, h_p2, h_oa, h_ob, h_oc, h_oa0]

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- **Chip-level faithfulness anchor — Memory-bus interactions, SYNTACTIC (composition + WITNESSED).** The
six Memory interactions the whole `AddChip` row emits (only the `RTypeReader` fragment emits Memory)
project to the same `LookupAccess` list as the Memory entries of SP1's extracted `AddCols.interactions`
oracle. The first chip-level anchor combining both techniques: it descends the chip to the `RTypeReader`
memory emits, and the `op_a` write value is the chip-**witnessed** ALU result `cols.add_operation.value`,
bound via `env.get (offset + k)` (the witnessed columns at the chip offset). The `clk_low` E4
(`clk_0_16 + clk_16_24 * 2^16`) is reconstructed from `h_c0`/`h_c1`. -/
theorem addcols_memory_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var AddChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : Extracted.AddCols (ZMod p))
    (h_ir : Expression.eval env input.is_real = cols.is_real)
    (h_ch : Expression.eval env input.state.clk_high = cols.state.clk_high)
    (h_c0 : Expression.eval env input.state.clk_0_16 = cols.state.clk_0_16)
    (h_c1 : Expression.eval env input.state.clk_16_24 = cols.state.clk_16_24)
    (h_oa : Expression.eval env input.adapter.op_a = cols.adapter.op_a)
    (h_ob : Expression.eval env input.adapter.op_b = cols.adapter.op_b)
    (h_oc : Expression.eval env input.adapter.op_c = cols.adapter.op_c)
    (h_wv0 : env.get offset = cols.add_operation.value[0])
    (h_wv1 : env.get (offset + 1) = cols.add_operation.value[1])
    (h_wv2 : env.get (offset + 2) = cols.add_operation.value[2])
    (h_wv3 : env.get (offset + 3) = cols.add_operation.value[3])
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
    (((AddChip.main input).operations offset).interactionsWith memoryChannel.toRaw).map
        (AbstractInteraction.toAccess env)
      = ((Extracted.AddCols.interactions cols).map Extracted.Interaction.toAccess).filter
          (fun a => a.1 = InteractionKind.Memory) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have heq := fun (n : ℕ) (inp : Var (ProvablePair id id) (ZMod p)) =>
    filter_interactions_formalAssertion_eq_nil (Gadgets.Equality.circuit id) memoryChannel.toRaw
      (n := n) inp List.not_mem_nil List.not_mem_nil
  simp only [AddChip.main, Readers.CPUState.circuit, Readers.CPUState.main,
    Readers.RTypeReader.circuit, Readers.RTypeReader.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    SP1Clean.AddOperation.circuit, SP1Clean.AddOperation.main,
    circuit_norm, FormalAssertion.toSubcircuit_interactions, toAccess_pushIf_memory, heq]
  simp [circuit_norm, toAccess_pushIf_memory, Gadgets.Equality.main,
    Extracted.AddCols.interactions, Extracted.AddOperation.interactions,
    Extracted.CPUState.interactions, Extracted.RTypeReader.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    h_ir, h_ch, h_c0, h_c1, h_oa, h_ob, h_oc,
    h_wv0, h_wv1, h_wv2, h_wv3, h_pl_a, h_pv_a0, h_pv_a1, h_pv_a2, h_pv_a3,
    h_pl_b, h_pv_b0, h_pv_b1, h_pv_b2, h_pv_b3,
    h_pl_c, h_pv_c0, h_pv_c1, h_pv_c2, h_pv_c3]

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- **Chip-level faithfulness anchor — Byte-bus interactions, SYNTACTIC (multi-fragment `Perm` + WITNESSED).**
All three fragments emit byte: `CPUState` (2 clock checks), `AddOperation` (4 result-limb ranges on the
chip-**witnessed** ALU `value`), `RTypeReader` (6 timestamp checks). The circuit emits them in order
`[CPUState 2] ++ [Add 4] ++ [RTypeReader 6]`, the oracle lists `[Add 4] ++ [CPUState 2] ++ [RTypeReader 6]`
— the first two blocks swapped, so this is a `List.Perm` (the bus is a multiset). The `Add` block's
`value[k]` is bound via `env.get (offset + k)`. -/
theorem addcols_byte_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var AddChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : Extracted.AddCols (ZMod p))
    (h_ir : Expression.eval env input.is_real = cols.is_real)
    (h_c0 : Expression.eval env input.state.clk_0_16 = cols.state.clk_0_16)
    (h_c1 : Expression.eval env input.state.clk_16_24 = cols.state.clk_16_24)
    (h_wv0 : env.get offset = cols.add_operation.value[0])
    (h_wv1 : env.get (offset + 1) = cols.add_operation.value[1])
    (h_wv2 : env.get (offset + 2) = cols.add_operation.value[2])
    (h_wv3 : env.get (offset + 3) = cols.add_operation.value[3])
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
      ((((AddChip.main input).operations offset).interactionsWith byteChannel.toRaw).map
        (AbstractInteraction.toAccess env))
      (((Extracted.AddCols.interactions cols).map Extracted.Interaction.toAccess).filter
          (fun a => a.1 = InteractionKind.Byte)) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h6 : (6 : ZMod p).val = 6 := by
    have h : (6 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt h
  have h3 : (3 : ZMod p).val = 3 := by
    have h : (3 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt h
  have hk : ∀ (g : Expression (ZMod p)) (s : ByteRow (Expression (ZMod p))),
      AbstractInteraction.toAccess env ((pullIf (channel := byteChannel) g s).toRaw) =
        (InteractionKind.Byte, "SP1Byte",
          [(Expression.eval env s.opcode).val, (Expression.eval env s.a).val,
           (Expression.eval env s.b).val, (Expression.eval env s.c).val],
          signedVal (Expression.eval env (-g))) :=
    fun g s => toAccess_pullIf_byte env g s
  have heq := fun (n : ℕ) (inp : Var (ProvablePair id id) (ZMod p)) =>
    filter_interactions_formalAssertion_eq_nil (Gadgets.Equality.circuit id) byteChannel.toRaw
      (n := n) inp List.not_mem_nil List.not_mem_nil
  simp only [AddChip.main, Readers.CPUState.circuit, Readers.CPUState.main,
    Readers.RTypeReader.circuit, Readers.RTypeReader.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    SP1Clean.AddOperation.circuit, SP1Clean.AddOperation.main,
    circuit_norm, FormalAssertion.toSubcircuit_interactions, hk, heq]
  simp [circuit_norm, hk, Gadgets.Equality.main,
    Extracted.AddCols.interactions, Extracted.AddOperation.interactions,
    Extracted.CPUState.interactions, Extracted.RTypeReader.interactions,
    Extracted.Interaction.toAccess_byte, Extracted.Interaction.toAccess, Extracted.Dir.sign,
    ByteOpcode.ofNat_six, ByteOpcode.ofNat_three, ByteOpcode.idx, ZMod.val_zero,
    h_ir, h_c0, h_c1, h_wv0, h_wv1, h_wv2, h_wv3,
    h_pl_a, h_dl_a, h_pl_b, h_dl_b, h_pl_c, h_dl_c, h6, h3, sub_eq_add_neg]
  -- circuit `[CPUState 2] ++ [Add 4] ++ [RTypeReader 6]` vs oracle `[Add 4] ++ [CPUState 2] ++ [RT 6]`:
  -- swap the first two blocks (the `RTypeReader 6` tail is shared).
  exact (List.perm_append_comm (l₁ := [_, _]) (l₂ := [_, _, _, _])).append_right [_, _, _, _, _, _]

set_option maxHeartbeats 4000000 in
/-- **Chip-level faithfulness anchor — COMBINED, SYNTACTIC.** The full faithfulness statement for `AddChip`:
the interactions the row emits on its four buses — `State`, `Byte`, `Memory`, `Program` — taken together
are a `List.Perm` of SP1's *entire* extracted `AddCols.interactions` oracle (projected to `LookupAccess`).
Assembled from the four per-channel anchors via `perm_filter_by_kind` (which decomposes the oracle image
into its four `InteractionKind` blocks) + `List.Perm.append` (Byte is the only `Perm`; State/Memory/Program
are `=`). No semantics, no channel filter — the complete emitted-interaction list vs the complete oracle.
This closes out `AddChip`'s four-artifact chain at the syntactic-interaction level. -/
theorem addcols_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var AddChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : Extracted.AddCols (ZMod p))
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
    (h_wv0 : env.get offset = cols.add_operation.value[0])
    (h_wv1 : env.get (offset + 1) = cols.add_operation.value[1])
    (h_wv2 : env.get (offset + 2) = cols.add_operation.value[2])
    (h_wv3 : env.get (offset + 3) = cols.add_operation.value[3])
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
      (((((AddChip.main input).operations offset).interactionsWith stateChannel.toRaw).map
          (AbstractInteraction.toAccess env)) ++
        ((((AddChip.main input).operations offset).interactionsWith byteChannel.toRaw).map
          (AbstractInteraction.toAccess env)) ++
        ((((AddChip.main input).operations offset).interactionsWith memoryChannel.toRaw).map
          (AbstractInteraction.toAccess env)) ++
        ((((AddChip.main input).operations offset).interactionsWith programChannel.toRaw).map
          (AbstractInteraction.toAccess env)))
      ((Extracted.AddCols.interactions cols).map Extracted.Interaction.toAccess) := by
  have hS := addcols_state_interactions_faithful_syntactic env input offset cols h_ir h_ch h_c0 h_c1 h_p0 h_p1 h_p2
  have hP := addcols_program_interactions_faithful_syntactic env input offset cols h_ir h_p0 h_p1 h_p2
    h_oa h_ob h_oc h_oa0
  have hM := addcols_memory_interactions_faithful_syntactic env input offset cols h_ir h_ch h_c0 h_c1
    h_oa h_ob h_oc h_wv0 h_wv1 h_wv2 h_wv3 h_pl_a h_pv_a0 h_pv_a1 h_pv_a2 h_pv_a3
    h_pl_b h_pv_b0 h_pv_b1 h_pv_b2 h_pv_b3 h_pl_c h_pv_c0 h_pv_c1 h_pv_c2 h_pv_c3
  have hB := addcols_byte_interactions_faithful_syntactic env input offset cols h_ir h_c0 h_c1
    h_wv0 h_wv1 h_wv2 h_wv3 h_pl_a h_dl_a h_pl_b h_dl_b h_pl_c h_dl_c
  refine List.Perm.trans ?_ (LookupAccessList.perm_filter_by_kind _).symm
  rw [hS, hM, hP]
  exact ((hB.append_left _).append_right _).append_right _

end SP1Clean.Faithful
