import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Foundations.SP1Constraint
import SP1Clean.Extracted.LoadDoubleChip
import SP1Clean.Faithful.AddressOperation
import SP1Clean.Faithful.CPUState
import SP1Clean.Faithful.ITypeReader

/-! # Chip-level faithfulness anchor — SP1's whole `LoadDouble` chip constraint list ↔ combined spec

Anchors the entire generated `Extracted.LoadDoubleColumns.asserts`/`interactions` to the native
combined spec, composing the fragment anchors in `Faithful/{AddressOperation,CPUState,ITypeReader}`.
SP1's chip constraints are `CS0 ++ CS1 ++ CS2 ++ [MemoryAccess timestamp gates + op_a_0]`, where
`CS0` = `AddressOperation` (the 3-limb `rs1 + signExtend(imm)` address gadget), `CS1` = `CPUState`
(`next_pc = pc + 4`, clk + 8), `CS2` = `ITypeReader` (opcode `35 = LD`, op_a write / op_b read).
We split at each `++` (`forall_append_pair`) and discharge each fragment by its anchor, leaving the
inlined `MemoryAccess` timestamp constraints (the `compare_low` binary + high/low timestamp selection
+ `diff = clk − prev − 1` limb decomposition) and the two byte range checks (`diff_low < 2^16`,
`diff_high < 2^8`), plus the `op_a_0 = 0` register-index gate. The two `.memory` bus interactions and
the `.program` fetch contribute `True` (their meaning is the trace-level buses,
`Soundness/{Memory,Program}Consistency.lean`). Composed from axiom-clean fragment anchors. -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- `(16 : ZMod p).val = 16` under `Fact (2^17 < p)`. -/
private lemma val_16 [NeZero p] : (16 : ZMod p).val = 16 := by
  have : (131072 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  exact ZMod.val_natCast_of_lt (show (16 : ℕ) < p by omega)

set_option maxHeartbeats 4000000 in
/-- **Chip-level faithfulness anchor.** Under `is_real = 1`, SP1's generated `LoadDouble` chip
constraint list holds iff: the `AddressOperation` raw spec on the `rs1` register read and the
immediate (offset bits `0`); the two CPUState clock bounds; the `ITypeReader` per-row
well-formedness (the four `op_a_0` zeroing gates on the loaded word + the op_a/op_b timestamp byte
bounds); the `MemoryAccess` timestamp consistency (`compare_low` binary, the high-timestamp
selection gate, the `clk − prev − 1 = diff` decomposition, and the `diff_low < 2^16` / `diff_high <
2^8` byte ranges); and the `op_a_0 = 0` register-index gate. -/
theorem loaddoublecols_constraints_faithful (cols : Extracted.LoadDoubleColumns (ZMod p))
    (h_real : cols.is_real = 1) :
    (List.Forall (· = 0) (Extracted.LoadDoubleColumns.asserts cols) ∧
      List.Forall Interaction.toProp (Extracted.LoadDoubleColumns.interactions cols)) ↔
      ((SP1Clean.AddressOperation.RawSpec
            #v[cols.adapter.op_b_memory.prev_value[0], cols.adapter.op_b_memory.prev_value[1],
              cols.adapter.op_b_memory.prev_value[2], cols.adapter.op_b_memory.prev_value[3]]
            #v[cols.adapter.op_c_imm[0], cols.adapter.op_c_imm[1], cols.adapter.op_c_imm[2],
              cols.adapter.op_c_imm[3]] 0 0 0
            { addr_operation :=
                { value := #v[cols.address_operation.addr_operation.value[0],
                    cols.address_operation.addr_operation.value[1],
                    cols.address_operation.addr_operation.value[2]] },
              top_two_limb_inv := cols.address_operation.top_two_limb_inv }
          ∧ (((cols.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13
              ∧ cols.state.clk_16_24.val < 2 ^ 8))
        ∧ ((cols.adapter.op_a_0 * cols.memory_access.prev_value[0] = 0 ∧
              cols.adapter.op_a_0 * cols.memory_access.prev_value[1] = 0 ∧
              cols.adapter.op_a_0 * cols.memory_access.prev_value[2] = 0 ∧
              cols.adapter.op_a_0 * cols.memory_access.prev_value[3] = 0) ∧
            (cols.adapter.op_a_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
              ((cols.state.clk_0_16 + cols.state.clk_16_24 * 65536 + 4
                  - cols.adapter.op_a_memory.access_timestamp.prev_low - 1
                  - cols.adapter.op_a_memory.access_timestamp.diff_low_limb)
                    * (65536 : ZMod p)⁻¹).val < 2 ^ 8) ∧
            cols.adapter.op_b_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
              ((cols.state.clk_0_16 + cols.state.clk_16_24 * 65536 + 3
                  - cols.adapter.op_b_memory.access_timestamp.prev_low - 1
                  - cols.adapter.op_b_memory.access_timestamp.diff_low_limb)
                    * (65536 : ZMod p)⁻¹).val < 2 ^ 8)
        ∧ ((cols.memory_access.access_timestamp.compare_low
                * (cols.memory_access.access_timestamp.compare_low - 1) = 0 ∧
              cols.memory_access.access_timestamp.compare_low
                  * (cols.state.clk_high - cols.memory_access.access_timestamp.prev_high) = 0 ∧
              cols.memory_access.access_timestamp.compare_low
                        * (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536 + 1) +
                      (1 - cols.memory_access.access_timestamp.compare_low) * cols.state.clk_high -
                    (cols.memory_access.access_timestamp.compare_low
                          * cols.memory_access.access_timestamp.prev_low +
                      (1 - cols.memory_access.access_timestamp.compare_low)
                        * cols.memory_access.access_timestamp.prev_high) -
                  1 -
                (cols.memory_access.access_timestamp.diff_low_limb +
                  cols.memory_access.access_timestamp.diff_high_limb * 65536) = 0 ∧
              cols.adapter.op_a_0 = 0) ∧
            cols.memory_access.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
              cols.memory_access.access_timestamp.diff_high_limb.val < 2 ^ 8)) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [Extracted.LoadDoubleColumns.asserts, Extracted.LoadDoubleColumns.interactions]
  rw [forall_append_pair, forall_append_pair, forall_append_pair]
  simp only [h_real]
  rw [address_constraints_faithful, cpustate_constraints_faithful, itypereader_constraints_faithful]
  simp only [List.Forall, Interaction.toProp_send_byte, Interaction.toProp_receive,
    Interaction.toProp_send_memory, ByteOpcode.ofNat_six, ByteOpcode.ofNat_three,
    ByteOpcode.constrain_Range, ByteOpcode.constrain_U8Range, val_16, ZMod.val_zero,
    one_ne_zero, ne_eq, not_false_eq_true, true_implies, one_mul, sub_self, mul_zero,
    Nat.ofNat_pos, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, true_and, and_true,
    show (2 : ℕ) ^ 8 = 256 from by norm_num, show (2 : ℕ) ^ 16 = 65536 from by norm_num]
  tauto

end SP1Clean.Faithful
