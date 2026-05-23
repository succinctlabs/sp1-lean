import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations.Constraint
import SP1Foundations.ByteOpcode
import SP1Foundations.Field
import SP1Operations.Reader.ITypeReader.ITypeReader
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Operation.AddrAddOperation.AddrAddOperation
import SP1Chips.Load.LoadByte.Common
import SP1Clean.AddrAddOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ITypeReader
import SP1Clean.Reader.OperandAccess

/-! # Chip-level `LoadByteChip` mirror — first chip with a real memory load

The Load Byte chip is the canonical example of a chip whose memory bus is
not exhausted by register reads: in addition to the three register
accesses every reader emits (`op_a`, `op_b`, `op_c`), `LoadByteChip` also
emits a memory access at the computed load address `op_b + sign_ext(imm_c)`.
That additional access has `addr0.val ≥ 32` in general, so it hits the
RAM branch of `SP1Constraint.toStateProp` rather than the
register-special-case branch — exercising both code paths the `MemoryAccess`
record needs to support.

This file is the **focused pilot mirror**: it captures the program-bus
interaction and the load-side `MemoryAccess` record explicitly, in a form
suitable for the trace-level `OfflineMemory` aggregation. The chip's full
`iff_sp1` to `_root_.Load.LoadByte.constraints` is deferred to follow-up
work; the goal here is to demonstrate that the `MemoryAccess` + `ProgramTable`
design generalizes from register-only chips (AddChip) to memory-touching
chips, and to seed the OfflineMemory consistency theorem with a real
non-register access.

Opcode: `29 = LB` (Load Byte, signed). Sibling chips `LoadByteUnsigned`,
`LoadHalf*`, `LoadWord*`, `LoadDouble` follow the same shape with width
and signedness selectors.
-/

namespace SP1Clean.LoadByte

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct, mirroring SP1's Rust `LoadByteCols<T>` over
47 field elements. Field order matches the `Main[k]` indexing in
`SP1Chips/Load/LoadByte/Constraints.lean`. -/
structure LoadByteCols (T : Type) where
  state : CPUState T
  adapter : ITypeReader T
  addr_value : Vector T 3                   -- Main[25..27] (op_b + imm_c, low 3 limbs)
  addr_top_two_limb_inv : T                 -- Main[28]
  load_prev_value : Vector T 4              -- Main[29..32] (the 4-limb loaded word)
  load_memory_prev_high : T                 -- Main[33]
  load_memory_prev_low : T                  -- Main[34]
  load_memory_flag : T                      -- Main[35]
  load_memory_diff_low : T                  -- Main[36]
  load_memory_diff_high : T                 -- Main[37]
  offset_bit_2 : T                     -- Main[38] (selects which of 8 bytes)
  offset_bit_1 : T                     -- Main[39]
  offset_bit_0 : T                      -- Main[40]
  selected_limb : T                         -- Main[41]
  selected_limb_low_byte : T                     -- Main[42]
  selected_byte : T                           -- Main[43] (the loaded byte value)
  signed_extension_flag : T                 -- Main[44] (1 if sign bit set, 0 otherwise)
  is_lb : T                                 -- Main[45]
  is_lbu : T                                -- Main[46]
  next_pc_carry_value : Vector T 3
deriving ProvableStruct

/-- Clean-side circuit. Mirrors the SP1 source's emissions for the LB
(signed Load Byte) case: byte lookups for the various range/U8 checks
plus the program-bus interaction. The full memory-access machinery is
exposed via the `Spec` predicate (one `memoryAccessSpec` per access) and
threaded through the trace-level OfflineMemory bridge — Clean has no
native send/receive bus, so per-row consistency is propositional rather
than circuit-level.

Opcode is `is_lb * 29 + is_lbu * 32` to admit both LB (signed) and LBU
(unsigned) variants in the same chip; the immediate-mode flag is
`imm_c = 1` (I-type), and `op_c` carries 4 immediate limbs from
`op_c_imm`. -/
def main (cols : Var LoadByteCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, _op_a_memory, op_a_0, op_b, _op_b_memory, op_c_imm⟩, _addr_value, _addr_top_two_limb_inv,
       _load_prev_value, _load_memory_prev_high, _load_memory_prev_low,
       _load_memory_flag, load_memory_diff_low, load_memory_diff_high,
       _offset_bit_2, _offset_bit_1, _offset_bit_0,
       _selected_limb, selected_limb_low_byte, selected_byte, signed_extension_flag,
       is_lb, is_lbu, _next_pc_carry_value⟩ := cols
  -- CPUState: clk_0_16 progression and clk_16_24 byte bound.
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), (clk_0_16 - 1) * (8 : ZMod p)⁻¹, 13, 0]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), clk_16_24, 8, 0]
      : Vector (Expression (ZMod p)) 4)
  -- Load-memory timestamp bounds (one Range(16) on the low diff, one
  -- U8Range on the high diff, mirroring the SP1 `.send (.byte 6 ... 16)`
  -- and `.send (.byte 3 0 ... 0)` calls).
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), load_memory_diff_low, 16, 0]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(3 : Expression (ZMod p)), 0, load_memory_diff_high, 0]
      : Vector (Expression (ZMod p)) 4)
  -- Selected byte U8 range (for the byte being loaded).
  lookup ByteOpcodeTable
    (#v[(3 : Expression (ZMod p)), 0, selected_limb_low_byte, 0]
      : Vector (Expression (ZMod p)) 4)
  -- MSB lookup (for sign-extension flag determination on LB).
  lookup ByteOpcodeTable
    (#v[(5 : Expression (ZMod p)), signed_extension_flag, selected_byte, 0]
      : Vector (Expression (ZMod p)) 4)
  -- Program-bus interaction. Opcode is is_lb * 29 + is_lbu * 32; I-type
  -- discipline: op_b is single-limb register index, op_c_imm carries
  -- 4 immediate limbs, imm_c = 1.
  SP1Clean.ProgramTable.assertion
    (⟨pc, is_lb * 29 + is_lbu * 32,
      op_a, #v[op_b, 0, 0, 0], op_c_imm, op_a_0, 0, 1⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  -- Boolean and selector gates.
  is_lb * (is_lb - 1) === 0
  is_lbu * (is_lbu - 1) === 0
  (is_lb + is_lbu) * (is_lb + is_lbu - 1) === 0
  op_a_0 === 0

/-- The Clean-flavored Spec for `LoadByteChip` under `is_lb + is_lbu = 1`.
Composes the existing per-fragment specs (`cpuStateSpec`, `itypeReaderSpec`)
with the four `memoryAccessSpec` records that drive the trace-level
OfflineMemory bridge:
- three register reads (op_a, op_b — op_c is immediate so no memory access)
- the load-side access at `addr_value` (which can be RAM, not a register)

The address-arithmetic side (the `AddressOperation` fragment that asserts
`addr_value = op_b + sign_ext(imm_c)`) is folded into a future iteration —
keeping `Spec` light here lets the OfflineMemory bridge consume the chip
without depending on those proofs. -/
def Spec (cols : LoadByteCols (ZMod p)) : Prop :=
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  -- Three register-bus accesses + their bookkeeping (op_a write, op_b read,
  -- op_c is immediate so no memory access).
  SP1Clean.memoryAccessSpec
    (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 4
    (SP1Clean.MemoryAccess.ofRegisterShared cols.adapter.op_a
      { prev_value := cols.adapter.op_a_memory.prev_value,
        access_timestamp :=
          { prev_low := cols.adapter.op_a_memory.access_timestamp.prev_low,
            diff_low_limb := cols.adapter.op_a_memory.access_timestamp.diff_low_limb } }) ∧
  SP1Clean.memoryAccessSpec
    (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 3
    (SP1Clean.MemoryAccess.ofRegisterShared cols.adapter.op_b
      { prev_value := cols.adapter.op_b_memory.prev_value,
        access_timestamp :=
          { prev_low := cols.adapter.op_b_memory.access_timestamp.prev_low,
            diff_low_limb := cols.adapter.op_b_memory.access_timestamp.diff_low_limb } }) ∧
  -- The load-side memory access. Address is the 3-limb `addr_value`
  -- computed by the AddressOperation; this is generally NOT a register
  -- address (`addr_value[0].val ≥ 32`), so the RAM branch of
  -- `SP1Constraint.toStateProp` fires.
  SP1Clean.memoryAccessSpec
    (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 1
    { addr := cols.addr_value,
      prev_value := cols.load_prev_value,
      prev_low := cols.load_memory_prev_low,
      diff_low_limb := cols.load_memory_diff_low } ∧
  -- Program-bus consequence (opcode = 29 = LB when is_lb = 1, 32 = LBU
  -- when is_lbu = 1).
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc,
      opcode := cols.is_lb * 29 + cols.is_lbu * 32,
      op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0],
      op_c := cols.adapter.op_c_imm,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 1 } ∧
  -- Boolean and selector gates.
  cols.is_lb * (cols.is_lb - 1) = 0 ∧
  cols.is_lbu * (cols.is_lbu - 1) = 0 ∧
  (cols.is_lb + cols.is_lbu) * (cols.is_lb + cols.is_lbu - 1) = 0 ∧
  cols.adapter.op_a_0 = 0

/-- The load access as a `MemoryAccess` record, exposed for trace-level
OfflineMemory aggregation. This is the access that hits the RAM branch
(not registers): `addr_value` is the load destination computed by the
AddressOperation sub-fragment.

The companion register-read access for `op_b` (which carries the base
address) is accessible via `MemoryAccess.ofRegisterShared` on the
`op_b_memory_*` column group; together with `addr_value`, OfflineMemory
sees both the register read and the subsequent memory read on the same
chip row. -/
def loadMemoryAccess (cols : LoadByteCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := cols.addr_value,
    prev_value := cols.load_prev_value,
    prev_low := cols.load_memory_prev_low,
    diff_low_limb := cols.load_memory_diff_low }

/-- Project a raw SP1 row into the structured `LoadByteCols` view. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 47) : LoadByteCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
      ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    #v[Main[21], Main[22], Main[23], Main[24]]⟩,
   #v[Main[25], Main[26], Main[27]],
   Main[28],
   #v[Main[29], Main[30], Main[31], Main[32]],
   Main[33], Main[34], Main[35], Main[36], Main[37],
   Main[38], Main[39], Main[40], Main[41], Main[42], Main[43], Main[44],
   Main[45], Main[46], #v[0, 0, 0]⟩

/-! ## `SpecForIff` — iff-equivalent to the SP1 constraint list

These two predicates mirror the RHS of
`_root_.Load.LoadByte.allHold_constraints_iff_of_is_l<op>` verbatim,
modulo replacing the raw `(CPUState.constraints …).allHold` /
`(ITypeReader.constraints …).allHold` clauses with the Clean-flavored
`cpuStateSpec` / `itypeReaderSpec` predicates. They serve the iff_sp1
bridge; the lighter-weight `Spec` above remains for the OfflineMemory
trace bridge (which consumes `loadMemoryAccess` directly, not `Spec`).

The `AddrAddOperation.constraints` clause stays in raw `.allHold` form
because no Clean-side mirror of that operation exists yet (Phase-B per
`docs/CLEAN_PILOT_ROADMAP.md` §3). -/

/-- Iff RHS for the signed Load Byte (LB) variant, mirroring
`_root_.Load.LoadByte.allHold_constraints_iff_of_is_lb`. -/
def SpecForIff_of_is_lb (cols : LoadByteCols (ZMod p)) : Prop :=
  SP1Clean.AddrAddOp.Spec
      cols.adapter.op_b_memory.prev_value cols.adapter.op_c_imm
      { value := cols.addr_value } ∧
  (cols.offset_bit_2 = 0 ∨ cols.offset_bit_2 = 1) ∧
  (cols.offset_bit_1 = 0 ∨ cols.offset_bit_1 = 1) ∧
  (cols.offset_bit_0 = 0 ∨ cols.offset_bit_0 = 1) ∧
  cols.addr_top_two_limb_inv * (cols.addr_value[1] + cols.addr_value[2]) = 1 ∧
  ((cols.addr_value[0] - 4 * cols.offset_bit_0 - 2 * cols.offset_bit_1
        - cols.offset_bit_2) * (8 : ZMod p)⁻¹).val
    < 2 ^ ZMod.val (13 : ZMod p) ∧
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ITypeReader.itypeReaderSpec
      (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 29 cols.state.pc
      #v[cols.selected_byte + 65280 * cols.signed_extension_flag,
         65535 * cols.signed_extension_flag,
         65535 * cols.signed_extension_flag,
         65535 * cols.signed_extension_flag]
      { op_a := cols.adapter.op_a,
        op_a_memory :=
          { prev_value := cols.adapter.op_a_memory.prev_value,
            access_timestamp :=
              { prev_low := cols.adapter.op_a_memory.access_timestamp.prev_low,
                diff_low_limb := cols.adapter.op_a_memory.access_timestamp.diff_low_limb } },
        op_a_0 := cols.adapter.op_a_0, op_b := cols.adapter.op_b,
        op_b_memory :=
          { prev_value := cols.adapter.op_b_memory.prev_value,
            access_timestamp :=
              { prev_low := cols.adapter.op_b_memory.access_timestamp.prev_low,
                diff_low_limb := cols.adapter.op_b_memory.access_timestamp.diff_low_limb } },
        op_c_imm := cols.adapter.op_c_imm } ∧
  (cols.load_memory_flag = 0 ∨ cols.load_memory_flag = 1) ∧
  (cols.load_memory_flag = 0 ∨ cols.state.clk_high = cols.load_memory_prev_high) ∧
  cols.load_memory_flag * (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536 + 1) +
      (1 - cols.load_memory_flag) * cols.state.clk_high -
      (cols.load_memory_flag * cols.load_memory_prev_low +
        (1 - cols.load_memory_flag) * cols.load_memory_prev_high) - 1 =
    cols.load_memory_diff_low + cols.load_memory_diff_high * 65536 ∧
  cols.load_memory_diff_low.val < 65536 ∧
  ((0 : ZMod p) < 256 ∧ cols.load_memory_diff_high < (256 : ZMod p) ∧
    (0 : ZMod p) < 256) ∧
  Word.isU64 cols.load_prev_value ∧
  cols.is_lbu = 0 ∧ cols.adapter.op_a_0 = 0 ∧
  (cols.offset_bit_1 = 1 ∨ cols.offset_bit_0 = 1 ∨
    cols.selected_limb = cols.load_prev_value[0]) ∧
  (cols.offset_bit_1 = 0 ∨ cols.offset_bit_0 = 1 ∨
    cols.selected_limb = cols.load_prev_value[1]) ∧
  (cols.offset_bit_1 = 1 ∨ cols.offset_bit_0 = 0 ∨
    cols.selected_limb = cols.load_prev_value[2]) ∧
  (cols.offset_bit_1 = 0 ∨ cols.offset_bit_0 = 0 ∨
    cols.selected_limb = cols.load_prev_value[3]) ∧
  ((0 : ZMod p) < 256 ∧ cols.selected_limb_low_byte < (256 : ZMod p) ∧
    (cols.selected_limb - cols.selected_limb_low_byte) * (256 : ZMod p)⁻¹
      < (256 : ZMod p)) ∧
  cols.selected_byte = cols.offset_bit_2 *
      ((cols.selected_limb - cols.selected_limb_low_byte) * (256 : ZMod p)⁻¹) +
    (1 - cols.offset_bit_2) * cols.selected_limb_low_byte ∧
  (cols.signed_extension_flag < (256 : ZMod p) ∧
    cols.selected_byte < (256 : ZMod p)) ∧
  (cols.signed_extension_flag = 0 ∨ cols.signed_extension_flag = 1) ∧
  (cols.signed_extension_flag = 1 ↔ (128 : ZMod p) ≤ cols.selected_byte)

/-- Iff RHS for the unsigned Load Byte (LBU) variant, mirroring
`_root_.Load.LoadByte.allHold_constraints_iff_of_is_lbu`. Differs from
the signed variant in the ITypeReader opcode (32 vs 29), the forced-zero
selector (`is_lb = 0` vs `is_lbu = 0`), and the sign-extension trailer
(`signed_extension_flag = 0` instead of the MSB lookup). -/
def SpecForIff_of_is_lbu (cols : LoadByteCols (ZMod p)) : Prop :=
  SP1Clean.AddrAddOp.Spec
      cols.adapter.op_b_memory.prev_value cols.adapter.op_c_imm
      { value := cols.addr_value } ∧
  (cols.offset_bit_2 = 0 ∨ cols.offset_bit_2 = 1) ∧
  (cols.offset_bit_1 = 0 ∨ cols.offset_bit_1 = 1) ∧
  (cols.offset_bit_0 = 0 ∨ cols.offset_bit_0 = 1) ∧
  cols.addr_top_two_limb_inv * (cols.addr_value[1] + cols.addr_value[2]) = 1 ∧
  ((cols.addr_value[0] - 4 * cols.offset_bit_0 - 2 * cols.offset_bit_1
        - cols.offset_bit_2) * (8 : ZMod p)⁻¹).val
    < 2 ^ ZMod.val (13 : ZMod p) ∧
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ITypeReader.itypeReaderSpec
      (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 32 cols.state.pc
      #v[cols.selected_byte + 65280 * cols.signed_extension_flag,
         65535 * cols.signed_extension_flag,
         65535 * cols.signed_extension_flag,
         65535 * cols.signed_extension_flag]
      { op_a := cols.adapter.op_a,
        op_a_memory :=
          { prev_value := cols.adapter.op_a_memory.prev_value,
            access_timestamp :=
              { prev_low := cols.adapter.op_a_memory.access_timestamp.prev_low,
                diff_low_limb := cols.adapter.op_a_memory.access_timestamp.diff_low_limb } },
        op_a_0 := cols.adapter.op_a_0, op_b := cols.adapter.op_b,
        op_b_memory :=
          { prev_value := cols.adapter.op_b_memory.prev_value,
            access_timestamp :=
              { prev_low := cols.adapter.op_b_memory.access_timestamp.prev_low,
                diff_low_limb := cols.adapter.op_b_memory.access_timestamp.diff_low_limb } },
        op_c_imm := cols.adapter.op_c_imm } ∧
  (cols.load_memory_flag = 0 ∨ cols.load_memory_flag = 1) ∧
  (cols.load_memory_flag = 0 ∨ cols.state.clk_high = cols.load_memory_prev_high) ∧
  cols.load_memory_flag * (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536 + 1) +
      (1 - cols.load_memory_flag) * cols.state.clk_high -
      (cols.load_memory_flag * cols.load_memory_prev_low +
        (1 - cols.load_memory_flag) * cols.load_memory_prev_high) - 1 =
    cols.load_memory_diff_low + cols.load_memory_diff_high * 65536 ∧
  cols.load_memory_diff_low.val < 65536 ∧
  ((0 : ZMod p) < 256 ∧ cols.load_memory_diff_high < (256 : ZMod p) ∧
    (0 : ZMod p) < 256) ∧
  Word.isU64 cols.load_prev_value ∧
  cols.is_lb = 0 ∧ cols.adapter.op_a_0 = 0 ∧
  (cols.offset_bit_1 = 1 ∨ cols.offset_bit_0 = 1 ∨
    cols.selected_limb = cols.load_prev_value[0]) ∧
  (cols.offset_bit_1 = 0 ∨ cols.offset_bit_0 = 1 ∨
    cols.selected_limb = cols.load_prev_value[1]) ∧
  (cols.offset_bit_1 = 1 ∨ cols.offset_bit_0 = 0 ∨
    cols.selected_limb = cols.load_prev_value[2]) ∧
  (cols.offset_bit_1 = 0 ∨ cols.offset_bit_0 = 0 ∨
    cols.selected_limb = cols.load_prev_value[3]) ∧
  ((0 : ZMod p) < 256 ∧ cols.selected_limb_low_byte < (256 : ZMod p) ∧
    (cols.selected_limb - cols.selected_limb_low_byte) * (256 : ZMod p)⁻¹
      < (256 : ZMod p)) ∧
  cols.selected_byte = cols.offset_bit_2 *
      ((cols.selected_limb - cols.selected_limb_low_byte) * (256 : ZMod p)⁻¹) +
    (1 - cols.offset_bit_2) * cols.selected_limb_low_byte ∧
  cols.signed_extension_flag = 0

set_option maxHeartbeats 800000 in
-- Higher heartbeats: the iff destructure unfolds the full constraint list
-- via the SP1-side `_of_is_lb` helper.
/-- The chip-level bridge for the signed Load Byte variant. -/
theorem iff_sp1_of_is_lb (Main : Vector (ZMod p) 47) (h_is_lb : Main[45] = 1) :
    (_root_.Load.LoadByte.constraints Main).allHold ↔
      SpecForIff_of_is_lb (fromMain Main) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  change List.Forall SP1Constraint.toProp (_root_.Load.LoadByte.constraints Main) ↔ _
  rw [_root_.Load.LoadByte.allHold_constraints_iff_of_is_lb Main h_is_lb]
  simp only [show ∀ (a : SP1ConstraintList (ZMod p)),
      List.Forall SP1Constraint.toProp a = a.allHold from fun _ => rfl,
    SP1Clean.CPUState.cpuStateSpec_iff_sp1,
    SP1Clean.ITypeReader.itypeReaderSpec_iff_sp1,
    SP1Clean.AddrAddOp.iff_sp1]
  simp [SpecForIff_of_is_lb, fromMain]

set_option maxHeartbeats 800000 in
-- Higher heartbeats: same reason as `iff_sp1_of_is_lb`.
/-- The chip-level bridge for the unsigned Load Byte variant. -/
theorem iff_sp1_of_is_lbu (Main : Vector (ZMod p) 47) (h_is_lbu : Main[46] = 1) :
    (_root_.Load.LoadByte.constraints Main).allHold ↔
      SpecForIff_of_is_lbu (fromMain Main) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  change List.Forall SP1Constraint.toProp (_root_.Load.LoadByte.constraints Main) ↔ _
  rw [_root_.Load.LoadByte.allHold_constraints_iff_of_is_lbu Main h_is_lbu]
  simp only [show ∀ (a : SP1ConstraintList (ZMod p)),
      List.Forall SP1Constraint.toProp a = a.allHold from fun _ => rfl,
    SP1Clean.CPUState.cpuStateSpec_iff_sp1,
    SP1Clean.ITypeReader.itypeReaderSpec_iff_sp1,
    SP1Clean.AddrAddOp.iff_sp1]
  simp [SpecForIff_of_is_lbu, fromMain]

/-! ## Full `FormalAssertion` promotion (Path-2)

Drops the bare byte lookups (CPUState inline bytes, load-memory diff
bytes, selected_limb_low_byte range, MSB lookup); covers `CPUState`,
`ProgramTable`, the three boolean gates (`is_lb`, `is_lbu`, sum), and
the `op_a_0 = 0` gate. Memory-bus consistency is deferred to
OfflineMemory. -/

namespace Assertion

open Circuit

@[reducible]
def main (cols : Var LoadByteCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c_imm⟩, _addr_value, _addr_top_two_limb_inv,
       _load_prev_value, _load_memory_prev_high, _load_memory_prev_low,
       _load_memory_flag, _load_memory_diff_low, _load_memory_diff_high,
       _offset_bit_2, _offset_bit_1, _offset_bit_0,
       _selected_limb, _selected_limb_low_byte, _selected_byte, _signed_extension_flag,
       is_lb, is_lbu, next_pc_carry_value⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ProgramTable.assertion
    (⟨pc, is_lb * 29 + is_lbu * 32,
      op_a, #v[op_b, 0, 0, 0], op_c_imm, op_a_0, 0, 1⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  SP1Clean.AddrAddOp.assertion
    (⟨#v[pc[0], pc[1], pc[2], (0 : Expression (ZMod p))],
       #v[(4 : Expression (ZMod p)), 0, 0, 0],
       next_pc_carry_value⟩ :
      Var SP1Clean.AddrAddOp.Inputs (ZMod p))
  is_lb * (is_lb - 1) === 0
  is_lbu * (is_lbu - 1) === 0
  (is_lb + is_lbu) * (is_lb + is_lbu - 1) === 0
  op_a_0 === 0
  -- Iter-8 sub-task E (partial for Load chips). Emit OperandAccess only
  -- for the 2 register accesses (op_a/+4, op_b/+3). The RAM access at
  -- +1 uses a (diff_low, diff_high) flag-gated timestamp encoding that
  -- doesn't match OperandAccess.Spec's scaled-timestamp form; deferred
  -- to a follow-up that introduces a flag-aware `LoadOperandAccess`
  -- variant (see memory `load-store-ram-access-deferred`).
  let clk_low := clk_0_16 + clk_16_24 * 65536
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 4, op_a_memory.access_timestamp.prev_low, op_a_memory.access_timestamp.diff_low_limb,
       op_a_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 3, op_b_memory.access_timestamp.prev_low, op_b_memory.access_timestamp.diff_low_limb,
       op_b_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))

set_option maxHeartbeats 800000 in
-- Higher heartbeats: 32 input fields + 4 subcircuit calls + 2 OperandAccess
-- calls pushes localLength_eq synthesis past the default 200k cap.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) LoadByteCols unit where
  name := "SP1Clean.LoadByte"
  main := main
  localLength _ := 0

def Assumptions (_ : LoadByteCols (ZMod p)) : Prop := True

def FormalSpec (cols : LoadByteCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := cols.is_lb * 29 + cols.is_lbu * 32,
      op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0], op_c := cols.adapter.op_c_imm,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 1 } ∧
  SP1Clean.AddrAddOp.assertion.Spec
    ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
     #v[(4 : ZMod p), 0, 0, 0],
     cols.next_pc_carry_value⟩ ∧
  cols.is_lb * (cols.is_lb - 1) = 0 ∧
  cols.is_lbu * (cols.is_lbu - 1) = 0 ∧
  (cols.is_lb + cols.is_lbu) * (cols.is_lb + cols.is_lbu - 1) = 0 ∧
  cols.adapter.op_a_0 = 0 ∧
  -- Iter-8 sub-task E (partial). Register-side memory-bus byte content:
  -- op_a/+4, op_b/+3. The load_mem/+1 access is deferred.
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 4, cols.adapter.op_a_memory.access_timestamp.prev_low, cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 3, cols.adapter.op_b_memory.access_timestamp.prev_low, cols.adapter.op_b_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_b_memory.prev_value⟩

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30,
          e31, e32⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu_sub, h_prog_sub, h_addr_sub, h_lb, h_lbu, h_sum,
          h_op_a_0, h_oa_a, h_oa_b⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_prog_sub trivial
  · simp only [Vector.getElem_map]
    exact h_addr_sub trivial
  · linear_combination h_lb
  · linear_combination h_lbu
  · linear_combination h_sum
  · exact h_op_a_0
  · exact h_oa_a trivial
  · exact h_oa_b trivial

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30,
          e31, e32⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu, h_prog, h_addr, h_lb, h_lbu, h_sum, h_op_a_0,
          h_oa_a, h_oa_b⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_prog⟩
  · refine ⟨trivial, ?_⟩
    simp only [Vector.getElem_map] at h_addr
    exact h_addr
  · linear_combination h_lb
  · linear_combination h_lbu
  · linear_combination h_sum
  · exact h_op_a_0
  · exact ⟨trivial, h_oa_a⟩
  · exact ⟨trivial, h_oa_b⟩

end Assertion

def assertion : FormalAssertion (ZMod p) LoadByteCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.LoadByte
