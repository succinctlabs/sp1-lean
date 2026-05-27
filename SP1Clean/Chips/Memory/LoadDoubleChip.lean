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
import SP1Chips.Load.LoadDouble.Common
import SP1Chips.Load.LoadDouble.LoadDoubleChip
import SP1Clean.Operations.AddrAddOperation
import SP1Clean.Operations.AddressShape
import SP1Clean.Operations.LoadMemoryAccessGated
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ITypeReader
import SP1Clean.Reader.OperandAccess
import SP1Clean.TrustMode
import SP1Clean.Chips.Structs
import SP1Clean.Chips.Spec

/-! # Chip-level `LoadDoubleChip` mirror — 64-bit load

Sibling of `LoadByteChip` for 64-bit doubleword loads (`ld`). 39
columns. No byte-selector machinery — LD loads the entire 4-limb word
at the computed address into op_a.

Opcode: `35 = LD` (Load Double).
-/

set_option linter.style.setOption false
set_option linter.style.longLine false

open LeanRV64D.Functions Sail SailState

namespace SP1Clean.LoadDouble

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def main (cols : Var LoadDoubleCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, _op_a_memory, op_a_0, op_b, _op_b_memory, op_c_imm⟩, _addr_value, _addr_top_two_limb_inv,
       _load_prev_value, _load_memory_prev_high, _load_memory_prev_low,
       _load_memory_flag, load_memory_diff_low, load_memory_diff_high,
       is_real, _adapter_cols⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), load_memory_diff_low, 16, 0]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(3 : Expression (ZMod p)), 0, load_memory_diff_high, 0]
      : Vector (Expression (ZMod p)) 4)
  SP1Clean.ProgramTable.assertion
    (⟨pc, 35, op_a, #v[op_b, 0, 0, 0], op_c_imm, op_a_0, 0, 1⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  is_real * (is_real - 1) === 0

def TraceSpec (cols : LoadDoubleCols (ZMod p)) : Prop :=
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
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
  SP1Clean.memoryAccessSpec
    (cols.load_memory_prev_high * (2 ^ 24) + cols.load_memory_prev_low) 1
    { addr := cols.addr_value,
      prev_value := cols.load_prev_value,
      prev_low := cols.load_memory_prev_low,
      diff_low_limb := cols.load_memory_diff_low } ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := 35,
      op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0],
      op_c := cols.adapter.op_c_imm,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 1 } ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.adapter_cols.is_trusted = 1

/-- The load-side memory access (read of the 4-limb doubleword at
addr_value; the chip itself doesn't modify RAM, write_value = prev_value
at aggregation time). -/
def loadMemoryAccess (cols : LoadDoubleCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := cols.addr_value,
    prev_value := cols.load_prev_value,
    prev_low := cols.load_memory_prev_low,
    diff_low_limb := cols.load_memory_diff_low }

/-- Iff RHS for the Load Double (LD) variant, mirroring
`_root_.Load.LoadDouble.allHold_constraints_iff_of_is_ld`. LD has only
one opcode (no LDU — RV64IM has no unsigned doubleword load), so a
single traceSpec_iff_allHold lemma per chip. The full 4-limb loaded word goes
directly into op_a_write_value (no sub-word selection or sign
extension). -/
def SpecForIff_of_is_ld (cols : LoadDoubleCols (ZMod p)) : Prop :=
  SP1Clean.AddrAddOp.Spec
      cols.adapter.op_b_memory.prev_value cols.adapter.op_c_imm
      { value := cols.addr_value } ∧
  cols.addr_top_two_limb_inv * (cols.addr_value[1] + cols.addr_value[2]) = 1 ∧
  (cols.addr_value[0] * (8 : ZMod p)⁻¹).val < 2 ^ ZMod.val (13 : ZMod p) ∧
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ITypeReader.itypeReaderSpec
      (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 35 cols.state.pc
      cols.load_prev_value
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
  cols.adapter.op_a_0 = 0

set_option maxHeartbeats 800000 in
-- Higher heartbeats: the iff destructure unfolds the full constraint list
-- via the SP1-side `_of_is_ld` helper.
/-- The chip-level bridge for the Load Double variant. -/
theorem iff_sp1_of_is_ld (Main : Vector (ZMod p) 39) (h_is_ld : Main[38] = 1) :
    (_root_.Load.LoadDouble.constraints Main).allHold ↔
      SpecForIff_of_is_ld (fromMain Main) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  change List.Forall SP1Constraint.toProp (_root_.Load.LoadDouble.constraints Main) ↔ _
  rw [_root_.Load.LoadDouble.allHold_constraints_iff_of_is_ld Main h_is_ld]
  simp only [show ∀ (a : SP1ConstraintList (ZMod p)),
      List.Forall SP1Constraint.toProp a = a.allHold from fun _ => rfl,
    SP1Clean.CPUState.cpuStateSpec_iff_sp1,
    SP1Clean.ITypeReader.itypeReaderSpec_iff_sp1,
    SP1Clean.AddrAddOp.iff_sp1]
  simp [SpecForIff_of_is_ld, fromMain]

/-! ## Full `FormalAssertion` promotion (Path-2)

Drops the two bare byte lookups on `load_memory_diff_low` /
`load_memory_diff_high`; covers `CPUState`, `ProgramTable`, and the
`is_real` boolean. Memory-bus consistency is deferred to OfflineMemory. -/

namespace Assertion

open Circuit

@[reducible]
def main (cols : Var LoadDoubleCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c_imm⟩, _addr_value, _addr_top_two_limb_inv,
       _load_prev_value, _load_memory_prev_high, _load_memory_prev_low,
       _load_memory_flag, _load_memory_diff_low, _load_memory_diff_high,
       is_real, _adapter_cols⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ProgramTable.assertion
    (⟨pc, 35, op_a, #v[op_b, 0, 0, 0], op_c_imm, op_a_0, 0, 1⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  is_real * (is_real - 1) === 0
  -- Iter-8 sub-task E (partial): register-side OperandAccess only.
  -- Load RAM access deferred (see `load-store-ram-access-deferred`).
  let clk_low := clk_0_16 + clk_16_24 * 65536
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 4, op_a_memory.access_timestamp.prev_low, op_a_memory.access_timestamp.diff_low_limb,
       op_a_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 3, op_b_memory.access_timestamp.prev_low, op_b_memory.access_timestamp.diff_low_limb,
       op_b_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) LoadDoubleCols unit where
  name := "SP1Clean.LoadDouble"
  main := main
  localLength _ := 0

def Assumptions (_ : LoadDoubleCols (ZMod p)) : Prop := True

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu_sub, h_prog_sub, h_isreal, h_oa_a, h_oa_b⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_prog_sub trivial
  · binary_iff h_isreal
  · exact h_oa_a trivial
  · exact h_oa_b trivial

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu, h_prog, h_isreal, h_oa_a, h_oa_b⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_prog⟩
  · binary_iff h_isreal
  · exact ⟨trivial, h_oa_a⟩
  · exact ⟨trivial, h_oa_b⟩

end Assertion

def assertion : FormalAssertion (ZMod p) LoadDoubleCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

/-! ## `AssertionGated` — full sub-circuit composition with gated multiplicities

LoadDouble loads a full 64-bit value with no sub-word selector. Composes
CPUState, AddrAddOp, AddressShape, ITypeReader, and LoadMemoryAccessGated.
Multiplicity is `is_real` (the single LD opcode flag). -/

namespace AssertionGated

open Circuit

@[reducible]
def main (cols : Var LoadDoubleCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c_imm⟩,
       addr_value, addr_top_two_limb_inv,
       load_prev_value, load_memory_prev_high, load_memory_prev_low,
       load_memory_flag, load_memory_diff_low, load_memory_diff_high,
       is_real, _adapter_cols⟩ := cols
  let clk_low : Expression (ZMod p) := clk_0_16 + clk_16_24 * 65536
  let opcode : Expression (ZMod p) := is_real * 35
  -- For LoadDouble, op_a_write_value = load_prev_value directly (no selector,
  -- no sign-extension). Pass the whole vector; matches the StoreDouble pattern
  -- (avoids #v[..[0],..[1],..[2],..[3]] literal-vs-Vector.map defeq friction).
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.AddrAddOp.assertion
    (⟨op_b_memory.prev_value, op_c_imm, addr_value⟩ :
      Var SP1Clean.AddrAddOp.Inputs (ZMod p))
  SP1Clean.AddressShape.assertion
    (⟨addr_value, addr_top_two_limb_inv, 0, 0, 0⟩ :
      Var SP1Clean.AddressShape.Inputs (ZMod p))
  SP1Clean.ITypeReader.assertion
    (⟨clk_high, clk_low, opcode, pc, load_prev_value,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c_imm⟩⟩ :
      Var SP1Clean.ITypeReader.Inputs (ZMod p))
  SP1Clean.LoadMemoryAccessGated.assertion
    (⟨clk_high, clk_low, addr_value, load_prev_value,
       load_memory_prev_high, load_memory_prev_low,
       load_memory_diff_low, load_memory_diff_high,
       load_memory_flag, is_real⟩ :
      Var SP1Clean.LoadMemoryAccessGated.Inputs (ZMod p))
  is_real * (is_real - 1) === 0
  op_a_0 === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) LoadDoubleCols unit where
  name := "SP1Clean.LoadDouble.Gated"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

/-- Chip-level Assumptions for `AssertionGated`: the load-memory contract
required by the `LoadMemoryAccessGated` sub-circuit. Trace-level callers
discharge this via the existing `iff_sp1_of_is_ld` bridge (which already
proves the disjunctive contract from `(LoadDouble.constraints Main).allHold`).

The sub-circuit's `main := pure ()` means its `Assumptions = Spec = Contract`,
so the chip must hand the contract in directly rather than deriving it
from in-circuit emissions. -/
def Assumptions (cols : LoadDoubleCols (ZMod p)) : Prop :=
  let clk_low : ZMod p := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.LoadMemoryAccessGated.Assertion.Contract
    ⟨cols.state.clk_high, clk_low, cols.addr_value, cols.load_prev_value,
     cols.load_memory_prev_high, cols.load_memory_prev_low,
     cols.load_memory_diff_low, cols.load_memory_diff_high,
     cols.load_memory_flag, cols.is_real⟩

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu_sub, h_addr_sub, h_addr_shape_sub, h_itr_sub,
          h_lmag_sub, h_isreal, h_op_a_0⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_addr_sub trivial
  · exact h_addr_shape_sub trivial
  · exact h_itr_sub trivial
  -- LoadMemoryAccessGated slot: discharge the sub-circuit Assumptions
  -- (= Contract = Spec) from the chip's own Assumptions.
  · exact h_lmag_sub h_assumptions
  · binary_iff h_isreal
  · exact h_op_a_0
  -- Semantic clause: under `is_real = 1`, `cols.load_prev_value` is `Word.isU64`.
  -- Extracted from `LoadMemoryAccessGated.Contract`'s `Word.isU64 prev_value`
  -- clause (the 6th conjunct of the right disjunct). h_is_real_eq has the
  -- `cols.is_real = 1` form (struct projection); we just need it to be nonzero.
  · intro h_is_real_eq
    have h_ir_ne_zero : _ ≠ (0 : ZMod p) := h_is_real_eq.symm ▸ one_ne_zero
    exact (h_assumptions.resolve_left h_ir_ne_zero).2.2.2.2.2

set_option maxHeartbeats 800000 in
-- Mirrors soundness destructure; circuit_proof_start unfolds 5 sub-circuits + 3 gates.
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21⟩ := h_input
  subst_eqs
  -- 8 conjuncts: 5 sub-circuit Specs + is_real binary + op_a_0 + semantic clause.
  obtain ⟨h_cpu, h_addr, h_addr_shape, h_itr, h_lmag, h_isreal, h_op_a_0, _h_sem⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_addr⟩
  · exact ⟨trivial, h_addr_shape⟩
  · exact ⟨trivial, h_itr⟩
  -- LoadMemoryAccessGated slot: sub-circuit Assumptions = Spec = Contract,
  -- so the chip's FormalSpec slot (`h_lmag`) is exactly the Assumptions.
  · exact ⟨h_lmag, h_lmag⟩
  · binary_iff h_isreal
  · exact h_op_a_0

end AssertionGated

def assertionGated : FormalAssertion (ZMod p) LoadDoubleCols :=
  { AssertionGated.elaborated with
    Assumptions := AssertionGated.Assumptions,
    Spec := AssertionGated.FormalSpec,
    soundness := AssertionGated.soundness,
    completeness := AssertionGated.completeness }

/-! ## Cols-level Sail helpers + structural bridge (Phase 2 SailBridge prep)

Mirror of `SP1Clean/Chips/ALU/AddChip/Cols.lean`'s pattern (cols-level
Sail-side helpers) and `Lemmas.lean` (cols round-trip + structural
`allHold_iff_structural`). Used by the upcoming `SailBridge.lean` to lift
SP1's `_root_.Load.LoadDouble.correct_ld` to a cols-parameterized
equivalence. -/

@[reducible] def sp1_op_a_cols (cols : LoadDoubleCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_a.val

@[reducible] def sp1_op_b_cols (cols : LoadDoubleCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_b.val

@[reducible] def sp1_imm_c_cols (cols : LoadDoubleCols (ZMod p)) : BitVec 12 :=
  BitVec.ofNat 12 cols.adapter.op_c_imm[0].val

/-- The chip's monadic `sp1_ld` projected off `LoadDoubleCols` fields
directly. Mirrors `_root_.Load.LoadDouble.sp1_ld Main` exactly on
`fromMain Main` (closes by `rfl` thanks to `@[reducible]`). -/
@[reducible] def sp1_ld_cols (cols : LoadDoubleCols (ZMod p)) :
    SailM ExecutionResult := do
  let op_a := sp1_op_a_cols cols
  Sail.writeReg Register.nextPC
    (Word.toBitVec64
      #v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], (0 : ZMod p)] + 4)
  Sail.write_reg op_a (Word.toBitVec64 cols.load_prev_value)
  return RETIRE_SUCCESS

/-- The cols-level initial-state precondition for the per-row Sail clause:
universally lifted over any flat `Main` row that re-projects to the given
`cols`. (Same shape as `SP1Clean.Add.addInitialState_cols`.) -/
def loadDoubleInitialState_cols (cols : LoadDoubleCols (ZMod p))
    (s : SailState) : Prop :=
  ∀ Main : Vector (ZMod p) 39, fromMain Main = cols →
    (_root_.Load.LoadDouble.constraints Main).initialState s

/-! ### Round-trip lemmas (`<helper>_cols (fromMain Main) = _root_.Load.LoadDouble.<helper> Main`). -/

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_a_cols_fromMain (Main : Vector (ZMod p) 39) :
    sp1_op_a_cols (fromMain Main) = _root_.Load.LoadDouble.sp1_op_a Main := rfl

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_b_cols_fromMain (Main : Vector (ZMod p) 39) :
    sp1_op_b_cols (fromMain Main) = _root_.Load.LoadDouble.sp1_ob_b Main := rfl

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_imm_c_cols_fromMain (Main : Vector (ZMod p) 39) :
    sp1_imm_c_cols (fromMain Main) = _root_.Load.LoadDouble.sp1_imm_c Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_ld_cols_fromMain (Main : Vector (ZMod p) 39) :
    sp1_ld_cols (fromMain Main) = _root_.Load.LoadDouble.sp1_ld Main := rfl

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
/-- `fromMain` is a left inverse of `toMain` (cols → Main → cols round-trip),
conditional on `cols.adapter_cols.is_trusted = cols.is_real` (the UserMode
TrustMode marker — `fromMain` aliases `is_trusted := Main[38] = is_real`). -/
lemma fromMain_toMain (cols : LoadDoubleCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted = cols.is_real) :
    fromMain (toMain cols) = cols := by
  rcases cols with ⟨state, adapter, addr_value, addr_top_two_limb_inv,
                    load_prev_value, lmph, lmpl, lmf, lmdl, lmdh,
                    is_real, adapter_cols⟩
  have : adapter_cols.is_trusted = is_real := by simpa using h_trusted
  simp [this, LoadDoubleCols.ext_iff, CPUState.ext_iff, ITypeReader.ext_iff,
    MemoryAccessInSharedCols.ext_iff, UserModeReaderCols.ext_iff]
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  all_goals simp [Array.ext_iff]; intro i hi; interval_cases i <;> simp

/-- Chip-level structural bridge: `(LoadDouble.constraints Main).allHold`
under `is_real = Main[38] = 1` is exactly `SpecForIff_of_is_ld (fromMain Main)`.
This is just `iff_sp1_of_is_ld` re-exported as a structural lemma for use
inside `SailBridge.sail_correct_of_formalSpec`. -/
lemma allHold_iff_structural
    (Main : Vector (ZMod p) 39) (h_is_real : Main[38] = 1) :
    (_root_.Load.LoadDouble.constraints Main).allHold ↔
      SpecForIff_of_is_ld (fromMain Main) :=
  iff_sp1_of_is_ld Main h_is_real

end SP1Clean.LoadDouble
