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
import SP1Operations.Operation.AddOperation.AddOperation
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.RTypeReader.RTypeReader
import SP1Chips.Add.AddChip
import SP1Chips.Soundness
import SP1Clean.AddOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.Reader.OperandAccess
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.RTypeReader
import SP1Clean.TrustMode

/-! # Chip-level `AddChip` mirror — R-type sibling of `AddiChip`

The R-type Add chip: 33 columns, composes `SP1Clean.AddOp` with
`CPUState` and `RTypeReader` Spec helpers. Differs from `AddiChip` by
having `op_c` as a register (with full memory-access substruct) rather
than the four immediate-byte limbs `op_c_imm`, and by carrying opcode
index `0` (`ADD`) into `RTypeReader`.

The chip's `Spec` is stated over a structured `AddCols (ZMod p)` view of
the flat row — same `ProvableStruct` discipline as `AddiCols` — with the
sub-fragment surfaces packaged as `SP1Clean.AddOp.Spec`,
`SP1Clean.CPUState.cpuStateSpec`, and `SP1Clean.RTypeReader.rtypeReaderSpec`.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Add

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct, mirroring SP1's Rust `AddCols<T, M: TrustMode>`
(`sp1/crates/core/machine/src/alu/add_sub/add.rs:47-62`). The
`adapter_cols : UserModeReaderCols T` slot is the last field, matching Rust
under `M = UserMode`. We don't carry an explicit `M` type parameter on the
struct because `deriving ProvableStruct` can't reduce through an abstract
`M`; future SupervisorMode chips would use a separate `*ColsSupervisor`
struct with `adapter_cols : EmptyCols T`. -/
@[ext]
structure AddCols (T : Type) where
  state : CPUState T
  adapter : RTypeReader T
  op_a_write_value : Vector T 4
  is_real : T
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Project a raw SP1 row into the structured `AddCols` view. Mirrors the
index map in `SP1Chips/Add/Constraints.lean`. `adapter_cols.is_trusted`
aliases `Main[32]` (= `is_real`) because the current extractor passes
`Main[32] Main[32]` to `RTypeReader.constraints` (see
`SP1Chips/Add/Constraints.lean:21`). When upstream regen lands a separate
`is_trusted` Main column, switch to that index. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 33) : AddCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
   ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    Main[21],
    ⟨#v[Main[22], Main[23], Main[24], Main[25]], ⟨Main[26], Main[27]⟩⟩⟩,
   #v[Main[28], Main[29], Main[30], Main[31]],
   Main[32],
   ⟨Main[32]⟩⟩

/-- Right inverse of `fromMain`: pack an `AddCols` into a 33-element flat
row using the same index map as `fromMain`. Used only internally by the
soundness proof of the Sail clause (see `Assertion.soundness`); not part
of the user-facing API. Index 32 (= `is_real`) is also the
`adapter_cols.is_trusted` slot, matching `fromMain`'s aliasing. -/
@[reducible] def toMain (cols : AddCols (ZMod p)) : Vector (ZMod p) 33 :=
  #v[cols.state.clk_high, cols.state.clk_16_24, cols.state.clk_0_16,
     cols.state.pc[0], cols.state.pc[1], cols.state.pc[2],
     cols.adapter.op_a,
     cols.adapter.op_a_memory.prev_value[0],
     cols.adapter.op_a_memory.prev_value[1],
     cols.adapter.op_a_memory.prev_value[2],
     cols.adapter.op_a_memory.prev_value[3],
     cols.adapter.op_a_memory.access_timestamp.prev_low,
     cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_0,
     cols.adapter.op_b,
     cols.adapter.op_b_memory.prev_value[0],
     cols.adapter.op_b_memory.prev_value[1],
     cols.adapter.op_b_memory.prev_value[2],
     cols.adapter.op_b_memory.prev_value[3],
     cols.adapter.op_b_memory.access_timestamp.prev_low,
     cols.adapter.op_b_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_c,
     cols.adapter.op_c_memory.prev_value[0],
     cols.adapter.op_c_memory.prev_value[1],
     cols.adapter.op_c_memory.prev_value[2],
     cols.adapter.op_c_memory.prev_value[3],
     cols.adapter.op_c_memory.access_timestamp.prev_low,
     cols.adapter.op_c_memory.access_timestamp.diff_low_limb,
     cols.op_a_write_value[0], cols.op_a_write_value[1],
     cols.op_a_write_value[2], cols.op_a_write_value[3],
     cols.is_real]

/-! ## Cols-level Sail-side helpers

Mirror the Main-level `_root_.Add.sp1_op_{a,b,c}` and `_root_.Add.sp1_add`
projections directly off `AddCols` fields, so the chip-level `FormalSpec`
Sail clause stays cols-parameterized without requiring callers to construct
a `Main : Vector (ZMod p) 33`. Each helper is `@[reducible]` so the
round-trip lemma `<helper>_cols (fromMain Main) = Add.<helper> Main` closes
by `rfl`. -/

@[reducible] def sp1_op_a_cols (cols : AddCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_a.val

@[reducible] def sp1_op_b_cols (cols : AddCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_b.val

@[reducible] def sp1_op_c_cols (cols : AddCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_c.val

def sp1_add_cols (cols : AddCols (ZMod p)) : SailM Unit := do
  let op_a := sp1_op_a_cols cols
  Sail.writeReg Register.nextPC
    (Word.toBitVec64 #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2], 0])
  Sail.write_reg op_a (Word.toBitVec64 cols.op_a_write_value)

/-- The cols-level state-bus precondition for the per-row Sail clause:
universally lifted over any flat `Main` row that re-projects to the given
`cols`. Stated this way (rather than directly via `toMain cols`) so we
don't depend on a `fromMain (toMain cols) = cols` round-trip, which fails
by `rfl` due to `Vector` not having structural eta. Downstream consumers
that have `cols` in hand can specialize with `Main := toMain cols`. -/
def addInitialState_cols (cols : AddCols (ZMod p)) (s : SailState) : Prop :=
  ∀ Main : Vector (ZMod p) 33, fromMain Main = cols →
    (_root_.Add.constraints Main).initialState s

/-! ### Round-trip lemmas

Each `cols`-level helper equals the corresponding `Main`-level def when
applied to `fromMain Main`. All hold by `rfl` thanks to `@[reducible]`. -/

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_a_cols_fromMain (Main : Vector (ZMod p) 33) :
    sp1_op_a_cols (fromMain Main) = _root_.Add.sp1_op_a Main := rfl

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_b_cols_fromMain (Main : Vector (ZMod p) 33) :
    sp1_op_b_cols (fromMain Main) = _root_.Add.sp1_op_b Main := rfl

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_c_cols_fromMain (Main : Vector (ZMod p) 33) :
    sp1_op_c_cols (fromMain Main) = _root_.Add.sp1_op_c Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_add_cols_fromMain (Main : Vector (ZMod p) 33) :
    sp1_add_cols (fromMain Main) = _root_.Add.sp1_add Main := rfl

-- The nested-struct ext attribute needs to be applied to the sub-types
-- for `ext <;> rfl` to recurse fully through `AddCols` → `CPUState` /
-- `RTypeReader` / `UserModeReaderCols` / `MemoryAccessInSharedCols` / ...
attribute [ext] _root_.CPUState _root_.RTypeReader
                _root_.MemoryAccessInSharedCols
                _root_.MemoryAccessInShardTimestamp
                SP1Clean.UserModeReaderCols

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
/-- `fromMain` is a left inverse of `toMain` (cols → Main → cols round-trip),
conditional on `cols.adapter_cols.is_trusted = cols.is_real`. The precondition
captures `fromMain`'s aliasing of `is_trusted := Main[32] = is_real` (which
matches the constraint compiler's emission — Main[32] is both `is_real` and
`is_trusted`). Recursive `ext` through `@[ext]`-marked sub-structures plus
`Vector.ext` reduces to per-element equations closed by `rfl` (each
`(toMain cols)[k]` reduces by `@[reducible]` to the matching `cols`
projection) or by the precondition on the lone `adapter_cols.is_trusted` leaf. -/
lemma fromMain_toMain (cols : AddCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted = cols.is_real) :
    fromMain (toMain cols) = cols := by
  ext
  all_goals first
    | rfl
    | exact h_trusted.symm
    | (next i _ => interval_cases i <;> rfl)
    | (next i => fin_cases i <;> rfl)

/-- The chip-level structural bridge: SP1's `allHold` over the flat row
`Add.constraints Main` is exactly the conjunction of `AddOp.Spec`,
`cpuStateSpec`, and `rtypeReaderSpec` over `fromMain Main`, under
`is_real = Main[32] = 1`. Used inside the Sail clause's soundness proof to
construct an `allHold` from the structural pieces of `FormalSpec`. -/
lemma allHold_iff_structural
    (Main : Vector (ZMod p) 33) (h_is_real : Main[32] = 1) :
    (_root_.Add.constraints Main).allHold ↔
      (SP1Clean.AddOp.Spec
          #v[Main[15], Main[16], Main[17], Main[18]]
          #v[Main[22], Main[23], Main[24], Main[25]]
          #v[Main[28], Main[29], Main[30], Main[31]] ∧
       SP1Clean.CPUState.cpuStateSpec Main[2] Main[1] ∧
       SP1Clean.RTypeReader.rtypeReaderSpec
          (Main[2] + Main[1] * 65536) 0 #v[Main[3], Main[4], Main[5]]
          #v[Main[28], Main[29], Main[30], Main[31]]
          { op_a := Main[6],
            op_a_memory :=
              { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
                access_timestamp :=
                  { prev_low := Main[11], diff_low_limb := Main[12] } },
            op_a_0 := Main[13], op_b := Main[14],
            op_b_memory :=
              { prev_value := #v[Main[15], Main[16], Main[17], Main[18]],
                access_timestamp :=
                  { prev_low := Main[19], diff_low_limb := Main[20] } },
            op_c := Main[21],
            op_c_memory :=
              { prev_value := #v[Main[22], Main[23], Main[24], Main[25]],
                access_timestamp :=
                  { prev_low := Main[26], diff_low_limb := Main[27] } } } ∧
       Main[32] * (Main[32] - 1) = 0 ∧
       Main[13] = 0) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rw [show (_root_.Add.constraints Main).allHold ↔
        ((AddOperation.constraints (F := ZMod p)
            #v[Main[15], Main[16], Main[17], Main[18]]
            #v[Main[22], Main[23], Main[24], Main[25]]
            { value := #v[Main[28], Main[29], Main[30], Main[31]] }
            Main[32]).allHold ∧
          (CPUState.constraints (F := ZMod p)
            { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2],
              pc := #v[Main[3], Main[4], Main[5]] }
            #v[Main[3] + 4, Main[4], Main[5]] 8 Main[32]).allHold ∧
          (RTypeReader.constraints (F := ZMod p)
            Main[0] (Main[2] + Main[1] * 65536)
            #v[Main[3], Main[4], Main[5]] 0
            #v[Main[28], Main[29], Main[30], Main[31]]
            { op_a := Main[6],
              op_a_memory :=
                { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
                  access_timestamp :=
                    { prev_low := Main[11], diff_low_limb := Main[12] } },
              op_a_0 := Main[13], op_b := Main[14],
              op_b_memory :=
                { prev_value := #v[Main[15], Main[16], Main[17], Main[18]],
                  access_timestamp :=
                    { prev_low := Main[19], diff_low_limb := Main[20] } },
              op_c := Main[21],
              op_c_memory :=
                { prev_value := #v[Main[22], Main[23], Main[24], Main[25]],
                  access_timestamp :=
                    { prev_low := Main[26], diff_low_limb := Main[27] } } }
            Main[32] Main[32]).allHold ∧
          (Main[32] * (Main[32] - 1) = 0 ∧ Main[13] = 0)) from by
      simp [_root_.Add.constraints, SP1ConstraintList.allHold,
        List.forall_append, List.Forall, SP1Constraint.toProp]]
  rw [h_is_real]
  rw [AddOperation.allHold_constraints_iff,
      SP1Clean.CPUState.cpuStateSpec_iff_sp1,
      SP1Clean.RTypeReader.rtypeReaderSpec_iff_sp1]
  simp [SP1Clean.AddOp.Spec, SP1Clean.CPUState.cpuStateSpec,
        SP1Clean.RTypeReader.rtypeReaderSpec, and_assoc]

/-! ## Full `FormalAssertion` promotion

Wraps the chip-level constraint surface into a single Clean `FormalAssertion`
whose `Spec` is the unified semantic-and-structural contract — the
`AddOperation` arithmetic Spec, the CPU-state byte bounds, the full
`rtypeReaderSpec` (program + memory bounds + bounds), the two trailing
scalar gates, and a per-row Sail equivalence between SP1's `sp1_add` and
the Sail spec.

`Assertion.main` composes three subcircuits — `AddOp.assertion`,
`CPUState.assertion`, and the new `RTypeReader.assertion` (which itself
wraps `ProgramTable.assertion` + 3 `OperandAccess.assertion` calls) —
mirroring `SP1Chips/Add/Constraints.lean`'s single `RTypeReader.constraints`
call (and faithfully reflecting the upstream Rust `AddChip::eval`'s
`RTypeReader::eval` call). -/

namespace Assertion

open Circuit

/-- Clean-side chip circuit. Mirrors SP1 Rust's `AddChip::eval(builder, cols)`
1:1: one `AddOp.assertion` + one `CPUState.assertion` + one
`RTypeReader.assertion` + two scalar gates. -/
@[reducible]
def main (cols : Var AddCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       adapter,
       op_a_write_value, is_real, _adapter_cols⟩ := cols
  SP1Clean.AddOp.assertion
    (⟨adapter.op_b_memory.prev_value, adapter.op_c_memory.prev_value,
      op_a_write_value⟩ :
      Var SP1Clean.AddOp.Inputs (ZMod p))
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.RTypeReader.assertion
    (⟨clk_0_16 + clk_16_24 * 65536, 0, pc, op_a_write_value, adapter⟩ :
      Var SP1Clean.RTypeReader.Inputs (ZMod p))
  is_real * (is_real - 1) === 0
  adapter.op_a_0 === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) AddCols unit where
  name := "SP1Clean.Add"
  main := main
  localLength _ := 0

/-- The chip is the `UserMode` variant (`M = UserMode` in upstream Rust),
so its `adapter_cols.is_trusted` payload is structurally equal to `is_real`
(both alias `Main[32]` in the constraint compiler's emission). This is a
type-level / TrustMode-marker fact that the circuit doesn't enforce. -/
def Assumptions (cols : AddCols (ZMod p)) : Prop :=
  cols.adapter_cols.is_trusted = cols.is_real

/-- The unified chip Spec. Subsumes the legacy `TraceSpec`/`ArithSpec`/
`FormalSpec`/`SemanticSpec` split into a single predicate:
- `AddOp.Spec` — `op_b + op_c = op_a_write_value` (carry chain)
- `cpuStateSpec` — clk_0_16/clk_16_24 byte bounds
- `rtypeReaderSpec` — full R-type reader spec (program + memory + bounds)
- `is_real * (is_real - 1) = 0` — is_real binary
- `adapter.op_a_0 = 0` — op_a_0 zero gate
- per-row Sail equivalence (conditional on `is_real = 1`) — bridges SP1's
  `sp1_add_cols` to the Sail spec via `_root_.Add.correct_add`. -/
def FormalSpec (cols : AddCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.AddOp.Spec
      cols.adapter.op_b_memory.prev_value cols.adapter.op_c_memory.prev_value
      cols.op_a_write_value ∧
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.RTypeReader.rtypeReaderSpec clk_low 0 cols.state.pc
      cols.op_a_write_value cols.adapter ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.adapter.op_a_0 = 0 ∧
  (cols.is_real = 1 → ∀ s : SailState, addInitialState_cols cols s →
    (sp1_add_cols cols).run s =
      (_root_.Add.spec_add (.Regidx (sp1_op_c_cols cols))
                           (.Regidx (sp1_op_b_cols cols))
                           (.Regidx (sp1_op_a_cols cols))).run s)

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e_adapter, e_oawv, e_is_real, e_ac⟩ := h_input
  subst_eqs
  obtain ⟨h_addop_sub, h_cpu_sub, h_rtr_sub, h_isreal, h_op_a_0⟩ := h_holds
  unfold id at *
  have h_addop := h_addop_sub trivial
  have h_cpu := h_cpu_sub trivial
  have h_rtr := h_rtr_sub trivial
  -- Rebind the explicit eval'd-form struct under the name `cols` so the
  -- helper-cols functions and `addInitialState_cols` references in the
  -- residual Sail clause unfold against a single named term rather than
  -- a giant inlined struct in every position.
  set cols : AddCols (ZMod p) :=
    { state :=
        { clk_high := Expression.eval env input_var_state_clk_high,
          clk_16_24 := Expression.eval env input_var_state_clk_16_24,
          clk_0_16 := Expression.eval env input_var_state_clk_0_16,
          pc := Vector.map (Expression.eval env) input_var_state_pc },
      adapter :=
        { op_a := input_adapter_op_a,
          op_a_memory :=
            { prev_value := input_adapter_op_a_memory_prev_value,
              access_timestamp :=
                { prev_low := input_adapter_op_a_memory_access_timestamp_prev_low,
                  diff_low_limb := input_adapter_op_a_memory_access_timestamp_diff_low_limb } },
          op_a_0 := input_adapter_op_a_0, op_b := input_adapter_op_b,
          op_b_memory :=
            { prev_value := input_adapter_op_b_memory_prev_value,
              access_timestamp :=
                { prev_low := input_adapter_op_b_memory_access_timestamp_prev_low,
                  diff_low_limb := input_adapter_op_b_memory_access_timestamp_diff_low_limb } },
          op_c := input_adapter_op_c,
          op_c_memory :=
            { prev_value := input_adapter_op_c_memory_prev_value,
              access_timestamp :=
                { prev_low := input_adapter_op_c_memory_access_timestamp_prev_low,
                  diff_low_limb := input_adapter_op_c_memory_access_timestamp_diff_low_limb } } },
      op_a_write_value := Vector.map (Expression.eval env) input_var_op_a_write_value,
      is_real := Expression.eval env input_var_is_real,
      adapter_cols := { is_trusted := Expression.eval env input_var_is_real } }
    with hcols
  refine ⟨h_addop, h_cpu, h_rtr, by linear_combination h_isreal, h_op_a_0, ?_⟩
  -- Sail clause: given `is_real = 1` and `addInitialState_cols cols s`, derive
  -- the Sail equivalence by bridging through `Main := toMain cols` and invoking
  -- `_root_.Add.correct_add`.
  intro h_is_real_eq s h_init
  -- Round-trip: `fromMain (toMain cols) = cols`. Precondition
  -- `is_trusted = is_real` is the chip's `Assumptions` (UserMode TrustMode
  -- marker), available in context after `circuit_proof_start`.
  have h_trusted : cols.adapter_cols.is_trusted = cols.is_real := rfl
  have h_round_trip := fromMain_toMain cols h_trusted
  have h_state := h_init (toMain cols) h_round_trip
  -- `(toMain cols)[32] = cols.is_real` reduces to `h_is_real_eq`.
  have h_isreal' : (toMain cols)[32] = 1 := h_is_real_eq
  -- Reconstruct SP1's `allHold` on `toMain cols` from the structural conjuncts
  -- of `FormalSpec`. Each `convert ... using N` reduces to Vector-eta side goals.
  have h_allHold : (_root_.Add.constraints (toMain cols)).allHold := by
    rw [allHold_iff_structural (toMain cols) h_isreal']
    refine ⟨?_, h_cpu, ?_, ?_, h_op_a_0⟩
    · -- AddOp.Spec: bridge `#v[(toMain cols)[k..k+3]]` ⇔ cols-level Vector.
      -- `convert ... using 1` closes via definitional reduction of `toMain`.
      convert h_addop using 1
    · -- rtypeReaderSpec: bridge via struct projections through `toMain`.
      convert h_rtr using 4
    · -- `(toMain cols)[32] = cols.is_real` reduces by rfl.
      change cols.is_real * (cols.is_real - 1) = 0
      linear_combination h_isreal
  -- Apply Main-level correctness; the result reads `sp1_X (toMain cols)`,
  -- which is definitionally `sp1_X_cols cols` for each helper.
  exact (_root_.Add.correct_add (toMain cols) s h_allHold h_isreal' h_state).symm

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e_adapter, e_oawv, e_is_real, e_ac⟩ := h_input
  subst_eqs
  obtain ⟨h_addop, h_cpu, h_rtr, h_isreal, h_op_a_0, _h_sail⟩ := h_spec
  unfold id at *
  refine ⟨⟨trivial, h_addop⟩, ⟨trivial, h_cpu⟩, ⟨trivial, h_rtr⟩,
          by linear_combination h_isreal, h_op_a_0⟩

end Assertion

/-- The full Clean `FormalAssertion` for `AddChip`. Single subcircuit
composition (`AddOp.assertion + CPUState.assertion + RTypeReader.assertion
+ 2 scalar gates`) backing one unified `Spec` that covers everything from
byte-lookup consequences to per-row Sail equivalence. -/
def assertion : FormalAssertion (ZMod p) AddCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.Add
