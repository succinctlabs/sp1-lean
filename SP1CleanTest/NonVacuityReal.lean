import SP1Clean
import SP1CleanTest.TraceGenTests.EventPopulate

/-! # Real-row satisfiability anchors: every chip constraint system has an `is_real = 1` model

The `Assumptions` anchors (`SP1CleanTest/NonVacuity.lean`) rule out contradictory chip
*preconditions*, but 17 of their 20 witnesses are the all-zero row (`is_real = 0`) — they do not
rule out a chip whose **constraint system** is unsatisfiable on real rows (which would make its
soundness theorem vacuous over the rows that matter). This module closes that gap: for **every
one of the 25 registered instruction chips**, a named theorem exhibits one concrete `is_real = 1`
row with non-degenerate operands and proves that the chip's complete constraint system holds on
it (Lt, Bitwise, and UType each get two rows covering both variants/outcomes), and
`constraint_systems_nonempty` guards that every checked assertion system is nonempty.

## What each theorem states, precisely

For a chip `X` with circuit `X.main`, concrete input columns `inputs` (with `is_real = 1`), and
prover hint `hint`, the theorem is

  `(chipOperations X.Inputs X.main inputs).ConstraintsHold (chipEnvironment X.Inputs X.main inputs hint)`

where

- `chipOperations` is `(X.main (varFromOffset X.Inputs 0)).operations inputs.length` — the chip's
  full operation list, exactly as instantiated by the chip's own `ElaboratedCircuit`;
- `chipEnvironment` is the environment built by Clean's `Circuit.proverEnvironment`: the input
  columns positionally, then **the witness values computed by `main`'s own witness closures**
  (the same `populate` closures SP1's trace generator conformance layer runs) — nothing is
  hand-assigned;
- `Operations.ConstraintsHold env ops` is Clean's verifier-side predicate
  `(∀ e ∈ ops.constraints, env e = 0) ∧ (∀ l ∈ ops.lookups, l.Contains env)`, where
  `ops.constraints` recursively includes **every subcircuit's** `assertZero` constraints
  (equivalent to `ConstraintsHoldFlat env ops.toFlat`, `Circuit.constraintsHold_toFlat_iff`).

So the claim is: every polynomial constraint of the whole flattened chip circuit — gadget
arithmetic, boolean gates, reader glue, chip-owned tail — evaluates to zero on this row, and the
circuit contains no (unchecked) static lookups. **Not covered**: channel interactions (byte-range
pulls, memory/state/program bus messages). Those carry no row-local constraint in Clean or in SP1
(they are checked globally by bus balance), so they are outside any single-row satisfiability
statement; the rows here nevertheless follow the same clk/timestamp discipline as the dumped
Rust traces. Each proof is a decidable whole-circuit evaluation at SP1's concrete KoalaBear prime
discharged by `native_decide` (sanctioned in this test library only), lifted to the `Prop`-level
`ConstraintsHold` statement by the axiom-clean bridge `constraintsHold_of_check`.

`is_real = 1` is visible by construction: the event-built input lists start with the literal `1`
(`rTypeEventInputs` / `aluTypeEventInputs`, see `rTypeEventInputs_is_real` /
`aluTypeEventInputs_is_real` below), and struct-built inputs set `is_real := 1` explicitly.
Operand non-degeneracy is stated per theorem. Where cheap, a companion theorem also pins the
Spec-level result computed by the row (e.g. the Lt compare bit on a true and a false comparison).
-/

namespace SP1Clean.NonVacuityRealTests

open SP1Clean
open SP1Clean.TraceGenTests

/-! ## Generic scaffolding -/

/-- The chip circuit's complete operation list — `main` applied to the positional input variables,
elaborated at offset `inputs.length` (inputs first, local witnesses after), exactly as in the
trace-generation layer (`TraceGenerator.lean`). -/
def chipOperations (Input : TypeMap) [ProvableType Input] {Output : TypeMap} [ProvableType Output]
    (main : Var Input (ZMod SP1Prime) → Circuit (ZMod SP1Prime) (Var Output (ZMod SP1Prime)))
    (inputs : List (ZMod SP1Prime)) : Operations (ZMod SP1Prime) :=
  ((main (varFromOffset Input 0)).operations inputs.length)

/-- The concrete row environment: the input columns positionally (indices `< inputs.length`),
then the witness values produced by `main`'s **own** witness closures in emission order
(`Circuit.proverEnvironment`, threading earlier witnesses into later closures). -/
def chipEnvironment (Input : TypeMap) [ProvableType Input] {Output : TypeMap} [ProvableType Output]
    (main : Var Input (ZMod SP1Prime) → Circuit (ZMod SP1Prime) (Var Output (ZMod SP1Prime)))
    (inputs : List (ZMod SP1Prime))
    (hint : ProverHint (ZMod SP1Prime) := ProverHint.empty _) : Environment (ZMod SP1Prime) :=
  ((main (varFromOffset Input 0)).proverEnvironment hint inputs).toEnvironment

/-- The evaluated output struct of the chip on the concrete row — the chip's own row layout,
used by the companion Spec-level result checks. -/
def chipOutput (Input : TypeMap) [ProvableType Input] {Output : TypeMap} [ProvableType Output]
    (main : Var Input (ZMod SP1Prime) → Circuit (ZMod SP1Prime) (Var Output (ZMod SP1Prime)))
    (inputs : List (ZMod SP1Prime))
    (hint : ProverHint (ZMod SP1Prime) := ProverHint.empty _) : Output (ZMod SP1Prime) :=
  let circ := main (varFromOffset Input 0)
  ProvableType.eval (circ.proverEnvironment hint inputs).toEnvironment (circ.output inputs.length)

/-- Executable whole-circuit constraint check: no static lookups, and every `assertZero`
expression of the flattened operation list (subcircuits included) evaluates to zero. -/
def constraintsCheck (env : Environment (ZMod SP1Prime)) (ops : Operations (ZMod SP1Prime)) :
    Bool :=
  (FlatOperation.lookups ops.toFlat).isEmpty &&
    (FlatOperation.constraints ops.toFlat).all fun e => decide (Expression.eval env e = 0)

/-- Bridge from the executable check to Clean's `Operations.ConstraintsHold` — axiom-clean; the
per-chip anchors discharge the `constraintsCheck` premise by `native_decide`. -/
theorem constraintsHold_of_check {env : Environment (ZMod SP1Prime)}
    {ops : Operations (ZMod SP1Prime)} (h : constraintsCheck env ops = true) :
    ops.ConstraintsHold env := by
  rw [← Circuit.constraintsHold_toFlat_iff, FlatOperation.constraintsHoldFlat_iff_forall_mem]
  simp only [constraintsCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    List.isEmpty_iff] at h
  exact ⟨h.2, fun l hl => absurd hl (by simp [h.1])⟩

/-- Every event-built R-type input row is a **real** row: the first input column (`is_real`)
is the literal `1`. -/
theorem rTypeEventInputs_is_real (e : AluEventRec) :
    (rTypeEventInputs (F := ZMod SP1Prime) e).head? = some 1 := rfl

/-- Every event-built ALU-type input row is a **real** row: the first input column (`is_real`)
is the literal `1`. -/
theorem aluTypeEventInputs_is_real (e : AluTypeEventRec) :
    (aluTypeEventInputs (F := ZMod SP1Prime) e).head? = some 1 := rfl

/-! ## Struct-building helpers (for chips without an `EventPopulate` input builder) -/

/-- A u64 value as its four canonical u16 limbs, as a field `Word`. -/
def u64Word (x : ℕ) : Word (ZMod SP1Prime) :=
  #v[((x % 65536 : ℕ) : ZMod SP1Prime), (((x >>> 16) % 65536 : ℕ) : ZMod SP1Prime),
     (((x >>> 32) % 65536 : ℕ) : ZMod SP1Prime), (((x >>> 48) % 65536 : ℕ) : ZMod SP1Prime)]

/-- One register-access column block from the record's value and previous/current access
timestamps — the same formulas as `EventPopulate.registerAccessPopulate` (mirroring
`RegisterAccessTimestamp::populate_timestamp`). -/
def accessCols (value prevTs currTs : ℕ) : Extracted.RegisterAccessCols (ZMod SP1Prime) :=
  let prevLow : ℕ := if prevTs >>> 24 = currTs >>> 24 then prevTs % 16777216 else 0
  { prev_value := u64Word value
    access_timestamp :=
      { prev_low := (prevLow : ZMod SP1Prime)
        diff_low_limb := (((currTs % 16777216 - prevLow - 1) % 65536 : ℕ) : ZMod SP1Prime) } }

/-- The `CPUState` block from a canonical clk/pc (mirroring `CPUState::populate`). -/
def cpuState (clk pc : ℕ) : Extracted.CPUState (ZMod SP1Prime) :=
  { clk_high := ((clk >>> 24 : ℕ) : ZMod SP1Prime)
    clk_16_24 := (((clk >>> 16) % 256 : ℕ) : ZMod SP1Prime)
    clk_0_16 := ((clk % 65536 : ℕ) : ZMod SP1Prime)
    pc := #v[((pc % 65536 : ℕ) : ZMod SP1Prime), (((pc >>> 16) % 65536 : ℕ) : ZMod SP1Prime),
             (((pc >>> 32) % 65536 : ℕ) : ZMod SP1Prime)] }

/-- Flatten a chip `Inputs` struct to its input-column list (`ProvableType` flattening order —
the same order `varFromOffset` reads them back). -/
def inputColumns {Input : TypeMap} [ProvableType Input] (s : Input (ZMod SP1Prime)) :
    List (ZMod SP1Prime) := (toElements s).toList

/-! ## Lt (SLT/SLTU — the EF-relevance flagship)

Register-variant SLT rows, the seed row from the release-audit session: `clk = 9`, `pc = 0x1000`,
register indices `rd = x7`, `rs1 = x5`, `rs2 = x6`, access clocks `13/12/11` against previous
timestamp `0` (so `diff_low_limb = 12/11/10` per `RegisterAccessTimestamp::populate_timestamp`).
The gadget internals (u16 compare flags, sign-bit columns, the compare bit) are filled by the
chip's own `LtOperationSigned.populate` witness closure — not hand-coded. -/

/-- SLT with a TRUE comparison: `rs1 = 5 < rs2 = 7` (signed), so `rd` receives `1`. -/
def ltSltTrueEvent : AluTypeEventRec :=
  { clk := 9, pc := 4096, a := 1, b := 5, c := 7, opA := 7, opB := 5, opC := 6, immC := 0,
    tsA := 13, prevTsA := 0, prevA := 0, tsB := 12, prevTsB := 0, tsC := 11, prevTsC := 0 }

/-- SLT with a FALSE comparison: `rs1 = 7 ≥ rs2 = 5` (signed), so `rd` receives `0`. -/
def ltSltFalseEvent : AluTypeEventRec :=
  { clk := 9, pc := 4096, a := 0, b := 7, c := 5, opA := 7, opB := 5, opC := 6, immC := 0,
    tsA := 13, prevTsA := 0, prevA := 0, tsB := 12, prevTsB := 0, tsC := 11, prevTsC := 0 }

/-- The honest `"lt_flags"` one-hot prover hint: `[is_slt, is_sltu]`. -/
def ltFlagsHint (slt : Bool) : ProverHint (ZMod SP1Prime) := fun key n =>
  match key, n with
  | "lt_flags", 2 => #[#v[if slt then 1 else 0, if slt then 0 else 1]]
  | _, _ => #[]

/-- **`LtChip` is satisfiable on a real row with a TRUE comparison**: the full constraint system
holds on the register-variant SLT row `x7 := (5 <ₛ 7) = 1`. -/
theorem lt_slt_true_real_row_satisfiable :
    (chipOperations LtChip.Inputs LtChip.main (aluTypeEventInputs ltSltTrueEvent)).ConstraintsHold
      (chipEnvironment LtChip.Inputs LtChip.main (aluTypeEventInputs ltSltTrueEvent)
        (ltFlagsHint true)) :=
  constraintsHold_of_check (by native_decide)

/-- **`LtChip` is satisfiable on a real row with a FALSE comparison**: the full constraint system
holds on the register-variant SLT row `x7 := (7 <ₛ 5) = 0`. -/
theorem lt_slt_false_real_row_satisfiable :
    (chipOperations LtChip.Inputs LtChip.main (aluTypeEventInputs ltSltFalseEvent)).ConstraintsHold
      (chipEnvironment LtChip.Inputs LtChip.main (aluTypeEventInputs ltSltFalseEvent)
        (ltFlagsHint true)) :=
  constraintsHold_of_check (by native_decide)

/-- Spec-level companion: on the TRUE row the chip's own witness closures compute compare bit `1`
(the value written to `rd`). -/
theorem lt_slt_true_bit :
    (chipOutput LtChip.Inputs LtChip.main (aluTypeEventInputs ltSltTrueEvent)
      (ltFlagsHint true)).lt_operation.result.u16_compare_operation.bit = 1 := by
  native_decide

/-- Spec-level companion: on the FALSE row the chip's own witness closures compute compare bit
`0`. Together with `lt_slt_true_bit` this shows the battery exercises both comparison outcomes. -/
theorem lt_slt_false_bit :
    (chipOutput LtChip.Inputs LtChip.main (aluTypeEventInputs ltSltFalseEvent)
      (ltFlagsHint true)).lt_operation.result.u16_compare_operation.bit = 0 := by
  native_decide

/-! ## Bitwise (AND / XOR) -/

/-- AND row: `rs1 = 0x00FF`, `rs2 = 0x0F0F`, so `rd` receives `0x000F`. Register-variant, same
state/timestamp discipline as the Lt seed. -/
def bitwiseAndEvent : AluTypeEventRec :=
  { clk := 9, pc := 4096, a := 0x000F, b := 0x00FF, c := 0x0F0F, opA := 7, opB := 5, opC := 6,
    immC := 0, tsA := 13, prevTsA := 0, prevA := 0, tsB := 12, prevTsB := 0,
    tsC := 11, prevTsC := 0 }

/-- XOR row: `rs1 = 0x00FF`, `rs2 = 0x0F0F`, so `rd` receives `0x0FF0`. -/
def bitwiseXorEvent : AluTypeEventRec :=
  { clk := 9, pc := 4096, a := 0x0FF0, b := 0x00FF, c := 0x0F0F, opA := 7, opB := 5, opC := 6,
    immC := 0, tsA := 13, prevTsA := 0, prevA := 0, tsB := 12, prevTsB := 0,
    tsC := 11, prevTsC := 0 }

/-- The honest `"bitwise_flags"` one-hot prover hint `[is_xor, is_or, is_and]`, from the executor
opcode discriminants (XOR = 3, OR = 4, AND = 5). -/
def bitwiseFlagsHint (op : ℕ) : ProverHint (ZMod SP1Prime) := fun key n =>
  match key, n with
  | "bitwise_flags", 3 =>
    #[#v[if op = 3 then 1 else 0, if op = 4 then 1 else 0, if op = 5 then 1 else 0]]
  | _, _ => #[]

/-- **`BitwiseChip` is satisfiable on a real AND row**: the full constraint system holds on the
register-variant row `x7 := 0x00FF AND 0x0F0F` (result `0x000F`). -/
theorem bitwise_and_real_row_satisfiable :
    (chipOperations BitwiseChip.Inputs BitwiseChip.main
      (aluTypeEventInputs bitwiseAndEvent)).ConstraintsHold
      (chipEnvironment BitwiseChip.Inputs BitwiseChip.main (aluTypeEventInputs bitwiseAndEvent)
        (bitwiseFlagsHint 5)) :=
  constraintsHold_of_check (by native_decide)

/-- **`BitwiseChip` is satisfiable on a real XOR row**: the full constraint system holds on the
register-variant row `x7 := 0x00FF XOR 0x0F0F` (result `0x0FF0`). -/
theorem bitwise_xor_real_row_satisfiable :
    (chipOperations BitwiseChip.Inputs BitwiseChip.main
      (aluTypeEventInputs bitwiseXorEvent)).ConstraintsHold
      (chipEnvironment BitwiseChip.Inputs BitwiseChip.main (aluTypeEventInputs bitwiseXorEvent)
        (bitwiseFlagsHint 3)) :=
  constraintsHold_of_check (by native_decide)

/-! ## UType (LUI / AUIPC — the predecessor audit's 'no theorem' precedent chip) -/

/-- LUI row: `x7 := 0x12345000` (`is_auipc = 0`, `op_b_imm` the already-shifted U-immediate),
write access clock `13` against previous timestamp `0`. -/
def utypeLuiInputs : UTypeChip.Inputs (ZMod SP1Prime) :=
  { is_real := 1
    state := cpuState 9 4096
    adapter :=
      { op_a := 7, op_a_memory := accessCols 0 0 13, op_a_0 := 0,
        op_b_imm := u64Word 0x12345000, op_c_imm := u64Word 0 }
    is_auipc := 0 }

/-- AUIPC row: `x7 := pc + 0x1000 = 0x2000` at `pc = 0x1000` (`is_auipc = 1`, the witnessed
addend is the pc word). -/
def utypeAuipcInputs : UTypeChip.Inputs (ZMod SP1Prime) :=
  { is_real := 1
    state := cpuState 9 4096
    adapter :=
      { op_a := 7, op_a_memory := accessCols 0 0 13, op_a_0 := 0,
        op_b_imm := u64Word 0x1000, op_c_imm := u64Word 0 }
    is_auipc := 1 }

/-- **`UTypeChip` is satisfiable on a real LUI row**: the full constraint system holds on
`x7 := LUI 0x12345000`. -/
theorem utype_lui_real_row_satisfiable :
    (chipOperations UTypeChip.Inputs UTypeChip.main (inputColumns utypeLuiInputs)).ConstraintsHold
      (chipEnvironment UTypeChip.Inputs UTypeChip.main (inputColumns utypeLuiInputs)) :=
  constraintsHold_of_check (by native_decide)

/-- **`UTypeChip` is satisfiable on a real AUIPC row**: the full constraint system holds on
`x7 := pc + 0x1000` at `pc = 0x1000`. -/
theorem utype_auipc_real_row_satisfiable :
    (chipOperations UTypeChip.Inputs UTypeChip.main
      (inputColumns utypeAuipcInputs)).ConstraintsHold
      (chipEnvironment UTypeChip.Inputs UTypeChip.main (inputColumns utypeAuipcInputs)) :=
  constraintsHold_of_check (by native_decide)

/-! ## Jalr -/

/-- JALR row: `x7 := pc + 4 = 0x1004`, jump to `rs1 + imm = 0x2000 + 0x10 = 0x2010` (aligned,
`lsb = 0`), with `rs1 = x5 = 0x2000`. -/
def jalrInputs : JalrChip.Inputs (ZMod SP1Prime) :=
  { is_real := 1
    state := cpuState 9 4096
    adapter :=
      { op_a := 7, op_a_memory := accessCols 0 0 13, op_a_0 := 0,
        op_b := 5, op_b_memory := accessCols 0x2000 0 12, op_c_imm := u64Word 0x10 } }

/-- **`JalrChip` is satisfiable on a real row**: the full constraint system holds on
`jalr x7, 0x10(x5)` with `x5 = 0x2000` at `pc = 0x1000` (link `0x1004`, target `0x2010`). -/
theorem jalr_real_row_satisfiable :
    (chipOperations JalrChip.Inputs JalrChip.main (inputColumns jalrInputs)).ConstraintsHold
      (chipEnvironment JalrChip.Inputs JalrChip.main (inputColumns jalrInputs)) :=
  constraintsHold_of_check (by native_decide)

/-! ## Loads

Shared discipline: `pc = 0x1000`, `clk = 9`; base register `x5 = 0x12000` (the address gadget
asserts `inv · (value[1] + value[2]) = is_real`, so real load/store addresses must exceed `2^16`);
RAM word `0x1111222233334444` at the 8-byte-aligned address; RAM previously touched at timestamp
`(0, 0)` in the same high window (`compare_low = 1`, so the gap decomposition asserts
`clk_low + 1 - prev_low - 1 = diff_low_limb`, i.e. `diff_low_limb = 9`). -/

/-- The RAM-access column block for the shared load/store row: previous value
`0x1111222233334444`, previously accessed at `(0, 0)`, current access at `clk_low = 9`. -/
def ramAccess : Extracted.MemoryAccessCols (ZMod SP1Prime) :=
  { prev_value := u64Word 0x1111222233334444
    access_timestamp :=
      { prev_high := 0, prev_low := 0, compare_low := 1, diff_low_limb := 9,
        diff_high_limb := 0 } }

/-- LW row: `x7 := signExtend32(mem[0x12004])` — base `x5 = 0x12000`, imm `4`, so `offset_bit = 1`
selects the high 32-bit half `[0x2222, 0x1111]` of the RAM word (loaded value `0x11112222`,
`msb = 0`). -/
def loadWordInputs : LoadWordChip.Inputs (ZMod SP1Prime) :=
  { is_lw := 1, is_lwu := 0
    state := cpuState 9 4096
    adapter :=
      { op_a := 7, op_a_memory := accessCols 0 0 13, op_a_0 := 0,
        op_b := 5, op_b_memory := accessCols 0x12000 0 12, op_c_imm := u64Word 4 }
    memory_access := ramAccess
    offset_bit := 1
    selected_word := #v[(0x2222 : ZMod SP1Prime), (0x1111 : ZMod SP1Prime)]
    msb := 0 }

/-- **`LoadWordChip` is satisfiable on a real LW row**: the full constraint system holds on
`lw x7, 4(x5)` with `x5 = 0x12000` and `mem[0x12000..8] = 0x1111222233334444`
(loaded value `0x11112222`). -/
theorem loadword_real_row_satisfiable :
    (chipOperations LoadWordChip.Inputs LoadWordChip.main
      (inputColumns loadWordInputs)).ConstraintsHold
      (chipEnvironment LoadWordChip.Inputs LoadWordChip.main (inputColumns loadWordInputs)) :=
  constraintsHold_of_check (by native_decide)

/-- LB row: `x7 := signExtend8(mem[0x12005])` — offset bits `[1,0,1]` select limb 2 (`0x2222`)
and its high byte (`0x22`; `msb = 0`, loaded value `0x22`). -/
def loadByteInputs : LoadByteChip.Inputs (ZMod SP1Prime) :=
  { is_lb := 1, is_lbu := 0
    state := cpuState 9 4096
    adapter :=
      { op_a := 7, op_a_memory := accessCols 0 0 13, op_a_0 := 0,
        op_b := 5, op_b_memory := accessCols 0x12000 0 12, op_c_imm := u64Word 5 }
    memory_access := ramAccess
    offset_bit := #v[1, 0, 1]
    selected_limb := 0x2222
    selected_limb_low_byte := 0x22
    selected_byte := 0x22
    msb := 0 }

/-- **`LoadByteChip` is satisfiable on a real LB row**: the full constraint system holds on
`lb x7, 5(x5)` (loaded byte `0x22`). -/
theorem loadbyte_real_row_satisfiable :
    (chipOperations LoadByteChip.Inputs LoadByteChip.main
      (inputColumns loadByteInputs)).ConstraintsHold
      (chipEnvironment LoadByteChip.Inputs LoadByteChip.main (inputColumns loadByteInputs)) :=
  constraintsHold_of_check (by native_decide)

/-- LH row: `x7 := signExtend16(mem[0x12006])` — offset bits `[1,1]` (address bits 1/2) select
limb 3 (`0x1111`; `msb = 0`). -/
def loadHalfInputs : LoadHalfChip.Inputs (ZMod SP1Prime) :=
  { is_lh := 1, is_lhu := 0
    state := cpuState 9 4096
    adapter :=
      { op_a := 7, op_a_memory := accessCols 0 0 13, op_a_0 := 0,
        op_b := 5, op_b_memory := accessCols 0x12000 0 12, op_c_imm := u64Word 6 }
    memory_access := ramAccess
    offset_bit := #v[1, 1]
    selected_half := 0x1111
    msb := 0 }

/-- **`LoadHalfChip` is satisfiable on a real LH row**: the full constraint system holds on
`lh x7, 6(x5)` (loaded half `0x1111`). -/
theorem loadhalf_real_row_satisfiable :
    (chipOperations LoadHalfChip.Inputs LoadHalfChip.main
      (inputColumns loadHalfInputs)).ConstraintsHold
      (chipEnvironment LoadHalfChip.Inputs LoadHalfChip.main (inputColumns loadHalfInputs)) :=
  constraintsHold_of_check (by native_decide)

/-- LD row: `x7 := mem[0x12000] = 0x1111222233334444` (8-byte aligned, imm `0`). -/
def loadDoubleInputs : LoadDoubleChip.Inputs (ZMod SP1Prime) :=
  { is_real := 1
    state := cpuState 9 4096
    adapter :=
      { op_a := 7, op_a_memory := accessCols 0 0 13, op_a_0 := 0,
        op_b := 5, op_b_memory := accessCols 0x12000 0 12, op_c_imm := u64Word 0 }
    memory_access := ramAccess }

/-- **`LoadDoubleChip` is satisfiable on a real LD row**: the full constraint system holds on
`ld x7, 0(x5)` (loaded word `0x1111222233334444`). -/
theorem loaddouble_real_row_satisfiable :
    (chipOperations LoadDoubleChip.Inputs LoadDoubleChip.main
      (inputColumns loadDoubleInputs)).ConstraintsHold
      (chipEnvironment LoadDoubleChip.Inputs LoadDoubleChip.main
        (inputColumns loadDoubleInputs)) :=
  constraintsHold_of_check (by native_decide)

/-- LoadX0 row: `lw x0, 4(x5)` — a real load discarded into `x0` (`op_a_0 = 1`, the x0 read is
the zero word; the chip asserts the destination IS x0). The memory read itself is non-degenerate
(the same RAM word as the other loads). -/
def loadX0Inputs : LoadX0Chip.Inputs (ZMod SP1Prime) :=
  { is_lb := 0, is_lbu := 0, is_lh := 0, is_lhu := 0, is_lw := 1, is_lwu := 0, is_ld := 0
    state := cpuState 9 4096
    adapter :=
      { op_a := 0, op_a_memory := accessCols 0 0 13, op_a_0 := 1,
        op_b := 5, op_b_memory := accessCols 0x12000 0 12, op_c_imm := u64Word 4 }
    memory_access := ramAccess
    offset_bit := #v[0, 0, 1] }

/-- **`LoadX0Chip` is satisfiable on a real row**: the full constraint system holds on
`lw x0, 4(x5)` (a discarded but genuinely performed memory read). -/
theorem loadx0_real_row_satisfiable :
    (chipOperations LoadX0Chip.Inputs LoadX0Chip.main (inputColumns loadX0Inputs)).ConstraintsHold
      (chipEnvironment LoadX0Chip.Inputs LoadX0Chip.main (inputColumns loadX0Inputs)) :=
  constraintsHold_of_check (by native_decide)

/-! ## Addi -/

/-- ADDI row: `x7 := x5 + 23 = 123` with `x5 = 100`. -/
def addiInputs : AddiChip.Inputs (ZMod SP1Prime) :=
  { is_real := 1
    state := cpuState 9 4096
    adapter :=
      { op_a := 7, op_a_memory := accessCols 0 0 13, op_a_0 := 0,
        op_b := 5, op_b_memory := accessCols 100 0 12, op_c_imm := u64Word 23 } }

/-- **`AddiChip` is satisfiable on a real row**: the full constraint system holds on
`addi x7, x5, 23` with `x5 = 100` (result `123`). -/
theorem addi_real_row_satisfiable :
    (chipOperations AddiChip.Inputs AddiChip.main (inputColumns addiInputs)).ConstraintsHold
      (chipEnvironment AddiChip.Inputs AddiChip.main (inputColumns addiInputs)) :=
  constraintsHold_of_check (by native_decide)

/-! ## DivRem (unsigned 64-bit DIVU with a nonzero divisor) -/

/-- DIVU row: `x7 := 100 / 7 = 14` (remainder `2`, divisor nonzero). R-type register row with the
standard state/timestamp discipline. -/
def divRemDivuEvent : AluEventRec :=
  { clk := 9, pc := 4096, a := 14, b := 100, c := 7, opA := 7, opB := 5, opC := 6,
    tsA := 13, prevTsA := 0, prevA := 0, tsB := 12, prevTsB := 0, tsC := 11, prevTsC := 0 }

/-- The honest `"div_rem_flags"` one-hot prover hint (slot order
`[div, divu, rem, remu, divw, remw, divuw, remuw]`), from the executor opcode. -/
def divRemFlagsHint (op : ℕ) : ProverHint (ZMod SP1Prime) := fun key n =>
  match key, n with
  | "div_rem_flags", 8 =>
    #[#v[if op = 15 then 1 else 0, if op = 16 then 1 else 0, if op = 17 then 1 else 0,
         if op = 18 then 1 else 0, if op = 25 then 1 else 0, if op = 27 then 1 else 0,
         if op = 26 then 1 else 0, if op = 28 then 1 else 0]]
  | _, _ => #[]

/-- **`DivRemChip` is satisfiable on a real DIVU row**: the full constraint system holds on
`divu x7, x5, x6` with `x5 = 100`, `x6 = 7` (quotient `14`, remainder `2`). -/
theorem divrem_divu_real_row_satisfiable :
    (chipOperations DivRemChip.Inputs DivRemChip.main
      (rTypeEventInputs divRemDivuEvent)).ConstraintsHold
      (chipEnvironment DivRemChip.Inputs DivRemChip.main (rTypeEventInputs divRemDivuEvent)
        (divRemFlagsHint 16)) :=
  constraintsHold_of_check (by native_decide)

/-! ## ShiftLeft / ShiftRight -/

/-- SLL row: `x7 := 0x1234 <<< 8 = 0x123400` (register shift amount `x6 = 8`). -/
def shiftLeftEvent : AluTypeEventRec :=
  { clk := 9, pc := 4096, a := 0x123400, b := 0x1234, c := 8, opA := 7, opB := 5, opC := 6,
    immC := 0, tsA := 13, prevTsA := 0, prevA := 0, tsB := 12, prevTsB := 0,
    tsC := 11, prevTsC := 0 }

/-- The honest `"shift_left_flags"` one-hot prover hint `[is_sll, is_sllw]`. -/
def shiftLeftFlagsHint (op : ℕ) : ProverHint (ZMod SP1Prime) := fun key n =>
  match key, n with
  | "shift_left_flags", 2 => #[#v[if op = 6 then 1 else 0, if op = 21 then 1 else 0]]
  | _, _ => #[]

/-- **`ShiftLeftChip` is satisfiable on a real SLL row**: the full constraint system holds on
`sll x7, x5, x6` with `x5 = 0x1234`, `x6 = 8` (result `0x123400`). -/
theorem shiftleft_sll_real_row_satisfiable :
    (chipOperations ShiftLeftChip.Inputs ShiftLeftChip.main
      (aluTypeEventInputs shiftLeftEvent)).ConstraintsHold
      (chipEnvironment ShiftLeftChip.Inputs ShiftLeftChip.main
        (aluTypeEventInputs shiftLeftEvent) (shiftLeftFlagsHint 6)) :=
  constraintsHold_of_check (by native_decide)

/-- SRL row: `x7 := 0x1234 >>> 4 = 0x123` (register shift amount `x6 = 4`). -/
def shiftRightEvent : AluTypeEventRec :=
  { clk := 9, pc := 4096, a := 0x123, b := 0x1234, c := 4, opA := 7, opB := 5, opC := 6,
    immC := 0, tsA := 13, prevTsA := 0, prevA := 0, tsB := 12, prevTsB := 0,
    tsC := 11, prevTsC := 0 }

/-- The honest `"shift_right_flags"` one-hot prover hint `[is_srl, is_sra, is_srlw, is_sraw]`. -/
def shiftRightFlagsHint (op : ℕ) : ProverHint (ZMod SP1Prime) := fun key n =>
  match key, n with
  | "shift_right_flags", 4 =>
    #[#v[if op = 7 then 1 else 0, if op = 8 then 1 else 0,
         if op = 22 then 1 else 0, if op = 23 then 1 else 0]]
  | _, _ => #[]

/-- **`ShiftRightChip` is satisfiable on a real SRL row**: the full constraint system holds on
`srl x7, x5, x6` with `x5 = 0x1234`, `x6 = 4` (result `0x123`). -/
theorem shiftright_srl_real_row_satisfiable :
    (chipOperations ShiftRightChip.Inputs ShiftRightChip.main
      (aluTypeEventInputs shiftRightEvent)).ConstraintsHold
      (chipEnvironment ShiftRightChip.Inputs ShiftRightChip.main
        (aluTypeEventInputs shiftRightEvent) (shiftRightFlagsHint 7)) :=
  constraintsHold_of_check (by native_decide)

/-! ## Add / Sub / Addw / Subw (fixed-witness R-type / ALU-type rows, no hint) -/

/-- ADD row: `x7 := x5 + x6 = 100 + 23 = 123`. -/
def addEvent : AluEventRec :=
  { clk := 9, pc := 4096, a := 123, b := 100, c := 23, opA := 7, opB := 5, opC := 6,
    tsA := 13, prevTsA := 0, prevA := 0, tsB := 12, prevTsB := 0, tsC := 11, prevTsC := 0 }

/-- **`AddChip` is satisfiable on a real row**: the full constraint system holds on
`add x7, x5, x6` with `x5 = 100`, `x6 = 23` (result `123`). -/
theorem add_real_row_satisfiable :
    (chipOperations AddChip.Inputs AddChip.main (rTypeEventInputs addEvent)).ConstraintsHold
      (chipEnvironment AddChip.Inputs AddChip.main (rTypeEventInputs addEvent)) :=
  constraintsHold_of_check (by native_decide)

/-- SUB row: `x7 := x5 - x6 = 123 - 23 = 100`. -/
def subEvent : AluEventRec :=
  { clk := 9, pc := 4096, a := 100, b := 123, c := 23, opA := 7, opB := 5, opC := 6,
    tsA := 13, prevTsA := 0, prevA := 0, tsB := 12, prevTsB := 0, tsC := 11, prevTsC := 0 }

/-- **`SubChip` is satisfiable on a real row**: the full constraint system holds on
`sub x7, x5, x6` with `x5 = 123`, `x6 = 23` (result `100`). -/
theorem sub_real_row_satisfiable :
    (chipOperations SubChip.Inputs SubChip.main (rTypeEventInputs subEvent)).ConstraintsHold
      (chipEnvironment SubChip.Inputs SubChip.main (rTypeEventInputs subEvent)) :=
  constraintsHold_of_check (by native_decide)

/-- ADDW row (ALU-type, register): `x7 := (x5 + x6)ʷ = 100 + 23 = 123`. -/
def addwEvent : AluTypeEventRec :=
  { clk := 9, pc := 4096, a := 123, b := 100, c := 23, opA := 7, opB := 5, opC := 6, immC := 0,
    tsA := 13, prevTsA := 0, prevA := 0, tsB := 12, prevTsB := 0, tsC := 11, prevTsC := 0 }

/-- **`AddwChip` is satisfiable on a real row**: the full constraint system holds on
`addw x7, x5, x6` with `x5 = 100`, `x6 = 23` (result `123`). -/
theorem addw_real_row_satisfiable :
    (chipOperations AddwChip.Inputs AddwChip.main (aluTypeEventInputs addwEvent)).ConstraintsHold
      (chipEnvironment AddwChip.Inputs AddwChip.main (aluTypeEventInputs addwEvent)) :=
  constraintsHold_of_check (by native_decide)

/-- SUBW row: `x7 := (x5 - x6)ʷ = 123 - 23 = 100`. -/
def subwEvent : AluEventRec :=
  { clk := 9, pc := 4096, a := 100, b := 123, c := 23, opA := 7, opB := 5, opC := 6,
    tsA := 13, prevTsA := 0, prevA := 0, tsB := 12, prevTsB := 0, tsC := 11, prevTsC := 0 }

/-- **`SubwChip` is satisfiable on a real row**: the full constraint system holds on
`subw x7, x5, x6` with `x5 = 123`, `x6 = 23` (result `100`). -/
theorem subw_real_row_satisfiable :
    (chipOperations SubwChip.Inputs SubwChip.main (rTypeEventInputs subwEvent)).ConstraintsHold
      (chipEnvironment SubwChip.Inputs SubwChip.main (rTypeEventInputs subwEvent)) :=
  constraintsHold_of_check (by native_decide)

/-! ## Mul -/

/-- MUL row: `x7 := x5 * x6 = 7 * 6 = 42`. -/
def mulEvent : AluEventRec :=
  { clk := 9, pc := 4096, a := 42, b := 7, c := 6, opA := 7, opB := 5, opC := 6,
    tsA := 13, prevTsA := 0, prevA := 0, tsB := 12, prevTsB := 0, tsC := 11, prevTsC := 0 }

/-- The honest `"mul_flags"` one-hot prover hint
`[is_mul, is_mulh, is_mulhu, is_mulhsu, is_mulw]`. -/
def mulFlagsHint (op : ℕ) : ProverHint (ZMod SP1Prime) := fun key n =>
  match key, n with
  | "mul_flags", 5 =>
    #[#v[if op = 11 then 1 else 0, if op = 12 then 1 else 0, if op = 13 then 1 else 0,
         if op = 14 then 1 else 0, if op = 24 then 1 else 0]]
  | _, _ => #[]

/-- **`MulChip` is satisfiable on a real MUL row**: the full constraint system holds on
`mul x7, x5, x6` with `x5 = 7`, `x6 = 6` (result `42`). -/
theorem mul_real_row_satisfiable :
    (chipOperations MulChip.Inputs MulChip.main (rTypeEventInputs mulEvent)).ConstraintsHold
      (chipEnvironment MulChip.Inputs MulChip.main (rTypeEventInputs mulEvent)
        (mulFlagsHint 11)) :=
  constraintsHold_of_check (by native_decide)

/-! ## Branch / Jal -/

/-- BEQ (taken) row: `beq x5, x6, +0x100` with `x5 = x6 = 42` (equal, nonzero operands; the
branch is taken, `next_pc = 0x1100`). The branch adapter reads rs1 on the `op_a` slot. -/
def branchBeqInputs : BranchChip.Inputs (ZMod SP1Prime) :=
  { is_real := 1
    state := cpuState 9 4096
    adapter :=
      { op_a := 5, op_a_memory := accessCols 42 0 13, op_a_0 := 0,
        op_b := 6, op_b_memory := accessCols 42 0 12, op_c_imm := u64Word 0x100 } }

/-- The honest `"branch_flags"` one-hot (opcodes BEQ = 40 … BGEU = 45) + `"branch_branching"`
decision prover hints. -/
def branchFlagsHint (op : ℕ) (branching : Bool) : ProverHint (ZMod SP1Prime) := fun key n =>
  match key, n with
  | "branch_flags", 6 =>
    #[#v[if op = 40 then 1 else 0, if op = 41 then 1 else 0, if op = 42 then 1 else 0,
         if op = 43 then 1 else 0, if op = 44 then 1 else 0, if op = 45 then 1 else 0]]
  | "branch_branching", 1 => #[#v[if branching then 1 else 0]]
  | _, _ => #[]

/-- **`BranchChip` is satisfiable on a real taken-BEQ row**: the full constraint system holds on
`beq x5, x6, +0x100` with `x5 = x6 = 42` (taken; `next_pc = pc + 0x100`). -/
theorem branch_beq_taken_real_row_satisfiable :
    (chipOperations BranchChip.Inputs BranchChip.main
      (inputColumns branchBeqInputs)).ConstraintsHold
      (chipEnvironment BranchChip.Inputs BranchChip.main (inputColumns branchBeqInputs)
        (branchFlagsHint 40 true)) :=
  constraintsHold_of_check (by native_decide)

/-- JAL row: `jal x7, +0x100` at `pc = 0x1000` (link `x7 := 0x1004`, jump to `0x1100`). -/
def jalInputs : JalChip.Inputs (ZMod SP1Prime) :=
  { is_real := 1
    state := cpuState 9 4096
    adapter :=
      { op_a := 7, op_a_memory := accessCols 0 0 13, op_a_0 := 0,
        op_b_imm := u64Word 0x100, op_c_imm := u64Word 0 } }

/-- **`JalChip` is satisfiable on a real row**: the full constraint system holds on
`jal x7, +0x100` at `pc = 0x1000` (link `0x1004`, target `0x1100`). -/
theorem jal_real_row_satisfiable :
    (chipOperations JalChip.Inputs JalChip.main (inputColumns jalInputs)).ConstraintsHold
      (chipEnvironment JalChip.Inputs JalChip.main (inputColumns jalInputs)) :=
  constraintsHold_of_check (by native_decide)

/-! ## Stores

Same address/RAM discipline as the loads (`x5 = 0x12000` base, RAM word `0x1111222233334444`,
previous RAM access at `(0, 0)`); the store source register is read on the adapter's `op_a` slot,
and `store_value` (the committed new RAM word) must splice the stored limbs into the previous
word per the chip's selection gates. -/

/-- SW row: `sw x7, 4(x5)` with `x7 = 0xAABBCCDD` — `offset_bit = 1` replaces the high 32-bit
half: new RAM word `0xAABBCCDD33334444`. -/
def storeWordInputs : StoreWordChip.Inputs (ZMod SP1Prime) :=
  { is_real := 1
    state := cpuState 9 4096
    adapter :=
      { op_a := 7, op_a_memory := accessCols 0xAABBCCDD 0 13, op_a_0 := 0,
        op_b := 5, op_b_memory := accessCols 0x12000 0 12, op_c_imm := u64Word 4 }
    memory_access := ramAccess
    offset_bit := 1
    store_value := u64Word 0xAABBCCDD33334444 }

/-- **`StoreWordChip` is satisfiable on a real SW row**: the full constraint system holds on
`sw x7, 4(x5)` with `x7 = 0xAABBCCDD` (new RAM word `0xAABBCCDD33334444`). -/
theorem storeword_real_row_satisfiable :
    (chipOperations StoreWordChip.Inputs StoreWordChip.main
      (inputColumns storeWordInputs)).ConstraintsHold
      (chipEnvironment StoreWordChip.Inputs StoreWordChip.main (inputColumns storeWordInputs)) :=
  constraintsHold_of_check (by native_decide)

/-- SH row: `sh x7, 6(x5)` with `x7 = 0xCCDD` — offset bits `[1,1]` replace limb 3: new RAM word
`0xCCDD222233334444`. -/
def storeHalfInputs : StoreHalfChip.Inputs (ZMod SP1Prime) :=
  { is_real := 1
    state := cpuState 9 4096
    adapter :=
      { op_a := 7, op_a_memory := accessCols 0xCCDD 0 13, op_a_0 := 0,
        op_b := 5, op_b_memory := accessCols 0x12000 0 12, op_c_imm := u64Word 6 }
    memory_access := ramAccess
    offset_bit := #v[1, 1]
    store_value := u64Word 0xCCDD222233334444 }

/-- **`StoreHalfChip` is satisfiable on a real SH row**: the full constraint system holds on
`sh x7, 6(x5)` with `x7 = 0xCCDD` (new RAM word `0xCCDD222233334444`). -/
theorem storehalf_real_row_satisfiable :
    (chipOperations StoreHalfChip.Inputs StoreHalfChip.main
      (inputColumns storeHalfInputs)).ConstraintsHold
      (chipEnvironment StoreHalfChip.Inputs StoreHalfChip.main (inputColumns storeHalfInputs)) :=
  constraintsHold_of_check (by native_decide)

/-- SB row: `sb x7, 5(x5)` with `x7 = 0xEE` — offset bits `[1,0,1]` replace the high byte of
limb 2 (`0x2222 → 0xEE22`, `increment = 0xCC00`): new RAM word `0x1111EE2233334444`. -/
def storeByteInputs : StoreByteChip.Inputs (ZMod SP1Prime) :=
  { is_real := 1
    state := cpuState 9 4096
    adapter :=
      { op_a := 7, op_a_memory := accessCols 0xEE 0 13, op_a_0 := 0,
        op_b := 5, op_b_memory := accessCols 0x12000 0 12, op_c_imm := u64Word 5 }
    memory_access := ramAccess
    offset_bit := #v[1, 0, 1]
    mem_limb := 0x2222
    mem_limb_low_byte := 0x22
    register_low_byte := 0xEE
    increment := 0xCC00
    store_value := u64Word 0x1111EE2233334444 }

/-- **`StoreByteChip` is satisfiable on a real SB row**: the full constraint system holds on
`sb x7, 5(x5)` with `x7 = 0xEE` (new RAM word `0x1111EE2233334444`). -/
theorem storebyte_real_row_satisfiable :
    (chipOperations StoreByteChip.Inputs StoreByteChip.main
      (inputColumns storeByteInputs)).ConstraintsHold
      (chipEnvironment StoreByteChip.Inputs StoreByteChip.main (inputColumns storeByteInputs)) :=
  constraintsHold_of_check (by native_decide)

/-- SD row: `sd x7, 0(x5)` with `x7 = 0xAABBCCDD11223344` (the whole RAM word replaced). -/
def storeDoubleInputs : StoreDoubleChip.Inputs (ZMod SP1Prime) :=
  { is_real := 1
    state := cpuState 9 4096
    adapter :=
      { op_a := 7, op_a_memory := accessCols 0xAABBCCDD11223344 0 13, op_a_0 := 0,
        op_b := 5, op_b_memory := accessCols 0x12000 0 12, op_c_imm := u64Word 0 }
    memory_access := ramAccess }

/-- **`StoreDoubleChip` is satisfiable on a real SD row**: the full constraint system holds on
`sd x7, 0(x5)` with `x7 = 0xAABBCCDD11223344`. -/
theorem storedouble_real_row_satisfiable :
    (chipOperations StoreDoubleChip.Inputs StoreDoubleChip.main
      (inputColumns storeDoubleInputs)).ConstraintsHold
      (chipEnvironment StoreDoubleChip.Inputs StoreDoubleChip.main
        (inputColumns storeDoubleInputs)) :=
  constraintsHold_of_check (by native_decide)

/-! ## AluX0 -/

/-- AluX0 row: `add x0, x5, x6` — a real ALU op discarded into `x0` (`op_a_0 = 1`, asserted; the
x0 read is the zero word) with non-degenerate sources `x5 = 100`, `x6 = 23` (opcode `0` = ADD). -/
def aluX0Inputs : AluX0Chip.Inputs (ZMod SP1Prime) :=
  { state := cpuState 9 4096
    adapter :=
      { op_a := 0, op_a_memory := accessCols 0 0 13, op_a_0 := 1,
        op_b := 5, op_b_memory := accessCols 100 0 12,
        op_c := u64Word 6, op_c_memory := accessCols 23 0 11, imm_c := 0 }
    opcode := 0
    is_real := 1 }

/-- **`AluX0Chip` is satisfiable on a real row**: the full constraint system holds on
`add x0, x5, x6` (a discarded but genuinely dispatched ALU op; the chip asserts the
destination IS x0). -/
theorem alux0_real_row_satisfiable :
    (chipOperations AluX0Chip.Inputs AluX0Chip.main (inputColumns aluX0Inputs)).ConstraintsHold
      (chipEnvironment AluX0Chip.Inputs AluX0Chip.main (inputColumns aluX0Inputs)) :=
  constraintsHold_of_check (by native_decide)

/-! ## Battery-level guard -/

/-- Guard against a degenerate reading of the anchors above: on its anchor row, **every** chip's
flattened operation list carries a nonempty `assertZero` constraint list — so no satisfiability
theorem in this battery is a vacuous evaluation over an empty assertion system. -/
theorem constraint_systems_nonempty :
    ([chipOperations LtChip.Inputs LtChip.main (aluTypeEventInputs ltSltTrueEvent),
      chipOperations LtChip.Inputs LtChip.main (aluTypeEventInputs ltSltFalseEvent),
      chipOperations BitwiseChip.Inputs BitwiseChip.main (aluTypeEventInputs bitwiseAndEvent),
      chipOperations BitwiseChip.Inputs BitwiseChip.main (aluTypeEventInputs bitwiseXorEvent),
      chipOperations UTypeChip.Inputs UTypeChip.main (inputColumns utypeLuiInputs),
      chipOperations UTypeChip.Inputs UTypeChip.main (inputColumns utypeAuipcInputs),
      chipOperations JalrChip.Inputs JalrChip.main (inputColumns jalrInputs),
      chipOperations LoadWordChip.Inputs LoadWordChip.main (inputColumns loadWordInputs),
      chipOperations LoadByteChip.Inputs LoadByteChip.main (inputColumns loadByteInputs),
      chipOperations LoadHalfChip.Inputs LoadHalfChip.main (inputColumns loadHalfInputs),
      chipOperations LoadDoubleChip.Inputs LoadDoubleChip.main (inputColumns loadDoubleInputs),
      chipOperations LoadX0Chip.Inputs LoadX0Chip.main (inputColumns loadX0Inputs),
      chipOperations AddiChip.Inputs AddiChip.main (inputColumns addiInputs),
      chipOperations DivRemChip.Inputs DivRemChip.main (rTypeEventInputs divRemDivuEvent),
      chipOperations ShiftLeftChip.Inputs ShiftLeftChip.main (aluTypeEventInputs shiftLeftEvent),
      chipOperations ShiftRightChip.Inputs ShiftRightChip.main
        (aluTypeEventInputs shiftRightEvent),
      chipOperations AddChip.Inputs AddChip.main (rTypeEventInputs addEvent),
      chipOperations SubChip.Inputs SubChip.main (rTypeEventInputs subEvent),
      chipOperations AddwChip.Inputs AddwChip.main (aluTypeEventInputs addwEvent),
      chipOperations SubwChip.Inputs SubwChip.main (rTypeEventInputs subwEvent),
      chipOperations MulChip.Inputs MulChip.main (rTypeEventInputs mulEvent),
      chipOperations BranchChip.Inputs BranchChip.main (inputColumns branchBeqInputs),
      chipOperations JalChip.Inputs JalChip.main (inputColumns jalInputs),
      chipOperations StoreWordChip.Inputs StoreWordChip.main (inputColumns storeWordInputs),
      chipOperations StoreHalfChip.Inputs StoreHalfChip.main (inputColumns storeHalfInputs),
      chipOperations StoreByteChip.Inputs StoreByteChip.main (inputColumns storeByteInputs),
      chipOperations StoreDoubleChip.Inputs StoreDoubleChip.main
        (inputColumns storeDoubleInputs),
      chipOperations AluX0Chip.Inputs AluX0Chip.main (inputColumns aluX0Inputs)].all
      fun ops => !(FlatOperation.constraints ops.toFlat).isEmpty) = true := by
  native_decide

end SP1Clean.NonVacuityRealTests
