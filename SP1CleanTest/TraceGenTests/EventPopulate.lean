import SP1CleanTest.TraceGenTests.Conformance

/-! # Event → input-column mirrors for the trace-generation conformance layer.

Whole rows are derived from the chip circuits (`TraceGenerator.lean`) and checked against SP1's
real prover by the dump-anchored pipeline (`export/sp1dump/` + the `--testdata` generation-time
gate in `scripts/witgenExport.lean`), not by a per-chip `native_decide` anchor; the *only*
hand-written remainder of SP1's `generate_trace` is the event → input-column extraction,
mirrored here. These are direct ℕ-arithmetic transcriptions of
SP1's adapter populate functions (read-only references, paths relative to the sibling `sp1`
checkout):

- `cpuStatePopulate` ← `CPUState::populate` (`crates/core/machine/src/adapter/state.rs`):
  clk split as `clk >> 24` / `(clk >> 16) & 0xFF` / `clk & 0xFFFF`, pc as three u16 limbs;
- `registerAccessPopulate` ← `RegisterAccessCols::populate` + `RegisterAccessTimestamp::
  populate_timestamp` (`crates/core/machine/src/memory/consistency/trace.rs`): the previous value
  as four u16 limbs, then `prev_low := if same 24-bit-high window then prev & 0xFFFFFF else 0` and
  `diff_low_limb := (curr & 0xFFFFFF) - prev_low - 1` truncated to u16. (`diff_high_limb` is only a
  range-check event, not a column.) The subtraction is exact for any record with increasing
  timestamps in the same high window — which the dumper's battery guarantees; a violation would
  surface as an anchor mismatch, not silent wrap;
- `rTypeReaderPopulate` ← `RTypeReader::populate` (`crates/core/machine/src/adapter/register/
  r_type.rs`): register indices, the three access blocks, and the `op_a_0` flag. Per
  `MemoryRecordEnum::previous_record`, a **Write** slot's `prev_value` is the overwritten value
  (`prevA`) while a **Read** slot's is the value read (`b`/`c`);
- `aluTypeReaderPopulate` ← `ALUTypeReader::populate` (`crates/core/machine/src/adapter/register/
  alu_type.rs`): like `RTypeReader` for the `op_a`/`op_b` slots, but the `op_c` slot is an
  immediate-capable `Word` + access block + `imm_c` flag. The `op_c` Word holds the raw record
  value `opC` as four u16 limbs — the **register index** (`[idx, 0, 0, 0]`) on register-`c` rows,
  the **immediate value** on immediate rows. On immediate rows (`record.c.is_none()`) the populate
  copies the `op_c` Word into `op_c_memory.prev_value` and zeroes both timestamp columns; on
  register rows it populates the access block from the read record.

Flattening order matches the `ProvableStruct` derivations field-for-field (`FormalModel/Contracts/Chips.lean`
`Inputs` = `is_real ++ state ++ adapter`; `Extracted/CPUState.lean`; `Extracted/RTypeReader.lean`;
`Extracted/ALUTypeReader.lean`), which in turn mirror SP1's `repr(C)` column structs. Everything is
computable and axiom-clean. -/

namespace SP1Clean.TraceGenTests

/-- One ALU row's worth of executor data for an `RTypeReader` chip: the `AluEvent` fields plus the
`RTypeRecord` register access records exactly as the dumper constructs them (`op_a` a Write,
`op_b`/`op_c` Reads). All values are canonical ℕ. -/
structure AluEventRec where
  clk : ℕ
  pc : ℕ
  a : ℕ
  b : ℕ
  c : ℕ
  opA : ℕ
  opB : ℕ
  opC : ℕ
  tsA : ℕ
  prevTsA : ℕ
  prevA : ℕ
  tsB : ℕ
  prevTsB : ℕ
  tsC : ℕ
  prevTsC : ℕ

/-- One ALU row's worth of executor data for an `ALUTypeReader` chip (the `ALUTypeRecord` mirror):
as `AluEventRec`, plus `immC` (1 on immediate-`c` rows, where the `op_c` slot has no register read
and `opC` is the immediate value; 0 on register rows, where `opC` is the register index and
`c`/`tsC`/`prevTsC` describe the read). -/
structure AluTypeEventRec where
  clk : ℕ
  pc : ℕ
  a : ℕ
  b : ℕ
  c : ℕ
  opA : ℕ
  opB : ℕ
  opC : ℕ
  immC : ℕ
  tsA : ℕ
  prevTsA : ℕ
  prevA : ℕ
  tsB : ℕ
  prevTsB : ℕ
  tsC : ℕ
  prevTsC : ℕ

/-- As `AluEventRec`, plus the executor `opcode` discriminant (last, matching the `"RTypeOp"`
dumper kind) — the hint-driven chips' anchors build the per-event variant-flag `ProverHint` from
it; the input columns ignore it. -/
structure AluEventOpRec where
  clk : ℕ
  pc : ℕ
  a : ℕ
  b : ℕ
  c : ℕ
  opA : ℕ
  opB : ℕ
  opC : ℕ
  tsA : ℕ
  prevTsA : ℕ
  prevA : ℕ
  tsB : ℕ
  prevTsB : ℕ
  tsC : ℕ
  prevTsC : ℕ
  opcode : ℕ

/-- As `AluTypeEventRec`, plus the executor `opcode` discriminant (last, matching the
`"ALUTypeOp"` dumper kind). -/
structure AluTypeOpEventRec where
  clk : ℕ
  pc : ℕ
  a : ℕ
  b : ℕ
  c : ℕ
  opA : ℕ
  opB : ℕ
  opC : ℕ
  immC : ℕ
  tsA : ℕ
  prevTsA : ℕ
  prevA : ℕ
  tsB : ℕ
  prevTsB : ℕ
  tsC : ℕ
  prevTsC : ℕ
  opcode : ℕ

/-- Forget the opcode (the input columns are opcode-independent; only the hint reads it). -/
def AluEventOpRec.toAluEventRec (e : AluEventOpRec) : AluEventRec :=
  ⟨e.clk, e.pc, e.a, e.b, e.c, e.opA, e.opB, e.opC,
   e.tsA, e.prevTsA, e.prevA, e.tsB, e.prevTsB, e.tsC, e.prevTsC⟩

/-- Forget the opcode (the input columns are opcode-independent; only the hint reads it). -/
def AluTypeOpEventRec.toAluTypeEventRec (e : AluTypeOpEventRec) : AluTypeEventRec :=
  ⟨e.clk, e.pc, e.a, e.b, e.c, e.opA, e.opB, e.opC, e.immC,
   e.tsA, e.prevTsA, e.prevA, e.tsB, e.prevTsB, e.tsC, e.prevTsC⟩

variable {F : Type} [Field F]

/-- A u64 value as its four canonical u16 limbs (little-endian), cast into the field. -/
def u16Limbs4 (x : ℕ) : List F :=
  [x % 65536, (x >>> 16) % 65536, (x >>> 32) % 65536, (x >>> 48) % 65536].map Nat.cast

/-- `RegisterAccessCols` (6 columns): `prev_value` limbs ++ `{prev_low, diff_low_limb}`, per
`RegisterAccessTimestamp::populate_timestamp`. -/
def registerAccessPopulate (value prevTs currTs : ℕ) : List F :=
  let prevLow : ℕ := if prevTs >>> 24 = currTs >>> 24 then prevTs % 16777216 else 0
  let diffLowLimb : ℕ := (currTs % 16777216 - prevLow - 1) % 65536
  u16Limbs4 value ++ [prevLow, diffLowLimb].map Nat.cast

/-- `CPUState` (6 columns): `{clk_high, clk_16_24, clk_0_16}` ++ three pc u16 limbs. -/
def cpuStatePopulate (clk pc : ℕ) : List F :=
  [clk >>> 24, (clk >>> 16) % 256, clk % 65536,
   pc % 65536, (pc >>> 16) % 65536, (pc >>> 32) % 65536].map Nat.cast

/-- `RTypeReader` (22 columns): `op_a` ++ its access block (a Write: `prev_value = prevA`) ++
`op_a_0` ++ `op_b` ++ its access block (a Read: `prev_value = b`) ++ `op_c` ++ its block. -/
def rTypeReaderPopulate (e : AluEventRec) : List F :=
  (e.opA : F) :: registerAccessPopulate e.prevA e.prevTsA e.tsA
    ++ [if e.opA = 0 then (1 : F) else 0, (e.opB : F)]
    ++ registerAccessPopulate e.b e.prevTsB e.tsB
    ++ (e.opC : F) :: registerAccessPopulate e.c e.prevTsC e.tsC

/-- `ALUTypeReader` (26 columns): `op_a` ++ its access block (a Write) ++ `op_a_0` ++ `op_b` ++ its
access block (a Read) ++ the `op_c` Word (`u16Limbs4 opC`) ++ the `op_c` access block (on immediate
rows: `prev_value` copied from the `op_c` Word, both timestamp columns zero) ++ `imm_c`. -/
def aluTypeReaderPopulate (e : AluTypeEventRec) : List F :=
  (e.opA : F) :: registerAccessPopulate e.prevA e.prevTsA e.tsA
    ++ [if e.opA = 0 then (1 : F) else 0, (e.opB : F)]
    ++ registerAccessPopulate e.b e.prevTsB e.tsB
    ++ u16Limbs4 e.opC
    ++ (if e.immC = 1 then u16Limbs4 e.opC ++ [0, 0]
        else registerAccessPopulate e.c e.prevTsC e.tsC)
    ++ [(e.immC : F)]

/-- The full 29-column `Inputs` element list for the `RTypeReader` ALU chips
(Add/Sub/Subw/Mul: `is_real = 1` ++ state ++ adapter), in `ProvableStruct` flattening order. -/
def rTypeEventInputs (e : AluEventRec) : List F :=
  (1 : F) :: (cpuStatePopulate e.clk e.pc ++ rTypeReaderPopulate e)

/-- The full 33-column `Inputs` element list for the `ALUTypeReader` ALU chips
(Addw/Bitwise/Lt: `is_real = 1` ++ state ++ adapter), in `ProvableStruct` flattening order. -/
def aluTypeEventInputs (e : AluTypeEventRec) : List F :=
  (1 : F) :: (cpuStatePopulate e.clk e.pc ++ aluTypeReaderPopulate e)

/-- `rTypeEventInputs` on an opcode-carrying event (the opcode feeds only the hint). -/
def rTypeOpEventInputs (e : AluEventOpRec) : List F :=
  rTypeEventInputs e.toAluEventRec

/-- `aluTypeEventInputs` on an opcode-carrying event (the opcode feeds only the hint). -/
def aluTypeOpEventInputs (e : AluTypeOpEventRec) : List F :=
  aluTypeEventInputs e.toAluTypeEventRec

end SP1Clean.TraceGenTests
