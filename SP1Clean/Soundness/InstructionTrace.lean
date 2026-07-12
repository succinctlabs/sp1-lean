import SP1Clean.Soundness.Coverage

/-! # `InstructionTrace` — the instruction sequence → circuit (ChipRow) sequence mapping

> **FROZEN (consolidation step 0, 2026-07-09).** Legacy soundness path — scheduled for deletion at the cutover (proposal §5.6). Do NOT add new lemmas against this module; new soundness work targets the timed-grounding engine (proposal §3.2).

The Lean analog of SP1's `ExecutionRecord` → `generate_trace`: a decoded instruction sequence maps,
opcode-by-opcode, to the heterogeneous trace of `ChipRow`s the soundness capstone consumes. SP1 routes
each executed instruction to one chip's event list (`tracing.rs`) and that chip emits one row
(`generate_trace`); here `routeOf` (`Soundness/Coverage.lean`) is that routing, and a valid trace is one
whose rows stand in the `Emits` relation to the program — row `i` is a real row of the chip instruction
`i` routes to, committing instruction `i`'s opcode.

We do **not** reconstruct each chip's witness columns generically (that *is* the prover's
`generate_trace`, deferred); instead we pin down precisely *which* `ChipRow` a given instruction must
produce (`Emits` / `EmitsProgram`), which is exactly what the partial-completeness statement in
`Soundness/Completeness.lean` quantifies over. The name-level map `programChipNames` is the readable
"this instruction sequence → this chip sequence" census. -/

namespace SP1Clean.Soundness

-- `routeOf` references `MulChip.kind`, which carries `Fact (2 ^ 24 < p)`; this file is stated under the
-- stronger bound with the project-standard `Fact (2 ^ 17 < p)` derived locally.
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]


/-! ## The decoded instruction -/

/-- A decoded RISC-V instruction — the Lean shadow of SP1's `Instruction` (opcode + operand registers
`op_a = rd`, `op_b = rs1`, `op_c = rs2`, an immediate, and the program counter). Enough to drive the
`(opcode, rd == x0)` routing and to key a row to its instruction. -/
structure Instruction where
  opcode : Opcode
  /-- `op_a` — the destination register `rd` (or `rs2` for stores/branches). -/
  op_a : ℕ
  /-- `op_b` — the first source register `rs1`. -/
  op_b : ℕ
  /-- `op_c` — the second source register `rs2`. -/
  op_c : ℕ
  /-- The instruction immediate. -/
  imm : ℕ
  /-- The program counter of this instruction. -/
  pc : ℕ
  deriving Repr, DecidableEq, Inhabited

/-- SP1's `op_a_0 = instruction.op_a == 0` — the `rd == x0` bit the load/ALU routing keys on. -/
def Instruction.rdIsX0 (i : Instruction) : Bool := i.op_a == 0

/-! ## Routing an instruction -/

/-- The chip an instruction routes to (`none` = uncovered) — `routeOf` on its `(opcode, rd == x0)`. -/
def Instruction.chipKind (i : Instruction) : Option (ChipKind p) := routeOf i.opcode i.rdIsX0

/-- The chip **name** an instruction routes to — the readable, `p`-free shadow. -/
def Instruction.chipName (i : Instruction) : Option String := routeName i.opcode i.rdIsX0

/-- **The instruction sequence → chip sequence census** (name level): the readable direct mapping from a
program to the chips its instructions exercise. `none` entries are uncovered instructions. -/
def programChipNames (prog : List Instruction) : List (Option String) :=
  prog.map Instruction.chipName

/-! ## When a `ChipRow` realizes an instruction -/

/-- `Emits i r` — the row `r` is *the* circuit row instruction `i` must produce: it belongs to the chip
`i` routes to, is a **real** row (`is_real = 1`), and commits `i`'s opcode on the Program bus
(`Opcode.toNat`). This is the per-row obligation a faithful `generate_trace` discharges, and the per-row
target of the partial-completeness statement. -/
def Emits (i : Instruction) (r : ChipRow p) : Prop :=
  routeOf i.opcode i.rdIsX0 = some r.kind ∧
  r.is_real = 1 ∧
  r.view.opcode = (i.opcode.toNat : ZMod p)

/-- **The instruction sequence → row sequence relation**: pointwise `Emits`, so `rows` is a valid
circuit trace for `prog` (one row per instruction, in order, each realizing its instruction). The capstone
then maps `rows.map ChipRow.view` through the bus machinery. -/
def EmitsProgram (prog : List Instruction) (rows : List (ChipRow p)) : Prop :=
  List.Forall₂ Emits prog rows

/-- An `Emits` row is dispatched to the chip the instruction routes to (the projection the capstone's
target-execution step `r.kind.advance` keys on). -/
theorem Emits.routes {i : Instruction} {r : ChipRow p} (h : Emits i r) :
    routeOf i.opcode i.rdIsX0 = some r.kind := h.1

/-- An `Emits` row is real, so its chip `Spec`'s gated identity and Sail bridge both fire. -/
theorem Emits.is_real {i : Instruction} {r : ChipRow p} (h : Emits i r) : r.is_real = 1 := h.2.1

/-! ## A worked demonstrator (the readable mapping)

A six-instruction program exercising a covered ALU op, a width load, the same load into `x0`, a branch,
a multiply (newly covered), and an uncovered divide — and the exact chip sequence it maps to. -/

/-- `add x1,x2,x3 ; ld x5,8(x6) ; ld x0,8(x6) ; beq x1,x2,16 ; mul x1,x2,x3 ; div x1,x2,x3`. -/
def demoProgram : List Instruction :=
  [⟨.ADD, 1, 2, 3, 0, 0⟩,
   ⟨.LD,  5, 6, 0, 8, 4⟩,
   ⟨.LD,  0, 6, 0, 8, 8⟩,
   ⟨.BEQ, 0, 1, 2, 16, 12⟩,
   ⟨.MUL, 1, 2, 3, 0, 16⟩,
   ⟨.DIV, 1, 2, 3, 0, 20⟩]

/-- The demonstrator maps to: Add, LoadDouble, LoadX0 (the `rd == x0` load), Branch, Mul, and DivRem (the
divide into `rd ≠ x0`). Reads as "instruction sequence → circuit sequence." -/
example : programChipNames demoProgram =
    [some "Add", some "LoadDouble", some "LoadX0", some "Branch", some "Mul", some "DivRem"] := rfl

/-- ALU into `x0` routes to `AluX0` (the result-discarding fast path), mirroring loads-into-`x0` → `LoadX0`:
`add x0,x2,x3` and `mul x0,x2,x3` both route to `AluX0`, while their `rd ≠ x0` siblings route to Add/Mul. -/
example : programChipNames
    [⟨.ADD, 0, 2, 3, 0, 0⟩, ⟨.ADD, 1, 2, 3, 0, 4⟩, ⟨.MUL, 0, 2, 3, 0, 8⟩] =
    [some "AluX0", some "Add", some "AluX0"] := rfl

end SP1Clean.Soundness
