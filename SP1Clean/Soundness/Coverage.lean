import SP1Clean.Soundness.ChipRegistry
import SP1Clean.Model.Opcode

/-! # `Coverage` — the one auditable instruction → chip → Sail table

The single grep-able answer to "which RISC-V instructions does this VM cover, which chip handles each,
and which Sail op does it reach?" It mirrors SP1's two-part structure:

* **`RiscvAir` enum** (`$SP1_DIR/.../riscv/mod.rs`) — the master chip list ↔ our `ChipRegistry.allChipKinds`.
* **`tracing.rs` opcode → event-list dispatch** ↔ our `routeOf`/`routeName` below, keyed on
  `(opcode, rd == x0)` exactly as SP1 routes (ALU ops with `rd == x0` → `AluX0`; loads with
  `rd == x0` → `LoadX0`; otherwise by width).

**Decidable auditing.** Each `ChipKind` carries function fields (no `DecidableEq`), so the audit guards
route through the chip's `name : String` (added in `ChipRow.lean`): `routeName` is a `p`-free `String`
shadow of `routeOf`, over which the covered/uncovered ledger, the partition of the opcode alphabet, and
"routing reaches exactly the wired set" are all `by decide`. The `kind`-level table `coverage` is tied to
the registry by `rfl` (`coverage.map (·.kind) = allChipKinds`).

**Register vs immediate ALU forms.** Routing is keyed on `(opcode, rd == x0)` *only*, exactly as SP1's
`tracing.rs`: the immediate ALU instructions (SLTI/SLTIU, XORI/ORI/ANDI, ADDIW) are **not** separate
`Opcode`s — they share their register opcode (`SLT = 9`, `XOR = 3`, `ADDW = 19`, …) and are distinguished by
the in-row `adapter.imm_c` *column*, not by routing. So `imm_c` is deliberately absent from this table. The
ALU chips each cover **both** forms — the register form (gated on the rs2 read) and the immediate form
(gated on the program-bus decode `op_c_val = sign_extend imm`), so routing covers SLTI/…/ADDIW as well as
their register forms. (`ShiftLeft`/`ShiftRight` model `imm_c` in-circuit; `ADDI` has its own `AddiChip`.) -/

namespace SP1Clean.Soundness

open Sail LeanRV64D LeanRV64D.Functions

-- `Mul` (wired below) carries `Fact (2 ^ 24 < p)`; this table references `MulChip.kind`, so the whole
-- file is stated under the stronger bound with the project-standard `Fact (2 ^ 17 < p)` derived locally.
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]


/-! ## The `rd == x0` routing guard -/

/-- The `op_a == 0` (write-to-`x0`) condition under which a chip claims its opcodes, mirroring SP1's
`tracing.rs`: ALU ops with `rd == x0` route to `AluX0` (not ported) — *not* the ALU chip; loads with
`rd == x0` route to `LoadX0` — *not* the width chip; stores / branches / jumps / U-type ignore `rd`. -/
inductive RdGuard where
  /-- Routes here regardless of `rd` (stores, branches, JAL/JALR, U-type). -/
  | any
  /-- Routes here only when `rd ≠ x0` (the ALU chips and the width load chips). -/
  | nonX0
  /-- Routes here only when `rd == x0` (`LoadX0`). -/
  | onlyX0
  deriving DecidableEq, Repr

/-- Whether the guard fires for a given `rd == x0` bit. -/
def RdGuard.holds : RdGuard → Bool → Bool
  | .any,    _ => true
  | .nonX0,  b => !b
  | .onlyX0, b => b

/-! ## Routing (the `tracing.rs` mirror)

`routeName` is the `p`-free `String` cascade (the decidable shadow); `routeOf` is the same cascade
returning the actual `ChipKind p` (consumed by `Soundness/InstructionTrace.lean`). `routeName_eq` keeps
them in lock-step. -/

/-- The instruction → chip-**name** routing: a `p`-free mirror of SP1's `tracing.rs` opcode dispatch,
keyed on `(opcode, rd == x0)`. `none` = uncovered (DivRem family, system traps). ALU ops with `rd == x0`
route to `AluX0` (the result-discarding fast path), exactly as SP1's `tracing.rs`. -/
def routeName (op : Opcode) (rdIsX0 : Bool) : Option String :=
  match op with
  | .ADD  => if rdIsX0 then some "AluX0" else some "Add"
  | .ADDI => if rdIsX0 then some "AluX0" else some "Addi"
  | .ADDW => if rdIsX0 then some "AluX0" else some "Addw"
  | .SUB  => if rdIsX0 then some "AluX0" else some "Sub"
  | .SUBW => if rdIsX0 then some "AluX0" else some "Subw"
  | .XOR | .OR | .AND => if rdIsX0 then some "AluX0" else some "Bitwise"
  | .SLT | .SLTU => if rdIsX0 then some "AluX0" else some "Lt"
  | .SLL | .SLLW => if rdIsX0 then some "AluX0" else some "ShiftLeft"
  | .SRL | .SRA | .SRLW | .SRAW => if rdIsX0 then some "AluX0" else some "ShiftRight"
  | .MUL | .MULH | .MULHU | .MULHSU | .MULW => if rdIsX0 then some "AluX0" else some "Mul"
  | .DIV | .DIVU | .REM | .REMU | .DIVW | .DIVUW | .REMW | .REMUW =>
      if rdIsX0 then some "AluX0" else some "DivRem"
  | .LB | .LBU => if rdIsX0 then some "LoadX0" else some "LoadByte"
  | .LH | .LHU => if rdIsX0 then some "LoadX0" else some "LoadHalf"
  | .LW | .LWU => if rdIsX0 then some "LoadX0" else some "LoadWord"
  | .LD => if rdIsX0 then some "LoadX0" else some "LoadDouble"
  | .SB => some "StoreByte"
  | .SH => some "StoreHalf"
  | .SW => some "StoreWord"
  | .SD => some "StoreDouble"
  | .BEQ | .BNE | .BLT | .BGE | .BLTU | .BGEU => some "Branch"
  | .JAL => some "Jal"
  | .JALR => some "Jalr"
  | .AUIPC | .LUI => some "UType"
  | _ => none

/-- The instruction → `ChipKind` routing — the same cascade as `routeName`, returning the wired chip's
`kind`. This is what `Soundness/InstructionTrace.lean` turns instructions into `ChipRow`s with. -/
def routeOf (op : Opcode) (rdIsX0 : Bool) : Option (ChipKind p) :=
  match op with
  | .ADD  => if rdIsX0 then some AluX0Chip.kind else some AddChip.kind
  | .ADDI => if rdIsX0 then some AluX0Chip.kind else some AddiChip.kind
  | .ADDW => if rdIsX0 then some AluX0Chip.kind else some AddwChip.kind
  | .SUB  => if rdIsX0 then some AluX0Chip.kind else some SubChip.kind
  | .SUBW => if rdIsX0 then some AluX0Chip.kind else some SubwChip.kind
  | .XOR | .OR | .AND => if rdIsX0 then some AluX0Chip.kind else some BitwiseChip.kind
  | .SLT | .SLTU => if rdIsX0 then some AluX0Chip.kind else some LtChip.kind
  | .SLL | .SLLW => if rdIsX0 then some AluX0Chip.kind else some ShiftLeftChip.kind
  | .SRL | .SRA | .SRLW | .SRAW => if rdIsX0 then some AluX0Chip.kind else some ShiftRightChip.kind
  | .MUL | .MULH | .MULHU | .MULHSU | .MULW => if rdIsX0 then some AluX0Chip.kind else some MulChip.kind
  | .DIV | .DIVU | .REM | .REMU | .DIVW | .DIVUW | .REMW | .REMUW =>
      if rdIsX0 then some AluX0Chip.kind else some DivRemChip.kind
  | .LB | .LBU => if rdIsX0 then some LoadX0Chip.kind else some LoadByteChip.kind
  | .LH | .LHU => if rdIsX0 then some LoadX0Chip.kind else some LoadHalfChip.kind
  | .LW | .LWU => if rdIsX0 then some LoadX0Chip.kind else some LoadWordChip.kind
  | .LD => if rdIsX0 then some LoadX0Chip.kind else some LoadDoubleChip.kind
  | .SB => some StoreByteChip.kind
  | .SH => some StoreHalfChip.kind
  | .SW => some StoreWordChip.kind
  | .SD => some StoreDoubleChip.kind
  | .BEQ | .BNE | .BLT | .BGE | .BLTU | .BGEU => some BranchChip.kind
  | .JAL => some JalChip.kind
  | .JALR => some JalrChip.kind
  | .AUIPC | .LUI => some UTypeChip.kind
  | _ => none

/-- `routeOf` and its `String` shadow agree: `routeName = (routeOf …).map (·.name)`. Keeps the decidable
audits below (stated on `routeName`) honest about the real `kind`-level routing. -/
theorem routeName_eq (op : Opcode) (rdIsX0 : Bool) :
    routeName op rdIsX0 = ((routeOf (p := p) op rdIsX0).map (·.name)) := by
  cases op <;> cases rdIsX0 <;> rfl

/-! ## The covered / uncovered ledger (over the full `Opcode` alphabet) -/

/-- The opcodes this VM covers — those `routeName` sends to a wired chip for some `rd`. -/
def coveredOpcodes : List Opcode :=
  [.ADD, .ADDI, .ADDW, .SUB, .SUBW, .XOR, .OR, .AND, .SLT, .SLTU,
   .SLL, .SLLW, .SRL, .SRA, .SRLW, .SRAW, .MUL, .MULH, .MULHU, .MULHSU, .MULW,
   .LB, .LH, .LW, .LBU, .LHU, .LWU, .LD, .SB, .SH, .SW, .SD,
   .BEQ, .BNE, .BLT, .BGE, .BLTU, .BGEU, .JAL, .JALR, .AUIPC, .LUI,
   .DIV, .DIVU, .REM, .REMU, .DIVW, .DIVUW, .REMW, .REMUW]

/-- The opcodes not covered: only the system traps (`ECALL/EBREAK/UNIMP`). The DivRem family routes to
`DivRem` for `rd ≠ x0` and `AluX0` for `rd = x0`; ALU ops with `rd = x0` route to `AluX0`. -/
def uncoveredOpcodes : List Opcode :=
  [.ECALL, .EBREAK, .UNIMP]

theorem coveredOpcodes_length : coveredOpcodes.length = 50 := rfl
theorem uncoveredOpcodes_length : uncoveredOpcodes.length = 3 := rfl

/-- The ledger **partitions** the opcode alphabet: every opcode is covered or uncovered… -/
theorem opcode_classified : ∀ op ∈ Opcode.all, op ∈ coveredOpcodes ∨ op ∈ uncoveredOpcodes := by decide

/-- …and never both. -/
theorem opcode_class_disjoint :
    ∀ op ∈ Opcode.all, ¬ (op ∈ coveredOpcodes ∧ op ∈ uncoveredOpcodes) := by decide

/-- The ledger is exactly the routing: covered ⟺ routes somewhere. -/
theorem covered_iff_routed : ∀ op ∈ Opcode.all,
    (op ∈ coveredOpcodes ↔ ((routeName op false).isSome ∨ (routeName op true).isSome)) := by decide

/-- Uncovered ⟺ routes nowhere (for either `rd`). -/
theorem uncovered_iff_unrouted : ∀ op ∈ Opcode.all,
    (op ∈ uncoveredOpcodes ↔ ((routeName op false).isNone ∧ (routeName op true).isNone)) := by decide

/-! ## Routing reaches exactly the wired chip set -/

/-- The 25 wired chip names, in `allChipKinds` order. -/
def wiredNames : List String :=
  ["Add", "Addi", "Addw", "Sub", "Subw", "Bitwise", "Lt", "ShiftLeft", "ShiftRight",
   "Jal", "Jalr", "Branch", "UType",
   "LoadByte", "LoadHalf", "LoadWord", "LoadDouble", "LoadX0",
   "StoreByte", "StoreHalf", "StoreWord", "StoreDouble", "Mul", "DivRem", "AluX0"]

/-- Every chip name `routeName` can produce (with duplicates; membership is all the audits below need). -/
def reachableNames : List String :=
  Opcode.all.filterMap (fun op => routeName op false) ++
  Opcode.all.filterMap (fun op => routeName op true)

/-- Routing never reaches a non-wired chip… -/
theorem reachable_subset_wired : ∀ nm ∈ reachableNames, nm ∈ wiredNames := by decide

/-- …and every wired chip is reached by some instruction (no dead-wired chip). -/
theorem wired_subset_reachable : ∀ nm ∈ wiredNames, nm ∈ reachableNames := by decide

/-- The wired names are exactly the registry's `name`s — ties the audit's `String` layer to the real
`allChipKinds` (whose `ChipKind`s have no `DecidableEq`). -/
theorem wiredNames_eq_registry : (allChipKinds (p := p)).map (·.name) = wiredNames := rfl

/-! ## The `kind`-level coverage table (the human-readable census) -/

/-- One row of the coverage census: a wired chip, the opcodes routed to it, and its `rd`-guard. -/
structure CoverageEntry (p : ℕ) [Fact p.Prime] [Fact (2 ^ 17 < p)] where
  kind : ChipKind p
  opcodes : List Opcode
  rdGuard : RdGuard

/-- **The coverage table** — one entry per wired chip, in `allChipKinds` order, mirroring SP1's
`tracing.rs` routing arms. Read top-to-bottom this *is* the instruction-coverage census. -/
def coverage : List (CoverageEntry p) :=
  [ ⟨AddChip.kind,        [.ADD],                       .nonX0⟩,
    ⟨AddiChip.kind,       [.ADDI],                      .nonX0⟩,
    ⟨AddwChip.kind,       [.ADDW],                      .nonX0⟩,
    ⟨SubChip.kind,        [.SUB],                       .nonX0⟩,
    ⟨SubwChip.kind,       [.SUBW],                      .nonX0⟩,
    ⟨BitwiseChip.kind,    [.XOR, .OR, .AND],            .nonX0⟩,
    ⟨LtChip.kind,         [.SLT, .SLTU],                .nonX0⟩,
    ⟨ShiftLeftChip.kind,  [.SLL, .SLLW],                .nonX0⟩,
    ⟨ShiftRightChip.kind, [.SRL, .SRA, .SRLW, .SRAW],   .nonX0⟩,
    ⟨JalChip.kind,        [.JAL],                       .any⟩,
    ⟨JalrChip.kind,       [.JALR],                      .any⟩,
    ⟨BranchChip.kind,     [.BEQ, .BNE, .BLT, .BGE, .BLTU, .BGEU], .any⟩,
    ⟨UTypeChip.kind,      [.AUIPC, .LUI],               .any⟩,
    ⟨LoadByteChip.kind,   [.LB, .LBU],                  .nonX0⟩,
    ⟨LoadHalfChip.kind,   [.LH, .LHU],                  .nonX0⟩,
    ⟨LoadWordChip.kind,   [.LW, .LWU],                  .nonX0⟩,
    ⟨LoadDoubleChip.kind, [.LD],                        .nonX0⟩,
    ⟨LoadX0Chip.kind,     [.LB, .LBU, .LH, .LHU, .LW, .LWU, .LD], .onlyX0⟩,
    ⟨StoreByteChip.kind,  [.SB],                        .any⟩,
    ⟨StoreHalfChip.kind,  [.SH],                        .any⟩,
    ⟨StoreWordChip.kind,  [.SW],                        .any⟩,
    ⟨StoreDoubleChip.kind,[.SD],                        .any⟩,
    ⟨MulChip.kind,        [.MUL, .MULH, .MULHU, .MULHSU, .MULW], .nonX0⟩,
    ⟨DivRemChip.kind,     [.DIV, .DIVU, .REM, .REMU, .DIVW, .DIVUW, .REMW, .REMUW], .nonX0⟩,
    ⟨AluX0Chip.kind,      [.ADD, .ADDI, .ADDW, .SUB, .SUBW, .XOR, .OR, .AND, .SLT, .SLTU,
                           .SLL, .SLLW, .SRL, .SRA, .SRLW, .SRAW,
                           .MUL, .MULH, .MULHU, .MULHSU, .MULW,
                           .DIV, .DIVU, .REM, .REMU, .DIVW, .DIVUW, .REMW, .REMUW], .onlyX0⟩ ]

/-- The census' chips are **exactly** the registry, in order (`ChipKind` has no `DecidableEq`, but the
two lists are the same terms, so this is `rfl`). -/
theorem coverage_kinds_eq_registry : (coverage (p := p)).map (·.kind) = allChipKinds := rfl

theorem coverage_length : (coverage (p := p)).length = 25 := rfl

/-- The census' names match the wired-name list. -/
theorem coverage_names : (coverage (p := p)).map (fun e => e.kind.name) = wiredNames := rfl

/-- The per-chip opcode census, read straight off the table. -/
theorem coverage_opcodes :
    (coverage (p := p)).map (·.opcodes) =
      [[.ADD], [.ADDI], [.ADDW], [.SUB], [.SUBW], [.XOR, .OR, .AND], [.SLT, .SLTU],
       [.SLL, .SLLW], [.SRL, .SRA, .SRLW, .SRAW], [.JAL], [.JALR],
       [.BEQ, .BNE, .BLT, .BGE, .BLTU, .BGEU], [.AUIPC, .LUI],
       [.LB, .LBU], [.LH, .LHU], [.LW, .LWU], [.LD],
       [.LB, .LBU, .LH, .LHU, .LW, .LWU, .LD],
       [.SB], [.SH], [.SW], [.SD],
       [.MUL, .MULH, .MULHU, .MULHSU, .MULW],
       [.DIV, .DIVU, .REM, .REMU, .DIVW, .DIVUW, .REMW, .REMUW],
       [.ADD, .ADDI, .ADDW, .SUB, .SUBW, .XOR, .OR, .AND, .SLT, .SLTU,
        .SLL, .SLLW, .SRL, .SRA, .SRLW, .SRAW,
        .MUL, .MULH, .MULHU, .MULHSU, .MULW,
        .DIV, .DIVU, .REM, .REMU, .DIVW, .DIVUW, .REMW, .REMUW]] := rfl

/-! ## Worked routing examples (the readable mapping) -/

example : routeName .ADD false = some "Add" := rfl
example : routeName .ADD true  = some "AluX0" := rfl      -- ALU into x0 → AluX0 (result discarded)
example : routeName .XOR false = some "Bitwise" := rfl
example : routeName .SRAW false = some "ShiftRight" := rfl
example : routeName .LD false = some "LoadDouble" := rfl
example : routeName .LD true  = some "LoadX0" := rfl       -- any load into x0 → LoadX0
example : routeName .LB true  = some "LoadX0" := rfl
example : routeName .SB true  = some "StoreByte" := rfl    -- stores ignore rd
example : routeName .BEQ false = some "Branch" := rfl
example : routeName .JALR false = some "Jalr" := rfl
example : routeName .LUI false = some "UType" := rfl
example : routeName .MUL false = some "Mul" := rfl
example : routeName .MUL true  = some "AluX0" := rfl       -- ALU into x0 → AluX0 (result discarded)
example : routeName .MULHSU false = some "Mul" := rfl
example : routeName .DIV false = some "DivRem" := rfl      -- DIV/REM family → DivRem (rd ≠ x0)
example : routeName .DIV true  = some "AluX0" := rfl        -- DIV/REM into x0 → AluX0
example : routeName .REMUW false = some "DivRem" := rfl
example : routeName .ECALL false = none := rfl

end SP1Clean.Soundness
