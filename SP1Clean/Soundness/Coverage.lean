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
route through the chip's `name : String` (added in `ChipRow.lean`): `routeName` is the `String`
projection of `routeOf`, over which the covered/uncovered ledger, the partition of the opcode alphabet, and
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


/-! ## Routing (the `tracing.rs` mirror)

Both functions search the one `SupportedMachine.supportedChips` descriptor: `routeName` projects its
human-readable name and `routeOf` its actual `ChipKind p`. -/

/-- The instruction → chip-**name** routing: the decidable projection of SP1's `tracing.rs` opcode dispatch,
keyed on `(opcode, rd == x0)`. `none` = uncovered (the system traps ECALL/EBREAK/UNIMP only — the
DivRem family routes). ALU ops with `rd == x0`
route to `AluX0` (the result-discarding fast path), exactly as SP1's `tracing.rs`. -/
def routeName (op : Opcode) (rdIsX0 : Bool) : Option String :=
  (routeChip (p := p) op rdIsX0).map (·.kind.name)

/-- The instruction → `ChipKind` routing — the same descriptor search as `routeName`, returning the wired chip's
`kind`. The witness decoder and timed grounding layer consume this routing identity. -/
def routeOf (op : Opcode) (rdIsX0 : Bool) : Option (ChipKind p) :=
  (routeChip (p := p) op rdIsX0).map (·.kind)

/-- `routeOf` and its `String` shadow agree: `routeName = (routeOf …).map (·.name)`. Keeps the decidable
audits below (stated on `routeName`) honest about the real `kind`-level routing. -/
theorem routeName_eq (op : Opcode) (rdIsX0 : Bool) :
    routeName (p := p) op rdIsX0 = ((routeOf (p := p) op rdIsX0).map (·.name)) := by
  unfold routeName routeOf
  cases routeChip (p := p) op rdIsX0 <;> rfl

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
    (op ∈ coveredOpcodes ↔
      ((routeName (p := p) op false).isSome ∨ (routeName (p := p) op true).isSome)) := by
  intro op _
  cases op <;>
    simp [coveredOpcodes, routeName, routeChip, supportedChips, SupportedChip.claims, RdGuard.holds]

/-- Uncovered ⟺ routes nowhere (for either `rd`). -/
theorem uncovered_iff_unrouted : ∀ op ∈ Opcode.all,
    (op ∈ uncoveredOpcodes ↔
      ((routeName (p := p) op false).isNone ∧ (routeName (p := p) op true).isNone)) := by
  intro op _
  cases op <;>
    simp [uncoveredOpcodes, routeName, routeChip, supportedChips, SupportedChip.claims, RdGuard.holds]

/-! ## Routing reaches exactly the wired chip set -/

/-- The 25 wired chip names, in `allChipKinds` order. -/
def wiredNames : List String :=
  (supportedChips (p := p)).map (·.kind.name)

/-- Every chip name `routeName` can produce (with duplicates; membership is all the audits below need). -/
def reachableNames : List String :=
  Opcode.all.filterMap (fun op => routeName (p := p) op false) ++
  Opcode.all.filterMap (fun op => routeName (p := p) op true)

/-- A small routing witness for every wired instruction chip, in descriptor order.  Keeping this
separate from the full opcode cross-product makes the no-dead-chip proof structural rather than a
large kernel reduction over the circuit-bearing `supportedChips` records. -/
def routingWitnesses : List (Opcode × Bool) :=
  [(.ADD, false), (.ADDI, false), (.ADDW, false), (.SUB, false), (.SUBW, false),
   (.XOR, false), (.SLT, false), (.SLL, false), (.SRL, false), (.JAL, false),
   (.JALR, false), (.BEQ, false), (.AUIPC, false), (.LB, false), (.LH, false),
   (.LW, false), (.LD, false), (.LB, true), (.SB, false), (.SH, false), (.SW, false),
   (.SD, false), (.MUL, false), (.DIV, false), (.ADD, true)]

theorem routingWitnesses_valid :
    ∀ witness ∈ routingWitnesses, witness.1 ∈ Opcode.all := by decide

theorem routingWitnessNames_eq_wired :
    routingWitnesses.filterMap (fun witness =>
      routeName (p := p) witness.1 witness.2) = wiredNames (p := p) := rfl

private theorem routeName_mem_wired {op : Opcode} {rdIsX0 : Bool} {nm : String}
    (h : routeName (p := p) op rdIsX0 = some nm) : nm ∈ wiredNames (p := p) := by
  unfold routeName at h
  obtain ⟨chip, hchip, rfl⟩ := Option.map_eq_some_iff.mp h
  simp only [wiredNames, List.mem_map]
  exact ⟨chip, List.mem_of_find?_eq_some hchip, rfl⟩

/-- Routing never reaches a non-wired chip… -/
theorem reachable_subset_wired :
    ∀ nm ∈ reachableNames (p := p), nm ∈ wiredNames (p := p) := by
  intro nm h
  simp only [reachableNames, List.mem_append, List.mem_filterMap] at h
  obtain ⟨op, _, hop⟩ | ⟨op, _, hop⟩ := h
  · exact routeName_mem_wired hop
  · exact routeName_mem_wired hop

/-- …and every wired chip is reached by some instruction (no dead-wired chip). -/
theorem wired_subset_reachable :
    ∀ nm ∈ wiredNames (p := p), nm ∈ reachableNames (p := p) := by
  intro nm h
  rw [← routingWitnessNames_eq_wired] at h
  obtain ⟨⟨op, rdIsX0⟩, hwitness, hroute⟩ := List.mem_filterMap.mp h
  have hopcode : op ∈ Opcode.all := routingWitnesses_valid (op, rdIsX0) hwitness
  simp only [reachableNames, List.mem_append, List.mem_filterMap]
  cases rdIsX0
  · exact Or.inl ⟨op, hopcode, hroute⟩
  · exact Or.inr ⟨op, hopcode, hroute⟩

/-- The wired names are exactly the registry's `name`s — ties the audit's `String` layer to the real
`allChipKinds` (whose `ChipKind`s have no `DecidableEq`). -/
theorem wiredNames_eq_registry :
    (allChipKinds (p := p)).map (·.name) = wiredNames (p := p) := rfl

/-! ## The `kind`-level coverage table (the human-readable census) -/

/-- Compatibility name for one row of the now-unified supported-machine descriptor. -/
abbrev CoverageEntry := SupportedChip

/-- **The coverage table** — one entry per wired chip, in `allChipKinds` order, mirroring SP1's
`tracing.rs` routing arms. Read top-to-bottom this *is* the instruction-coverage census. -/
def coverage : List (CoverageEntry p) :=
  supportedChips (p := p)

/-- The census' chips are **exactly** the registry, in order (`ChipKind` has no `DecidableEq`, but the
two lists are the same terms, so this is `rfl`). -/
theorem coverage_kinds_eq_registry :
    (coverage (p := p)).map (·.kind) = allChipKinds (p := p) := rfl

theorem coverage_length : (coverage (p := p)).length = 25 := rfl

/-- The census' names match the wired-name list. -/
theorem coverage_names :
    (coverage (p := p)).map (fun e => e.kind.name) = wiredNames (p := p) := rfl

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

example : routeName (p := p) .ADD false = some "Add" := rfl
example : routeName (p := p) .ADD true = some "AluX0" := rfl -- ALU into x0 → AluX0
example : routeName (p := p) .XOR false = some "Bitwise" := rfl
example : routeName (p := p) .SRAW false = some "ShiftRight" := rfl
example : routeName (p := p) .LD false = some "LoadDouble" := rfl
example : routeName (p := p) .LD true = some "LoadX0" := rfl -- any load into x0 → LoadX0
example : routeName (p := p) .LB true = some "LoadX0" := rfl
example : routeName (p := p) .SB true = some "StoreByte" := rfl -- stores ignore rd
example : routeName (p := p) .BEQ false = some "Branch" := rfl
example : routeName (p := p) .JALR false = some "Jalr" := rfl
example : routeName (p := p) .LUI false = some "UType" := rfl
example : routeName (p := p) .MUL false = some "Mul" := rfl
example : routeName (p := p) .MUL true = some "AluX0" := rfl -- ALU into x0 → AluX0
example : routeName (p := p) .MULHSU false = some "Mul" := rfl
example : routeName (p := p) .DIV false = some "DivRem" := rfl -- DIV/REM family → DivRem
example : routeName (p := p) .DIV true = some "AluX0" := rfl -- DIV/REM into x0 → AluX0
example : routeName (p := p) .REMUW false = some "DivRem" := rfl
example : routeName (p := p) .ECALL false = none := rfl

end SP1Clean.Soundness
