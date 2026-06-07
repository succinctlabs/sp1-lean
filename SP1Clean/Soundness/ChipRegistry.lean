import SP1Clean.Soundness.ChipRow
import SP1Clean.Chips.AddChip.Bridge
import SP1Clean.Chips.AddiChip.Bridge
import SP1Clean.Chips.AddwChip.Bridge
import SP1Clean.Chips.SubChip.Bridge
import SP1Clean.Chips.SubwChip.Bridge
import SP1Clean.Chips.BitwiseChip.Bridge
import SP1Clean.Chips.LtChip.Bridge
import SP1Clean.Chips.ShiftLeftChip.Bridge
import SP1Clean.Chips.ShiftRightChip.Bridge
import SP1Clean.Chips.JalChip.Bridge
import SP1Clean.Chips.JalrChip.Bridge
import SP1Clean.Chips.BranchChip.Bridge
import SP1Clean.Chips.UTypeChip.Bridge
import SP1Clean.Chips.LoadByteChip.Bridge
import SP1Clean.Chips.LoadHalfChip.Bridge
import SP1Clean.Chips.LoadWordChip.Bridge
import SP1Clean.Chips.LoadDoubleChip.Bridge
import SP1Clean.Chips.LoadX0Chip.Bridge
import SP1Clean.Chips.StoreByteChip.Bridge
import SP1Clean.Chips.StoreHalfChip.Bridge
import SP1Clean.Chips.StoreWordChip.Bridge
import SP1Clean.Chips.StoreDoubleChip.Bridge
import SP1Clean.Chips.MulChip.Bridge
import SP1Clean.Chips.DivRemChip.Bridge
import SP1Clean.Chips.AluX0Chip.Bridge

/-! # `ChipRegistry` — the auditable list of every capstone-wired chip

A single bottom-level hub gathering every chip that has a capstone-integration `Soundness.ChipKind`
(defined next to its Sail bridge in `Chips/<Op>Chip/Bridge.lean`). `ChipKind p` is one type — the
per-chip heterogeneity (its `Inputs`/`Cols` `TypeMap`s) lives *inside* each value — so `List (ChipKind p)`
type-checks and `allChipKinds` is the one grep-able enumeration of the wired set.

This file is an enumeration / re-export hub, **not** a dispatch mechanism: the capstone never iterates
`allChipKinds`; it dispatches each row generically via `r.kind.reaches_sail`. The registry exists for
**auditability** — one entry ⇔ one wired chip — and gives a single import that pulls in every `kind`.

The instruction → chip → Sail **routing/identity** home is `Soundness/Coverage.lean` (the `Opcode` →
`ChipKind` table mirroring SP1's `tracing.rs`); it is tied back to this registry by
`coverage_kinds_eq_registry : coverage.map (·.kind) = allChipKinds`.

## Wired (25)

* **ALU / R-type:** Add, Addi, Addw, Sub, Subw, Bitwise (AND/OR/XOR), Lt (SLT/SLTU),
  ShiftLeft (SLL/SLLW), ShiftRight (SRL/SRA/SRLW/SRAW), Mul (MUL/MULH/MULHU/MULHSU/MULW), UType (LUI/AUIPC),
  DivRem (DIV/DIVU/REM/REMU/DIVW/REMW/DIVUW/REMUW),
  AluX0 (any covered ALU op — now incl. the DIV/REM family — with `rd = x0`, result discarded).
* **Control flow:** Jal, Jalr, Branch (BEQ/BNE/BLT/BGE/BLTU/BGEU).
* **Memory:** LoadByte, LoadHalf, LoadWord, LoadDouble, LoadX0 (loads into `x0`), StoreByte, StoreHalf,
  StoreWord, StoreDouble.

`Mul` carries the stronger `Fact (2 ^ 24 < p)` field bound (the `MulOperation` column-sum bound), so this
registry and everything downstream (`sp1Tables`, the capstone, `Coverage`) are stated under
`[Fact (2 ^ 24 < p)]` with a local `Fact (2 ^ 17 < p)` derived from it; KoalaBear (p ≈ 2³¹) satisfies it.

`DivRem` is now wired (its soundness landed, axiom-clean); only its `completeness` stays `sorry`. -/

namespace SP1Clean.Soundness

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- Every chip with a capstone-integration `ChipKind`. **Auditable:** one entry ⇔ one wired chip; to wire a
new chip, define its `kind` in its `Bridge.lean` and add it here. (Not a dispatch table — the capstone
dispatches generically per row; this is the enumeration the all-chips trace draws from.) -/
def allChipKinds : List (ChipKind p) :=
  [ AddChip.kind, AddiChip.kind, AddwChip.kind, SubChip.kind, SubwChip.kind,
    BitwiseChip.kind, LtChip.kind, ShiftLeftChip.kind, ShiftRightChip.kind,
    JalChip.kind, JalrChip.kind, BranchChip.kind, UTypeChip.kind,
    LoadByteChip.kind, LoadHalfChip.kind, LoadWordChip.kind, LoadDoubleChip.kind, LoadX0Chip.kind,
    StoreByteChip.kind, StoreHalfChip.kind, StoreWordChip.kind, StoreDoubleChip.kind,
    MulChip.kind, DivRemChip.kind, AluX0Chip.kind ]

/-- Regression guard: the wired-chip count is exactly 25. If a `kind` is added to / removed from
`allChipKinds` without updating this, the `rfl` breaks — keeping the audit count honest. -/
theorem allChipKinds_length : (allChipKinds (p := p)).length = 25 := rfl

end SP1Clean.Soundness
