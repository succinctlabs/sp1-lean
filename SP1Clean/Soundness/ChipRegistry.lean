import SP1Clean.Soundness.SupportedMachine

/-! # `ChipRegistry` — the auditable list of every capstone-wired chip

A projection of `SupportedMachine.supportedChips`, gathering every chip that has a capstone-integration `Soundness.ChipKind`
(defined next to its Sail bridge in `Chips/<Op>Chip/Bridge.lean`). `ChipKind p` is one type — the
per-chip heterogeneity (its `Inputs`/`Cols` `TypeMap`s) lives *inside* each value — so `List (ChipKind p)`
type-checks and `allChipKinds` is the semantic projection of the one grep-able realization map.

This file is a compatibility projection / re-export hub, **not** a dispatch mechanism: the capstone dispatches each
row generically via `r.kind.advance`. The registry exists for **auditability** — one entry ⇔ one
wired chip — and gives a single import that pulls in every `kind`.

The instruction → chip → Sail **routing/identity** home is `Soundness/Coverage.lean` (the `Opcode` →
`ChipKind` table mirroring SP1's `tracing.rs`); both are derived from `supportedChips`, with
`coverage_kinds_eq_registry : coverage.map (·.kind) = allChipKinds`.

## Wired (25)

* **ALU / R-type:** Add, Addi, Addw, Sub, Subw, Bitwise (AND/OR/XOR), Lt (SLT/SLTU),
  ShiftLeft (SLL/SLLW), ShiftRight (SRL/SRA/SRLW/SRAW), Mul (MUL/MULH/MULHU/MULHSU/MULW), UType (LUI/AUIPC),
  DivRem (DIV/DIVU/REM/REMU/DIVW/REMW/DIVUW/REMUW),
  AluX0 (any covered ALU op — incl. the DIV/REM family — with `rd = x0`, result discarded).
* **Control flow:** Jal, Jalr, Branch (BEQ/BNE/BLT/BGE/BLTU/BGEU).
* **Memory:** LoadByte, LoadHalf, LoadWord, LoadDouble, LoadX0 (loads into `x0`), StoreByte, StoreHalf,
  StoreWord, StoreDouble.

`Mul` carries the stronger `Fact (2 ^ 24 < p)` field bound (the `MulOperation` column-sum bound), so this
registry and everything downstream (`sp1Tables`, the capstone, `Coverage`) are stated under
`[Fact (2 ^ 24 < p)]` with a local `Fact (2 ^ 17 < p)` derived from it; KoalaBear (p ≈ 2³¹) satisfies it.

Every chip's `circuit` is axiom-clean in both directions (soundness and completeness): the census in
`docs/snapshots/axiom-ledger.md` and the zero-deferral gate in `scripts/run_audit.sh` certify no
`sorryAx` anywhere in the released set. -/

namespace SP1Clean.Soundness

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]


/-- Every chip with a capstone-integration `ChipKind`. To wire a new chip, extend the neutral
`InstructionChipId` enumeration, define its Sail-adjacent `kind`, and add the corresponding
`supportedChipFor` case; do not add another independent list here. -/
def allChipKinds : List (ChipKind p) :=
  (supportedChips (p := p)).map (·.kind)

/-- Regression guard: the wired-chip count is inherited from the complete neutral identity list. -/
theorem allChipKinds_length : (allChipKinds (p := p)).length = 25 := by
  simpa [allChipKinds] using supportedChips_length (p := p)

/-- **Full advance coverage (SC Phase 4, complete).** Every registered chip carries a populated
`advance` field (`isSome`) — the 25/25 milestone: MUL/MULHSU (via the Move-2 guarded `inv_mul'`) and the
four width-8 seam chips (Load/StoreDouble, LoadX0, Mul) are all migrated. At a real trace row whose
`kind ∈ allChipKinds`, `kind.advance.isSome` holds, so the grounding engine can fire that chip's
`advance` generically (`RowWiring.advance_at`, `Soundness/GroundingAdapter.lean`). -/
theorem allChipKinds_migrated : ∀ k ∈ allChipKinds (p := p), k.advance.isSome = true := by
  intro k hk
  fin_cases hk <;> rfl

end SP1Clean.Soundness
