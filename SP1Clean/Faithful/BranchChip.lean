import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Proofs.Chips.BranchChip.Formal
import SP1Clean.Model.SP1Constraint
import SP1Clean.Extracted.BranchChip

/-! # Chip-level faithfulness anchor for BRANCH

Anchors SP1's generated `Extracted.BranchColumns.asserts` / `.interactions` lists (opcodes 40–45)
to the native chip's structural specs (`branchAssertSpec`, `branchInteractSpec`).

BRANCH's `asserts` list has the composed `CPUState ++ ITypeReaderImmutable ++ LtOperationSigned`
prefix plus a rich inline tail: the six opcode-flag booleans, the flag sum bound, the `is_branching`
boolean and its decision constraint, and the two gated `AddOperation` carry-chains for `next_pc`.
The `interactions` tail is the three `next_pc` byte-range sends.

Both halves are proven in the forward direction (`→`) by peeling the composed sub-lists and reading
off the inline tail; the kept-opaque sub-lists and carry-chains are discarded. -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- `(14 : ZMod p).val = 14` under `Fact (2^17 < p)` (for the `Range(next_pc[0]/4, 14)` send). -/
private lemma val_14 [NeZero p] : (14 : ZMod p).val = 14 := by
  have : (131072 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  exact ZMod.val_natCast_of_lt (show (14 : ℕ) < p by omega)

/-- `(16 : ZMod p).val = 16` under `Fact (2^17 < p)` (for the `next_pc[1]`/`next_pc[2]` u16 sends). -/
private lemma val_16 [NeZero p] : (16 : ZMod p).val = 16 := by
  have : (131072 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  exact ZMod.val_natCast_of_lt (show (16 : ℕ) < p by omega)

/-- The chip-local structural meaning of BRANCH's `asserts` inline tail (everything past the composed
`CPUState`/`ITypeReaderImmutable`/`LtOperationSigned` sub-lists): the six opcode-flag booleans, the flag
sum bound (`E16 = Σ is_b*` boolean), the `is_branching` boolean, the `is_real`-gated decision constraint
(`is_real·(is_branching − decision) = 0`, the `E80–E92` branching logic), and the two gated `AddOperation`
carry-chains for `next_pc` (taken target `pc + op_c_imm`, fall-through `pc + 4`). -/
def branchAssertSpec (cols : BranchColumns (ZMod p)) : Prop :=
  let sum := cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge + cols.is_bltu + cols.is_bgeu
  (cols.is_beq * (cols.is_beq - 1) = 0) ∧ (cols.is_bne * (cols.is_bne - 1) = 0) ∧
  (cols.is_blt * (cols.is_blt - 1) = 0) ∧ (cols.is_bge * (cols.is_bge - 1) = 0) ∧
  (cols.is_bltu * (cols.is_bltu - 1) = 0) ∧ (cols.is_bgeu * (cols.is_bgeu - 1) = 0) ∧
  (sum * (sum - 1) = 0) ∧
  (cols.is_branching * (cols.is_branching - 1) = 0) ∧
  (let is_eq : ZMod p := 1 - (cols.compare_operation.result.u16_flags[0]
        + cols.compare_operation.result.u16_flags[1] + cols.compare_operation.result.u16_flags[2]
        + cols.compare_operation.result.u16_flags[3]);
    let bit := cols.compare_operation.result.u16_compare_operation.bit;
    let decision := cols.is_beq * is_eq + cols.is_bne * (1 - is_eq)
      + (cols.is_bge + cols.is_bgeu) * (1 - bit) + (cols.is_blt + cols.is_bltu) * bit;
    sum * (cols.is_branching - decision) = 0)

/-- The chip-local structural meaning of BRANCH's `interactions` tail: the three `next_pc` byte-range
sends (the low limb 4-byte-aligned via `Range(next_pc[0]/4, 14)`, the two high limbs `u16`), all gated by
the flag sum `Σ is_b*`. -/
def branchInteractSpec (cols : BranchColumns (ZMod p)) : Prop :=
  let sum := cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge + cols.is_bltu + cols.is_bgeu
  ((cols.next_pc[0] * (4 : ZMod p)⁻¹).val < 2 ^ 14 ∨ sum = 0) ∧
  (cols.next_pc[1].val < 2 ^ 16 ∨ sum = 0) ∧
  (cols.next_pc[2].val < 2 ^ 16 ∨ sum = 0)

set_option linter.unusedSectionVars false in
set_option maxHeartbeats 2000000 in
/-- **Faithfulness anchor — assertion half.** SP1's `Branch` chip `asserts` list entails the native
chip's inline structural meaning (`branchAssertSpec`): peel the composed
`CPUState`/`ITypeReaderImmutable`/`LtOperationSigned` sub-lists and flatten the inline tail, reading
off the six opcode-flag booleans, the flag-sum bound, the `is_branching` boolean, and the gated
decision constraint (the two `AddOperation` carry-chains are extra and discarded). -/
theorem branch_asserts_faithful (cols : BranchColumns (ZMod p)) :
    List.Forall (· = 0) (BranchColumns.asserts cols) → branchAssertSpec cols := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  intro h
  -- Peel the composed `CPUState ++ ITypeReaderImmutable ++ LtOperationSigned` sub-lists (kept opaque)
  -- and flatten the inline tail; we only need the nine inline gates (the two `AddOperation`
  -- carry-chains `E103…E156` are extra and discarded).
  simp only [Extracted.BranchColumns.asserts, List.forall_append, List.Forall] at h
  obtain ⟨-, hE1, hE3, hE5, hE7, hE9, hE11, hE18, hE94, hE96, -⟩ := h
  simp only [branchAssertSpec]
  exact ⟨hE1, hE3, hE5, hE7, hE9, hE11, hE18, hE94, by linear_combination hE96⟩

set_option linter.unusedSectionVars false in
set_option maxHeartbeats 2000000 in
/-- **Faithfulness anchor — interaction half.** SP1's `Branch` chip `interactions` tail (the three
`next_pc` byte-range sends) entails the native chip's `branchInteractSpec`: peel the composed
reader/compare interaction sub-lists and read off the three trailing byte sends (`Range(next_pc[0]/4,
14)` and the two u16 limbs), each gated by the flag sum. -/
theorem branch_interactions_faithful (cols : BranchColumns (ZMod p)) :
    List.Forall Interaction.toProp (BranchColumns.interactions cols) → branchInteractSpec cols := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  intro h
  -- Peel the composed interaction sub-lists (kept opaque) and read off the three trailing byte sends:
  -- `Range(next_pc[0]/4, 14)`, u16 `next_pc[1]`, u16 `next_pc[2]`, each gated by the flag sum `E16`.
  simp only [Extracted.BranchColumns.interactions, List.forall_append, List.Forall,
    Interaction.toProp_send_byte, ByteOpcode.ofNat_six, ByteOpcode.constrain_Range,
    val_14, val_16] at h
  obtain ⟨-, h0, h1, h2⟩ := h
  simp only [branchInteractSpec]
  refine ⟨?_, ?_, ?_⟩
  · rcases eq_or_ne (cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge + cols.is_bltu
      + cols.is_bgeu) 0 with hs | hs
    · exact Or.inr hs
    · exact Or.inl (h0 hs)
  · rcases eq_or_ne (cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge + cols.is_bltu
      + cols.is_bgeu) 0 with hs | hs
    · exact Or.inr hs
    · exact Or.inl (h1 hs)
  · rcases eq_or_ne (cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge + cols.is_bltu
      + cols.is_bgeu) 0 with hs | hs
    · exact Or.inr hs
    · exact Or.inl (h2 hs)

end SP1Clean.Faithful
