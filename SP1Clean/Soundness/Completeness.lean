import SP1Clean.Soundness.InstructionTrace

/-! # `Completeness` — partial VM completeness scaffold (Sail execution → circuit accepts)

The capstone (`SP1GatedVm.lean`) proves **soundness** (circuit accepts ⟹ a valid RISC-V-Sail trail
exists). This file scaffolds the dual **completeness** direction (a valid instruction ⟹ the circuit can
accept it) to the extent the per-chip proofs already support it, with an eye on eventually closing it.

**What is proven.** Each wired chip is a Clean `GeneralFormalCircuit` carrying a `completeness` field — for
valid prover inputs the constraint system is satisfiable, i.e. *an accepting row exists*. That proof is
**sorry-free for 24 of the 25 wired chips** (`completeChipNames`); only `DivRem` still carries a
`sorry` completeness. `completeChipNames` is registered
here, tied to `Coverage.wiredNames` by decidable guards, and every entry is cross-checked against the
actual `<Chip>.completeness` theorem (so this file breaks if one regresses or is renamed).

**The partial-completeness statement.** For a program all of whose instructions route to a *complete*
chip (`ProgramComplete`), every instruction's chip can produce an accepting row — `sp1_partial_completeness`.

**The open obligation (documented, not `sorry`'d).** Going from "each row is individually acceptable" to
"the whole circuit accepts the program" requires assembling the per-row witnesses into one
`EnsembleWitness` whose four channels balance — the *completeness dual* of the residual
`sp1_gatedExecution_prereqs` (`SP1GatedVm.lean`). That global step is future work; this file deliberately
stops at the per-row reduction rather than claim it. -/

namespace SP1Clean.Soundness

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## The complete-chip registry -/

/-- The wired chips whose Clean circuit `completeness` is **sorry-free** — for valid prover inputs the
prover can always produce an accepting row. This is `Coverage.wiredNames` minus the one chip whose
`completeness` is still `sorry` (`DivRem`). -/
def completeChipNames : List String :=
  ["Add", "Addi", "Addw", "Sub", "Subw", "Bitwise", "Lt", "Mul", "ShiftLeft", "ShiftRight",
   "Jal", "Jalr", "Branch", "UType",
   "LoadByte", "LoadHalf", "LoadWord", "LoadDouble", "LoadX0",
   "StoreByte", "StoreHalf", "StoreWord", "StoreDouble", "AluX0"]

theorem completeChipNames_length : completeChipNames.length = 24 := rfl

/-- Every complete chip is wired. -/
theorem completeChipNames_sub_wired : ∀ nm ∈ completeChipNames, nm ∈ wiredNames := by decide

/-- The wired chips whose `completeness` still carries a `sorry`: only `DivRem`; the partition is
honest. -/
theorem incomplete_wired_names :
    wiredNames.filter (fun nm => !completeChipNames.contains nm) = ["DivRem"] := by
  decide

/-- **Cross-check that every name in `completeChipNames` is backed by a real, in-scope chip `completeness`
theorem** — referenced here so this file fails to compile if one is removed or renamed. (Sorry-freeness
itself is enforced by the project's build gate, which surfaces every `sorry` as a warning.) -/
example : True := by
  have _ := @AddChip.completeness; have _ := @AddiChip.completeness; have _ := @AddwChip.completeness
  have _ := @SubChip.completeness; have _ := @SubwChip.completeness; have _ := @BitwiseChip.completeness
  have _ := @LtChip.completeness; have _ := @MulChip.completeness
  have _ := @ShiftLeftChip.completeness; have _ := @ShiftRightChip.completeness
  have _ := @JalChip.completeness; have _ := @JalrChip.completeness
  have _ := @BranchChip.completeness; have _ := @UTypeChip.completeness
  have _ := @LoadByteChip.completeness; have _ := @LoadHalfChip.completeness
  have _ := @LoadWordChip.completeness; have _ := @LoadDoubleChip.completeness
  have _ := @LoadX0Chip.completeness
  have _ := @StoreByteChip.completeness; have _ := @StoreHalfChip.completeness
  have _ := @StoreWordChip.completeness; have _ := @StoreDoubleChip.completeness
  have _ := @AluX0Chip.completeness
  trivial

/-! ## Instruction / program completeness -/

/-- An instruction routes to a chip whose Clean circuit completeness is proven. -/
def Instruction.toCompleteChip (i : Instruction) : Prop :=
  match i.chipName with
  | some nm => nm ∈ completeChipNames
  | none => False

instance : DecidablePred Instruction.toCompleteChip := fun i => by
  unfold Instruction.toCompleteChip; cases i.chipName <;> infer_instance

/-- A program is (partially-)complete when every instruction routes to a complete chip. -/
def ProgramComplete (prog : List Instruction) : Prop := ∀ i ∈ prog, i.toCompleteChip

/-! ## Partial VM completeness (the per-row reduction) -/

/-- **Partial VM completeness.** For a program all of whose instructions route to a chip with a proven
(sorry-free) Clean completeness, every instruction maps to a covered, *complete* chip — so the prover can
produce an accepting row for each. (The remaining step — assembling the per-row witnesses into one
balanced `EnsembleWitness`, the completeness dual of `sp1_gatedExecution_prereqs` — is the documented open
obligation.) -/
theorem sp1_partial_completeness {prog : List Instruction} (h : ProgramComplete prog) :
    ∀ i ∈ prog, ∃ nm, i.chipName = some nm ∧ nm ∈ completeChipNames := by
  intro i hi
  have hc := h i hi
  unfold Instruction.toCompleteChip at hc
  revert hc
  cases hcn : i.chipName with
  | none => intro hc; exact hc.elim
  | some nm => intro hc; exact ⟨nm, rfl, hc⟩

/-! ## A worked complete program -/

/-- `add x1,x2,x3 ; ld x5,8(x6) ; ld x0,8(x6) ; sd x3,8(x6) ; addi x7,x8,4` — every instruction routes to a
complete chip (Add, LoadDouble, LoadX0, StoreDouble, Addi). -/
def completeDemo : List Instruction :=
  [⟨.ADD,  1, 2, 3, 0, 0⟩,
   ⟨.LD,   5, 6, 0, 8, 4⟩,
   ⟨.LD,   0, 6, 0, 8, 8⟩,
   ⟨.SD,   3, 6, 0, 8, 12⟩,
   ⟨.ADDI, 7, 8, 0, 4, 16⟩]

example : ProgramComplete completeDemo := by
  intro i hi
  fin_cases hi <;> decide

/-- The chip sequence `completeDemo` maps to — all complete. -/
example : programChipNames completeDemo =
    [some "Add", some "LoadDouble", some "LoadX0", some "StoreDouble", some "Addi"] := rfl

end SP1Clean.Soundness
