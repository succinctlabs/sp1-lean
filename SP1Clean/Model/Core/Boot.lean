import SP1Clean.Model.Core.ProgramImage
import SP1Clean.Model.Core.MemoryWord
import SP1Clean.Model.Machine.ConfiguredState
import SP1Clean.Model.Semantics.ProgramCommitment

/-! # Boot from a checked finite image

The native core owns its initial state. It fixes the entry PC and platform configuration, zeros
the integer registers, and realizes the ROM-overlaid sparse image with zero defaults throughout
the supported address space. `initialSailState_loaded` proves this construction satisfies the
official Sail loader relation for every checked image, without a caller-supplied boot witness.

The full Sail memory is a semantic realization, not an executable loader used by the compiler.
The compiler and host operations consume `initialMemory`, the sparse executable representation;
`initialSailState_memory` is their bridge to the official Sail memory map.
-/

namespace SP1Clean.Model.Core.ProgramImage

open Sail LeanRV64D SP1Clean.Soundness.Target

/-- The fixed native boot state, independently of an AIR witness or an execution trace. -/
noncomputable def initialSailState (input : ProgramImage) : SailState :=
  { configuredState input.entry with mem := input.initialMemory.toSailMemory (2 ^ 48) }

private theorem initialSailState_regs (input : ProgramImage) :
    input.initialSailState.regs = (configuredState input.entry).regs :=
  Eq.refl (configuredState input.entry).regs

/-- Every guest byte has its canonical initial value; missing sparse-image bytes are zero. -/
theorem initialSailState_memory (input : ProgramImage) (address : ℕ) (bound : address < 2 ^ 48) :
    input.initialSailState.mem.get? address = some (input.initialMemory.read address) := by
  exact (input.initialMemory.toSailMemory_get? (2 ^ 48) address).trans (if_pos bound)

/-- Sparse initial-memory words agree with the actual Sail memory used by timed grounding. -/
theorem initialSailState_word (input : ProgramImage) (address : BitVec 64)
    (footprint : address.toNat + 8 ≤ 2 ^ 48) :
    Semantics.ramWord64? input.initialSailState address =
      some (input.initialMemory.readWord address.toNat) := by
  apply input.initialMemory.ramWord64?_of_bytes
  intro index
  exact input.initialSailState_memory _ (by have := index.isLt; omega)

theorem initialSailState_configured (input : ProgramImage) : SailConfigured input.initialSailState :=
  configured_with_memory (cfgState_configured input.entry) _

theorem initialSailState_registersZero (input : ProgramImage) :
    SP1Clean.Machine.RegistersZero input.initialSailState := by
  intro index
  have zero := registersZero_configuredState input.entry index
  simpa only [SailState.get_reg?, initialSailState_regs] using zero

/-- Input validation suffices to construct an actual loaded, configured Sail state. -/
theorem initialSailState_loaded (input : ProgramImage) (valid : input.Valid) :
    IsInitialState (input.toGuestProgram valid) input.initialSailState where
  initialized := by
    intro reg
    change reg ∈ input.initialSailState.regs
    rw [initialSailState_regs]
    exact cfgState_init input.entry reg
  pc := by
    change input.initialSailState.regs.get? LeanRV64D.Defs.Register.PC = some input.entry
    rw [initialSailState_regs]
    exact cfgState_pc input.entry
  configured := input.initialSailState_configured
  romLoaded := by
    intro address word fetched index
    obtain ⟨row, found, wordEq⟩ := Option.map_eq_some_iff.mp fetched
    have member : row ∈ input.rom := List.mem_of_find?_eq_some found
    have atPC : row.1 = address := by simpa using List.find?_some found
    have inWindow : 2 ^ 16 ≤ row.1.toNat ∧ row.1.toNat + 4 ≤ 2 ^ 48 :=
      (valid.2.1 row member).2.1
    rw [← atPC, ← wordEq, input.initialSailState_memory _ (by have := index.isLt; omega),
      input.initialMemory_rom valid row member index]
  imageLoaded := by
    intro byte member
    rw [input.initialSailState_memory _ (valid.2.2.2.2.1 byte member).2,
      input.initialMemory_image valid byte member]

/-- The checked-image domain is non-vacuous at the loader boundary for every accepted input. -/
theorem hasInitialState (input : ProgramImage) (valid : input.Valid) :
    (input.toGuestProgram valid).HasInitialState :=
  ⟨input.initialSailState, input.initialSailState_loaded valid⟩

/-- The existing canonical commitment encoder is total on checked finite images. -/
theorem toGuestProgram_encodable (input : ProgramImage) (valid : input.Valid) :
    SP1Clean.Commit.Encodable (input.toGuestProgram valid) := by
  intro byte member
  exact (valid.2.2.2.2.1 byte member).2

/-- Reusing the existing commitment representation needs no caller-supplied semantic binding
for the honest compiler: it follows from the finite input checks. -/
theorem dataOf_statementFor {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
    (input : ProgramImage) (valid : input.Valid) :
    SP1Clean.Commit.StatementFor
      (SP1Clean.Commit.dataOf (p := p) (input.toGuestProgram valid)) (input.toGuestProgram valid) :=
  SP1Clean.Commit.dataOf_statementFor _ (input.toGuestProgram_wellFormed valid)
    (input.toGuestProgram_encodable valid)

end SP1Clean.Model.Core.ProgramImage
