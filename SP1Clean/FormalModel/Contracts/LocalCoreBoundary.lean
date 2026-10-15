import SP1Clean.FormalModel.Contracts.PublicValues
import SP1Clean.Model.Core.SourceExecution
import SP1Clean.Model.Semantics.Decode
import SP1Clean.Model.Semantics.MicroTime

/-! # Public encoding of a complete local source

The source snapshot is fixed instance data. Its actual PC and execution clock determine the
public incoming State token; the verifier may not choose unrelated endpoints. The ordinary public
limb checks and the source's 48-bit ranges make these equalities canonical, without field aliases.
A stopped source also requires unchanged clock endpoints. The full outgoing snapshot and
host-effect accounting remain separate integration work.
-/

namespace SP1Clean.SP1PublicIO

open SP1Clean.Model.Core SP1Clean.Soundness.Target

variable {p : ℕ} [Fact p.Prime]

/-- Canonical field encoding of the complete snapshot's incoming clock and actual PC. -/
def SourceFor (source : ExecutionSnapshot) (input : SP1PublicIO (ZMod p)) : Prop :=
  input.init_clk_high = (source.clock / 2 ^ 24 : ℕ) ∧
    input.init_clk_low = (source.clock % 2 ^ 24 : ℕ) ∧
    input.init_pc0 = (bitVecToWord source.pc)[0] ∧
    input.init_pc1 = (bitVecToWord source.pc)[1] ∧
    input.init_pc2 = (bitVecToWord source.pc)[2]

/-- A stopped host permits an identity segment but no further clock advance. The State walk
turns this endpoint condition into absence of active instruction and syscall rows. -/
def PreservesStoppedClock (source : ExecutionSnapshot) (input : SP1PublicIO (ZMod p)) : Prop :=
  source.host.exitCode ≠ none →
    input.final_clk_high = input.init_clk_high ∧ input.final_clk_low = input.init_clk_low

/-- The incoming field clock decodes to the actual source clock, without modular aliases. -/
theorem SourceFor.clock [Fact (2 ^ 24 < p)] {source : ExecutionSnapshot}
    {input : SP1PublicIO (ZMod p)} (bound : source.clock < 2 ^ 48)
    (binding : input.SourceFor source) :
    SP1Clean.Semantics.clkNat input.init_clk_high input.init_clk_low = source.clock := by
  have primeBound := Fact.out (p := 2 ^ 24 < p)
  have high : source.clock / 2 ^ 24 < p := by omega
  have low : source.clock % 2 ^ 24 < p := by omega
  simp only [SP1Clean.Semantics.clkNat, binding.1, binding.2.1,
    ZMod.val_natCast, Nat.mod_eq_of_lt high, Nat.mod_eq_of_lt low]
  omega

/-- The incoming PC is the source's real Sail PC, including the checked zero upper limb. -/
theorem SourceFor.pc [Fact (2 ^ 17 < p)] {source : ExecutionSnapshot}
    {input : SP1PublicIO (ZMod p)} (bound : source.pc.toNat < 2 ^ 48)
    (binding : input.SourceFor source) :
    SP1Clean.Semantics.pcBits input.init_pc0 input.init_pc1 input.init_pc2 = source.pc := by
  have high : (BitVec.extractLsb' 48 16 source.pc).toNat = 0 := by
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt bound, Nat.zero_mod]
  have wordHigh : (bitVecToWord (p := p) source.pc)[3] = 0 := by
    simp [bitVecToWord, high]
  have full := toBitVec64_bitVecToWord (p := p) source.pc
  rw [Word.toBitVec64, Word.toNat, wordHigh, ZMod.val_zero, zero_mul, add_zero] at full
  simpa only [SP1Clean.Semantics.pcBits, binding.2.2.1, binding.2.2.2.1, binding.2.2.2.2] using full

end SP1Clean.SP1PublicIO

namespace SP1Clean.LocalSourceBoundary

open Model.Core

/-- The complete source is valid and bound to the incoming public token; a stopped source
cannot advance the public clock. Public limb bounds are supplied by the State verifier. -/
def Spec {p : ℕ} [Fact p.Prime] (image : ProgramImage) (source : ExecutionSnapshot)
    (input : SP1PublicIO (ZMod p)) : Prop :=
  ExecutionSourceValid image source ∧ input.SourceFor source ∧ input.PreservesStoppedClock source

end SP1Clean.LocalSourceBoundary
