import SP1Clean.FormalModel.Contracts.ResourceBoundary
import SP1Clean.Model.Core.SailFinalCheck

/-! # Supplied Sail target: invariant fields and actual public endpoints

This is one part of complete Sail target binding. Register presence and invariant values are
checked as finite snapshot data. The public clock and PC are tied to the same target. Dynamic
nextPC and retirement, and full host-field reconstruction, are separate remaining obligations.
-/

namespace SP1Clean.SailBoundary

open Model.Core Soundness.Target

/-- Check invariant Sail fields and endpoint ranges before conversion to the AIR field. -/
def checkStatic (source target : ExecutionSnapshot) : Bool :=
  source.sail.checkFrame target.sail && decide (target.clock < 2 ^ 48) && decide (target.pc.toNat < 2 ^ 48)

/-- The outgoing public State token is the canonical clock and PC of the supplied target. -/
def TargetFor {p : ℕ} [Fact p.Prime] (target : ExecutionSnapshot) (input : SP1PublicIO (ZMod p)) : Prop :=
  ResourceBoundary.ClockFor target input ∧
    input.final_pc0 = (bitVecToWord target.pc)[0] ∧
    input.final_pc1 = (bitVecToWord target.pc)[1] ∧
    input.final_pc2 = (bitVecToWord target.pc)[2]

/-- The invariant-field and public-endpoint portion of complete Sail target validation. -/
def Spec {p : ℕ} [Fact p.Prime] (source target : ExecutionSnapshot) (input : SP1PublicIO (ZMod p)) : Prop :=
  checkStatic source target = true ∧ TargetFor target input

/-- The existing canonical clock decoder identifies the supplied target's natural clock. -/
theorem TargetFor.clock {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]
    {target : ExecutionSnapshot} {input : SP1PublicIO (ZMod p)}
    (bound : target.clock < 2 ^ 48) (binding : TargetFor target input) :
    Semantics.clkNat input.final_clk_high input.final_clk_low = target.clock :=
  ResourceBoundary.ClockFor.clock bound binding.1

/-- Reuse the source endpoint decoder on the same public limbs viewed as the outgoing endpoint. -/
theorem TargetFor.pc {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
    {target : ExecutionSnapshot} {input : SP1PublicIO (ZMod p)}
    (bound : target.pc.toNat < 2 ^ 48) (binding : TargetFor target input) :
    Semantics.pcBits input.final_pc0 input.final_pc1 input.final_pc2 = target.pc := by
  let incoming : SP1PublicIO (ZMod p) := { input with
    init_clk_0_16 := input.final_clk_0_16
    init_clk_16_24 := input.final_clk_16_24
    init_clk_24_32 := input.final_clk_24_32
    init_clk_32_48 := input.final_clk_32_48
    init_pc0 := input.final_pc0
    init_pc1 := input.final_pc1
    init_pc2 := input.final_pc2 }
  have source : incoming.SourceFor target := ⟨binding.1.1, binding.1.2, binding.2⟩
  exact SP1PublicIO.SourceFor.pc bound source

/-- The static assertion enforces the complete invariant-field check. -/
theorem Spec.frame {p : ℕ} [Fact p.Prime]
    {source target : ExecutionSnapshot} {input : SP1PublicIO (ZMod p)} (spec : Spec source target input) :
    source.sail.checkFrame target.sail = true := by
  have checked := spec.1
  simp only [checkStatic, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact checked.1.1

/-- Endpoint ranges are checked before any reduction modulo the AIR characteristic. -/
theorem Spec.ranges {p : ℕ} [Fact p.Prime]
    {source target : ExecutionSnapshot} {input : SP1PublicIO (ZMod p)} (spec : Spec source target input) :
    target.clock < 2 ^ 48 ∧ target.pc.toNat < 2 ^ 48 := by
  have checked := spec.1
  simp only [checkStatic, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact ⟨checked.1.2, checked.2⟩

/-- No missing target GPR can be hidden by the Memory projection's zero fallback. -/
theorem Spec.initialized {p : ℕ} [Fact p.Prime]
    {source target : ExecutionSnapshot} {input : SP1PublicIO (ZMod p)} (spec : Spec source target input) :
    target.sail.skeleton.isInitialized := (SailSnapshot.checkFrame_iff _ _).mp spec.frame |>.1

/-- The checked target's Memory projection is its real Sail register/memory observation. -/
theorem Spec.memorySnapshot_realizes {p : ℕ} [Fact p.Prime]
    {source target : ExecutionSnapshot} {input : SP1PublicIO (ZMod p)} (spec : Spec source target input) :
    target.sail.memorySnapshot.Realizes target.sail.realize :=
  target.sail.memorySnapshot_realizes spec.initialized

end SP1Clean.SailBoundary
