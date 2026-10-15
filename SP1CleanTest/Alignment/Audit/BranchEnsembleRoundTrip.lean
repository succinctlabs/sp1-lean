import SP1CleanTest.Alignment.Support.BranchEnsembleInventory

/-! # One official branch step and an accepted complete local host-ensemble witness

This is a concrete witness, not a generic completeness or final capstone theorem. The decoder,
official Sail retirement, canonical semantic projection, compiler payload, physical Branch row,
providers, fixed lookup meanings, complete target Memory and every registered channel meet here.
-/

namespace SP1Clean.Audit.BranchEnsemble

open Circuit Air.Flat SP1Clean.Model.Core SP1Clean.Semantics
open LeanRV64D.Defs LeanRV64D.Functions

/-- Every concrete input seed has a valid physical slot and exact input length. -/
theorem seeds_present : (seeds? target header consumerSeeds).isSome = true := by native_decide

/-- Exact successful provider construction, without a fallback witness. -/
def activeSeeds : List Seed := (seeds? target header consumerSeeds).get seeds_present

/-- The actual witness on `HostFinalMemory.ensemble`, retaining its complete original registry. -/
def activeWitness : EnsembleWitness (assembly target) := witness target header activeSeeds

/-- All 93 tables remain installed, including empty instruction and host components. -/
theorem activeWitness_length : activeWitness.tables.length = 93 := builtTables_length target activeSeeds

/-- Concrete execution of the generic authenticated checker accepts all rows and channels. -/
theorem active_checked : checkPhysical target header activeSeeds = true := by native_decide

/-- Raw Clean constraints and all channel balances hold on the original assembled witness. -/
theorem accepted : activeWitness.Constraints ∧ activeWitness.BalancedChannels :=
  (checkPhysical_iff target header activeSeeds).mp active_checked

/-- The original assembled Clean relation has this concrete public statement. -/
theorem statement : (assembly target).Statement header :=
  ⟨activeWitness, rfl, accepted⟩

/-- The public header encodes the same ordinary clock and PC endpoints as the official step. -/
theorem public_endpoints :
    header.init_clk_low = 1 ∧ header.init_clk_high = 0 ∧
    header.final_clk_low = 9 ∧ header.final_clk_high = 0 ∧
    header.init_pc0.val + 65536 * header.init_pc1.val + 65536 ^ 2 * header.init_pc2.val = 65536 ∧
    header.final_pc0.val + 65536 * header.final_pc1.val + 65536 ^ 2 * header.final_pc2.val = 69628 := by
  native_decide

/-- The active instruction occupies the original installed Branch component. -/
theorem branch_component :
    (activeWitness.tables[18]'(by rw [activeWitness_length]; decide)).component = BranchChip.component := by
  exact (activeWitness.same_circuits 18 (by decide)).symm

/-- The assembled Branch table contains exactly the earlier compiler-built real row. -/
theorem actual_branch_row :
    (activeWitness.tables[18]'(by rw [activeWitness_length]; decide)).table = [BranchCompilerRoundTrip.row] := by native_decide

/-- The installed Branch row has its real selector enabled. -/
theorem branch_is_real :
    (BranchChip.component.rowInput BranchCompilerRoundTrip.env).is_real = 1 :=
  BranchCompilerRoundTrip.table_one_real_row.2

/-- Semantic and circuit evidence refer to the same decoded, compiled, normally retiring branch. -/
theorem joined (policy : HostPolicy) :
    source.realize = ⟨BranchCompilerRoundTrip.source, {}, 1⟩ ∧
    target.Realizes BranchCompilerRoundTrip.target ∧
    (try_step 0 false).run BranchCompilerRoundTrip.source =
      .ok false BranchCompilerRoundTrip.target ∧
    ExecutionStep policy BranchCompilerRoundTrip.program source.realize .ordinary
      ⟨BranchCompilerRoundTrip.target, {}, 9⟩ ∧
    projectSP1Transition? BranchCompilerRoundTrip.program
      ⟨BranchCompilerRoundTrip.source, ⟨.ordinary, BranchCompilerRoundTrip.target⟩⟩ =
      some BranchCompilerRoundTrip.view ∧
    BranchCompilerRoundTrip.compiled? = some BranchCompilerRoundTrip.compiled ∧
    (activeWitness.tables[18]'(by rw [activeWitness_length]; decide)).table = [BranchCompilerRoundTrip.row] ∧
    activeWitness.Constraints ∧ activeWitness.BalancedChannels := by
  refine ⟨source_realizes, target_realizes, BranchCompilerRoundTrip.official_try_step, ?_,
    BranchCompilerRoundTrip.projected _, BranchCompilerRoundTrip.compiled_eq, actual_branch_row,
    accepted.1, accepted.2⟩
  rw [source_realizes]
  exact BranchCompilerRoundTrip.execution_step policy

/-- Identity endpoints retain the complete source snapshot and unchanged ordinary clock. -/
def identityHeader : SP1PublicIO Fp := { header with final_clk_0_16 := 1, final_pc0 := 0 }

/-- Empty instruction traces still carry their real ordered and host-bank terminals and Exit padding. -/
def identityConsumers : List Seed :=
  [terminal 2 [], terminal 5 []] ++ hostTerminals ++
    [Seed.ofCells 57 (List.replicate (size HaltChip.Inputs) 0)]

/-- Named computed outcomes; exceptions and malformed outputs are rejected by the runner. -/
def results : List (String × Bool × Bool) :=
  [("active-branch", true, check target header consumerSeeds),
    ("wrong-public-next-pc", false, check target { header with final_pc0 := 4096 } consumerSeeds),
    ("missing-authentication-row", false,
      check target header (consumerSeeds.eraseP fun seed => seed.table == 89)),
    ("duplicate-authentication-row", false, check target header (consumerSeeds ++ validatorSeeds.take 1)),
    ("changed-untouched-register", false,
      check { target with registers := target.registers.set 31 1 } header consumerSeeds),
    ("empty-identity", true, check target identityHeader identityConsumers),
    ("malformed-seed-index", false, check target header (consumerSeeds ++ [Seed.ofCells 999 []])),
    ("malformed-seed-length", false,
      check target header ({ branchSeed with cells := [] } :: consumerSeeds))]

end SP1Clean.Audit.BranchEnsemble
