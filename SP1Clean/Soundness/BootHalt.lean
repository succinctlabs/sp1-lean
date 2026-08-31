import SP1Clean.Soundness.AIR

/-! # The single-shard boot→halt corollary

The first **whole-execution** claim of this workstream.  Everything above concludes a *shard-local*
segment: a run between two committed public endpoints, with boot reachability deliberately absent.
This module names the one case where the two ends of the shard are the two ends of the program —
a first shard (`BootBoundaryFacts`: `IsInitialState` at the committed entry pc, SP1's zeroed
integer register file, boot clock `1`) that also halts (a live Halt row, forced unique by the Exit
hand-off) — and states the resulting fact in plain Sail/`GuestProgram` vocabulary:

> from the program's entry point with zeroed registers, a normally-retiring official-interpreter
> run reaches a genuine `SP1Halted` state whose `a0` is the committed public exit code, the
> committed final pc is SP1's terminal `haltPc`, and the committed final clock is exactly
> `1 + 8·steps + 264`.

No conjunct is an AIR artifact: `SailRetireChain`, `IsInitialState`, `RegistersZero` and
`SP1Halted` are all statements about the official Sail model and the committed guest program.

What this is *not*: a multi-shard theorem.  It applies to a single shard that both boots and halts.
The reserved multi-shard vocabulary (`EventShardLayout`, `LastExecutionHalts`,
`SP1ExecutionRelation`) composes shards along an authenticated ledger and is a separate,
recursion-dependent target. -/

open LeanRV64D.Defs

namespace SP1Clean.Soundness

open Air.Flat Circuit
open SP1Clean.Execution

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- **The single-shard boot→halt relation.**  The ensemble algebra, a *boot* semantic boundary
(strictly stronger than `SemanticBoundaryBinding`: the selected initial state is a genuine
`IsInitialState` at the program entry point, with zeroed registers and SP1's boot clock `1`), a
live Halt row, and the ordinary row-capacity policy.

The halt restriction is stated as `realHaltRows witness ≠ []` rather than as a public-values
condition on purpose: which branch a shard is in is decided by the Exit hand-off's *algebra*
(`Soundness/ExitAccounting.lean`), not by a separate promise about the statement. -/
def SupportedCoreBootHaltRelation :
    WitnessRelation.Relation (SupportedCoreStatement p) (SupportedCoreNativeWitness p) :=
  fun statement witness =>
    SupportedCoreEnsembleRelation statement witness ∧
      (∃ initial, BootBoundaryFacts statement witness initial) ∧
      realHaltRows witness ≠ [] ∧
      CoreProfile.WithinOrdinaryRowLimit
        (realDecodedInstructionRows witness.data witness.tables).length

/-- A boot→halt witness is in particular an ordinary capacity-bounded native shard witness, so
every shard-level theorem above applies to it unchanged. -/
theorem SupportedCoreBootHaltRelation.toShardRelation
    {statement : SupportedCoreStatement p} {witness : SupportedCoreNativeWitness p}
    (valid : SupportedCoreBootHaltRelation statement witness) :
    SupportedCoreNativeShardRelation statement witness := by
  obtain ⟨ensemble, ⟨initial, boot⟩, -, rowLimit⟩ := valid
  exact ⟨⟨ensemble, boot.base.binding⟩, rowLimit⟩

/-- **Boot to halt, on one shard.**  A satisfying, channel-balanced native witness whose semantic
boundary is a genuine boot state and whose Halt table carries a live row yields a complete
official-Sail execution of the committed guest program: from the entry point with zeroed
registers, `steps` normally-retiring interpreter steps reach a state that is `SP1Halted` with the
committed public exit code, and the public endpoint agrees — terminal pc `haltPc`, final clock
`1 + 8·steps + 264` (the boot clock, the eight-tick instruction window per step, and SP1's
264-tick syscall window). -/
theorem supported_core_boot_to_halt_single_shard
    (statement : SupportedCoreStatement p) (witness : SupportedCoreNativeWitness p)
    (valid : SupportedCoreBootHaltRelation statement witness) :
    ∃ (initial preHalt : SailState) (steps : ℕ),
      Target.IsInitialState statement.program initial ∧
      Machine.RegistersZero initial ∧
      Target.SailRetireChain steps initial preHalt ∧
      Target.SP1Halted statement.program statement.publicValues.exitCodeBits preHalt ∧
      statement.finalPcBits = Machine.haltPc ∧
      statement.finalClkNat = 1 + 8 * steps + 264 := by
  obtain ⟨⟨publicInputEq, constraints, balanced⟩, ⟨initial, boot⟩, haltLive, -⟩ := valid
  obtain ⟨rows, halt, hg⟩ :=
    (supported_core_witness_grounding statement witness initial publicInputEq constraints balanced
      boot.base).resolve_left (by
        rintro ⟨haltFree, -, -⟩
        exact haltLive haltFree)
  obtain ⟨preHalt, retire, halted, -⟩ :=
    haltedSail_of_haltGrounding statement witness initial rows halt hg boot.base
  refine ⟨initial, preHalt, rows.length, boot.isInitial, boot.registersZero, retire, halted,
    hg.finalPc, ?_⟩
  have hfin := hg.finalClock
  have hpull := hg.pullClock
  have hone := boot.clockOne
  show Semantics.clkNat statement.publicValues.final_clk_high
    statement.publicValues.final_clk_low = _
  omega

end SP1Clean.Soundness
