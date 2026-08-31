import SP1Clean.FormalModel.Contracts.SystemChips
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.RegisterAccessCols
import SP1Clean.Model.Channels
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The Halt table row as a native circuit

The provider-segment system table that witnesses a halting shard's `HALT` ECALL (contract:
`FormalModel/Contracts/SystemChips.lean`, `HaltChip.Inputs`/`Spec`). Composes the standard
`Readers.CPUState` block at the halt transition (`next_pc = (1, 0, 0)`, `clk_inc = 264`) and one
`Readers.RegisterAccessCols` timestamp sub-assertion per register read (`x5/x10/x11` at clock
offsets `+4/+3/+2`), pulls the committed ECALL instruction from the Program bus, emits the three
register read-prior/read-back Memory pairs, constrains the `x5` word (the syscall code) to zero,
and pushes `x10`'s word (the exit code) on the Exit bus.

This is a **native** system table — like `StateBumpChip`/`MemoryBumpChip` it has no
`ChipKind.advance` and no extracted Rust oracle: SP1's own syscall path runs through
`SyscallInstrsChip` + the global syscall tables, which the supported profile excludes; the halt
table is the native ensemble's explicit, auditable replacement for exactly the `HALT` arm
(`ExecutableSyscallHandler.haltOnly`). Ensemble wiring (table position, the verifier's gated Exit
pull, decode/grounding) is the follow-up chunk; this file is the standalone row circuit.

(`main` + `ElaboratedCircuit` here; soundness/completeness/`circuit` in
`Proofs/Chips/HaltChip/Formal.lean`.) -/

namespace SP1Clean.HaltChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel exitChannel
  ProgramMsg MemoryMsg ExitMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The row's recombined 24-bit low clock (the standard `clk_0_16 + clk_16_24 · 2^16` spelling). -/
@[circuit_norm] def clkLow (input : Var Inputs (ZMod p)) : Expression (ZMod p) :=
  input.state.clk_0_16 + input.state.clk_16_24 * 65536

/-- The Program-bus fetch: the committed instruction at the row's pc, pinned to the ECALL shape —
`opcode = Opcode.ECALL.toNat = 50`, operands `x5/x10/x11` as register indices, `op_a_0 = 0`
(`x5 ≠ x0`), no immediates. This is what proves the halt happened at a genuine `ECALL` site. -/
@[circuit_norm] def programMsg (input : Var Inputs (ZMod p)) : ProgramMsg (Expression (ZMod p)) :=
  ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 50,
   5, #v[10, 0, 0, 0], #v[11, 0, 0, 0], 0, 0, 0⟩

/-- One register read's **read-prior** Memory pull: the record at the pulled timestamp
(`prev_low` from the access block), register index `idx`, value = the read-back word. -/
@[circuit_norm] def memPullMsg (input : Var Inputs (ZMod p))
    (block : Extracted.RegisterAccessCols (Expression (ZMod p))) (idx : Expression (ZMod p)) :
    MemoryMsg (Expression (ZMod p)) :=
  ⟨input.state.clk_high, block.access_timestamp.prev_low, idx, 0, 0, block.prev_value⟩

/-- One register read's **read-back** Memory push: the same record re-established at this row's
access clock `clk_low + off`. -/
@[circuit_norm] def memPushMsg (input : Var Inputs (ZMod p))
    (block : Extracted.RegisterAccessCols (Expression (ZMod p))) (idx off : Expression (ZMod p)) :
    MemoryMsg (Expression (ZMod p)) :=
  ⟨input.state.clk_high, clkLow input + off, idx, 0, 0, block.prev_value⟩

/-- The Exit-bus payload of a real row: the **reduced** `x10`/`a0` word — SP1's `b().reduce()`
(`crates/core/machine/src/syscall/instructions/air.rs:487`), `w0 + w1·2^16 + w2·2^32 + w3·2^48`.
With the gated upper-limb zero checks below this is exactly the low limb, so the single committed
`exit_code` cell decodes back to `a0` with no modular wraparound. -/
@[circuit_norm] def exitMsg (input : Var Inputs (ZMod p)) : ExitMsg (Expression (ZMod p)) :=
  ⟨input.x10_memory.prev_value[0] +
    (input.x10_memory.prev_value[1] +
      (input.x10_memory.prev_value[2] + input.x10_memory.prev_value[3] * 65536) * 65536) * 65536⟩

/-- The Exit-bus payload of a padding row: the zero exit code. The verifier's ungated pull then
forces `exit_code = 0` on ordinary shards and exactly one halt-table row overall (`ExitMsg`). -/
@[circuit_norm] def exitPaddingMsg : ExitMsg (Expression (ZMod p)) := ⟨0⟩

/-- The halt row: the inline `is_real` gate, the `CPUState` block at the halt transition, the three
register-access timestamp sub-assertions, the ECALL Program pull, the gated `x5 = 0` (syscall code
`HALT`) asserts, the three register read-prior/read-back Memory pairs, and the Exit push. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  -- Local, shallow `is_real` boolean gate (`assertZero`, not `=== 0`) so it is visible to
  -- `ConstraintsHold.Shallow`, discharging every off-gate pull `Requirements`.
  assertZero (input.is_real * (input.is_real - 1))
  -- `CPUState` pulls `(clk, pc)` and pushes `(clk + 264, pc = 1)` — the halt transition: SP1's
  -- syscall row duration and `HALT_PC = 1` (`Model/Machine/Syscall.lean`'s `haltPc`).
  let _ ← Readers.CPUState.circuit ⟨input.state, #v[1, 0, 0], 264, input.is_real⟩
  -- Per-register timestamp byte checks (the standard access-clock offsets `+4/+3/+2`).
  assertion Readers.RegisterAccessCols.circuit ⟨input.x5_memory, input.is_real, clkLow input + 4⟩
  assertion Readers.RegisterAccessCols.circuit ⟨input.x10_memory, input.is_real, clkLow input + 3⟩
  assertion Readers.RegisterAccessCols.circuit ⟨input.x11_memory, input.is_real, clkLow input + 2⟩
  -- The committed instruction at `pc` is `ECALL x5, x10, x11`.
  programChannel.pullIf input.is_real (programMsg input)
  -- The syscall code (`x5`/`t0`) is `HALT = 0`, limb-wise (gated: padding rows are free).
  assertZero (input.is_real * input.x5_memory.prev_value[0])
  assertZero (input.is_real * input.x5_memory.prev_value[1])
  assertZero (input.is_real * input.x5_memory.prev_value[2])
  assertZero (input.is_real * input.x5_memory.prev_value[3])
  -- The exit code fits one 16-bit limb: `x10`'s upper three limbs vanish.  This is the disclosed
  -- profile strengthening that makes the single committed `exit_code` cell reconstruct the exact
  -- 64-bit `a0` value — SP1's own AIR reduces the whole word into one cell, which wraps mod `p`
  -- for `a0 ≥ p` (KoalaBear is below `2 ^ 32`), so no unconditional decode exists there.
  assertZero (input.is_real * input.x10_memory.prev_value[1])
  assertZero (input.is_real * input.x10_memory.prev_value[2])
  assertZero (input.is_real * input.x10_memory.prev_value[3])
  -- Three pure register reads: read-prior pull + read-back push (`x5` at `+4`, `x10` at `+3`,
  -- `x11` at `+2`), exactly the `RTypeReader` read shape.
  memoryChannel.pullIf input.is_real (memPullMsg input input.x5_memory 5)
  memoryChannel.pushIf input.is_real (memPushMsg input input.x5_memory 5 4)
  memoryChannel.pullIf input.is_real (memPullMsg input input.x10_memory 10)
  memoryChannel.pushIf input.is_real (memPushMsg input input.x10_memory 10 3)
  memoryChannel.pullIf input.is_real (memPullMsg input input.x11_memory 11)
  memoryChannel.pushIf input.is_real (memPushMsg input input.x11_memory 11 2)
  -- The exit binding: a real row pushes the reduced `x10` word, a padding row the zero code; the
  -- state-boundary verifier's ungated `⟨exit_code⟩` pull balances against exactly one of them.
  exitChannel.pushIf input.is_real (exitMsg input)
  exitChannel.pushIf (1 - input.is_real) exitPaddingMsg

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main where
  localLength _ := 0
  output _ _ := ()
  -- Pulled buses (guarantees assumed): byte (via the composed readers), the structural State pull,
  -- the Program fetch, and the three memory read-priors. The Memory read-backs and the Exit push
  -- owe requirements (declared on `circuit.channelsWithRequirements` in `Formal`); Exit joins the
  -- list here so its interaction stays visible to composing ensembles.
  channelsWithGuarantees :=
    [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw,
     exitChannel.toRaw]
  channelsLawful := by
    dsimp only [ElaboratedCircuit.ChannelsLawful]
    intro input offset
    dsimp only [Operations.ChannelsLawful]
    refine ⟨by simp only [circuit_norm, main, Readers.CPUState.circuit,
        Readers.RegisterAccessCols.circuit], ?_,
      by simp only [circuit_norm, main, Readers.CPUState.circuit,
        Readers.RegisterAccessCols.circuit]⟩
    intro env
    rw [Operations.inChannelsOrGuarantees_iff_forall_mem]
    intro interaction h_interaction
    simp only [circuit_norm, main, Readers.CPUState.circuit,
      Readers.RegisterAccessCols.circuit] at h_interaction
    rcases h_interaction with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    -- program (slot 2), the six memory interactions (slot 3), the two exit pushes (slot 4)
    · exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    all_goals first
      | exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ List.mem_cons_self)))
      | exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))

-- Expose the declared channel list + `localLength` as `@[circuit_norm]` rfl-lemmas so composing
-- ensembles' `channelsLawful` / `circuit_proof_start` are discharged automatically.
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw,
         exitChannel.toRaw] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

end SP1Clean.HaltChip
