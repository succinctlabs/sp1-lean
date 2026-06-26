# Clean merged-`main` migration (roadmap W9 residual)

**Status:** attempted 2026-06-26, **reverted** (build red, migration larger than expected). All machinery
the final `sorry` (`sp1_witness_decode`) needs is already present at the current pin, so this migration is
**independent** of the decode work and can be done on its own. **Heavy** — full rebuilds of Clean + SP1Clean
(~20–40 min each); do on better hardware.

## The move

- **From:** `292b9cc369be11baf816926a4bd5a697c01b1dcc` (Clean PR #398 *branch head*, `fix-zero-multiplicity-channels`,
  the commit "Derive VM enabledness from constraints", 2026-06-09).
- **To:** `2c20f7f0fb30ed336dd42bbf023254b5a650faaf` (Clean `main` HEAD = the #398 **merge commit**,
  2026-06-25). Same toolchain `leanprover/lean4:v4.28.0` (verified). Mechanics: edit `lakefile.toml` `rev`,
  run the **scoped** `lake update Clean` (NOT bare `lake update` — it bumps to the max dep toolchain → 4.29),
  then full `lake build SP1Clean`.

The delta `292b9cc3..2c20f7f0` (13 commits) includes the breaking ones: `cedc171b` "assume constraints for
channels with reqs", `e9a88dd2` "get rid of wellformedness", `50f03662` "rename variables", plus
`d25bba8d` "Avoid Fin fold lemma clash with Batteries" (likely retires our import-narrowing workaround).

## API deltas to migrate (concrete)

1. **`BalancedChannel` dropped `∧ InteractionsWellFormed`** (`Air/FlatEnsemble.lean:332` — now bare
   `BalancedInteractions (witness.allTablesWitness.interactionsWith channel)`).
   - **Fix:** `Soundness/SP1GatedVm.lean:278` — `(hB … (List.mem_cons_self ..)).1` → drop the `.1`
     (the value is no longer an `∧`). One line. (This was the only project consumer of the conjunction.)

2. **`channelsWithRequirements` moved OFF `ElaboratedCircuit` ONTO the formal-circuit structures**
   (`Air`/`Circuit/Formal.lean:38` — it's a field of `GeneralFormalCircuit`/`FormalCircuit`/`FormalAssertion`
   now; `channelsWithGuarantees` *stays* on `ElaboratedCircuit`, `Circuit/Basic.lean:246`). A new obligation
   field **`requirementsChannelsLawful`** appears on the formal-circuit/assertion (synth-default fails → must
   be supplied).
   - **Migrate (per chip / reader):** move `channelsWithRequirements := [...]` from the `elaborated`
     `ElaboratedCircuit` instance (in `Native/Chips/<C>Chip/Defs.lean`) to the **`circuit`
     `GeneralFormalCircuit` def** (in `Proofs/Chips/<C>Chip/Formal.lean`). Add
     `requirementsChannelsLawful input_var i₀ := by simp only [circuit_norm, <ChannelName defs>]`
     (idiom from `Examples/FibonacciWithChannels.lean:164-212`). Re-point each `channelsWithRequirements_eq`
     `@[circuit_norm]` rfl-lemma to the new owner (or delete if Clean now provides it).
   - This is a **cross-file move** (Defs → Formal) and affects every chip's `circuit_proof_start` /
     `ElaboratedCircuit`-default story — see AGENTS.md "ElaboratedCircuit field obligations".

3. **`pushIf`/`pullIf` are now `Channel.` methods; `ChannelInteraction` gained a 3rd field**
   (`Circuit/Basic.lean:143/155`): `channel.pullIf enabled msg` / `channel.pushIf enabled msg`, building
   `ChannelInteraction channel := ⟨ mult, msg, isPull ⟩` (3rd = `true` pull / `false` push). The
   `pushIf (channel := …) mult msg` named-argument form is **gone**.
   - **Fix:** `Model/InteractionProjection.lean` (the `toAccess_pushIf_*` / `toAccess_pullIf_*` kernels —
     ~lines 107-130+): rewrite `pushIf (channel := c) …` → `c.pushIf …`, and update the unfolding simp sets
     (`ChannelInteraction.toRaw`, `pushIf`, `pullIf`) for the new 3-field constructor. Same in any reader
     that emits via the named-arg form.

## File inventory (the build only *reached* 11 before stopping; true surface is larger)

- **Hand-written, one root cause each:**
  - `Model/InteractionProjection.lean` — delta 3.
  - `Soundness/SP1GatedVm.lean` — delta 1 (the `.1`) + `sp1VerifierElaborated` sets
    `channelsWithRequirements := [stateChannel.toRaw]` → move it to `sp1Verifier` (the GeneralFormalCircuit)
    + its `channelsWithRequirements_eq` rfl-lemma (`:98-100`).
  - **~20 `Native/Chips/*/Defs.lean` + their `Proofs/Chips/*/Formal.lean`** — delta 2 (cross-file move +
    `requirementsChannelsLawful`). The 3 whole chips (DivRem/ShiftLeft/ShiftRight) live under `Proofs/Chips/*`.
  - **`Native/Readers/*.lean`** (CPUState, MemoryAccess, RegisterAccessTimestamp, RegisterAccessCols,
    RTypeReader, ITypeReader[Immutable], ALUTypeReader[Immutable], JTypeReader) — deltas 2+3.
  - **`Native/Operations/*.lean`** that expose `channelsWith*` (AddressOperation, U16toU8Operation{Safe,Unsafe},
    BitwiseU16Operation) — delta 2.
  - **`Faithful/*`** FormalAssertions (the 3 `requirementsChannelsLawful` synth-default failures, seen in
    AddChip/SubChip/AddwChip/SubwChip Faithful) — delta 2.
- **Auto-gen (DO NOT hand-edit) — regen via `update_extracted.py`:** 7 `Extracted/Circuit/*.lean`
  (AddOperation, AddrAddOperation, BitwiseOperation, IsZeroOperation, SubOperation, U16CompareOperation,
  U16MSBOperation; likely all 14+ once reached). The emitter normalizer **`_normalize_circuit_api`** must be
  updated for the new API (channelsWithRequirements location + `Channel.pushIf`/`pullIf` names + 3-field
  interaction). `../sp1` (the extraction source) **is present**, so a full regen at the SP1 pin is runnable;
  budget time for it. Re-check `Extracted/` byte-currency via the audit afterward.

## Migration idiom (copy from the working `Examples/FibonacciWithChannels.lean`)

```lean
def pushBytes : GeneralFormalCircuit (F p) (fields 256) unit where
  main multiplicities := do …
  channelsWithRequirements := [ BytesChannel.toRaw ]        -- now on the GeneralFormalCircuit
  Spec _ _ _ := True
  …
-- and for a FormalAssertion with reqs:
  channelsWithRequirements := [ FibonacciChannel.toRaw ]
  requirementsChannelsLawful input_var i₀ := by
    simp only [circuit_norm, FibonacciChannel, Add8Channel]
-- emission:  FibonacciChannel.pullIf enabled (n, x, y) ;  Add8Channel.pullIf enabled (x, y, z) ;
--            FibonacciChannel.pushIf enabled (n + 1, y, z)
```

## Suggested order

1. `lakefile.toml` rev → `2c20f7f0…`; scoped `lake update Clean`.
2. Update `update_extracted.py` `_normalize_circuit_api`; regen `Extracted/` (+ `WitnessTests/`); confirm
   byte-currency.
3. Bottom-up hand migration: Operations → Readers → Chips Defs/Formal → Faithful → `SP1GatedVm` →
   `InteractionProjection`. Lean on `circuit_norm` defaults; re-point/delete `channelsWith*_eq` lemmas.
4. Re-test the Batteries import-narrowing collision (`docs/agents/lean-sail-notes.md:43-54`); remove the
   workaround if `d25bba8d` retired it.
5. Full `lake build SP1Clean` (0/0, no stray `info:`), `lake test`, `scripts/run_audit.sh`.
6. Docs: flip roadmap **W9** residual to closed; update `lean-sail-notes.md` (pin + Batteries note) and the
   `lakefile.toml` Clean comment.

## Why this is decoupled from the final `sorry`

`sp1_witness_decode` only needs: Clean's gated VM/OrderedChannel/Balance lemmas
(`spec_and_guarantees_of_soundChannels`, `guarantees_of_requirements_of_requirements_of_guarantees_gated`),
`byteAccessValid_of_balance` (`Soundness/ByteConsistency.lean`), `MemoryIsU64`'s
`operand_*_isU64_of_memBalance`, and `stateLookups_eq_emitted` — **all already present at `292b9cc3`**.
The decode (`~/.claude/plans/make-a-plan-to-rustling-manatee.md`, Stages 1-5) proceeds on the current pin;
this migration is a nicety, not a prerequisite.
