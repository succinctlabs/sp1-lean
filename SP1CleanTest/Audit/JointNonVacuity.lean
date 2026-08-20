import SP1Clean.Soundness.AIR
import SP1Clean.FormalModel.Trace.Witness
import SP1Clean.Proofs.Sail.Advance
import SP1Clean.Model.SailDecode
import SP1CleanTest.TraceGenTests.Conformance

/-! # Joint non-vacuity: the capstone's hypothesis bundle is satisfiable

The external PR110 report's Finding 3 asks whether the capstone's **full** hypothesis bundle —
`SupportedCoreNativeRelation` (constraints ∧ four-bus balance ∧ the semantic boundary binding ∧ the
memory-timestamp range companion) — is **jointly** satisfiable, or whether some conjunction of
boundary fields is silently contradictory.  This file exhibits a fully proved witness at the
concrete prime (KoalaBear, `SP1Prime`): the **empty shard** — every one of the 38 mapped tables has
zero rows, the boundary verifier row carries a public State record with **equal initial and final
endpoints** (clk `(0, 1)`, pc `0x10000` at both ends), so its final-state pull and initial-state
push are the same State message and cancel exactly.

The committed guest program is the minimal **one-instruction** program `JAL x0, 0` (a self-jump) at
`0x10000`, decoded from canonical prover data.  The original sketch used the ROM-free
`emptyProgram`, but `GuestProgram.WellFormed.entryPointPresent` demands a fetchable entry
instruction, so the ROM-free program satisfies no `InitialBoundaryFacts` — a real (and intended)
non-vacuity observation about the boundary bundle itself.  The self-jump keeps every reachable Sail
state at the same pc with untouched memory, which is what lets `SailCodeMemoryCompatible` be proved
outright rather than assumed.

**What this witnesses**: `SupportedCoreNativeRelation` is jointly satisfiable, so the capstone
`supported_core_native_sound` is not vacuously true of an unsatisfiable relation.  Per-family
provider-content satisfiability is separately witnessed by the 18 `decodedInROM` family examples
(`Soundness/Decode.lean`), and single-row constraint satisfiability by the real-row battery
(`SP1CleanTest/NonVacuityReal.lean` and `Audit/OneAddNativePremises.lean`).

**What this deliberately does NOT claim**: a satisfying **non-empty** shard (an execution shard
with active instruction rows and balanced provider content) — that is the machine-completeness
workstream (`docs/roadmap.md`).  The capstone applied to this witness yields the honest 0-step
local execution between the equal public endpoints. -/

open LeanRV64D.Defs

namespace SP1Clean.Audit.JointNonVacuity

open Air.Flat Circuit
open SP1Clean SP1Clean.TraceGenTests
open SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Execution
open SP1Clean.Channels (stateChannel byteChannel programChannel memoryChannel)
open Sail LeanRV64D LeanRV64D.Functions

/-! ## The committed program: `JAL x0, 0` at `0x10000`

One canonical ROM row `[pc0, pc1, pc2, w_lo, w_hi] = [0, 1, 0, 0x006F, 0]`: the self-jump
`JAL x0, 0` (encoding `0x0000006F`) at pc `0x10000 = 65536`.  The entry point and genesis clock are
the matching singleton keys. -/

/-- Canonical committed prover data: one ROM row (`JAL x0, 0` at `0x10000`), entry point
`0x10000`, genesis clock `(0, 1)`, no data image. -/
def anchorData : ProverData (ZMod SP1Prime) := fun key n =>
  match key, n with
  | "sp1.rom", 5 => #[#v[0, 1, 0, 111, 0]]
  | "sp1.pc_start", 3 => #[#v[0, 1, 0]]
  | "sp1.init_clk", 2 => #[#v[0, 1]]
  | _, _ => #[]

/-- The committed guest program, by definition the decode of the committed data — so the
`StatementFor` binding `progOf data = program` holds by `rfl`. -/
def anchorProgram : GuestProgram := Commit.progOf anchorData

/-- The public State boundary: **initial = final** (clk `(0, 1)`, pc `(0, 1, 0)` = `0x10000` at
both ends), which is what makes the verifier row's final-state pull and initial-state push the same
message with cancelling multiplicities. -/
def pv : SP1StateBoundary (ZMod SP1Prime) := ⟨0, 1, 0, 1, 0, 0, 1, 0, 1, 0⟩

/-- The public statement of the empty shard. -/
def stmt : SupportedCoreStatement SP1Prime := ⟨anchorProgram, pv⟩

/-- The concrete decoded ROM: exactly the self-jump word at `0x10000`. -/
theorem anchorProgram_rom :
    anchorProgram.rom = [(65536#64, (0x0000006F : BitVec 32))] := by native_decide

/-- The committed data image is empty. -/
theorem anchorProgram_memImage :
    anchorProgram.memImage = ([] : List (BitVec 64 × BitVec 8)) := by native_decide

/-- The only fetchable address/word pair is the committed self-jump. -/
theorem anchorProgram_fetchWord {a : BitVec 64} {w : BitVec 32}
    (hf : anchorProgram.fetchWord a = some w) :
    a = 65536#64 ∧ w = (0x0000006F : BitVec 32) := by
  rw [GuestProgram.fetchWord, anchorProgram_rom] at hf
  by_cases ha : (65536#64 : BitVec 64) = a
  · rw [List.find?_cons_of_pos (by simp [ha])] at hf
    simp only [Option.map_some, Option.some_inj] at hf
    exact ⟨ha.symm, hf.symm⟩
  · rw [List.find?_cons_of_neg (by simpa using ha), List.find?_nil] at hf
    simp at hf

/-- The one-instruction program satisfies the loader-facing well-formedness contract.  This is the
field the ROM-free `emptyProgram` cannot satisfy (`entryPointPresent` demands a fetchable entry
instruction), which is why the joint witness commits a real instruction. -/
theorem anchorProgram_wellFormed : anchorProgram.WellFormed where
  entryPointPresent := ⟨0x0000006F, by native_decide⟩
  imageAddressesUnique := by
    rw [GuestProgram.ImageAddressesUnique, anchorProgram_memImage]
    simp
  imageCompatibleWithROM := by
    intro address instruction hfetch index imageEntry hmem
    rw [anchorProgram_memImage] at hmem
    simp at hmem

/-- The concrete committed ROM/image row lists. -/
theorem anchorData_romRows :
    Commit.romRowsOf (p := SP1Prime) anchorData = [#v[0, 1, 0, 111, 0]] := by native_decide

theorem anchorData_imageRows :
    Commit.imageRowsOf (p := SP1Prime) anchorData = [] := by native_decide

/-- Boolean-checker bridge for the limb-range side conditions.  A bounded `∀ v ∈ l, …` over
`ZMod SP1Prime` must NOT be handed to `decide`/`native_decide` directly: instance synthesis picks
`Fintype.decidableForallFintype` over the 2^31-element field, not `List.decidableBAll`.  The `Bool`
`List.all` form evaluates over just the list. -/
theorem rowValuesBelow_of_all {n bound : ℕ} (row : Vector (ZMod SP1Prime) n)
    (h : row.toList.all (fun v => decide (v.val < bound)) = true) :
    Commit.RowValuesBelow bound row := by
  intro value hvalue
  exact of_decide_eq_true (List.all_eq_true.mp h value hvalue)

/-- The committed representation is canonical: nothing is sanitized away, all limbs are in range,
and the singleton keys are singletons. -/
theorem anchorData_canonicalEncoding : Commit.CanonicalEncoding (p := SP1Prime) anchorData := by
  refine ⟨by native_decide, ?_, ?_, ?_,
    ⟨#v[0, 1, 0], by native_decide, rowValuesBelow_of_all _ (by native_decide)⟩,
    ⟨#v[0, 1], by native_decide⟩⟩
  · rw [anchorData_romRows]
    intro row hrow
    rw [List.mem_singleton] at hrow
    subst hrow
    exact rowValuesBelow_of_all _ (by native_decide)
  · rw [anchorData_imageRows]
    intro row hrow
    exact absurd hrow (List.not_mem_nil)
  · rw [anchorData_imageRows]
    simp

/-! ## The empty-shard witness: 38 zero-row tables over the canonical data -/

/-- A zero-row table for one ensemble component. -/
def emptyTableOf (c : Component (ZMod SP1Prime)) : Table (ZMod SP1Prime) where
  component := c
  width := 0
  table := []
  data := anchorData
  uniform_width := by simp

/-- The 38 zero-row tables in the stable ensemble layout. -/
noncomputable def emptyTables : List (Table (ZMod SP1Prime)) :=
  (sp1Ensemble (p := SP1Prime)).tables.map emptyTableOf

theorem emptyTables_table_eq_nil : ∀ t ∈ emptyTables, t.table = [] := by
  intro t ht
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp ht
  rfl

/-- **The empty shard**: every mapped table has zero rows, the shared data is the canonical
committed program, and the public input is the equal-endpoints boundary. -/
noncomputable def emptyWitness : SupportedCoreNativeWitness SP1Prime where
  tables := emptyTables
  data := anchorData
  publicInput := pv
  same_length := by simp [emptyTables]
  same_circuits := by
    intro i hi
    simp [emptyTables, emptyTableOf]
  same_data := by
    intro t ht
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp ht
    rfl

@[simp] theorem emptyWitness_tables : emptyWitness.tables = emptyTables := rfl
@[simp] theorem emptyWitness_data : emptyWitness.data = anchorData := rfl
@[simp] theorem emptyWitness_publicInput : emptyWitness.publicInput = pv := rfl

/-! ## Conjunct 1a: constraints

The 38 mapped tables are constraint-satisfied vacuously (zero rows).  The verifier row's
operations are two State-channel interacts and no assertions/lookups; the State channel's local
guarantee is `True`, so its `ConstraintsHold` discharges by `circuit_norm` reduction. -/

theorem emptyWitness_constraints : emptyWitness.Constraints := by
  refine (EnsembleWitness.forall_mem_allTables_iff _ _).mpr ⟨?_, ?_⟩
  · rw [← EnsembleWitness.verifierConstraints_iff_verifierTable_constraints]
    show ((sp1Ensemble (p := SP1Prime)).verifierOperations).ConstraintsHold
      (.fromInput pv anchorData)
    show ((sp1StateVerifierMain (varFromOffset SP1PublicIO 0)).operations
      (size SP1PublicIO)).ConstraintsHold (.fromInput pv anchorData)
    simp [circuit_norm, sp1StateVerifierMain, Channels.stateChannel]
  · intro t ht row hrow
    rw [emptyTables_table_eq_nil t ht] at hrow
    exact absurd hrow (List.not_mem_nil)

/-! ## Conjunct 1b: four-bus balance

Zero-row tables contribute no interactions.  The verifier contributes nothing on the Byte, Program,
and Memory channels, and exactly the final-pull/initial-push pair on the State channel; with
initial = final endpoints the two are the same message with multiplicities `-1` and `1`. -/

/-- A pull/push pair of one message balances: the multiplicities cancel pointwise. -/
theorem balancedInteractions_pair {F : Type} [FiniteField F] [DecidableEq F]
    {i₁ i₂ : Interaction F} (hmsg : i₁.msg = i₂.msg) (hmult : i₁.mult + i₂.mult = 0)
    (hchar : (2 : ℕ) < ringChar F ∨ ringChar F = 0) :
    BalancedInteractions [i₁, i₂] := by
  constructor
  · rcases hchar with h | h
    · exact Or.inl (by simpa using h)
    · exact Or.inr h
  · intro msg
    rw [balanceOf_cons, balanceOf_cons]
    have hnil : balanceOf ([] : List (Interaction F)) msg = 0 := rfl
    rw [hnil, add_zero]
    by_cases h : i₁.msg = msg
    · rw [if_pos h, if_pos (hmsg.symm.trans h)]
      exact hmult
    · rw [if_neg h, if_neg (fun hc => h (hmsg.trans hc))]
      exact add_zero 0

/-- The empty interaction list balances (over a positive-characteristic field). -/
theorem balancedInteractions_nil {F : Type} [FiniteField F] [DecidableEq F]
    (hchar : (0 : ℕ) < ringChar F ∨ ringChar F = 0) :
    BalancedInteractions ([] : List (Interaction F)) := by
  constructor
  · rcases hchar with h | h
    · exact Or.inl (by simpa using h)
    · exact Or.inr h
  · intro msg
    rfl

theorem sp1Prime_char_pos_facts :
    (2 : ℕ) < ringChar (ZMod SP1Prime) ∧ (0 : ℕ) < ringChar (ZMod SP1Prime) := by
  rw [ZMod.ringChar_zmod_n]
  norm_num [SP1Prime]

/-- Zero-row tables emit no typed interactions on any channel. -/
theorem emptyTables_flatMap_nil {Message : TypeMap} [ProvableType Message]
    (channel : Channel (ZMod SP1Prime) Message) :
    emptyTables.flatMap (typedTableInteractionsWith · channel) = [] := by
  rw [List.flatMap_eq_nil_iff]
  intro t ht
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp ht
  rfl

/-- The verifier declares only the State channel, so its Byte contribution is empty (the Byte twin
of `witness_verifierProgramInteractions_eq_nil`). -/
theorem emptyWitness_verifierByte_nil :
    typedTableInteractionsWith emptyWitness.verifierTable byteChannel = [] := by
  apply List.map_eq_nil_iff.mp
  rw [typedTableInteractionsWith_raw]
  apply Table.interactionsWith_nil_of_channel_not_mem
  change byteChannel.toRaw ∉ [stateChannel.toRaw]
  simp [Channels.byteChannel_eq_stateChannel_false]

/-- The whole empty-shard State-channel view: exactly the boundary pull/push pair. -/
theorem emptyWitness_typedState :
    typedEnsembleInteractionsWith emptyWitness stateChannel =
      [TypedInteraction.pulledIfValue stateChannel 1
        ⟨pv.final_clk_high, pv.final_clk_low, pv.final_pc0, pv.final_pc1, pv.final_pc2⟩,
       TypedInteraction.pushedIfValue stateChannel 1
        ⟨pv.init_clk_high, pv.init_clk_low, pv.init_pc0, pv.init_pc1, pv.init_pc2⟩] := by
  show (emptyWitness.verifierTable :: emptyWitness.tables).flatMap
    (typedTableInteractionsWith · stateChannel) = _
  simp only [List.flatMap_cons]
  rw [witness_verifierStateInteractions_eq, emptyWitness_tables, emptyTables_flatMap_nil,
    List.append_nil]
  rfl

/-- The empty-shard Byte-channel view is empty. -/
theorem emptyWitness_typedByte :
    typedEnsembleInteractionsWith emptyWitness byteChannel = [] := by
  show (emptyWitness.verifierTable :: emptyWitness.tables).flatMap
    (typedTableInteractionsWith · byteChannel) = _
  simp only [List.flatMap_cons]
  rw [emptyWitness_verifierByte_nil, emptyWitness_tables, emptyTables_flatMap_nil]
  rfl

/-- The empty-shard Program-channel view is empty. -/
theorem emptyWitness_typedProgram :
    typedEnsembleInteractionsWith emptyWitness programChannel = [] := by
  show (emptyWitness.verifierTable :: emptyWitness.tables).flatMap
    (typedTableInteractionsWith · programChannel) = _
  simp only [List.flatMap_cons]
  rw [witness_verifierProgramInteractions_eq_nil, emptyWitness_tables, emptyTables_flatMap_nil]
  rfl

/-- The empty-shard Memory-channel view is empty. -/
theorem emptyWitness_typedMemory :
    typedEnsembleInteractionsWith emptyWitness memoryChannel = [] := by
  show (emptyWitness.verifierTable :: emptyWitness.tables).flatMap
    (typedTableInteractionsWith · memoryChannel) = _
  simp only [List.flatMap_cons]
  rw [witness_verifierMemoryInteractions_eq_nil, emptyWitness_tables, emptyTables_flatMap_nil]
  rfl

theorem emptyWitness_balanced : emptyWitness.BalancedChannels := by
  intro channel hchannel
  rw [sp1Ensemble_channels] at hchannel
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hchannel
  rcases hchannel with rfl | rfl | rfl | rfl
  · show BalancedInteractions (emptyWitness.interactionsWith stateChannel.toRaw)
    rw [← typedEnsembleInteractionsWith_raw, emptyWitness_typedState]
    simp only [List.map_cons, List.map_nil, TypedInteraction.pulledIfValue_raw,
      TypedInteraction.pushedIfValue_raw]
    exact balancedInteractions_pair rfl (neg_add_cancel 1)
      (Or.inl sp1Prime_char_pos_facts.1)
  · show BalancedInteractions (emptyWitness.interactionsWith byteChannel.toRaw)
    rw [← typedEnsembleInteractionsWith_raw, emptyWitness_typedByte, List.map_nil]
    exact balancedInteractions_nil (Or.inl sp1Prime_char_pos_facts.2)
  · show BalancedInteractions (emptyWitness.interactionsWith programChannel.toRaw)
    rw [← typedEnsembleInteractionsWith_raw, emptyWitness_typedProgram, List.map_nil]
    exact balancedInteractions_nil (Or.inl sp1Prime_char_pos_facts.2)
  · show BalancedInteractions (emptyWitness.interactionsWith memoryChannel.toRaw)
    rw [← typedEnsembleInteractionsWith_raw, emptyWitness_typedMemory, List.map_nil]
    exact balancedInteractions_nil (Or.inl sp1Prime_char_pos_facts.2)

/-! ## The concrete initial Sail state

`configuredState 0x10000` (the reusable W6b witness machinery) with the four little-endian bytes of
the self-jump word loaded at `0x10000..0x10003`, so `RomLoaded` holds with content. -/

/-- The witness memory: the four instruction bytes of `JAL x0, 0` at `0x10000`. -/
noncomputable def anchorMem : Std.ExtHashMap ℕ (BitVec 8) :=
  (((((configuredState (65536#64)).mem.insert 65536 (0x6F : BitVec 8)).insert
    65537 (0x00 : BitVec 8)).insert 65538 (0x00 : BitVec 8)).insert 65539 (0x00 : BitVec 8))

/-- The concrete initial state: every register initialized, pc pinned to the self-jump, machine
mode, SP1 PMA region, and the instruction bytes in memory. -/
noncomputable def anchorState : SailState :=
  { configuredState (65536#64) with mem := anchorMem }

theorem anchorMem_65536 : anchorMem.get? 65536 = some (0x6F : BitVec 8) := by
  show anchorMem[(65536 : ℕ)]? = some (0x6F : BitVec 8)
  unfold anchorMem
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by decide), Std.ExtHashMap.getElem?_insert,
    if_neg (by decide), Std.ExtHashMap.getElem?_insert, if_neg (by decide),
    Std.ExtHashMap.getElem?_insert, if_pos (by decide)]

theorem anchorMem_65537 : anchorMem.get? 65537 = some (0x00 : BitVec 8) := by
  show anchorMem[(65537 : ℕ)]? = some (0x00 : BitVec 8)
  unfold anchorMem
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by decide), Std.ExtHashMap.getElem?_insert,
    if_neg (by decide), Std.ExtHashMap.getElem?_insert, if_pos (by decide)]

theorem anchorMem_65538 : anchorMem.get? 65538 = some (0x00 : BitVec 8) := by
  show anchorMem[(65538 : ℕ)]? = some (0x00 : BitVec 8)
  unfold anchorMem
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by decide), Std.ExtHashMap.getElem?_insert,
    if_pos (by decide)]

theorem anchorMem_65539 : anchorMem.get? 65539 = some (0x00 : BitVec 8) := by
  show anchorMem[(65539 : ℕ)]? = some (0x00 : BitVec 8)
  unfold anchorMem
  rw [Std.ExtHashMap.getElem?_insert, if_pos (by decide)]

theorem anchorState_pc : anchorState.regs.get? Register.PC = some (65536#64) :=
  cfgState_pc (65536#64)

/-- The full platform configuration of `configuredState`, generalized over the pc (the inline
`configured` block of `isInitialState_nonvacuous`, made reusable). -/
theorem configuredState_sailConfigured (pc : BitVec 64) : SailConfigured (configuredState pc) where
  init := cfgState_init pc
  priv := cfgState_priv pc
  active := by
    rw [cfgState_get?_other pc Register.hart_state (by decide) (by decide) (by decide) (by decide)]
    rfl
  mie := by
    rw [cfgState_get_other pc Register.mstatus (by decide) (by decide) (by decide) (by decide)]
    exact (by decide : _get_Mstatus_MIE (default : RegisterType Register.mstatus) = 0#1)
  mideleg := by
    rw [cfgState_get_other pc Register.mideleg (by decide) (by decide) (by decide) (by decide)]
    exact (by decide : (default : RegisterType Register.mideleg) = zeros)
  no_landing_pad := by
    rw [cfgState_get?_other pc Register.elp (by decide) (by decide) (by decide) (by decide)]
    exact (by decide : ¬ (some (default : RegisterType Register.elp)
      = some (landing_pad_bits_backwards landing_pad_expectation.LP_EXPECTED)))
  mprv_disabled := by
    rw [cfgState_get_other pc Register.mstatus (by decide) (by decide) (by decide) (by decide)]
    exact (by decide :
      BitVec.ofNat 1 ((default : RegisterType Register.mstatus).toNat >>> 17) = 0#1)
  mseccfg_disabled := by
    rw [cfgState_get_other pc Register.mseccfg (by decide) (by decide) (by decide) (by decide)]
    exact (by decide :
      BitVec.ofNat 1 ((default : RegisterType Register.mseccfg).toNat >>> 10) = 0#1)
  mseccfg_pmm := by
    rw [cfgState_get_other pc Register.mseccfg (by decide) (by decide) (by decide) (by decide)]
    exact (by decide :
      BitVec.ofNat 2 ((default : RegisterType Register.mseccfg).toNat >>> 32) = 0#2)
  htif_disabled := by
    rw [cfgState_get_other pc Register.htif_tohost_base (by decide) (by decide) (by decide)
      (by decide)]
    exact (by decide : (default : RegisterType Register.htif_tohost_base) = none)
  pmp_off := by
    rw [cfgState_get_other pc Register.pmpcfg_n (by decide) (by decide) (by decide) (by decide)]
    exact (by decide : (default : RegisterType Register.pmpcfg_n) = Vector.replicate 64 0#8)
  misa_m := by
    rw [cfgState_misa pc _]
    decide
  pma_regions := cfgState_pma pc _

/-- The enriched state keeps the register-only configuration (the memory update is invisible to
every `SailConfigured` field). -/
theorem anchorState_configured : SailConfigured anchorState :=
  let base := configuredState_sailConfigured (65536#64)
  { init := base.init
    priv := base.priv
    active := base.active
    mie := base.mie
    mideleg := base.mideleg
    no_landing_pad := base.no_landing_pad
    mprv_disabled := base.mprv_disabled
    mseccfg_disabled := base.mseccfg_disabled
    mseccfg_pmm := base.mseccfg_pmm
    htif_disabled := base.htif_disabled
    pmp_off := base.pmp_off
    misa_m := base.misa_m
    pma_regions := base.pma_regions }

/-- The committed ROM's bytes are loaded in the witness state, little-endian. -/
theorem anchorState_romLoaded : RomLoaded anchorProgram anchorState := by
  intro a w hf i
  obtain ⟨rfl, rfl⟩ := anchorProgram_fetchWord hf
  fin_cases i
  · exact anchorMem_65536
  · exact anchorMem_65537
  · exact anchorMem_65538
  · exact anchorMem_65539

/-! ## Conjunct 2: the semantic boundary binding -/

/-- The provider tables of the empty shard have zero rows. -/
theorem emptyWitness_mem_tables_table_nil : ∀ t ∈ emptyWitness.tables, t.table = [] :=
  emptyTables_table_eq_nil

theorem programProviderTable_table_nil :
    (programProviderTable (p := SP1Prime) emptyWitness).table = [] := by
  apply emptyWitness_mem_tables_table_nil
  exact List.getElem_mem _

theorem memoryInitProviderTable_table_nil :
    (memoryInitProviderTable (p := SP1Prime) emptyWitness).table = [] := by
  apply emptyWitness_mem_tables_table_nil
  exact List.getElem_mem _

theorem memoryFinalizeProviderTable_table_nil :
    (memoryFinalizeProviderTable (p := SP1Prime) emptyWitness).table = [] := by
  apply emptyWitness_mem_tables_table_nil
  exact List.getElem_mem _

theorem emptyWitness_programProviderBound : ProgramProviderBound (p := SP1Prime) emptyWitness := by
  intro interaction member _
  exfalso
  simp only [Table.interactionsWith, programProviderTable_table_nil, List.flatMap_nil] at member
  exact absurd member (List.not_mem_nil)

theorem emptyWitness_memoryInitProviderBound :
    MemoryInitProviderBound (p := SP1Prime) emptyWitness anchorState
      (Commit.initClkNat anchorData) := by
  intro interaction member _
  exfalso
  simp only [Table.interactionsWith, memoryInitProviderTable_table_nil,
    List.flatMap_nil] at member
  exact absurd member (List.not_mem_nil)

theorem emptyWitness_memoryInitProviderUnique :
    MemoryInitProviderUnique (p := SP1Prime) emptyWitness := by
  show (typedTableInteractionsWith (memoryInitProviderTable emptyWitness) memoryChannel).Pairwise _
  rw [typedTableInteractionsWith, memoryInitProviderTable_table_nil, List.flatMap_nil]
  exact List.Pairwise.nil

theorem emptyWitness_memoryFinalizeProviderUnique :
    MemoryFinalizeProviderUnique (p := SP1Prime) emptyWitness := by
  show (typedTableInteractionsWith (memoryFinalizeProviderTable emptyWitness)
    memoryChannel).Pairwise _
  rw [typedTableInteractionsWith, memoryFinalizeProviderTable_table_nil, List.flatMap_nil]
  exact List.Pairwise.nil

/-- The public pc limbs recombine to the self-jump address. -/
theorem supportedPcBits_anchor :
    supportedPcBits (0 : ZMod SP1Prime) 1 0 = 65536#64 := by native_decide

/-! ### Closing `SailCodeMemoryCompatible`: the self-jump step invariant

`JAL x0, 0` jumps to its own address and commits no register write and no memory write, so every
reachable Sail state keeps pc `0x10000`, the ROM bytes, and the platform configuration.  One
application of the proved `advance_of_jal_x0` per step, plus determinism of the `EStateM`
interpreter run, closes the boundary contract outright — no preservation assumption remains. -/

/-- A zeroed register-access block (gated off on the J-type row; never read by `advance`). -/
def zeroAccess : Extracted.RegisterAccessCols (ZMod SP1Prime) := ⟨#v[0, 0, 0, 0], ⟨0, 0⟩⟩

/-- The row view of the committed self-jump: opcode JAL, destination `x0`, immediate `op_b = 0`,
current and next pc both `0x10000`, no commit effect. -/
def jalView : Trace.RowView (ZMod SP1Prime) where
  state := { clk_high := 0, clk_16_24 := 0, clk_0_16 := 1, pc := #v[0, 1, 0] }
  next_pc := #v[0, 1, 0]
  adapter :=
    { op_a := 0, op_a_memory := zeroAccess, op_a_0 := 1,
      op_b := bitVecToWord ((0#21 : BitVec 21).signExtend 64), op_b_memory := zeroAccess,
      imm_b := 1,
      op_c := #v[0, 0, 0, 0], op_c_memory := zeroAccess, imm_c := 1 }
  is_real := 1
  rdWrite := #v[0, 0, 0, 0]
  opcode := ((Opcode.JAL).toNat : ZMod SP1Prime)
  commit := .noWrite

theorem jalView_rcvPc : rcvPcOf (stateAccess jalView) = 65536#64 := by native_decide

theorem jalView_sndPc : sndPcOf (stateAccess jalView) = 65536#64 := by native_decide

/-- The official decoder on the committed word `0x0000006F` is `JAL x0, 0` (the `decode_JAL`
recipe of `Model/SailDecode.lean`, at the self-jump word). -/
theorem decode_jal_x0 (s : SailState) (hs : s.isInitialized)
    (hpriv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hseccfg :
      BitVec.ofNat 1 ((s.regs.get Register.mseccfg (hs Register.mseccfg)).toNat >>> 10) = 0#1) :
    (ext_decode 0x0000006F#32).run s
      = .ok (instruction.JAL (0#21, regidx.Regidx 0#5)) s := by
  conv_lhs => whnf
  rw [SailDecode.cePause_apply]
  conv_lhs => whnf
  rw [SailDecode.ceZicfilp_bind_apply s hs hpriv hseccfg]
  conv_lhs => whnf
  rfl

/-- The committed Program row of the self-jump view is the decode of the fetched ROM word. -/
theorem jalView_decodedInROM :
    decodedInROM (p := SP1Prime) anchorProgram (programAccess jalView).toRow := by
  refine ⟨0x0000006F#32, .JAL (0#21, .Regidx 0#5), ?_, ?_, ?_⟩
  · native_decide
  · intro s hs
    exact decode_jal_x0 s hs.init hs.priv hs.mseccfg_disabled
  · rfl

/-- The persistent step invariant: pc at the self-jump, ROM loaded, configuration intact. -/
def AnchorInv (s : SailState) : Prop :=
  s.regs.get? Register.PC = some (65536#64) ∧ RomLoaded anchorProgram s ∧ SailConfigured s

theorem anchorInv_base : AnchorInv anchorState :=
  ⟨anchorState_pc, anchorState_romLoaded, anchorState_configured⟩

/-- One interpreter step from an invariant state re-establishes the invariant: the step is the
committed self-jump (`advance_of_jal_x0` plus determinism of the `EStateM` run), whose `RowEffect`
commits pc `0x10000` with no register write, no memory write, and configuration persistence. -/
theorem anchorInv_step {s next : SailState} (inv : AnchorInv s) (step : SailStep s next) :
    AnchorInv next := by
  obtain ⟨hpc, hrom, hcfg⟩ := inv
  obtain ⟨s', hstep', heff⟩ :=
    Advance.advance_of_jal_x0 (p := SP1Prime) (prog := anchorProgram) (r := jalView)
      hcfg hrom (by rw [jalView_rcvPc]; exact hpc) jalView_decodedInROM rfl rfl rfl
      (by rw [jalView_sndPc]; decide)
      (fun imm hb => by
        have hb' : bitVecToWord (p := SP1Prime) ((0#21 : BitVec 21).signExtend 64) =
            bitVecToWord (imm.signExtend 64) := hb
        have h64 := congrArg Word.toBitVec64 hb'
        rw [toBitVec64_bitVecToWord, toBitVec64_bitVecToWord] at h64
        rw [jalView_rcvPc, jalView_sndPc,
          show sign_extend (m := 64) imm = imm.signExtend 64 from rfl, ← h64]
        decide)
  obtain ⟨b, hb⟩ := step
  obtain ⟨b', hb'⟩ := hstep'
  have hnext : next = s' := by
    have hok := hb.symm.trans hb'
    injection hok
  subst hnext
  refine ⟨?_, ?_, heff.cfg hcfg⟩
  · rw [heff.pc, jalView_sndPc]
  · intro a w hf i
    rw [heff.mem.1 rfl]
    exact hrom a w hf i

theorem anchorInv_of_chain {n : ℕ} {a b : SailState}
    (inva : AnchorInv a) (chain : Target.SailChain n a b) : AnchorInv b := by
  induction chain with
  | refl s => exact inva
  | step h1 _ ih => exact ih (anchorInv_step inva h1)

/-- ROM preservation along every reachable Sail step: reachable states satisfy the self-jump
invariant, and each further step re-establishes it — in particular `RomLoaded` persists. -/
theorem anchor_codeMemoryCompatible : SailCodeMemoryCompatible anchorProgram anchorState := by
  intro n state next chain step _hromState
  exact (anchorInv_step (anchorInv_of_chain anchorInv_base chain) step).2.1

/-- The full boundary bundle at the concrete initial state. -/
theorem anchorBoundaryFacts : InitialBoundaryFacts stmt emptyWitness anchorState where
  programWellFormed := anchorProgram_wellFormed
  programCommitted := ⟨anchorData_canonicalEncoding, rfl⟩
  initialPc := by
    show anchorState.regs.get? Register.PC = some (supportedPcBits (0 : ZMod SP1Prime) 1 0)
    rw [supportedPcBits_anchor]
    exact anchorState_pc
  initialClock := by
    show Commit.initClkNat anchorData = Semantics.clkNat pv.init_clk_high pv.init_clk_low
    native_decide
  romLoaded := anchorState_romLoaded
  configured := anchorState_configured
  codeMemoryCompatible := anchor_codeMemoryCompatible
  programProvider := emptyWitness_programProviderBound
  memoryProvider := emptyWitness_memoryInitProviderBound
  memoryProviderUnique := emptyWitness_memoryInitProviderUnique
  memoryFinalizeProviderUnique := emptyWitness_memoryFinalizeProviderUnique

/-! ## Conjunct 3: the memory-timestamp range companion (vacuous over zero rows) -/

/-- Decoding pairs of chips with zero-row tables yields no rows. -/
theorem decodeInstructionTables_eq_nil {chips : List (SupportedChip SP1Prime)}
    {tables : List (Table (ZMod SP1Prime))} (h : ∀ t ∈ tables, t.table = []) :
    decodeInstructionTables chips tables = [] := by
  induction chips generalizing tables with
  | nil => cases tables <;> rfl
  | cons chip chips ih =>
    cases tables with
    | nil => rfl
    | cons t ts =>
      show t.table.map _ ++ decodeInstructionTables chips ts = []
      rw [h t List.mem_cons_self]
      simp only [List.map_nil, List.nil_append]
      exact ih fun t' ht' => h t' (List.mem_cons_of_mem _ ht')

theorem emptyWitness_realDecodedInstructionRows_nil :
    realDecodedInstructionRows anchorData emptyWitness.tables = [] := by
  show (decodeInstructionTables (supportedChips (p := SP1Prime))
    (emptyWitness.tables.take 25)).filter _ = []
  rw [decodeInstructionTables_eq_nil
    (fun t ht => emptyWitness_mem_tables_table_nil t (List.mem_of_mem_take ht))]
  rfl

theorem emptyWitness_memoryTimestampRange :
    SupportedCoreMemoryTimestampRangeRelation (p := SP1Prime) stmt emptyWitness := by
  intro decoded mem
  rw [show emptyWitness.data = anchorData from rfl,
    emptyWitness_realDecodedInstructionRows_nil] at mem
  exact absurd mem (List.not_mem_nil)

/-! ## The joint witness -/

/-- **Joint non-vacuity of the capstone's hypothesis bundle.**  The empty shard with equal public
State endpoints satisfies the complete `SupportedCoreNativeRelation` at the concrete prime: the
raw ensemble relation (constraints + four-bus balance), the semantic boundary binding (with the
committed one-instruction program and the concrete configured initial state), and the
memory-timestamp range companion.  Applying `supported_core_native_sound` to this witness yields
the honest 0-step local Sail execution between the equal endpoints. -/
theorem supportedCoreNativeRelation_nonvacuous :
    SupportedCoreNativeRelation (p := SP1Prime) stmt emptyWitness :=
  ⟨⟨rfl, emptyWitness_constraints, emptyWitness_balanced⟩,
   ⟨anchorState, anchorBoundaryFacts⟩,
   emptyWitness_memoryTimestampRange⟩

end SP1Clean.Audit.JointNonVacuity
