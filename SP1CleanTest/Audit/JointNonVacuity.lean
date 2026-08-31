import SP1Clean.Soundness.AIR
import SP1Clean.FormalModel.Trace.Witness
import SP1Clean.Proofs.Sail.Advance
import SP1Clean.Model.SailDecode
import SP1CleanTest.TraceGenTests.Conformance

/-! # Joint non-vacuity: the capstone's hypothesis bundle is satisfiable

The external PR110 report's Finding 3 asks whether the capstone's **full** hypothesis bundle —
`SupportedCoreNativeRelation` (constraints ∧ four-bus balance ∧ the semantic boundary binding) — is
**jointly** satisfiable, or whether some conjunction of
boundary fields is silently contradictory.  This file exhibits a fully proved witness at the
concrete prime (KoalaBear, `SP1Prime`): the **boundary-only shard** — all 25 instruction tables and
26 of the 29 boundary/provider tables have zero rows, and the boundary verifier row carries a
public State record with **equal initial and final endpoints** (clk `(0, 1)`, pc `0x10000` at both
ends, committed in the W3 D5-A split-limb form), so its final-state pull and initial-state push are
the same State message and cancel exactly.

Since W3 D5-A the verifier row also pulls the twelve Byte-bus range checks of the split public
limbs, so the shard is no longer channel-empty: two provider tables carry honest in-circuit rows
whose pushes balance those pulls exactly.  `RangeChip.circuitFor ⟨16, …⟩` (stable position 47) checks
`a = 1` and `a = 0` in-circuit and pushes `⟨6, 1, 16, 0⟩` with multiplicity 4 and `⟨6, 0, 16, 0⟩`
with multiplicity 6; `ByteChip.U8Range.circuit` (stable position 25) checks the byte pair `(0, 0)`
and pushes `⟨3, 0, 0, 0⟩` with multiplicity 2.  Together they cancel the verifier's twelve `-1`
pulls (four `⟨6, 1, 16, 0⟩`, six `⟨6, 0, 16, 0⟩`, two `⟨3, 0, 0, 0⟩`) message-for-message.

Since the halt wave the verifier row also pulls `⟨exit_code⟩` **ungated** on the fifth (Exit) bus,
and every shard's Halt table (stable position 53) carries exactly one row pushing the gated hand-off
pair `is_real · ⟨reduce(x10)⟩` and `(1 - is_real) · ⟨0⟩`.  A shard whose Halt table is empty cannot
balance the Exit bus at all, so the joint witness carries the mandatory **Halt padding table**: one
all-zero row, whose `1 - 0 = 1` push of `⟨0⟩` cancels the verifier's `-1` pull of the committed
`exit_code = 0`.  Its selector being off, each of its other eighteen interactions (State, Byte,
Program, Memory) sits at multiplicity zero and so moves no other bus's balance.

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

**What this deliberately does NOT claim**: this boundary-only witness itself contains an active
instruction. `Audit/ActiveTraceNonVacuity.lean` separately supplies one hand-assembled JAL event
with circuit-built physical rows and balanced provider content. General Sail-to-trace generation
for arbitrary executions remains the machine-completeness workstream (`docs/roadmap.md`). The
capstone applied to this witness yields the honest 0-step local execution between the equal public
endpoints. -/

open LeanRV64D.Defs

namespace SP1Clean.Audit.JointNonVacuity

open Air.Flat Circuit
open SP1Clean SP1Clean.TraceGenTests
open SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Execution
open SP1Clean.Channels (stateChannel byteChannel programChannel memoryChannel exitChannel)
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
both ends), in the split-limb field order `clk_0_16, clk_16_24, clk_24_32, clk_32_48, pc0, pc1,
pc2` per end.  The recombination projections then give `init_clk_high = 0`, `init_clk_low = 1`
(and the same finally), so the verifier row's final-state pull and initial-state push are the same
State message with cancelling multiplicities, exactly as before the split. -/
def pv : SP1StateBoundary (ZMod SP1Prime) :=
  ⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, Vector.replicate 32 0⟩

/-- The public statement of the boundary-only shard. -/
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
    ⟨#v[0, 1], by native_decide, rowValuesBelow_of_all _ (by native_decide)⟩⟩
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

/-! ## The joint witness: 51 zero-row tables, the two Byte providers, and the Halt padding row

Every table except the two byte providers and the Halt table has zero rows. The provider rows are
honest witnesses of their circuits: input cells first (`ProvableType` order, including the explicit
multiplicity), then the `rangeCheck n` subcircuits' local bit-decomposition cells in emission
order. -/

/-- A zero-row table for one ensemble component. -/
def emptyTableOf (c : Component (ZMod SP1Prime)) : Table (ZMod SP1Prime) where
  component := c
  width := 0
  table := []
  data := anchorData
  uniform_width := by simp

/-- The 54 zero-row tables in the stable ensemble layout — the all-empty template the joint
witness patches at the two byte-provider positions and the Halt position. -/
noncomputable def emptyTables : List (Table (ZMod SP1Prime)) :=
  (sp1Ensemble (p := SP1Prime)).tables.map emptyTableOf

theorem emptyTables_table_eq_nil : ∀ t ∈ emptyTables, t.table = [] := by
  intro t ht
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp ht
  rfl

theorem emptyTables_data : ∀ t ∈ emptyTables, t.data = anchorData := by
  intro t ht
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp ht
  rfl

theorem emptyTables_length : emptyTables.length = 54 := by
  simp only [emptyTables, List.length_map, sp1Ensemble_tables, List.length_append]
  rfl

/-- The `U8Range` provider table (stable position 25): one row checking the byte pair `(0, 0)` and
pushing `⟨3, 0, 0, 0⟩` with multiplicity 2. Row layout: `[b, c, multiplicity]`, then the two
`rangeCheck 8` bit blocks (all zero). -/
def u8RangeTable : Table (ZMod SP1Prime) where
  component := ⟨ByteChip.U8Range.circuit⟩
  width := 19
  table := [#[0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
  data := anchorData
  uniform_width := by intro row hrow; fin_cases hrow; rfl

/-- The width-16 `RangeChip` provider table (stable position 47): two rows checking `a = 1` and
`a = 0`, pushing `⟨6, 1, 16, 0⟩` with multiplicity 4 and `⟨6, 0, 16, 0⟩` with multiplicity 6.  Row
layout: `[a, multiplicity]`, then the `rangeCheck 16` bit block (little-endian, so `a = 1` sets
exactly the first bit). -/
def rangeWidth16 : RangeChip.Width := ⟨16, by norm_num⟩

def range16Table : Table (ZMod SP1Prime) where
  component := ⟨RangeChip.circuitFor rangeWidth16⟩
  width := 18
  table := [#[1, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            #[0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
  data := anchorData
  uniform_width := by intro row hrow; fin_cases hrow <;> rfl

/-- The all-zero Halt row: the `size HaltChip.Inputs = 25` input cells (the halt circuit declares
`localLength := 0`, so it owns no witness cells beyond them), i.e. `HaltChip.paddingInputs` in
physical form. -/
def haltPaddingRow : Array (ZMod SP1Prime) := Array.replicate 25 0

/-- The mandatory Halt table (stable position 53): exactly one padding row. Its selector is off, so
the composed `CPUState`/`RegisterAccessCols` Byte pulls, the State pair, the ECALL Program fetch and
the six register Memory records are all emitted at multiplicity zero; only the anti-gated
`1 - is_real = 1` Exit push of `⟨0⟩` is live, and that is what balances the boundary verifier's
ungated `⟨exit_code⟩` pull. -/
def haltPaddingTable : Table (ZMod SP1Prime) where
  component := ⟨HaltChip.circuit⟩
  width := 25
  table := [haltPaddingRow]
  data := anchorData
  uniform_width := by intro row hrow; fin_cases hrow; rfl

/-- The 54 mapped tables of the joint shard: the all-empty template with the two byte-provider
positions and the Halt position patched (25 = `U8Range`, 47 = `Range16`, 53 = `Halt`, matching
`sp1ProviderTables` order). -/
noncomputable def jointTables : List (Table (ZMod SP1Prime)) :=
  ((emptyTables.set 25 u8RangeTable).set 47 range16Table).set 53 haltPaddingTable

theorem mem_jointTables {t : Table (ZMod SP1Prime)} (ht : t ∈ jointTables) :
    t ∈ emptyTables ∨ t = u8RangeTable ∨ t = range16Table ∨ t = haltPaddingTable := by
  rcases List.mem_or_eq_of_mem_set ht with h | rfl
  · rcases List.mem_or_eq_of_mem_set h with h | rfl
    · rcases List.mem_or_eq_of_mem_set h with h | rfl
      exacts [Or.inl h, Or.inr (Or.inl rfl)]
    · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

theorem jointTables_length : jointTables.length = 54 := by
  simp only [jointTables, List.length_set]
  exact emptyTables_length

/-- Generic: `flatMap` over a single-`set` list whose other elements all map to `[]`. -/
theorem flatMap_set_of_nil {α β : Type*} {l : List α} {f : α → List β} {i : ℕ} {a : α}
    (hi : i < l.length) (hnil : ∀ x ∈ l, f x = []) :
    (l.set i a).flatMap f = f a := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [List.set_cons_zero, List.flatMap_cons]
      rw [List.flatMap_eq_nil_iff.mpr fun y hy => hnil y (List.mem_cons_of_mem _ hy),
        List.append_nil]
    | succ n =>
      simp only [List.set_cons_succ, List.flatMap_cons, hnil x List.mem_cons_self,
        List.nil_append]
      exact ih (by simpa using hi) fun y hy => hnil y (List.mem_cons_of_mem _ hy)

/-- Generic: `flatMap` over a double-`set` list (positions `i < j`) whose other elements all map
to `[]` is the two patched images in position order. -/
theorem flatMap_set_set_of_nil {α β : Type*} {l : List α} {f : α → List β} {i j : ℕ} {a b : α}
    (hij : i < j) (hj : j < l.length) (hnil : ∀ x ∈ l, f x = []) :
    ((l.set i a).set j b).flatMap f = f a ++ f b := by
  induction l generalizing i j with
  | nil => simp at hj
  | cons x xs ih =>
    cases j with
    | zero => omega
    | succ m =>
      cases i with
      | zero =>
        simp only [List.set_cons_zero, List.set_cons_succ, List.flatMap_cons]
        congr 1
        exact flatMap_set_of_nil (by simpa using hj)
          fun y hy => hnil y (List.mem_cons_of_mem _ hy)
      | succ n =>
        simp only [List.set_cons_succ, List.flatMap_cons, hnil x List.mem_cons_self,
          List.nil_append]
        exact ih (by omega) (by simpa using hj)
          fun y hy => hnil y (List.mem_cons_of_mem _ hy)

/-- Generic: `flatMap` over a triple-`set` list (positions `i < j < k`) whose other elements all map
to `[]` is the three patched images in position order. -/
theorem flatMap_set_set_set_of_nil {α β : Type*} {l : List α} {f : α → List β} {i j k : ℕ}
    {a b c : α} (hij : i < j) (hjk : j < k) (hk : k < l.length)
    (hnil : ∀ x ∈ l, f x = []) :
    (((l.set i a).set j b).set k c).flatMap f = f a ++ (f b ++ f c) := by
  induction l generalizing i j k with
  | nil => simp at hk
  | cons x xs ih =>
    cases k with
    | zero => omega
    | succ m =>
      cases j with
      | zero => omega
      | succ n =>
        cases i with
        | zero =>
          simp only [List.set_cons_zero, List.set_cons_succ, List.flatMap_cons]
          congr 1
          exact flatMap_set_set_of_nil (by omega) (by simpa using hk)
            fun y hy => hnil y (List.mem_cons_of_mem _ hy)
        | succ q =>
          simp only [List.set_cons_succ, List.flatMap_cons, hnil x List.mem_cons_self,
            List.nil_append]
          exact ih (by omega) (by omega) (by simpa using hk)
            fun y hy => hnil y (List.mem_cons_of_mem _ hy)

/-- **The joint shard**: 51 zero-row tables plus the two byte-provider tables and the Halt padding
table, the shared canonical committed program data, and the equal-endpoints public boundary. -/
noncomputable def jointWitness : SupportedCoreNativeWitness SP1Prime where
  tables := jointTables
  data := anchorData
  publicInput := pv
  same_length := by simp [jointTables, emptyTables]
  same_circuits := by
    intro i hi
    rcases eq_or_ne i 25 with rfl | h25
    · simp only [jointTables, List.getElem_set_ne (by omega : (53 : ℕ) ≠ 25),
        List.getElem_set_ne (by omega : (47 : ℕ) ≠ 25), List.getElem_set_self]
      rfl
    rcases eq_or_ne i 47 with rfl | h47
    · simp only [jointTables, List.getElem_set_ne (by omega : (53 : ℕ) ≠ 47),
        List.getElem_set_self]
      rfl
    rcases eq_or_ne i 53 with rfl | h53
    · simp only [jointTables, List.getElem_set_self]
      rfl
    · simp only [jointTables, List.getElem_set_ne (Ne.symm h53),
        List.getElem_set_ne (Ne.symm h47), List.getElem_set_ne (Ne.symm h25)]
      simp [emptyTables, emptyTableOf]
  same_data := by
    intro t ht
    rcases mem_jointTables ht with h | rfl | rfl | rfl
    · exact emptyTables_data t h
    · rfl
    · rfl
    · rfl

@[simp] theorem jointWitness_tables : jointWitness.tables = jointTables := rfl
@[simp] theorem jointWitness_data : jointWitness.data = anchorData := rfl
@[simp] theorem jointWitness_publicInput : jointWitness.publicInput = pv := rfl

/-- Positions other than the two byte providers and the Halt table keep zero rows — in particular
the stable provider/boundary positions 48/49/50 consumed by the semantic boundary bindings. -/
theorem jointTables_table_nil_of_ne (i : ℕ) (hi : i < jointTables.length)
    (h25 : i ≠ 25) (h47 : i ≠ 47) (h53 : i ≠ 53) : jointTables[i].table = [] := by
  have hmem : jointTables[i] ∈ emptyTables := by
    simp only [jointTables, List.getElem_set_ne (Ne.symm h53), List.getElem_set_ne (Ne.symm h47),
      List.getElem_set_ne (Ne.symm h25)]
    exact List.getElem_mem _
  exact emptyTables_table_eq_nil _ hmem

/-! ## Conjunct 1a: constraints

The 51 zero-row tables are constraint-satisfied vacuously.  The verifier row, the three concrete
provider rows and the Halt padding row are discharged by the executable whole-circuit check (the
`NonVacuityReal.lean` bridge, replicated here): no static lookups, and every flattened `assertZero`
expression — the `rangeCheck` bit decompositions included — evaluates to zero on the concrete
cells. -/

/-- Executable whole-circuit constraint check: no static lookups, and every `assertZero`
expression of the flattened operation list (subcircuits included) evaluates to zero. -/
def constraintsCheck (env : Environment (ZMod SP1Prime)) (ops : Operations (ZMod SP1Prime)) :
    Bool :=
  (FlatOperation.lookups ops.toFlat).isEmpty &&
    (FlatOperation.constraints ops.toFlat).all fun e => decide (Expression.eval env e = 0)

/-- Bridge from the executable check to Clean's `Operations.ConstraintsHold` — axiom-clean; the
concrete rows discharge the `constraintsCheck` premise by `native_decide`. -/
theorem constraintsHold_of_check {env : Environment (ZMod SP1Prime)}
    {ops : Operations (ZMod SP1Prime)} (h : constraintsCheck env ops = true) :
    ops.ConstraintsHold env := by
  rw [← Circuit.constraintsHold_toFlat_iff, FlatOperation.constraintsHoldFlat_iff_forall_mem]
  simp only [constraintsCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    List.isEmpty_iff] at h
  exact ⟨h.2, fun l hl => absurd hl (by simp [h.1])⟩

theorem jointWitness_constraints : jointWitness.Constraints := by
  refine (EnsembleWitness.forall_mem_allTables_iff _ _).mpr ⟨?_, ?_⟩
  · rw [← EnsembleWitness.verifierConstraints_iff_verifierTable_constraints]
    show ((sp1Ensemble (p := SP1Prime)).verifierOperations).ConstraintsHold
      (.fromInput pv anchorData)
    show ((sp1StateVerifierMain (varFromOffset SP1PublicIO 0)).operations
      (size SP1PublicIO)).ConstraintsHold (.fromInput pv anchorData)
    exact constraintsHold_of_check (by native_decide)
  · intro t ht row hrow
    rcases mem_jointTables ht with h | rfl | rfl | rfl
    · rw [emptyTables_table_eq_nil t h] at hrow
      exact absurd hrow (List.not_mem_nil)
    · fin_cases hrow
      exact constraintsHold_of_check (by native_decide)
    · fin_cases hrow
      · exact constraintsHold_of_check (by native_decide)
      · exact constraintsHold_of_check (by native_decide)
    · fin_cases hrow
      exact constraintsHold_of_check (by native_decide)

/-! ## Conjunct 1b: five-bus balance

Zero-row tables contribute no interactions.  On the State channel the verifier contributes exactly
the final-pull/initial-push pair, which cancels with initial = final endpoints; on the Byte channel
its twelve `-1` limb-range pulls cancel against the two provider tables' pushes (multiplicities
`4 + 6 + 2`); on the Exit channel its ungated `-1` pull of `⟨exit_code⟩ = ⟨0⟩` cancels against the
Halt padding row's anti-gated `+1` push of `⟨0⟩`; Program and Memory stay empty.  The Halt padding
row's remaining eighteen interactions are all gated off, so on the other four buses it only appends
multiplicity-zero entries. -/

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

/-- Multiplicity-zero interactions move no message's balance. -/
theorem balanceOf_eq_zero_of_mult_zero {l : List (Interaction (ZMod SP1Prime))}
    (h : ∀ i ∈ l, i.mult = 0) (msg : Array (ZMod SP1Prime)) : balanceOf l msg = 0 := by
  rw [balanceOf]
  refine List.sum_eq_zero fun m hm => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
  exact h i (List.mem_of_mem_filter hi)

theorem sp1Prime_char_pos_facts :
    (2 : ℕ) < ringChar (ZMod SP1Prime) ∧ (0 : ℕ) < ringChar (ZMod SP1Prime) := by
  rw [ZMod.ringChar_zmod_n]
  norm_num [SP1Prime]

/-- Balance follows from balance at the finitely many **member** messages: a message carried by no
interaction has every `if` in its `balanceOf` sum false.  This is what makes a concrete-list
balance decidable — `BalancedInteractions`' `∀ msg : Array F` must NOT be handed to
`decide`/`native_decide` directly (cf. the Fintype landmine at `rowValuesBelow_of_all`); the
bounded member form evaluates over just the list. -/
theorem balancedInteractions_of_member_balance {l : List (Interaction (ZMod SP1Prime))}
    (hlen : l.length < ringChar (ZMod SP1Prime))
    (h : ∀ msg ∈ l.map (·.msg), balanceOf l msg = 0) :
    BalancedInteractions l := by
  refine ⟨Or.inl hlen, fun msg => ?_⟩
  by_cases hmem : msg ∈ l.map (·.msg)
  · exact h msg hmem
  · have hfilter : l.filter (·.msg = msg) = [] := by
      rw [List.filter_eq_nil_iff]
      intro i hi hdec
      exact hmem (List.mem_map.mpr ⟨i, hi, of_decide_eq_true hdec⟩)
    rw [balanceOf, hfilter]
    rfl

/-- A table over a single-channel circuit filters nothing: its channel view is its whole
interaction list. -/
theorem table_interactionsWith_eq_interactions {t : Table (ZMod SP1Prime)}
    {ch : RawChannel (ZMod SP1Prime)}
    (h : ∀ c ∈ t.component.circuit.channels, c = ch) :
    t.interactionsWith ch = t.interactions := by
  rw [Table.interactionsWith_eq_filter]
  apply List.filter_eq_self.mpr
  intro i hi
  simp only [decide_eq_true_eq]
  obtain ⟨row, -, hrow⟩ := List.mem_flatMap.mp hi
  obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hrow
  rw [AbstractInteraction.eval_channel]
  apply h
  apply t.component.circuit.channels_subset t.component.rowInputVar t.component.rowOffset
  apply List.mem_map_of_mem
  exact Component.interactions_eq (component := t.component) ▸ hi'

theorem u8RangeTable_channels :
    ∀ c ∈ u8RangeTable.component.circuit.channels, c = byteChannel.toRaw := by
  show ∀ c ∈ (ByteChip.U8Range.circuit (p := SP1Prime)).channels, c = byteChannel.toRaw
  simp [GeneralFormalCircuit.channels, ByteChip.U8Range.circuit, circuit_norm]

theorem range16Table_channels :
    ∀ c ∈ range16Table.component.circuit.channels, c = byteChannel.toRaw := by
  show ∀ c ∈ (RangeChip.circuitFor rangeWidth16 (p := SP1Prime)).channels, c = byteChannel.toRaw
  simp [GeneralFormalCircuit.channels, RangeChip.circuitFor, RangeChip.circuit, circuit_norm]

/-- The two provider tables are silent on every channel other than Byte. -/
theorem u8RangeTable_interactionsWith_nil {ch : RawChannel (ZMod SP1Prime)}
    (hne : ch ≠ byteChannel.toRaw) :
    u8RangeTable.interactionsWith ch = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  intro hmem
  exact hne (u8RangeTable_channels _ hmem)

theorem range16Table_interactionsWith_nil {ch : RawChannel (ZMod SP1Prime)}
    (hne : ch ≠ byteChannel.toRaw) :
    range16Table.interactionsWith ch = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  intro hmem
  exact hne (range16Table_channels _ hmem)

theorem emptyTables_interactionsWith_nil (ch : RawChannel (ZMod SP1Prime)) :
    ∀ t ∈ emptyTables, t.interactionsWith ch = [] := by
  intro t ht
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp ht
  rfl

/-- The whole-shard channel view splits into the verifier row plus the two provider tables and the
Halt padding table (in stable position order), the 51 zero-row tables contributing nothing. -/
theorem jointWitness_interactionsWith_split (ch : RawChannel (ZMod SP1Prime)) :
    jointWitness.interactionsWith ch =
      jointWitness.verifierTable.interactionsWith ch ++
        (u8RangeTable.interactionsWith ch ++
          (range16Table.interactionsWith ch ++ haltPaddingTable.interactionsWith ch)) := by
  show (jointWitness.verifierTable :: jointWitness.tables).flatMap (·.interactionsWith ch) = _
  rw [List.flatMap_cons]
  show _ ++ jointTables.flatMap (·.interactionsWith ch) = _
  rw [jointTables, flatMap_set_set_set_of_nil (f := (·.interactionsWith ch)) (by omega) (by omega)
    (by rw [emptyTables_length]; omega) fun t ht => emptyTables_interactionsWith_nil ch t ht]

/-! ### The Halt padding row's per-channel views

The padding row emits nineteen interactions.  Eighteen are gated by `is_real = 0` and so carry
multiplicity zero; the nineteenth is the anti-gated Exit push of `⟨0⟩` at multiplicity `1 - 0 = 1`.
The first fact is checked executably over the (computable) whole-row interaction list; the Exit view
is recovered from the halt circuit's own exposed-channel closed form. -/

/-- Executable check: every Halt padding-row interaction outside the Exit bus is gated off. -/
theorem haltPaddingTable_zeroOrExit :
    haltPaddingTable.interactions.all
      (fun i => decide (i.mult = 0) || (i.channel.name == "SP1Exit")) = true := by native_decide

/-- Executable check: the padding row emits nineteen interactions in total. -/
theorem haltPaddingTable_interactions_length : haltPaddingTable.interactions.length = 19 := by
  native_decide

/-- On any non-Exit channel the Halt padding table contributes only multiplicity-zero entries. -/
theorem haltPaddingTable_mult_zero {ch : RawChannel (ZMod SP1Prime)} (hname : ch.name ≠ "SP1Exit") :
    ∀ i ∈ haltPaddingTable.interactionsWith ch, i.mult = 0 := by
  intro i hi
  rw [Table.interactionsWith_eq_filter] at hi
  obtain ⟨hmem, hch⟩ := List.mem_filter.mp hi
  have hchannel : i.channel = ch := by simpa using hch
  rcases Bool.or_eq_true _ _ |>.mp (List.all_eq_true.mp haltPaddingTable_zeroOrExit i hmem) with
    hzero | hexit
  · exact of_decide_eq_true hzero
  · exact absurd (hchannel ▸ beq_iff_eq.mp hexit : ch.name = "SP1Exit") hname

/-- A channel view is a sublist of the whole interaction list, so it is bounded by its length. -/
theorem haltPaddingTable_interactionsWith_length (ch : RawChannel (ZMod SP1Prime)) :
    (haltPaddingTable.interactionsWith ch).length ≤ 19 := by
  rw [Table.interactionsWith_eq_filter, ← haltPaddingTable_interactions_length]
  exact List.length_filter_le _ _

/-- Appending the Halt padding row's view of a non-Exit channel preserves balance: each of its
entries is gated off, so it shifts no message's balance, and its length is bounded by the row's
nineteen interactions. -/
theorem balancedInteractions_append_halt {l : List (Interaction (ZMod SP1Prime))}
    (hlen : l.length < 100) (hbal : ∀ msg, balanceOf l msg = 0)
    {ch : RawChannel (ZMod SP1Prime)} (hname : ch.name ≠ "SP1Exit") :
    BalancedInteractions (l ++ haltPaddingTable.interactionsWith ch) := by
  have hchar : (119 : ℕ) < ringChar (ZMod SP1Prime) := by
    rw [ZMod.ringChar_zmod_n]; norm_num [SP1Prime]
  refine ⟨Or.inl ?_, fun msg => ?_⟩
  · have h19 := haltPaddingTable_interactionsWith_length ch
    rw [List.length_append]
    omega
  · rw [balanceOf_append, hbal msg,
      balanceOf_eq_zero_of_mult_zero (haltPaddingTable_mult_zero hname), add_zero]

/-! ### The verifier row's per-channel views -/

/-- The verifier row's State view: exactly the boundary pull/push pair (the erasure of
`witness_verifierStateInteractions_eq` at the joint witness). -/
theorem jointWitness_verifierState :
    jointWitness.verifierTable.interactionsWith stateChannel.toRaw =
      [stateChannel.pulledIfValue 1
         ⟨pv.final_clk_high, pv.final_clk_low, pv.final_pc0, pv.final_pc1, pv.final_pc2⟩,
       stateChannel.pushedIfValue 1
         ⟨pv.init_clk_high, pv.init_clk_low, pv.init_pc0, pv.init_pc1, pv.init_pc2⟩] := by
  have h := congrArg (List.map TypedInteraction.raw)
    (witness_verifierStateInteractions_eq (p := SP1Prime) jointWitness)
  rw [typedTableInteractionsWith_raw] at h
  simpa using h

theorem jointWitness_verifierProgram_nil :
    jointWitness.verifierTable.interactionsWith programChannel.toRaw = [] := by
  have h := congrArg (List.map TypedInteraction.raw)
    (witness_verifierProgramInteractions_eq_nil (p := SP1Prime) jointWitness)
  rw [typedTableInteractionsWith_raw] at h
  simpa using h

theorem jointWitness_verifierMemory_nil :
    jointWitness.verifierTable.interactionsWith memoryChannel.toRaw = [] := by
  have h := congrArg (List.map TypedInteraction.raw)
    (witness_verifierMemoryInteractions_eq_nil (p := SP1Prime) jointWitness)
  rw [typedTableInteractionsWith_raw] at h
  simpa using h

/-- The verifier row's Exit view: the single ungated `⟨exit_code⟩` pull (the erasure of
`witness_verifierExitInteractions_eq` at the joint witness).  The committed `exit_code` is `0`, so
this is a `-1` pull of `⟨0⟩`. -/
theorem jointWitness_verifierExit :
    jointWitness.verifierTable.interactionsWith exitChannel.toRaw =
      [exitChannel.pulledIfValue 1 (⟨pv.exit_code⟩ : Channels.ExitMsg (ZMod SP1Prime))] := by
  have h := congrArg (List.map TypedInteraction.raw)
    (witness_verifierExitInteractions_eq (p := SP1Prime) jointWitness)
  rw [typedTableInteractionsWith_raw] at h
  simpa using h

/-- The verifier's twelve syntactic Byte-bus pulls, in emission order (the Byte sibling of
`sp1StateVerifierMain_stateInteractions`, transcribed from `sp1StateVerifierMain`). -/
def verifierBytePulls (pi : Var SP1PublicIO (ZMod SP1Prime)) :
    List (AbstractInteraction (ZMod SP1Prime)) :=
  [(byteChannel.pulled (⟨6, pi.init_clk_0_16, Expression.const ((16 : ℕ) : ZMod SP1Prime), 0⟩ :
      ByteRow (Expression (ZMod SP1Prime)))).toRaw,
   (byteChannel.pulled (⟨6, pi.init_clk_32_48, Expression.const ((16 : ℕ) : ZMod SP1Prime), 0⟩ :
      ByteRow (Expression (ZMod SP1Prime)))).toRaw,
   (byteChannel.pulled (⟨3, 0, pi.init_clk_24_32, pi.init_clk_16_24⟩ :
      ByteRow (Expression (ZMod SP1Prime)))).toRaw,
   (byteChannel.pulled (⟨6, pi.init_pc0, Expression.const ((16 : ℕ) : ZMod SP1Prime), 0⟩ :
      ByteRow (Expression (ZMod SP1Prime)))).toRaw,
   (byteChannel.pulled (⟨6, pi.init_pc1, Expression.const ((16 : ℕ) : ZMod SP1Prime), 0⟩ :
      ByteRow (Expression (ZMod SP1Prime)))).toRaw,
   (byteChannel.pulled (⟨6, pi.init_pc2, Expression.const ((16 : ℕ) : ZMod SP1Prime), 0⟩ :
      ByteRow (Expression (ZMod SP1Prime)))).toRaw,
   (byteChannel.pulled (⟨6, pi.final_clk_0_16, Expression.const ((16 : ℕ) : ZMod SP1Prime), 0⟩ :
      ByteRow (Expression (ZMod SP1Prime)))).toRaw,
   (byteChannel.pulled (⟨6, pi.final_clk_32_48, Expression.const ((16 : ℕ) : ZMod SP1Prime), 0⟩ :
      ByteRow (Expression (ZMod SP1Prime)))).toRaw,
   (byteChannel.pulled (⟨3, 0, pi.final_clk_24_32, pi.final_clk_16_24⟩ :
      ByteRow (Expression (ZMod SP1Prime)))).toRaw,
   (byteChannel.pulled (⟨6, pi.final_pc0, Expression.const ((16 : ℕ) : ZMod SP1Prime), 0⟩ :
      ByteRow (Expression (ZMod SP1Prime)))).toRaw,
   (byteChannel.pulled (⟨6, pi.final_pc1, Expression.const ((16 : ℕ) : ZMod SP1Prime), 0⟩ :
      ByteRow (Expression (ZMod SP1Prime)))).toRaw,
   (byteChannel.pulled (⟨6, pi.final_pc2, Expression.const ((16 : ℕ) : ZMod SP1Prime), 0⟩ :
      ByteRow (Expression (ZMod SP1Prime)))).toRaw]

/-- The verifier's exact syntactic Byte pulls, exposed without unfolding its formal-circuit
record. -/
theorem sp1StateVerifierMain_byteInteractions (pi : Var SP1PublicIO (ZMod SP1Prime))
    (offset : ℕ) :
    ((sp1StateVerifierMain pi).operations offset).interactionsWith byteChannel.toRaw =
      verifierBytePulls pi := by
  simp [sp1StateVerifierMain, circuit_norm, verifierBytePulls]

/-- A public boundary whose two middle timestamp bytes are pairwise distinct at both ends. -/
def asymmetricClockBoundary : SP1PublicIO (ZMod SP1Prime) :=
  ⟨0, 1, 2, 0, 0, 1, 0, 0, 3, 4, 0, 0, 1, 0, 0, 1, Vector.replicate 32 0⟩

/-- Evaluated verifier Byte interactions for the asymmetric-clock regression. -/
def asymmetricClockVerifierByteInteractions : List (Interaction (ZMod SP1Prime)) :=
  (verifierBytePulls (varFromOffset SP1PublicIO 0)).map
    (AbstractInteraction.eval (Environment.fromInput asymmetricClockBoundary anchorData))

/-- The verifier emits the W3 U8 pairs in exact-public-value order `(24..32, 16..24)`.
Distinct concrete bytes make this regression sensitive to an accidental operand swap. -/
theorem verifierBytePulls_asymmetricClockOrder :
    ((asymmetricClockVerifierByteInteractions.drop 2).head?.map (fun interaction => interaction.msg),
      (asymmetricClockVerifierByteInteractions.drop 8).head?.map (fun interaction => interaction.msg)) =
      (some #[(3 : ZMod SP1Prime), 0, 2, 1],
        some #[(3 : ZMod SP1Prime), 0, 4, 3]) := by native_decide

/-- The evaluated Byte-channel contribution of the joint shard, as one executable list: the
verifier row's twelve pulls followed by the two provider tables' pushes.  Keeping this list
computable (evaluation applied, no channel filter) is what lets `native_decide` check its
balance. -/
def byteInteractions : List (Interaction (ZMod SP1Prime)) :=
  (verifierBytePulls (varFromOffset SP1PublicIO 0)).map
      (AbstractInteraction.eval (Environment.fromInput pv anchorData)) ++
    (u8RangeTable.interactions ++ range16Table.interactions)

theorem jointWitness_verifierByte :
    jointWitness.verifierTable.interactionsWith byteChannel.toRaw =
      (verifierBytePulls (varFromOffset SP1PublicIO 0)).map
        (AbstractInteraction.eval (Environment.fromInput pv anchorData)) := by
  unfold Table.interactionsWith
  rw [EnsembleWitness.verifierTable_flatMap]
  rw [Operations.interactionValuesWith_eq_map, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval (Environment.fromInput pv anchorData))
    (((sp1StateVerifierMain (varFromOffset SP1PublicIO 0)).operations
      (size SP1PublicIO)).interactionsWith byteChannel.toRaw) = _
  rw [sp1StateVerifierMain_byteInteractions]

theorem jointWitness_byteInteractions :
    jointWitness.interactionsWith byteChannel.toRaw =
      byteInteractions ++ haltPaddingTable.interactionsWith byteChannel.toRaw := by
  rw [jointWitness_interactionsWith_split, jointWitness_verifierByte,
    table_interactionsWith_eq_interactions u8RangeTable_channels,
    table_interactionsWith_eq_interactions range16Table_channels]
  simp only [byteInteractions, List.append_assoc]

/-- The verifier's twelve pulls and the two provider tables' pushes cancel message-for-message. -/
theorem byteInteractions_balanced : BalancedInteractions byteInteractions := by
  refine balancedInteractions_of_member_balance ?_ (by native_decide)
  rw [show byteInteractions.length = 15 from by native_decide, ZMod.ringChar_zmod_n]
  norm_num [SP1Prime]

/-! ### The Exit bus

The verifier's ungated `-1` pull of `⟨exit_code⟩ = ⟨0⟩` against the Halt padding row's two pushes:
the reduced-`x10` push at multiplicity `is_real = 0` and the padding push of `⟨0⟩` at multiplicity
`1 - is_real = 1`. -/

/-- The Halt padding table's Exit view: the halt circuit's two exposed Exit pushes, evaluated at the
all-zero row.  Recovering it through the circuit's own `interactionsWith_exit_eq` closed form is
what keeps the list computable (`interactionsWith` itself filters over an undecidable channel
equality). -/
def haltExitInteractions : List (Interaction (ZMod SP1Prime)) :=
  [(exitChannel.pushedIf
      (varFromOffset HaltChip.Inputs 0 : Var HaltChip.Inputs (ZMod SP1Prime)).is_real
      (HaltChip.exitMsg (varFromOffset HaltChip.Inputs 0))).toRaw,
   (exitChannel.pushedIf
      (1 - (varFromOffset HaltChip.Inputs 0 : Var HaltChip.Inputs (ZMod SP1Prime)).is_real)
      (HaltChip.exitPaddingMsg (p := SP1Prime))).toRaw].map
    (AbstractInteraction.eval (haltPaddingTable.environment haltPaddingRow))

theorem haltPaddingTable_exit :
    haltPaddingTable.interactionsWith exitChannel.toRaw = haltExitInteractions := by
  show [haltPaddingRow].flatMap _ = _
  rw [List.flatMap_singleton, Operations.interactionValuesWith_eq_map,
    Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval (haltPaddingTable.environment haltPaddingRow))
    (((HaltChip.main
      (varFromOffset HaltChip.Inputs 0 : Var HaltChip.Inputs (ZMod SP1Prime))).operations
        (size HaltChip.Inputs)).interactionsWith exitChannel.toRaw) = _
  rw [HaltChip.interactionsWith_exit_eq]
  rfl

/-- The evaluated Exit-channel contribution of the joint shard, as one executable list. -/
def exitInteractions : List (Interaction (ZMod SP1Prime)) :=
  [exitChannel.pulledIfValue 1 (⟨pv.exit_code⟩ : Channels.ExitMsg (ZMod SP1Prime))] ++
    haltExitInteractions

theorem jointWitness_exitInteractions :
    jointWitness.interactionsWith exitChannel.toRaw = exitInteractions := by
  rw [jointWitness_interactionsWith_split, jointWitness_verifierExit,
    u8RangeTable_interactionsWith_nil (of_eq_false Channels.exitChannel_eq_byteChannel_false),
    range16Table_interactionsWith_nil (of_eq_false Channels.exitChannel_eq_byteChannel_false),
    haltPaddingTable_exit, List.nil_append, List.nil_append]
  rfl

theorem jointWitness_balanced : jointWitness.BalancedChannels := by
  intro channel hchannel
  rw [sp1Ensemble_channels] at hchannel
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hchannel
  rcases hchannel with rfl | rfl | rfl | rfl | rfl
  · show BalancedInteractions (jointWitness.interactionsWith stateChannel.toRaw)
    rw [jointWitness_interactionsWith_split, jointWitness_verifierState,
      u8RangeTable_interactionsWith_nil (of_eq_false Channels.stateChannel_eq_byteChannel_false),
      range16Table_interactionsWith_nil (of_eq_false Channels.stateChannel_eq_byteChannel_false),
      List.nil_append, List.nil_append]
    exact balancedInteractions_append_halt (by norm_num)
      (balancedInteractions_pair (by native_decide) (neg_add_cancel 1)
        (Or.inl sp1Prime_char_pos_facts.1)).2
      (by simp only [Channel.toRaw_name, Channels.stateChannel]; decide)
  · show BalancedInteractions (jointWitness.interactionsWith byteChannel.toRaw)
    rw [jointWitness_byteInteractions]
    exact balancedInteractions_append_halt
      (by rw [show byteInteractions.length = 15 from by native_decide]; norm_num)
      byteInteractions_balanced.2
      (by simp only [Channel.toRaw_name, Channels.byteChannel]; decide)
  · show BalancedInteractions (jointWitness.interactionsWith programChannel.toRaw)
    rw [jointWitness_interactionsWith_split, jointWitness_verifierProgram_nil,
      u8RangeTable_interactionsWith_nil (of_eq_false Channels.programChannel_eq_byteChannel_false),
      range16Table_interactionsWith_nil
        (of_eq_false Channels.programChannel_eq_byteChannel_false),
      List.nil_append, List.nil_append]
    exact balancedInteractions_append_halt (by norm_num) (fun _ => rfl)
      (by simp only [Channel.toRaw_name, Channels.programChannel]; decide)
  · show BalancedInteractions (jointWitness.interactionsWith memoryChannel.toRaw)
    rw [jointWitness_interactionsWith_split, jointWitness_verifierMemory_nil,
      u8RangeTable_interactionsWith_nil (of_eq_false Channels.memoryChannel_eq_byteChannel_false),
      range16Table_interactionsWith_nil
        (of_eq_false Channels.memoryChannel_eq_byteChannel_false),
      List.nil_append, List.nil_append]
    exact balancedInteractions_append_halt (by norm_num) (fun _ => rfl)
      (by simp only [Channel.toRaw_name, Channels.memoryChannel]; decide)
  · show BalancedInteractions (jointWitness.interactionsWith exitChannel.toRaw)
    rw [jointWitness_exitInteractions]
    refine balancedInteractions_of_member_balance ?_ (by native_decide)
    rw [show exitInteractions.length = 3 from by native_decide, ZMod.ringChar_zmod_n]
    norm_num [SP1Prime]

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

theorem programProviderTable_table_nil :
    (programProviderTable (p := SP1Prime) jointWitness).table = [] :=
  jointTables_table_nil_of_ne 35 (by rw [jointTables_length]; omega) (by omega) (by omega)
    (by omega)

theorem memoryInitProviderTable_table_nil :
    (memoryInitProviderTable (p := SP1Prime) jointWitness).table = [] :=
  jointTables_table_nil_of_ne 36 (by rw [jointTables_length]; omega) (by omega) (by omega)
    (by omega)

theorem memoryFinalizeProviderTable_table_nil :
    (memoryFinalizeProviderTable (p := SP1Prime) jointWitness).table = [] :=
  jointTables_table_nil_of_ne 37 (by rw [jointTables_length]; omega) (by omega) (by omega)
    (by omega)

theorem jointWitness_programProviderBound :
    ProgramProviderBound (p := SP1Prime) jointWitness := by
  intro interaction member _
  exfalso
  simp only [Table.interactionsWith, programProviderTable_table_nil, List.flatMap_nil] at member
  exact absurd member (List.not_mem_nil)

theorem jointWitness_memoryInitProviderBound :
    MemoryInitProviderBound (p := SP1Prime) jointWitness anchorState
      (Commit.initClkNat anchorData) := by
  intro interaction member _
  exfalso
  simp only [Table.interactionsWith, memoryInitProviderTable_table_nil,
    List.flatMap_nil] at member
  exact absurd member (List.not_mem_nil)

theorem jointWitness_memoryInitProviderUnique :
    MemoryInitProviderUnique (p := SP1Prime) jointWitness := by
  show (typedTableInteractionsWith (memoryInitProviderTable jointWitness)
    memoryChannel).Pairwise _
  rw [typedTableInteractionsWith, memoryInitProviderTable_table_nil, List.flatMap_nil]
  exact List.Pairwise.nil

theorem jointWitness_memoryFinalizeProviderUnique :
    MemoryFinalizeProviderUnique (p := SP1Prime) jointWitness := by
  show (typedTableInteractionsWith (memoryFinalizeProviderTable jointWitness)
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

/-- The committed self-jump takes one official Sail step and exposes the exact row effect used by
both the reachability invariant and the active deterministic-compiler audit. -/
theorem anchorStep :
    ∃ next, SailStep anchorState next ∧ RowEffect anchorProgram jalView anchorState next := by
  exact Advance.advance_of_jal_x0 (p := SP1Prime) (prog := anchorProgram) (r := jalView)
    anchorState_configured anchorState_romLoaded
    (by rw [jalView_rcvPc]; exact anchorState_pc) jalView_decodedInROM rfl rfl rfl
    (by rw [jalView_sndPc]; decide)
    (fun imm hb => by
      have hb' : bitVecToWord (p := SP1Prime) ((0#21 : BitVec 21).signExtend 64) =
          bitVecToWord (imm.signExtend 64) := hb
      have h64 := congrArg Word.toBitVec64 hb'
      rw [toBitVec64_bitVecToWord, toBitVec64_bitVecToWord] at h64
      rw [jalView_rcvPc, jalView_sndPc,
        show sign_extend (m := 64) imm = imm.signExtend 64 from rfl, ← h64]
      decide)

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
theorem anchorBoundaryFacts : InitialBoundaryFacts stmt jointWitness anchorState where
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
  programProvider := jointWitness_programProviderBound
  memoryProvider := jointWitness_memoryInitProviderBound
  memoryProviderUnique := jointWitness_memoryInitProviderUnique
  memoryFinalizeProviderUnique := jointWitness_memoryFinalizeProviderUnique

/-! ## The joint witness -/

/-- **Joint non-vacuity of the capstone's hypothesis bundle.**  The boundary-only shard with equal
public State endpoints satisfies the complete `SupportedCoreNativeRelation` at the concrete prime:
the raw ensemble relation (constraints + five-bus balance, the Byte bus balanced by the two honest
provider tables and the Exit bus by the mandatory Halt padding row) and the semantic boundary
binding (with the committed one-instruction program and the concrete configured initial state).  Those two conjuncts are the whole relation — the memory
pull-timestamp range fact that used to ride along as a third companion is now derived inside the
capstone from the per-location Memory balance.  Applying `supported_core_native_sound` to this
witness yields the honest 0-step local Sail execution between the equal endpoints. -/
theorem supportedCoreNativeRelation_nonvacuous :
    SupportedCoreNativeRelation (p := SP1Prime) stmt jointWitness :=
  ⟨⟨rfl, jointWitness_constraints, jointWitness_balanced⟩,
   anchorBoundaryFacts.binding⟩

end SP1Clean.Audit.JointNonVacuity
