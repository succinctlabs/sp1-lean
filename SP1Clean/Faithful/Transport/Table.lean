import SP1Clean.Faithful.ChipOracle
import ToClean.Air.TableBuild

/-! # Transporting an extracted Rust table to a native Clean table

The external PR #110 report's Finding 1: the Rust-faithfulness theorems and the Sail-soundness
capstone are two families that share an endpoint but are never composed inside Lean — `Faithful/`
is a leaf of the dependency graph, so nothing in the repository consumes a `ChipFaithful` proof.
This file is the first half of the composition: it turns a per-row faithfulness statement into a
per-**table** one, so a valid extracted table becomes a valid native `Air.Flat.Table` that the
soundness side can then read.

## What a `ChipFaithful` already gives, and what was missing

`ChipFaithful.constraints` says: for one Rust row, the Rust assertion list is all-zero **iff** the
codec's reconstructed native physical row satisfies the whole native circuit's `ConstraintsHold`.
`ChipFaithful.interactions` says the two active interaction multisets agree. Both are stated one
row at a time, at `NativeRowAssignment.environment` — an environment built from a bare `Array`.

What was missing is only plumbing, but it is the plumbing that makes the composition exist: Clean's
flat-AIR layer consumes a `Table`, whose `Constraints` quantify over `table.environment row`. Since
a transported table's `data` is the codec's `data` and its rows are the codec's rows, those two
environments are *definitionally* the same, and the whole per-table statement falls out row by row.

## Generic, deliberately

Nothing here mentions a chip. `transportTable` and its three theorems are stated over an arbitrary
`ChipRowCodec`/`ChipOracle`/`ChipFaithful` triple, so each of the twenty-five registered chips
instantiates them by supplying its own anchor — no per-chip proof, and no opportunity for
twenty-five copies to drift.

## Why the codec's codimension-1 image needs no repair

The external report's Finding 11 observes that for the six flag-hinted chips the faithfulness
codec covers only a codimension-1 slice of the native row space: `deconfigure` sets `is_real` to
the sum of the one-hot operation flags, so no native row whose `is_real` disagrees with its flag
sum is in the codec's image.

That is the right shape for every theorem stated here, and the reason is directional. Transport
runs extracted → native: it *starts* from a Rust row and *constructs* the native row through
`deconfigure`, so the constructed row satisfies the flag-sum relation by definition and the slice
is not a restriction on anything — it is where the construction lands. An image-forcing lemma
(every native solution equals `deconfigure` of some Rust row) would be needed only for a
native → Rust direction quantified over arbitrary native solutions, and no theorem in this
repository states that direction. `ChipFaithful.constraints` is an `↔` at a *given* row, not a
surjectivity claim, so it does not need one either.

## Scope

This is the table-level half. The ensemble-level transport — assembling twenty-five transported
tables plus the provider and boundary segments into an `EnsembleWitness`, and deriving the four
channel balances from the extracted AIR's own ℕ-exact balance — builds on these theorems; see
`docs/roadmap.md`.
-/

set_option autoImplicit false

namespace SP1Clean.Faithful.Transport

open Circuit
open Air.Flat (Component Table)
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime]
variable {Input NativeCols RustCols : TypeMap}
variable [ProvableStruct Input] [ProvableStruct NativeCols]
variable {circuit : GeneralFormalCircuit (ZMod p) Input NativeCols}
variable {codec : ChipRowCodec Input NativeCols circuit}
variable {oracle : ChipOracle (ZMod p) NativeCols RustCols}

/-- The native physical row an extracted Rust row transports to: deconfigure the Rust columns into
the chip's own native row type, then let the codec lay them out in Clean's input-first order. -/
def transportRow (codec : ChipRowCodec Input NativeCols circuit)
    (oracle : ChipOracle (ZMod p) NativeCols RustCols) (rustCols : RustCols (ZMod p))
    (data : ProverData (ZMod p)) : Array (ZMod p) :=
  (codec.assignment (oracle.deconfigure rustCols) data).row

/-- The environment a transported row is read in is the one the faithfulness statement speaks
about. This is the whole bridge between `NativeRowAssignment.environment` and `Table.environment`:
both are `Environment.fromArray` of the same array at the same committed data. -/
theorem environment_transportRow (codec : ChipRowCodec Input NativeCols circuit)
    (oracle : ChipOracle (ZMod p) NativeCols RustCols) (rustCols : RustCols (ZMod p))
    (data : ProverData (ZMod p)) :
    Environment.fromArray (transportRow codec oracle rustCols data) data =
      (codec.assignment (oracle.deconfigure rustCols) data).environment := rfl

/-- **The transported table**: one native physical row per extracted Rust row, at the extracted
AIR's own committed prover data. -/
def transportTable (codec : ChipRowCodec Input NativeCols circuit)
    (oracle : ChipOracle (ZMod p) NativeCols RustCols)
    (rustRows : List (RustCols (ZMod p))) (data : ProverData (ZMod p)) : Table (ZMod p) where
  component := ⟨circuit⟩
  width := (⟨circuit⟩ : Component (ZMod p)).width
  table := rustRows.map (transportRow codec oracle · data)
  data := data
  uniform_width := by
    intro row hrow
    obtain ⟨rustCols, -, rfl⟩ := List.mem_map.mp hrow
    exact (codec.assignment (oracle.deconfigure rustCols) data).width_eq

@[simp] theorem transportTable_component (rustRows : List (RustCols (ZMod p)))
    (data : ProverData (ZMod p)) :
    (transportTable codec oracle rustRows data).component = ⟨circuit⟩ := rfl

@[simp] theorem transportTable_data (rustRows : List (RustCols (ZMod p)))
    (data : ProverData (ZMod p)) :
    (transportTable codec oracle rustRows data).data = data := rfl

@[simp] theorem transportTable_table (rustRows : List (RustCols (ZMod p)))
    (data : ProverData (ZMod p)) :
    (transportTable codec oracle rustRows data).table =
      rustRows.map (transportRow codec oracle · data) := rfl

/-- A transported table has exactly as many rows as the extracted table it came from — no padding
is introduced and none is dropped. -/
@[simp] theorem transportTable_length (rustRows : List (RustCols (ZMod p)))
    (data : ProverData (ZMod p)) :
    (transportTable codec oracle rustRows data).length = rustRows.length :=
  List.length_map ..

/-! ## The two transported facts -/

/--
**A valid extracted table transports to a constraint-satisfying native table.**

The premise is exactly what the extracted AIR asserts of its own rows: every entry of the chip's
complete Rust `assertZeros` list is zero. The conclusion is Clean's `Table.Constraints` for the
native chip circuit — every `assertZero` of the whole flattened native circuit, gadget subcircuits
included, on every transported row.

This is the forward direction of `ChipFaithful.constraints`, lifted row-wise. The reverse direction
is available from the same anchor and is what a completeness-shaped transport would use.
-/
theorem transportTable_constraints
    (faithful : ChipFaithful Input NativeCols RustCols circuit codec oracle)
    (rustRows : List (RustCols (ZMod p))) (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (oracle.assertZeros rustCols)) :
    (transportTable codec oracle rustRows data).Constraints := by
  intro row hrow
  obtain ⟨rustCols, hmem, rfl⟩ := List.mem_map.mp hrow
  exact (faithful.constraints rustCols data).mp (valid rustCols hmem)

/-- **Per row, the transported table's active interactions are the extracted row's.** The native
circuit's whole interaction multiset — State, Byte, the dualized Memory and Program pulls, and any
unexpected-channel tail — permutes the Rust chip's, after dropping multiplicity-zero entries on
both sides. -/
theorem transportRow_accesses_perm
    (faithful : ChipFaithful Input NativeCols RustCols circuit codec oracle)
    (rustCols : RustCols (ZMod p)) (data : ProverData (ZMod p))
    (valid : List.Forall (· = 0) (oracle.assertZeros rustCols)) :
    List.Perm
      (LookupAccessList.active
        (nativeAccesses (Environment.fromArray (transportRow codec oracle rustCols data) data)
          (⟨circuit⟩ : Component (ZMod p)).operations))
      (LookupAccessList.active (oracle.rustAccesses rustCols)) :=
  faithful.interactions rustCols data valid

/--
**The whole transported table's interaction multiset is the whole extracted table's.**

Concatenating the per-row permutations in row order. This is the form the ensemble-level balance
argument consumes: a channel's balance is a sum over the table's interactions, so a permutation of
the whole table's access list is exactly what transports a `balanceOf = 0` from one side to the
other.
-/
theorem transportTable_accesses_perm
    (faithful : ChipFaithful Input NativeCols RustCols circuit codec oracle)
    (rustRows : List (RustCols (ZMod p))) (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (oracle.assertZeros rustCols)) :
    List.Perm
      ((transportTable codec oracle rustRows data).table.flatMap fun row =>
        LookupAccessList.active
          (nativeAccesses (Environment.fromArray row data)
            (⟨circuit⟩ : Component (ZMod p)).operations))
      (rustRows.flatMap fun rustCols => LookupAccessList.active (oracle.rustAccesses rustCols)) := by
  rw [transportTable_table, List.flatMap_map]
  induction rustRows with
  | nil => simp
  | cons rustCols rest ih =>
    simp only [List.flatMap_cons]
    exact List.Perm.append
      (transportRow_accesses_perm faithful rustCols data (valid rustCols List.mem_cons_self))
      (ih fun c hc => valid c (List.mem_cons_of_mem _ hc))

/-! ## Composing with the native soundness side

This is the point of the file. Clean's `Table.weakSoundness` turns a table's constraints into its
component's semantic `Spec` — for a chip, the `FormalModel/Contracts/Chips.lean` predicate saying
what the row *means*. Feeding a transported table into it composes the two theorem families the
external report found disconnected: extracted Rust validity on one side, the native chip's semantic
contract on the other, in one kernel-checked implication. -/

/--
**A valid extracted table's rows satisfy the native chip's semantic contract.**

The two extra premises are the ones Clean's soundness statement always carries and this file does
not attempt to discharge: the chip's honest-prover `Assumptions` on each transported row, and the
row's channel `Guarantees`. They are stated at the transported table rather than assumed of the
extracted one deliberately — an ensemble-level transport gets both from the extracted AIR's own
provider segment, which is where the facts actually live, and pushing them down to here would
misplace the obligation.
-/
theorem transportTable_spec
    (faithful : ChipFaithful Input NativeCols RustCols circuit codec oracle)
    (rustRows : List (RustCols (ZMod p))) (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (oracle.assertZeros rustCols))
    (assumptions : (transportTable codec oracle rustRows data).Assumptions)
    (guarantees : (transportTable codec oracle rustRows data).Guarantees) :
    (transportTable codec oracle rustRows data).Spec :=
  (Table.weakSoundness assumptions
    (transportTable_constraints faithful rustRows data valid) guarantees).1

end SP1Clean.Faithful.Transport
