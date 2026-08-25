import SP1Clean.Faithful.SupportedMachine
import SP1Clean.Composition.Table

/-! # The twenty-five per-chip table transports

`Faithful/Transport/Table.lean` proves the transport once, over an arbitrary
codec/oracle/faithfulness triple. This file instantiates it at each of the twenty-five registered
chips, so every `Faithful/<Chip>.lean` anchor is *consumed* by a named theorem rather than sitting
at the edge of the dependency graph — the concrete measurement the external PR #110 report made
against the previous tree (`Faithful/` unreachable from the capstone) inverts here.

Each chip contributes three theorems, all one-line citations of the generic ones:

* `<chip>_transportTable_constraints` — a table of valid extracted Rust rows becomes a native Clean
  table satisfying the whole native circuit's constraint system;
* `<chip>_transportTable_accesses` — that table's active interaction multiset is the extracted
  table's, after the project-wide bus-orientation convention;
* `<chip>_transportTable_spec` — and its rows satisfy the chip's semantic contract, given the
  honest-prover assumptions and channel guarantees Clean's soundness statement always carries.

There is no per-chip proof here by design: twenty-five copies of an argument are twenty-five
opportunities for one of them to be quietly weaker than the rest.
-/

set_option autoImplicit false

namespace SP1Clean.Composition

-- The faithfulness vocabulary (`ChipOracle`, `ChipFaithful`, `ChipRowCodec`,
-- `nativeAccesses`) is at the stratum below; this namespace no longer encloses it since the
-- 2026-08 move out of `Faithful/Transport/`.
open SP1Clean.Faithful

open Circuit
open Air.Flat (Component Table)
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- Every registered chip's faithfulness anchor is stated under `Fact (2 ^ 17 < p)`, and Mul and
DivRem's under the stronger `Fact (2 ^ 24 < p)`. Taking the stronger one as this file's ambient
hypothesis and deriving the weaker keeps one variable block for all twenty-five. -/
local instance transportFieldBound : Fact (2 ^ 17 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩


/-! ### `AddChip` -/

theorem addChip_transportTable_constraints (rustRows : List (Extracted.AddOracle.AddCols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (addChipOracle.assertZeros rustCols)) :
    (transportTable addChipRowCodec addChipOracle rustRows data).Constraints :=
  transportTable_constraints addChip_faithful rustRows data valid

theorem addChip_transportTable_accesses (rustRows : List (Extracted.AddOracle.AddCols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (addChipOracle.assertZeros rustCols)) :
    List.Perm
      ((transportTable addChipRowCodec addChipOracle rustRows data).table.flatMap fun row =>
        LookupAccessList.active
          (nativeAccesses (Environment.fromArray row data)
            (⟨AddChip.circuit⟩ : Component (ZMod p)).operations))
      (rustRows.flatMap fun rustCols =>
        LookupAccessList.active (addChipOracle.rustAccesses rustCols)) :=
  transportTable_accesses_perm addChip_faithful rustRows data valid

theorem addChip_transportTable_spec (rustRows : List (Extracted.AddOracle.AddCols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (addChipOracle.assertZeros rustCols))
    (assumptions : (transportTable addChipRowCodec addChipOracle rustRows data).Assumptions)
    (guarantees : (transportTable addChipRowCodec addChipOracle rustRows data).Guarantees) :
    (transportTable addChipRowCodec addChipOracle rustRows data).Spec :=
  transportTable_spec addChip_faithful rustRows data valid assumptions guarantees

/-! ### `AddiChip` -/

theorem addiChip_transportTable_constraints (rustRows : List (Extracted.AddiOracle.AddiCols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (addiChipOracle.assertZeros rustCols)) :
    (transportTable addiChipRowCodec addiChipOracle rustRows data).Constraints :=
  transportTable_constraints addiChip_faithful rustRows data valid

theorem addiChip_transportTable_accesses (rustRows : List (Extracted.AddiOracle.AddiCols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (addiChipOracle.assertZeros rustCols)) :
    List.Perm
      ((transportTable addiChipRowCodec addiChipOracle rustRows data).table.flatMap fun row =>
        LookupAccessList.active
          (nativeAccesses (Environment.fromArray row data)
            (⟨AddiChip.circuit⟩ : Component (ZMod p)).operations))
      (rustRows.flatMap fun rustCols =>
        LookupAccessList.active (addiChipOracle.rustAccesses rustCols)) :=
  transportTable_accesses_perm addiChip_faithful rustRows data valid

theorem addiChip_transportTable_spec (rustRows : List (Extracted.AddiOracle.AddiCols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (addiChipOracle.assertZeros rustCols))
    (assumptions : (transportTable addiChipRowCodec addiChipOracle rustRows data).Assumptions)
    (guarantees : (transportTable addiChipRowCodec addiChipOracle rustRows data).Guarantees) :
    (transportTable addiChipRowCodec addiChipOracle rustRows data).Spec :=
  transportTable_spec addiChip_faithful rustRows data valid assumptions guarantees

/-! ### `AddwChip` -/

theorem addwChip_transportTable_constraints (rustRows : List (Extracted.AddwOracle.AddwCols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (addwChipOracle.assertZeros rustCols)) :
    (transportTable addwChipRowCodec addwChipOracle rustRows data).Constraints :=
  transportTable_constraints addwChip_faithful rustRows data valid

theorem addwChip_transportTable_accesses (rustRows : List (Extracted.AddwOracle.AddwCols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (addwChipOracle.assertZeros rustCols)) :
    List.Perm
      ((transportTable addwChipRowCodec addwChipOracle rustRows data).table.flatMap fun row =>
        LookupAccessList.active
          (nativeAccesses (Environment.fromArray row data)
            (⟨AddwChip.circuit⟩ : Component (ZMod p)).operations))
      (rustRows.flatMap fun rustCols =>
        LookupAccessList.active (addwChipOracle.rustAccesses rustCols)) :=
  transportTable_accesses_perm addwChip_faithful rustRows data valid

theorem addwChip_transportTable_spec (rustRows : List (Extracted.AddwOracle.AddwCols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (addwChipOracle.assertZeros rustCols))
    (assumptions : (transportTable addwChipRowCodec addwChipOracle rustRows data).Assumptions)
    (guarantees : (transportTable addwChipRowCodec addwChipOracle rustRows data).Guarantees) :
    (transportTable addwChipRowCodec addwChipOracle rustRows data).Spec :=
  transportTable_spec addwChip_faithful rustRows data valid assumptions guarantees

/-! ### `SubChip` -/

theorem subChip_transportTable_constraints (rustRows : List (Extracted.SubOracle.SubCols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (subChipOracle.assertZeros rustCols)) :
    (transportTable subChipRowCodec subChipOracle rustRows data).Constraints :=
  transportTable_constraints subChip_faithful rustRows data valid

theorem subChip_transportTable_accesses (rustRows : List (Extracted.SubOracle.SubCols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (subChipOracle.assertZeros rustCols)) :
    List.Perm
      ((transportTable subChipRowCodec subChipOracle rustRows data).table.flatMap fun row =>
        LookupAccessList.active
          (nativeAccesses (Environment.fromArray row data)
            (⟨SubChip.circuit⟩ : Component (ZMod p)).operations))
      (rustRows.flatMap fun rustCols =>
        LookupAccessList.active (subChipOracle.rustAccesses rustCols)) :=
  transportTable_accesses_perm subChip_faithful rustRows data valid

theorem subChip_transportTable_spec (rustRows : List (Extracted.SubOracle.SubCols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (subChipOracle.assertZeros rustCols))
    (assumptions : (transportTable subChipRowCodec subChipOracle rustRows data).Assumptions)
    (guarantees : (transportTable subChipRowCodec subChipOracle rustRows data).Guarantees) :
    (transportTable subChipRowCodec subChipOracle rustRows data).Spec :=
  transportTable_spec subChip_faithful rustRows data valid assumptions guarantees

/-! ### `SubwChip` -/

theorem subwChip_transportTable_constraints (rustRows : List (Extracted.SubwOracle.SubwCols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (subwChipOracle.assertZeros rustCols)) :
    (transportTable subwChipRowCodec subwChipOracle rustRows data).Constraints :=
  transportTable_constraints subwChip_faithful rustRows data valid

theorem subwChip_transportTable_accesses (rustRows : List (Extracted.SubwOracle.SubwCols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (subwChipOracle.assertZeros rustCols)) :
    List.Perm
      ((transportTable subwChipRowCodec subwChipOracle rustRows data).table.flatMap fun row =>
        LookupAccessList.active
          (nativeAccesses (Environment.fromArray row data)
            (⟨SubwChip.circuit⟩ : Component (ZMod p)).operations))
      (rustRows.flatMap fun rustCols =>
        LookupAccessList.active (subwChipOracle.rustAccesses rustCols)) :=
  transportTable_accesses_perm subwChip_faithful rustRows data valid

theorem subwChip_transportTable_spec (rustRows : List (Extracted.SubwOracle.SubwCols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (subwChipOracle.assertZeros rustCols))
    (assumptions : (transportTable subwChipRowCodec subwChipOracle rustRows data).Assumptions)
    (guarantees : (transportTable subwChipRowCodec subwChipOracle rustRows data).Guarantees) :
    (transportTable subwChipRowCodec subwChipOracle rustRows data).Spec :=
  transportTable_spec subwChip_faithful rustRows data valid assumptions guarantees

/-! ### `BitwiseChip` -/

theorem bitwiseChip_transportTable_constraints (rustRows : List (Extracted.BitwiseOracle.BitwiseCols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (bitwiseChipOracle.assertZeros rustCols)) :
    (transportTable bitwiseChipRowCodec bitwiseChipOracle rustRows data).Constraints :=
  transportTable_constraints bitwiseChip_faithful rustRows data valid

theorem bitwiseChip_transportTable_accesses (rustRows : List (Extracted.BitwiseOracle.BitwiseCols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (bitwiseChipOracle.assertZeros rustCols)) :
    List.Perm
      ((transportTable bitwiseChipRowCodec bitwiseChipOracle rustRows data).table.flatMap fun row =>
        LookupAccessList.active
          (nativeAccesses (Environment.fromArray row data)
            (⟨BitwiseChip.circuit⟩ : Component (ZMod p)).operations))
      (rustRows.flatMap fun rustCols =>
        LookupAccessList.active (bitwiseChipOracle.rustAccesses rustCols)) :=
  transportTable_accesses_perm bitwiseChip_faithful rustRows data valid

theorem bitwiseChip_transportTable_spec (rustRows : List (Extracted.BitwiseOracle.BitwiseCols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (bitwiseChipOracle.assertZeros rustCols))
    (assumptions : (transportTable bitwiseChipRowCodec bitwiseChipOracle rustRows data).Assumptions)
    (guarantees : (transportTable bitwiseChipRowCodec bitwiseChipOracle rustRows data).Guarantees) :
    (transportTable bitwiseChipRowCodec bitwiseChipOracle rustRows data).Spec :=
  transportTable_spec bitwiseChip_faithful rustRows data valid assumptions guarantees

/-! ### `LtChip` -/

theorem ltChip_transportTable_constraints (rustRows : List (Extracted.LtOracle.LtCols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (ltChipOracle.assertZeros rustCols)) :
    (transportTable ltChipRowCodec ltChipOracle rustRows data).Constraints :=
  transportTable_constraints ltChip_faithful rustRows data valid

theorem ltChip_transportTable_accesses (rustRows : List (Extracted.LtOracle.LtCols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (ltChipOracle.assertZeros rustCols)) :
    List.Perm
      ((transportTable ltChipRowCodec ltChipOracle rustRows data).table.flatMap fun row =>
        LookupAccessList.active
          (nativeAccesses (Environment.fromArray row data)
            (⟨LtChip.circuit⟩ : Component (ZMod p)).operations))
      (rustRows.flatMap fun rustCols =>
        LookupAccessList.active (ltChipOracle.rustAccesses rustCols)) :=
  transportTable_accesses_perm ltChip_faithful rustRows data valid

theorem ltChip_transportTable_spec (rustRows : List (Extracted.LtOracle.LtCols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (ltChipOracle.assertZeros rustCols))
    (assumptions : (transportTable ltChipRowCodec ltChipOracle rustRows data).Assumptions)
    (guarantees : (transportTable ltChipRowCodec ltChipOracle rustRows data).Guarantees) :
    (transportTable ltChipRowCodec ltChipOracle rustRows data).Spec :=
  transportTable_spec ltChip_faithful rustRows data valid assumptions guarantees

/-! ### `ShiftLeftChip` -/

theorem shiftLeftChip_transportTable_constraints (rustRows : List (Extracted.ShiftLeftOracle.ShiftLeftCols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (shiftLeftChipOracle.assertZeros rustCols)) :
    (transportTable shiftLeftChipRowCodec shiftLeftChipOracle rustRows data).Constraints :=
  transportTable_constraints shiftLeftChip_faithful rustRows data valid

theorem shiftLeftChip_transportTable_accesses (rustRows : List (Extracted.ShiftLeftOracle.ShiftLeftCols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (shiftLeftChipOracle.assertZeros rustCols)) :
    List.Perm
      ((transportTable shiftLeftChipRowCodec shiftLeftChipOracle rustRows data).table.flatMap fun row =>
        LookupAccessList.active
          (nativeAccesses (Environment.fromArray row data)
            (⟨ShiftLeftChip.circuit⟩ : Component (ZMod p)).operations))
      (rustRows.flatMap fun rustCols =>
        LookupAccessList.active (shiftLeftChipOracle.rustAccesses rustCols)) :=
  transportTable_accesses_perm shiftLeftChip_faithful rustRows data valid

theorem shiftLeftChip_transportTable_spec (rustRows : List (Extracted.ShiftLeftOracle.ShiftLeftCols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (shiftLeftChipOracle.assertZeros rustCols))
    (assumptions : (transportTable shiftLeftChipRowCodec shiftLeftChipOracle rustRows data).Assumptions)
    (guarantees : (transportTable shiftLeftChipRowCodec shiftLeftChipOracle rustRows data).Guarantees) :
    (transportTable shiftLeftChipRowCodec shiftLeftChipOracle rustRows data).Spec :=
  transportTable_spec shiftLeftChip_faithful rustRows data valid assumptions guarantees

/-! ### `ShiftRightChip` -/

theorem shiftRightChip_transportTable_constraints (rustRows : List (Extracted.ShiftRightOracle.ShiftRightCols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (shiftRightChipOracle.assertZeros rustCols)) :
    (transportTable shiftRightChipRowCodec shiftRightChipOracle rustRows data).Constraints :=
  transportTable_constraints shiftRightChip_faithful rustRows data valid

theorem shiftRightChip_transportTable_accesses (rustRows : List (Extracted.ShiftRightOracle.ShiftRightCols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (shiftRightChipOracle.assertZeros rustCols)) :
    List.Perm
      ((transportTable shiftRightChipRowCodec shiftRightChipOracle rustRows data).table.flatMap fun row =>
        LookupAccessList.active
          (nativeAccesses (Environment.fromArray row data)
            (⟨ShiftRightChip.circuit⟩ : Component (ZMod p)).operations))
      (rustRows.flatMap fun rustCols =>
        LookupAccessList.active (shiftRightChipOracle.rustAccesses rustCols)) :=
  transportTable_accesses_perm shiftRightChip_faithful rustRows data valid

theorem shiftRightChip_transportTable_spec (rustRows : List (Extracted.ShiftRightOracle.ShiftRightCols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (shiftRightChipOracle.assertZeros rustCols))
    (assumptions : (transportTable shiftRightChipRowCodec shiftRightChipOracle rustRows data).Assumptions)
    (guarantees : (transportTable shiftRightChipRowCodec shiftRightChipOracle rustRows data).Guarantees) :
    (transportTable shiftRightChipRowCodec shiftRightChipOracle rustRows data).Spec :=
  transportTable_spec shiftRightChip_faithful rustRows data valid assumptions guarantees

/-! ### `JalChip` -/

theorem jalChip_transportTable_constraints (rustRows : List (Extracted.JalOracle.JalColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (jalChipOracle.assertZeros rustCols)) :
    (transportTable jalChipRowCodec jalChipOracle rustRows data).Constraints :=
  transportTable_constraints jalChip_faithful rustRows data valid

theorem jalChip_transportTable_accesses (rustRows : List (Extracted.JalOracle.JalColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (jalChipOracle.assertZeros rustCols)) :
    List.Perm
      ((transportTable jalChipRowCodec jalChipOracle rustRows data).table.flatMap fun row =>
        LookupAccessList.active
          (nativeAccesses (Environment.fromArray row data)
            (⟨JalChip.circuit⟩ : Component (ZMod p)).operations))
      (rustRows.flatMap fun rustCols =>
        LookupAccessList.active (jalChipOracle.rustAccesses rustCols)) :=
  transportTable_accesses_perm jalChip_faithful rustRows data valid

theorem jalChip_transportTable_spec (rustRows : List (Extracted.JalOracle.JalColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (jalChipOracle.assertZeros rustCols))
    (assumptions : (transportTable jalChipRowCodec jalChipOracle rustRows data).Assumptions)
    (guarantees : (transportTable jalChipRowCodec jalChipOracle rustRows data).Guarantees) :
    (transportTable jalChipRowCodec jalChipOracle rustRows data).Spec :=
  transportTable_spec jalChip_faithful rustRows data valid assumptions guarantees

/-! ### `JalrChip` -/

theorem jalrChip_transportTable_constraints (rustRows : List (Extracted.JalrOracle.JalrColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (jalrChipOracle.assertZeros rustCols)) :
    (transportTable jalrChipRowCodec jalrChipOracle rustRows data).Constraints :=
  transportTable_constraints jalrChip_faithful rustRows data valid

theorem jalrChip_transportTable_accesses (rustRows : List (Extracted.JalrOracle.JalrColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (jalrChipOracle.assertZeros rustCols)) :
    List.Perm
      ((transportTable jalrChipRowCodec jalrChipOracle rustRows data).table.flatMap fun row =>
        LookupAccessList.active
          (nativeAccesses (Environment.fromArray row data)
            (⟨JalrChip.circuit⟩ : Component (ZMod p)).operations))
      (rustRows.flatMap fun rustCols =>
        LookupAccessList.active (jalrChipOracle.rustAccesses rustCols)) :=
  transportTable_accesses_perm jalrChip_faithful rustRows data valid

theorem jalrChip_transportTable_spec (rustRows : List (Extracted.JalrOracle.JalrColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (jalrChipOracle.assertZeros rustCols))
    (assumptions : (transportTable jalrChipRowCodec jalrChipOracle rustRows data).Assumptions)
    (guarantees : (transportTable jalrChipRowCodec jalrChipOracle rustRows data).Guarantees) :
    (transportTable jalrChipRowCodec jalrChipOracle rustRows data).Spec :=
  transportTable_spec jalrChip_faithful rustRows data valid assumptions guarantees

/-! ### `BranchChip` -/

theorem branchChip_transportTable_constraints (rustRows : List (Extracted.BranchOracle.BranchColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (branchChipOracle.assertZeros rustCols)) :
    (transportTable branchChipRowCodec branchChipOracle rustRows data).Constraints :=
  transportTable_constraints branchChip_faithful rustRows data valid

theorem branchChip_transportTable_accesses (rustRows : List (Extracted.BranchOracle.BranchColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (branchChipOracle.assertZeros rustCols)) :
    List.Perm
      ((transportTable branchChipRowCodec branchChipOracle rustRows data).table.flatMap fun row =>
        LookupAccessList.active
          (nativeAccesses (Environment.fromArray row data)
            (⟨BranchChip.circuit⟩ : Component (ZMod p)).operations))
      (rustRows.flatMap fun rustCols =>
        LookupAccessList.active (branchChipOracle.rustAccesses rustCols)) :=
  transportTable_accesses_perm branchChip_faithful rustRows data valid

theorem branchChip_transportTable_spec (rustRows : List (Extracted.BranchOracle.BranchColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (branchChipOracle.assertZeros rustCols))
    (assumptions : (transportTable branchChipRowCodec branchChipOracle rustRows data).Assumptions)
    (guarantees : (transportTable branchChipRowCodec branchChipOracle rustRows data).Guarantees) :
    (transportTable branchChipRowCodec branchChipOracle rustRows data).Spec :=
  transportTable_spec branchChip_faithful rustRows data valid assumptions guarantees

/-! ### `UTypeChip` -/

theorem uTypeChip_transportTable_constraints (rustRows : List (Extracted.UTypeOracle.UTypeColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (uTypeChipOracle.assertZeros rustCols)) :
    (transportTable uTypeChipRowCodec uTypeChipOracle rustRows data).Constraints :=
  transportTable_constraints uTypeChip_faithful rustRows data valid

theorem uTypeChip_transportTable_accesses (rustRows : List (Extracted.UTypeOracle.UTypeColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (uTypeChipOracle.assertZeros rustCols)) :
    List.Perm
      ((transportTable uTypeChipRowCodec uTypeChipOracle rustRows data).table.flatMap fun row =>
        LookupAccessList.active
          (nativeAccesses (Environment.fromArray row data)
            (⟨UTypeChip.circuit⟩ : Component (ZMod p)).operations))
      (rustRows.flatMap fun rustCols =>
        LookupAccessList.active (uTypeChipOracle.rustAccesses rustCols)) :=
  transportTable_accesses_perm uTypeChip_faithful rustRows data valid

theorem uTypeChip_transportTable_spec (rustRows : List (Extracted.UTypeOracle.UTypeColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (uTypeChipOracle.assertZeros rustCols))
    (assumptions : (transportTable uTypeChipRowCodec uTypeChipOracle rustRows data).Assumptions)
    (guarantees : (transportTable uTypeChipRowCodec uTypeChipOracle rustRows data).Guarantees) :
    (transportTable uTypeChipRowCodec uTypeChipOracle rustRows data).Spec :=
  transportTable_spec uTypeChip_faithful rustRows data valid assumptions guarantees

/-! ### `LoadByteChip` -/

theorem loadByteChip_transportTable_constraints (rustRows : List (Extracted.LoadByteOracle.LoadByteColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (loadByteChipOracle.assertZeros rustCols)) :
    (transportTable loadByteChipRowCodec loadByteChipOracle rustRows data).Constraints :=
  transportTable_constraints loadByteChip_faithful rustRows data valid

theorem loadByteChip_transportTable_accesses (rustRows : List (Extracted.LoadByteOracle.LoadByteColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (loadByteChipOracle.assertZeros rustCols)) :
    List.Perm
      ((transportTable loadByteChipRowCodec loadByteChipOracle rustRows data).table.flatMap fun row =>
        LookupAccessList.active
          (nativeAccesses (Environment.fromArray row data)
            (⟨LoadByteChip.circuit⟩ : Component (ZMod p)).operations))
      (rustRows.flatMap fun rustCols =>
        LookupAccessList.active (loadByteChipOracle.rustAccesses rustCols)) :=
  transportTable_accesses_perm loadByteChip_faithful rustRows data valid

theorem loadByteChip_transportTable_spec (rustRows : List (Extracted.LoadByteOracle.LoadByteColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (loadByteChipOracle.assertZeros rustCols))
    (assumptions : (transportTable loadByteChipRowCodec loadByteChipOracle rustRows data).Assumptions)
    (guarantees : (transportTable loadByteChipRowCodec loadByteChipOracle rustRows data).Guarantees) :
    (transportTable loadByteChipRowCodec loadByteChipOracle rustRows data).Spec :=
  transportTable_spec loadByteChip_faithful rustRows data valid assumptions guarantees

/-! ### `LoadHalfChip` -/

theorem loadHalfChip_transportTable_constraints (rustRows : List (Extracted.LoadHalfOracle.LoadHalfColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (loadHalfChipOracle.assertZeros rustCols)) :
    (transportTable loadHalfChipRowCodec loadHalfChipOracle rustRows data).Constraints :=
  transportTable_constraints loadHalfChip_faithful rustRows data valid

theorem loadHalfChip_transportTable_accesses (rustRows : List (Extracted.LoadHalfOracle.LoadHalfColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (loadHalfChipOracle.assertZeros rustCols)) :
    List.Perm
      ((transportTable loadHalfChipRowCodec loadHalfChipOracle rustRows data).table.flatMap fun row =>
        LookupAccessList.active
          (nativeAccesses (Environment.fromArray row data)
            (⟨LoadHalfChip.circuit⟩ : Component (ZMod p)).operations))
      (rustRows.flatMap fun rustCols =>
        LookupAccessList.active (loadHalfChipOracle.rustAccesses rustCols)) :=
  transportTable_accesses_perm loadHalfChip_faithful rustRows data valid

theorem loadHalfChip_transportTable_spec (rustRows : List (Extracted.LoadHalfOracle.LoadHalfColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (loadHalfChipOracle.assertZeros rustCols))
    (assumptions : (transportTable loadHalfChipRowCodec loadHalfChipOracle rustRows data).Assumptions)
    (guarantees : (transportTable loadHalfChipRowCodec loadHalfChipOracle rustRows data).Guarantees) :
    (transportTable loadHalfChipRowCodec loadHalfChipOracle rustRows data).Spec :=
  transportTable_spec loadHalfChip_faithful rustRows data valid assumptions guarantees

/-! ### `LoadWordChip` -/

theorem loadWordChip_transportTable_constraints (rustRows : List (Extracted.LoadWordOracle.LoadWordColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (loadWordChipOracle.assertZeros rustCols)) :
    (transportTable loadWordChipRowCodec loadWordChipOracle rustRows data).Constraints :=
  transportTable_constraints loadWordChip_faithful rustRows data valid

theorem loadWordChip_transportTable_accesses (rustRows : List (Extracted.LoadWordOracle.LoadWordColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (loadWordChipOracle.assertZeros rustCols)) :
    List.Perm
      ((transportTable loadWordChipRowCodec loadWordChipOracle rustRows data).table.flatMap fun row =>
        LookupAccessList.active
          (nativeAccesses (Environment.fromArray row data)
            (⟨LoadWordChip.circuit⟩ : Component (ZMod p)).operations))
      (rustRows.flatMap fun rustCols =>
        LookupAccessList.active (loadWordChipOracle.rustAccesses rustCols)) :=
  transportTable_accesses_perm loadWordChip_faithful rustRows data valid

theorem loadWordChip_transportTable_spec (rustRows : List (Extracted.LoadWordOracle.LoadWordColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (loadWordChipOracle.assertZeros rustCols))
    (assumptions : (transportTable loadWordChipRowCodec loadWordChipOracle rustRows data).Assumptions)
    (guarantees : (transportTable loadWordChipRowCodec loadWordChipOracle rustRows data).Guarantees) :
    (transportTable loadWordChipRowCodec loadWordChipOracle rustRows data).Spec :=
  transportTable_spec loadWordChip_faithful rustRows data valid assumptions guarantees

/-! ### `LoadDoubleChip` -/

theorem loadDoubleChip_transportTable_constraints (rustRows : List (Extracted.LoadDoubleOracle.LoadDoubleColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (loadDoubleChipOracle.assertZeros rustCols)) :
    (transportTable loadDoubleChipRowCodec loadDoubleChipOracle rustRows data).Constraints :=
  transportTable_constraints loadDoubleChip_faithful rustRows data valid

theorem loadDoubleChip_transportTable_accesses (rustRows : List (Extracted.LoadDoubleOracle.LoadDoubleColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (loadDoubleChipOracle.assertZeros rustCols)) :
    List.Perm
      ((transportTable loadDoubleChipRowCodec loadDoubleChipOracle rustRows data).table.flatMap fun row =>
        LookupAccessList.active
          (nativeAccesses (Environment.fromArray row data)
            (⟨LoadDoubleChip.circuit⟩ : Component (ZMod p)).operations))
      (rustRows.flatMap fun rustCols =>
        LookupAccessList.active (loadDoubleChipOracle.rustAccesses rustCols)) :=
  transportTable_accesses_perm loadDoubleChip_faithful rustRows data valid

theorem loadDoubleChip_transportTable_spec (rustRows : List (Extracted.LoadDoubleOracle.LoadDoubleColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (loadDoubleChipOracle.assertZeros rustCols))
    (assumptions : (transportTable loadDoubleChipRowCodec loadDoubleChipOracle rustRows data).Assumptions)
    (guarantees : (transportTable loadDoubleChipRowCodec loadDoubleChipOracle rustRows data).Guarantees) :
    (transportTable loadDoubleChipRowCodec loadDoubleChipOracle rustRows data).Spec :=
  transportTable_spec loadDoubleChip_faithful rustRows data valid assumptions guarantees

/-! ### `LoadX0Chip` -/

theorem loadX0Chip_transportTable_constraints (rustRows : List (Extracted.LoadX0Oracle.LoadX0Columns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (loadX0ChipOracle.assertZeros rustCols)) :
    (transportTable loadX0ChipRowCodec loadX0ChipOracle rustRows data).Constraints :=
  transportTable_constraints loadX0Chip_faithful rustRows data valid

theorem loadX0Chip_transportTable_accesses (rustRows : List (Extracted.LoadX0Oracle.LoadX0Columns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (loadX0ChipOracle.assertZeros rustCols)) :
    List.Perm
      ((transportTable loadX0ChipRowCodec loadX0ChipOracle rustRows data).table.flatMap fun row =>
        LookupAccessList.active
          (nativeAccesses (Environment.fromArray row data)
            (⟨LoadX0Chip.circuit⟩ : Component (ZMod p)).operations))
      (rustRows.flatMap fun rustCols =>
        LookupAccessList.active (loadX0ChipOracle.rustAccesses rustCols)) :=
  transportTable_accesses_perm loadX0Chip_faithful rustRows data valid

theorem loadX0Chip_transportTable_spec (rustRows : List (Extracted.LoadX0Oracle.LoadX0Columns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (loadX0ChipOracle.assertZeros rustCols))
    (assumptions : (transportTable loadX0ChipRowCodec loadX0ChipOracle rustRows data).Assumptions)
    (guarantees : (transportTable loadX0ChipRowCodec loadX0ChipOracle rustRows data).Guarantees) :
    (transportTable loadX0ChipRowCodec loadX0ChipOracle rustRows data).Spec :=
  transportTable_spec loadX0Chip_faithful rustRows data valid assumptions guarantees

/-! ### `StoreByteChip` -/

theorem storeByteChip_transportTable_constraints (rustRows : List (Extracted.StoreByteOracle.StoreByteColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (storeByteChipOracle.assertZeros rustCols)) :
    (transportTable storeByteChipRowCodec storeByteChipOracle rustRows data).Constraints :=
  transportTable_constraints storeByteChip_faithful rustRows data valid

theorem storeByteChip_transportTable_accesses (rustRows : List (Extracted.StoreByteOracle.StoreByteColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (storeByteChipOracle.assertZeros rustCols)) :
    List.Perm
      ((transportTable storeByteChipRowCodec storeByteChipOracle rustRows data).table.flatMap fun row =>
        LookupAccessList.active
          (nativeAccesses (Environment.fromArray row data)
            (⟨StoreByteChip.circuit⟩ : Component (ZMod p)).operations))
      (rustRows.flatMap fun rustCols =>
        LookupAccessList.active (storeByteChipOracle.rustAccesses rustCols)) :=
  transportTable_accesses_perm storeByteChip_faithful rustRows data valid

theorem storeByteChip_transportTable_spec (rustRows : List (Extracted.StoreByteOracle.StoreByteColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (storeByteChipOracle.assertZeros rustCols))
    (assumptions : (transportTable storeByteChipRowCodec storeByteChipOracle rustRows data).Assumptions)
    (guarantees : (transportTable storeByteChipRowCodec storeByteChipOracle rustRows data).Guarantees) :
    (transportTable storeByteChipRowCodec storeByteChipOracle rustRows data).Spec :=
  transportTable_spec storeByteChip_faithful rustRows data valid assumptions guarantees

/-! ### `StoreHalfChip` -/

theorem storeHalfChip_transportTable_constraints (rustRows : List (Extracted.StoreHalfOracle.StoreHalfColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (storeHalfChipOracle.assertZeros rustCols)) :
    (transportTable storeHalfChipRowCodec storeHalfChipOracle rustRows data).Constraints :=
  transportTable_constraints storeHalfChip_faithful rustRows data valid

theorem storeHalfChip_transportTable_accesses (rustRows : List (Extracted.StoreHalfOracle.StoreHalfColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (storeHalfChipOracle.assertZeros rustCols)) :
    List.Perm
      ((transportTable storeHalfChipRowCodec storeHalfChipOracle rustRows data).table.flatMap fun row =>
        LookupAccessList.active
          (nativeAccesses (Environment.fromArray row data)
            (⟨StoreHalfChip.circuit⟩ : Component (ZMod p)).operations))
      (rustRows.flatMap fun rustCols =>
        LookupAccessList.active (storeHalfChipOracle.rustAccesses rustCols)) :=
  transportTable_accesses_perm storeHalfChip_faithful rustRows data valid

theorem storeHalfChip_transportTable_spec (rustRows : List (Extracted.StoreHalfOracle.StoreHalfColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (storeHalfChipOracle.assertZeros rustCols))
    (assumptions : (transportTable storeHalfChipRowCodec storeHalfChipOracle rustRows data).Assumptions)
    (guarantees : (transportTable storeHalfChipRowCodec storeHalfChipOracle rustRows data).Guarantees) :
    (transportTable storeHalfChipRowCodec storeHalfChipOracle rustRows data).Spec :=
  transportTable_spec storeHalfChip_faithful rustRows data valid assumptions guarantees

/-! ### `StoreWordChip` -/

theorem storeWordChip_transportTable_constraints (rustRows : List (Extracted.StoreWordOracle.StoreWordColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (storeWordChipOracle.assertZeros rustCols)) :
    (transportTable storeWordChipRowCodec storeWordChipOracle rustRows data).Constraints :=
  transportTable_constraints storeWordChip_faithful rustRows data valid

theorem storeWordChip_transportTable_accesses (rustRows : List (Extracted.StoreWordOracle.StoreWordColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (storeWordChipOracle.assertZeros rustCols)) :
    List.Perm
      ((transportTable storeWordChipRowCodec storeWordChipOracle rustRows data).table.flatMap fun row =>
        LookupAccessList.active
          (nativeAccesses (Environment.fromArray row data)
            (⟨StoreWordChip.circuit⟩ : Component (ZMod p)).operations))
      (rustRows.flatMap fun rustCols =>
        LookupAccessList.active (storeWordChipOracle.rustAccesses rustCols)) :=
  transportTable_accesses_perm storeWordChip_faithful rustRows data valid

theorem storeWordChip_transportTable_spec (rustRows : List (Extracted.StoreWordOracle.StoreWordColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (storeWordChipOracle.assertZeros rustCols))
    (assumptions : (transportTable storeWordChipRowCodec storeWordChipOracle rustRows data).Assumptions)
    (guarantees : (transportTable storeWordChipRowCodec storeWordChipOracle rustRows data).Guarantees) :
    (transportTable storeWordChipRowCodec storeWordChipOracle rustRows data).Spec :=
  transportTable_spec storeWordChip_faithful rustRows data valid assumptions guarantees

/-! ### `StoreDoubleChip` -/

theorem storeDoubleChip_transportTable_constraints (rustRows : List (Extracted.StoreDoubleOracle.StoreDoubleColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (storeDoubleChipOracle.assertZeros rustCols)) :
    (transportTable storeDoubleChipRowCodec storeDoubleChipOracle rustRows data).Constraints :=
  transportTable_constraints storeDoubleChip_faithful rustRows data valid

theorem storeDoubleChip_transportTable_accesses (rustRows : List (Extracted.StoreDoubleOracle.StoreDoubleColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (storeDoubleChipOracle.assertZeros rustCols)) :
    List.Perm
      ((transportTable storeDoubleChipRowCodec storeDoubleChipOracle rustRows data).table.flatMap fun row =>
        LookupAccessList.active
          (nativeAccesses (Environment.fromArray row data)
            (⟨StoreDoubleChip.circuit⟩ : Component (ZMod p)).operations))
      (rustRows.flatMap fun rustCols =>
        LookupAccessList.active (storeDoubleChipOracle.rustAccesses rustCols)) :=
  transportTable_accesses_perm storeDoubleChip_faithful rustRows data valid

theorem storeDoubleChip_transportTable_spec (rustRows : List (Extracted.StoreDoubleOracle.StoreDoubleColumns (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (storeDoubleChipOracle.assertZeros rustCols))
    (assumptions : (transportTable storeDoubleChipRowCodec storeDoubleChipOracle rustRows data).Assumptions)
    (guarantees : (transportTable storeDoubleChipRowCodec storeDoubleChipOracle rustRows data).Guarantees) :
    (transportTable storeDoubleChipRowCodec storeDoubleChipOracle rustRows data).Spec :=
  transportTable_spec storeDoubleChip_faithful rustRows data valid assumptions guarantees

/-! ### `MulChip` -/

theorem mulChip_transportTable_constraints (rustRows : List (Extracted.MulOracle.MulCols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (mulChipOracle.assertZeros rustCols)) :
    (transportTable mulChipRowCodec mulChipOracle rustRows data).Constraints :=
  transportTable_constraints mulChip_faithful rustRows data valid

theorem mulChip_transportTable_accesses (rustRows : List (Extracted.MulOracle.MulCols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (mulChipOracle.assertZeros rustCols)) :
    List.Perm
      ((transportTable mulChipRowCodec mulChipOracle rustRows data).table.flatMap fun row =>
        LookupAccessList.active
          (nativeAccesses (Environment.fromArray row data)
            (⟨MulChip.circuit⟩ : Component (ZMod p)).operations))
      (rustRows.flatMap fun rustCols =>
        LookupAccessList.active (mulChipOracle.rustAccesses rustCols)) :=
  transportTable_accesses_perm mulChip_faithful rustRows data valid

theorem mulChip_transportTable_spec (rustRows : List (Extracted.MulOracle.MulCols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (mulChipOracle.assertZeros rustCols))
    (assumptions : (transportTable mulChipRowCodec mulChipOracle rustRows data).Assumptions)
    (guarantees : (transportTable mulChipRowCodec mulChipOracle rustRows data).Guarantees) :
    (transportTable mulChipRowCodec mulChipOracle rustRows data).Spec :=
  transportTable_spec mulChip_faithful rustRows data valid assumptions guarantees

/-! ### `DivRemChip` -/

theorem divRemChip_transportTable_constraints (rustRows : List (Extracted.DivRemOracle.DivRemCols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (divRemChipOracle.assertZeros rustCols)) :
    (transportTable divRemChipRowCodec divRemChipOracle rustRows data).Constraints :=
  transportTable_constraints divRemChip_faithful rustRows data valid

theorem divRemChip_transportTable_accesses (rustRows : List (Extracted.DivRemOracle.DivRemCols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (divRemChipOracle.assertZeros rustCols)) :
    List.Perm
      ((transportTable divRemChipRowCodec divRemChipOracle rustRows data).table.flatMap fun row =>
        LookupAccessList.active
          (nativeAccesses (Environment.fromArray row data)
            (⟨DivRemChip.circuit⟩ : Component (ZMod p)).operations))
      (rustRows.flatMap fun rustCols =>
        LookupAccessList.active (divRemChipOracle.rustAccesses rustCols)) :=
  transportTable_accesses_perm divRemChip_faithful rustRows data valid

theorem divRemChip_transportTable_spec (rustRows : List (Extracted.DivRemOracle.DivRemCols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (divRemChipOracle.assertZeros rustCols))
    (assumptions : (transportTable divRemChipRowCodec divRemChipOracle rustRows data).Assumptions)
    (guarantees : (transportTable divRemChipRowCodec divRemChipOracle rustRows data).Guarantees) :
    (transportTable divRemChipRowCodec divRemChipOracle rustRows data).Spec :=
  transportTable_spec divRemChip_faithful rustRows data valid assumptions guarantees

/-! ### `AluX0Chip` -/

theorem aluX0Chip_transportTable_constraints (rustRows : List (Extracted.AluX0Oracle.AluX0Cols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (aluX0ChipOracle.assertZeros rustCols)) :
    (transportTable aluX0ChipRowCodec aluX0ChipOracle rustRows data).Constraints :=
  transportTable_constraints aluX0Chip_faithful rustRows data valid

theorem aluX0Chip_transportTable_accesses (rustRows : List (Extracted.AluX0Oracle.AluX0Cols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (aluX0ChipOracle.assertZeros rustCols)) :
    List.Perm
      ((transportTable aluX0ChipRowCodec aluX0ChipOracle rustRows data).table.flatMap fun row =>
        LookupAccessList.active
          (nativeAccesses (Environment.fromArray row data)
            (⟨AluX0Chip.circuit⟩ : Component (ZMod p)).operations))
      (rustRows.flatMap fun rustCols =>
        LookupAccessList.active (aluX0ChipOracle.rustAccesses rustCols)) :=
  transportTable_accesses_perm aluX0Chip_faithful rustRows data valid

theorem aluX0Chip_transportTable_spec (rustRows : List (Extracted.AluX0Oracle.AluX0Cols (ZMod p)))
    (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (aluX0ChipOracle.assertZeros rustCols))
    (assumptions : (transportTable aluX0ChipRowCodec aluX0ChipOracle rustRows data).Assumptions)
    (guarantees : (transportTable aluX0ChipRowCodec aluX0ChipOracle rustRows data).Guarantees) :
    (transportTable aluX0ChipRowCodec aluX0ChipOracle rustRows data).Spec :=
  transportTable_spec aluX0Chip_faithful rustRows data valid assumptions guarantees


end SP1Clean.Composition
