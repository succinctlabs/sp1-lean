import SP1Clean.Soundness.RowView
import SP1Clean.Model.SailWrap
import SP1Clean.Math.Word
import SP1Clean.Soundness.RowEffectDefs
import SP1Clean.Soundness.ProgramConsistency

/-! # `ChipKind` / `ChipRow` — the heterogeneous trace row, dispatched by *value*

A single ordered trace mixing rows of different chips. Every per-row bus projection in
`Soundness/*Consistency.lean` is defined once over the chip-agnostic `Trace.RowView`; a `ChipRow` maps to
its `RowView` via `ChipRow.view`, and one `List (ChipRow …)` yields one `List RowView` whose interleaved
PC chain / memory consistency are genuinely cross-chip.

A `ChipKind` is a **structure of functions**: a chip registers one value (its `Inputs`/`Cols` type maps,
the five projections, and its `reaches_sail` proof), a `ChipRow` names its kind by value, and the capstone
dispatches the Sail step generically via `r.kind.reaches_sail` — no `cases`, no central edit. Adding a chip
touches no file here; it defines its `kind` next to its Sail bridge (`Chips/<Op>Bridge.lean`).

`ChipKind`/`ChipRow` are parameterized **explicitly** by `(p : ℕ) [Fact p.Prime] [Fact (2^17 < p)]`:
auto-generalizing `p` from a `variable` block breaks inference of the dependent `kind` field at use sites.

`view.is_real` is the **input** selector (`inp.is_real`): the chip commits it into the `is_real` column and
gates every bus emission by it, and it is exactly what the chip `Spec`'s gated identity and the Sail bridge
key on — so the bus gating, the semantic clause, and the Sail step all reference one selector. -/

open LeanRV64D.Defs
namespace SP1Clean.Soundness

open SP1Clean
open Sail LeanRV64D LeanRV64D.Functions

/-- A chip's registration into the heterogeneous trace: its input/column type maps and the projections
the soundness capstone consumes. `reaches_sail` is the chip's verified Sail step — on a real row, the chip
`Spec` drives the RISC-V Sail execution to agree with the SP1 chip emulation (`sailEquiv`), whose own
register/PC read (and, for J-type, immediate-decode) preconditions are quantified internally per kind. A
chip supplies `reaches_sail` as a thin wrapper around its `<op>_chip_reaches_sail` bridge lemma. -/
structure ChipKind (p : ℕ) [Fact p.Prime] [Fact (2 ^ 17 < p)] where
  /-- The chip's SP1 `MachineAir::name()` string (e.g. `"Add"`) — its stable, auditable identity in the
  coverage table (`Soundness/Coverage.lean`) and the registry. Non-dependent and placed **first** so the
  explicit `(p)` parameterization and the dependent `kind`-field inference noted above are undisturbed. -/
  name : String
  /-- The chip's input type map (e.g. `AddChip.Inputs`). -/
  Inputs : TypeMap
  /-- The chip's committed-column type map (e.g. `Extracted.AddCols`). -/
  Cols : TypeMap
  /-- The chip-agnostic bus view (shared reader blocks, `is_real`, the rd write value, the opcode). -/
  view : Inputs (ZMod p) → Cols (ZMod p) → Trace.RowView (ZMod p)
  /-- The per-row in-circuit contract — the chip's verified `Spec` (e.g. `AddChip.Spec`). -/
  chipSpec : Inputs (ZMod p) → Cols (ZMod p) → ProverData (ZMod p) → Prop
  /-- The op-specific RISC-V Sail ≡ SP1-emulation statement in a Sail state. Each kind quantifies the
  row's own register/PC read preconditions **internally** — ALU/R-type over a PC read + the two source
  register reads `rs1`/`rs2` (keyed to `op_b_val`/`op_c_val`); J-type/JAL over a PC read + the
  immediate-decode fact. Folding the reads inside `sailEquiv` keeps the capstone agnostic to a row's
  register arity: it only ever asks for `sailEquiv inp cols s`, never naming `rs1`/`rs2`. -/
  sailEquiv : Inputs (ZMod p) → Cols (ZMod p) → SailState → Prop
  /-- **The chip's Sail step.** On a real row, the chip `Spec` drives `sailEquiv` (whose internal
  read/decode preconditions the downstream Sail-state consumer supplies). -/
  reaches_sail : ∀ (inp : Inputs (ZMod p)) (cols : Cols (ZMod p)) (data : ProverData (ZMod p))
      (s : SailState),
    (view inp cols).is_real = 1 →
    chipSpec inp cols data →
    sailEquiv inp cols s
  /-- **The chip-specific "row is ready to advance" bundle** (SC Phase 4): the extra facts the trace
  dispatcher supplies per chip beyond the uniform refinement + `Spec` — the reader-passthrough
  well-formedness (`cols = main inp`, i.e. `inp.adapter = cols.adapter`), the routing invariant (`op_a ≠ 0`
  for register-writing chips, or the active-operation flag for multi-op chips), and any pc-limb bounds not
  already in the `Spec`. Defaults to `True`; each migrated chip overrides it with exactly what its `advance`
  proof consumes. Analogue of how `sailEquiv` folds the chip's own read/decode preconditions internally. -/
  advanceReady : Inputs (ZMod p) → Cols (ZMod p) → Target.GuestProgram → SailState → Prop :=
    fun _ _ _ _ => True
  /-- **The chip's uniform `advance` obligation** (SC Phase 4 — the semantic model core): in a state `s`
  refining this row (`SailConfigured`, ROM loaded, the committed pc, and the operand-value bound) with the
  program-bus decode (`decodedInROM`) and the chip's `advanceReady` bundle, one real Sail `try_step`
  produces the row's committed `RowEffect` (the PC write + the `op_a` register write + ROM/config
  preservation). This is `TargetObligations.lift` restricted to one chip's rows; the dispatcher
  (`chipRows_advance_sound`) assembles the per-chip `advance`s into the whole-trace `lift`. `Option (PLift …)`
  so chips migrate incrementally — `none` until a chip proves it (Add/Sub/Addi so far); `PLift` lifts the
  obligation `Prop` into a `Type` that `Option` accepts. -/
  advance : Option (PLift (∀ (inp : Inputs (ZMod p)) (cols : Cols (ZMod p)) (data : ProverData (ZMod p))
      (prog : Target.GuestProgram) (s : SailState),
    (view inp cols).is_real = 1 →
    chipSpec inp cols data →
    Target.SailConfigured s → Target.RomLoaded prog s →
    s.regs.get? Register.PC = some (Target.rcvPcOf (stateAccess (view inp cols))) →
    Target.ValueOperandsBound (view inp cols) s →
    Target.decodedInROM prog (programAccess (view inp cols)).toRow →
    advanceReady inp cols prog s →
    ∃ s', Target.SailStep s s' ∧ Target.RowEffect prog (view inp cols) s s')) := none

/-- A committed trace row: a chip `kind` together with that chip's inputs + committed column struct. The
dependent `inputs`/`cols` fields take their types from `kind`, so a `List (ChipRow p)` freely interleaves
rows of different chips. -/
structure ChipRow (p : ℕ) [Fact p.Prime] [Fact (2 ^ 17 < p)] where
  kind : ChipKind p
  inputs : kind.Inputs (ZMod p)
  cols : kind.Cols (ZMod p)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip-agnostic bus view (projects through `r.kind`). -/
def ChipRow.view (r : ChipRow p) : Trace.RowView (ZMod p) := r.kind.view r.inputs r.cols

/-- The row's `is_real` selector (= the input selector the buses gate on). -/
def ChipRow.is_real (r : ChipRow p) : ZMod p := r.view.is_real

/-- The per-row in-circuit contract — the chip's verified `Spec`, the hypothesis the capstone consumes.
(`data`-first arg order keeps `r.chipSpec data` working by dot notation.) -/
def ChipRow.chipSpec (data : ProverData (ZMod p)) (r : ChipRow p) : Prop :=
  r.kind.chipSpec r.inputs r.cols data

/-- The op-specific RISC-V Sail ≡ SP1-emulation statement (projects through `r.kind`). -/
def ChipRow.sailEquiv (r : ChipRow p) (s : SailState) : Prop :=
  r.kind.sailEquiv r.inputs r.cols s

end SP1Clean.Soundness
