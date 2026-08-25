import SP1Clean.Soundness.TypedTime
import SP1Clean.Soundness.StatePcClass
import SP1Clean.Soundness.StateCanon
import SP1Clean.Soundness.GoodnessFilter

/-! # CPUState clock contracts for the supported instruction chips

Each theorem below pins the actual `Readers.CPUState.circuit` composed by one chip.  The contracts
are deliberately chip-level and syntactic: arithmetic gadgets may be reorganized freely as long as
the chip retains a CPU reader fed by the State columns and active-row selector exposed in its
`RowView`.
-/

namespace SP1Clean.Soundness

open Air.Flat Circuit
open SP1Clean.Channels (StateMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- Common proof for chips whose first top-level subcircuit is the ordinary straight-line CPU
reader.  This macro only removes declaration boilerplate; every expansion still proves membership
in that concrete chip's `main` operation list. -/
local macro "firstStraightCPUTimeContract" inputs:term "," circuit:term "," main:term ","
    rowView:term : tactic =>
  `(tactic| (
    unfold CircuitCPUStateTimeContract
    dsimp only
    let input : Var $inputs (ZMod p) := varFromOffset $inputs 0
    let offset := size $inputs
    refine ⟨offset,
      ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8,
        input.is_real⟩, ?_, ?_⟩
    · simp only [input, offset, $circuit:term, $main:term, circuit_norm]
    · intro env
      constructor <;> simp only [input, $circuit:term, $rowView:term, circuit_norm]))

/-- As `firstStraightCPUTimeContract`, for the load chips whose row selector is a named sum of
width flags rather than a single `is_real` column. -/
local macro "widthGatedStraightCPUTimeContract" inputs:term "," circuit:term "," main:term ","
    rowView:term "," isReal:term "," gate:term : tactic =>
  `(tactic| (
    unfold CircuitCPUStateTimeContract
    dsimp only
    let input : Var $inputs (ZMod p) := varFromOffset $inputs 0
    let offset := size $inputs
    refine ⟨offset,
      ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8,
        $gate input⟩, ?_, ?_⟩
    · simp only [input, offset, $circuit:term, $main:term, circuit_norm]
    · intro env
      constructor <;> simp only [input, $rowView:term, $isReal:term, circuit_norm]))

theorem AddChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (AddChip.circuit (p := p)) AddChip.rowView := by
  firstStraightCPUTimeContract AddChip.Inputs, AddChip.circuit, AddChip.main, AddChip.rowView

theorem AddiChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (AddiChip.circuit (p := p)) AddiChip.rowView := by
  firstStraightCPUTimeContract AddiChip.Inputs, AddiChip.circuit, AddiChip.main, AddiChip.rowView

theorem AddwChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (AddwChip.circuit (p := p)) AddwChip.rowView := by
  firstStraightCPUTimeContract AddwChip.Inputs, AddwChip.circuit, AddwChip.main, AddwChip.rowView

theorem SubChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (SubChip.circuit (p := p)) SubChip.rowView := by
  firstStraightCPUTimeContract SubChip.Inputs, SubChip.circuit, SubChip.main, SubChip.rowView

theorem SubwChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (SubwChip.circuit (p := p)) SubwChip.rowView := by
  firstStraightCPUTimeContract SubwChip.Inputs, SubwChip.circuit, SubwChip.main, SubwChip.rowView

theorem BitwiseChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (BitwiseChip.circuit (p := p)) BitwiseChip.rowView := by
  firstStraightCPUTimeContract BitwiseChip.Inputs, BitwiseChip.circuit, BitwiseChip.main,
    BitwiseChip.rowView

theorem LtChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (LtChip.circuit (p := p)) LtChip.rowView := by
  firstStraightCPUTimeContract LtChip.Inputs, LtChip.circuit, LtChip.main, LtChip.rowView

theorem ShiftLeftChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (ShiftLeftChip.circuit (p := p)) ShiftLeftChip.rowView := by
  firstStraightCPUTimeContract ShiftLeftChip.Inputs, ShiftLeftChip.circuit, ShiftLeftChip.main,
    ShiftLeftChip.rowView

-- `ShiftRightChip.main` is the longest operation list in the registry, so this entry recurses deepest
-- when `simp` unfolds that list — but it still runs at the plain default like its ~20 siblings.
-- Measured bracket (128, 256], i.e. 2x headroom under the 512 default; the former 4000 ceiling was a
-- never-measured budget, ~16x over.
theorem ShiftRightChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (ShiftRightChip.circuit (p := p))
      ShiftRightChip.rowView := by
  firstStraightCPUTimeContract ShiftRightChip.Inputs, ShiftRightChip.circuit, ShiftRightChip.main,
    ShiftRightChip.rowView

theorem UTypeChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (UTypeChip.circuit (p := p)) UTypeChip.rowView := by
  unfold CircuitCPUStateTimeContract
  dsimp only
  let input : Var UTypeChip.Inputs (ZMod p) := varFromOffset UTypeChip.Inputs 0
  let offset := size UTypeChip.Inputs
  refine ⟨offset + 7,
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8,
      input.is_real⟩, ?_, ?_⟩
  · simp only [input, offset, UTypeChip.circuit, UTypeChip.main, circuit_norm]
  · intro env
    constructor <;> simp only [input, UTypeChip.circuit, UTypeChip.rowView, circuit_norm]

theorem JalChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (JalChip.circuit (p := p)) JalChip.rowView := by
  unfold CircuitCPUStateTimeContract
  dsimp only
  let input : Var JalChip.Inputs (ZMod p) := varFromOffset JalChip.Inputs 0
  let offset := size JalChip.Inputs
  refine ⟨offset + 8,
    ⟨input.state,
      #v[var { index := offset }, var { index := offset + 1 }, var { index := offset + 2 }],
      8, input.is_real⟩, ?_, ?_⟩
  · simp only [input, offset, JalChip.circuit, JalChip.main, circuit_norm]
  · intro env
    constructor <;> simp only [input, JalChip.circuit, JalChip.rowView, circuit_norm]

theorem JalrChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (JalrChip.circuit (p := p)) JalrChip.rowView := by
  unfold CircuitCPUStateTimeContract
  dsimp only
  let input : Var JalrChip.Inputs (ZMod p) := varFromOffset JalrChip.Inputs 0
  let offset := size JalrChip.Inputs
  refine ⟨offset + 9,
    ⟨input.state,
      #v[var { index := offset } - var { index := offset + 8 }, var { index := offset + 1 },
        var { index := offset + 2 }], 8, input.is_real⟩, ?_, ?_⟩
  · simp only [input, offset, JalrChip.circuit, JalrChip.main, circuit_norm]
    right
    left
    rfl
  · intro env
    constructor <;> simp only [input, JalrChip.circuit, JalrChip.rowView, circuit_norm]

theorem BranchChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (BranchChip.circuit (p := p)) BranchChip.rowView := by
  unfold CircuitCPUStateTimeContract
  dsimp only
  let input : Var BranchChip.Inputs (ZMod p) := varFromOffset BranchChip.Inputs 0
  let offset := size BranchChip.Inputs
  refine ⟨offset + 20,
    ⟨input.state,
      #v[var { index := offset + 7 }, var { index := offset + 8 },
        var { index := offset + 9 }], 8, input.is_real⟩, ?_, ?_⟩
  · simp only [input, offset, BranchChip.circuit, BranchChip.main, circuit_norm]
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    rfl
  · intro env
    constructor <;> simp only [input, BranchChip.circuit, BranchChip.rowView, circuit_norm]

theorem LoadByteChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (LoadByteChip.circuit (p := p))
      LoadByteChip.rowView := by
  widthGatedStraightCPUTimeContract LoadByteChip.Inputs, LoadByteChip.circuit, LoadByteChip.main,
    LoadByteChip.rowView, LoadByteChip.isReal, (fun input => input.is_lb + input.is_lbu)

theorem LoadHalfChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (LoadHalfChip.circuit (p := p))
      LoadHalfChip.rowView := by
  widthGatedStraightCPUTimeContract LoadHalfChip.Inputs, LoadHalfChip.circuit, LoadHalfChip.main,
    LoadHalfChip.rowView, LoadHalfChip.isReal, (fun input => input.is_lh + input.is_lhu)

theorem LoadWordChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (LoadWordChip.circuit (p := p))
      LoadWordChip.rowView := by
  widthGatedStraightCPUTimeContract LoadWordChip.Inputs, LoadWordChip.circuit, LoadWordChip.main,
    LoadWordChip.rowView, LoadWordChip.isReal, (fun input => input.is_lw + input.is_lwu)

theorem LoadX0Chip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (LoadX0Chip.circuit (p := p)) LoadX0Chip.rowView := by
  widthGatedStraightCPUTimeContract LoadX0Chip.Inputs, LoadX0Chip.circuit, LoadX0Chip.main,
    LoadX0Chip.rowView, LoadX0Chip.isReal, (fun input => input.is_lb + input.is_lbu + input.is_lh + input.is_lhu
      + input.is_lw + input.is_lwu + input.is_ld)

theorem LoadDoubleChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (LoadDoubleChip.circuit (p := p))
      LoadDoubleChip.rowView := by
  firstStraightCPUTimeContract LoadDoubleChip.Inputs, LoadDoubleChip.circuit,
    LoadDoubleChip.main, LoadDoubleChip.rowView

theorem StoreByteChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (StoreByteChip.circuit (p := p))
      StoreByteChip.rowView := by
  firstStraightCPUTimeContract StoreByteChip.Inputs, StoreByteChip.circuit, StoreByteChip.main,
    StoreByteChip.rowView

theorem StoreHalfChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (StoreHalfChip.circuit (p := p))
      StoreHalfChip.rowView := by
  firstStraightCPUTimeContract StoreHalfChip.Inputs, StoreHalfChip.circuit, StoreHalfChip.main,
    StoreHalfChip.rowView

theorem StoreWordChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (StoreWordChip.circuit (p := p))
      StoreWordChip.rowView := by
  firstStraightCPUTimeContract StoreWordChip.Inputs, StoreWordChip.circuit, StoreWordChip.main,
    StoreWordChip.rowView

theorem StoreDoubleChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (StoreDoubleChip.circuit (p := p))
      StoreDoubleChip.rowView := by
  firstStraightCPUTimeContract StoreDoubleChip.Inputs, StoreDoubleChip.circuit,
    StoreDoubleChip.main, StoreDoubleChip.rowView

theorem MulChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (MulChip.circuit (p := p)) MulChip.rowView := by
  firstStraightCPUTimeContract MulChip.Inputs, MulChip.circuit, MulChip.main, MulChip.rowView

theorem DivRemChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (DivRemChip.circuit (p := p)) DivRemChip.rowView := by
  unfold CircuitCPUStateTimeContract
  dsimp only
  let input : Var DivRemChip.Inputs (ZMod p) := varFromOffset DivRemChip.Inputs 0
  let offset := size DivRemChip.Inputs
  refine ⟨offset + 217,
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8,
      input.is_real⟩, ?_, ?_⟩
  · -- The CPU reader is the first composed subcircuit of the rewired `main` (the whole witness
    -- stream precedes it, hence the `offset + 217`).
    simp only [input, offset, DivRemChip.circuit, DivRemChip.main, circuit_norm]
    right
    simp only [DivRemChip.constrainRow, circuit_norm]
  · intro env
    constructor <;>
      simp only [input, DivRemChip.circuit, DivRemChip.rowView, circuit_norm]

theorem AluX0Chip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (AluX0Chip.circuit (p := p)) AluX0Chip.rowView := by
  firstStraightCPUTimeContract AluX0Chip.Inputs, AluX0Chip.circuit, AluX0Chip.main,
    AluX0Chip.rowView

/-! ## Registry and decoded-witness consequences -/

/-- A supported descriptor's physical Byte guarantees force its active semantic State edge to
advance by exactly eight natural-number ticks. -/
def StateTimeConstraintShape (chip : SupportedChip p) : Prop :=
  ∀ data physical,
    let env := Environment.fromArray physical data
    let row := chip.decodeRow data physical
    chip.table.operations.ChannelGuarantees Channels.byteChannel.toRaw env →
      row.is_real = 1 →
        Semantics.StateMsg.timeNat (statePushMessage row) =
          Semantics.StateMsg.timeNat (statePullMessage row) + 8

/-- Transport a circuit-local clock theorem to its supported descriptor without unfolding the
dependent registry record. -/
theorem stateTimeConstraintShape_of_circuit (kind : ChipKind p)
    (circuit : @GeneralFormalCircuit (ZMod p) kind.Inputs kind.Cols inferInstance
      kind.provableInputs kind.provableCols)
    (spec_eq : @GeneralFormalCircuit.Spec (ZMod p) kind.Inputs kind.Cols inferInstance
      kind.provableInputs kind.provableCols circuit = kind.chipSpec)
    (opcodes : List Opcode) (rdGuard : RdGuard)
    (shape : @CircuitStateTimeStep p _ kind.Inputs kind.Cols kind.provableInputs
      kind.provableCols circuit kind.view) :
    StateTimeConstraintShape ⟨kind, circuit, spec_eq, opcodes, rdGuard⟩ := by
  letI := kind.provableInputs
  letI := kind.provableCols
  intro data physical
  dsimp only
  intro guarantees real
  exact shape.step data physical guarantees real

/-- Registry-case boilerplate: install the descriptor's retained dependent instances and turn its
concrete CPU-reader contract into the uniform physical-row clock theorem. -/
local macro "timeRegistryCase " kind:term ", " contract:term : tactic =>
  `(tactic| (
    letI := ($kind:term).provableInputs
    letI := ($kind:term).provableCols
    apply stateTimeConstraintShape_of_circuit
    apply circuitStateTimeStep_of_cpuStateContract
    exact $contract:term))

/-- Every chip in the stable supported-machine registry derives strict clock progress from its own
physical CPU reader and the Byte channel. -/
theorem supportedChip_stateTimeConstraintShape (chip : SupportedChip p)
    (chipMem : chip ∈ supportedChips (p := p)) : StateTimeConstraintShape chip := by
  fin_cases chipMem
  · timeRegistryCase (AddChip.kind (p := p)), (AddChip.cpuStateTimeContract (p := p))
  · timeRegistryCase (AddiChip.kind (p := p)), (AddiChip.cpuStateTimeContract (p := p))
  · timeRegistryCase (AddwChip.kind (p := p)), (AddwChip.cpuStateTimeContract (p := p))
  · timeRegistryCase (SubChip.kind (p := p)), (SubChip.cpuStateTimeContract (p := p))
  · timeRegistryCase (SubwChip.kind (p := p)), (SubwChip.cpuStateTimeContract (p := p))
  · timeRegistryCase (BitwiseChip.kind (p := p)), (BitwiseChip.cpuStateTimeContract (p := p))
  · timeRegistryCase (LtChip.kind (p := p)), (LtChip.cpuStateTimeContract (p := p))
  · timeRegistryCase (ShiftLeftChip.kind (p := p)),
      (ShiftLeftChip.cpuStateTimeContract (p := p))
  · timeRegistryCase (ShiftRightChip.kind (p := p)),
      (ShiftRightChip.cpuStateTimeContract (p := p))
  · timeRegistryCase (JalChip.kind (p := p)), (JalChip.cpuStateTimeContract (p := p))
  · timeRegistryCase (JalrChip.kind (p := p)), (JalrChip.cpuStateTimeContract (p := p))
  · timeRegistryCase (BranchChip.kind (p := p)), (BranchChip.cpuStateTimeContract (p := p))
  · timeRegistryCase (UTypeChip.kind (p := p)), (UTypeChip.cpuStateTimeContract (p := p))
  · timeRegistryCase (LoadByteChip.kind (p := p)),
      (LoadByteChip.cpuStateTimeContract (p := p))
  · timeRegistryCase (LoadHalfChip.kind (p := p)),
      (LoadHalfChip.cpuStateTimeContract (p := p))
  · timeRegistryCase (LoadWordChip.kind (p := p)),
      (LoadWordChip.cpuStateTimeContract (p := p))
  · timeRegistryCase (LoadDoubleChip.kind (p := p)),
      (LoadDoubleChip.cpuStateTimeContract (p := p))
  · timeRegistryCase (LoadX0Chip.kind (p := p)), (LoadX0Chip.cpuStateTimeContract (p := p))
  · timeRegistryCase (StoreByteChip.kind (p := p)),
      (StoreByteChip.cpuStateTimeContract (p := p))
  · timeRegistryCase (StoreHalfChip.kind (p := p)),
      (StoreHalfChip.cpuStateTimeContract (p := p))
  · timeRegistryCase (StoreWordChip.kind (p := p)),
      (StoreWordChip.cpuStateTimeContract (p := p))
  · timeRegistryCase (StoreDoubleChip.kind (p := p)),
      (StoreDoubleChip.cpuStateTimeContract (p := p))
  · timeRegistryCase (MulChip.kind (p := p)), (MulChip.cpuStateTimeContract (p := p))
  · timeRegistryCase (DivRemChip.kind (p := p)), (DivRemChip.cpuStateTimeContract (p := p))
  · timeRegistryCase (AluX0Chip.kind (p := p)), (AluX0Chip.cpuStateTimeContract (p := p))

/-- One canonical decoded row inherits exact clock progress from its retained descriptor and the
Byte guarantees of that exact physical row. -/
theorem DecodedInstructionRow.stateTimeStep_of_byteGuarantees
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (tables : List (Table (ZMod p)))
    (decodedMem : decoded ∈ decodedInstructionRows (p := p) tables)
    (guarantees : decoded.chip.table.operations.ChannelGuarantees
      Channels.byteChannel.toRaw (decoded.environment data))
    (real : (decoded.toChipRow data).is_real = 1) :
    Semantics.StateMsg.timeNat (decodedStateEdge data decoded).2 =
      Semantics.StateMsg.timeNat (decodedStateEdge data decoded).1 + 8 := by
  exact supportedChip_stateTimeConstraintShape decoded.chip
    (decodedInstructionRows_chip_mem tables decodedMem) data decoded.physical guarantees real

/-- Finished Byte-channel grounding specializes to every row of the canonical typed instruction
decoder. -/
theorem decodedInstructionRow_byteGuarantees
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (decoded : DecodedInstructionRow p)
    (decodedMem : decoded ∈ decodedInstructionRows (p := p) witness.tables) :
    decoded.chip.table.operations.ChannelGuarantees Channels.byteChannel.toRaw
      (decoded.environment witness.data) := by
  apply channelGuarantees_of_mem_decodeInstructionTables witness.data Channels.byteChannel.toRaw
    (witness_instructionTables_aligned witness)
  · intro table tableMem
    exact (sp1_finishedChannel_guarantees witness constraints balanced table
      (witness.mem_allTables_of_mem_tables (List.mem_of_mem_take tableMem))).1
  · exact decodedMem

/-- Every active canonical instruction row advances its decoded State time by exactly eight. -/
theorem witness_realDecodedInstructionRows_timeStep
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ decoded ∈ realDecodedInstructionRows witness.data witness.tables,
      Semantics.StateMsg.timeNat (decodedStateEdge witness.data decoded).2 =
        Semantics.StateMsg.timeNat (decodedStateEdge witness.data decoded).1 + 8 := by
  intro decoded decodedMem
  rw [realDecodedInstructionRows, List.mem_filter] at decodedMem
  simp only [decide_eq_true_eq] at decodedMem
  exact decoded.stateTimeStep_of_byteGuarantees witness.data witness.tables decodedMem.1
    (decodedInstructionRow_byteGuarantees witness constraints balanced decoded decodedMem.1)
    decodedMem.2

/-- Consequently every active decoded State edge is strictly increasing in natural-number time. -/
theorem witness_realDecodedInstructionRows_time_increases
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ decoded ∈ realDecodedInstructionRows witness.data witness.tables,
      Semantics.StateMsg.timeNat (decodedStateEdge witness.data decoded).1 <
        Semantics.StateMsg.timeNat (decodedStateEdge witness.data decoded).2 := by
  intro decoded decodedMem
  rw [witness_realDecodedInstructionRows_timeStep witness constraints balanced decoded decodedMem]
  omega

/-! ## The canonicalized State trail (W3, external report Finding 2)

The StateBump table makes the raw decoded edge multiset unrankable — a bump edge carries the same
semantic time on both sides, so no strict rank exists for it.  The exhaustive trail is therefore
built over the **canonicalized** edges:

1. start from the with-bump endpoint balance
   (`realState_endpointBalanced_withBump_of_constraints`);
2. goodness-filter pass 1 (`clk_high < 2^24`, rank `timeNat`): instruction edges preserve
   `clk_high` literally and strictly advance the clock, bump pushes are range-checked in-circuit,
   and the boundary is canonical by the verifier row's own byte pulls
   (`witness_publicInput_limbBounds`);
3. goodness-filter pass 2 (`pc1, pc2 < 2^16`): instruction edges split by
   `witness_realDecodedRows_pcClass` into the limb-preserving and range-checked-target classes;
4. with every pulled side good, `stateBump_canon_eq` cancels each bump edge as a self-loop of the
   canonicalized balance (`endpointBalanced_of_cancel_loops`), the boundary endpoints reappear
   verbatim (`canonState_eq_self`), and the strictly-ranked instruction residue feeds the unchanged
   `RankedGrounding` engine through `timeNat_canonState`. -/

/-- The witness's boundary-verifier table carries the `sp1StateVerifier` circuit. -/
theorem witness_verifierTable_component (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    witness.verifierTable.component = ⟨sp1StateVerifier (p := p)⟩ := rfl

/-- Every committed public-boundary limb is in range: the boundary verifier's `Spec` is
`SP1StateBoundary.LimbBounds`, extracted through `Component.weakSoundness` from the verifier row's
constraints, its finished-channel byte pulls, and the State channel's trivial guarantee. -/
theorem witness_publicInput_limbBounds
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    SP1StateBoundary.LimbBounds witness.publicInput := by
  have tableConstraints : witness.verifierTable.Constraints :=
    constraints _ witness.mem_allTables_verifierTable
  have byteGuarantees := (sp1_finishedChannel_guarantees witness constraints balanced
    _ witness.mem_allTables_verifierTable).1
  have rowMem : (toElements witness.publicInput).toArray ∈ witness.verifierTable.table := by
    rw [EnsembleWitness.verifierTable_table]
    exact List.mem_singleton_self _
  have hlist : witness.verifierTable.component.circuit.channelsWithGuarantees =
      [Channels.stateChannel.toRaw, Channels.byteChannel.toRaw] := rfl
  have guarantees : witness.verifierTable.component.operations.FullGuarantees
      (witness.verifierTable.environment (toElements witness.publicInput).toArray) := by
    simp only [Component.guarantees_iff, Component.rowOperations]
    rw [GeneralFormalCircuit.guarantees_iff]
    intro channel channelMem
    show witness.verifierTable.component.rowOperations.ChannelGuarantees channel
      (witness.verifierTable.environment (toElements witness.publicInput).toArray)
    rw [← Component.channelGuarantees_iff]
    rw [hlist] at channelMem
    rcases List.mem_cons.mp channelMem with rfl | channelMem
    · intro i hi hmult
      exact stateChannel_interaction_guarantees _ hmult
    · rw [List.mem_singleton.mp channelMem]
      exact byteGuarantees _ rowMem
  have spec := (witness.verifierTable.component.weakSoundness
    (env := witness.verifierTable.environment (toElements witness.publicInput).toArray)
    (by rw [witness_verifierTable_component]; trivial) (tableConstraints _ rowMem) guarantees).1
  rw [witness_verifierTable_component] at spec
  have spec' : SP1StateBoundary.LimbBounds
      (valueFromOffset SP1PublicIO 0
        (Environment.fromInput witness.publicInput witness.data)) := spec
  rwa [ProvableType.valueFromOffset_zero_fromInput_eq] at spec'

/-- The public initial State message's limbs, in the recombined form the State bus carries: the
boundary `LimbBounds` recombine to a genuine 24-bit clock split and 16-bit pc limbs. -/
theorem initialBoundaryStateMessage_bounds (pi : SP1PublicIO (ZMod p))
    (h : SP1StateBoundary.LimbBounds pi) :
    (initialBoundaryStateMessage pi).clk_high.val < 2 ^ 24 ∧
      (initialBoundaryStateMessage pi).clk_low.val < 2 ^ 24 ∧
      (initialBoundaryStateMessage pi).pc0.val < 2 ^ 16 ∧
      (initialBoundaryStateMessage pi).pc1.val < 2 ^ 16 ∧
      (initialBoundaryStateMessage pi).pc2.val < 2 ^ 16 := by
  have hp := Fact.out (p := 2 ^ 25 < p)
  simp only [SP1StateBoundary.LimbBounds] at h
  obtain ⟨h016, h1624, h2432, h3248, hpc0, hpc1, hpc2, -, -, -, -, -, -, -⟩ := h
  have v256 : ((256 : ZMod p)).val = 256 := by
    rw [show ((256 : ZMod p)) = ((256 : ℕ) : ZMod p) by norm_cast,
      ZMod.val_natCast_of_lt (by omega)]
  have v65536 : ((65536 : ZMod p)).val = 65536 := by
    rw [show ((65536 : ZMod p)) = ((65536 : ℕ) : ZMod p) by norm_cast,
      ZMod.val_natCast_of_lt (by omega)]
  refine ⟨?_, ?_, hpc0, hpc1, hpc2⟩
  · show (pi.init_clk_24_32 + pi.init_clk_32_48 * 256).val < 2 ^ 24
    rw [val_recombine v256 (by omega)]
    omega
  · show (pi.init_clk_0_16 + pi.init_clk_16_24 * 65536).val < 2 ^ 24
    rw [val_recombine v65536 (by omega)]
    omega

/-- The public final State message's limbs, as `initialBoundaryStateMessage_bounds`. -/
theorem finalBoundaryStateMessage_bounds (pi : SP1PublicIO (ZMod p))
    (h : SP1StateBoundary.LimbBounds pi) :
    (finalBoundaryStateMessage pi).clk_high.val < 2 ^ 24 ∧
      (finalBoundaryStateMessage pi).clk_low.val < 2 ^ 24 ∧
      (finalBoundaryStateMessage pi).pc0.val < 2 ^ 16 ∧
      (finalBoundaryStateMessage pi).pc1.val < 2 ^ 16 ∧
      (finalBoundaryStateMessage pi).pc2.val < 2 ^ 16 := by
  have hp := Fact.out (p := 2 ^ 25 < p)
  simp only [SP1StateBoundary.LimbBounds] at h
  obtain ⟨-, -, -, -, -, -, -, h016, h1624, h2432, h3248, hpc0, hpc1, hpc2⟩ := h
  have v256 : ((256 : ZMod p)).val = 256 := by
    rw [show ((256 : ZMod p)) = ((256 : ℕ) : ZMod p) by norm_cast,
      ZMod.val_natCast_of_lt (by omega)]
  have v65536 : ((65536 : ZMod p)).val = 65536 := by
    rw [show ((65536 : ZMod p)) = ((65536 : ℕ) : ZMod p) by norm_cast,
      ZMod.val_natCast_of_lt (by omega)]
  refine ⟨?_, ?_, hpc0, hpc1, hpc2⟩
  · show (pi.final_clk_24_32 + pi.final_clk_32_48 * 256).val < 2 ^ 24
    rw [val_recombine v256 (by omega)]
    omega
  · show (pi.final_clk_0_16 + pi.final_clk_16_24 * 65536).val < 2 ^ 24
    rw [val_recombine v65536 (by omega)]
    omega

/-- Membership in the active StateBump rows unpacks to physical-table membership plus the live
selector. -/
theorem mem_realStateBumpRows (witness : EnsembleWitness (sp1Ensemble (p := p)))
    {row : Array (ZMod p)} (rowMem : row ∈ realStateBumpRows witness) :
    row ∈ (stateBumpTable witness).table ∧
      (stateBumpRow (stateBumpTable witness) row).is_real = 1 := by
  rw [realStateBumpRows, List.mem_filter] at rowMem
  simpa only [decide_eq_true_eq] using rowMem

/-- Both endpoints of a decoded State edge read the same physical `clk_high` column, so the first
goodness pass's preservation condition is definitional. -/
theorem decodedStateEdge_snd_clk_high (data : ProverData (ZMod p))
    (decoded : DecodedInstructionRow p) :
    ((decodedStateEdge data decoded).2).clk_high = ((decodedStateEdge data decoded).1).clk_high :=
  rfl

/-- The two goodness-filter passes over the with-bump State balance, exported at their raw
strength: every active instruction edge's endpoints carry a genuine 24-bit `clk_high` and genuine
16-bit upper pc limbs, and every active StateBump row's edge canonicalizes to a self-loop.  The
clk facts feed `timeNat_canonState` (the trail's rank transport and the walk's clock telescopes),
the pc facts feed `pcBits_canonState` (the capstone's `PcWalk` transport), and the loop fact
cancels the bump edges from the canonicalized balance. -/
theorem witness_stateEdges_goodness
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    (∀ decoded ∈ realDecodedInstructionRows witness.data witness.tables,
      ((decodedStateEdge witness.data decoded).1.clk_high.val < 2 ^ 24 ∧
        (decodedStateEdge witness.data decoded).2.clk_high.val < 2 ^ 24) ∧
      ((decodedStateEdge witness.data decoded).1.pc1.val < 2 ^ 16 ∧
        (decodedStateEdge witness.data decoded).1.pc2.val < 2 ^ 16) ∧
      ((decodedStateEdge witness.data decoded).2.pc1.val < 2 ^ 16 ∧
        (decodedStateEdge witness.data decoded).2.pc2.val < 2 ^ 16)) ∧
    ∀ row ∈ realStateBumpRows witness,
      canonState (StateBumpChip.pulledMessage (stateBumpRow (stateBumpTable witness) row)) =
        canonState (StateBumpChip.pushedMessage (stateBumpRow (stateBumpTable witness) row)) := by
  classical
  obtain ⟨ih, -, -, ip1, ip2⟩ := initialBoundaryStateMessage_bounds witness.publicInput
    (witness_publicInput_limbBounds witness constraints balanced)
  obtain ⟨fh, -, -, fp1, fp2⟩ := finalBoundaryStateMessage_bounds witness.publicInput
    (witness_publicInput_limbBounds witness constraints balanced)
  have balanced0 := realState_endpointBalanced_withBump_of_constraints witness constraints balanced
  -- pass 1: `clk_high < 2^24` is preserved by instruction edges and range-checked on bump pushes
  have pass1 := GoodnessFilter.good_of_endpointBalanced (fun e => e)
    (fun m : StateMsg (ZMod p) => m.clk_high.val < 2 ^ 24) Semantics.StateMsg.timeNat
    _ _ _ _ balanced0 ih fh ?pres1 ?cons1
  case pres1 =>
    intro e he
    obtain ⟨decoded, dmem, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp he)
    exact ⟨by rw [decodedStateEdge_snd_clk_high], fun _ =>
      witness_realDecodedInstructionRows_time_increases witness constraints balanced decoded dmem⟩
  case cons1 =>
    intro e he
    obtain ⟨row, rowMem, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp he)
    obtain ⟨tableMem, real⟩ := mem_realStateBumpRows witness rowMem
    exact (stateBump_pushedMessage_good
      (stateBumpTable_spec witness constraints balanced row tableMem) real).1
  -- pass 2: `pc1, pc2 < 2^16`; instruction edges split by the pc-limb classification
  rw [← Multiset.filter_add_not
    (fun e : StateMsg (ZMod p) × StateMsg (ZMod p) => e.2.pc1 = e.1.pc1 ∧ e.2.pc2 = e.1.pc2)
    (↑((realDecodedInstructionRows witness.data witness.tables).map
      (decodedStateEdge witness.data)) : Multiset (StateMsg (ZMod p) × StateMsg (ZMod p))),
    add_assoc] at balanced0
  have pass2 := GoodnessFilter.good_of_endpointBalanced (fun e => e)
    (fun m : StateMsg (ZMod p) => m.pc1.val < 2 ^ 16 ∧ m.pc2.val < 2 ^ 16)
    Semantics.StateMsg.timeNat _ _ _ _ balanced0 ⟨ip1, ip2⟩ ⟨fp1, fp2⟩ ?pres2 ?cons2
  case pres2 =>
    intro e he
    rw [Multiset.mem_filter] at he
    obtain ⟨he, hq⟩ := he
    obtain ⟨decoded, dmem, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp he)
    exact ⟨by rw [hq.1, hq.2], fun _ =>
      witness_realDecodedInstructionRows_time_increases witness constraints balanced decoded dmem⟩
  case cons2 =>
    intro e he
    rcases Multiset.mem_add.mp he with he | he
    · rw [Multiset.mem_filter] at he
      obtain ⟨he, hnq⟩ := he
      obtain ⟨decoded, dmem, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp he)
      rcases witness_realDecodedRows_pcClass witness constraints balanced decoded dmem
        with hkeep | hbound
      · exact absurd hkeep hnq
      · exact hbound
    · obtain ⟨row, rowMem, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp he)
      obtain ⟨tableMem, real⟩ := mem_realStateBumpRows witness rowMem
      exact (stateBump_pushedMessage_good
        (stateBumpTable_spec witness constraints balanced row tableMem) real).2
  refine ⟨fun decoded dmem => ?_, fun row rowMem => ?_⟩
  · have emem : decodedStateEdge witness.data decoded ∈
        (↑((realDecodedInstructionRows witness.data witness.tables).map
          (decodedStateEdge witness.data)) :
            Multiset (StateMsg (ZMod p) × StateMsg (ZMod p))) :=
      Multiset.mem_coe.mpr (List.mem_map_of_mem dmem)
    refine ⟨pass1.1 _ emem, ?_⟩
    by_cases hq : ((decodedStateEdge witness.data decoded).2.pc1 =
          (decodedStateEdge witness.data decoded).1.pc1 ∧
        (decodedStateEdge witness.data decoded).2.pc2 =
          (decodedStateEdge witness.data decoded).1.pc2)
    · exact pass2.1 _ (Multiset.mem_filter.mpr ⟨emem, hq⟩)
    · refine ⟨pass2.2 _ (Multiset.mem_add.mpr (Or.inl (Multiset.mem_filter.mpr ⟨emem, hq⟩))), ?_⟩
      rcases witness_realDecodedRows_pcClass witness constraints balanced decoded dmem
        with hkeep | hbound
      · exact absurd hkeep hq
      · exact hbound
  · obtain ⟨tableMem, real⟩ := mem_realStateBumpRows witness rowMem
    have h1 := pass1.2 _ (Multiset.mem_coe.mpr (List.mem_map_of_mem rowMem))
    have h2 := pass2.2 _ (Multiset.mem_add.mpr (Or.inr
      (Multiset.mem_coe.mpr (List.mem_map_of_mem rowMem))))
    exact stateBump_canon_eq_of_pulled_good
      (stateBumpTable_spec witness constraints balanced row tableMem) real h1 h2.1 h2.2

/-- Physical constraints plus four-bus balance construct an exhaustive, clock-ordered trail of all
active decoded instruction rows over their **canonicalized** State edges.  The StateBump rows'
re-limbing edges cancel as self-loops of the canonicalized balance, the boundary endpoints are
canonical by the verifier row's own byte pulls, and selector booleanity, the pc-limb classes, and
strict clock progress are all derived AIR facts; none remains a capstone premise. -/
theorem witness_realDecodedState_canonExhaustiveTrail
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    RankedGrounding.ExhaustiveTrail
      (↑(realDecodedInstructionRows witness.data witness.tables) :
        Multiset (DecodedInstructionRow p))
      (fun decoded =>
        (canonState (decodedStateEdge witness.data decoded).1,
         canonState (decodedStateEdge witness.data decoded).2))
      (initialBoundaryStateMessage witness.publicInput)
      (finalBoundaryStateMessage witness.publicInput) := by
  classical
  obtain ⟨instrGood, bumpCanon⟩ := witness_stateEdges_goodness witness constraints balanced
  obtain ⟨-, il, ip0, ip1, -⟩ := initialBoundaryStateMessage_bounds witness.publicInput
    (witness_publicInput_limbBounds witness constraints balanced)
  obtain ⟨-, fl, fp0, fp1, -⟩ := finalBoundaryStateMessage_bounds witness.publicInput
    (witness_publicInput_limbBounds witness constraints balanced)
  have cancelled := GoodnessFilter.endpointBalanced_of_cancel_loops _ _ _ _ _ ?loops
    (GoodnessFilter.endpointBalanced_map canonState _ _ _ _
      (realState_endpointBalanced_withBump_of_constraints witness constraints balanced))
  case loops =>
    intro l hl
    obtain ⟨row, rowMem, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp hl)
    exact bumpCanon row rowMem
  rw [canonState_eq_self il ip0 ip1, canonState_eq_self fl fp0 fp1] at cancelled
  refine RankedGrounding.exists_exhaustiveTrail_of_endpointBalanced _ _
    Semantics.StateMsg.timeNat _ _ ?_ ?_
  · exact GoodnessFilter.endpointBalanced_of_map (decodedStateEdge witness.data)
      (↑(realDecodedInstructionRows witness.data witness.tables))
      (fun e => (canonState e.1, canonState e.2))
      (initialBoundaryStateMessage witness.publicInput)
      (finalBoundaryStateMessage witness.publicInput) cancelled
  · intro decoded dmem
    obtain ⟨⟨hclkPull, hclkPush⟩, -, -⟩ := instrGood decoded (Multiset.mem_coe.mp dmem)
    show Semantics.StateMsg.timeNat (canonState (decodedStateEdge witness.data decoded).1) <
      Semantics.StateMsg.timeNat (canonState (decodedStateEdge witness.data decoded).2)
    rw [timeNat_canonState hclkPull, timeNat_canonState hclkPush]
    exact witness_realDecodedInstructionRows_time_increases witness constraints balanced decoded
      (Multiset.mem_coe.mp dmem)

end SP1Clean.Soundness
