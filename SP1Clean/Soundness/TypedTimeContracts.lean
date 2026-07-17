import SP1Clean.Soundness.TypedTime

/-! # CPUState clock contracts for the supported instruction chips

Each theorem below pins the actual `Readers.CPUState.circuit` composed by one chip.  The contracts
are deliberately chip-level and syntactic: arithmetic gadgets may be reorganized freely as long as
the chip retains a CPU reader fed by the State columns and active-row selector exposed in its
`RowView`.
-/

namespace SP1Clean.Soundness

open Air.Flat Circuit

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
    · simp [input, offset, $circuit:term, $main:term, circuit_norm]
    · intro env
      constructor <;> simp [input, $circuit:term, $rowView:term, circuit_norm]))

set_option maxHeartbeats 2000000 in
theorem AddChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (AddChip.circuit (p := p)) AddChip.rowView := by
  firstStraightCPUTimeContract AddChip.Inputs, AddChip.circuit, AddChip.main, AddChip.rowView

set_option maxHeartbeats 2000000 in
theorem AddiChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (AddiChip.circuit (p := p)) AddiChip.rowView := by
  firstStraightCPUTimeContract AddiChip.Inputs, AddiChip.circuit, AddiChip.main, AddiChip.rowView

set_option maxHeartbeats 2000000 in
theorem AddwChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (AddwChip.circuit (p := p)) AddwChip.rowView := by
  firstStraightCPUTimeContract AddwChip.Inputs, AddwChip.circuit, AddwChip.main, AddwChip.rowView

set_option maxHeartbeats 2000000 in
theorem SubChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (SubChip.circuit (p := p)) SubChip.rowView := by
  firstStraightCPUTimeContract SubChip.Inputs, SubChip.circuit, SubChip.main, SubChip.rowView

set_option maxHeartbeats 2000000 in
theorem SubwChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (SubwChip.circuit (p := p)) SubwChip.rowView := by
  firstStraightCPUTimeContract SubwChip.Inputs, SubwChip.circuit, SubwChip.main, SubwChip.rowView

set_option maxHeartbeats 2000000 in
theorem BitwiseChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (BitwiseChip.circuit (p := p)) BitwiseChip.rowView := by
  firstStraightCPUTimeContract BitwiseChip.Inputs, BitwiseChip.circuit, BitwiseChip.main,
    BitwiseChip.rowView

set_option maxHeartbeats 2000000 in
theorem LtChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (LtChip.circuit (p := p)) LtChip.rowView := by
  firstStraightCPUTimeContract LtChip.Inputs, LtChip.circuit, LtChip.main, LtChip.rowView

set_option maxHeartbeats 4000000 in
theorem ShiftLeftChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (ShiftLeftChip.circuit (p := p)) ShiftLeftChip.rowView := by
  firstStraightCPUTimeContract ShiftLeftChip.Inputs, ShiftLeftChip.circuit, ShiftLeftChip.main,
    ShiftLeftChip.rowView

set_option maxHeartbeats 4000000 in
theorem ShiftRightChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (ShiftRightChip.circuit (p := p))
      ShiftRightChip.rowView := by
  firstStraightCPUTimeContract ShiftRightChip.Inputs, ShiftRightChip.circuit, ShiftRightChip.main,
    ShiftRightChip.rowView

set_option maxHeartbeats 4000000 in
theorem UTypeChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (UTypeChip.circuit (p := p)) UTypeChip.rowView := by
  unfold CircuitCPUStateTimeContract
  dsimp only
  let input : Var UTypeChip.Inputs (ZMod p) := varFromOffset UTypeChip.Inputs 0
  let offset := size UTypeChip.Inputs
  refine ⟨offset + 7,
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8,
      input.is_real⟩, ?_, ?_⟩
  · simp [input, offset, UTypeChip.circuit, UTypeChip.main, circuit_norm]
  · intro env
    constructor <;> simp [input, UTypeChip.circuit, UTypeChip.rowView, circuit_norm]

set_option maxHeartbeats 4000000 in
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
  · simp [input, offset, JalChip.circuit, JalChip.main, circuit_norm]
  · intro env
    constructor <;> simp [input, JalChip.circuit, JalChip.rowView, circuit_norm]

set_option maxHeartbeats 4000000 in
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
    constructor <;> simp [input, JalrChip.circuit, JalrChip.rowView, circuit_norm]

set_option maxHeartbeats 8000000 in
theorem BranchChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (BranchChip.circuit (p := p)) BranchChip.rowView := by
  unfold CircuitCPUStateTimeContract
  dsimp only
  let input : Var BranchChip.Inputs (ZMod p) := varFromOffset BranchChip.Inputs 0
  let offset := size BranchChip.Inputs
  refine ⟨offset + 28,
    ⟨input.state,
      #v[var { index := offset + 15 }, var { index := offset + 16 },
        var { index := offset + 17 }], 8, input.is_real⟩, ?_, ?_⟩
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
    right
    left
    rfl
  · intro env
    constructor <;> simp [input, BranchChip.circuit, BranchChip.rowView, circuit_norm]

set_option maxHeartbeats 2000000 in
theorem LoadByteChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (LoadByteChip.circuit (p := p))
      LoadByteChip.rowView := by
  unfold CircuitCPUStateTimeContract
  dsimp only
  let input : Var LoadByteChip.Inputs (ZMod p) := varFromOffset LoadByteChip.Inputs 0
  let offset := size LoadByteChip.Inputs
  refine ⟨offset,
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8,
      input.is_lb + input.is_lbu⟩, ?_, ?_⟩
  · simp [input, offset, LoadByteChip.circuit, LoadByteChip.main, circuit_norm]
  · intro env
    constructor <;>
      simp [input, LoadByteChip.rowView, LoadByteChip.isReal, circuit_norm]

set_option maxHeartbeats 2000000 in
theorem LoadHalfChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (LoadHalfChip.circuit (p := p))
      LoadHalfChip.rowView := by
  unfold CircuitCPUStateTimeContract
  dsimp only
  let input : Var LoadHalfChip.Inputs (ZMod p) := varFromOffset LoadHalfChip.Inputs 0
  let offset := size LoadHalfChip.Inputs
  refine ⟨offset,
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8,
      input.is_lh + input.is_lhu⟩, ?_, ?_⟩
  · simp [input, offset, LoadHalfChip.circuit, LoadHalfChip.main, circuit_norm]
  · intro env
    constructor <;>
      simp [input, LoadHalfChip.rowView, LoadHalfChip.isReal, circuit_norm]

set_option maxHeartbeats 2000000 in
theorem LoadWordChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (LoadWordChip.circuit (p := p))
      LoadWordChip.rowView := by
  unfold CircuitCPUStateTimeContract
  dsimp only
  let input : Var LoadWordChip.Inputs (ZMod p) := varFromOffset LoadWordChip.Inputs 0
  let offset := size LoadWordChip.Inputs
  refine ⟨offset,
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8,
      input.is_lw + input.is_lwu⟩, ?_, ?_⟩
  · simp [input, offset, LoadWordChip.circuit, LoadWordChip.main, circuit_norm]
  · intro env
    constructor <;>
      simp [input, LoadWordChip.rowView, LoadWordChip.isReal, circuit_norm]

set_option maxHeartbeats 4000000 in
theorem LoadX0Chip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (LoadX0Chip.circuit (p := p)) LoadX0Chip.rowView := by
  unfold CircuitCPUStateTimeContract
  dsimp only
  let input : Var LoadX0Chip.Inputs (ZMod p) := varFromOffset LoadX0Chip.Inputs 0
  let offset := size LoadX0Chip.Inputs
  refine ⟨offset,
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8,
      input.is_lb + input.is_lbu + input.is_lh + input.is_lhu + input.is_lw + input.is_lwu +
        input.is_ld⟩, ?_, ?_⟩
  · simp [input, offset, LoadX0Chip.circuit, LoadX0Chip.main, circuit_norm]
  · intro env
    constructor <;>
      simp [input, LoadX0Chip.rowView, LoadX0Chip.isReal, circuit_norm]

set_option maxHeartbeats 2000000 in
theorem LoadDoubleChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (LoadDoubleChip.circuit (p := p))
      LoadDoubleChip.rowView := by
  firstStraightCPUTimeContract LoadDoubleChip.Inputs, LoadDoubleChip.circuit,
    LoadDoubleChip.main, LoadDoubleChip.rowView

set_option maxHeartbeats 2000000 in
theorem StoreByteChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (StoreByteChip.circuit (p := p))
      StoreByteChip.rowView := by
  firstStraightCPUTimeContract StoreByteChip.Inputs, StoreByteChip.circuit, StoreByteChip.main,
    StoreByteChip.rowView

set_option maxHeartbeats 2000000 in
theorem StoreHalfChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (StoreHalfChip.circuit (p := p))
      StoreHalfChip.rowView := by
  firstStraightCPUTimeContract StoreHalfChip.Inputs, StoreHalfChip.circuit, StoreHalfChip.main,
    StoreHalfChip.rowView

set_option maxHeartbeats 2000000 in
theorem StoreWordChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (StoreWordChip.circuit (p := p))
      StoreWordChip.rowView := by
  firstStraightCPUTimeContract StoreWordChip.Inputs, StoreWordChip.circuit, StoreWordChip.main,
    StoreWordChip.rowView

set_option maxHeartbeats 2000000 in
theorem StoreDoubleChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (StoreDoubleChip.circuit (p := p))
      StoreDoubleChip.rowView := by
  firstStraightCPUTimeContract StoreDoubleChip.Inputs, StoreDoubleChip.circuit,
    StoreDoubleChip.main, StoreDoubleChip.rowView

set_option maxHeartbeats 4000000 in
theorem MulChip.cpuStateTimeContract :
    CircuitCPUStateTimeContract (p := p) (MulChip.circuit (p := p)) MulChip.rowView := by
  firstStraightCPUTimeContract MulChip.Inputs, MulChip.circuit, MulChip.main, MulChip.rowView

set_option maxHeartbeats 4000000 in
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
  · intro env
    constructor <;>
      simp [input, DivRemChip.circuit, DivRemChip.rowView, circuit_norm]

set_option maxHeartbeats 2000000 in
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

set_option maxHeartbeats 8000000 in
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

/-- Physical constraints plus four-bus balance now construct an exhaustive, clock-ordered trail of
all active decoded instruction rows.  Selector booleanity and strict progress are both derived AIR
facts; neither remains a capstone premise. -/
theorem witness_realDecodedState_exhaustiveTrail
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    RankedGrounding.ExhaustiveTrail
      (↑(realDecodedInstructionRows witness.data witness.tables) :
        Multiset (DecodedInstructionRow p))
      (decodedStateEdge witness.data)
      (initialBoundaryStateMessage witness.publicInput)
      (finalBoundaryStateMessage witness.publicInput) :=
  realDecodedState_exhaustiveTrail_of_constraints witness constraints balanced
    (witness_realDecodedInstructionRows_time_increases witness constraints balanced)

end SP1Clean.Soundness
