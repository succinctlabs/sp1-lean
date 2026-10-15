import SP1Clean.Native.Chips.HostCallChip.Defs

/-! # Soundness and completeness of the instruction-to-host boundary

The instruction's CPU contract supplies the extra read's clock discipline. Full-word equality
determines its gate, including on padding, so the host can neither omit WRITE's x12 observation
nor create extra register reads for another call.
-/

namespace SP1Clean.HostCallChip

open Circuit Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def ProverAssumptions (input : Inputs (ZMod p)) : Prop :=
  SyscallInstrsChip.RowContract input.instruction ∧
    SyscallCodeGuard.Spec ⟨input.instruction.op_a_memory.prev_value, input.instruction.is_real⟩ ∧
    Readers.RegisterRead.ProverAssumptions
      (input.read (writeFlag input.instruction.op_a_memory.prev_value))

omit [Fact (2 ^ 25 < p)] in
theorem writeFlag_binary (word : Word (ZMod p)) : writeFlag word = 0 ∨ writeFlag word = 1 := by
  unfold writeFlag
  split <;> simp

private theorem read_assumptions (instruction : SyscallInstrsChip.Inputs (ZMod p))
    (length : Circuits.Types.RegisterAccessCols (ZMod p))
    (valid : CoreSyscallChip.Spec instruction) (flag : ZMod p) (binary : flag = 0 ∨ flag = 1) :
    Readers.RegisterRead.Assumptions ((⟨instruction, length⟩ : Inputs (ZMod p)).read flag) := by
  have realBinary : instruction.is_real = 0 ∨ instruction.is_real = 1 := valid.2.1
  refine ⟨?_, ?_⟩
  · rcases realBinary with zero | one
    · exact Or.inl (by simp [Inputs.read, zero])
    · simpa only [Inputs.read, one, one_mul] using binary
  · intro active
    change instruction.is_real * flag = 1 at active
    have real : instruction.is_real = 1 := by
      rcases realBinary with zero | one
      · simp only [zero, zero_mul] at active
        exact False.elim (zero_ne_one active)
      · exact one
    exact (Readers.ClkDiscipline.of_cpuState_spec valid.1.2.1).at_one real

theorem soundness : GeneralFormalCircuit.Soundness (Output := unit) (ZMod p) main
    (fun _ _ => True) (fun input _ _ => Spec input) := by
  circuit_proof_start [CoreSyscallChip.circuit, Gadgets.IsEqual.circuit, Gadgets.IsEqual.Spec,
    Gadgets.IsEqual.Assumptions, Readers.RegisterRead.circuit, channel, writeWord, Inputs.read]
  obtain ⟨core, flag, read⟩ := h_holds
  rw [flag] at read
  have assumptions := read_assumptions _
    ⟨input_length_prev_value,
      ⟨input_length_access_timestamp_prev_low, input_length_access_timestamp_diff_low_limb⟩⟩
    core (writeFlag input_instruction_op_a_memory_prev_value) (writeFlag_binary _)
  simp only [Inputs.read, writeFlag, writeWord, circuit_norm] at assumptions
  rw [flag]
  simpa only [writeFlag, writeWord, circuit_norm] using
    And.intro (And.intro core (read assumptions)) assumptions

theorem completeness : GeneralFormalCircuit.Completeness (Output := unit) (ZMod p) main
    (fun input _ _ => ProverAssumptions input) (fun _ _ _ => True) := by
  circuit_proof_start [CoreSyscallChip.circuit, Gadgets.IsEqual.circuit, Gadgets.IsEqual.Spec,
    Gadgets.IsEqual.Assumptions, Readers.RegisterRead.circuit, channel, writeWord, Inputs.read]
  obtain ⟨_, flag, _⟩ := h_env
  rw [flag]
  simpa only [writeFlag, writeWord, circuit_norm] using
    And.intro (And.intro h_assumptions.1 h_assumptions.2.1) h_assumptions.2.2

def circuit : GeneralFormalCircuit (ZMod p) Inputs unit where
  name := "sp1.native.host_call"
  main
  elaborated
  Spec input _ _ := Spec input
  ProverAssumptions input _ _ := ProverAssumptions input
  soundness
  completeness
  channelsWithRequirements := [memoryChannel.toRaw, channel.toRaw]
  requirementsChannelsLawful := by
    preserve_tactic_target
    intro input offset
    rw [operations_eq]
    refine ⟨?_, ?_, ?_⟩
    · simp only [circuit_norm]
    · simp only [circuit_norm]
    · intro env _
      rw [Operations.inChannelsOrRequirements_iff_forall_mem]
      intro interaction member
      simp only [Operations.shallowInteractions, List.mem_singleton] at member
      subst interaction
      exact Or.inl (by simp only [circuit_norm])

end SP1Clean.HostCallChip
