import Clean.Air.FlatComponent
import ToClean.Circuit.SubcircuitProjection
import SP1Clean.Native.Chips.SyscallInstrsChip.Defs
import Clean.Utils.Tactics

/-! # `SyscallInstrs` soundness and completeness

The chip boundary for SP1's ECALL table. `Assumptions` is `True`: every fact the `Spec` reports is
either asserted by the row or received as a pulled guarantee.

The `Spec`'s halt conjunct is where the interesting content sits. `ExitCodeValid` is a disjunction
because SP1's bound is one: the `U16CompareOperation` decides whether `a0`'s limb 1 is strictly
below `0x7F00`, and when it is not, the two conditionals force limb 1 to *equal* the bound and
limb 0 to vanish. Both branches keep the word's reduction under KoalaBear's modulus, which is what
makes the committed exit code decode back to `a0`. -/

namespace SP1Clean.SyscallInstrsChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel exitChannel
  syscallChannel publicValuesChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
/-- A gated constraint holds when the gate is boolean and the gated fact holds on a live gate. -/
private lemma gate_zero {x y : ZMod p}
    (hx : x = 0 ∨ x = 1) (h : x = 1 → y = 0) : x * y = 0 := by
  rcases hx with h0 | h1
  · rw [h0]; ring
  · rw [h1, one_mul]; exact h h1

omit [Fact (2 ^ 17 < p)] in
/-- The mirror shape: a constraint gated on `is_real - 1`, which vanishes on a live row. -/
private lemma pad_zero {x y : ZMod p}
    (hx : x = 0 ∨ x = 1) (h : x = 0 → y = 0) : (x - 1) * y = 0 := by
  rcases hx with h0 | h1
  · rw [h0, h h0]; ring
  · rw [h1]; ring

theorem soundness :
    GeneralFormalCircuit.Soundness (Output := unit) (ZMod p) main
      (fun _ _ => True) (fun input _ _ => Spec input) := by
  circuit_proof_start
  simp only [circuit_norm, memoryChannel, programChannel,
    Channels.MemoryMsg.isU64, Channels.MemoryMsg.ClkBound, Channels.ProgramMsg.RowSpec]
    at h_holds ⊢
  obtain ⟨h_gate, h_cbool, h_dbool, h_hbool, h_tbool, h_u16, h_izh, h_ize, h_izl, h_izc, h_izd,
    h_hdef, h_padt, h_padh, h_padd,
    h_cpu, h_raca, h_racb, h_racc, h_prog, h_ma, h_mb, h_mc,
    h_write, h_pc, h_disp, h_fbb, h_fbc, h_commit, h_ba0, h_ba1, h_ba2, h_ba3, -⟩ :=
    h_holds
  have h_rbin := bool_of_mul_pred h_gate
  have h_cbin := bool_of_mul_pred h_cbool
  have h_dbin := bool_of_mul_pred h_dbool
  have h_hbin := bool_of_mul_pred h_hbool
  have eoa0 : Expression.eval env input_var_op_a_memory_prev_value[0]
      = input_op_a_memory_prev_value[0] := by
    have := congrArg (fun v => v[0]'(by norm_num)) h_input.2.2.1.1; simpa using this
  have esb0 : Expression.eval env input_var_syscall_id_bytes_low_bytes[0]
      = input_syscall_id_bytes_low_bytes[0] := by
    have := congrArg (fun v => v[0]'(by norm_num)) h_input.2.2.2.2.2.2.2.2.2.2.2.1
    simpa using this
  -- The arm sees the row's own expression; `GatesBoolean` states it over the decoded fields.
  have h_tbinE := bool_of_mul_pred h_tbool
  rw [eoa0, esb0] at h_tbool
  have h_tbin := bool_of_mul_pred h_tbool
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec (h_cpu h_rbin)
  have eav : ∀ i (hi : i < 4),
      Expression.eval env input_var_op_a_value[i] = input_op_a_value[i] := by
    intro i hi
    have := congrArg (fun v => v[i]'hi) h_input.2.2.2.2.2.2.2.2.2.2.1
    simpa using this
  have avU64 : (-input_is_real : ZMod p) = -1 → Word.isU64 input_op_a_value := by
    intro hneg
    have hp : (2 : ℕ) ^ 17 < p := Fact.out
    refine Word.isU64_of_cases ?_ ?_ ?_ ?_
    · have := h_ba0 hneg; rw [eav 0 (by norm_num)] at this
      exact (byteRowSpec_range (n := 16) _ (by omega)).mp this
    · have := h_ba1 hneg; rw [eav 1 (by norm_num)] at this
      exact (byteRowSpec_range (n := 16) _ (by omega)).mp this
    · have := h_ba2 hneg; rw [eav 2 (by norm_num)] at this
      exact (byteRowSpec_range (n := 16) _ (by omega)).mp this
    · have := h_ba3 hneg; rw [eav 3 (by norm_num)] at this
      exact (byteRowSpec_range (n := 16) _ (by omega)).mp this
  have hrealHalt : input_is_halt = 1 → (-input_is_real : ZMod p) = -1 := by
    intro hh
    rw [hh, mul_one] at h_padh
    have hr : input_is_real = 1 := by linear_combination h_padh
    rw [hr]
  have hrealDef : input_is_commit_deferred_result = 1 → (-input_is_real : ZMod p) = -1 := by
    intro hd
    rw [hd, mul_one] at h_padd
    have hr : input_is_real = 1 := by linear_combination h_padd
    rw [hr]
  -- Two selectors cannot both fire: one identifier cannot equal two distinct codes.
  have distinct : ∀ c d : ℕ, c < 2 ^ 17 → d < 2 ^ 17 → c ≠ d →
      Expression.eval env input_var_syscall_id_bytes_low_bytes[0] - ((c : ℕ) : ZMod p) = 0 →
      Expression.eval env input_var_syscall_id_bytes_low_bytes[0] - ((d : ℕ) : ZMod p) = 0 →
      False := by
    intro c d hc hd hne h1 h2
    have hp : (2 : ℕ) ^ 17 < p := Fact.out
    have hcd : ((c : ℕ) : ZMod p) = ((d : ℕ) : ZMod p) := by linear_combination h2 - h1
    have := congrArg ZMod.val hcd
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at this
    exact hne this
  -- Each selector is the indicator of its code, so it is boolean and at most one fires.
  have indicator : ∀ (res : ZMod p) (c : ℕ),
      res = (if Expression.eval env input_var_syscall_id_bytes_low_bytes[0]
              - ((c : ℕ) : ZMod p) = 0 then 1 else 0) →
      (res = 0 ∨ res = 1) := by
    intro res c h
    by_cases hz : Expression.eval env input_var_syscall_id_bytes_low_bytes[0]
        - ((c : ℕ) : ZMod p) = 0
    · exact Or.inr (by rw [h, if_pos hz])
    · exact Or.inl (by rw [h, if_neg hz])
  have pairSum : ∀ (r1 r2 : ZMod p) (c d : ℕ), c < 2 ^ 17 → d < 2 ^ 17 → c ≠ d →
      r1 = (if Expression.eval env input_var_syscall_id_bytes_low_bytes[0]
              - ((c : ℕ) : ZMod p) = 0 then 1 else 0) →
      r2 = (if Expression.eval env input_var_syscall_id_bytes_low_bytes[0]
              - ((d : ℕ) : ZMod p) = 0 then 1 else 0) →
      (r1 + r2 = 0 ∨ r1 + r2 = 1) := by
    intro r1 r2 c d hc hd hne h1 h2
    by_cases hz1 : Expression.eval env input_var_syscall_id_bytes_low_bytes[0]
        - ((c : ℕ) : ZMod p) = 0
    · by_cases hz2 : Expression.eval env input_var_syscall_id_bytes_low_bytes[0]
          - ((d : ℕ) : ZMod p) = 0
      · exact absurd (distinct c d hc hd hne hz1 hz2) not_false
      · exact Or.inr (by rw [h1, h2, if_pos hz1, if_neg hz2]; ring)
    · by_cases hz2 : Expression.eval env input_var_syscall_id_bytes_low_bytes[0]
          - ((d : ℕ) : ZMod p) = 0
      · exact Or.inr (by rw [h1, h2, if_neg hz1, if_pos hz2]; ring)
      · exact Or.inl (by rw [h1, h2, if_neg hz1, if_neg hz2]; ring)
  have h_ebin : input_is_real = 1 →
      (input_is_enter_unconstrained_result = 0 ∨ input_is_enter_unconstrained_result = 1) :=
    fun hr => indicator _ enterUnconstrainedCode ((h_ize h_rbin) hr).1
  have h_ehsum : input_is_real = 1 →
      (input_is_enter_unconstrained_result + input_is_hint_len_result = 0 ∨
        input_is_enter_unconstrained_result + input_is_hint_len_result = 1) :=
    fun hr => pairSum _ _ enterUnconstrainedCode hintLenCode (by norm_num [enterUnconstrainedCode])
      (by norm_num [hintLenCode]) (by norm_num [enterUnconstrainedCode, hintLenCode])
      ((h_ize h_rbin) hr).1 ((h_izl h_rbin) hr).1
  have h_sum : input_is_real = 1 →
      (input_is_commit_result + input_is_commit_deferred_result = 0 ∨
        input_is_commit_result + input_is_commit_deferred_result = 1) :=
    fun hr => pairSum _ _ commitCode commitDeferredCode (by norm_num [commitCode])
      (by norm_num [commitDeferredCode]) (by norm_num [commitCode, commitDeferredCode])
      ((h_izc h_rbin) hr).1 ((h_izd h_rbin) hr).1
  refine ⟨⟨⟨h_rbin, h_cbin, h_dbin, h_hbin, h_tbin⟩, h_cpu h_rbin, h_raca h_rbin,
    h_racb h_rbin, h_racc h_rbin, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro ha0
    exact h_write ⟨h_rbin, ha0, h_ebin, h_ehsum⟩
  · exact h_pc ⟨h_rbin, h_hbin⟩
  · have hd := h_disp h_tbinE
    simp only [eoa0, esb0] at hd
    exact hd
  · exact h_fbb ⟨h_hbin, fun hh => (h_mb (hrealHalt hh)).1 1⟩
  · exact h_fbc ⟨h_dbin, fun hd => (h_mc (hrealDef hd)).1 1⟩
  · exact h_commit ⟨h_rbin, h_cbin, h_dbin, h_sum⟩
  · -- `SelectorsValid`: the byte split, the five indicators with their inverse witnesses, the
    -- `is_halt = is_halt_zero · is_real` definition, and the padding-row zeros. All of it was
    -- already in scope and discarded before this conjunct joined `Spec`.
    have bridge : ∀ c : ℕ,
        (input_syscall_id_bytes_low_bytes[0] = ((c : ℕ) : ZMod p)) ↔
          (Expression.eval env input_var_syscall_id_bytes_low_bytes[0] - ((c : ℕ) : ZMod p) = 0) := by
      intro c
      rw [esb0, sub_eq_zero]
    refine ⟨h_u16 h_rbin, fun hr => ⟨?_, ?_, ?_, ?_, ?_⟩, fun hr => ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [(h_izh h_rbin hr).1]; exact if_congr (bridge haltCode).symm rfl rfl
    · rw [(h_ize h_rbin hr).1]
      exact if_congr (bridge enterUnconstrainedCode).symm rfl rfl
    · rw [(h_izl h_rbin hr).1]; exact if_congr (bridge hintLenCode).symm rfl rfl
    · rw [(h_izc h_rbin hr).1]; exact if_congr (bridge commitCode).symm rfl rfl
    · rw [(h_izd h_rbin hr).1]
      exact if_congr (bridge commitDeferredCode).symm rfl rfl
    · intro hne
      have h := (h_izh h_rbin hr).2 (by rw [esb0]; exact hne)
      rw [esb0] at h
      exact h
    · intro hne
      have h := (h_ize h_rbin hr).2 (by rw [esb0]; exact hne)
      rw [esb0] at h
      exact h
    · intro hne
      have h := (h_izl h_rbin hr).2 (by rw [esb0]; exact hne)
      rw [esb0] at h
      exact h
    · intro hne
      have h := (h_izc h_rbin hr).2 (by rw [esb0]; exact hne)
      rw [esb0] at h
      exact h
    · intro hne
      have h := (h_izd h_rbin hr).2 (by rw [esb0]; exact hne)
      rw [esb0] at h
      exact h
    · linear_combination h_hdef
    · intro h0
      have h0' : input_is_real = 0 := h0
      rw [eoa0, esb0, h0'] at h_padt
      rw [h0'] at h_padh h_padd
      refine ⟨?_, ?_, ?_⟩
      · show (input_op_a_memory_prev_value[0] - input_syscall_id_bytes_low_bytes[0])
          * (256 : ZMod p)⁻¹ = 0
        linear_combination -h_padt
      · show input_is_halt = 0
        linear_combination -h_padh
      · show input_is_commit_deferred_result = 0
        linear_combination -h_padd
  · and_intros <;>
      first
        | exact Or.inl rfl
        | exact Or.inr h_rbin
        | exact fun _ _ => trivial
        | exact fun h1 h0 => off_gate_vacuous h_rbin h1 h0
        | exact fun h1 h0 => off_gate_vacuous h_cbin h1 h0
        | (intro _ h0
           have hr : input_is_real = 1 := h_rbin.resolve_left h0
           have hneg : (-input_is_real : ZMod p) = -1 := by rw [hr]
           refine ⟨?_, ?_⟩
           · first
               | exact (h_ma hneg).1
               | exact (h_mb hneg).1
               | exact (h_mc hneg).1
               | exact avU64 hneg
           · first
               | exact h_clk.at_four hr
               | exact h_clk.at_three hr
               | exact h_clk.at_two hr)

theorem completeness :
    GeneralFormalCircuit.Completeness (Output := unit) (ZMod p) main
      (fun input _ _ => RowContract input) (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨h_gates, h_cpu, h_raca, h_racb, h_racc, h_sel,
    h_wA, h_wS, h_pA, h_pS, h_dA, h_dS, h_bA, h_bS, h_cA, h_cS, h_mA, h_mS,
    h_pull, h_bytes⟩ := h_assumptions
  obtain ⟨h_rbin, h_cbin, h_dbin, h_hbin, h_tbin⟩ := h_gates
  obtain ⟨h_split, h_res, h_inv, h_halteq, h_pad⟩ := h_sel
  have eoa : ∀ i (hi : i < 4),
      Expression.eval env.toEnvironment input_var_op_a_memory_prev_value[i]
        = input_op_a_memory_prev_value[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.2.1.1; simpa using this
  have esb : ∀ i (hi : i < 4),
      Expression.eval env.toEnvironment input_var_syscall_id_bytes_low_bytes[i]
        = input_syscall_id_bytes_low_bytes[i] := by
    intro i hi
    have := congrArg (fun v => v[i]'hi) h_input.2.2.2.2.2.2.2.2.2.2.2.1; simpa using this
  have eav : ∀ i (hi : i < 4),
      Expression.eval env.toEnvironment input_var_op_a_value[i] = input_op_a_value[i] := by
    intro i hi
    have := congrArg (fun v => v[i]'hi) h_input.2.2.2.2.2.2.2.2.2.2.1; simpa using this
  have eob : ∀ i (hi : i < 4),
      Expression.eval env.toEnvironment input_var_op_b_memory_prev_value[i]
        = input_op_b_memory_prev_value[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.2.2.2.2.1.1; simpa using this
  have eoc : ∀ i (hi : i < 4),
      Expression.eval env.toEnvironment input_var_op_c_memory_prev_value[i]
        = input_op_c_memory_prev_value[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.2.2.2.2.2.2.1.1; simpa using this
  have edw : ∀ i (hi : i < 4),
      Expression.eval env.toEnvironment input_var_digest_word[i] = input_digest_word[i] := by
    intro i hi
    have := congrArg (fun v => v[i]'hi) h_input.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    simpa using this
  have epc : ∀ i (hi : i < 3),
      Expression.eval env.toEnvironment input_var_state_pc[i] = input_state_pc[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.1.2.2.2; simpa using this
  simp only [epc, eoa, esb, eav, eoc, edw]
  and_intros
  all_goals try (first
    | exact h_rbin
    | exact h_split
    | exact h_cpu
    | exact h_raca
    | exact h_racb
    | exact h_racc
    | linear_combination h_halteq
    | exact gate_zero h_rbin (fun h => by rw [h]; ring)
    | exact gate_zero h_cbin (fun h => by rw [h]; ring)
    | exact gate_zero h_dbin (fun h => by rw [h]; ring)
    | exact gate_zero h_hbin (fun h => by rw [h]; ring)
    | exact gate_zero h_tbin (fun h => by rw [h]; ring))
  all_goals try (first
    | exact pad_zero h_rbin (fun h => (h_pad h).1)
    | exact pad_zero h_rbin (fun h => (h_pad h).2.1)
    | exact pad_zero h_rbin (fun h => (h_pad h).2.2)
    | exact h_wA.1 | exact h_wA.2.1 | exact h_wA.2.2.1 | exact h_wA.2.2.2
    | exact h_wS.1 | exact h_wS.2.1 | exact h_wS.2.2.1 | exact h_wS.2.2.2
    | exact h_pA.1 | exact h_pA.2 | exact h_pS.1 | exact h_pS.2
    | exact h_dA | exact h_dS)
  all_goals try (first
    | exact h_bA.1 | exact h_bA.2 | exact h_bS.1 | exact h_bS.2
    | exact h_cA.1 | exact h_cA.2 | exact h_cS.1 | exact h_cS.2
    | exact h_mA.1 | exact h_mA.2.1 | exact h_mA.2.2.1 | exact h_mA.2.2.2
    | exact h_mS.1 | exact h_mS.2.1 | exact h_mS.2.2.1 | exact h_mS.2.2.2.1
    | exact h_mS.2.2.2.2.1 | exact h_mS.2.2.2.2.2)
  all_goals try (first
    | (intro hr
       exact ⟨by rw [(h_res hr).1]; simp [syscallId, sub_eq_zero]; rfl, (h_inv hr).1⟩)
    | (intro hr
       exact ⟨by rw [(h_res hr).2.1]; simp [syscallId, sub_eq_zero]; rfl, (h_inv hr).2.1⟩)
    | (intro hr
       exact ⟨by rw [(h_res hr).2.2.1]; simp [syscallId, sub_eq_zero]; rfl, (h_inv hr).2.2.1⟩)
    | (intro hr
       exact ⟨by rw [(h_res hr).2.2.2.1]; simp [syscallId, sub_eq_zero]; rfl, (h_inv hr).2.2.2.1⟩)
    | (intro hr
       exact ⟨by rw [(h_res hr).2.2.2.2]; simp [syscallId, sub_eq_zero]; rfl, (h_inv hr).2.2.2.2⟩)
    | exact h_dA
    | exact h_dS)
  all_goals try (first
    | (intro hneg
       have hr : input_is_real = 1 := neg_inj.mp hneg
       exact ⟨(h_pull hr).1, (h_pull hr).2.1, (h_pull hr).2.2.1, (h_pull hr).2.2.2.1,
         (h_pull hr).2.2.2.2.1⟩)
    | (intro hneg
       have hr : input_is_real = 1 := neg_inj.mp hneg
       exact ⟨(h_pull hr).2.2.2.2.2.1, (h_pull hr).2.2.2.2.2.2.1⟩)
    | (intro hneg
       have hr : input_is_real = 1 := neg_inj.mp hneg
       exact ⟨(h_pull hr).2.2.2.2.2.2.2.1, (h_pull hr).2.2.2.2.2.2.2.2.1⟩)
    | (intro hneg
       have hr : input_is_real = 1 := neg_inj.mp hneg
       exact ⟨(h_pull hr).2.2.2.2.2.2.2.2.2.1, (h_pull hr).2.2.2.2.2.2.2.2.2.2.1⟩)
    | exact fun _ => trivial)
  all_goals try (first
    | (intro hneg
       exact (byteRowSpec_u8range_pair _ _).mpr
         ⟨h_bytes (neg_inj.mp hneg) 0, h_bytes (neg_inj.mp hneg) 1⟩)
    | (intro hneg
       exact (byteRowSpec_u8range_pair _ _).mpr
         ⟨h_bytes (neg_inj.mp hneg) 2, h_bytes (neg_inj.mp hneg) 3⟩))
  all_goals (intro hneg
             have hr : input_is_real = 1 := neg_inj.mp hneg
             have h16 : (16 : ℕ) < p := by
               have : (2 : ℕ) ^ 17 < p := Fact.out
               omega
             have hu : Word.isU64 input_op_a_value :=
               (h_pull hr).2.2.2.2.2.2.2.2.2.2.2
             first
               | simpa [byteChannel] using (byteRowSpec_range (n := 16) _ h16).mpr (hu 0)
               | simpa [byteChannel] using (byteRowSpec_range (n := 16) _ h16).mpr (hu 1)
               | simpa [byteChannel] using (byteRowSpec_range (n := 16) _ h16).mpr (hu 2)
               | simpa [byteChannel] using (byteRowSpec_range (n := 16) _ h16).mpr (hu 3))


/-! ## The bundled `circuit`

The three obligations below are **structural**, not semantic: they ask which channels the row's
operations touch, not what those operations mean. Answering them with `circuit_norm` normalises
the whole composed block and exceeds the elaboration budget; the monadic-append and per-leaf
`rfl`-lemmas answer them in seconds. `DivRemChip` uses the same shape. -/

/-- The row's own structural simp set: unfold the monad and the leaves, and read each composed
circuit's declared channels off its `rfl`-lemma rather than its definition. -/
private lemma subcircuitRequirements_eq (input : Var Inputs (ZMod p)) (i₀ : ℕ) :
    Operations.subcircuitChannelsWithRequirements ((main input).operations i₀) = [] := by
  simp only [main, Circuit.operations, Circuit.bind_def, assertZero, subcircuitWithAssertion,
    assertion, Channel.pullIf, Channel.pushIf,
    Operations.subcircuitChannelsWithRequirements_append,
    Operations.subcircuitChannelsWithRequirements_assert,
    Operations.subcircuitChannelsWithRequirements_interact,
    Operations.subcircuitChannelsWithRequirements_subcircuit,
    Operations.subcircuitChannelsWithRequirements_nil, List.append_nil,
    FormalAssertion.toSubcircuit_channelsWithRequirements,
    GeneralFormalCircuit.toSubcircuit_channelsWithRequirements,
    U16toU8OperationSafe.circuit, IsZeroOperation.circuit,
    Readers.CPUState.circuit, Readers.RegisterAccessCols.circuit,
    PcArm.circuit_channelsWithRequirements, CommitArm.circuit_channelsWithRequirements,
    WriteArm.circuit_channelsWithRequirements, FieldBoundArm.circuit_channelsWithRequirements,
    DispatchArm.circuit_channelsWithRequirements]


/-- The row's requirement-channel law. Structural throughout: `circuit_norm` would normalise the
composed block's *meaning* to answer a question about its metadata, and exceeds the elaboration
budget doing so; the monadic-append and per-leaf `rfl`-lemmas answer it directly. `DivRemChip`
uses the same shape. -/
private theorem requirementsLawful (input_var : Var Inputs (ZMod p)) (i₀ : ℕ) :
    Operations.RequirementsChannelsLawful ((main input_var).operations i₀)
      (elaborated.channelsWithGuarantees) [memoryChannel.toRaw] := by
  dsimp only [Operations.RequirementsChannelsLawful]
  refine ⟨by rw [subcircuitRequirements_eq]; exact List.nil_subset _, ?_, ?_⟩
  · intro channel h_channel
    simp only [main, Circuit.operations, Circuit.bind_def, assertZero, subcircuitWithAssertion,
      assertion, Channel.pullIf, Channel.pushIf,
      Operations.shallowChannels_append, Operations.shallowChannels_nil,
      Operations.shallowChannels_subcircuit, Operations.shallowChannels_assert,
      Operations.shallowChannels_interact, List.nil_append,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h_channel
    rcases h_channel with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact Or.inl (by simp only [circuit_norm])
  · intro env h_constraints
    simp only [main, Circuit.operations, Circuit.bind_def, assertZero, subcircuitWithAssertion,
      assertion, Channel.pullIf, Channel.pushIf,
      constraintsHold_shallow_iff_forall_mem] at h_constraints
    have hb0 := h_constraints.1 _ List.mem_cons_self
    have hb1 := h_constraints.1 _ (List.mem_cons_of_mem _ List.mem_cons_self)
    simp only [Expression.eval, eval_sub] at hb0 hb1
    have h_bool := bool_of_mul_pred hb0
    have h_cbool := bool_of_mul_pred hb1
    rw [Operations.inChannelsOrRequirements_iff_forall_mem]
    intro interaction h_interaction
    simp only [main, Circuit.operations, Circuit.bind_def, assertZero, subcircuitWithAssertion,
      assertion, Channel.pullIf, Channel.pushIf,
      Operations.shallowInteractions_append, Operations.shallowInteractions_nil,
      Operations.shallowInteractions_subcircuit, Operations.shallowInteractions_assert,
      Operations.shallowInteractions_interact, List.nil_append,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h_interaction
    rcases h_interaction with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
        | exact Or.inl List.mem_cons_self
        | (right
           rw [ChannelInteraction.toRaw_requirements]
           intro h1 h0
           simp only [Expression.eval, neg_one_mul] at h1 h0
           first
             | exact off_gate_vacuous_neg h_bool h1 h0
             | exact off_gate_vacuous_neg h_cbool h1 h0
             | trivial)

/-- The `SyscallInstrs` row as a bundled circuit — SP1's ECALL table, all thirteen inline arms.

`ProverAssumptions` is the row contract; `Spec` is the row's meaning. `memoryChannel` is the one bus
whose guarantee the row *requires* rather than supplies: the three register accesses pull a prior
value the memory argument owns. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs unit where
  name := "sp1.native.syscall_instrs"
  main
  elaborated
  Assumptions := fun _ _ => True
  Spec := fun input _ _ => Spec input
  ProverAssumptions := fun input _ _ => RowContract input
  ProverSpec := fun _ _ _ => True
  soundness := soundness
  completeness := completeness
  channelsWithRequirements := [memoryChannel.toRaw]
  requirementsChannelsLawful := requirementsLawful

set_option linter.unusedSectionVars false in
/-- The bundled `Spec` field, applied — the shape the ensemble's `weakSoundness` extraction needs. -/
@[circuit_norm] lemma circuit_Spec_apply (input : Inputs (ZMod p)) (out : unit (ZMod p))
    (data : ProverData (ZMod p)) :
    (circuit (p := p)).Spec input out data = Spec input := rfl

set_option linter.unusedSectionVars false in
/-- The bundled `Assumptions` field, applied. -/
@[circuit_norm] lemma circuit_Assumptions_apply (input : Inputs (ZMod p))
    (data : ProverData (ZMod p)) :
    (circuit (p := p)).Assumptions input data = True := rfl

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    (circuit (p := p)).localLength x = 0 := rfl


@[circuit_norm] theorem circuit_main_eq :
    (SyscallInstrsChip.circuit (p := p)).main = SyscallInstrsChip.main := rfl

private theorem u16toU8SafeLookups (input : Var SP1Clean.U16toU8OperationSafe.Inputs (ZMod p))
    (n : ℕ) :
    Operations.lookups ((SP1Clean.U16toU8OperationSafe.circuit.main input).operations n) = [] := rfl

omit [Fact (2 ^ 17 < p)] in
private theorem isZeroLookups (input : Var SP1Clean.IsZeroOperation.Inputs (ZMod p)) (n : ℕ) :
    Operations.lookups ((SP1Clean.IsZeroOperation.circuit.main input).operations n) = [] := by
  simp only [SP1Clean.IsZeroOperation.circuit, SP1Clean.IsZeroOperation.main, circuit_norm,
    Gadgets.Equality.main]

private theorem cpuStateLookups (input : Var Readers.CPUState.Inputs (ZMod p)) (n : ℕ) :
    Operations.lookups ((Readers.CPUState.circuit.main input).operations n) = [] := rfl

private theorem registerAccessColsLookups (input : Var Readers.RegisterAccessCols.Inputs (ZMod p))
    (n : ℕ) :
    Operations.lookups ((Readers.RegisterAccessCols.circuit.main input).operations n) = [] := by
  simp only [Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main, circuit_norm,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main]

omit [Fact (2 ^ 17 < p)] in
private theorem pcArmLookups (input : Var SyscallInstrsChip.PcArm.Inputs (ZMod p)) (n : ℕ) :
    Operations.lookups ((SyscallInstrsChip.PcArm.circuit.main input).operations n) = [] := rfl

omit [Fact (2 ^ 17 < p)] in
private theorem commitArmLookups (input : Var SyscallInstrsChip.CommitArm.Inputs (ZMod p))
    (n : ℕ) :
    Operations.lookups ((SyscallInstrsChip.CommitArm.circuit.main input).operations n) = [] := rfl

omit [Fact (2 ^ 17 < p)] in
private theorem writeArmLookups (input : Var SyscallInstrsChip.WriteArm.Inputs (ZMod p)) (n : ℕ) :
    Operations.lookups ((SyscallInstrsChip.WriteArm.circuit.main input).operations n) = [] := rfl

private theorem fieldBoundArmLookups (input : Var SyscallInstrsChip.FieldBoundArm.Inputs (ZMod p))
    (n : ℕ) :
    Operations.lookups ((SyscallInstrsChip.FieldBoundArm.circuit.main input).operations n) = [] := by
  simp only [SyscallInstrsChip.FieldBoundArm.circuit, SyscallInstrsChip.FieldBoundArm.main,
    circuit_norm, Gadgets.Equality.main, SP1Clean.U16CompareOperation.circuit,
    SP1Clean.U16CompareOperation.main]

omit [Fact (2 ^ 17 < p)] in
private theorem dispatchArmLookups (input : Var SyscallInstrsChip.DispatchArm.Inputs (ZMod p))
    (n : ℕ) :
    Operations.lookups ((SyscallInstrsChip.DispatchArm.circuit.main input).operations n) = [] := rfl

/-- The row contains no Clean lookup operations; cross-table checks use channels. -/
theorem lookups_empty :
    ({ circuit := SyscallInstrsChip.circuit (p := p) } :
      Air.Flat.Component (ZMod p)).operations.lookups = [] := by
  rw [Air.Flat.Component.lookups_eq, Air.Flat.Component.rowOperations_mk,
    SyscallInstrsChip.circuit_main_eq]
  simp only [SyscallInstrsChip.main, Circuit.operations, Circuit.bind_def, assertZero,
    subcircuitWithAssertion, assertion, Channel.pullIf, Channel.pushIf,
    Operations.lookups_append, Operations.lookups_assert, Operations.lookups_interact,
    Operations.lookups_nil, Operations.lookups_subcircuit,
    FormalAssertion.toSubcircuit_lookups, GeneralFormalCircuit.toSubcircuit_lookups,
    FormalAssertion.toSubcircuit_localLength, GeneralFormalCircuit.toSubcircuit_localLength,
    Readers.CPUState.circuit_localLength, Readers.RegisterAccessCols.circuit_localLength,
    SP1Clean.IsZeroOperation.circuit_localLength,
    SyscallInstrsChip.PcArm.circuit_localLength,
    SyscallInstrsChip.WriteArm.circuit_localLength,
    SyscallInstrsChip.FieldBoundArm.circuit_localLength,
    SyscallInstrsChip.DispatchArm.circuit_localLength,
    SP1Clean.U16toU8OperationSafe.circuit_localLength,
    u16toU8SafeLookups, isZeroLookups, cpuStateLookups, registerAccessColsLookups, pcArmLookups, commitArmLookups, writeArmLookups, fieldBoundArmLookups, dispatchArmLookups,
    Operations.localLength, Nat.add_zero, List.append_nil]

end SP1Clean.SyscallInstrsChip
