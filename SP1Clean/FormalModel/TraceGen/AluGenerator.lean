import SP1Clean.FormalModel.TraceGen.GenState

/-!
# Generating an R-type ALU event stream

The fold. Given a shard's ALU steps — each the executor's view of one instruction: which registers,
what they held, what the destination displaced — this produces the `RTypeEvent` list the chips'
trace tables consume, and proves every event `WellFormed`.

The whole content is the timestamp bookkeeping, which is why `GenState.lean` comes first. Everything
else an event carries is read straight off the step: the register indices are `BitVec 5`, so their
`< 32` bounds are free; the values carry their own 64-bit bounds; the clock is the window index.
What no step can supply is *when each register was last touched*, and that is what the fold threads.

**Scope.** This is the R-type family — `ADD`, `SUB`, and the rest of the two-register ALU
instructions — and it is deliberately the whole of it rather than `ADD` alone: the opcode is a
payload column the R-type adapter does not constrain, so restricting to one opcode would restrict
nothing structurally. What *is* restricted is the instruction shape: two register sources, one
register destination, no memory, no branch. Widening past that is per-family work in this same
shape, not a change to the fold.

This module does not read the Sail model. Producing the `AluStep` list *from* an execution is the
remaining half of the generator, and it is where the decode restriction and the register read-through
live.
-/

namespace SP1Clean.TraceGen

open SP1Clean.Semantics

/-- The executor's view of one R-type ALU instruction. Register indices are `BitVec 5`, so the
architectural-index bounds every event owes are structural rather than assumed. -/
structure AluStep where
  /-- The address this instruction was fetched from. -/
  pc : ℕ
  /-- The executor's opcode discriminant. Payload for the multi-opcode chips' variant selection;
  the R-type adapter commits no opcode column. -/
  opcode : ℕ
  /-- `rd`. -/
  a : BitVec 5
  /-- `rs1`. -/
  b : BitVec 5
  /-- `rs2`. -/
  c : BitVec 5
  /-- What `rs1` held. -/
  bVal : ℕ
  /-- What `rs2` held. -/
  cVal : ℕ
  /-- What `rd` held before this instruction overwrote it — the record the offline-memory argument
  is handed back. -/
  prevAVal : ℕ

/-- **What makes a step a real one.** Four value bounds and the `rd ≠ x0` routing condition; the
index bounds are structural. Everything else `RTypeEvent.WellFormed` asks for is the fold's job. -/
structure AluStep.WellFormed (s : AluStep) : Prop where
  /-- The program counter is a 48-bit address. -/
  pc_lt : s.pc < 2 ^ 48
  /-- The destination is not `x0` — those rows are routed to the `AluX0` chip. -/
  a_ne_zero : s.a ≠ 0
  /-- Register contents are 64-bit values. -/
  bVal_lt : s.bVal < 2 ^ 64
  cVal_lt : s.cVal < 2 ^ 64
  prevAVal_lt : s.prevAVal < 2 ^ 64

/-- One step's event, at the clock its window begins and against the timestamps recorded so far. -/
def aluEventOf (g : GenState) (clk : ℕ) (s : AluStep) : RTypeEvent where
  clk := clk
  pc := s.pc
  opcode := s.opcode
  opA := s.a.toNat
  opB := s.b.toNat
  opC := s.c.toNat
  b := s.bVal
  c := s.cVal
  prevA := s.prevAVal
  prevTsA := g.prevTsA clk s.a s.b s.c
  prevTsB := g.prevTsB clk s.b s.c
  prevTsC := g.prevTsC s.c

/-- **The fold.** Each step consumes one `CLK_INC` window and updates the shadow bookkeeping. -/
def aluEvents (g : GenState) (clk : ℕ) : List AluStep → List RTypeEvent
  | [] => []
  | s :: rest =>
      aluEventOf g clk s ::
        aluEvents (g.stepRType clk s.a s.b s.c) (clk + ordinaryClkInc) rest

/-- A `BitVec 5` index is an architectural register index. -/
theorem bitVec5_toNat_lt (i : BitVec 5) : i.toNat < 32 := i.isLt

theorem bitVec5_toNat_ne_zero {i : BitVec 5} (h : i ≠ 0) : i.toNat ≠ 0 := by
  intro hzero
  exact h (BitVec.eq_of_toNat_eq (by rw [hzero]; rfl))

/-- **Every generated event is well-formed.**

The three timestamp conjuncts come from `GenState.prevTs_lt` at the current window, and the
invariant that feeds the next window comes from `GenState.stepRType_bounded` — which is the whole
reason the fold threads a state at all. The clock discipline propagates because `CLK_INC` is a
multiple of 8. -/
theorem aluEvents_wellFormed :
    ∀ (steps : List AluStep) (g : GenState) (clk : ℕ),
      g.Bounded (clk + regCOffset) → clk % ordinaryClkInc = 1 →
      (∀ s ∈ steps, s.WellFormed) →
      ∀ e ∈ aluEvents g clk steps, e.WellFormed
  | [], _, _, _, _, _ => by simp [aluEvents]
  | s :: rest, g, clk, hb, hclk, hs => by
      intro e he
      rw [aluEvents, List.mem_cons] at he
      rcases he with rfl | he
      · obtain ⟨hA, hB, hC⟩ := GenState.prevTs_lt hb s.a s.b s.c
        obtain ⟨hpc, hane, hbv, hcv, hpa⟩ := hs s List.mem_cons_self
        exact
          { clk_mod := hclk
            pc_lt := hpc
            opA_lt := bitVec5_toNat_lt _
            opB_lt := bitVec5_toNat_lt _
            opC_lt := bitVec5_toNat_lt _
            opA_ne_zero := bitVec5_toNat_ne_zero hane
            b_lt := hbv
            c_lt := hcv
            prevA_lt := hpa
            prevTsA_lt := hA
            prevTsB_lt := hB
            prevTsC_lt := hC }
      · refine aluEvents_wellFormed rest _ _ (GenState.stepRType_bounded hb s.a s.b s.c) ?_
          (fun t ht => hs t (List.mem_cons_of_mem _ ht)) e he
        show (clk + 8) % 8 = 1
        have : clk % 8 = 1 := hclk
        omega


/-! ## Non-vacuity

`AluStep.WellFormed` is five bounds and a disequality; `GenState.Bounded` is two universal bounds.
Either could be accidentally unsatisfiable, and the fold's theorem would then say nothing. These
witnesses are the guard, and the step is a real one: `add x1, x1, x1` at the machine's genesis
clock — deliberately the aliasing case, where `op_b`'s previous access is this same row's `op_c`
read rather than anything before the row, which is the case the intra-row ordering exists for. -/

/-- A real ALU step. -/
def witnessStep : AluStep where
  pc := 65536
  opcode := 0
  a := 1
  b := 1
  c := 1
  bVal := 0
  cVal := 0
  prevAVal := 0

theorem witnessStep_wellFormed : witnessStep.WellFormed where
  pc_lt := by norm_num [witnessStep]
  a_ne_zero := by decide
  bVal_lt := by norm_num [witnessStep]
  cVal_lt := by norm_num [witnessStep]
  prevAVal_lt := by norm_num [witnessStep]

/-- The genesis bookkeeping admits the first row: SP1's clock starts at `1`, and nothing has been
accessed. -/
theorem initial_bounded_at_genesis : GenState.initial.Bounded (1 + regCOffset) :=
  GenState.initial_bounded.mono (by norm_num)

/-- **The fold produces well-formed events on a real input** — the two guards composed. -/
theorem witnessEvents_wellFormed :
    ∀ e ∈ aluEvents GenState.initial 1 [witnessStep], e.WellFormed :=
  aluEvents_wellFormed _ _ _ initial_bounded_at_genesis (by norm_num)
    (by simpa using witnessStep_wellFormed)

end SP1Clean.TraceGen
